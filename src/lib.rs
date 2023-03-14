//! # broomdog 🧹🐕
//!
//! `broomdog` is a Rust library providing a type map.
//!
//! ## what is a type map?
//!
//! `broomdog`'s type map is a map of `std::any::TypeId` keys to type-erased
//! values. There may be at most one value for each key, which means the map
//! stores singleton values of different types.
//!
//! ## type values
//! Values of `TypeMap` may be any value that is `Any + Send + Sync`.
use rustc_hash::FxHashMap;
use snafu::prelude::*;

use std::{
    any::{Any, TypeId},
    ops::{Deref, DerefMut},
    sync::{Arc, Mutex},
};

#[cfg(doctest)]
pub mod doctest {
    #[doc = include_str!("../README.md")]
    pub struct ReadmeDoctests;
}

#[derive(Debug, Snafu)]
pub enum BroomdogErr {
    #[snafu(display("Cannot downcast_ref from {} to {to}", from.unwrap_or_else(|| "unknown")))]
    DowncastRef {
        from: Option<&'static str>,
        to: &'static str,
    },

    #[snafu(display("Cannot downcast_mut from {} to {to}", from.unwrap_or_else(|| "unknown")))]
    DowncastMut {
        from: Option<&'static str>,
        to: &'static str,
    },

    #[snafu(display("The type of a new value '{new_type}' doesn't match the type of an old value '{}'", old_type.unwrap_or_else(|| "unknown")))]
    Mismatch {
        new_type: &'static str,
        old_type: Option<&'static str>,
    },

    #[snafu(display("Values are still on loan:  {}", loans.iter().map(|k| k.name()).collect::<Vec<_>>().join(", ")))]
    Unify { loans: Vec<TypeKey> },

    #[snafu(display("Type {name} is already exclusively loaned"))]
    ExclusiveLoan { name: &'static str },

    #[snafu(display("Type {name} is already loaned"))]
    Loan { name: &'static str },
}

pub type Result<T> = std::result::Result<T, BroomdogErr>;

/// A key for a type-erased value.
#[derive(Clone, Copy, Debug)]
pub struct TypeKey {
    type_id: TypeId,
    #[cfg(debug_assertions)]
    type_name: &'static str,
}

impl std::fmt::Display for TypeKey {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        #[cfg(debug_assertions)]
        {
            f.write_str(self.type_name)
        }
        #[cfg(not(debug_assertions))]
        {
            f.write_str("_")
        }
    }
}

impl std::hash::Hash for TypeKey {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.type_id.hash(state);
    }
}

impl PartialEq for TypeKey {
    fn eq(&self, other: &Self) -> bool {
        self.type_id == other.type_id
    }
}

impl Eq for TypeKey {}

impl TypeKey {
    /// Create a new `TypeKey`.
    pub fn new<T: Any + Send + Sync>() -> Self {
        TypeKey {
            type_id: TypeId::of::<T>(),
            #[cfg(debug_assertions)]
            type_name: std::any::type_name::<T>(),
        }
    }

    /// Returns the name of the type, if compiled with `debug_assertions`,
    /// otherwise `"unknown"`.
    pub const fn name(&self) -> &'static str {
        #[cfg(debug_assertions)]
        {
            self.type_name
        }
        #[cfg(not(debug_assertions))]
        {
            "unknown"
        }
    }
}

/// A type-erased value.
#[derive(Debug)]
pub struct TypeValue {
    inner: Box<dyn Any + Send + Sync>,
    #[cfg(debug_assertions)]
    type_name: &'static str,
}

impl<T: Any + Send + Sync> From<Box<T>> for TypeValue {
    fn from(inner: Box<T>) -> Self {
        TypeValue {
            inner,
            #[cfg(debug_assertions)]
            type_name: std::any::type_name::<T>(),
        }
    }
}

impl TypeValue {
    /// Create a new type value from a value.
    pub fn new<T: Any + Send + Sync>(value: T) -> Self {
        TypeValue::from(Box::new(value))
    }

    /// Return the name of the type this value holds, if possible.
    ///
    /// This only returns `Some` when compiled with `debug_assertions`.
    pub fn type_name(&self) -> Option<&'static str> {
        #[cfg(debug_assertions)]
        {
            Some(self.type_name)
        }
        #[cfg(not(debug_assertions))]
        {
            None
        }
    }

    /// Attempt to downcast the value to the given parameterized type,
    /// if the downcast fails (because the type givin doesn't match) the
    /// original `TypeValue` will be returned wrapped in `Err`.
    pub fn downcast<T: Any + Send + Sync + 'static>(
        self,
    ) -> std::result::Result<Box<T>, TypeValue> {
        self.inner.downcast::<T>().map_err(|inner| TypeValue {
            inner,
            #[cfg(debug_assertions)]
            type_name: self.type_name,
        })
    }

    /// Attempt to downcast a reference to the given parameterized type.
    pub fn downcast_ref<T: Any + Send + Sync + 'static>(&self) -> Result<&T> {
        self.inner
            .downcast_ref::<T>()
            .with_context(|| DowncastRefSnafu {
                from: self.type_name(),
                to: std::any::type_name::<T>(),
            })
    }

    /// Attempt to downcast a mutable reference to the given parameterized type.
    pub fn downcast_mut<T: Any + Send + Sync + 'static>(&mut self) -> Result<&mut T> {
        let from = self.type_name();
        self.inner
            .downcast_mut::<T>()
            .with_context(move || DowncastMutSnafu {
                from,
                to: std::any::type_name::<T>(),
            })
    }
}

/// A shared, type-erased value.
pub struct Loan {
    inner: Arc<TypeValue>,
}

impl Deref for Loan {
    type Target = TypeValue;

    fn deref(&self) -> &Self::Target {
        &self.inner
    }
}

/// An exclusive type-erased value.
///
/// When the loan is dropped the inner value is sent back to the [`TypeMap`] it
/// originated from.
pub struct LoanMut {
    inner: Option<TypeValue>,
    outer: Arc<Mutex<Option<TypeValue>>>,
}

impl Drop for LoanMut {
    fn drop(&mut self) {
        // UNWRAP: safe because this is the only time we take
        let inner = self.inner.take().unwrap();
        let mut outer = self.outer.lock().unwrap();
        *outer = Some(inner);
    }
}

impl Deref for LoanMut {
    type Target = TypeValue;

    fn deref(&self) -> &Self::Target {
        // UNWRAP: safe because inner is only `None` _after_ `drop`
        self.inner.as_ref().unwrap()
    }
}

impl DerefMut for LoanMut {
    fn deref_mut(&mut self) -> &mut Self::Target {
        // UNWRAP: safe because inner is only `None` _after_ `drop`
        self.inner.as_mut().unwrap()
    }
}

/// The internal state of a [`TypeValue`] within a [`TypeMap`].
#[derive(Debug)]
pub enum InnerLoan {
    // The type is available for any kind of loan.
    Owned(TypeValue),
    // The type has been loaned but can be loaned again.
    Loan(Arc<TypeValue>),
    // The type has been loaned exclusively and cannot be loaned again until unified.
    LoanMut(Arc<Mutex<Option<TypeValue>>>),
}

impl From<TypeValue> for InnerLoan {
    fn from(value: TypeValue) -> Self {
        InnerLoan::Owned(value)
    }
}

impl InnerLoan {
    pub fn as_owned(&self, name: &'static str) -> Result<&TypeValue> {
        match self {
            InnerLoan::Owned(a) => Ok(a),
            InnerLoan::Loan(_) => Err(BroomdogErr::Loan { name }),
            InnerLoan::LoanMut(_) => Err(BroomdogErr::ExclusiveLoan { name }),
        }
    }

    pub fn as_owned_mut(&mut self, name: &'static str) -> Result<&mut TypeValue> {
        match self {
            InnerLoan::Owned(a) => Ok(a),
            InnerLoan::Loan(_) => Err(BroomdogErr::Loan { name }),
            InnerLoan::LoanMut(_) => Err(BroomdogErr::ExclusiveLoan { name }),
        }
    }

    pub fn into_owned(self, name: &'static str) -> Result<TypeValue> {
        match self {
            InnerLoan::Owned(value) => Ok(value),
            InnerLoan::Loan(arc) => {
                let value = Arc::try_unwrap(arc)
                    .ok()
                    .with_context(|| LoanSnafu { name })?;
                log::trace!("unified {name}");
                Ok(value)
            }
            InnerLoan::LoanMut(arc_mut_opt) => {
                let may_value = arc_mut_opt.lock().unwrap().take();
                let value = may_value.with_context(|| ExclusiveLoanSnafu { name })?;
                log::trace!("unified {name}");
                Ok(value)
            }
        }
    }

    pub fn into_loaned(self, name: &'static str) -> Result<Arc<TypeValue>> {
        match self {
            InnerLoan::Owned(value) => Ok(Arc::new(value)),
            InnerLoan::Loan(arc) => Ok(arc),
            InnerLoan::LoanMut(arc_mut_opt) => {
                let may_value = arc_mut_opt.lock().unwrap().take();
                let value = may_value.with_context(|| ExclusiveLoanSnafu { name })?;
                log::trace!("converted exclusive {name} loan to non-exclusive");
                Ok(Arc::new(value))
            }
        }
    }

    pub fn downcast_ref<T: Any + Send + Sync>(&self, name: &'static str) -> Result<&T> {
        match self {
            InnerLoan::Owned(value) => value.downcast_ref(),
            InnerLoan::Loan(arc) => arc.downcast_ref(),
            InnerLoan::LoanMut(_) => Err(BroomdogErr::ExclusiveLoan { name }),
        }
    }

    pub fn downcast_mut<T: Any + Send + Sync>(&mut self, name: &'static str) -> Result<&mut T> {
        let owned = self.as_owned_mut(name)?;
        owned.downcast_mut()
    }
}

/// A map of type identifiers to type-erased values.
#[derive(Default, Debug)]
pub struct TypeMap {
    inner: FxHashMap<TypeKey, InnerLoan>,
}

impl Deref for TypeMap {
    type Target = FxHashMap<TypeKey, InnerLoan>;

    fn deref(&self) -> &Self::Target {
        &self.inner
    }
}

impl DerefMut for TypeMap {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.inner
    }
}

impl TypeMap {
    /// Insert a value into the type map.
    pub fn insert_value<T: Any + Send + Sync>(&mut self, value: T) -> Result<Option<T>> {
        let key = TypeKey::new::<T>();
        if let Some(old_value) = self
            .inner
            .insert(key, InnerLoan::Owned(TypeValue::new(value)))
        {
            let old_value = old_value.into_owned(key.name())?;
            log::trace!("inserted {key} and am returning old value");
            old_value
                .downcast()
                .map(|box_t| Some(*box_t))
                .map_err(|old_value| BroomdogErr::Mismatch {
                    new_type: std::any::type_name::<T>(),
                    old_type: old_value.type_name(),
                })
        } else {
            log::trace!("inserted {key}");
            Ok(None)
        }
    }

    /// Returns a reference to the value of the given parameterized type.
    pub fn get_value<T: Any + Send + Sync>(&self) -> Result<Option<&T>> {
        let key = TypeKey::new::<T>();
        if let Some(value) = self.inner.get(&key) {
            let t = value.downcast_ref(key.name())?;
            Ok(Some(t))
        } else {
            Ok(None)
        }
    }

    /// Returns a mutable reference to the value of the given parameterized
    /// type.
    pub fn get_value_mut<T: Any + Send + Sync>(&mut self) -> Result<Option<&mut T>> {
        let key = TypeKey::new::<T>();
        if let Some(value) = self.inner.get_mut(&key) {
            let t = value.downcast_mut(key.name())?;
            Ok(Some(t))
        } else {
            Ok(None)
        }
    }

    /// Indefinitely loans the typed value for sharing across threads.
    ///
    /// [`TypeMap::unify`] should be called before any call to
    /// [`TypeMap::get_value`] or [`TypeMap::get_value_mut`], or those will
    /// result in an error.
    ///
    /// Additionally, if [`TypeMap::loan_mut`] is called before the returned
    /// `Loan` is dropped, that call will err.
    pub fn loan(&mut self, key: TypeKey) -> Result<Option<Loan>> {
        //
        if let Some(inner) = self.inner.remove(&key) {
            log::trace!("loaning {key}");
            let arc = inner.into_loaned(key.name())?;
            self.inner.insert(key, InnerLoan::Loan(arc.clone()));
            Ok(Some(Loan { inner: arc }))
        } else {
            log::trace!("can't loan {key}, DNE");
            Ok(None)
        }
    }

    /// Indefinitely loans the typed value for exclusive mutation.
    ///
    /// [`TypeMap::unify`] should be called before any call to
    /// [`TypeMap::get_value`] or [`TypeMap::get_value_mut`], or those will
    /// result in an error.
    ///
    /// Additionally, if [`TypeMap::loan`] or [`TypeMap::loan_mut`] are called
    /// again before the returned `LoanMut` is dropped, those calls will err.
    pub fn loan_mut(&mut self, key: TypeKey) -> Result<Option<LoanMut>> {
        if let Some(value) = self.inner.remove(&key) {
            log::trace!("exclusively loaning {key}");
            let value = value.into_owned(key.name())?;
            let outer = Arc::new(Mutex::new(None));
            self.inner.insert(key, InnerLoan::LoanMut(outer.clone()));
            Ok(Some(LoanMut {
                inner: Some(value),
                outer,
            }))
        } else {
            log::trace!("can't exclusively loan {key}, DNE");
            Ok(None)
        }
    }


    /// Attempts to unify the map, converting all loaned values back into owned
    /// values.
    ///
    /// This must be called before using [`TypeMap::get_value`] or
    /// [`TypeMap::get_value_mut`].
    pub fn unify(&mut self) -> Result<()> {
        for (key, inner_loan) in std::mem::take(&mut self.inner).into_iter() {
            let value = inner_loan.into_owned(key.name())?;
            let _ = self.inner.insert(key, InnerLoan::Owned(value));
        }
        Ok(())
    }
}
