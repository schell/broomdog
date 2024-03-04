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

    #[snafu(display("Types are still loaned: \n{}", names.concat()))]
    ManyLoans { names: Vec<&'static str> },
}

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
    pub fn downcast_ref<T: Any + Send + Sync + 'static>(
        &self,
    ) -> std::result::Result<&T, BroomdogErr> {
        self.inner
            .downcast_ref::<T>()
            .with_context(|| DowncastRefSnafu {
                from: self.type_name(),
                to: std::any::type_name::<T>(),
            })
    }

    /// Attempt to downcast a mutable reference to the given parameterized type.
    pub fn downcast_mut<T: Any + Send + Sync + 'static>(
        &mut self,
    ) -> std::result::Result<&mut T, BroomdogErr> {
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
    pub fn is_owned(&self) -> bool {
        matches!(self, InnerLoan::Owned(_))
    }

    pub fn as_owned(&self, name: &'static str) -> std::result::Result<&TypeValue, BroomdogErr> {
        match self {
            InnerLoan::Owned(a) => Ok(a),
            InnerLoan::Loan(_) => Err(BroomdogErr::Loan { name }),
            InnerLoan::LoanMut(_) => Err(BroomdogErr::ExclusiveLoan { name }),
        }
    }

    pub fn as_owned_mut(
        &mut self,
        name: &'static str,
    ) -> std::result::Result<&mut TypeValue, BroomdogErr> {
        match self {
            InnerLoan::Owned(a) => Ok(a),
            InnerLoan::Loan(_) => Err(BroomdogErr::Loan { name }),
            InnerLoan::LoanMut(_) => Err(BroomdogErr::ExclusiveLoan { name }),
        }
    }

    pub fn into_owned(self, name: &'static str) -> std::result::Result<TypeValue, InnerLoan> {
        match self {
            InnerLoan::Owned(value) => Ok(value),
            InnerLoan::Loan(arc) => match Arc::try_unwrap(arc) {
                Ok(value) => {
                    log::trace!("unified {name}");
                    Ok(value)
                }
                Err(arc) => Err(InnerLoan::Loan(arc)),
            },
            InnerLoan::LoanMut(arc_mut_opt) => {
                let mut guard = arc_mut_opt.lock().unwrap();
                let may_value = guard.take();
                drop(guard);
                if let Some(value) = may_value {
                    log::trace!("unified {name}");
                    Ok(value)
                } else {
                    log::error!(
                        "'{name}' cannot be converted to owned as it is loaned exclusively"
                    );
                    Err(InnerLoan::LoanMut(arc_mut_opt))
                }
            }
        }
    }

    pub fn into_loaned(self, name: &'static str) -> std::result::Result<Arc<TypeValue>, InnerLoan> {
        match self {
            InnerLoan::Owned(value) => Ok(Arc::new(value)),
            InnerLoan::Loan(arc) => Ok(arc),
            InnerLoan::LoanMut(arc_mut_opt) => {
                let maybe_value = arc_mut_opt.lock().unwrap().take();
                if let Some(value) = maybe_value {
                    log::trace!("converted exclusive {name} loan to non-exclusive");
                    Ok(Arc::new(value))
                } else {
                    log::error!(
                        "'{name}' cannot be converted into a loan as it is loaned exclusively"
                    );
                    Err(InnerLoan::LoanMut(arc_mut_opt))
                }
            }
        }
    }

    pub fn downcast_ref<T: Any + Send + Sync>(
        &self,
        name: &'static str,
    ) -> std::result::Result<&T, BroomdogErr> {
        match self {
            InnerLoan::Owned(value) => value.downcast_ref(),
            InnerLoan::Loan(arc) => arc.downcast_ref(),
            InnerLoan::LoanMut(_) => Err(BroomdogErr::ExclusiveLoan { name }),
        }
    }

    pub fn downcast_mut<T: Any + Send + Sync>(
        &mut self,
        name: &'static str,
    ) -> std::result::Result<&mut T, BroomdogErr> {
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
    pub fn insert_value<T: Any + Send + Sync>(
        &mut self,
        value: T,
    ) -> std::result::Result<Option<T>, BroomdogErr> {
        let key = TypeKey::new::<T>();
        if let Some(old_value) = self
            .inner
            .insert(key, InnerLoan::Owned(TypeValue::new(value)))
        {
            let old_value = old_value
                .into_owned(key.name())
                .map_err(|_| BroomdogErr::Loan {
                    name: std::any::type_name::<T>(),
                })?;
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
    pub fn get_value<T: Any + Send + Sync>(&self) -> std::result::Result<Option<&T>, BroomdogErr> {
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
    pub fn get_value_mut<T: Any + Send + Sync>(
        &mut self,
    ) -> std::result::Result<Option<&mut T>, BroomdogErr> {
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
    /// Returns an error if the typed value is already exclusively loaned.
    ///
    /// [`TypeMap::unify`] should be called before any call to
    /// [`TypeMap::get_value`] or [`TypeMap::get_value_mut`], or those will
    /// result in an error.
    ///
    /// Additionally, if [`TypeMap::loan_mut`] is called before the returned
    /// `Loan` is dropped, that call will err.
    pub fn loan(&mut self, key: TypeKey) -> std::result::Result<Option<Loan>, BroomdogErr> {
        if let Some(inner) = self.inner.remove(&key) {
            log::trace!("loaning {key}");
            match inner.into_loaned(key.name()) {
                Ok(arc) => {
                    self.inner.insert(key, InnerLoan::Loan(arc.clone()));
                    Ok(Some(Loan { inner: arc }))
                }
                Err(inner) => {
                    self.inner.insert(key, inner);
                    ExclusiveLoanSnafu { name: key.name() }.fail()
                }
            }
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
    pub fn loan_mut(&mut self, key: TypeKey) -> std::result::Result<Option<LoanMut>, BroomdogErr> {
        if let Some(value) = self.inner.remove(&key) {
            log::trace!("exclusively loaning {key}");
            if value.is_owned() {
                // UNWRAP: safe because we just checked that this value is owned
                let value = value.into_owned(key.name()).unwrap();
                let outer = Arc::new(Mutex::new(None));
                self.inner.insert(key, InnerLoan::LoanMut(outer.clone()));
                Ok(Some(LoanMut {
                    inner: Some(value),
                    outer,
                }))
            } else {
                LoanSnafu { name: key.name() }.fail()
            }
        } else {
            log::trace!("can't exclusively loan {key}, DNE");
            Ok(None)
        }
    }

    /// Return whether all values are unified.
    pub fn is_unified(&self) -> bool {
        self.inner
            .iter()
            .all(|(_ty_key, loan): (_, &InnerLoan)| loan.is_owned())
    }

    /// Attempts to unify the map, converting all loaned values back into owned
    /// values.
    ///
    /// This must be called before using [`TypeMap::get_value`] or
    /// [`TypeMap::get_value_mut`].
    ///
    /// If the map fails to unify, the map will remain in a consistent state.
    pub fn unify(&mut self) -> std::result::Result<(), BroomdogErr> {
        let mut names = vec![];
        for (key, inner_loan) in std::mem::take(&mut self.inner) {
            let loan = match inner_loan.into_owned(key.name()) {
                Ok(value) => InnerLoan::Owned(value),
                Err(loan) => {
                    names.push(key.name());
                    loan
                }
            };
            let _ = self.inner.insert(key, loan);
        }
        if names.is_empty() {
            Ok(())
        } else {
            ManyLoansSnafu { names }.fail()
        }
    }
}
