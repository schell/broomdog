# broomdog 🧹🐕

`broomdog` is a Rust library providing a map of type-erased values with indefinite loanership semantics.

## what is a type map?

`broomdog`'s type map is a map of `std::any::TypeId` keys to type-erased values.
There may be at most one value for each key, which means the map stores singleton values of different types.

## why another type map library?

`broomdog` provides the usual map-like API, and then some.
Notably `broomdog` provides "indefinite loanership".

### wtf is indefinite loanership?

It's a wordsmush that roughly means you can get a loaned value from the map without
a lifetime.

#### wtf is a loaned value?

A loaned value is a smart pointer to a value that you can `deref` or `deref_mut`.

You may only have one exclusive (write) loan of any one value at a time, but you may have as many non-exclusive (read) loans of the same value as you like. You may also have multiple exclusive loans of _different_ types at the same time.

After an exclusive loan is dropped you may make another exclusive loan of the same type, or multiple non-exclusive loans of that type.

This allows you to make multiple loans of different types at the same time, without map borrow conflicts - so long as you don't try to share an exclusive loan of the same type at the same time.

Furthermore, `broomdog` has nice descriptive errors with the names of the types (more even, if compiled with `debug_assertions`).

## uses

Type erased maps have many uses, but `broomdog` was to facilitate the following:

* resource storage layer for [`apecs`](https://github.com/schell/apecs)'s system schedule runner (`apecs` is an ECS library)
* resource storage layer for [`renderling`](https://github.com/schell/renderling)'s render node schedule runner (part of the render graph)

It works particularly well with [`dagga`](https://github.com/schell/dagga), which is a DAG scheduler.
Together it's possible to define and run an extensible system of functions that share mutable resources, some of which may run in parallel.

## why (the heck) did you name it `broomdog`

* "broomdog" is the name of the part broom / part dog character in Alice in Wonderland that erases the path as it walks along it.

* I think names should be funny.

* It's my library, oh well.

# example

```rust
use broomdog::{TypeMap, TypeKey};

let mut map = TypeMap::default();
assert!(map.insert_value(0usize).unwrap().is_none());
assert!(map.insert_value(0.0f32).unwrap().is_none());
assert!(map.insert_value("hello").unwrap().is_none());

{
    let num_usize = map.get_value_mut::<usize>().unwrap().unwrap();
    *num_usize += 666;
}
assert_eq!(666, *map.get_value::<usize>().unwrap().unwrap());
assert_eq!("hello", *map.get_value::<&str>().unwrap().unwrap());

{
    let loan = map.loan(TypeKey::new::<usize>()).unwrap().unwrap();
    assert_eq!(666, *loan.downcast_ref::<usize>().unwrap());
    let loan2 = map.loan(TypeKey::new::<usize>()).unwrap().unwrap();
    assert_eq!(666, *loan2.downcast_ref::<usize>().unwrap());

    let mut loan_mut = map.loan_mut(TypeKey::new::<&str>()).unwrap().unwrap();
    let word = loan_mut.downcast_mut::<&str>().unwrap();
    assert_eq!("hello", *word);
    *word = "goodbye";
}

map.unify().unwrap();
```
