# `minsize`

Collections with a statically known minimum size, using const generics.

## Features

 - Wrapper type around a plain standard library `Vec` that enforces an arbitrary minimum size
     - Special methods that simplify operations on collections that are known to be non-empty<sup>[[note](#note-const-generics-support)]</sup>
 - Ability to deref to a slice and to cheaply convert from and to an unrestricted `Vec`
     - All the methods provided by standard slices you already know and use remain available!

#### Note: Const generics support

With the basic first level of const generics support (historically known as `min_const_generics`), it is not possible to guarante the non-empty property for *all* const-generic values.
This crate uses an indirection through a trait, that for now is implemented by hand for a small number of useful values.
Once the necessary language features are stabilized, this list of manual implementations will be replaced with a proper blanket implementation.

## License

Licensed under either of

 - Apache License, Version 2.0 ([LICENSE-APACHE](LICENSE-APACHE) or http://www.apache.org/licenses/LICENSE-2.0)
 - MIT license ([LICENSE-MIT](LICENSE-MIT) or http://opensource.org/licenses/MIT)

at your option.

#### Contribution

Unless you explicitly state otherwise, any contribution intentionally submitted for inclusion in the work by you, as defined in the Apache-2.0 license, shall be dual licensed as above, without any additional terms or conditions.

