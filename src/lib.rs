#![warn(
    missing_debug_implementations,
    missing_docs,
    rust_2018_idioms,
    unreachable_pub
)]
#![deny(broken_intra_doc_links)]
#![forbid(unsafe_code)]

//! Collections with a statically known minimum size.

use std::{
    cmp,
    convert::TryFrom,
    fmt,
    ops::{Deref, DerefMut, Index, IndexMut},
    slice::{Iter as SliceIter, IterMut as SliceIterMut, SliceIndex},
    vec::IntoIter,
};

/// Marker trait for non-empty minimum sizes.
///
/// The purpose of this is to abstract over the length restriction until const expressions are
/// stabilized. Currently it is implemented for some useful sizes manually, but once the necessary
/// language features are stabilized, this will be replaced with a blanket impl for all unsigned
/// integers greater than zero.
pub trait NotEmpty: sealed::Sealed {}

mod sealed {
    pub trait Sealed {}
}

macro_rules! impl_for_arrays {
    ($($size:literal),+) => {
        $(
            impl<T> sealed::Sealed for MinSizedVec<T, $size> {}
            impl<T> NotEmpty for MinSizedVec<T, $size> {}
        )*
    };
}

impl_for_arrays!(1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 32, 64, 128);

/// A [`Vec`] that always contains at least one element.
///
/// This is just a utility alias, so see the [`MinSizedVec`] docs for available methods.
pub type NonEmptyVec<T> = MinSizedVec<T, 1>;

/// A [`Vec`] with a minimum size.
///
/// This wraps a plain standard library [`Vec`], but inserts checks that it never falls below the
/// required length.
///
/// This type derefs to slices in the same way [`Vec`] does, so most of the methods you already
/// know are available too.
#[derive(Clone, Eq, Ord, Hash)]
pub struct MinSizedVec<T, const N: usize>(Vec<T>);

impl<T, const MINIMUM_SIZE: usize> MinSizedVec<T, MINIMUM_SIZE> {
    /// The minimum size of this collection.
    pub const MINIMUM_SIZE: usize = MINIMUM_SIZE;

    /// Create a `MinSizedVec` from a plain `Vec`.
    ///
    /// This checks the length, handing you back the input if it is less than the required length.
    ///
    /// This is equivalent to the [`TryFrom<Vec<T>>`][`TryFrom`] impl.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::convert::TryInto;
    /// # use minsize::MinSizedVec;
    /// let min_size: MinSizedVec<_, 3> = vec![1, 2, 3].try_into().unwrap();
    ///
    /// // Too short input:
    /// let result: Result<MinSizedVec<_, 2>, _> = vec![1].try_into();
    /// assert_eq!(result, Err(vec![1]));
    /// ```
    pub fn new(value: Vec<T>) -> Result<MinSizedVec<T, MINIMUM_SIZE>, Vec<T>> {
        Self::try_from(value)
    }

    /// Create a `MinSizedVec` from an iterator.
    ///
    /// This collects the given iterator into a plain [`Vec`] and then checks the length, returning
    /// either a `MinSizedVec`, or the raw collected [`Vec`] if it is too short.
    ///
    /// # Examples
    ///
    /// ```
    /// # use minsize::MinSizedVec;
    /// let v = MinSizedVec::<_, 2>::from_iterator(vec![1, 2, 3]).unwrap();
    /// assert_eq!(v.len(), 3);
    ///
    /// let v = MinSizedVec::<_, 2>::from_iterator(vec![1]);
    /// assert_eq!(v, Err(vec![1]));
    /// ```
    pub fn from_iterator<I>(iterator: I) -> Result<MinSizedVec<T, MINIMUM_SIZE>, Vec<T>>
    where
        I: IntoIterator<Item = T>,
    {
        let vec: Vec<T> = iterator.into_iter().collect();

        if vec.len() >= MINIMUM_SIZE {
            Ok(Self(vec))
        } else {
            Err(vec)
        }
    }

    /// Extract the contained [`Vec`], thus removing the length restriction.
    ///
    /// # Examples
    ///
    /// ```
    /// # use minsize::MinSizedVec;
    /// let v: MinSizedVec<_, 3> = MinSizedVec::new(vec![1, 2, 3]).unwrap();
    /// let v: Vec<_> = v.into_inner();
    /// assert_eq!(v, vec![1, 2, 3]);
    /// ```
    pub fn into_inner(self) -> Vec<T> {
        self.0
    }

    /// Append a value.
    ///
    /// # Examples
    ///
    /// ```
    /// # use minsize::MinSizedVec;
    /// let mut v: MinSizedVec<_, 2> = MinSizedVec::new(vec![1, 2]).unwrap();
    /// v.push(3);
    /// assert_eq!(v, &[1, 2, 3]);
    /// ```
    pub fn push(&mut self, value: T) {
        self.0.push(value);
    }

    /// Remove a value from the end of the collection.
    ///
    /// This will return `None` when the minimum length is reached.
    ///
    /// # Examples
    ///
    /// ```
    /// # use minsize::MinSizedVec;
    /// let mut v: MinSizedVec<_, 2> = MinSizedVec::new(vec![1, 2, 3]).unwrap();
    /// assert_eq!(v.pop(), Some(3));
    /// assert_eq!(v.pop(), None);
    /// assert_eq!(v, &[1, 2]);
    /// ```
    pub fn pop(&mut self) -> Option<T> {
        if self.len() > MINIMUM_SIZE {
            self.0.pop()
        } else {
            None
        }
    }

    /// Clear the collection to the minimum size required.
    ///
    /// This drops any elements after the index required for the minimum size.
    ///
    /// # Examples
    ///
    /// ```
    /// # use minsize::MinSizedVec;
    /// let mut v: MinSizedVec<_, 2> = MinSizedVec::new(vec![1, 2, 3]).unwrap();
    /// v.clear_to_minimum();
    /// assert_eq!(v, &[1, 2]);
    /// ```
    pub fn clear_to_minimum(&mut self) {
        self.truncate(MINIMUM_SIZE);
    }

    /// Shorten the collection, keeping the first `len` elements.
    ///
    /// If `len` is greater than the current length, this has no effect. If `len` is smaller than
    /// the minimum size, the collection is shortened to the minimum size.
    ///
    /// # Examples
    ///
    /// ```
    /// # use minsize::MinSizedVec;
    /// let mut v: MinSizedVec<_, 2> = MinSizedVec::new(vec![1, 2, 3, 4]).unwrap();
    /// v.truncate(3);
    /// assert_eq!(v, &[1, 2, 3]);
    ///
    /// // The length is still capped to the minimum size:
    /// v.truncate(0);
    /// assert_eq!(v, &[1, 2]);
    /// ```
    pub fn truncate(&mut self, len: usize) {
        let len = cmp::max(len, MINIMUM_SIZE);
        self.0.truncate(len);
    }

    /// Clones and appends all elements in `other` to the collection.
    ///
    /// # Examples
    ///
    /// ```
    /// # use minsize::MinSizedVec;
    /// let mut v: MinSizedVec<_, 2> = MinSizedVec::new(vec![1, 2]).unwrap();
    /// v.extend_from_slice(&[3, 4]);
    /// assert_eq!(v, &[1, 2, 3, 4]);
    /// ```
    pub fn extend_from_slice(&mut self, other: &[T])
    where
        T: Clone,
    {
        self.0.extend_from_slice(other);
    }

    /// Reserves capacity for at least `additional` more elements to be inserted.
    ///
    /// See [`Vec::reserve`] for details.
    pub fn reserve(&mut self, additional: usize) {
        self.0.reserve(additional);
    }

    /// Reserves the minimum capacity for exactly `additional` more elements to be inserted.
    ///
    /// See [`Vec::reserve_exact`] for details.
    pub fn reserve_exact(&mut self, additional: usize) {
        self.0.reserve_exact(additional);
    }

    /// Resizes the collection so that the length equals `new_len`.
    ///
    /// If the current length is less than `new_len`, clones of `value` are appended.
    ///
    /// If the current length is larger than `new_len`, the collection is truncated to `new_len` or
    /// the minimum size, whichever is larger.
    ///
    /// # Examples
    ///
    /// ```
    /// # use minsize::MinSizedVec;
    /// let mut v: MinSizedVec<_, 2> = MinSizedVec::new(vec![1, 2, 3]).unwrap();
    ///
    /// v.resize(5, 4);
    /// assert_eq!(v, &[1, 2, 3, 4, 4]);
    ///
    /// v.resize(3, 4);
    /// assert_eq!(v, &[1, 2, 3]);
    ///
    /// v.resize(0, 4);
    /// assert_eq!(v, &[1, 2]);
    /// ```
    pub fn resize(&mut self, new_len: usize, value: T)
    where
        T: Clone,
    {
        self.0.resize(cmp::max(new_len, MINIMUM_SIZE), value);
    }

    /// Resizes the collection so that the length equals `new_len`.
    ///
    /// If the current length is less than `new_len`, the collection is extended by the values
    /// returned from calling the `f` closure.
    ///
    /// If the current length is larger than `new_len`, the collection is truncated to `new_len` or
    /// the minimum size, whichever is larger.
    ///
    /// # Examples
    ///
    /// ```
    /// # use minsize::MinSizedVec;
    /// let mut v: MinSizedVec<_, 2> = MinSizedVec::new(vec![1, 2, 3]).unwrap();
    ///
    /// let mut start = v.len();
    /// v.resize_with(5, || { start += 1; start });
    /// assert_eq!(v, &[1, 2, 3, 4, 5]);
    ///
    /// v.resize_with(3, || 4);
    /// assert_eq!(v, &[1, 2, 3]);
    ///
    /// v.resize_with(0,  || 4);
    /// assert_eq!(v, &[1, 2]);
    /// ```
    pub fn resize_with<F>(&mut self, new_len: usize, f: F)
    where
        F: FnMut() -> T,
    {
        self.0.resize_with(cmp::max(new_len, MINIMUM_SIZE), f);
    }

    /// Insert the given `element` at the given `index`, shifting all elements after it to the right.
    ///
    /// # Panics
    ///
    /// Panics if the given index is greater than the length of the collection.
    ///
    /// # Examples
    ///
    /// ```
    /// # use minsize::MinSizedVec;
    /// let mut v = MinSizedVec::from([1, 2]);
    /// v.insert(2, 3);
    /// assert_eq!(v, &[1, 2, 3]);
    /// v.insert(2, 4);
    /// assert_eq!(v, &[1, 2, 4, 3]);
    /// ```
    pub fn insert(&mut self, index: usize, element: T) {
        self.0.insert(index, element);
    }

    /// Remove and and return the element at the given index from the collection.
    ///
    /// This will shift all elements after `index` to the left.
    ///
    /// # Panics
    ///
    /// This will panic if `index` is out of bounds, or if removing the element would put the
    /// collection below the minimum size.
    ///
    /// # Examples
    ///
    /// ```
    /// # use minsize::MinSizedVec;
    /// let mut v: MinSizedVec<_, 2> = MinSizedVec::new(vec![1, 2, 3]).unwrap();
    /// assert_eq!(v.remove(1), 2);
    /// assert_eq!(v, &[1, 3]);
    /// ```
    ///
    /// ```should_panic
    /// # use minsize::MinSizedVec;
    /// let mut v: MinSizedVec<_, 2> = MinSizedVec::new(vec![1, 2]).unwrap();
    /// // This will panic, since the minimum size is 2:
    /// v.remove(1);
    /// ```
    pub fn remove(&mut self, index: usize) -> T {
        if index >= self.len() {
            panic!(
                "index {} out of bounds for MinSizedVec of length {}",
                index,
                self.len()
            );
        }

        if self.len() == MINIMUM_SIZE {
            panic!(
                "removing element at index {} would underflow minimum size of {}",
                index, MINIMUM_SIZE
            );
        }

        self.0.remove(index)
    }

    /// Remove and and return the element at the given index from the collection.
    ///
    /// This will replace the empty slot left by the removal with the last element in the
    /// collection. This does not preserve ordering, but is O(1).
    ///
    /// # Panics
    ///
    /// This will panic if `index` is out of bounds, or if removing the element would put the
    /// collection below the minimum size.
    ///
    /// # Examples
    ///
    /// ```
    /// # use minsize::MinSizedVec;
    /// let mut v: MinSizedVec<_, 2> = MinSizedVec::new(vec![1, 2, 3]).unwrap();
    /// assert_eq!(v.swap_remove(0), 1);
    /// assert_eq!(v, &[3, 2]);
    /// ```
    ///
    /// ```should_panic
    /// # use minsize::MinSizedVec;
    /// let mut v: MinSizedVec<_, 2> = MinSizedVec::new(vec![1, 2]).unwrap();
    /// // This will panic, since the minimum size is 2:
    /// v.swap_remove(1);
    /// ```
    pub fn swap_remove(&mut self, index: usize) -> T {
        if index >= self.len() {
            panic!(
                "index {} out of bounds for MinSizedVec of length {}",
                index,
                self.len()
            );
        }

        if self.len() == MINIMUM_SIZE {
            panic!(
                "removing element at index {} would underflow minimum size of {}",
                index, MINIMUM_SIZE
            );
        }

        self.0.swap_remove(index)
    }

    /// Retain only the elements specified by the predicate, capped to the minimum size.
    ///
    /// This will remove all elements for which `f` returns `false` from the collection, until the
    /// minimum size has been reached. The closure will be called with each element starting from
    /// the beginning, but will stop being called after the maximum removable number of elements
    /// have been removed.
    ///
    /// # Examples
    ///
    /// ```
    /// # use minsize::MinSizedVec;
    /// let mut v: MinSizedVec<_, 2> = MinSizedVec::new(vec![1, 2, 3, 4, 5]).unwrap();
    /// v.capped_retain(|&e| e % 2 == 0);
    /// assert_eq!(v, &[2, 4]);
    /// ```
    ///
    /// The length remains capped, and will stop removing elements once it is reached:
    ///
    /// ```
    /// # use minsize::MinSizedVec;
    /// let mut v: MinSizedVec<_, 2> = MinSizedVec::new(vec![1, 2, 3, 4, 5]).unwrap();
    /// v.capped_retain(|_| false); // try to remove everything
    /// assert_eq!(v, &[4, 5]); // the last two elements remain
    /// ```
    pub fn capped_retain<F>(&mut self, mut f: F)
    where
        F: FnMut(&T) -> bool,
    {
        let mut allowed_to_remove = self.len() - MINIMUM_SIZE;

        if allowed_to_remove == 0 {
            return;
        }

        self.0.retain(|e| {
            let remove = allowed_to_remove != 0 && !f(e);

            if remove {
                allowed_to_remove -= 1;
            }

            !remove
        });
    }

    /// Retain only the elements specified by the predicate.
    ///
    /// This will remove all elements for which `f` returns `false` from the collection. The
    /// closure will be called with each element starting from the beginning.
    ///
    /// If the length after the removal operations is still greater than the minimum size, the
    /// collection is returned in the `Ok()` variant. If it is less than the minimum size, the
    /// collection is degraded to a plain [`Vec`] and return in the `Err(_)` variant.
    ///
    /// # Examples
    ///
    /// ```
    /// # use minsize::MinSizedVec;
    /// let mut v: MinSizedVec<_, 2> = MinSizedVec::new(vec![1, 2, 3, 4, 5]).unwrap();
    /// let v = v.try_retain(|&e| e % 2 == 0);
    /// assert_eq!(v, Ok(MinSizedVec::from([2, 4])));
    /// ```
    ///
    /// The length remains capped, and will stop removing elements once it is reached:
    ///
    /// ```
    /// # use minsize::MinSizedVec;
    /// let mut v: MinSizedVec<_, 2> = MinSizedVec::new(vec![1, 2, 3, 4, 5]).unwrap();
    /// let v = v.try_retain(|_| false); // try to remove everything
    /// assert_eq!(v, Err(vec![])); // a plain empty Vec remains
    /// ```
    pub fn try_retain<F>(mut self, f: F) -> Result<Self, Vec<T>>
    where
        F: FnMut(&T) -> bool,
    {
        self.0.retain(f);

        if self.0.len() >= MINIMUM_SIZE {
            Ok(self)
        } else {
            Err(self.0)
        }
    }

    /// Try to change the mininum size of the collection to `NEW`.
    ///
    /// This will inspect the current **runtime** length of the collection. If it is greater than
    /// or equal to `NEW`, a successful [`Result`] containing a collection with the updated minimum
    /// size is returned. If it is smaller, the original collection is returned in an `Err`
    /// variant.
    ///
    /// # Examples
    ///
    /// ```
    /// # use minsize::MinSizedVec;
    /// let v: MinSizedVec<_, 2> = MinSizedVec::new(vec![1, 2, 3, 4, 5]).unwrap();
    ///
    /// assert!(v.clone().change_minimum_size::<5>().is_ok());
    /// assert!(v.clone().change_minimum_size::<6>().is_err());
    /// ```
    pub fn change_minimum_size<const NEW: usize>(self) -> Result<MinSizedVec<T, NEW>, Self> {
        if self.len() >= NEW {
            Ok(MinSizedVec(self.0))
        } else {
            Err(self)
        }
    }

    /// Returns the number of elements the collection can hold without reallocating.
    pub fn capacity(&self) -> usize {
        self.0.capacity()
    }

    /// Returs the entire collection as a slice.
    fn as_slice(&self) -> &[T] {
        self
    }
}

/// **NOTE**: This impl block contains methods that are available if the minimum size is greater
/// than 0.
impl<T, const MINIMUM_SIZE: usize> MinSizedVec<T, MINIMUM_SIZE>
where
    MinSizedVec<T, MINIMUM_SIZE>: NotEmpty,
{
    /// Returns a mutable reference to the first element.
    ///
    /// # Examples
    ///
    /// ```
    /// # use minsize::MinSizedVec;
    /// let mut v = MinSizedVec::from([1, 2]);
    ///
    /// let first = v.first_mut();
    /// assert_eq!(*first, 1);
    ///
    /// *first = 3;
    /// assert_eq!(v, &[3, 2]);
    /// ```
    pub fn first_mut(&mut self) -> &mut T {
        self.0.first_mut().unwrap()
    }

    /// Returns a mutable reference to the last element.
    ///
    /// # Examples
    ///
    /// ```
    /// # use minsize::MinSizedVec;
    /// let mut v = MinSizedVec::from([1, 2]);
    ///
    /// let last = v.last_mut();
    /// assert_eq!(*last, 2);
    ///
    /// *last = 3;
    /// assert_eq!(v, &[1, 3]);
    /// ```
    pub fn last_mut(&mut self) -> &mut T {
        self.0.last_mut().unwrap()
    }

    /// Returns a reference to the first element.
    ///
    /// # Examples
    ///
    /// ```
    /// # use minsize::MinSizedVec;
    /// let mut v = MinSizedVec::from([1, 2]);
    ///
    /// let first = v.first();
    /// assert_eq!(*first, 1);
    /// ```
    pub fn first(&self) -> &T {
        self.0.first().unwrap()
    }

    /// Returns a reference to the last element.
    ///
    /// # Examples
    ///
    /// ```
    /// # use minsize::MinSizedVec;
    /// let mut v = MinSizedVec::from([1, 2]);
    ///
    /// let last = v.last();
    /// assert_eq!(*last, 2);
    /// ```
    pub fn last(&self) -> &T {
        self.0.last().unwrap()
    }
}

impl<T, const N: usize> fmt::Debug for MinSizedVec<T, N>
where
    T: fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0.fmt(f)
    }
}

impl<T, const N: usize> Default for MinSizedVec<T, N>
where
    T: Default,
{
    /// Creates a [`MinSizedVec`] filled to its minimum capacity with the default value for the
    /// contained type.
    fn default() -> Self {
        let mut vec = Vec::new();
        vec.resize_with(N, T::default);
        Self(vec)
    }
}

impl<T, const N: usize> Deref for MinSizedVec<T, N> {
    type Target = [T];

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<T, const N: usize> DerefMut for MinSizedVec<T, N> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

impl<T, I, const N: usize> Index<I> for MinSizedVec<T, N>
where
    I: SliceIndex<[T]>,
{
    type Output = <I as SliceIndex<[T]>>::Output;

    fn index(&self, index: I) -> &Self::Output {
        self.0.index(index)
    }
}

impl<T, I, const N: usize> IndexMut<I> for MinSizedVec<T, N>
where
    I: SliceIndex<[T]>,
{
    fn index_mut(&mut self, index: I) -> &mut Self::Output {
        self.0.index_mut(index)
    }
}

impl<T, U, const A: usize, const B: usize> PartialEq<MinSizedVec<U, B>> for MinSizedVec<T, A>
where
    T: PartialEq<U>,
{
    fn eq(&self, other: &MinSizedVec<U, B>) -> bool {
        self.as_slice() == other.as_slice()
    }
}

impl<T, U, const N: usize> PartialEq<[U]> for MinSizedVec<T, N>
where
    T: PartialEq<U>,
{
    fn eq(&self, other: &[U]) -> bool {
        self.as_slice() == other
    }
}

impl<'a, T, U, const N: usize> PartialEq<&'a [U]> for MinSizedVec<T, N>
where
    T: PartialEq<U>,
{
    fn eq(&self, other: &&'a [U]) -> bool {
        self.as_slice() == *other
    }
}

impl<T, U, const A: usize, const B: usize> PartialEq<[U; B]> for MinSizedVec<T, A>
where
    T: PartialEq<U>,
{
    fn eq(&self, other: &[U; B]) -> bool {
        self.as_slice() == other
    }
}

impl<'a, T, U, const A: usize, const B: usize> PartialEq<&'a [U; B]> for MinSizedVec<T, A>
where
    T: PartialEq<U>,
{
    fn eq(&self, other: &&'a [U; B]) -> bool {
        self.as_slice() == *other
    }
}

impl<T, const A: usize, const B: usize> PartialOrd<MinSizedVec<T, B>> for MinSizedVec<T, A>
where
    T: PartialOrd,
{
    fn partial_cmp(&self, other: &MinSizedVec<T, B>) -> Option<cmp::Ordering> {
        self.as_slice().partial_cmp(other)
    }
}

impl<T, const N: usize> AsRef<[T]> for MinSizedVec<T, N> {
    fn as_ref(&self) -> &[T] {
        self
    }
}

impl<T, const N: usize> AsMut<[T]> for MinSizedVec<T, N> {
    fn as_mut(&mut self) -> &mut [T] {
        self
    }
}

impl<T, const N: usize> IntoIterator for MinSizedVec<T, N> {
    type Item = T;

    type IntoIter = IntoIter<T>;

    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
}

impl<'a, T, const N: usize> IntoIterator for &'a MinSizedVec<T, N> {
    type Item = &'a T;

    type IntoIter = SliceIter<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<'a, T, const N: usize> IntoIterator for &'a mut MinSizedVec<T, N> {
    type Item = &'a mut T;

    type IntoIter = SliceIterMut<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter_mut()
    }
}

impl<T, const N: usize> Extend<T> for MinSizedVec<T, N> {
    fn extend<I: IntoIterator<Item = T>>(&mut self, iter: I) {
        self.0.extend(iter);
    }
}

impl<T, const N: usize> From<[T; N]> for MinSizedVec<T, N> {
    fn from(val: [T; N]) -> Self {
        let mut vec = Vec::new();
        vec.extend(val);
        MinSizedVec(vec)
    }
}

impl<T, const N: usize> TryFrom<Vec<T>> for MinSizedVec<T, N> {
    type Error = Vec<T>;

    fn try_from(value: Vec<T>) -> Result<Self, Self::Error> {
        if value.len() >= N {
            Ok(Self(value))
        } else {
            Err(value)
        }
    }
}
