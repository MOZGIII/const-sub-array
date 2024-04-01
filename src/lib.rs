//! Allows to extract a fixed size sub-array out of an array with complie-time length and offset
//! checks.
//!
//! Based on [`sub-array`](https://crates.io/crates/sub-array) crate.
//!
//! # Example
//!
//! Getting a sub array:
//!
//! ```
//! use const_sub_array::SubArray;
//!
//! let arr: [u8; 7] = [1, 2, 3, 4, 5, 6, 7];
//!
//! // Get a sub-array starting at offset 1 with 3 items.
//! let sub: &[u8; 3] = arr.sub_array_ref::<1, 3>();
//! assert_eq!(sub, &[2, 3, 4]);
//! ```
//!
//! Initializing an `[u8; 10]` array with `(u16, u32, u32)`:
//!
//! ```
//! use const_sub_array::SubArray;
//!
//! let foo: u16 = 42;
//! let bar: u32 = 0x1234;
//! let baz: u32 = 0x5678;
//!
//! let mut arr = [0u8; 10];
//! *arr.sub_array_mut::<0, 2>() = foo.to_be_bytes();
//! *arr.sub_array_mut::<2, 4>() = bar.to_be_bytes();
//! *arr.sub_array_mut::<6, 4>() = baz.to_be_bytes();
//!
//! assert_eq!(
//!     arr,
//!     [
//!         0, 42, // foo
//!         0x0, 0x0, 0x12, 0x34, // bar
//!         0x0, 0x0, 0x56, 0x78, // baz
//!     ]
//! );
//! ```

#![no_std]

/// Apply a compile-time const generic assertion.
///
/// Based on <https://github.com/nvzqz/static-assertions/issues/40#issuecomment-846228355>.
#[macro_export]
macro_rules! const_assert {
    ($($list:ident : $ty:ty),* => $expr:expr) => {{
        struct Assert<$(const $list: usize,)*>;
        impl<$(const $list: $ty,)*> Assert<$($list,)*> {
            const OK: u8 = 0 - !($expr) as u8;
        }
        Assert::<$($list,)*>::OK
    }};
    ($expr:expr) => {
        const OK: u8 = 0 - !($expr) as u8;
    };
}

/// Array that can be slice into a smaller sub-array.
///
/// See the [crate] level reference.
///
/// # Safety
///
/// Implementation guarantees to generate *compile-time* errors when the requested sub-array
/// `length + offset` combinations exceed the size of the array that the sub-array is being
/// extracted from.
pub unsafe trait SubArray {
    /// The value type of this array.
    ///
    /// This is the `T` in `[T; N]` on regular arrays.
    type Item;

    /// Get a reference to a sub-array of length `M` starting at `OFFSET`.
    ///
    /// # Safety
    ///
    /// Implementation guarantees to generate a *compile-time* error
    /// when `M + OFFSET` is greater than the size of the array
    /// that sub-array is being extracted from.
    ///
    /// # Example
    /// ```
    /// use const_sub_array::SubArray;
    ///
    /// let arr: [u8; 5] = [9, 8, 7, 6, 5];
    ///
    /// // Get a sub-array starting at offset 3 and size 2.
    /// let sub: &[u8; 2] = arr.sub_array_ref::<3, 2>();
    /// assert_eq!(sub, &[6, 5]);
    /// ```
    fn sub_array_ref<const OFFSET: usize, const M: usize>(&self) -> &[Self::Item; M];

    /// Get a mutable reference to a sub-array of length `M` starting at `OFFSET`.
    ///
    /// # Example
    /// ```
    /// use const_sub_array::SubArray;
    ///
    /// let mut arr: [u8; 5] = [9, 8, 7, 6, 5];
    ///
    /// // Get a mutable sub-array starting at offset 0 and size 2.
    /// let sub: &mut [u8; 2] = arr.sub_array_mut::<0, 2>();
    /// assert_eq!(sub, &mut [9, 8]);
    /// ```
    fn sub_array_mut<const OFFSET: usize, const M: usize>(&mut self) -> &mut [Self::Item; M];
}

/// Implementation on regular arrays.
unsafe impl<T, const N: usize> SubArray for [T; N] {
    type Item = T;

    #[allow(unsafe_code)]
    fn sub_array_ref<const OFFSET: usize, const M: usize>(&self) -> &[Self::Item; M] {
        const_assert!(OFFSET: usize, M: usize, N: usize => OFFSET + M <= N);
        unsafe { &*(self.as_ptr().add(OFFSET) as *const [T; M]) }
    }

    #[allow(unsafe_code)]
    fn sub_array_mut<const OFFSET: usize, const M: usize>(&mut self) -> &mut [Self::Item; M] {
        const_assert!(OFFSET: usize, M: usize, N: usize => OFFSET + M <= N);
        unsafe { &mut *(self.as_ptr().add(OFFSET) as *mut [T; M]) }
    }
}

/// Implementation on mutable references.
unsafe impl<T> SubArray for &mut T
where
    T: SubArray,
{
    type Item = T::Item;

    fn sub_array_ref<const OFFSET: usize, const N: usize>(&self) -> &[Self::Item; N] {
        (**self).sub_array_ref::<OFFSET, N>()
    }

    fn sub_array_mut<const OFFSET: usize, const N: usize>(&mut self) -> &mut [Self::Item; N] {
        (**self).sub_array_mut::<OFFSET, N>()
    }
}

#[cfg(test)]
mod tests {
    extern crate alloc;

    use alloc::string::String;
    use alloc::string::ToString;

    use super::*;

    #[test]
    fn empty_ref() {
        let arr = [0_u8; 0];
        assert_eq!(arr.sub_array_ref::<0, 0>(), &[]);
    }

    #[test]
    fn empty_mut() {
        let mut arr = [0_u8; 0];
        assert_eq!(arr.sub_array_mut::<0, 0>(), &mut []);
    }

    #[test]
    fn full_ref() {
        let arr = [1, 2, 3_i8];
        assert_eq!(arr.sub_array_ref::<0, 3>(), &[1, 2, 3]);
    }

    #[test]
    fn full_mut() {
        let mut arr = [1, 2, 3_i8];
        assert_eq!(arr.sub_array_mut::<0, 3>(), &mut [1, 2, 3]);
    }

    #[test]
    fn first_ref() {
        let arr = [1, 2, 3_u16];
        assert_eq!(arr.sub_array_ref::<0, 1>(), &[1]);
    }

    #[test]
    fn first_mut() {
        let mut arr = [1, 2, 3_u16];
        assert_eq!(arr.sub_array_mut::<0, 1>(), &mut [1]);
    }

    #[test]
    fn middle_ref() {
        let arr = [1, 2, 3_i16];
        assert_eq!(arr.sub_array_ref::<1, 1>(), &[2]);
    }

    #[test]
    fn middle_mut() {
        let mut arr = [1, 2, 3_i16];
        assert_eq!(arr.sub_array_mut::<1, 1>(), &mut [2]);
    }

    #[test]
    fn last_ref() {
        let arr = [1, 2, 3_i16];
        assert_eq!(arr.sub_array_ref::<2, 1>(), &[3]);
    }

    #[test]
    fn last_mut() {
        let mut arr = [1, 2, 3_i16];
        assert_eq!(arr.sub_array_mut::<2, 1>(), &mut [3]);
    }

    #[derive(Debug, PartialEq, Eq)]
    struct NotClone(&'static str);

    const NOT_CLONE_ARRAY: [NotClone; 5] = [
        NotClone("abc"),
        NotClone("foo"),
        NotClone("bar"),
        NotClone("qux"),
        NotClone("fox"),
    ];

    #[test]
    fn not_clone_ref() {
        let exp_arr = [NotClone("foo"), NotClone("bar"), NotClone("qux")];
        let arr = NOT_CLONE_ARRAY;
        assert_eq!(arr.sub_array_ref::<1, 3>(), &exp_arr);
    }

    #[test]
    fn not_clone_mut() {
        let mut exp_arr = [NotClone("foo"), NotClone("bar"), NotClone("qux")];
        let mut arr = NOT_CLONE_ARRAY;
        assert_eq!(arr.sub_array_mut::<1, 3>(), &mut exp_arr);
    }

    #[test]
    fn some_strings() {
        let arr: [String; 5] = NOT_CLONE_ARRAY.map(|s| s.0.to_string());
        assert_eq!(
            arr.sub_array_ref::<2, 2>(),
            &[String::from("bar"), String::from("qux")]
        );
    }
}
