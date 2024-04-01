# const-sub-array

[![crates.io](https://img.shields.io/crates/v/const-sub-array.svg)](https://crates.io/crates/const-sub-array)
[![docs.rs](https://img.shields.io/docsrs/const-sub-array)](https://docs.rs/const-sub-array)

<!-- cargo-rdme start -->

Allows to extract a fixed size sub-array out of an array with complie-time length and offset
checks.

Based on [`sub-array`](https://crates.io/crates/sub-array) crate.

## Example

Getting a sub array:

```rust
use const_sub_array::SubArray;

let arr: [u8; 7] = [1, 2, 3, 4, 5, 6, 7];

// Get a sub-array starting at offset 1 with 3 items.
let sub: &[u8; 3] = arr.sub_array_ref::<1, 3>();
assert_eq!(sub, &[2, 3, 4]);
```

Initializing an `[u8; 10]` array with `(u16, u32, u32)`:

```rust
use const_sub_array::SubArray;

let foo: u16 = 42;
let bar: u32 = 0x1234;
let baz: u32 = 0x5678;

let mut arr = [0u8; 10];
*arr.sub_array_mut::<0, 2>() = foo.to_be_bytes();
*arr.sub_array_mut::<2, 4>() = bar.to_be_bytes();
*arr.sub_array_mut::<6, 4>() = baz.to_be_bytes();

assert_eq!(
    arr,
    [
        0, 42, // foo
        0x0, 0x0, 0x12, 0x34, // bar
        0x0, 0x0, 0x56, 0x78, // baz
    ]
);
```

<!-- cargo-rdme end -->

License: MIT
