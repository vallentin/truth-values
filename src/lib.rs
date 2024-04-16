//! Tiny, zero-dependency, zero-allocation*, `no_std` library for generating all possible
//! combinations of `n` [`bool`]s. Useful for testing [boolean functions],
//! verifying [logical equivalence], and generating [truth tables].
//! _\*Optional `alloc` feature for [`Vec`] related functions._
//!
//! [boolean functions]: https://en.wikipedia.org/wiki/Boolean_function
//! [logical equivalence]: https://en.wikipedia.org/wiki/Logical_equivalence
//! [truth tables]: https://en.wikipedia.org/wiki/Truth_table
//!
//! # Example - `each()` and `each_const()`
//!
//! Consider implementing an interpreter or optimizer, and now you
//! want to assert [logical equivalence] between expressions, e.g.
//! asserting [De Morgan's laws]:
//!
//! - not (A or B)  = (not A) and (not B)
//! - not (A and B) = (not A) or (not B)
//!
//! [De Morgan's laws]: https://en.wikipedia.org/wiki/De_Morgan%27s_laws
//!
//! Using [const generic variant](crate::each_const), i.e. where `N` is const:
//!
//! ```
//! # use truth_values::each_const;
//! each_const(|[a, b]| {
//!     assert_eq!(!(a || b), !a && !b);
//!     assert_eq!(!(a && b), !a || !b);
//! });
//! // The closure is called for each combination of 2 `bool`s, i.e.:
//! // [false, false]
//! // [true,  false]
//! // [false, true]
//! // [true,  true]
//! ```
//!
//! Using [non-const generic variant](crate::each), i.e. where `n` can be dynamic:
//!
//! ```
//! # use truth_values::each;
//! each(2, |bools| match bools {
//!     &[a, b] => {
//!         assert_eq!(!(a || b), !a && !b);
//!         assert_eq!(!(a && b), !a || !b);
//!     }
//!     _ => unreachable!(),
//! });
//! // The closure is called for each combination of 2 `bool`s, i.e.:
//! // &[false, false]
//! // &[true,  false]
//! // &[false, true]
//! // &[true,  true]
//! ```
//!
//! # Example - `gen()` and `gen_const()`
//!
//! Alternatively, use [`gen()` functions](crate#functions) to obtain
//! an [`Iterator`] for generating all combinations. This could be used
//! to e.g. map each combination into an `Expr` for an [AST], to easily
//! generate all `Expr` combinations to verify their evaluation.
//!
//! [AST]: https://en.wikipedia.org/wiki/Abstract_syntax_tree
//!
//! Using [const generic variant](crate::gen_const), i.e. where `N` is const:
//!
//! ```
//! #[derive(PartialEq, Debug)]
//! enum Expr {
//!     Bool(bool),
//!     And(Box<Self>, Box<Self>),
//!     // ...
//! }
//!
//! impl Expr {
//!     fn and(lhs: Self, rhs: Self) -> Self {
//!         Self::And(Box::new(lhs), Box::new(rhs))
//!     }
//! }
//!
//! let exprs = truth_values::gen_const()
//!     .map(|[a, b]| {
//!         Expr::and(Expr::Bool(a), Expr::Bool(b))
//!     })
//!     .collect::<Vec<_>>();
//!
//! assert_eq!(
//!     exprs,
//!     [
//!         Expr::and(Expr::Bool(false), Expr::Bool(false)),
//!         Expr::and(Expr::Bool(true),  Expr::Bool(false)),
//!         Expr::and(Expr::Bool(false), Expr::Bool(true)),
//!         Expr::and(Expr::Bool(true),  Expr::Bool(true)),
//!     ]
//! );
//! ```
//!
//! Using [non-const generic variant](crate::gen_slice), i.e. where `n` can be dynamic:
//!
//! ```
//! # #[derive(PartialEq, Debug)]
//! # enum Expr {
//! #     Bool(bool),
//! #     And(Box<Self>, Box<Self>),
//! # }
//! #
//! # impl Expr {
//! #     fn and(lhs: Expr, rhs: Expr) -> Expr {
//! #         Expr::And(Box::new(lhs), Box::new(rhs))
//! #     }
//! # }
//! #
//! let exprs = truth_values::gen_slice(2, |bools| {
//!     match bools {
//!         &[a, b] => {
//!             Expr::and(Expr::Bool(a), Expr::Bool(b))
//!         }
//!         _ => unreachable!(),
//!     }
//! })
//! .collect::<Vec<_>>();
//!
//! assert_eq!(
//!     exprs,
//!     [
//!         Expr::and(Expr::Bool(false), Expr::Bool(false)),
//!         Expr::and(Expr::Bool(true),  Expr::Bool(false)),
//!         Expr::and(Expr::Bool(false), Expr::Bool(true)),
//!         Expr::and(Expr::Bool(true),  Expr::Bool(true)),
//!     ]
//! );
//! ```
//!
//! # Combinations of 1, 2, 3, 4 `bool`s
//!
//! <table>
//! <tr>
//! <td style="text-align: center;">
//!
//! ```
//! # use truth_values::gen_const;
//! gen_const::<1>()
//! # ;
//! ```
//!
//! </td>
//! <td style="text-align: center;">
//!
//! ```
//! # use truth_values::gen_const;
//! gen_const::<2>()
//! # ;
//! ```
//!
//! </td>
//! <td style="text-align: center;">
//!
//! ```
//! # use truth_values::gen_const;
//! gen_const::<3>()
//! # ;
//! ```
//!
//! </td>
//! <td style="text-align: center;">
//!
//! ```
//! # use truth_values::gen_const;
//! gen_const::<4>()
//! # ;
//! ```
//!
//! </td>
//! </tr>
//! <tr>
//! <td style="vertical-align: top;">
//!
//! ```
//! # [
//! [false]
//! # ,
//! [true]
//! # ];
//! ```
//!
//! </td>
//! <td style="vertical-align: top;">
//!
//! ```
//! # [
//! [false, false]
//! # ,
//! [true,  false]
//! # ,
//! [false, true]
//! # ,
//! [true,  true]
//! # ];
//! ```
//!
//! </td>
//! <td style="vertical-align: top;">
//!
//! ```
//! # [
//! [false, false, false]
//! # ,
//! [true,  false, false]
//! # ,
//! [false, true,  false]
//! # ,
//! [true,  true,  false]
//! # ,
//! [false, false, true]
//! # ,
//! [true,  false, true]
//! # ,
//! [false, true,  true]
//! # ,
//! [true,  true,  true]
//! # ];
//! ```
//!
//! </td>
//! <td style="vertical-align: top;">
//!
//! ```
//! # [
//! [false, false, false, false]
//! # ,
//! [true,  false, false, false]
//! # ,
//! [false, true,  false, false]
//! # ,
//! [true,  true,  false, false]
//! # ,
//! [false, false, true,  false]
//! # ,
//! [true,  false, true,  false]
//! # ,
//! [false, true,  true,  false]
//! # ,
//! [true,  true,  true,  false]
//! # ,
//! [false, false, false, true]
//! # ,
//! [true,  false, false, true]
//! # ,
//! [false, true,  false, true]
//! # ,
//! [true,  true,  false, true]
//! # ,
//! [false, false, true,  true]
//! # ,
//! [true,  false, true,  true]
//! # ,
//! [false, true,  true,  true]
//! # ,
//! [true,  true,  true,  true]
//! # ];
//! ```
//!
//! </td>
//! </tr>
//! </table>
//!
//! # Implementation
//!
//! The [`gen()` functions](crate#functions) return an [`Iterator`], which
//! additionally specializes [`size_hint()`], [`count()`], [`nth()`], [`last()`].
//!
//! The [`Iterator`] also implements:
//!
//! - [`DoubleEndedIterator`] implementing [`next_back()`] and [`nth_back()`]
//! - [`ExactSizeIterator`] implementing [`len()`]
//! - [`FusedIterator`]
//!
//! # Warning
//!
//! The amount of combinations is exponential!
//! The number of combinations for `N` boolean variables is <code>2<sup>N</sup></code>.
//! In short, **10 variables** produce **1024 combinations**, but **20 variables**
//! produce over **1 million combinations**.
//!
//! _Just alone exhausting the generator for **30 variables**, i.e. over **1 billion
//! combinations**, takes a handful of seconds on my machine._
//!
//! Ideally, if used to test expressions, then there will likely only be a handful of
//! variables. However, if user input is accepted, then it might be worth guarding and
//! limiting the number of variables.
//!
//! So even though up to [`MAX`] (`63`) variables for 64-bit platforms
//! is supported, it is probably undesirable to even attempt to process
//! that many variables.
//!
//! [`MAX`]: crate::MAX
//!
//! [`size_hint()`]: https://doc.rust-lang.org/std/iter/trait.Iterator.html#method.size_hint
//! [`count()`]: https://doc.rust-lang.org/std/iter/trait.Iterator.html#method.count
//! [`nth()`]: https://doc.rust-lang.org/std/iter/trait.Iterator.html#method.nth
//! [`last()`]: https://doc.rust-lang.org/std/iter/trait.Iterator.html#method.last
//! [`next_back()`]: https://doc.rust-lang.org/std/iter/trait.DoubleEndedIterator.html#tymethod.next_back
//! [`nth_back()`]: https://doc.rust-lang.org/std/iter/trait.DoubleEndedIterator.html#method.nth_back
//! [`len()`]: https://doc.rust-lang.org/std/iter/trait.ExactSizeIterator.html#method.len

#![no_std]
#![forbid(unsafe_code)]
#![forbid(elided_lifetimes_in_paths)]
#![cfg_attr(debug_assertions, allow(missing_docs, missing_debug_implementations,))]
#![warn(clippy::all)]

#[cfg(feature = "alloc")]
extern crate alloc;

use core::array;
use core::iter::FusedIterator;
use core::ops::Range;

#[cfg(feature = "alloc")]
use alloc::{vec, vec::Vec};

/// Maximum number of variables supported by
/// [`gen()` functions](crate#functions).
///
/// - `15` variables is supported on 16-bit targets
/// - `31` variables is supported on 32-bit targets
/// - `63` variables is supported on 64-bit targets
///
/// ```
/// // Assuming `usize` is 64 bits, i.e. `u64`
/// assert_eq!(truth_values::MAX, 63);
/// ```
///
/// Use <code>[count]\(n)</code> to calculate how many
/// combinations `n` variables produces.
///
/// See [warning notice in crate root](crate#warning).
pub const MAX: usize = (usize::BITS - 1) as usize;

/// Returns `true` if `n` variables is supported
/// by [`gen()` functions](crate#functions), i.e.
/// <code>n <= [MAX]</code>.
///
/// - `15` variables is supported on 16-bit targets
/// - `31` variables is supported on 32-bit targets
/// - `63` variables is supported on 64-bit targets
///
/// ```
/// // Assuming `usize` is 64 bits, i.e. `u64`
/// assert_eq!(truth_values::is_supported(63), true);
/// assert_eq!(truth_values::is_supported(64), false);
/// ```
///
/// See [warning notice in crate root](crate#warning).
#[inline]
pub const fn is_supported(n: usize) -> bool {
    n <= MAX
}

/// Returns `Some` with the number of combinations that `n` variables produces.
///
/// Returns `None` if `n` variables would produce more than what can be represented.
///
/// - `1` variable produces `2` combinations
/// - `2` variables produces `4` combinations
/// - `3` variables produces `8` combinations
/// - `4` variables produces `16` combinations
/// - [`MAX`] variables produces <code>[count]\([MAX])</code> combinations
///
/// Use <code>[is_supported]\(n)</code> or <code>[count]\(n).is_some()</code>
/// to check if `n` variables is supported.
///
/// - `15` variables is supported on 16-bit targets
/// - `31` variables is supported on 32-bit targets
/// - `63` variables is supported on 64-bit targets
///
/// See [warning notice in crate root](crate#warning).
///
/// # Example
///
/// ```
/// # use truth_values::count;
/// assert_eq!(count(0), Some(0));
///
/// assert_eq!(count(1), Some(2));
/// assert_eq!(count(2), Some(4));
/// assert_eq!(count(3), Some(8));
/// assert_eq!(count(4), Some(16));
/// assert_eq!(count(5), Some(32));
/// assert_eq!(count(6), Some(64));
/// assert_eq!(count(7), Some(128));
/// assert_eq!(count(8), Some(256));
/// assert_eq!(count(9), Some(512));
/// assert_eq!(count(10), Some(1024));
/// assert_eq!(count(11), Some(2048));
/// assert_eq!(count(12), Some(4096));
/// assert_eq!(count(13), Some(8192));
/// assert_eq!(count(14), Some(16384));
///
/// assert_eq!(count(100), None);
/// ```
#[inline]
pub const fn count(n: usize) -> Option<usize> {
    if n == 0 {
        Some(0)
    } else if n > MAX {
        None
    } else {
        let n = n as u32;
        1_usize.checked_shl(n)
    }
}

/// Returns an [`Iterator`] producing all possible combinations of `[bool; N]`.
///
/// See also [`gen()`] for non-const generic variant.
///
/// See also [implementation](crate#implementation) for more information
/// about the [`Iterator`] implementation.
///
/// # Panics
///
/// Panics if `N` is larger than the [`MAX`] number of supported variables.
/// _However, you likely have other problems, if you encounter this._
///
/// See also <code>[count]\(N)</code> and <code>[is_supported]\(N)</code>.
///
/// # Example
///
/// See [crate root](crate) for more examples.
///
/// ```
/// let combinations = truth_values::gen_const()
///     .map(|[a, b]| {
///         (a, b)
///     })
///     .collect::<Vec<_>>();
///
/// assert_eq!(
///     combinations,
///     [
///         (false, false),
///         (true, false),
///         (false, true),
///         (true, true),
///     ]
/// );
/// ```
#[inline]
pub fn gen_const<const N: usize>(
) -> impl DoubleEndedIterator<Item = [bool; N]> + ExactSizeIterator + FusedIterator {
    ConstBoolsGenerator::new()
}

/// Returns an [`Iterator`] producing all possible combinations of `n` [`bool`]s,
/// in the form of individual [`Bools`] iterators.
///
/// Alternatively, use [`gen_slice()`] or [`gen_vec_slice()`]
/// to receives `&[bool]` instead, where <code>[len()] == n</code>.
///
/// See also [`gen_const()`] for const generic variant.
///
/// See also [implementation](crate#implementation) for more information
/// about the [`Iterator`] implementation.
///
/// # Panics
///
/// Panics if `n` is larger than the [`MAX`] number of supported variables.
/// _However, you likely have other problems, if you encounter this._
///
/// See also <code>[count]\(n)</code> and <code>[is_supported]\(n)</code>.
///
/// # Example
///
/// See [crate root](crate) for more examples.
///
/// ```
/// let n = 2;
/// let combinations = truth_values::gen(n)
///     .map(|mut bools| {
///         (bools.next().unwrap(), bools.next().unwrap())
///     })
///     .collect::<Vec<_>>();
///
/// assert_eq!(
///     combinations,
///     [
///         (false, false),
///         (true, false),
///         (false, true),
///         (true, true),
///     ]
/// );
/// ```
///
/// [len()]: slice::len
#[inline]
pub fn gen(n: usize) -> impl DoubleEndedIterator<Item = Bools> + ExactSizeIterator + FusedIterator {
    BoolsGenerator::new(n)
}

/// Returns an [`Iterator`] producing `T` for each possible combinations
/// of `n` [`bool`]s.
///
/// Each combination is mapped from `&[bool] -> T` using `f`,
/// where `f` receives `&[bool]` where <code>[len()] == n</code>.
///
/// See also [`gen_const()`] for const generic variant.
///
/// See also [implementation](crate#implementation) for more information
/// about the [`Iterator`] implementation.
///
/// # Memory
///
/// The returned [`Iterator`] stores a <code>[bool; [MAX]]</code> on the stack.
///
/// Alternatively, [`gen_vec_slice()`] stores a
/// <code>[Vec]\<bool>::[with_capacity]\(n)</code>
/// on the stack.
///
/// See also [`gen_with_buffer()`] for using a custom buffer.
///
/// # Panics
///
/// Panics if `n` is larger than the [`MAX`] number of supported variables.
/// _However, you likely have other problems, if you encounter this._
///
/// See also <code>[count]\(n)</code> and <code>[is_supported]\(n)</code>.
///
/// # Example
///
/// See [crate root](crate) for more examples.
///
/// ```
/// let n = 2;
/// let combinations = truth_values::gen_slice(n, |bools| {
///     match bools {
///         &[a, b] => (a, b),
///         _ => unreachable!(),
///     }
/// })
/// .collect::<Vec<_>>();
///
/// assert_eq!(
///     combinations,
///     [
///         (false, false),
///         (true, false),
///         (false, true),
///         (true, true),
///     ]
/// );
/// ```
///
/// [with_capacity]: Vec::with_capacity
/// [len()]: slice::len
#[inline]
pub fn gen_slice<T, F>(
    n: usize,
    mut f: F,
) -> impl DoubleEndedIterator<Item = T> + ExactSizeIterator + FusedIterator
where
    for<'a> F: FnMut(&[bool]) -> T,
{
    let mut bools = [false; MAX];
    gen(n).map(move |values| {
        let bools = values.fill_bools_into(&mut bools);
        f(bools)
    })
}

/// Returns an [`Iterator`] producing <code>[Vec]<[bool]></code>
/// for each possible combinations of `n` [`bool`]s.
///
/// **Note:** If a <code>[Vec]<[bool]></code> is **not needed**
/// for **each combination**, then consider using [`gen_slice()`]
/// or [`gen_vec_slice()`] instead.
///
/// See also [implementation](crate#implementation) for more information
/// about the [`Iterator`] implementation.
///
/// # Panics
///
/// Panics if `n` is larger than the [`MAX`] number of supported variables.
/// _However, you likely have other problems, if you encounter this._
///
/// See also <code>[count]\(n)</code> and <code>[is_supported]\(n)</code>.
///
/// # Example
///
/// See [crate root](crate) for more examples.
///
/// ```
/// let n = 2;
/// let combinations = truth_values::gen_vec(n).collect::<Vec<_>>();
///
/// assert_eq!(
///     combinations,
///     [
///         vec![false, false],
///         vec![true, false],
///         vec![false, true],
///         vec![true, true],
///     ]
/// );
/// ```
#[cfg(feature = "alloc")]
#[inline]
pub fn gen_vec(
    n: usize,
) -> impl DoubleEndedIterator<Item = Vec<bool>> + ExactSizeIterator + FusedIterator {
    gen(n).map(Iterator::collect)
}

/// Returns an [`Iterator`] producing `T` for each possible combinations
/// of `n` [`bool`]s.
///
/// Each combination is mapped from `&[bool] -> T` using `f`,
/// where `f` receives `&[bool]` where <code>[len()] == n</code>.
///
/// See also [`gen_const()`] for const generic variant.
///
/// See also [implementation](crate#implementation) for more information
/// about the [`Iterator`] implementation.
///
/// # Memory
///
/// The returned [`Iterator`] stores a
/// <code>[Vec]\<bool>::[with_capacity]\(n)</code>
/// on the stack.
///
/// Alternatively, [`gen_slice()`] stores a <code>[bool; [MAX]]</code>
/// on the stack.
///
/// See also [`gen_with_buffer()`] for using a custom buffer.
///
/// # Panics
///
/// Panics if `n` is larger than the [`MAX`] number of supported variables.
/// _However, you likely have other problems, if you encounter this._
///
/// See also <code>[count]\(n)</code> and <code>[is_supported]\(n)</code>.
///
/// # Example
///
/// See [crate root](crate) for more examples.
///
/// ```
/// let n = 2;
/// let combinations = truth_values::gen_vec_slice(n, |bools| {
///     match bools {
///         &[a, b] => (a, b),
///         _ => unreachable!(),
///     }
/// })
/// .collect::<Vec<_>>();
///
/// assert_eq!(
///     combinations,
///     [
///         (false, false),
///         (true, false),
///         (false, true),
///         (true, true),
///     ]
/// );
/// ```
///
/// [with_capacity]: Vec::with_capacity
/// [len()]: slice::len
#[cfg(feature = "alloc")]
#[inline]
pub fn gen_vec_slice<T, F>(
    n: usize,
    mut f: F,
) -> impl DoubleEndedIterator<Item = T> + ExactSizeIterator + FusedIterator
where
    for<'a> F: FnMut(&[bool]) -> T,
{
    let mut bools = vec![false; n];
    gen(n).map(move |mut values| {
        let bools = bools.as_mut();
        values.fill_into(bools);
        f(bools)
    })
}

/// Returns an [`Iterator`] producing `T` for each possible combinations
/// of `n` [`bool`]s.
///
/// Each combination is mapped from `&[bool] -> T` using `f`,
/// where `f` receives `&[bool]` where <code>[len()] == n</code>.
///
/// The `buffer` only needs to be as big as the largest used `n`.
/// Whereas [`gen_slice()`] which always uses a
/// <code>[[bool]; [MAX]]</code>.
///
/// See also [implementation](crate#implementation) for more information
/// about the [`Iterator`] implementation.
///
/// # Panics
///
/// - Panics if <code>buffer.[len()] < n</code>
/// - Panics if `n` is larger than the [`MAX`] number of supported variables.
///   _However, you likely have other problems, if you encounter this._
///
/// See also <code>[count]\(n)</code> and <code>[is_supported]\(n)</code>.
///
/// # Example
///
/// See [crate root](crate) for more examples.
///
/// ```
/// // buffer only needs to be as big as the largest `n`
/// let mut buffer = [false; 5];
///
/// // `3 <= buffer.len()` so `buffer` can be used
/// let n = 3;
/// let combinations = truth_values::gen_with_buffer(n, &mut buffer, |bools| {
///     match bools {
///         &[a, b, c] => (a, b, c),
///         _ => unreachable!(),
///     }
/// })
/// .collect::<Vec<_>>();
///
/// assert_eq!(
///     combinations,
///     [
///         (false, false, false),
///         (true, false, false),
///         (false, true, false),
///         (true, true, false),
///         (false, false, true),
///         (true, false, true),
///         (false, true, true),
///         (true, true, true),
///     ]
/// );
///
/// // `2 <= buffer.len()` so `buffer` can be reused
/// let n = 2;
/// let combinations = truth_values::gen_with_buffer(n, &mut buffer, |bools| {
///     match bools {
///         &[a, b] => (a, b),
///         _ => unreachable!(),
///     }
/// })
/// .collect::<Vec<_>>();
///
/// assert_eq!(
///     combinations,
///     [
///         (false, false),
///         (true, false),
///         (false, true),
///         (true, true),
///     ]
/// );
/// ```
///
/// [len()]: slice::len
pub fn gen_with_buffer<'a, T, F>(
    n: usize,
    buffer: &'a mut [bool],
    mut f: F,
) -> impl DoubleEndedIterator<Item = T> + ExactSizeIterator + FusedIterator + 'a
where
    for<'b> F: FnMut(&'b [bool]) -> T + 'a,
{
    if n > buffer.len() {
        panic!("buffer too small {n} > {}", buffer.len());
    }
    let buffer = &mut buffer[..n];

    gen(n).map(move |mut values| {
        values.fill_into(buffer);
        f(buffer)
    })
}

/// Shorthand for <code>[gen_const]\().[for_each]\(f)</code>.
///
/// See [`gen_const()`] for more information.
///
/// See [`each()`] for the non-const generic variant.
///
/// # Example
///
/// See [crate root](crate) for more examples.
///
/// ```
/// # use truth_values::each_const;
/// #
/// each_const(|[a]| {
///     println!("{a}");
/// });
/// // Outputs:
/// // false
/// // true
///
/// each_const(|[a, b]| {
///     println!("{a} {b}");
/// });
/// // Outputs:
/// // false false
/// // true  false
/// // false true
/// // true  true
///
/// each_const(|[a, b, c, d]| {
///     println!("{a} {b} {c} {d}");
/// });
/// // Outputs:
/// // false false false false
/// // true  false false false
/// // false true  false false
/// // true  true  false false
/// // false false true  false
/// // true  false true  false
/// // false true  true  false
/// // true  true  true  false
/// // false false false true
/// // true  false false true
/// // false true  false true
/// // true  true  false true
/// // false false true  true
/// // true  false true  true
/// // false true  true  true
/// // true  true  true  true
/// ```
///
/// [for_each]: Iterator::for_each
#[inline]
pub fn each_const<const N: usize, F>(f: F)
where
    F: FnMut([bool; N]),
{
    gen_const::<N>().for_each(f)
}

/// Shorthand for <code>[gen_slice]\(n, f).[for_each]\(|_| ())</code>.
///
/// See [`gen_slice()`] for more information.
///
/// See [`each_const()`] for the const generic variant.
///
/// # Example
///
/// See [crate root](crate) for more examples.
///
/// ```
/// # use truth_values::each;
/// each(1, |bools| {
///     println!("{:?}", bools);
/// });
/// // Outputs:
/// // [false]
/// // [true]
///
/// each(2, |bools| {
///     println!("{:?}", bools);
/// });
/// // Outputs:
/// // [false, false]
/// // [true, false]
/// // [false, true]
/// // [true, true]
///
/// each(4, |bools| {
///     println!("{:?}", bools);
/// });
/// // Outputs:
/// // [false, false, false, false]
/// // [true, false, false, false]
/// // [false, true, false, false]
/// // [true, true, false, false]
/// // [false, false, true, false]
/// // [true, false, true, false]
/// // [false, true, true, false]
/// // [true, true, true, false]
/// // [false, false, false, true]
/// // [true, false, false, true]
/// // [false, true, false, true]
/// // [true, true, false, true]
/// // [false, false, true, true]
/// // [true, false, true, true]
/// // [false, true, true, true]
/// // [true, true, true, true]
/// ```
///
/// [for_each]: Iterator::for_each
#[inline]
pub fn each<F>(n: usize, f: F)
where
    for<'a> F: FnMut(&'a [bool]),
{
    gen_slice(n, f).for_each(drop);
}

/// Shorthand for <code>[gen_vec_slice]\(n, f).[for_each]\(|_| ())</code>.
///
/// See [`gen_vec_slice()`] for more information.
///
/// See [`each_const()`] for the const generic variant.
///
/// # Example
///
/// See [crate root](crate) for more examples.
///
/// ```
/// # use truth_values::each_vec_slice;
/// each_vec_slice(1, |bools| {
///     println!("{:?}", bools);
/// });
/// // Outputs:
/// // [false]
/// // [true]
///
/// each_vec_slice(2, |bools| {
///     println!("{:?}", bools);
/// });
/// // Outputs:
/// // [false, false]
/// // [true, false]
/// // [false, true]
/// // [true, true]
///
/// each_vec_slice(4, |bools| {
///     println!("{:?}", bools);
/// });
/// // Outputs:
/// // [false, false, false, false]
/// // [true, false, false, false]
/// // [false, true, false, false]
/// // [true, true, false, false]
/// // [false, false, true, false]
/// // [true, false, true, false]
/// // [false, true, true, false]
/// // [true, true, true, false]
/// // [false, false, false, true]
/// // [true, false, false, true]
/// // [false, true, false, true]
/// // [true, true, false, true]
/// // [false, false, true, true]
/// // [true, false, true, true]
/// // [false, true, true, true]
/// // [true, true, true, true]
/// ```
///
/// [for_each]: Iterator::for_each
#[cfg(feature = "alloc")]
#[inline]
pub fn each_vec_slice<F>(n: usize, f: F)
where
    for<'a> F: FnMut(&[bool]),
{
    let mut bools = vec![false; n];
    each_with_buffer(n, &mut bools, f);
}

/// Shorthand for <code>[gen_with_buffer]\(n, buffer, f).[for_each]\(|_| ())</code>.
///
/// See [`each_with_buffer()`] for more information.
///
/// # Example
///
/// See [crate root](crate) for more examples.
///
/// ```
/// # use truth_values::each_with_buffer;
/// #
/// // Buffer only needs to be as big as the largest `n`
/// let mut buffer = [false; 5];
///
/// each_with_buffer(1, &mut buffer, |bools| {
///     println!("{:?}", bools);
/// });
/// // Outputs:
/// // [false]
/// // [true]
///
/// each_with_buffer(2, &mut buffer, |bools| {
///     println!("{:?}", bools);
/// });
/// // Outputs:
/// // [false, false]
/// // [true, false]
/// // [false, true]
/// // [true, true]
///
/// each_with_buffer(4, &mut buffer, |bools| {
///     println!("{:?}", bools);
/// });
/// // Outputs:
/// // [false, false, false, false]
/// // [true, false, false, false]
/// // [false, true, false, false]
/// // [true, true, false, false]
/// // [false, false, true, false]
/// // [true, false, true, false]
/// // [false, true, true, false]
/// // [true, true, true, false]
/// // [false, false, false, true]
/// // [true, false, false, true]
/// // [false, true, false, true]
/// // [true, true, false, true]
/// // [false, false, true, true]
/// // [true, false, true, true]
/// // [false, true, true, true]
/// // [true, true, true, true]
/// ```
///
/// [for_each]: Iterator::for_each
#[inline]
pub fn each_with_buffer<F>(n: usize, buffer: &mut [bool], f: F)
where
    for<'a> F: FnMut(&'a [bool]),
{
    gen_with_buffer(n, buffer, f).for_each(drop);
}

#[derive(PartialEq, Eq, Hash, Clone, Debug)]
struct ConstBoolsGenerator<const N: usize> {
    index: Range<usize>,
}

impl<const N: usize> ConstBoolsGenerator<N> {
    pub fn new() -> Self {
        struct AssertLeMax<const N: usize>;
        impl<const N: usize> AssertLeMax<N> {
            const ASSERT: () = assert!(N <= MAX, "too many variables");
        }
        #[allow(clippy::let_unit_value)]
        {
            _ = AssertLeMax::<N>::ASSERT;
        }

        // Safe to unwrap otherwise the above
        // assert would have triggered
        let count = count(N).unwrap();

        Self { index: 0..count }
    }

    #[inline]
    fn to_bools(index: usize) -> [bool; N] {
        array::from_fn(|var| ((index >> var) & 1) != 0)
    }
}

impl<const N: usize> Iterator for ConstBoolsGenerator<N> {
    type Item = [bool; N];

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        self.index.next().map(Self::to_bools)
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.index.size_hint()
    }

    #[inline]
    fn count(self) -> usize
    where
        Self: Sized,
    {
        self.index.count()
    }

    #[inline]
    fn nth(&mut self, n: usize) -> Option<Self::Item> {
        self.index.nth(n).map(Self::to_bools)
    }

    #[inline]
    fn last(mut self) -> Option<Self::Item>
    where
        Self: Sized,
    {
        self.next_back()
    }

    #[inline]
    fn min(mut self) -> Option<Self::Item>
    where
        Self::Item: Ord,
    {
        self.next()
    }

    #[inline]
    fn max(mut self) -> Option<Self::Item>
    where
        Self::Item: Ord,
    {
        self.next_back()
    }
}

impl<const N: usize> DoubleEndedIterator for ConstBoolsGenerator<N> {
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        self.index.next_back().map(Self::to_bools)
    }

    #[inline]
    fn nth_back(&mut self, n: usize) -> Option<Self::Item> {
        self.index.nth_back(n).map(Self::to_bools)
    }
}

impl<const N: usize> ExactSizeIterator for ConstBoolsGenerator<N> {
    #[inline]
    fn len(&self) -> usize {
        self.index.len()
    }
}

impl<const N: usize> FusedIterator for ConstBoolsGenerator<N> {}

#[derive(PartialEq, Eq, Hash, Clone, Debug)]
struct BoolsGenerator {
    index: Range<usize>,
    /// Number of variables.
    n: u8,
}

impl BoolsGenerator {
    #[inline]
    pub fn new(n: usize) -> Self {
        Self::new_checked(n).expect("too many variables")
    }

    #[inline]
    pub fn new_checked(n: usize) -> Option<Self> {
        let count = count(n)?;

        // Safe to unwrap, as even with a `u128`,
        // there could only be at most 127 variables,
        // i.e. `count()` returning at most 127 for `u128`
        let n = u8::try_from(n).unwrap();

        Some(Self { n, index: 0..count })
    }

    #[inline]
    fn to_bools(&self, index: usize) -> Bools {
        Bools::new(self.n, index)
    }
}

impl Iterator for BoolsGenerator {
    type Item = Bools;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        let index = self.index.next()?;
        Some(self.to_bools(index))
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.index.size_hint()
    }

    #[inline]
    fn count(self) -> usize
    where
        Self: Sized,
    {
        self.index.count()
    }

    #[inline]
    fn nth(&mut self, n: usize) -> Option<Self::Item> {
        let index = self.index.nth(n)?;
        Some(self.to_bools(index))
    }

    #[inline]
    fn last(mut self) -> Option<Self::Item>
    where
        Self: Sized,
    {
        self.next_back()
    }
}

impl DoubleEndedIterator for BoolsGenerator {
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        let index = self.index.next_back()?;
        Some(self.to_bools(index))
    }

    #[inline]
    fn nth_back(&mut self, n: usize) -> Option<Self::Item> {
        let index = self.index.nth_back(n)?;
        Some(self.to_bools(index))
    }
}

impl ExactSizeIterator for BoolsGenerator {
    #[inline]
    fn len(&self) -> usize {
        self.index.len()
    }
}

impl FusedIterator for BoolsGenerator {}

/// An [`Iterator`] that produces exactly `n` [`bool`]s.
///
/// See [`gen()`] for more information.
#[derive(PartialEq, Eq, Hash, Clone, Debug)]
pub struct Bools {
    variables: Range<u8>,
    index: usize,
}

impl Bools {
    #[inline]
    fn new(n: u8, index: usize) -> Self {
        Self {
            variables: 0..n,
            index,
        }
    }

    #[inline]
    fn fill_into(&mut self, bools: &mut [bool]) {
        for (b, val) in bools.iter_mut().zip(self.by_ref()) {
            *b = val;
        }
    }

    #[inline]
    fn fill_bools_into(mut self, bools: &mut [bool; MAX]) -> &[bool] {
        let n = self.variables.len();

        // Safe as `gen()` panics if `n > MAX`
        let bools = &mut bools[..n];

        // Safe to unwrap as `self` produces exactly `n` items
        bools.fill_with(|| self.next().unwrap());

        bools
    }

    #[inline]
    fn to_bool(&self, var: u8) -> bool {
        ((self.index >> var) & 1) != 0
    }
}

impl Iterator for Bools {
    type Item = bool;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        let var = self.variables.next()?;
        Some(self.to_bool(var))
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.variables.size_hint()
    }

    #[inline]
    fn count(self) -> usize
    where
        Self: Sized,
    {
        self.variables.count()
    }

    #[inline]
    fn nth(&mut self, n: usize) -> Option<Self::Item> {
        let index = self.variables.nth(n)?;
        Some(self.to_bool(index))
    }

    #[inline]
    fn last(mut self) -> Option<Self::Item>
    where
        Self: Sized,
    {
        self.next_back()
    }

    #[inline]
    fn min(mut self) -> Option<Self::Item>
    where
        Self::Item: Ord,
    {
        self.next()
    }

    #[inline]
    fn max(mut self) -> Option<Self::Item>
    where
        Self::Item: Ord,
    {
        self.next_back()
    }
}

impl DoubleEndedIterator for Bools {
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        let var = self.variables.next_back()?;
        Some(self.to_bool(var))
    }

    #[inline]
    fn nth_back(&mut self, n: usize) -> Option<Self::Item> {
        let var = self.variables.nth_back(n)?;
        Some(self.to_bool(var))
    }
}

impl ExactSizeIterator for Bools {
    #[inline]
    fn len(&self) -> usize {
        self.variables.len()
    }
}

impl FusedIterator for Bools {}

#[cfg(test)]
mod tests {
    use alloc::boxed::Box;
    use alloc::vec;

    use super::*;

    #[test]
    fn test_is_supported() {
        for n in 0..=MAX {
            assert!(is_supported(n));
        }

        assert!(!is_supported(MAX + 1));
    }

    #[test]
    fn test_count() {
        assert_eq!(count(0), Some(0));
        assert_eq!(count(1), Some(2));
        assert_eq!(count(2), Some(4));
        assert_eq!(count(3), Some(8));
        assert_eq!(count(4), Some(16));
        assert_eq!(count(5), Some(32));
        assert_eq!(count(6), Some(64));
        assert_eq!(count(7), Some(128));
        assert_eq!(count(8), Some(256));
        assert_eq!(count(9), Some(512));
        assert_eq!(count(10), Some(1024));

        assert_eq!(count(usize::MAX), None);
    }

    #[test]
    fn test_count_max() {
        assert!(count(MAX).is_some());
    }

    #[test]
    #[cfg_attr(not(target_pointer_width = "16"), ignore)]
    fn test_count_16() {
        assert_eq!(count(15), Some(32768));
        assert_eq!(count(16), None);
    }

    #[test]
    #[cfg_attr(not(target_pointer_width = "32"), ignore)]
    fn test_count_32() {
        assert_eq!(count(31), Some(2147483648));
        assert_eq!(count(32), None);
    }

    #[test]
    #[cfg_attr(not(target_pointer_width = "64"), ignore)]
    fn test_count_64() {
        assert_eq!(count(63), Some(9223372036854775808));
        assert_eq!(count(64), None);
    }

    macro_rules! test_gen {
        ($test_name:ident, $n:literal $(, $($case:expr),* $(,)?)?) => {
            #[test]
            fn $test_name() {
                let n = $n;
                let mut iter = gen_vec(n);

                let cases = &[$($($case.as_slice()),*)?];

                assert_eq!(count(n), Some(cases.len()));

                for (i, &case) in cases.iter().enumerate() {
                    assert_eq!(iter.next().as_deref(), Some(case), "index {i}");
                }

                assert_eq!(iter.next(), None);
            }
        };
    }

    test_gen!(test_gen_0, 0);
    test_gen!(test_gen_1, 1, [false], [true]);
    test_gen!(
        test_gen_2,
        2,
        [false, false],
        [true, false],
        [false, true],
        [true, true],
    );
    test_gen!(
        test_gen_3,
        3,
        [false, false, false],
        [true, false, false],
        [false, true, false],
        [true, true, false],
        [false, false, true],
        [true, false, true],
        [false, true, true],
        [true, true, true],
    );
    test_gen!(
        test_gen_4,
        4,
        [false, false, false, false],
        [true, false, false, false],
        [false, true, false, false],
        [true, true, false, false],
        [false, false, true, false],
        [true, false, true, false],
        [false, true, true, false],
        [true, true, true, false],
        [false, false, false, true],
        [true, false, false, true],
        [false, true, false, true],
        [true, true, false, true],
        [false, false, true, true],
        [true, false, true, true],
        [false, true, true, true],
        [true, true, true, true],
    );

    #[test]
    fn test_gen_max_ends() {
        for n in 0..=MAX {
            let mut iter = gen(n).map(Iterator::collect::<Vec<_>>);

            assert_eq!(count(n), Some(iter.len()));

            if iter.len() == 0 {
                continue;
            }

            assert_eq!(iter.next().unwrap(), vec![false; n]);
            assert_eq!(iter.next_back().unwrap(), vec![true; n]);
        }
    }

    #[derive(PartialEq, Clone, Debug)]
    enum Expr {
        Bool(bool),
        And(Box<Self>, Box<Self>),
        Or(Box<Self>, Box<Self>),
    }

    impl From<bool> for Expr {
        fn from(b: bool) -> Self {
            Expr::Bool(b)
        }
    }

    fn and(lhs: impl Into<Expr>, rhs: impl Into<Expr>) -> Expr {
        Expr::And(Box::new(lhs.into()), Box::new(rhs.into()))
    }

    fn or(lhs: impl Into<Expr>, rhs: impl Into<Expr>) -> Expr {
        Expr::Or(Box::new(lhs.into()), Box::new(rhs.into()))
    }

    #[test]
    fn test_gen_const() {
        const N: usize = 3;

        let exprs = gen_const::<N>()
            .map(|[a, b, c]| and(a, or(b, c)))
            .collect::<Vec<_>>();

        assert_eq!(count(N), Some(exprs.len()));

        let mut exprs = exprs.into_iter();
        assert_eq!(exprs.next().unwrap(), and(false, or(false, false)));
        assert_eq!(exprs.next().unwrap(), and(true, or(false, false)));
        assert_eq!(exprs.next().unwrap(), and(false, or(true, false)));
        assert_eq!(exprs.next().unwrap(), and(true, or(true, false)));
        assert_eq!(exprs.next().unwrap(), and(false, or(false, true)));
        assert_eq!(exprs.next().unwrap(), and(true, or(false, true)));
        assert_eq!(exprs.next().unwrap(), and(false, or(true, true)));
        assert_eq!(exprs.next().unwrap(), and(true, or(true, true)));
        assert_eq!(exprs.next(), None);
    }

    #[test]
    fn test_gen_slice() {
        const N: usize = 3;

        let exprs = gen_slice(N, |bools| and(bools[0], or(bools[1], bools[2]))).collect::<Vec<_>>();

        assert_eq!(count(N), Some(exprs.len()));

        let mut exprs = exprs.into_iter();
        assert_eq!(exprs.next().unwrap(), and(false, or(false, false)));
        assert_eq!(exprs.next().unwrap(), and(true, or(false, false)));
        assert_eq!(exprs.next().unwrap(), and(false, or(true, false)));
        assert_eq!(exprs.next().unwrap(), and(true, or(true, false)));
        assert_eq!(exprs.next().unwrap(), and(false, or(false, true)));
        assert_eq!(exprs.next().unwrap(), and(true, or(false, true)));
        assert_eq!(exprs.next().unwrap(), and(false, or(true, true)));
        assert_eq!(exprs.next().unwrap(), and(true, or(true, true)));
        assert_eq!(exprs.next(), None);
    }

    #[test]
    fn test_gen_const_rev() {
        const N: usize = 3;

        let mut combinations = gen_const::<N>().collect::<Vec<_>>();
        combinations.reverse();

        let combinations2 = gen_const::<N>().rev().collect::<Vec<_>>();

        assert_eq!(combinations, combinations2);
    }

    #[test]
    fn test_gen_rev() {
        const N: usize = 3;

        let mut combinations = gen_vec(N).collect::<Vec<_>>();
        combinations.reverse();

        let combinations2 = gen_vec(N).rev().collect::<Vec<_>>();

        assert_eq!(combinations, combinations2);
    }

    #[test]
    fn test_each_const() {
        const N: usize = 3;

        let mut iter = gen_vec(N);

        each_const::<N, _>(|bools| {
            assert_eq!(bools, iter.next().unwrap().as_slice());
        });

        assert_eq!(iter.next(), None);
    }

    #[test]
    fn test_each() {
        const N: usize = 3;

        let mut iter = gen_vec(N);

        each(N, |bools| {
            assert_eq!(bools, iter.next().unwrap());
        });

        assert_eq!(iter.next(), None);
    }

    #[test]
    fn test_each_vec_slice() {
        const N: usize = 3;

        let mut iter = gen_vec(N);

        each_vec_slice(N, |bools| {
            assert_eq!(bools, iter.next().unwrap());
        });

        assert_eq!(iter.next(), None);
    }

    #[test]
    fn test_each_with_buffer() {
        const N: usize = 3;

        let mut iter = gen_vec(N);

        let mut buf = [false; N];
        each_with_buffer(N, &mut buf, |bools| {
            assert_eq!(bools, iter.next().unwrap());
        });

        assert_eq!(iter.next(), None);
    }
}
