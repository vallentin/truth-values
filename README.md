# truth-values

[![CI](https://github.com/vallentin/truth-values/workflows/CI/badge.svg)](https://github.com/vallentin/truth-values/actions?query=workflow%3ACI)
[![Latest Version](https://img.shields.io/crates/v/truth-values.svg)](https://crates.io/crates/truth-values)
[![Docs](https://docs.rs/truth-values/badge.svg)](https://docs.rs/truth-values)
[![License](https://img.shields.io/github/license/vallentin/truth-values.svg)](https://github.com/vallentin/truth-values)

<!-- cargo-rdme start -->

Tiny, zero-dependency, zero-allocation*, `no_std` library for generating all possible
combinations of `n` [`bool`]s. Useful for testing [boolean functions],
verifying [logical equivalence], and generating [truth tables].
_\*Optional `alloc` feature for [`Vec`] related functions._

[boolean functions]: https://en.wikipedia.org/wiki/Boolean_function
[logical equivalence]: https://en.wikipedia.org/wiki/Logical_equivalence
[truth tables]: https://en.wikipedia.org/wiki/Truth_table

## Example - `each()` and `each_const()`

Consider implementing an interpreter or optimizer, and now you
want to assert [logical equivalence] between expressions, e.g.
asserting [De Morgan's laws]:

- not (A or B)  = (not A) and (not B)
- not (A and B) = (not A) or (not B)

[De Morgan's laws]: https://en.wikipedia.org/wiki/De_Morgan%27s_laws

Using [const generic variant](https://docs.rs/truth-values/latest/truth_values/fn.each_const.html), i.e. where `N` is const:

```rust
each_const(|[a, b]| {
    assert_eq!(!(a || b), !a && !b);
    assert_eq!(!(a && b), !a || !b);
});
// The closure is called for each combination of 2 `bool`s, i.e.:
// [false, false]
// [true,  false]
// [false, true]
// [true,  true]
```

Using [non-const generic variant](https://docs.rs/truth-values/latest/truth_values/fn.each.html), i.e. where `n` can be dynamic:

```rust
each(2, |bools| match bools {
    &[a, b] => {
        assert_eq!(!(a || b), !a && !b);
        assert_eq!(!(a && b), !a || !b);
    }
    _ => unreachable!(),
});
// The closure is called for each combination of 2 `bool`s, i.e.:
// &[false, false]
// &[true,  false]
// &[false, true]
// &[true,  true]
```

## Example - `gen()` and `gen_const()`

Alternatively, use [`gen()` functions](https://docs.rs/truth-values/latest/truth_values/#functions) to obtain
an [`Iterator`] for generating all combinations. This could be used
to e.g. map each combination into an `Expr` for an [AST], to easily
generate all `Expr` combinations to verify their evaluation.

[AST]: https://en.wikipedia.org/wiki/Abstract_syntax_tree

Using [const generic variant](https://docs.rs/truth-values/latest/truth_values/fn.gen_const.html), i.e. where `N` is const:

```rust
#[derive(PartialEq, Debug)]
enum Expr {
    Bool(bool),
    And(Box<Self>, Box<Self>),
    // ...
}

impl Expr {
    fn and(lhs: Expr, rhs: Expr) -> Expr {
        Expr::And(Box::new(lhs), Box::new(rhs))
    }
}

let exprs = truth_values::gen_const()
    .map(|[a, b]| {
        Expr::and(Expr::Bool(a), Expr::Bool(b))
    })
    .collect::<Vec<_>>();

assert_eq!(
    exprs,
    [
        Expr::and(Expr::Bool(false), Expr::Bool(false)),
        Expr::and(Expr::Bool(true),  Expr::Bool(false)),
        Expr::and(Expr::Bool(false), Expr::Bool(true)),
        Expr::and(Expr::Bool(true),  Expr::Bool(true)),
    ]
);
```

Using [non-const generic variant](https://docs.rs/truth-values/latest/truth_values/fn.gen_slice.html), i.e. where `n` can be dynamic:

```rust
let exprs = truth_values::gen_slice(2, |bools| {
    match bools {
        &[a, b] => {
            Expr::and(Expr::Bool(a), Expr::Bool(b))
        }
        _ => unreachable!(),
    }
})
.collect::<Vec<_>>();

assert_eq!(
    exprs,
    [
        Expr::and(Expr::Bool(false), Expr::Bool(false)),
        Expr::and(Expr::Bool(true),  Expr::Bool(false)),
        Expr::and(Expr::Bool(false), Expr::Bool(true)),
        Expr::and(Expr::Bool(true),  Expr::Bool(true)),
    ]
);
```

## Combinations of 1, 2, 3, 4 `bool`s

<table>
<tr>
<td style="text-align: center;">

```rust
gen_const::<1>()
```

</td>
<td style="text-align: center;">

```rust
gen_const::<2>()
```

</td>
<td style="text-align: center;">

```rust
gen_const::<3>()
```

</td>
<td style="text-align: center;">

```rust
gen_const::<4>()
```

</td>
</tr>
<tr>
<td style="vertical-align: top;">

```rust
[false]
[true]
```

</td>
<td style="vertical-align: top;">

```rust
[false, false]
[true,  false]
[false, true]
[true,  true]
```

</td>
<td style="vertical-align: top;">

```rust
[false, false, false]
[true,  false, false]
[false, true,  false]
[true,  true,  false]
[false, false, true]
[true,  false, true]
[false, true,  true]
[true,  true,  true]
```

</td>
<td style="vertical-align: top;">

```rust
[false, false, false, false]
[true,  false, false, false]
[false, true,  false, false]
[true,  true,  false, false]
[false, false, true,  false]
[true,  false, true,  false]
[false, true,  true,  false]
[true,  true,  true,  false]
[false, false, false, true]
[true,  false, false, true]
[false, true,  false, true]
[true,  true,  false, true]
[false, false, true,  true]
[true,  false, true,  true]
[false, true,  true,  true]
[true,  true,  true,  true]
```

</td>
</tr>
</table>

## Implementation

The [`gen()` functions](https://docs.rs/truth-values/latest/truth_values/#functions) return an [`Iterator`], which
additionally specializes [`size_hint()`], [`count()`], [`nth()`], [`last()`].

The [`Iterator`] also implements:

- [`DoubleEndedIterator`] implementing [`next_back()`] and [`nth_back()`]
- [`ExactSizeIterator`] implementing [`len()`]
- [`FusedIterator`]

## Warning

The amount of combinations is exponential!
The number of combinations for `N` boolean variables is <code>2<sup>N</sup></code>.
In short, **10 variables** produce **1024 combinations**, but **20 variables**
produce over **1 million combinations**.

_Just alone exhausting the generator for **30 variables**, i.e. over **1 billion
combinations**, takes a handful of seconds on my machine._

Ideally, if used to test expressions, then there will likely only be a handful of
variables. However, if user input is accepted, then it might be worth guarding and
limiting the number of variables.

So even though up to [`MAX`] (`63`) variables for 64-bit platforms
is supported, it is probably undesirable to even attempt to process
that many variables.

[`MAX`]: https://docs.rs/truth-values/latest/truth_values/const.MAX.html

[`size_hint()`]: https://doc.rust-lang.org/std/iter/trait.Iterator.html#method.size_hint
[`count()`]: https://doc.rust-lang.org/std/iter/trait.Iterator.html#method.count
[`nth()`]: https://doc.rust-lang.org/std/iter/trait.Iterator.html#method.nth
[`last()`]: https://doc.rust-lang.org/std/iter/trait.Iterator.html#method.last
[`next_back()`]: https://doc.rust-lang.org/std/iter/trait.DoubleEndedIterator.html#tymethod.next_back
[`nth_back()`]: https://doc.rust-lang.org/std/iter/trait.DoubleEndedIterator.html#method.nth_back
[`len()`]: https://doc.rust-lang.org/std/iter/trait.ExactSizeIterator.html#method.len

<!-- cargo-rdme end -->

[`bool`]: https://doc.rust-lang.org/std/primitive.bool.html
[`Vec`]: https://doc.rust-lang.org/std/vec/struct.Vec.html
[`Iterator`]: https://doc.rust-lang.org/std/iter/trait.Iterator.html
[`DoubleEndedIterator`]: https://doc.rust-lang.org/std/iter/trait.DoubleEndedIterator.html
[`ExactSizeIterator`]: https://doc.rust-lang.org/std/iter/trait.ExactSizeIterator.html
[`FusedIterator`]: https://doc.rust-lang.org/std/iter/trait.FusedIterator.html
