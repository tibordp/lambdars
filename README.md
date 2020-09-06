# lambdars

lambdars is a REPL for playing with untyped lambda calculus.

## Usage

lambdars accepts a lambda expression on every line and then tries to reduce it to a canonical form with a sequence of β-reductions and α-conversions.

Both `λ` and `\` are accepted for specifying a lambda abstraction, for example:

```
> (\f.\x.f (f x)) (\f.\x.f (f x))
 INFO  lambdars::runtime > Reduced in 6 iterations, total α: 3, total β: 6
λx.λy.x (x (x (x y)))
```

lambdars also supports defining macros that are substituted before reduction in order to make the lengthy expressions a bit more manageable:

```
> #define 0 \f.\x.x
> #define 1 \f.\x.f x
> #define plus \m.\n.\f.\x.m f (n f x)
> plus 1 1
 INFO  lambdars::runtime > Reduced in 6 iterations, total α: 2, total β: 6
λx.λy.x (x y)
```

As a lambda expression may not converge to a normal form by repeated β and α reductions (lossely speaking, may never terminate), there are some execution limits in place, they can be controlled as such:

```
#max_reductions 10000
#max_depth 1000
#max_size 1000000
```

A preamble file (see e.g. [Church numerals and combinators](./examples/church.txt)) can be specified using a command line parameter

```
lambdars --preamble ./example/church.txt
```

## Demo

![](./docs/demo.gif)

## Building from source

lambdars can be built using standard Rust tooling out of the box.

```
cargo --release build
```