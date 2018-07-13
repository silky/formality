# Formality

A massively parallel programming language featuring formal proofs, smart contracts and optimal beta-reduction.

## Usage

Currently there is just a prototypal, untested type-checker. You can run a simple example by executing `Main.hs`.

## Benchmarks

TODO

## How it is possible

Formality's core is a small pure type system based on Elementary Affine Logic (instead of Classic Logic, as usual). That allows its term language to be executed by [Lamping's abstract algorithm](https://github.com/MaiaVictor/articles/tree/master/0004-supercompilation-for-free), which is remarkable for being massively parallel and for having a perfect cost model (for smart-contracts). The main difference w.r.t classical logic is that it functions must be affine - i.e., bound variables can't be used more than once. To compensate, it introduces an explicit duplication operator, `dup term as name in expr`, that must follow certain structural restrictions.

1. Only "boxed" terms can be duplicated.

2. A term can be "boxed" if it has no free affine (i.e., lam-bound) variables.

3. There must be exactly one box between the introduction of an exponential variable (i.e., dup-bound) and its occurrence.

The precise rules will be detailed in a future document. For now, here is a brief explanation:

```haskell
-- EACC is obtained from CC by restricting functions to be affine and adding 3 constructs:
-- - Put: `|x` marks a term without free affine variables.
-- - Exp: `!x` is the type of `|x`.
-- - Dup: `$v x y` replaces occurrences of `v` by `x` in `y`.
-- With the following reduction rules:
-- - nf(!a)     => !nf(a)
-- - nf(|a)     => nf(a)
-- - nf($x y z) => nf(z[y/x])
-- With the following typing rules:
-- - Γ |-  x :  t    Γ |-  t : *    Γ |- x : !t   Γ, x0 : t, ... xN : t |- y : u
-- - ------------    -----------    --------------------------------------------
-- - Γ |- |x : !t    Γ |- !t : *    Γ |- $v x y : u
--
-- Examples:
-- (Note: I use `:->=` for clarity, but those characters are ignored.)
--
-- The type of Church nats is as expected, except for additional `!`s:

Nat = ∀ P : * -> !(P -> P) -> !(P -> P)

-- The number 3 is represented as:

c3 =
  Λ P : * ->
  λ s : !(P -> P) ->
  $ S = s
  | λ z : P ->
    S (S (S z))

-- Notice that:
-- 1. `Λ` represents an erased lambda. Its variables are not affine.
-- 2. The first `!` was used to allow the duplication of `s`.
-- 3. `$ S = s in ...` was used to duplicate the `s` variable.
-- 4. There is no free affine variable inside the expression inside `|`.
-- 5. There is exactly one `|` between the declaration of S and its occurrences.
-- 6. The term correctly type-checks as `∀ P : * -> !(P -> P) -> !(P -> P)`.
-- 7. If you erase the `!`s, `|`s and `$`s, you get the usual CC definition.
-- 
-- The definitions of `add`, `mul` and `exp` are as follows:

exp =
  λ a : Nat ->
  λ b : !Nat ->
  Λ P : * ->
  $ B = b
  a !(P -> P) |(B P)

mul =
  λ a : Nat ->
  λ b : Nat ->
  Λ P : * ->
  λ s : !(P -> P) ->
  a P (b P s)

add = 
  λ a : Nat ->
  λ b : Nat ->
  Λ P : * ->
  λ s : ! (P -> P) ->
  $ S = s
  $ f = (a P |S)
  $ g = (b P |S)
  | λ z : P ->
    f (g z)

-- Notice that all those functions correctly type check as `Nat -> Nat -> Nat`.
-- Notice also that, again, erasing `!`s, `|`s and `$`s gives the usual CC definitions.
```

This README is a draft. Future work should focus in formalizing, developing a friendly, Elm-like syntax and researching methods to express inductive proofs.
