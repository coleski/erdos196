# #196 canonical-statement and positive-convention correspondence

2026-09-13. **Generic correspondence verified; this file does not assert that the full counterexample construction has been formally completed.**

## Frozen public source

The current [Google Formal Conjectures #196 source](https://raw.githubusercontent.com/google-deepmind/formal-conjectures/main/FormalConjectures/ErdosProblems/196.lean) was fetched and read completely. Its mathematical right-hand side is

```lean
∀ (f : ℕ ≃ ℕ), HasMonotoneAP f 4
```

The current [complete AP utility source](https://raw.githubusercontent.com/google-deepmind/formal-conjectures/main/FormalConjecturesForMathlib/Combinatorics/AP/Basic.lean) was also fetched and read completely. It defines a list AP as either the forward or reversed image of `List.range l` under `n ↦ a + n • d`. `HasMonotoneAP f k` asks for a list of strictly increasing indices whose image is such a length-`k` AP. The three definitions used by #196 are reproduced verbatim in body and type, with formerly surrounding implicit typeclass binders made explicit, in `Erdos196Correspondence.lean`; original global names and Apache-2.0 attribution are retained. No unproved public theorem or `answer(sorry)` placeholder is imported.

GitHub's path-specific latest-change API identified these immutable versions, whose raw files were separately fetched and hashed:

- [Problem196 at commit c252a41054125b5fd9c8356e2137cd9b55337657](https://raw.githubusercontent.com/google-deepmind/formal-conjectures/c252a41054125b5fd9c8356e2137cd9b55337657/FormalConjectures/ErdosProblems/196.lean), SHA-256 `886148886e591a0fdccde7c199ad04a08202d5088b19a5e9714f633e7541dbd2`.
- [AP/Basic at commit ee4aaef5655f8aa4a29d59391a822f398891a2b3](https://raw.githubusercontent.com/google-deepmind/formal-conjectures/ee4aaef5655f8aa4a29d59391a822f398891a2b3/FormalConjecturesForMathlib/Combinatorics/AP/Basic.lean), SHA-256 `62f0a0987d49c5dbfd7b4f82a4f3dd4faba7ad545c676df06d0cda009567b5c3`.

## Exact verified equivalence

For every injective `f : ℕ → ℕ`, the public `HasMonotoneAP f 4` is equivalent to four indices `i < j < k < l` satisfying our `AP4 (f i) (f j) (f k) (f l)`. Therefore our entire `OriginalQuestion` is equivalent to the public universal statement over all `ℕ ≃ ℕ`.

Degenerate-difference handling is substantive: the public list definition itself allows `d = 0`. However, the four indices are distinct and `f` is injective, so the first two image values differ. This rules out both forward and reversed constant lists. The proof does not silently strengthen the public definition by adding `d > 0`.

Conversely, our two midpoint equalities plus unequal first entries imply that all four values strictly increase or strictly decrease. In the increasing case the public witness uses first value `f i` and difference `f j - f i`; in the decreasing case it uses first value `f l` and difference `f k - f l`, with the reversed list. Thus both directions of monotonicity, zero-based values and all possible index gaps are covered.

The generic theorem `avoiding_permutation_refutes_canonical` concludes the negation of the exact public universal statement from the existence of an actual bijection satisfying `NoAP4Sequence`. Its premise is deliberately not discharged inside this correspondence file.

## Positive integers

`positivePermutation f` conjugates an arbitrary natural-number permutation by Mathlib's exact `ℕ+ ≃ ℕ` equivalence. Both index and value conventions shift by one: at positive index `i`, its natural value is `f (i-1) + 1`. The checked midpoint identities are unchanged by adding one, and predecessor strictly preserves order on positive integers.

The generic theorem `avoiding_permutation_refutes_positive` therefore refutes `PositiveOriginalQuestion`, quantified over all permutations `ℕ+ ≃ ℕ+` and all strictly increasing positive indices, from the same avoiding natural-number bijection. This is an actual positive-index/value correspondence, not merely a verbal shift of a zero-based list.

## Build and axioms

Local source SHA-256: `2220c308bd410b27184f688249bd352a636c1b1072b9ee67b59a369b5ac6c890`.

Imported Core source SHA-256: `b78484c873576551b114d952fc64ce9a74cbf04fbc0148e25fd5574c04f8bc9e`.

`lake env lean Erdos196Correspondence.lean` completed with exit0 and no warnings using the project's pinned toolchain. Both printed theorems depend only on `[propext, Classical.choice, Quot.sound]`. No `sorry`, custom axiom, `native_decide`, unproved final construction, or external solver certificate occurs in this file.
