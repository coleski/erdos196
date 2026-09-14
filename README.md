# Erdős problem 196: full negative resolution package

The exact canonical theorem, full clean build, and independent formal-meaning
audit have passed. The prior-work search is documented separately; local
verification is not a claim of outside expert endorsement or publication.

Start with [the complete proof](FINAL-HUMAN-PROOF.md),
[the verification record](VERIFICATION.md),
[the independent statement audit](FORMAL-STATEMENT-AUDIT.md), and
[the prior-art audit](FINAL-PRIOR-ART-AUDIT.md).

## Exact scope and answer

There exists a bijection `f : ℕ ≃ ℕ` such that no four indices `i < j < k < l`
have values forming a nonconstant arithmetic progression, in either increasing
or decreasing numerical order. The answer to the full original question is
therefore **no**. This is one infinite, one-sided permutation, not unrelated
finite examples, a two-sided order, or a special family of progressions.

The final theorems in `Erdos196.lean` are:

```lean
theorem erdos_196_negative : ¬ (∀ f : ℕ ≃ ℕ, HasMonotoneAP f 4)
theorem erdos_196_counterexample : ∃ f : ℕ ≃ ℕ, ¬ HasMonotoneAP f 4
theorem erdos_196_positive_integers_negative : ¬ PositiveOriginalQuestion
```

The public AP definitions are reproduced with attribution in
`Erdos196Correspondence.lean`. A checked equivalence handles both directions
and the nominal zero-difference case; injectivity excludes that degeneracy.
No public conjecture theorem or unproved placeholder is imported.

## Proof mechanism

A finite prefix is certified against an adaptable binary-residue-tree tail.
To extend it, first complete the nonpreferred parity child, obtaining a finite
maximum `H`. Then complete the preferred child far enough to cover every
preferred value through `2H`. Append the new preferred entries, then the new
other entries. Every potential odd-difference progression would require a
preferred tail value at most `2H`, which the coverage has excluded. Even
differences are handled by the child proofs. Strong induction on the old
prefix maximum proves extension for every requested bound. Nested fair
extensions yield an actual bijection.

The complete standalone argument is in `FINAL-HUMAN-PROOF.md`.

## Reproduce

Pinned Lean: `leanprover/lean4:v4.34.0-rc2`.

Pinned Mathlib: `141f6b6455959bfeb0b2a6b04118031191d62683`.
Transitive dependency commits are recorded in `lake-manifest.json`.

In a fresh directory containing the ten `.lean` source files, `lean-toolchain`,
`lakefile.toml`, and `lake-manifest.json`, with Elan/Lake installed:

```sh
lake exe cache get
lake build
lake env lean Erdos196.lean
```

The library configuration explicitly includes all ten local modules. The
final command prints the axiom reports for all three final theorems. Only
`propext`, `Classical.choice`, and `Quot.sound` are permitted; `sorryAx` or any
custom mathematical axiom invalidates the claimed verification.

The recorded build and all three final reports passed. See `VERIFICATION.md`,
`CLEAN-BUILD.log`, `AXIOMS.log`, and `FORMAL-STATEMENT-AUDIT.md`.

For the recorded clean build, no local `.olean` was copied. Only the pinned
external Lean/Mathlib/dependency caches are reused. The `.lake/packages`
symlink is a local convenience and is not needed for reproduction: obtain
the pinned packages with Lake in a fresh directory instead. We do not claim
to have rebuilt the Lean compiler or all Mathlib dependencies from source.

## Source and novelty boundaries

The original question is in Davis, Entringer, Graham, and Simmons,
*On permutations containing no long arithmetic progressions*, Acta Arithmetica 34 (1977),
pp. 81–90; the singly-infinite four-term question appears on pp. 85 and 88.
That paper establishes unavoidable three-term and avoidable five-term
progressions, and separately discusses two-sided four-term avoidance.

- [Original paper](https://matwbn.icm.edu.pl/ksiazki/aa/aa34/aa3417.pdf)
- [Erdős problem 196](https://www.erdosproblems.com/196)
- [Jig problem 73](https://jig.so/p/73)
- [Canonical Formal Conjectures statement](https://github.com/google-deepmind/formal-conjectures/blob/c252a41054125b5fd9c8356e2137cd9b55337657/FormalConjectures/ErdosProblems/196.lean)

The construction and its formal proofs were developed in this research run
by the assistant and cooperating AI agents. Independent AI-agent proof and
meaning audits are not independent human-expert review. Public-source
searches can establish the prior-work evidence checked, but cannot rule out
unpublished or unindexed results. No remote verifier acceptance, public
posting, GitHub publication, or outside expert endorsement is claimed.

The bounded final search found no prior full resolution or competing full
claim in the checked sources. Classical binary-order facts are credited in
the proof; the new contribution is adaptive uniform finite-prefix extension
and its fair completion. The August 2026 density results are not treated as
solutions of the original question.
