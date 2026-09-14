# Jig verification

The full refutation is submitted as an original statement under `coleski`:
[Jig problem 73, statement 4](https://jig.so/p/73?s=4).
It explicitly refutes the original root statement, rather than a boundary case.
The GitHub repository is linked as our own proof package, not prior art.

## Compatibility adjustment

Jig pins Lean `v4.33.0` and Mathlib
`db584cd6d46c92f209a44c0f1c829460d327499d`, older than this repository's
original reproduction environment. The first local run of Jig's verifier
found that `List.Pairwise.rel_getElem_of_lt` was unavailable there.

One line in `Erdos196Base.lean` now uses the equivalent
`List.pairwise_iff_getElem.mp` instead. No definition, theorem statement,
construction, hypothesis, or mathematical argument changes. The adjusted
sources build on the original pinned environment; `SOURCE-SHA256.txt`
records the current source hashes. The original audit and build logs refer
to the sources preserved in the initial public commit
`43b5f6cc87173d30b24f71bd1763c43f6ce3eeea`.

Jig verification and root closure are pending. A posted statement alone
does not establish either; the remote artifact verdict is authoritative.
