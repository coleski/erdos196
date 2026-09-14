# Jig verification

The full refutation is verified as an original statement under `coleski`:
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

## Remote verification: GREEN; problem: CLOSED / REFUTED

Jig closed the full original problem at **2026-09-14 03:53:20.739 UTC**.
The root status is `refuted`; our statement status is `proved`.
This is a full root refutation, not a partial result or prior-art closure.

- [Verified statement](https://jig.so/p/73?s=4)
- [Remote artifact and complete verdict](https://jig.so/api/artifacts/50b32c8b-0027-4024-ab4a-64cfc1081daa)
- [Verification run](https://github.com/WoshuaJolk/jig-verifier/actions/runs/34803974764)
- [Exact verified proof commit](https://github.com/coleski/erdos196/commit/994b1cd0456d4a69c7bb6911e652acf4a85fd68d)

All seven reported checks passed: manifest, static policy, build,
anti-restatement, no-new-axioms, allowed axioms, and exact refutation link.
The latter checks definitional equality with the negation of Jig's existing
root, `Statements.Erdos196MonotoneFourAP.statement`.

The only axioms are `Classical.choice`, `Quot.sound`, and `propext`.
The remote source hash matches the local verifier's:
`sha256:f1525190bdbd4516baba544e0b3a0243486bbf4320d178fbf66a8a64bf16327a`.
Both report the normalized term hash
`sha256:839c539ce873c3b1115054d0fe9db12f722cf5082369e4d1d5d1e7d92f1b93d7`.

The first remote canonical-statement check used an older repository
snapshot predating the statement file. Reconciliation reran it against the
published file and passed. The first and only proof artifact is green.

Platform verification is not a claim of journal publication or independent
human-expert review. The novelty audit remains a bounded public-source
search, not a guarantee concerning unpublished work.
