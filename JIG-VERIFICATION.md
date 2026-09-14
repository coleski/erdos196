# Jig verification

[Jig verified the refutation](https://jig.so/p/73?s=4) and closed the
original question on 14 September 2026 at 03:53:20 UTC.

- [Complete verifier output](https://jig.so/api/artifacts/50b32c8b-0027-4024-ab4a-64cfc1081daa)
- [Verification run](https://github.com/WoshuaJolk/jig-verifier/actions/runs/34803974764)
- [Verified source commit](https://github.com/coleski/erdos196/commit/994b1cd0456d4a69c7bb6911e652acf4a85fd68d)

## Statement and checks

The submitted theorem is `Erdos196.erdos_196_negative`. The verifier checks
that its type agrees with the submitted statement and that this statement
is definitionally equal to the negation of Jig's root,
`Statements.Erdos196MonotoneFourAP.statement`.

All seven checks passed: manifest, static policy, build, statement
agreement, absence of new axioms, allowed axiom dependencies, and the
refutation link. The only axiom dependencies are `Classical.choice`,
`Quot.sound`, and `propext`.

## Toolchain

Jig used Lean `v4.33.0` and Mathlib
`db584cd6d46c92f209a44c0f1c829460d327499d`.
The repository's own build uses Lean `v4.34.0-rc2` and Mathlib
`141f6b6455959bfeb0b2a6b04118031191d62683`.

To support both versions, `pairwise_ordered` in `Erdos196Base.lean`
uses `List.pairwise_iff_getElem.mp` in place of the newer
`List.Pairwise.rel_getElem_of_lt`. This one-line change leaves the
mathematical statement and argument unchanged.

## Source identity

The local and remote verifier report the same source hash:

```text
sha256:f1525190bdbd4516baba544e0b3a0243486bbf4320d178fbf66a8a64bf16327a
```

They also report the same normalized proof-term hash:

```text
sha256:839c539ce873c3b1115054d0fe9db12f722cf5082369e4d1d5d1e7d92f1b93d7
```

`SOURCE-SHA256.txt` lists the individual source hashes.
[VERIFICATION.md](VERIFICATION.md) records the original clean build and
AI-agent statement audits. These records do not constitute human peer review.
