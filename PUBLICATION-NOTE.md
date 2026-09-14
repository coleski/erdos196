# Publication and acceptance status

Publication date: 14 September 2026 UTC (13 September in the workspace).

**Update:** Jig verified the full proof and closed the original problem as
refuted on 14 September 2026 at 03:53:20.739 UTC. See
[the verified statement](https://jig.so/p/73?s=4) and
[JIG-VERIFICATION.md](JIG-VERIFICATION.md). The publication-time observations
below are retained as historical context; their pending-acceptance wording
does not describe the current Jig status.

The initial public proof commit is
[`43b5f6cc87173d30b24f71bd1763c43f6ce3eeea`](https://github.com/coleski/erdos196/commit/43b5f6cc87173d30b24f71bd1763c43f6ce3eeea).
Its publication was confirmed by reading the remote branch and fetching
the final theorem through GitHub's unauthenticated raw-content endpoint.

A second clean local-proof build in the publication checkout also passed
all ten modules, reusing only external dependency caches. Its complete
output is in [PUBLICATION-BUILD.log](PUBLICATION-BUILD.log). The final
theorems again report only `propext`, `Classical.choice`, and `Quot.sound`.

## What is proved

The final theorem negates the complete canonical Erdős #196 statement:
there is a bijection of the natural numbers whose values at no four
increasing indices form an increasing or decreasing nonconstant arithmetic
progression. The positive-integer convention is also proved. This is not
a fixed-size test, a statement about a subset, or a leftover of a known
solution. It meets the mathematical scope of a full refutation.

The initial published sources matched the clean, audited proof package.
The later one-line library compatibility change is documented in
[JIG-VERIFICATION.md](JIG-VERIFICATION.md); `SOURCE-SHA256.txt` tracks
the current sources. Local kernel acceptance and source-meaning
audits are documented; actual Jig acceptance and outside expert review have
not occurred. Those are separate from mathematical completeness.

## Novelty evidence

The final bounded source audit found no earlier full result or competing
full claim. The live Jig board still listed the original problem as open
immediately before publication. The August 2026 paper by Geneson explicitly
distinguishes its density results from an avoiding permutation of all
naturals. Classical binary-order ingredients are credited; the claimed
new contribution is adaptive uniform finite-prefix extension and its fair
completion. See `FINAL-PRIOR-ART-AUDIT.md` for sources and search limitations.

An additional publication-time search found
[neelsomani/gpt-erdos's #196 note](https://github.com/neelsomani/gpt-erdos/blob/main/data/solutions/196/candidate_solution.md).
Its indexed contents expressly leave the question open and describe only
known boundary and fixed-divisibility results; it is not an earlier
full-resolution claim. This is indexed evidence, not an exhaustive search
of private or unindexed work.

## Comparison with other Jig closures

[Declan Gessel's #488 refutation](https://jig.so/p/398?s=40) is a
kernel-checked negation of that full root statement. The present theorem
has the same full-refutation logical scope, but has not yet passed Jig's
own submission and verification process. No guarantee of another party's
acceptance is asserted.

At this publication-time check, [Jig's #811 C6 question](https://jig.so/p/353)
was still open. Its partial checked statements must not be described as a
full closure. This distinction does not affect the scope of the #196
theorem published here.
