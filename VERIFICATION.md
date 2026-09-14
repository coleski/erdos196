# Verification record

Date: 2026-09-14 UTC (2026-09-13 America/Chicago).

## Full clean proof build: PASS

All ten local Lean modules were copied as source into this newly created
directory. No local compiled artifact was copied. The first build exposed a
Lake configuration error: only the aggregator was registered as a library
root, so Lake did not discover the other top-level modules. That attempt
compiled no local proof module. Its machine-specific failure log remains
in the private local research package and is omitted from this repository.

The configuration was corrected to enumerate all ten local modules. The
subsequent `lake build` checked every one from source and exited 0, without
warnings. The complete output is `CLEAN-BUILD.log`. Its 8,931-job count
includes cached external dependencies; it is not a claim that 8,931 modules
were rebuilt from source. All ten LOCAL modules are explicitly marked Built.

An additional `lake env lean Erdos196.lean` exited 0 and produced `AXIOMS.log`.
Each final theorem reports exactly:

```text
[propext, Classical.choice, Quot.sound]
```

The reports cover `erdos_196_negative`, `erdos_196_counterexample`, and
`erdos_196_positive_integers_negative`, including their transitive
dependencies. There are no admitted steps or custom mathematical axioms.
Source inspection found no `sorry`, `admit`, `native_decide`, unsafe
declarations, or evaluation-based substitute for a proof.

`SOURCE-SHA256.txt` identifies all ten sources, the toolchain file, Lake
configuration, and pinned dependency manifest. `shasum -a 256 -c
SOURCE-SHA256.txt` passed for every entry after the build and axiom check.

## Trust boundary

Lean `v4.34.0-rc2` and the existing external Mathlib/dependency caches are
trusted. Mathlib's checkout HEAD was independently checked to equal
`141f6b6455959bfeb0b2a6b04118031191d62683`; its worktree was clean. The exact
transitive package revisions are pinned in `lake-manifest.json`.

No stale LOCAL proof cache was trusted. No claim is made that the Lean
compiler, operating system, or entire external library cache was rebuilt.
No external solver or native computation certificate is a premise of the
final theorem.

## Statement and mathematical audits

The root read every local proof source, the complete standalone human proof,
and two earlier independently produced adversarial mathematical audits of
the finite-extension construction. An additional AI agent completed the
final formal-meaning audit with verdict PASS and independently imported the
clean final artifact to check its statements and axioms. The source-matched
report is `FORMAL-STATEMENT-AUDIT.md`. Its author explicitly identifies the
three helper modules they authored; their review of those helpers is not
misrepresented as independent. Their review of the final statement, main
construction, and correspondence is independent of those modules' authors.

The formal development separately proves equivalence with the canonical
public statement. The main theorem discharges every premise of that bridge.
It proves a genuine bijection, both progression orientations, all index
gaps, every size, and the positive-natural convention.

This is local kernel verification plus AI-agent auditing, not external
human-expert review or acceptance by Jig, GitHub, a journal, or a problem
curator.
