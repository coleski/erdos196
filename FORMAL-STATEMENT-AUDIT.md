# Independent formal-meaning audit of the #196 construction

2026-09-13. Auditor: the multiplicative lane, independently reviewing the central Base, ParityLift, Extension, and Correspondence arguments. The auditor authored Children, Assembly, and Limit, so the audit of those three modules is an explicit self-review, not a claim of independent authorship. No proof sources were changed for this audit.

## Verdict and verification gate

**Mathematical meaning and proof-interface audit: PASS.** The final statement is a negative answer to the entire one-sided permutation question, not a finite example, a two-sided order, or a result about a subset. No missing mathematical hypothesis or vacuity was found in the full source review.

**Final imported-artifact axiom check: PASS.** After the clean package build, this auditor independently imported the final aggregator in the persistent package `erdos196-proof-khO0gz` and ran the checks in Section8. The command exited0 with all three final theorems depending only on `propext`, `Classical.choice`, and `Quot.sound`. There is no remaining conditional mathematical or formal gate in this audit.

This audit does not itself certify novelty, priority, publication, or the completeness of the separate public-claim search.

## 1. Original and public-formal scope

I reread the frozen `reserve196/REVERSE-COLEX-TARGET.md`, the complete candidate human proof, and the actual current source of all ten Lean modules listed below. I visually rechecked DEGS77 printed pages85 and88 in the saved primary scans. They distinguish the question about singly-infinite permutations of the positive integers from the established doubly-infinite construction. The audited statement has the required singly-infinite domain.

I independently fetched and read the entire pinned primary formal files:

- [Public #196 statement](https://raw.githubusercontent.com/google-deepmind/formal-conjectures/c252a41054125b5fd9c8356e2137cd9b55337657/FormalConjectures/ErdosProblems/196.lean).
- [Public AP definitions](https://raw.githubusercontent.com/google-deepmind/formal-conjectures/ee4aaef5655f8aa4a29d59391a822f398891a2b3/FormalConjecturesForMathlib/Combinatorics/AP/Basic.lean).

The public right-hand side is `∀ f : ℕ ≃ ℕ, HasMonotoneAP f 4`. Its `answer(sorry)` and theorem proof are NOT imported. The three copied definitions in Correspondence have identical types and mathematical bodies, with surrounding implicit binders made explicit. In particular, the list AP permits forward **or reversed** progressions; the index list is strictly increasing. This is not an altered one-direction-only predicate.

`AP4 a b c d` means `a+c=2*b`, `b+d=2*c`, and `a≠b`. Over naturals these equations force either all four values strictly increasing or all four strictly decreasing. The explicit theorem `ap4_increasing_or_decreasing` verifies this. Thus both signs of the common difference are included, and constant progressions are excluded. The public predicate formally permits difference0, but injectivity of a permutation and strict indices exclude that case; Correspondence uses exactly this injectivity fact.

`canonical_hasMonotoneAP_four_iff` proves both directions of the correspondence for every injective natural-valued sequence. The decreasing direction uses the last value as the starting term and a positive natural difference, then reverses the four-term list. There is no truncating-subtraction loophole: the strict inequalities and AP equations discharge the natural subtraction identities.

Finally, `positivePermutation` conjugates a natural permutation by the equivalence between positive naturals and naturals. Both indices and values shift by1. The AP equations are translation invariant, and the predecessor map is strictly monotone on positive naturals. Therefore the positive-integer original is addressed as well.

## 2. Finite certificate is substantive, not vacuous

`Admissible p` includes `p.Nodup` and an existential binary-tree witness whose concrete computed comparison, appended after the literal list, avoids every AP4 chain. `Before` always places every listed value before every absent value and uses list indices internally. Its use of `idxOf` is safe on the nodup lists where internal chronology is required.

No arbitrary relation is postulated to be empty in the global construction. The witness is a function assigning a Bool to every finite binary path, and `treeBefore` recursively compares at the first differing bit. Its recursion is well-founded by the natural sum of its inputs. Although the proof need not establish that every such relation has order type omega (indeed it generally does not), that does not create a loophole: the final enumeration comes from stabilized finite lists, not by enumerating the tail order.

`admissible_noAP4List` proves that four strictly increasing, in-range list indices give three `Before` comparisons. All `getD` accesses are converted to in-range `getElem` accesses, so the fallback0 is never used in this argument.

## 3. Base audit

Base proves irreflexivity, totality, asymmetry, transitivity, the anchor-first property, and absence of monotone3APs for the concrete fixed-bit order. It also proves that the first and last pairs of every AP4 have the same fixed-order comparison.

The two-scan theorem actually handles all memberships of the four terms in the prefix. Cases with an absent term before a present term contradict `Before`; at least three terms in either scan contradict the three-term lemma; the two-plus-two case contradicts equal first/last comparisons after reversal. This does not assume a finite order extends the previous tail orientation.

The singleton extension is `h :: sort(range(N+1) erase h)`. It starts with the old singleton even if `h>N`, has no duplicates, and covers every natural at mostN. The reverse fixed tree certifies its tail. The empty case is also proved rather than assumed. Thus admissibility is populated and every small base admits arbitrary finite coverage.

## 4. Central parity merge audit

The actual `admissible_parity_merge` conclusion is admissibility of the full list `p ++ A ++ B`. Its hypotheses are supplied later by Extension: old admissibility, nodup of the assembled list, correct parities, an upper boundH for all new other-parity values, coverage of all preferred values at most2H, and admissibility of both exact projected children.

For same-parity APs, all four values share parity by the AP equations. Division by2 preserves the two equations and nonconstancy; `before_childPrefix` transfers all three comparisons to the appropriate child witness. No mixed-prefix ordering is discarded.

For odd-difference APs, the stage function has exact chronological blocks0,1,2,3,4: old prefix; new preferred; new other; preferred tail; other tail. The file proves its membership characterization and monotonicity from the actual `Before` relation, not as an extra global hypothesis.

If the third AP term is old, the entire chain transfers to the old witness. If the second term is old and the third is preferred, the old root order supplies the missing last comparison and again contradicts the old witness. The remaining alternating cases force either a stage2 second term followed by a stage3 third term, or a stage2 third term followed by a stage3 fourth term. In the first case `c≤2b≤2H`; in the second `d≤2c≤2H`. Both contradict preferred-tail coverage. These inequalities use nonnegativity, not positivity of the common difference, so decreasing progressions are not lost.

Only the old root preference is retained. The two recursive child witnesses may change freely. This precisely matches the viable human construction and avoids the earlier overconstrained fixed-tail approach.

## 5. Uniform extension quantifiers and termination

`admissible_finite_extension` quantifies over every finite admissible listp and every natural targetN and produces a finite admissibleq with **literal initial-list** relation `p.IsPrefix q` and coverage of allx≤N.

The induction is strong induction on `p.foldr max 0`, generalizing bothp andN. For a nodup list of length at least2, its maximum is positive; every normalized child's maximum is at most half of it. Therefore both recursive inputs have strictly smaller measure, even when all old values have one parity. The target is not part of the measure.

The other child is extended first. H is then calculated from its entire lifted finite output. Only afterwards is the preferred child extended with target `max N (2*H)`. That target may be extremely large; the induction hypothesis is uniform in it. This is not circular recursion on the size of the new output. The chosen normalized targets over-cover rather than under-cover the necessary actual values.

Assembly appends only the two new child suffixes afterp. Its exact parity-projection identities guarantee that the child's old internal order and new suffix are both preserved. Nodup of both projections implies nodup of the whole parent, including all old/new and cross-parity collision cases. Coverage is pulled back through `liftValue` for each parity. Every hypothesis of the central merge is thus discharged.

## 6. Omega-type bijection and final theorem

Limit builds a countable chain by ordinary natural recursion, making a finite extension cover0 throughn at stage n+1. Coverage implies stage n+1 has at least n+1 entries. Hence the definition `f i = (p (i+1)).getD i 0` is always in range.

The prefix relation proves stabilization at every index. A common later nodup list proves injectivity; the stage coveringx proves thatx is attained, giving surjectivity. `Equiv.ofBijective` therefore produces an actual `ℕ ≃ ℕ`, not merely an injection, an arbitrary linear order, or a permutation of a sparse subset. Any four indices stabilize together inside one avoiding finite stage. The tail witnesses need not converge and are not used to definef.

Extension instantiates this generic bridge with the proved `Admissible` predicate and extension theorem. The aggregator has no remaining assumptions: it proves both the negative universal public statement and an existential avoiding bijection, plus the positive-natural negative statement.

Classical choice in selecting a fair chain is ordinary foundational choice. It is not a hypothesis asserting any unproved extension theorem. The concrete human recursion is stronger in effectiveness than the existential formal chain requires.

## 7. Source identity

SHA-256 values of the fully read source versions:

| Module | SHA-256 |
|---|---|
| Erdos196 | f9be0cb446f69a5e65c830cf234c834ef4456259210dea42547d1abfb88880f4 |
| Core | b78484c873576551b114d952fc64ce9a74cbf04fbc0148e25fd5574c04f8bc9e |
| Tree | 612900b49974e71753e955b0f6d8f5a5407066a5d3bd0c7d0d0dc12bc986b0c4 |
| Base | 49417d311a19aabc745c9dfb589771605b05ef2806d149a58ea97abaea0dace7 |
| Children | a840ed7c057c5125ccc3e41a972f9ae761e0b91512d22edf6d21de399b69dc61 |
| Assembly | 47f0cffb4ed84451769350b7f6b7a0a5abe5aa7f47f386702797330f77d8808f |
| ParityLift | ecac6fedf23f320072b287d4963ed70ad0ba0527a54ca756b93d2b07f8660d7d |
| Limit | e9cf5915a5c44dd4179f64f00e93e38f8c5e6a83ac124b9afd032efdd1220666 |
| Extension | 7a9da9205666fe58dc4ad26da56759991e168214f2f4971a43eac19953463fa6 |
| Correspondence | 2220c308bd410b27184f688249bd352a636c1b1072b9ee67b59a369b5ac6c890 |

Source scanning found no `sorry`, `admit`, `axiom`, `unsafe`, `partial`, `implemented_by`, or `native_decide` in these ten files. This scan is only a supplement to, not a replacement for, the final imported theorem axiom check.

## 8. Independent final imported-artifact check

The ten source hashes in the independently imported clean package exactly match Section7. The parent performed the full clean build; this auditor separately ran `lake env lean --stdin`, importing only the final `Erdos196` aggregator, with the following commands:

```lean
import Erdos196
#print axioms Erdos196.erdos_196_negative
#print axioms Erdos196.erdos_196_counterexample
#print axioms Erdos196.erdos_196_positive_integers_negative
#check Erdos196.erdos_196_negative
#check Erdos196.erdos_196_counterexample
#check Erdos196.erdos_196_positive_integers_negative
#print Erdos196.OriginalQuestion
#print Erdos196.AP4
#print HasMonotoneAP
#print List.IsAPOfLengthWith
```

Exit status0. The exact axiom output was:

```text
'Erdos196.erdos_196_negative' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos196.erdos_196_counterexample' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos196.erdos_196_positive_integers_negative' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The printed definition bodies match Section1. The final canonical theorem printed as `¬∀ (f : ℕ ≃ ℕ), HasMonotoneAP (⇑f) 4`; the existential theorem printed as an avoiding equivalence; the positive theorem printed as the negation of `PositiveOriginalQuestion`.

These are Lean's ordinary foundational axioms, not additional number-theoretic or combinatorial assumptions. In particular, the result does not depend on `sorryAx`, a supplied finite-extension axiom, an admitted original statement, or a native-evaluation trust shortcut. The audit passes under the normal Lean/kernel and pinned-library trust boundary. It remains separate from a novelty or priority determination.
