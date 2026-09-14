# A one-sided permutation with no monotone four-term arithmetic progression

2026-09-13. Self-contained human proof aligned with the Lean development in `lean196/`. Final build, source-meaning review, and provenance checks are separate verification records; this document itself does not certify those checks or claim publication priority.

## Theorem

There exists a bijection f from the nonnegative integers to themselves such that no four values of f, taken in increasing index order, form a nonconstant arithmetic progression in either numerical direction.

Thus the answer to the original one-sided permutation question, Erdős problem 196, is negative. Adding 1 to every value gives the equivalent positive-integer statement. The original question is recorded in Davis–Entringer–Graham–Simmons (1977), *On permutations containing no long arithmetic progressions*, Acta Arithmetica 34, 81–90: https://matwbn.icm.edu.pl/ksiazki/aa/aa34/aa3417.pdf . The construction below produces order type omega, not merely an avoiding total order of a different order type.

**Prior work.** The binary recursion, its three-term-progression avoidance, and the opposite-pair comparison identity are classical ingredients, not claimed as new here. [Geneson, *Density bounds for permutations avoiding monotone arithmetic progressions*, Section 2](https://arxiv.org/html/2608.12604v1#S2), credits Davis–Entringer–Graham–Simmons and Ardal–Brown–Jungić for the binary constructions and attributes the pair-comparison identity to Hirose–Saito. The contribution claimed in the present argument is the adaptive finite-prefix extension lemma and its fair completion to a permutation of all nonnegative integers. This is distinct from density-supremum results, which need not produce such a permutation.

Throughout, a time-ordered four-term progression means a tuple (u,v,w,z) of nonnegative integers satisfying

    u+w=2v,    v+z=2w,    u≠v.

Its common difference may be positive or negative. Both cases are treated together.

## 1. Binary-tree orders and admissible prefixes

Partition the nonnegative integers into their two parity classes. Independently choose which class comes first. Within each class, divide by 2 after subtracting its parity, again choose which parity class comes first, and continue in this way, making an independent choice at every node.

For distinct x,y, the comparison is decided at their least differing binary digit. This defines a strict total order, which we call a binary-tree order. The choices may differ between nodes at the same depth. Such an order need not have order type omega.

Every binary-tree order avoids monotone nonconstant three-term arithmetic progressions. Indeed, if the common difference has 2-adic valuation j, then the two endpoints agree at bit j and the midpoint has the opposite bit. All three values have the same lower bits. At the corresponding node the midpoint is therefore either before both endpoints or after both, never between them. This proof applies to either sign of the difference.

A finite list P of distinct nonnegative integers is **admissible** if there is a binary-tree order on the integers outside P such that the concatenated total order

    P in its given list order; then all remaining integers in that tree order

has no time-ordered nonconstant four-term arithmetic progression. We call the tree order a witness for P. The witness may be changed when P is extended.

We will prove the following uniform extension lemma.

**Extension lemma.** For every admissible finite list P and every N>=0, there is an admissible finite list Q extending P as an initial list and containing every integer from 0 through N.

## 2. A two-order completion of an empty or singleton prefix

Fix an anchor a. Let T_a be the binary-tree order which, at every node of depth j, prefers the j-th bit of a. In particular, a precedes every other integer in T_a. Let T_a^opp reverse the preferred child at every node.

For a finite set F containing a, list its elements in T_a order and place all remaining integers afterward in T_a^opp order. This concatenated order has no monotone four-term progression.

To prove this, each block is three-term-progression-free, so a bad four-term progression must have exactly two terms in each block. Write it in time order as (u,v,w,z), with signed common difference d≠0. Set j=v_2(|d|). The pair (u,v) and the pair (w,z) have the same least differing node, and their first entries have the same bit at that node: w=u+2d and z=v+2d, while 2d is divisible by 2^(j+1). Therefore the two pairs have the same orientation in T_a and opposite orientations when the second is read in T_a^opp. They cannot both occur in the required time order. This proves the assertion.

For a singleton prefix (a), apply it to F={a} union {0,...,N}. The first element is a, so this is an admissible extension with the required coverage. For an empty prefix, use the same construction with a=0. These constructions settle the extension lemma when P has at most one entry.

The opposite order on the tail is essential. No assertion about a same-orientation two-block construction is used.

## 3. The parity merge

Let P be admissible and fix a witness tree. Call the parity preferred at its root A, and call the other parity B. The symbols A and B refer to parity values in {0,1}, not to numerical inequalities.

For each parity e, filter P to that parity, keeping its list order, and normalize its entries by

    x -> (x-e)/2.

Denote the resulting child prefix by P_e. It is admissible under the corresponding child of the original witness: a forbidden child progression would lift to a forbidden same-parity progression in the original order.

Suppose we have obtained finite admissible child extensions Q_B of P_B and Q_A of P_A. Let H be the maximum actual value among the B integers represented by Q_B; if that set is empty, put H=0. Require Q_A to cover enough values that every actual A integer at most 2H is represented in Q_A.

Form the new finite list Q by keeping P unchanged, appending the newly added A values in their child-extension order, and then appending the newly added B values in their child-extension order. Its two parity projections are exactly Q_A and Q_B. In particular Q has distinct entries.

Give the remaining tail a tree whose root still prefers A, but whose two child trees are the witnesses for the completed child prefixes. In chronological blocks the resulting total order is

    P ; new A values ; new B values ; A tail ; B tail.       (3.1)

Every new B value is at most H. Every A-tail value is greater than 2H.

We claim that this order has no monotone four-term progression. A progression with even common difference lies wholly in one parity class and is excluded by the corresponding completed child order. It remains to check odd common differences.

Read a putative odd-difference progression in increasing time order as (u,v,w,z). Its parities alternate. The entries belonging to P form an initial segment of this time order.

**At least three entries belong to P.** If all four do, the old witness already excludes them. If exactly the first three do, the fourth originally lay in the old tail; those same four values would therefore already have violated old admissibility.

**Exactly two entries belong to P.** The last two values were both outside the old prefix. The parity pattern cannot be A,B,A,B: under the original root preference A, its last A value would precede its last B value, already producing a forbidden progression with the first two old entries.

Thus the only possible pattern is B,A,B,A. If w is in B tail, z cannot follow it, because every A-tail value precedes B tail, and every finite value is earlier still. Hence w must be a new B value, so w<=H. If z is a new A value it precedes w, again impossible. Otherwise z is in A tail, so z>2H. But the progression identity gives

    z=2w-v<=2H,

since v>=0. This is a contradiction.

**At most one entry belongs to P, with pattern A,B,A,B.** The second entry v is not old. It cannot be in B tail, since no A value could then follow it. Thus v is a new B value. The third entry w must then be in A tail, as every new A value precedes every new B value. Consequently v<=H and w>2H, while

    u=2v-w<0,

contradicting nonnegativity.

**At most one entry belongs to P, with pattern B,A,B,A.** The second entry v cannot be in A tail, since the next B value would then be in B tail and no A value could follow it. Thus v is new A. The third entry w cannot be in B tail for the same reason, so it is new B. The final entry z must be in A tail. Hence w<=H and z>2H, whereas z=2w-v<=2H, again a contradiction.

These cases exhaust all possibilities. None assumes that the numerical common difference is positive. Therefore Q is admissible. If the finite B block is empty, cases requiring a new B value simply cannot occur; the convention H=0 causes no exceptional case.

## 4. Proof of the uniform extension lemma

Proceed by strong induction on the maximum M of the old finite prefix, taking the maximum of the empty list to be 0. The cases with at most one entry were proved in Section 2.

Otherwise P has at least two distinct nonnegative entries, so M>=1. Each normalized parity child has maximum at most floor(M/2), with the maximum of an empty child again 0. Thus BOTH child maxima are strictly less than M. This remains true if all old entries have the same parity.

First use the inductive hypothesis to extend the nonpreferred child P_B so that its normalized list contains every integer through N. Call the extension Q_B, and compute its actual maximum H as in Section 3.

Next use the inductive hypothesis to extend P_A so that its normalized list contains every integer through max(N,2H). Call it Q_A. This is more coverage than strictly necessary, but it makes both requirements immediate:

- Every actual A value at most N has normalized value at most N and is included.
- Every actual A value at most 2H has normalized value at most 2H and is included.

Similarly every actual B value at most N occurs in the first child extension. Apply the parity merge from Section 3. The resulting Q is admissible, extends the original list P without reordering it, and contains {0,...,N}.

This induction is well founded even though H and the second required bound can be arbitrarily large. The induction parameter is the maximum of the OLD child prefix, not the required bound or the size of the newly produced buffer. That parameter strictly decreases in every recursive call. The construction therefore gives a finite extension at each stage, proving the lemma.

## 5. Passing to a one-sided permutation

The empty prefix is admissible. Starting with it, apply the extension lemma successively for required bounds 0,1,2,..., obtaining finite lists

    P_0 initial-segment-of P_1 initial-segment-of P_2 ...

which eventually contain every nonnegative integer. All lists have distinct entries, and their lengths tend to infinity because their covered intervals do. Their coherent union therefore defines a bijection f from the nonnegative integers to themselves: the value at each fixed list position eventually exists and can never change.

If four values of this enumeration formed a monotone nonconstant arithmetic progression in index order, all four positions would occur in some finite P_j. Its admissibility excludes that progression, independently of the tree witness chosen for its unused tail. This contradiction proves the theorem.

Notice that the tree witnesses themselves need not stabilize, and their individual order types are irrelevant. Only the finite prefixes stabilize. This is what supplies an actual one-sided permutation rather than a two-sided or non-well-ordered avoiding order.

## Lean correspondence

The proof is represented by the following modules and theorem interfaces. No finite search criterion or computationally tested cutoff is needed for the proof.

- `Erdos196Core.lean`: `AP4`, `Tree`, `treeBefore`, `Before`, `Admissible`, and the literal `OriginalQuestion`.
- `Erdos196Tree.lean`: root/child comparison identities and parity normalization.
- `Erdos196Base.lean`: `fixed_two_scan`, `singleton_finite_extension`, `small_finite_extension` (Section 2).
- `Erdos196Children.lean`: `before_childPrefix`, `admissible_childPrefix`, `childPrefix_max_lt`.
- `Erdos196Assembly.lean`: exact parity projections, distinctness, initial-prefix preservation, and coverage of the merged list.
- `Erdos196ParityLift.lean`: `admissible_parity_merge` (the complete Section 3 argument, including old-prefix and both signed-difference cases).
- `Erdos196Extension.lean`: `admissible_finite_extension`, `exists_avoiding_permutation`, `original_question_false`.
- `Erdos196Limit.lean`: `permutation_of_fair_chain` and `permutation_of_good_extensions` (Section 5).

Build and axiom-audit records should be consulted separately to identify the exact verified source snapshot. This note is not a substitute for those records.
