# A permutation without monotone four-term arithmetic progressions

We construct a permutation of the natural numbers containing no increasing
or decreasing four-term arithmetic progression as a subsequence. This gives
a negative answer to [Erdős problem 196](https://www.erdosproblems.com/196).

[Read the proof](FINAL-HUMAN-PROOF.md) ·
[Lean formalization](Erdos196.lean) ·
[Verified on Jig](https://jig.so/p/73?s=4)

## Theorem

There exists a bijection $f : \mathbb{N} \to \mathbb{N}$ such that, for every
$i < j < k < l$, the sequence

$$f(i),\quad f(j),\quad f(k),\quad f(l)$$

is not a nonconstant arithmetic progression.

Here $\mathbb{N} = \{0,1,2,\ldots\}$. Shifting both indices and values by one
gives the equivalent statement for the positive integers.

## Construction

The proof extends finite prefixes while maintaining an admissible
binary-residue-tree order on the unused values. The two parity classes
are extended in a prescribed order, with a coverage bound excluding
odd-difference progressions; even-difference progressions reduce to the
corresponding child orders.

Strong induction on the maximum of the existing prefix gives extensions
covering every prescribed finite interval. A nested sequence of these
extensions yields the required permutation.

The [proof](FINAL-HUMAN-PROOF.md) develops the extension lemma and the
passage to the infinite permutation. The [formalization](Erdos196.lean)
also proves equivalence with the public formulation of the problem.

## Reproducing the formalization

With [Elan](https://github.com/leanprover/elan) installed, run from the
repository root:

```sh
lake exe cache get
lake build
lake env lean Erdos196.lean
```

The repository pins Lean `v4.34.0-rc2` and Mathlib
`141f6b6455959bfeb0b2a6b04118031191d62683`.
The final command prints the axiom dependencies of the three main theorems:
`propext`, `Classical.choice`, and `Quot.sound`.

Jig independently checked the formalization against its pinned Lean
`v4.33.0` environment. See the [verification record](JIG-VERIFICATION.md)
for the exact source commit, toolchain, and verifier output.

## References

- Davis, Entringer, Graham, and Simmons,
  [*On permutations containing no long arithmetic progressions*](https://matwbn.icm.edu.pl/ksiazki/aa/aa34/aa3417.pdf),
  Acta Arithmetica 34 (1977), 81–90.
- Geneson,
  [*Density bounds for permutations avoiding monotone arithmetic progressions*](https://arxiv.org/html/2608.12604v1)
  (2026).
- [Formal Conjectures: Erdős problem 196](https://github.com/google-deepmind/formal-conjectures/blob/c252a41054125b5fd9c8356e2137cd9b55337657/FormalConjectures/ErdosProblems/196.lean).

The classical binary-order ingredients are attributed in the proof.
[Literature notes](FINAL-PRIOR-ART-AUDIT.md) and
[statement correspondence](CORRESPONDENCE-VERIFICATION.md) provide further detail.

## Acknowledgments

Thanks to Joshua Wolk for creating [Jig](https://jig.so), and to Declan
Gessel for inspiring the competition.

The proof and Lean formalization were developed with Codex.
