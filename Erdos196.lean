import Erdos196Extension
import Erdos196Correspondence

/-! Full negative resolution of the one-sided permutation question, #196. -/
namespace Erdos196

/-- The exact public canonical question has a negative answer. -/
theorem erdos_196_negative : ¬ (∀ f : ℕ ≃ ℕ, HasMonotoneAP f 4) :=
  avoiding_permutation_refutes_canonical exists_avoiding_permutation

/-- Equivalently, one bijection avoids both orientations at every four indices. -/
theorem erdos_196_counterexample : ∃ f : ℕ ≃ ℕ, ¬ HasMonotoneAP f 4 := by
  obtain ⟨f, hf⟩ := exists_avoiding_permutation
  exact ⟨f, (noAP4Sequence_iff_not_canonical f f.injective).mp hf⟩

/-- The positive-integer version of the original question also has a negative answer. -/
theorem erdos_196_positive_integers_negative : ¬ PositiveOriginalQuestion :=
  avoiding_permutation_refutes_positive exists_avoiding_permutation

#print axioms erdos_196_negative
#print axioms erdos_196_counterexample
#print axioms erdos_196_positive_integers_negative

end Erdos196
