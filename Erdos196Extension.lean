import Erdos196Base
import Erdos196Limit
import Erdos196Assembly
import Erdos196ParityLift

namespace Erdos196

theorem admissible_noAP4List {p : List ℕ} (hp : Admissible p) : NoAP4List p := by
  obtain ⟨hn, t, ht⟩ := hp
  have before_indices (i j : ℕ) (hij : i < j) (hj : j < p.length) :
      Before p (fun x y => treeBefore t x y = true) (p.getD i 0) (p.getD j 0) := by
    have hi : i < p.length := hij.trans hj
    rw [← List.getElem_eq_getD (h := hi) 0, ← List.getElem_eq_getD (h := hj) 0]
    simp only [Before, List.getElem_mem, ↓reduceIte]
    exact Or.inr (by simpa only [hn.idxOf_getElem] using hij)
  intro i j k l hij hjk hkl hl hap
  exact ht _ _ _ _ hap ⟨before_indices i j hij (by omega),
    before_indices j k hjk (by omega), before_indices k l hkl hl⟩

theorem admissible_empty : Admissible [] := by
  exact fixed_sorted_admissible (h := 0) (p := []) (by simp) (by simp)

theorem admissible_finite_extension (p : List ℕ) (hp : Admissible p) (N : ℕ) :
    ∃ q, Admissible q ∧ p.IsPrefix q ∧ ∀ x, x ≤ N → x ∈ q := by
  induction hn : p.foldr max 0 using Nat.strong_induction_on generalizing p N with
  | h n ih =>
    by_cases hlen : p.length ≤ 1
    · obtain ⟨q, hpq, hq, hcov⟩ := small_finite_extension p hlen N
      exact ⟨q, hq, hpq, hcov⟩
    have hlen' : 2 ≤ p.length := by omega
    obtain ⟨oldTree, hold⟩ := hp.2
    let a := oldTree []
    have hchild (b : Bool) : (childPrefix p b).foldr max 0 < n := by
      rw [← hn]
      exact childPrefix_max_lt hp.1 hlen' b
    obtain ⟨qB, hqB, hpB, hcovB⟩ :=
      ih _ (hchild (!a)) (childPrefix p (!a)) (admissible_childPrefix hp (!a)) N rfl
    obtain ⟨rB, rfl⟩ := hpB
    let H := ((childPrefix p (!a) ++ rB).map (liftValue (!a))).foldr max 0
    obtain ⟨qA, hqA, hpA, hcovA⟩ :=
      ih _ (hchild a) (childPrefix p a) (admissible_childPrefix hp a) (max N (2 * H)) rfl
    obtain ⟨rA, rfl⟩ := hpA
    let q := assembleChildren p rA rB a
    have hA : Admissible (childPrefix q a) := by
      simpa only [q, childPrefix_assemble_preferred] using hqA
    have hB : Admissible (childPrefix q (!a)) := by
      simpa only [q, childPrefix_assemble_other] using hqB
    have hchildren (b : Bool) : Admissible (childPrefix q b) := by
      have hb : b = a ∨ b = !a := by cases b <;> cases a <;> decide
      rcases hb with hb | hb
      · simpa only [hb] using hA
      · simpa only [hb] using hB
    have hqnodup : q.Nodup := assembleChildren_nodup p rA rB a hqA.1 hqB.1
    have hpref_cover (x : ℕ) (hx : parity x = a) (hbound : x ≤ 2 * H) : x ∈ q := by
      have hrec : liftValue a (x / 2) = x := by simpa [hx] using liftValue_parity_div x
      have hm : x / 2 ∈ childPrefix q a := by
        rw [show childPrefix q a = childPrefix p a ++ rA from childPrefix_assemble_preferred ..]
        apply hcovA
        have := Nat.div_le_self x 2
        omega
      simpa only [hrec] using (mem_childPrefix q a (x / 2)).mp hm
    have hqgood : Admissible q := by
      apply admissible_parity_merge p (rA.map (liftValue a)) (rB.map (liftValue (!a))) oldTree H
      · exact hqnodup
      · exact hold
      · intro x hx
        obtain ⟨y, _, rfl⟩ := List.mem_map.mp hx
        exact parity_liftValue a y
      · intro x hx
        obtain ⟨y, _, rfl⟩ := List.mem_map.mp hx
        simp only [parity_liftValue]
        exact Bool.not_ne_self a
      · intro x hx
        apply List.le_max_of_le (l := (childPrefix p (!a) ++ rB).map (liftValue (!a))) _ le_rfl
        obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
        exact List.mem_map.mpr ⟨y, List.mem_append_right _ hy, rfl⟩
      · exact hpref_cover
      · exact hchildren false
      · exact hchildren true
    refine ⟨q, hqgood, assembleChildren_prefix p rA rB a, ?_⟩
    apply assembleChildren_coverage p rA rB a N
    · intro x hx
      apply hcovA
      have hd := Nat.div_le_div_right (c := 2) hx
      rw [div_liftValue] at hd
      have := Nat.div_le_self N 2
      omega
    · intro x hx
      apply hcovB
      have hd := Nat.div_le_div_right (c := 2) hx
      rw [div_liftValue] at hd
      exact hd.trans (Nat.div_le_self N 2)

theorem exists_avoiding_permutation : ∃ f : ℕ ≃ ℕ, NoAP4Sequence f := by
  exact permutation_of_good_extensions Admissible admissible_empty
    (fun _ hp => hp.1) (fun _ hp => admissible_noAP4List hp) admissible_finite_extension

theorem original_question_false : ¬ OriginalQuestion :=
  avoiding_permutation_refutes_original exists_avoiding_permutation

#print axioms original_question_false

end Erdos196
