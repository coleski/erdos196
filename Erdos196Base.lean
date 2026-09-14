import Erdos196Core

namespace Erdos196

/-- Least-significant-bit order preferring the bits of `h`. -/
def fixedBefore (h x y : ℕ) : Prop :=
  if x = y then False else
  if x % 2 = y % 2 then fixedBefore (h / 2) (x / 2) (y / 2)
  else x % 2 = h % 2
termination_by x + y
decreasing_by omega

theorem fixedBefore_irrefl (h x : ℕ) : ¬ fixedBefore h x x := by
  rw [fixedBefore]
  simp

theorem fixedBefore_same {h x y : ℕ} (hp : x % 2 = y % 2) :
    fixedBefore h x y ↔ fixedBefore (h / 2) (x / 2) (y / 2) := by
  rw [fixedBefore]
  split_ifs with he
  · subst y
    simp [fixedBefore_irrefl]
  · rfl

theorem fixedBefore_different {h x y : ℕ} (hp : x % 2 ≠ y % 2) :
    fixedBefore h x y ↔ x % 2 = h % 2 := by
  rw [fixedBefore]
  have hne : x ≠ y := by omega
  simp [hne, hp]

theorem fixedBefore_total (h x y : ℕ) (hne : x ≠ y) :
    fixedBefore h x y ∨ fixedBefore h y x := by
  induction hn : x + y using Nat.strong_induction_on generalizing h x y with
  | h n ih =>
    by_cases hp : x % 2 = y % 2
    · rw [fixedBefore_same hp, fixedBefore_same hp.symm]
      exact ih (x / 2 + y / 2) (by omega) (h / 2) (x / 2) (y / 2) (by omega) rfl
    · rw [fixedBefore_different hp, fixedBefore_different (Ne.symm hp)]
      omega

theorem fixedBefore_asymm {h x y : ℕ} (hxy : fixedBefore h x y) :
    ¬ fixedBefore h y x := by
  induction hn : x + y using Nat.strong_induction_on generalizing h x y with
  | h n ih =>
    by_cases hp : x % 2 = y % 2
    · rw [fixedBefore_same hp] at hxy
      rw [fixedBefore_same hp.symm]
      by_cases he : x = y
      · subst y
        exact False.elim (fixedBefore_irrefl _ _ hxy)
      · exact ih (x / 2 + y / 2) (by omega) hxy rfl
    · rw [fixedBefore_different hp] at hxy
      rw [fixedBefore_different (Ne.symm hp)]
      omega

theorem fixedBefore_trans {h x y z : ℕ}
    (hxy : fixedBefore h x y) (hyz : fixedBefore h y z) : fixedBefore h x z := by
  induction hn : x + y + z using Nat.strong_induction_on generalizing h x y z with
  | h n ih =>
    by_cases hxyP : x % 2 = y % 2 <;> by_cases hyzP : y % 2 = z % 2
    · rw [fixedBefore_same hxyP] at hxy
      rw [fixedBefore_same hyzP] at hyz
      rw [fixedBefore_same (hxyP.trans hyzP)]
      have hne : x ≠ y := by
        intro he
        subst y
        exact fixedBefore_irrefl _ _ hxy
      exact ih (x / 2 + y / 2 + z / 2) (by omega) hxy hyz rfl
    · rw [fixedBefore_different hyzP] at hyz
      rw [fixedBefore_different (show x % 2 ≠ z % 2 by omega)]
      omega
    · rw [fixedBefore_different hxyP] at hxy
      rw [fixedBefore_different (show x % 2 ≠ z % 2 by omega)]
      exact hxy
    · rw [fixedBefore_different hxyP] at hxy
      rw [fixedBefore_different hyzP] at hyz
      omega

theorem fixedBefore_anchor (h x : ℕ) (hne : h ≠ x) : fixedBefore h h x := by
  induction hn : h + x using Nat.strong_induction_on generalizing h x with
  | h n ih =>
    by_cases hp : h % 2 = x % 2
    · rw [fixedBefore_same hp]
      exact ih (h / 2 + x / 2) (by omega) (h / 2) (x / 2) (by omega) rfl
    · exact (fixedBefore_different hp).2 rfl

theorem fixedBefore_noAP3 {h a b c : ℕ} (hap : a + c = 2 * b) (hne : a ≠ b) :
    ¬ (fixedBefore h a b ∧ fixedBefore h b c) := by
  induction hn : a + b + c using Nat.strong_induction_on generalizing h a b c with
  | h n ih =>
    by_cases hp : a % 2 = b % 2
    · have hp' : b % 2 = c % 2 := by omega
      rw [fixedBefore_same hp, fixedBefore_same hp']
      exact ih (a / 2 + b / 2 + c / 2) (by omega) (by omega) (by omega) rfl
    · have hp' : b % 2 ≠ c % 2 := by omega
      rw [fixedBefore_different hp, fixedBefore_different hp']
      omega

theorem fixedBefore_opposite_pairs {h a b c d : ℕ} (hap : AP4 a b c d) :
    fixedBefore h a b ↔ fixedBefore h c d := by
  induction hn : a + b + c + d using Nat.strong_induction_on generalizing h a b c d with
  | h n ih =>
    obtain ⟨hac, hbd, hne⟩ := hap
    by_cases hp : a % 2 = b % 2
    · have hp' : c % 2 = d % 2 := by omega
      rw [fixedBefore_same hp, fixedBefore_same hp']
      exact ih (a / 2 + b / 2 + c / 2 + d / 2) (by omega)
        (show AP4 (a / 2) (b / 2) (c / 2) (d / 2) from ⟨by omega, by omega, by omega⟩) rfl
    · have hp' : c % 2 ≠ d % 2 := by omega
      rw [fixedBefore_different hp, fixedBefore_different hp']
      omega

theorem fixedBefore_affine_bit (h x y p : ℕ) (hp : p < 2) :
    fixedBefore h (2*x+p) (2*y+p) ↔ fixedBefore (h/2) x y := by
  rw [fixedBefore_same (show (2*x+p)%2 = (2*y+p)%2 by omega)]
  have hx : (2*x+p)/2 = x := by omega
  have hy : (2*y+p)/2 = y := by omega
  rw [hx, hy]

theorem fixedBefore_scale (h x y k r : ℕ) (hr : r < 2^k) :
    fixedBefore h (2^k*x+r) (2^k*y+r) ↔ fixedBefore (h/2^k) x y := by
  induction k generalizing h r with
  | zero =>
    have : r = 0 := by simpa using hr
    subst r
    simp
  | succ k ih =>
    have hx : 2^(k+1)*x+r = 2*(2^k*x+r/2)+r%2 := by
      rw [pow_succ]
      have := Nat.mod_add_div r 2
      nlinarith
    have hy : 2^(k+1)*y+r = 2*(2^k*y+r/2)+r%2 := by
      rw [pow_succ]
      have := Nat.mod_add_div r 2
      nlinarith
    rw [hx, hy, fixedBefore_affine_bit _ _ _ _ (Nat.mod_lt _ (by decide))]
    rw [ih (h/2) (r/2) (by rw [pow_succ] at hr; omega)]
    rw [Nat.div_div_eq_div_mul, ← pow_succ']

def fixedTree (h : ℕ) (reverse : Bool) : Tree := fun path =>
  if reverse then !(parity (h / 2^path.length)) else parity (h / 2^path.length)

theorem childTree_fixed (h : ℕ) (reverse b : Bool) :
    childTree (fixedTree h reverse) b = fixedTree (h/2) reverse := by
  funext path
  simp [childTree, fixedTree, Nat.div_div_eq_div_mul, pow_succ, Nat.mul_comm]

theorem treeBefore_fixed (h x y : ℕ) (reverse : Bool) :
    treeBefore (fixedTree h reverse) x y = true ↔
      if reverse then fixedBefore h y x else fixedBefore h x y := by
  induction hn : x + y using Nat.strong_induction_on generalizing h x y reverse with
  | h n ih =>
    by_cases he : x = y
    · subst y
      rw [treeBefore]
      simp [fixedBefore_irrefl]
    · by_cases hp : x % 2 = y % 2
      · have hp' : parity x = parity y := by simp [parity, hp]
        rw [treeBefore]
        simp only [he, hp', ite_false, ite_true, childTree_fixed]
        rw [ih (x/2+y/2) (by omega) (h/2) (x/2) (y/2) reverse rfl]
        cases reverse <;> simp only [Bool.false_eq_true, ite_false, ite_true]
        · exact (fixedBefore_same hp).symm
        · exact (fixedBefore_same hp.symm).symm
      · have hp' : parity x ≠ parity y := by simp [parity]; omega
        rw [treeBefore]
        simp only [he, hp', ite_false, fixedTree, List.length_nil, pow_zero, Nat.div_one]
        cases reverse <;> simp only [Bool.false_eq_true, ite_false, ite_true]
        · rw [fixedBefore_different hp]
          simp [parity]
          omega
        · rw [fixedBefore_different (Ne.symm hp)]
          rcases Nat.mod_two_eq_zero_or_one x with hx | hx <;>
            rcases Nat.mod_two_eq_zero_or_one y with hy | hy <;>
            rcases Nat.mod_two_eq_zero_or_one h with hh | hh <;>
            simp_all [parity]

def fixedLE (h x y : ℕ) : Prop := x = y ∨ fixedBefore h x y

instance fixedLE_trans (h : ℕ) : IsTrans ℕ (fixedLE h) where
  trans := by
    intro x y z hxy hyz
    rcases hxy with rfl | hxy
    · exact hyz
    rcases hyz with rfl | hyz
    · exact Or.inr hxy
    exact Or.inr (fixedBefore_trans hxy hyz)

instance fixedLE_antisymm (h : ℕ) : Std.Antisymm (fixedLE h) where
  antisymm := by
    intro x y hxy hyx
    rcases hxy with he | hxy
    · exact he
    rcases hyx with he | hyx
    · exact he.symm
    exact False.elim (fixedBefore_asymm hxy hyx)

instance fixedLE_total (h : ℕ) : Std.Total (fixedLE h) where
  total := by
    intro x y
    by_cases he : x = y
    · exact Or.inl (Or.inl he)
    rcases fixedBefore_total h x y he with hxy | hyx
    · exact Or.inl (Or.inr hxy)
    · exact Or.inr (Or.inr hyx)

theorem pairwise_ordered {h : ℕ} {p : List ℕ}
    (hp : p.Pairwise (fixedLE h)) {x y : ℕ} (hx : x ∈ p) (hy : y ∈ p)
    (hxy : p.idxOf x < p.idxOf y) : fixedBefore h x y := by
  have hz := hp.rel_getElem_of_lt (List.idxOf_lt_length_of_mem hx)
    (List.idxOf_lt_length_of_mem hy) hxy
  simp only [List.getElem_idxOf] at hz
  rcases hz with he | hz
  · subst y
    omega
  · exact hz

theorem fixed_two_scan {h : ℕ} {p : List ℕ} (hp : p.Pairwise (fixedLE h)) :
    NoAP4Rel (Before p (fun x y => fixedBefore h y x)) := by
  intro a b c d hap habcd
  have hab : a ≠ b := hap.2.2
  have hbc : b ≠ c := by obtain ⟨_, _, _⟩ := hap; omega
  have hcd : c ≠ d := by obtain ⟨_, _, _⟩ := hap; omega
  by_cases ha : a ∈ p <;> by_cases hb : b ∈ p <;>
      by_cases hc : c ∈ p <;> by_cases hd : d ∈ p <;>
      simp only [Before, ha, hb, hc, hd, ite_true, ite_false, not_true_eq_false,
        not_false_eq_true, false_or, true_or, true_and, false_and, and_false, and_true] at habcd
  · exact fixedBefore_noAP3 hap.1 hab
      ⟨pairwise_ordered hp ha hb habcd.1, pairwise_ordered hp hb hc habcd.2.1⟩
  · exact fixedBefore_noAP3 hap.1 hab
      ⟨pairwise_ordered hp ha hb habcd.1, pairwise_ordered hp hb hc habcd.2⟩
  · exact fixedBefore_asymm ((fixedBefore_opposite_pairs hap).1
      (pairwise_ordered hp ha hb habcd.1)) habcd.2
  · exact fixedBefore_noAP3 (show d + b = 2*c by have := hap.2.1; omega) hcd.symm
      ⟨habcd.2, habcd.1⟩
  · exact fixedBefore_noAP3 (show d + b = 2*c by have := hap.2.1; omega) hcd.symm
      ⟨habcd.2.2, habcd.2.1⟩

theorem fixed_sorted_admissible {h : ℕ} {p : List ℕ} (hn : p.Nodup)
    (hp : p.Pairwise (fixedLE h)) : Admissible p := by
  refine ⟨hn, fixedTree h true, ?_⟩
  have he : (fun x y => treeBefore (fixedTree h true) x y = true) =
      (fun x y => fixedBefore h y x) := by
    funext x y
    apply propext
    simpa using treeBefore_fixed h x y true
  rw [he]
  exact fixed_two_scan hp

theorem singleton_finite_extension (h N : ℕ) :
    ∃ q : List ℕ, [h] <+: q ∧ Admissible q ∧ ∀ x ≤ N, x ∈ q := by
  classical
  let s := (Finset.range (N+1)).erase h
  let q := h :: s.sort (fixedLE h)
  have hmem : h ∉ s.sort (fixedLE h) := by simp [s]
  have hn : q.Nodup := List.nodup_cons.mpr ⟨hmem, s.sort_nodup _⟩
  have hp : q.Pairwise (fixedLE h) := by
    apply List.pairwise_cons.mpr
    refine ⟨?_, s.pairwise_sort _⟩
    intro x hx
    exact Or.inr (fixedBefore_anchor h x (by intro he; subst x; exact hmem hx))
  refine ⟨q, ?_, fixed_sorted_admissible hn hp, ?_⟩
  · exact ⟨s.sort (fixedLE h), rfl⟩
  · intro x hx
    by_cases he : x = h
    · simp [q, he]
    · have hs : x ∈ s := by simp [s, he]; omega
      simp [q, hs]

theorem small_finite_extension (p : List ℕ) (hlen : p.length ≤ 1) (N : ℕ) :
    ∃ q : List ℕ, p <+: q ∧ Admissible q ∧ ∀ x ≤ N, x ∈ q := by
  cases p with
  | nil =>
    obtain ⟨q, _, hq, hcov⟩ := singleton_finite_extension 0 N
    exact ⟨q, List.nil_prefix, hq, hcov⟩
  | cons h tail =>
    cases tail with
    | nil => exact singleton_finite_extension h N
    | cons x tail => simp at hlen

#print axioms small_finite_extension

end Erdos196
