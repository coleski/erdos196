import Erdos196Children

namespace Erdos196

private theorem childPrefix_cons_eq (p : List ℕ) (a : ℕ) (b : Bool) :
    childPrefix (a :: p) b =
      if parity a = b then a / 2 :: childPrefix p b else childPrefix p b := by
  by_cases h : parity a = b <;> simp [childPrefix, h]

theorem nodup_of_childPrefixes {p : List ℕ}
    (h0 : (childPrefix p false).Nodup) (h1 : (childPrefix p true).Nodup) :
    p.Nodup := by
  have hall : ∀ b, (childPrefix p b).Nodup := by
    intro b; cases b <;> assumption
  clear h0 h1
  induction p with
  | nil => simp
  | cons a p ih =>
    have htail : ∀ b, (childPrefix p b).Nodup := by
      intro b
      have h := hall b
      rw [childPrefix_cons_eq] at h
      split_ifs at h with heq
      · exact (List.nodup_cons.mp h).2
      · exact h
    apply List.nodup_cons.mpr
    refine ⟨?_, ih htail⟩
    intro ha
    have h := hall (parity a)
    rw [childPrefix_cons_eq] at h
    simp only [ite_true] at h
    apply (List.nodup_cons.mp h).1
    apply (mem_childPrefix p (parity a) (a / 2)).mpr
    simpa using ha

def assembleChildren (p rA rB : List ℕ) (a : Bool) : List ℕ :=
  p ++ rA.map (liftValue a) ++ rB.map (liftValue (!a))

@[simp] theorem childPrefix_assemble_preferred (p rA rB : List ℕ) (a : Bool) :
    childPrefix (assembleChildren p rA rB a) a = childPrefix p a ++ rA := by
  cases a <;> simp [assembleChildren, childPrefix_map_lift_other]

@[simp] theorem childPrefix_assemble_other (p rA rB : List ℕ) (a : Bool) :
    childPrefix (assembleChildren p rA rB a) (!a) = childPrefix p (!a) ++ rB := by
  cases a <;> simp [assembleChildren, childPrefix_map_lift_other]

theorem assembleChildren_nodup (p rA rB : List ℕ) (a : Bool)
    (hA : (childPrefix p a ++ rA).Nodup)
    (hB : (childPrefix p (!a) ++ rB).Nodup) :
    (assembleChildren p rA rB a).Nodup := by
  apply nodup_of_childPrefixes
  · cases a
    · simpa using hA
    · simpa [assembleChildren, childPrefix_map_lift_other] using hB
  · cases a
    · simpa [assembleChildren, childPrefix_map_lift_other] using hB
    · simpa using hA

theorem assembleChildren_prefix (p rA rB : List ℕ) (a : Bool) :
    p.IsPrefix (assembleChildren p rA rB a) := by
  exact ⟨rA.map (liftValue a) ++ rB.map (liftValue (!a)), by
    simp [assembleChildren, List.append_assoc]⟩

theorem assembleChildren_coverage (p rA rB : List ℕ) (a : Bool) (n : ℕ)
    (hA : ∀ x, liftValue a x ≤ n → x ∈ childPrefix p a ++ rA)
    (hB : ∀ x, liftValue (!a) x ≤ n → x ∈ childPrefix p (!a) ++ rB) :
    ∀ x, x ≤ n → x ∈ assembleChildren p rA rB a := by
  intro x hx
  by_cases hp : parity x = a
  · have hrec : liftValue a (x / 2) = x := by
      simpa [hp] using liftValue_parity_div x
    have hm : x / 2 ∈ childPrefix (assembleChildren p rA rB a) a := by
      rw [childPrefix_assemble_preferred]
      exact hA _ (by simpa [hrec] using hx)
    simpa [hrec] using (mem_childPrefix _ a (x / 2)).mp hm
  · have hp' : parity x = !a := by
      cases h : parity x <;> cases a <;> simp_all
    have hrec : liftValue (!a) (x / 2) = x := by
      simpa [hp'] using liftValue_parity_div x
    have hm : x / 2 ∈ childPrefix (assembleChildren p rA rB a) (!a) := by
      rw [childPrefix_assemble_other]
      exact hB _ (by simpa [hrec] using hx)
    simpa [hrec] using (mem_childPrefix _ (!a) (x / 2)).mp hm

end Erdos196
