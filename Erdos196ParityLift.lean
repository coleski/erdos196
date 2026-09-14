import Erdos196Children

/-!
The arithmetic core of the adaptive parity lift.

Stages are chronological blocks:
0 = old prefix; 1 = new preferred parity; 2 = new other parity;
3 = preferred-parity tail; 4 = other-parity tail.

This file deliberately does not define the shared admissibility predicate.
The caller must obtain the old-stage exclusions from old admissibility.
-/

namespace Erdos196

def PreferredStage (s : ℕ) : Prop := s = 0 ∨ s = 1 ∨ s = 3

def OtherStage (s : ℕ) : Prop := s = 0 ∨ s = 2 ∨ s = 4

/-- Alternating parity and chronological block order force a small finite
other-parity term immediately before a preferred tail term. The AP equations
then contradict nonnegativity. Both numerical AP directions are covered. -/
theorem parity_lift_stage_contradiction
    {a b c d H sa sb sc sd : ℕ}
    (hap₁ : a + c = 2 * b) (hap₂ : b + d = 2 * c)
    (hab : sa ≤ sb) (hbc : sb ≤ sc) (hcd : sc ≤ sd)
    (hc_old : sc ≠ 0)
    (hpattern :
      (PreferredStage sa ∧ OtherStage sb ∧ PreferredStage sc ∧
        OtherStage sd ∧ sb ≠ 0) ∨
      (OtherStage sa ∧ PreferredStage sb ∧ OtherStage sc ∧
        PreferredStage sd))
    (hb_small : sb = 2 → b ≤ H)
    (hc_small : sc = 2 → c ≤ H)
    (hc_large : sc = 3 → 2 * H < c)
    (hd_large : sd = 3 → 2 * H < d) : False := by
  rcases hpattern with ⟨ha, hb, hc, hd, hb_old⟩ | ⟨ha, hb, hc, hd⟩
  · have hb_two : sb = 2 := by
      simp only [PreferredStage, OtherStage] at *
      omega
    have hc_three : sc = 3 := by
      simp only [PreferredStage] at hc
      omega
    have := hb_small hb_two
    have := hc_large hc_three
    omega
  · have hc_two : sc = 2 := by
      simp only [PreferredStage, OtherStage] at *
      omega
    have hd_three : sd = 3 := by
      simp only [PreferredStage] at hd
      omega
    have := hc_small hc_two
    have := hd_large hd_three
    omega

/-- Relation-level form of the entire odd-parity lifting argument. The stage
and transfer assumptions are the concrete facts supplied by list assembly. -/
theorem parity_lift_relation_contradiction
    {old next : ℕ → ℕ → Prop} {stage : ℕ → ℕ} {preferred H : ℕ}
    (hp : preferred < 2)
    (hold : ∀ a b c d, AP4 a b c d →
      ¬ (old a b ∧ old b c ∧ old c d))
    (hstage : ∀ x, if x % 2 = preferred then PreferredStage (stage x)
      else OtherStage (stage x))
    (hmono : ∀ x y, next x y → stage x ≤ stage y)
    (htransfer : ∀ x y, next x y → stage x = 0 → old x y)
    (hroot : ∀ x y, stage x ≠ 0 → stage y ≠ 0 →
      x % 2 = preferred → y % 2 ≠ preferred → old x y)
    (hsmall : ∀ x, stage x = 2 → x ≤ H)
    (hlarge : ∀ x, stage x = 3 → 2 * H < x)
    {a b c d : ℕ} (hap : AP4 a b c d) (hodd : a % 2 ≠ b % 2)
    (hab : next a b) (hbc : next b c) (hcd : next c d) : False := by
  have h₁ := hap.1
  have h₂ := hap.2.1
  have hac : a % 2 = c % 2 := by omega
  have hbd : b % 2 = d % 2 := by omega
  have hsab := hmono a b hab
  have hsbc := hmono b c hbc
  have hscd := hmono c d hcd
  have hc_old : stage c ≠ 0 := by
    intro hc
    have ha : stage a = 0 := by omega
    have hb : stage b = 0 := by omega
    exact hold a b c d hap
      ⟨htransfer a b hab ha, htransfer b c hbc hb, htransfer c d hcd hc⟩
  have hd_old : stage d ≠ 0 := by omega
  by_cases ha_pref : a % 2 = preferred
  · have hb_other : b % 2 ≠ preferred := by omega
    have hc_pref : c % 2 = preferred := by omega
    have hd_other : d % 2 ≠ preferred := by omega
    have hb_old : stage b ≠ 0 := by
      intro hb
      have ha : stage a = 0 := by omega
      exact hold a b c d hap
        ⟨htransfer a b hab ha, htransfer b c hbc hb,
          hroot c d hc_old hd_old hc_pref hd_other⟩
    have haS := hstage a
    have hbS := hstage b
    have hcS := hstage c
    have hdS := hstage d
    simp only [ha_pref, hb_other, hc_pref, hd_other, ite_true, ite_false] at haS hbS hcS hdS
    exact parity_lift_stage_contradiction h₁ h₂ hsab hsbc hscd hc_old
      (Or.inl ⟨haS, hbS, hcS, hdS, hb_old⟩)
      (hsmall b) (hsmall c) (hlarge c) (hlarge d)
  · have hb_pref : b % 2 = preferred := by omega
    have hc_other : c % 2 ≠ preferred := by omega
    have hd_pref : d % 2 = preferred := by omega
    have haS := hstage a
    have hbS := hstage b
    have hcS := hstage c
    have hdS := hstage d
    simp only [ha_pref, hb_pref, hc_other, hd_pref, ite_true, ite_false] at haS hbS hcS hdS
    exact parity_lift_stage_contradiction h₁ h₂ hsab hsbc hscd hc_old
      (Or.inr ⟨haS, hbS, hcS, hdS⟩)
      (hsmall b) (hsmall c) (hlarge c) (hlarge d)

/-- Chronological stage of an entry in a three-block prefix and parity tail. -/
def mergeStage (p A B : List ℕ) (preferred : Bool) (x : ℕ) : ℕ :=
  let q := p ++ A ++ B
  if q.idxOf x < p.length then 0
  else if q.idxOf x < p.length + A.length then 1
  else if q.idxOf x < q.length then 2
  else if parity x = preferred then 3 else 4

theorem before_append_old_transfer {p s : List ℕ} {R S : ℕ → ℕ → Prop}
    {x y : ℕ} (h : Before (p ++ s) R x y) (hx : x ∈ p) : Before p S x y := by
  by_cases hy : y ∈ p
  · have hxq : x ∈ p ++ s := List.mem_append_left s hx
    have hyq : y ∈ p ++ s := List.mem_append_left s hy
    have hh : (p ++ s).idxOf x < (p ++ s).idxOf y := by
      simpa only [Before, hxq, hyq, ite_true, not_true_eq_false, false_or] using h
    simpa only [Before, hx, hy, ite_true, not_true_eq_false, false_or,
      List.idxOf_append_of_mem hx, List.idxOf_append_of_mem hy] using hh
  · simp only [Before, hx, hy, ite_true, not_false_eq_true, true_or]

theorem before_iff_idx {q : List ℕ} {R : ℕ → ℕ → Prop} {x y : ℕ} :
    Before q R x y ↔
      (if x ∈ q then q.idxOf x < q.idxOf y else y ∉ q ∧ R x y) := by
  by_cases hx : x ∈ q
  · by_cases hy : y ∈ q
    · simp [Before, hx, hy]
    · have hix : q.idxOf x < q.length := List.idxOf_lt_length_of_mem hx
      have hiy : q.idxOf y = q.length := List.idxOf_eq_length_iff.mpr hy
      simp [Before, hx, hy, hix]
  · simp [Before, hx]

theorem mergeStage_eq_zero_iff (p A B : List ℕ) (preferred : Bool) (x : ℕ) :
    mergeStage p A B preferred x = 0 ↔ x ∈ p := by
  have hp : p <+: p ++ A ++ B := ⟨A ++ B, by simp [List.append_assoc]⟩
  have hx := hp.mem_iff_idxOf_lt_length x
  rw [hx]
  unfold mergeStage
  dsimp only
  split_ifs <;> simp_all

theorem mergeStage_mem (p A B : List ℕ) (preferred : Bool) (x : ℕ) :
    mergeStage p A B preferred x =
      if x ∈ p then 0 else if x ∈ p ++ A then 1
      else if x ∈ p ++ A ++ B then 2
      else if parity x = preferred then 3 else 4 := by
  have hp : p <+: p ++ A ++ B := ⟨A ++ B, by simp [List.append_assoc]⟩
  have hpa : p ++ A <+: p ++ A ++ B := ⟨B, by simp [List.append_assoc]⟩
  have hx := hp.mem_iff_idxOf_lt_length x
  have hxa : x ∈ p ++ A ↔ (p ++ A ++ B).idxOf x < p.length + A.length := by
    simpa only [List.length_append] using hpa.mem_iff_idxOf_lt_length x
  have hxq : x ∈ p ++ A ++ B ↔
      (p ++ A ++ B).idxOf x < (p ++ A ++ B).length := List.idxOf_lt_length_iff.symm
  simp only [mergeStage, ← hx, ← hxa, ← hxq]

theorem mergeStage_parity (p A B : List ℕ) (preferred : Bool)
    (hA : ∀ x ∈ A, parity x = preferred)
    (hB : ∀ x ∈ B, parity x ≠ preferred) (x : ℕ) :
    if parity x = preferred then PreferredStage (mergeStage p A B preferred x)
    else OtherStage (mergeStage p A B preferred x) := by
  rw [mergeStage_mem]
  by_cases hx : x ∈ p
  · simp [hx, PreferredStage, OtherStage]
  by_cases hxa : x ∈ A
  · have hp := hA x hxa
    simp [hx, hxa, hp, PreferredStage]
  by_cases hxb : x ∈ B
  · have hp := hB x hxb
    simp [hx, hxa, hxb, hp, OtherStage]
  by_cases hp : parity x = preferred <;>
    simp [hx, hxa, hxb, hp, PreferredStage, OtherStage]

theorem mergeStage_eq_three (p A B : List ℕ) (preferred : Bool) (x : ℕ) :
    mergeStage p A B preferred x = 3 ↔
      x ∉ p ++ A ++ B ∧ parity x = preferred := by
  rw [mergeStage_mem]
  simp only [List.mem_append]
  split_ifs <;> simp_all

theorem mergeStage_eq_two_mem (p A B : List ℕ) (preferred : Bool) (x : ℕ)
    (h : mergeStage p A B preferred x = 2) : x ∈ B := by
  rw [mergeStage_mem] at h
  simp only [List.mem_append] at h
  split_ifs at h <;> simp_all

theorem mergeStage_mono (p A B : List ℕ) (preferred : Bool)
    (R : ℕ → ℕ → Prop)
    (hR : ∀ x y, R x y → parity x ≠ preferred → parity y = preferred → False)
    {x y : ℕ} (h : Before (p ++ A ++ B) R x y) :
    mergeStage p A B preferred x ≤ mergeStage p A B preferred y := by
  rw [before_iff_idx] at h
  by_cases hx : x ∈ p ++ A ++ B <;> by_cases hy : y ∈ p ++ A ++ B
  · simp only [hx, ite_true] at h
    have hix := List.idxOf_lt_length_of_mem hx
    have hiy := List.idxOf_lt_length_of_mem hy
    unfold mergeStage
    dsimp only
    simp only [List.length_append] at *
    split_ifs <;> omega
  · simp only [hx, ite_true] at h
    have hix := List.idxOf_lt_length_of_mem hx
    have hiy : (p ++ A ++ B).idxOf y = (p ++ A ++ B).length :=
      List.idxOf_eq_length_iff.mpr hy
    unfold mergeStage
    dsimp only
    simp only [List.length_append] at *
    split_ifs <;> omega
  · simp only [hx, hy, ite_false, not_true_eq_false, false_and] at h
  · simp only [hx, hy, ite_false, not_false_eq_true, true_and] at h
    have hix : (p ++ A ++ B).idxOf x = (p ++ A ++ B).length :=
      List.idxOf_eq_length_iff.mpr hx
    have hiy : (p ++ A ++ B).idxOf y = (p ++ A ++ B).length :=
      List.idxOf_eq_length_iff.mpr hy
    by_cases hpx : parity x = preferred <;> by_cases hpy : parity y = preferred
    all_goals try exact False.elim (hR x y h (by assumption) (by assumption))
    all_goals
      rw [mergeStage_mem, mergeStage_mem]
      simp_all

theorem parity_eq_toNat (x : ℕ) (b : Bool) :
    parity x = b ↔ x % 2 = b.toNat := by
  cases b <;> simp [parity]

theorem noAP4_sameParity_of_children
    {q : List ℕ} {t : Tree}
    (hchildren : ∀ e : Bool, NoAP4Rel
      (Before (childPrefix q e) (fun x y => treeBefore (childTree t e) x y = true)))
    {a b c d : ℕ} (hap : AP4 a b c d) (heven : a % 2 = b % 2)
    (hab : Before q (fun x y => treeBefore t x y = true) a b)
    (hbc : Before q (fun x y => treeBefore t x y = true) b c)
    (hcd : Before q (fun x y => treeBefore t x y = true) c d) : False := by
  have h₁ := hap.1
  have h₂ := hap.2.1
  have habP : parity a = parity b := (parity_eq_iff_mod_eq a b).mpr heven
  have hacP : parity a = parity c := (parity_eq_iff_mod_eq a c).mpr (by omega)
  have hadP : parity a = parity d := (parity_eq_iff_mod_eq a d).mpr (by omega)
  have ha : liftValue (parity a) (a / 2) = a := liftValue_parity_div a
  have hb : liftValue (parity a) (b / 2) = b := by rw [habP]; simp
  have hc : liftValue (parity a) (c / 2) = c := by rw [hacP]; simp
  have hd : liftValue (parity a) (d / 2) = d := by rw [hadP]; simp
  have hquot : AP4 (a / 2) (b / 2) (c / 2) (d / 2) := by
    unfold AP4 at *
    omega
  apply hchildren (parity a) _ _ _ _ hquot
  refine ⟨?_, ?_, ?_⟩
  · apply (before_childPrefix q t (parity a) (a / 2) (b / 2)).mpr
    simpa only [ha, hb] using hab
  · apply (before_childPrefix q t (parity a) (b / 2) (c / 2)).mpr
    simpa only [hb, hc] using hbc
  · apply (before_childPrefix q t (parity a) (c / 2) (d / 2)).mpr
    simpa only [hc, hd] using hcd

/-- The complete central merge. The two projected lists are the recursively
completed children; new preferred values are appended before new other values. -/
theorem admissible_parity_merge
    (p A B : List ℕ) (oldTree : Tree) (H : ℕ)
    (hq : (p ++ A ++ B).Nodup)
    (hold : NoAP4Rel (Before p (fun x y => treeBefore oldTree x y = true)))
    (hA : ∀ x ∈ A, parity x = oldTree [])
    (hB : ∀ x ∈ B, parity x ≠ oldTree [])
    (hsmall : ∀ x ∈ B, x ≤ H)
    (hcover : ∀ x, parity x = oldTree [] → x ≤ 2 * H → x ∈ p ++ A ++ B)
    (h0 : Admissible (childPrefix (p ++ A ++ B) false))
    (h1 : Admissible (childPrefix (p ++ A ++ B) true)) :
    Admissible (p ++ A ++ B) := by
  obtain ⟨_, t0, ht0⟩ := h0
  obtain ⟨_, t1, ht1⟩ := h1
  let t := splitTree (oldTree []) t0 t1
  refine ⟨hq, t, ?_⟩
  intro a b c d hap hchain
  obtain ⟨hab, hbc, hcd⟩ := hchain
  by_cases heven : a % 2 = b % 2
  · apply noAP4_sameParity_of_children (q := p ++ A ++ B) (t := t) _ hap heven hab hbc hcd
    intro e
    cases e
    · simpa only [t, childTree_splitTree_false] using ht0
    · simpa only [t, childTree_splitTree_true] using ht1
  · let st := mergeStage p A B (oldTree [])
    apply parity_lift_relation_contradiction
      (old := Before p (fun x y => treeBefore oldTree x y = true))
      (next := Before (p ++ A ++ B) (fun x y => treeBefore t x y = true))
      (stage := st) (preferred := (oldTree []).toNat) (H := H)
      (by cases oldTree [] <;> decide) hold _ _ _ _ _ _ hap heven hab hbc hcd
    · intro x
      simpa only [← parity_eq_toNat] using mergeStage_parity p A B (oldTree []) hA hB x
    · intro x y hxy
      apply mergeStage_mono p A B (oldTree []) (fun x y => treeBefore t x y = true) _ hxy
      intro u v huv hu hv
      have hp : parity u ≠ parity v := by simpa only [hv] using hu
      rw [treeBefore_different_parity t u v hp] at huv
      have hrt : t [] = oldTree [] := rfl
      rw [hrt] at huv
      exact hu (by simpa using huv)
    · intro x y hxy hx
      have hxp : x ∈ p := (mergeStage_eq_zero_iff p A B (oldTree []) x).mp hx
      apply before_append_old_transfer (p := p) (s := A ++ B) (R := fun x y => treeBefore t x y = true)
        (S := fun x y => treeBefore oldTree x y = true) ?_ hxp
      simpa only [List.append_assoc] using hxy
    · intro x y hx hy hpx hpy
      have hxn : x ∉ p := by
        intro hmem
        exact hx ((mergeStage_eq_zero_iff p A B (oldTree []) x).mpr hmem)
      have hyn : y ∉ p := by
        intro hmem
        exact hy ((mergeStage_eq_zero_iff p A B (oldTree []) y).mpr hmem)
      have hxp : parity x = oldTree [] := (parity_eq_toNat x _).mpr hpx
      have hyp : parity y ≠ oldTree [] := by
        intro he
        exact hpy ((parity_eq_toNat y _).mp he)
      have hpar : parity x ≠ parity y := by intro he; exact hyp (he.symm.trans hxp)
      simp only [Before, hxn, hyn, ite_false, not_false_eq_true, true_and]
      rw [treeBefore_different_parity oldTree x y hpar]
      simp [hxp]
    · intro x hx
      exact hsmall x (mergeStage_eq_two_mem p A B (oldTree []) x hx)
    · intro x hx
      obtain ⟨hnot, hpar⟩ := (mergeStage_eq_three p A B (oldTree []) x).mp hx
      by_contra hle
      exact hnot (hcover x hpar (by omega))

end Erdos196
