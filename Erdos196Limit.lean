import Erdos196Core

namespace Erdos196

private theorem getD_eq_of_prefix {p q : List ℕ} (h : p.IsPrefix q)
    {i : ℕ} (hi : i < p.length) : p.getD i 0 = q.getD i 0 := by
  calc
    p.getD i 0 = p[i] := (List.getElem_eq_getD (h := hi) 0).symm
    _ = q[i]'(hi.trans_le h.length_le) := h.getElem hi
    _ = q.getD i 0 := List.getElem_eq_getD 0

/-- A nested, fair chain of finite avoiding lists has a bijective avoiding limit. -/
theorem permutation_of_fair_chain (p : ℕ → List ℕ)
    (hprefix : ∀ n, (p n).IsPrefix (p (n + 1)))
    (hnodup : ∀ n, (p n).Nodup)
    (havoid : ∀ n, NoAP4List (p n))
    (hcover : ∀ n x, x ≤ n → x ∈ p (n + 1)) :
    ∃ f : ℕ ≃ ℕ, NoAP4Sequence f := by
  classical
  have mono : ∀ b a, a ≤ b → (p a).IsPrefix (p b) := by
    intro b
    induction b with
    | zero =>
      intro a ha
      have : a = 0 := by omega
      subst a
      exact List.prefix_refl _
    | succ b ih =>
      intro a ha
      by_cases hab : a ≤ b
      · exact (ih a hab).trans (hprefix b)
      · have : a = b + 1 := by omega
        subst a
        exact List.prefix_refl _
  have hlen (n : ℕ) : n + 1 ≤ (p (n + 1)).length := by
    have hs : Finset.range (n + 1) ⊆ (p (n + 1)).toFinset := by
      intro x hx
      apply List.mem_toFinset.mpr
      apply hcover n x
      simpa only [Finset.mem_range, Nat.lt_succ_iff] using hx
    have hc := Finset.card_le_card hs
    rw [Finset.card_range] at hc
    exact hc.trans (List.toFinset_card_le _)
  have agree (n m i : ℕ) (hi : i < (p n).length)
      (hj : i < (p m).length) : (p n).getD i 0 = (p m).getD i 0 := by
    exact (getD_eq_of_prefix (mono (max n m) n (Nat.le_max_left _ _)) hi).trans
      (getD_eq_of_prefix (mono (max n m) m (Nat.le_max_right _ _)) hj).symm
  let f : ℕ → ℕ := fun i => (p (i + 1)).getD i 0
  have stable (n i : ℕ) (hi : i < (p n).length) : f i = (p n).getD i 0 := by
    exact agree (i + 1) n i (by have := hlen i; omega) hi
  have hinj : Function.Injective f := by
    intro i j hij
    have hi : i < (p (i + j + 1)).length := by have := hlen (i + j); omega
    have hj : j < (p (i + j + 1)).length := by have := hlen (i + j); omega
    have heq : (p (i + j + 1)).getD i 0 = (p (i + j + 1)).getD j 0 := by
      rw [← stable (i + j + 1) i hi, ← stable (i + j + 1) j hj]
      exact hij
    apply (List.Nodup.getElem_inj_iff (hnodup (i + j + 1))).mp
    calc
      (p (i + j + 1))[i] = (p (i + j + 1)).getD i 0 := List.getElem_eq_getD 0
      _ = (p (i + j + 1)).getD j 0 := heq
      _ = (p (i + j + 1))[j] := (List.getElem_eq_getD 0).symm
  have hsurj : Function.Surjective f := by
    intro x
    obtain ⟨i, hi, hix⟩ := List.getElem_of_mem (hcover x x (Nat.le_refl x))
    refine ⟨i, ?_⟩
    rw [stable (x + 1) i hi]
    exact (List.getElem_eq_getD (h := hi) 0).symm.trans hix
  have hf : NoAP4Sequence f := by
    intro i j k l hij hjk hkl
    have hl : l < (p (l + 1)).length := by have := hlen l; omega
    have hi : i < (p (l + 1)).length := by omega
    have hj : j < (p (l + 1)).length := by omega
    have hk : k < (p (l + 1)).length := by omega
    rw [stable (l + 1) i hi, stable (l + 1) j hj,
      stable (l + 1) k hk, stable (l + 1) l hl]
    exact havoid (l + 1) i j k l hij hjk hkl hl
  exact ⟨Equiv.ofBijective f ⟨hinj, hsurj⟩, hf⟩

/-- The generic fair-extension principle needed by the finite adaptive lift. -/
theorem permutation_of_good_extensions (Good : List ℕ → Prop)
    (hempty : Good [])
    (hnodup : ∀ p, Good p → p.Nodup)
    (havoid : ∀ p, Good p → NoAP4List p)
    (hext : ∀ p, Good p → ∀ n : ℕ,
      ∃ q, Good q ∧ p.IsPrefix q ∧ ∀ x, x ≤ n → x ∈ q) :
    ∃ f : ℕ ≃ ℕ, NoAP4Sequence f := by
  classical
  let step (n : ℕ) (p : {p : List ℕ // Good p}) : {p : List ℕ // Good p} :=
    ⟨Classical.choose (hext p.val p.property n),
      (Classical.choose_spec (hext p.val p.property n)).1⟩
  let states : ℕ → {p : List ℕ // Good p} :=
    Nat.rec ⟨[], hempty⟩ step
  let p : ℕ → List ℕ := fun n => (states n).val
  have hp (n : ℕ) : Good (p n) := (states n).property
  have hprefix (n : ℕ) : (p n).IsPrefix (p (n + 1)) := by
    exact (Classical.choose_spec (hext (states n).val (states n).property n)).2.1
  have hcover (n x : ℕ) (hx : x ≤ n) : x ∈ p (n + 1) := by
    exact (Classical.choose_spec (hext (states n).val (states n).property n)).2.2 x hx
  exact permutation_of_fair_chain p hprefix
    (fun n => hnodup (p n) (hp n)) (fun n => havoid (p n) (hp n)) hcover

end Erdos196
