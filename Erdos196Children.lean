import Erdos196Tree

namespace Erdos196

private theorem lift_recover {a : ℕ} {b : Bool} (h : parity a = b) :
    liftValue b (a / 2) = a := by
  simpa [h] using liftValue_parity_div a

private theorem before_cons (p : List ℕ) (R : ℕ → ℕ → Prop) (a x y : ℕ) :
    Before (a :: p) R x y ↔
      if x = a then y ≠ a else if y = a then False else Before p R x y := by
  by_cases hx : x = a
  · subst x
    by_cases hy : y = a
    · subst y
      simp [Before]
    · by_cases hyp : y ∈ p <;>
        simp [Before, hy, Ne.symm hy, hyp]
  · by_cases hy : y = a
    · subst y
      by_cases hxp : x ∈ p <;>
        simp [Before, hx, Ne.symm hx, hxp]
    · by_cases hxp : x ∈ p <;> by_cases hyp : y ∈ p <;>
        simp [Before, hx, Ne.symm hx, hy, Ne.symm hy, hxp, hyp]

/-- Parity filtering and division preserve every prefix/tail comparison. -/
theorem before_childPrefix_of_lift (p : List ℕ) (b : Bool)
    (R R' : ℕ → ℕ → Prop)
    (hR : ∀ x y, R' x y ↔ R (liftValue b x) (liftValue b y)) (x y : ℕ) :
    Before (childPrefix p b) R' x y ↔
      Before p R (liftValue b x) (liftValue b y) := by
  induction p with
  | nil => simpa [childPrefix, Before] using hR x y
  | cons a p ih =>
    by_cases ha : parity a = b
    · have heq : liftValue b (a / 2) = a := lift_recover ha
      have hx : x = a / 2 ↔ liftValue b x = a := by
        constructor
        · intro h; simpa [h] using heq
        · intro h; exact liftValue_injective b (h.trans heq.symm)
      have hy : y = a / 2 ↔ liftValue b y = a := by
        constructor
        · intro h; simpa [h] using heq
        · intro h; exact liftValue_injective b (h.trans heq.symm)
      have hchild : childPrefix (a :: p) b = a / 2 :: childPrefix p b := by
        simp [childPrefix, ha]
      rw [hchild, before_cons, before_cons]
      by_cases hxa : x = a / 2 <;> by_cases hya : y = a / 2 <;>
        simp_all
    · have hx : liftValue b x ≠ a := by
        intro h
        have := congrArg parity h
        rw [parity_liftValue] at this
        exact ha this.symm
      have hy : liftValue b y ≠ a := by
        intro h
        have := congrArg parity h
        rw [parity_liftValue] at this
        exact ha this.symm
      have hchild : childPrefix (a :: p) b = childPrefix p b := by
        simp [childPrefix, ha]
      rw [hchild, before_cons]
      simpa [hx, hy] using ih

theorem childPrefix_nodup {p : List ℕ} (hp : p.Nodup) (b : Bool) :
    (childPrefix p b).Nodup := by
  unfold childPrefix
  apply List.Nodup.map_on _ (hp.filter _)
  intro x hx y hy hxy
  have hxp : parity x = b := by simpa using (List.mem_filter.mp hx).2
  have hyp : parity y = b := by simpa using (List.mem_filter.mp hy).2
  calc
    x = liftValue b (x / 2) := (lift_recover hxp).symm
    _ = liftValue b (y / 2) := congrArg (liftValue b) hxy
    _ = y := lift_recover hyp

theorem childPrefix_length_le (p : List ℕ) (b : Bool) :
    (childPrefix p b).length ≤ p.length := by
  simpa only [childPrefix, List.length_map] using
    List.length_filter_le (fun x => parity x == b) p

theorem before_childPrefix (p : List ℕ) (t : Tree) (b : Bool) (x y : ℕ) :
    Before (childPrefix p b) (fun x y => treeBefore (childTree t b) x y = true) x y ↔
      Before p (fun x y => treeBefore t x y = true) (liftValue b x) (liftValue b y) := by
  apply before_childPrefix_of_lift
  intro x y
  simp

theorem admissible_childPrefix {p : List ℕ} (hp : Admissible p) (b : Bool) :
    Admissible (childPrefix p b) := by
  obtain ⟨hn, t, ht⟩ := hp
  refine ⟨childPrefix_nodup hn b, childTree t b, ?_⟩
  intro a c d e hap hab
  exact ht _ _ _ _ (ap4_liftValue b hap)
    ⟨(before_childPrefix p t b a c).mp hab.1,
      (before_childPrefix p t b c d).mp hab.2.1,
      (before_childPrefix p t b d e).mp hab.2.2⟩

@[simp] theorem mem_childPrefix (p : List ℕ) (b : Bool) (x : ℕ) :
    x ∈ childPrefix p b ↔ liftValue b x ∈ p := by
  constructor
  · intro hx
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
    obtain ⟨ha, hb⟩ := List.mem_filter.mp ha
    have hb' : parity a = b := by simpa using hb
    simpa [lift_recover hb'] using ha
  · intro hx
    apply List.mem_map.mpr
    refine ⟨liftValue b x, ?_, div_liftValue b x⟩
    exact List.mem_filter.mpr ⟨hx, by simp⟩

@[simp] theorem childPrefix_append (p q : List ℕ) (b : Bool) :
    childPrefix (p ++ q) b = childPrefix p b ++ childPrefix q b := by
  simp [childPrefix, List.filter_append]

@[simp] theorem childPrefix_map_lift_same (p : List ℕ) (b : Bool) :
    childPrefix (p.map (liftValue b)) b = p := by
  induction p with
  | nil => simp [childPrefix]
  | cons a p ih => simpa [childPrefix] using congrArg (List.cons a) ih

theorem childPrefix_map_lift_other (p : List ℕ) (a b : Bool) (h : a ≠ b) :
    childPrefix (p.map (liftValue a)) b = [] := by
  induction p with
  | nil => simp [childPrefix]
  | cons x p ih => simp [childPrefix, h]

theorem childPrefix_max_le (p : List ℕ) (b : Bool) :
    (childPrefix p b).foldr max 0 ≤ (p.foldr max 0) / 2 := by
  apply List.max_le_of_forall_le
  intro x hx
  have hm : liftValue b x ≤ p.foldr max 0 :=
    List.le_max_of_le ((mem_childPrefix p b x).mp hx) le_rfl
  have hd := Nat.div_le_div_right (c := 2) hm
  simpa using hd

theorem max_pos_of_nodup_length {p : List ℕ} (hp : p.Nodup)
    (hlen : 2 ≤ p.length) : 0 < p.foldr max 0 := by
  cases p with
  | nil => simp at hlen
  | cons a p =>
    cases p with
    | nil => simp at hlen
    | cons b p =>
      have hab : a ≠ b := by
        intro h
        exact (List.nodup_cons.mp hp).1 (by simp [h])
      have ha : a ≤ (a :: b :: p).foldr max 0 :=
        List.le_max_of_le (by simp) le_rfl
      have hb : b ≤ (a :: b :: p).foldr max 0 :=
        List.le_max_of_le (by simp) le_rfl
      omega

theorem childPrefix_max_lt {p : List ℕ} (hp : p.Nodup)
    (hlen : 2 ≤ p.length) (b : Bool) :
    (childPrefix p b).foldr max 0 < p.foldr max 0 := by
  have hpos := max_pos_of_nodup_length hp hlen
  have hle := childPrefix_max_le p b
  omega

/-- Both coordinates weakly decrease and the maximum strictly decreases. -/
theorem childPrefix_measure_decreases {p : List ℕ} (hp : p.Nodup)
    (hlen : 2 ≤ p.length) (b : Bool) :
    (childPrefix p b).length < p.length ∨
      ((childPrefix p b).length = p.length ∧
        (childPrefix p b).foldr max 0 < p.foldr max 0) := by
  have hl := childPrefix_length_le p b
  have hm := childPrefix_max_lt hp hlen b
  omega

end Erdos196
