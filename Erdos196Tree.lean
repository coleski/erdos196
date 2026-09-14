import Erdos196Core

namespace Erdos196

@[simp] theorem parity_liftValue (b : Bool) (x : ℕ) : parity (liftValue b x) = b := by
  cases b <;> simp [parity, liftValue]

@[simp] theorem div_liftValue (b : Bool) (x : ℕ) : liftValue b x / 2 = x := by
  cases b <;> simp only [liftValue, Bool.false_eq_true, ↓reduceIte] <;> omega

@[simp] theorem liftValue_parity_div (x : ℕ) : liftValue (parity x) (x / 2) = x := by
  cases h : parity x with
  | false =>
    have hx : x % 2 ≠ 1 := by simpa [parity] using h
    simp only [liftValue, Bool.false_eq_true, ↓reduceIte]
    omega
  | true =>
    have hx : x % 2 = 1 := by simpa [parity] using h
    simp only [liftValue, ↓reduceIte]
    omega

theorem liftValue_injective (b : Bool) : Function.Injective (liftValue b) := by
  intro x y h
  have := congrArg (fun n => n / 2) h
  simpa using this

@[simp] theorem treeBefore_self (t : Tree) (x : ℕ) : treeBefore t x x = false := by
  rw [treeBefore]
  simp

theorem treeBefore_same_parity (t : Tree) (x y : ℕ) (h : parity x = parity y) :
    treeBefore t x y = treeBefore (childTree t (parity x)) (x / 2) (y / 2) := by
  by_cases hxy : x = y
  · subst y
    simp
  · rw [treeBefore]
    simp [hxy, h]

theorem treeBefore_different_parity (t : Tree) (x y : ℕ)
    (h : parity x ≠ parity y) : treeBefore t x y = (parity x == t []) := by
  have hxy : x ≠ y := by intro hxy; subst y; exact h rfl
  rw [treeBefore]
  simp [hxy, h]

@[simp] theorem treeBefore_liftValue (t : Tree) (b : Bool) (x y : ℕ) :
    treeBefore t (liftValue b x) (liftValue b y) = treeBefore (childTree t b) x y := by
  rw [treeBefore_same_parity t _ _ (by simp)]
  simp

@[simp] theorem childTree_splitTree_false (b : Bool) (t0 t1 : Tree) :
    childTree (splitTree b t0 t1) false = t0 := by
  funext path
  simp [childTree, splitTree]

@[simp] theorem childTree_splitTree_true (b : Bool) (t0 t1 : Tree) :
    childTree (splitTree b t0 t1) true = t1 := by
  funext path
  simp [childTree, splitTree]

theorem ap4_liftValue (p : Bool) {a b c d : ℕ} (h : AP4 a b c d) :
    AP4 (liftValue p a) (liftValue p b) (liftValue p c) (liftValue p d) := by
  unfold AP4 liftValue at *
  split <;> omega

theorem parity_eq_iff_mod_eq (x y : ℕ) : parity x = parity y ↔ x % 2 = y % 2 := by
  by_cases hx : x % 2 = 1 <;> by_cases hy : y % 2 = 1 <;>
    simp [parity, hx, hy] <;> omega

def flipTree (t : Tree) : Tree := fun path => !(t path)

theorem treeBefore_flip (t : Tree) (x y : ℕ) (hxy : x ≠ y) :
    treeBefore (flipTree t) x y = !(treeBefore t x y) := by
  by_cases hpar : parity x = parity y
  · have hmod : x % 2 = y % 2 := (parity_eq_iff_mod_eq x y).mp hpar
    have hdiv : x / 2 ≠ y / 2 := by omega
    rw [treeBefore_same_parity _ _ _ hpar, treeBefore_same_parity _ _ _ hpar]
    change treeBefore (flipTree (childTree t (parity x))) (x / 2) (y / 2) = _
    exact treeBefore_flip _ _ _ hdiv
  · rw [treeBefore_different_parity _ _ _ hpar, treeBefore_different_parity _ _ _ hpar]
    simp only [flipTree]
    cases parity x <;> cases t [] <;> rfl
termination_by x + y
decreasing_by omega

end Erdos196
