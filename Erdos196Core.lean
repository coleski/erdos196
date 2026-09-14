import Mathlib

namespace Erdos196

/-- A nonconstant four-term arithmetic progression, in either direction. -/
def AP4 (a b c d : ℕ) : Prop :=
  a + c = 2 * b ∧ b + d = 2 * c ∧ a ≠ b

/-- Independently selected orientations of the binary residue tree. -/
abbrev Tree := List Bool → Bool

def parity (x : ℕ) : Bool := x % 2 == 1

def childTree (t : Tree) (b : Bool) : Tree := fun path => t (b :: path)

def splitTree (preferred : Bool) (even odd : Tree) : Tree
  | [] => preferred
  | b :: path => if b then odd path else even path

/-- Compare at the first differing binary digit, read least-significant first. -/
def treeBefore (t : Tree) (x y : ℕ) : Bool :=
  if x = y then false
  else if parity x = parity y then
    treeBefore (childTree t (parity x)) (x / 2) (y / 2)
  else parity x == t []
termination_by x + y
decreasing_by omega

/-- Put the finite list before the remaining relation. -/
def Before (p : List ℕ) (R : ℕ → ℕ → Prop) (x y : ℕ) : Prop :=
  if x ∈ p then y ∉ p ∨ p.idxOf x < p.idxOf y
  else y ∉ p ∧ R x y

def NoAP4Rel (R : ℕ → ℕ → Prop) : Prop :=
  ∀ a b c d : ℕ, AP4 a b c d → ¬ (R a b ∧ R b c ∧ R c d)

/-- A finite prefix certified against some adaptable binary-tree tail. -/
def Admissible (p : List ℕ) : Prop :=
  p.Nodup ∧ ∃ t : Tree, NoAP4Rel (Before p (fun x y => treeBefore t x y = true))

def childPrefix (p : List ℕ) (b : Bool) : List ℕ :=
  (p.filter (fun x => parity x == b)).map (fun x => x / 2)

def liftValue (b : Bool) (x : ℕ) : ℕ := 2 * x + if b then 1 else 0

/-- The list has no arithmetic progression in chronological subsequence order. -/
def NoAP4List (p : List ℕ) : Prop :=
  ∀ i j k l : ℕ, i < j → j < k → k < l → l < p.length →
    ¬ AP4 (p.getD i 0) (p.getD j 0) (p.getD k 0) (p.getD l 0)

/-- An infinite sequence has no increasing or decreasing nonconstant 4AP. -/
def NoAP4Sequence (f : ℕ → ℕ) : Prop :=
  ∀ i j k l : ℕ, i < j → j < k → k < l →
    ¬ AP4 (f i) (f j) (f k) (f l)

/-- The entire original one-sided permutation question, using zero-based naturals. -/
def OriginalQuestion : Prop :=
  ∀ f : ℕ ≃ ℕ, ∃ i j k l : ℕ,
    i < j ∧ j < k ∧ k < l ∧ AP4 (f i) (f j) (f k) (f l)

theorem avoiding_permutation_refutes_original
    (h : ∃ f : ℕ ≃ ℕ, NoAP4Sequence f) : ¬ OriginalQuestion := by
  rintro hq
  obtain ⟨f, hf⟩ := h
  obtain ⟨i, j, k, l, hij, hjk, hkl, hap⟩ := hq f
  exact hf i j k l hij hjk hkl hap

theorem ap4_increasing_or_decreasing {a b c d : ℕ} (h : AP4 a b c d) :
    (a < b ∧ b < c ∧ c < d) ∨ (d < c ∧ c < b ∧ b < a) := by
  unfold AP4 at h
  omega

theorem ap4_reverse {a b c d : ℕ} (h : AP4 a b c d) : AP4 d c b a := by
  unfold AP4 at *
  omega

theorem ap4_translate_one {a b c d : ℕ} :
    AP4 (a + 1) (b + 1) (c + 1) (d + 1) ↔ AP4 a b c d := by
  unfold AP4
  omega

end Erdos196
