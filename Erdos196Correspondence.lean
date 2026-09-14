/-
The three public definitions below are reproduced from the Formal Conjectures
Authors' AP/Basic.lean (Copyright 2025), under Apache-2.0:
https://www.apache.org/licenses/LICENSE-2.0
Source commit ee4aaef5655f8aa4a29d59391a822f398891a2b3.
Correspondence proofs are fresh work for this project.
-/
import Erdos196Core

def List.IsAPOfLengthWith {α : Type*} [AddCommMonoid α]
    (s : List α) (l : ℕ) (a d : α) : Prop :=
  s = (List.range l).map (fun n ↦ a + n • d) ∨
    s = (List.range l).reverse.map (fun n ↦ a + n • d)

def List.IsAPOfLength {α : Type*} [AddCommMonoid α] (s : List α) (l : ℕ) : Prop :=
  ∃ a d : α, s.IsAPOfLengthWith l a d

def HasMonotoneAP {α : Type*} [AddCommMonoid α] {β : Type*} [Preorder β]
    (f : β → α) (k : ℕ) : Prop :=
  ∃ l : List β, (l.map f).IsAPOfLength k ∧ l.Pairwise (· < ·)

namespace Erdos196

theorem canonical_hasMonotoneAP_four_iff (f : ℕ → ℕ) (hinj : Function.Injective f) :
    HasMonotoneAP f 4 ↔ ∃ i j k l : ℕ,
      i < j ∧ j < k ∧ k < l ∧ AP4 (f i) (f j) (f k) (f l) := by
  constructor
  · rintro ⟨seq, ⟨a, d, hseq⟩, hsorted⟩
    have hlen : seq.length = 4 := by
      rcases hseq with hseq | hseq <;>
        have hl := congrArg List.length hseq <;> simpa using hl
    obtain ⟨i, j, k, l, rfl⟩ := List.length_eq_four.mp hlen
    simp only [List.pairwise_cons, List.mem_cons, forall_eq_or_imp] at hsorted
    have hij : i < j := hsorted.1.1
    have hjk : j < k := hsorted.2.1.1
    have hkl : k < l := hsorted.2.2.1.1
    have hne : f i ≠ f j := by intro he; have := hinj he; omega
    refine ⟨i, j, k, l, hij, hjk, hkl, ?_⟩
    simp [List.IsAPOfLengthWith, List.range_succ] at hseq
    unfold AP4
    rcases hseq with hseq | hseq <;> omega
  · rintro ⟨i, j, k, l, hij, hjk, hkl, hap⟩
    refine ⟨[i,j,k,l], ?_, ?_⟩
    · rcases ap4_increasing_or_decreasing hap with hinc | hdec
      · refine ⟨f i, f j - f i, Or.inl ?_⟩
        simp [List.range_succ]
        obtain ⟨h1, h2, h3⟩ := hap
        omega
      · refine ⟨f l, f k - f l, Or.inr ?_⟩
        simp [List.range_succ]
        obtain ⟨h1, h2, h3⟩ := hap
        omega
    · simp
      omega

theorem noAP4Sequence_iff_not_canonical (f : ℕ → ℕ) (hinj : Function.Injective f) :
    NoAP4Sequence f ↔ ¬ HasMonotoneAP f 4 := by
  rw [canonical_hasMonotoneAP_four_iff f hinj]
  unfold NoAP4Sequence
  aesop

theorem original_iff_canonical :
    OriginalQuestion ↔ ∀ f : ℕ ≃ ℕ, HasMonotoneAP f 4 := by
  unfold OriginalQuestion
  exact forall_congr' (fun f => (canonical_hasMonotoneAP_four_iff f f.injective).symm)

theorem avoiding_permutation_refutes_canonical
    (h : ∃ f : ℕ ≃ ℕ, NoAP4Sequence f) :
    ¬ (∀ f : ℕ ≃ ℕ, HasMonotoneAP f 4) := by
  rw [← original_iff_canonical]
  exact avoiding_permutation_refutes_original h

theorem noAP4Sequence_translate_one (f : ℕ → ℕ) :
    NoAP4Sequence (fun n => f n + 1) ↔ NoAP4Sequence f := by
  unfold NoAP4Sequence
  simp only [ap4_translate_one]

/-- Reindex both the positions and values by the natural/positive-natural equivalence. -/
def positivePermutation (f : ℕ ≃ ℕ) : ℕ+ ≃ ℕ+ :=
  (Equiv.pnatEquivNat.trans f).trans Equiv.pnatEquivNat.symm

theorem positivePermutation_value (f : ℕ ≃ ℕ) (i : ℕ+) :
    (positivePermutation f i : ℕ) = f ((i : ℕ) - 1) + 1 := rfl

def PositiveOriginalQuestion : Prop :=
  ∀ f : ℕ+ ≃ ℕ+, ∃ i j k l : ℕ+,
    i < j ∧ j < k ∧ k < l ∧
      AP4 (f i : ℕ) (f j : ℕ) (f k : ℕ) (f l : ℕ)

theorem avoiding_permutation_refutes_positive
    (h : ∃ f : ℕ ≃ ℕ, NoAP4Sequence f) : ¬ PositiveOriginalQuestion := by
  rintro hpos
  obtain ⟨f, hf⟩ := h
  obtain ⟨i, j, k, l, hij, hjk, hkl, hap⟩ := hpos (positivePermutation f)
  simp only [positivePermutation_value, ap4_translate_one] at hap
  exact hf ((i : ℕ)-1) ((j : ℕ)-1) ((k : ℕ)-1) ((l : ℕ)-1)
    (PNat.natPred_strictMono hij) (PNat.natPred_strictMono hjk)
    (PNat.natPred_strictMono hkl) hap

#print axioms avoiding_permutation_refutes_canonical
#print axioms avoiding_permutation_refutes_positive

end Erdos196
