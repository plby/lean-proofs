import ErdosProblems.Erdos220.Basic

/-!
# The literal formulation of Erdős Problem 220

The problem statement uses the positive reduced residues `1 ≤ m < n`.  This
differs from Mathlib's canonical representatives in `[0,n)` only at `n = 1`:
the literal set is empty there, while `Nat.totient 1 = 1` counts the class
represented by `0`.  Since both formulations have no internal gap at `n = 1`,
their adjacent-gap square sums nevertheless agree for every `n`.
-/

open scoped BigOperators

namespace Erdos220

/-- The positive reduced residues strictly below `n`, exactly as written in
Erdős Problem 220. -/
def reducedResidues (n : ℕ) : Finset ℕ :=
  (Finset.Ico 1 n).filter fun m ↦ n.Coprime m

/-- The literal reduced residues, in increasing order. -/
def reducedResidueList (n : ℕ) : List ℕ :=
  (reducedResidues n).sort (· ≤ ·)

/-- The sum of the squares of the internal adjacent gaps in the literal
increasing list.  There is no wrap-around term. -/
def internalGapSquareSum (n : ℕ) : ℝ :=
  let a := reducedResidueList n
  ∑ k ∈ Finset.range (a.length - 1),
    ((a[k + 1]! : ℝ) - (a[k]! : ℝ)) ^ 2

@[simp] lemma mem_reducedResidues {n m : ℕ} :
    m ∈ reducedResidues n ↔ 1 ≤ m ∧ m < n ∧ n.Coprime m := by
  simp [reducedResidues, and_assoc]

@[simp] lemma reducedResidues_zero : reducedResidues 0 = ∅ := by
  simp [reducedResidues]

@[simp] lemma reducedResidues_one : reducedResidues 1 = ∅ := by
  simp [reducedResidues]

/-- Away from the exceptional modulus `1`, the literal positive residue set
is the canonical unit-representative finset used in `Basic.lean`. -/
lemma reducedResidues_eq_reducedResidueFinset {n : ℕ} (hn : 1 < n) :
    reducedResidues n = reducedResidueFinset n := by
  ext m
  simp only [mem_reducedResidues, mem_reducedResidueFinset]
  constructor
  · rintro ⟨_hm1, hmn, hcop⟩
    exact ⟨hmn, hcop⟩
  · rintro ⟨hmn, hcop⟩
    have hm0 : m ≠ 0 := by
      intro hm
      subst m
      have hn1 : n = 1 := (Nat.coprime_zero_right n).mp hcop
      omega
    exact ⟨Nat.one_le_iff_ne_zero.mpr hm0, hmn, hcop⟩

/-- The literal set has cardinality `φ(n)` for `n ≥ 2`.  The hypothesis is
necessary: the literal set is empty at `n = 1`, but `Nat.totient 1 = 1`. -/
lemma card_reducedResidues {n : ℕ} (hn : 1 < n) :
    (reducedResidues n).card = n.totient := by
  rw [reducedResidues_eq_reducedResidueFinset hn]
  exact card_reducedResidueFinset n

lemma length_reducedResidueList {n : ℕ} (hn : 1 < n) :
    (reducedResidueList n).length = n.totient := by
  rw [reducedResidueList, Finset.length_sort, card_reducedResidues hn]

/-- Indexing the literal sorted list agrees with the canonical order
embedding from `Basic.lean`. -/
lemma reducedResidueList_getElem! {n i : ℕ} (hn : 1 < n)
    (hi : i < n.totient) :
    (reducedResidueList n)[i]! = reducedResidue n ⟨i, hi⟩ := by
  have hilist : i < (reducedResidueList n).length := by
    rw [length_reducedResidueList hn]
    exact hi
  rw [getElem!_pos (reducedResidueList n) i hilist]
  simpa [reducedResidueList, reducedResidues_eq_reducedResidueFinset hn,
    reducedResidue] using
      (Finset.orderEmbOfFin_apply (reducedResidueFinset n)
        (card_reducedResidueFinset n) ⟨i, hi⟩).symm

/-- For `n ≥ 2`, the literal adjacent-gap sum is the canonical gap sum
used by the analytic development. -/
lemma internalGapSquareSum_eq_gapSquareSum_of_one_lt {n : ℕ} (hn : 1 < n) :
    internalGapSquareSum n = gapSquareSum n := by
  rw [internalGapSquareSum, length_reducedResidueList hn, gapSquareSum,
    Finset.sum_fin_eq_sum_range]
  apply Finset.sum_congr rfl
  intro k hk
  have hk' : k < n.totient - 1 := Finset.mem_range.mp hk
  have hkLeft : k < n.totient := by omega
  have hkRight : k + 1 < n.totient := by omega
  rw [dif_pos hk']
  rw [reducedResidueList_getElem! hn hkRight,
    reducedResidueList_getElem! hn hkLeft]
  rfl

/-- The literal and canonical internal-gap square sums agree at every
modulus, including the exceptional moduli `0` and `1`. -/
lemma internalGapSquareSum_eq_gapSquareSum (n : ℕ) :
    internalGapSquareSum n = gapSquareSum n := by
  by_cases hn : 1 < n
  · exact internalGapSquareSum_eq_gapSquareSum_of_one_lt hn
  · have hn_cases : n = 0 ∨ n = 1 := by omega
    rcases hn_cases with rfl | rfl <;>
      rw [gapSquareSum, Finset.sum_fin_eq_sum_range] <;>
      simp [internalGapSquareSum, reducedResidueList]

end Erdos220
