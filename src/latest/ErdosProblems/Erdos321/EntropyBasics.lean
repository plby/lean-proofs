import ErdosProblems.Erdos321.EntropyRecurrence

namespace Erdos321

/-- A finite denominator set has no more values than subsets. -/
theorem subsetSumCount_le_pow (A : Finset ℕ) :
    subsetSumCount A ≤ 2 ^ A.card := by
  rw [subsetSumCount, subsetSumValues]
  exact (Finset.card_image_le).trans (by simp)

/-- Trivial total entropy bound. -/
theorem harmonicSubsetSumCount_le_two_pow (N : ℕ) :
    harmonicSubsetSumCount N ≤ 2 ^ N := by
  exact (subsetSumCount_le_pow (Finset.Icc 1 N)).trans_eq (by simp)

/-- The set of harmonic subset-sum values grows with the endpoint. -/
theorem harmonicSubsetSumCount_mono : Monotone harmonicSubsetSumCount := by
  intro N M hNM
  change (subsetSumValues (Finset.Icc 1 N)).card ≤
    (subsetSumValues (Finset.Icc 1 M)).card
  apply Finset.card_le_card
  intro q hq
  rcases Finset.mem_image.mp hq with ⟨S, hS, rfl⟩
  rw [subsetSumValues, Finset.mem_image]
  refine ⟨S, Finset.mem_powerset.mpr ?_, rfl⟩
  intro n hn
  have hnIcc := Finset.mem_Icc.mp (Finset.mem_powerset.mp hS hn)
  exact Finset.mem_Icc.mpr ⟨hnIcc.1, hnIcc.2.trans hNM⟩

/-- Entropy is nonnegative. -/
theorem harmonicEntropy_nonneg (N : ℕ) : 0 ≤ harmonicEntropy N := by
  rw [harmonicEntropy]
  apply Real.log_nonneg
  exact_mod_cast (Nat.succ_le_iff.mpr (harmonicSubsetSumCount_pos N))

/-- Entropy is monotone. -/
theorem harmonicEntropy_mono : Monotone harmonicEntropy := by
  intro N M hNM
  rw [harmonicEntropy, harmonicEntropy]
  exact Real.log_le_log
    (by exact_mod_cast harmonicSubsetSumCount_pos N)
    (by exact_mod_cast harmonicSubsetSumCount_mono hNM)

/-- In natural logarithms, total entropy is at most `N log 2`. -/
theorem harmonicEntropy_le_card (N : ℕ) :
    harmonicEntropy N ≤ N * Real.log 2 := by
  have hpos : (0 : ℝ) < harmonicSubsetSumCount N := by
    exact_mod_cast harmonicSubsetSumCount_pos N
  have hcast : (harmonicSubsetSumCount N : ℝ) ≤ (2 ^ N : ℕ) := by
    exact_mod_cast harmonicSubsetSumCount_le_two_pow N
  calc
    harmonicEntropy N ≤ Real.log ((2 ^ N : ℕ) : ℝ) := by
      exact Real.log_le_log hpos hcast
    _ = N * Real.log 2 := by
      rw [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]

end Erdos321
