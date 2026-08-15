import ErdosProblems.Erdos321.NormalizedRecurrence

namespace Erdos321

/-- Discrete logarithmic integral operator after normalization. -/
noncomputable def discreteLogOperator (f : ℕ → ℝ) (T : ℕ) : ℝ :=
  ∑ t ∈ Finset.Icc 2 T, f t / ((t + 1) * Real.log t)

private theorem sum_Icc_one_split {T : ℕ} (hT : 1 ≤ T) (f : ℕ → ℝ) :
    (∑ t ∈ Finset.Icc 1 T, f t) = f 1 + ∑ t ∈ Finset.Icc 2 T, f t := by
  have hset : Finset.Icc 1 T = insert 1 (Finset.Icc 2 T) := by
    ext t
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  rw [hset, Finset.sum_insert (by simp)]

/-- Exact endpoint values at `N=1`. -/
theorem extremalSize_one : extremalSize 1 = 1 := by
  exact Nat.le_antisymm (extremalSize_le 1) (one_le_extremalSize le_rfl)

theorem harmonicSubsetSumCount_one : harmonicSubsetSumCount 1 = 2 := by
  have hIcc : Finset.Icc 1 1 = {1} := by ext n; simp
  rw [harmonicSubsetSumCount, hIcc,
    subsetSumCount_eq_pow_of_valid valid_singleton_one]
  simp

/-- Exact conversion of the extremal weighted sum to the normalized discrete
logarithmic operator, including its seed `1/2`. -/
theorem weightedCofactorSum_extremal_eq
    {T : ℕ} (hT : 1 ≤ T) :
    weightedCofactorSum (fun t => (extremalSize t : ℝ)) T =
      1 / 2 + discreteLogOperator normalizedExtremal T := by
  rw [weightedCofactorSum, discreteLogOperator, sum_Icc_one_split hT]
  simp only [extremalSize_one, Nat.cast_one, one_mul]
  norm_num
  apply Finset.sum_congr rfl
  intro t ht
  have ht2 := (Finset.mem_Icc.mp ht).1
  have htpos : (0 : ℝ) < t := by exact_mod_cast (show 0 < t by omega)
  have hlogpos : 0 < Real.log (t : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < t by omega))
  dsimp [normalizedExtremal, discreteLogOperator]
  field_simp [ne_of_gt htpos, ne_of_gt hlogpos]

/-- Entropy analogue, whose seed is `(log 2)/2`. -/
theorem weightedCofactorSum_entropy_eq
    {T : ℕ} (hT : 1 ≤ T) :
    weightedCofactorSum harmonicEntropy T =
      Real.log 2 / 2 + discreteLogOperator normalizedEntropy T := by
  have hH1 : harmonicEntropy 1 = Real.log 2 := by
    rw [harmonicEntropy, harmonicSubsetSumCount_one]
    norm_num
  rw [weightedCofactorSum, discreteLogOperator,
    sum_Icc_one_split hT, hH1]
  norm_num
  apply Finset.sum_congr rfl
  intro t ht
  have ht2 := (Finset.mem_Icc.mp ht).1
  have htpos : (0 : ℝ) < t := by exact_mod_cast (show 0 < t by omega)
  have hlogpos : 0 < Real.log (t : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < t by omega))
  dsimp [normalizedEntropy, discreteLogOperator]
  field_simp [ne_of_gt htpos, ne_of_gt hlogpos]

end Erdos321
