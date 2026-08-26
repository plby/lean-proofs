import ErdosProblems.Erdos69.Construction

/-! # Logarithmic size of the CRT construction -/

open scoped BigOperators

namespace Erdos69.Elementary

theorem patternSize_ge_thirtysix {m : ℕ} (hm : 0 < m) : 36 ≤ patternSize m := by
  change 36 ≤ 36 ^ m
  simpa using Nat.pow_le_pow_right (by norm_num : 0 < 36) (show 1 ≤ m by omega)

theorem constructionMaxDilation_pos (m : ℕ) : 0 < constructionMaxDilation m :=
  roughDilation_pos _ _

theorem log_constructionMaxDilation_le (m : ℕ) :
    Real.log (constructionMaxDilation m : ℝ) ≤ 5 * dilationPrimeCutoff m :=
  log_roughDilation_le (dilationPrimeCutoff_pos m) le_rfl

theorem log_constructionProduct_le (m : ℕ) :
    Real.log (constructionProduct m : ℝ) ≤ 5 * patternSize m * dilationPrimeCutoff m := by
  rw [constructionProduct, Nat.cast_prod, Real.log_prod
    (fun i _ ↦ by exact_mod_cast (constructionDilation_pos m i).ne')]
  calc
    _ ≤ ∑ _i : PatternLabel m, (5 : ℝ) * dilationPrimeCutoff m := by
      apply Finset.sum_le_sum
      intro i hi
      have hlog : Real.log (constructionDilation m i : ℝ) ≤
          Real.log (constructionMaxDilation m : ℝ) := by
        apply Real.log_le_log (by exact_mod_cast constructionDilation_pos m i)
        exact_mod_cast constructionDilation_le_max m i
      exact hlog.trans (log_constructionMaxDilation_le m)
    _ = _ := by simp [card_patternLabel, patternSize]; ring

theorem constructionShift_le (m : ℕ) (r : ConstructionShift m) :
    r.val ≤ constructionMaxDilation m * (6 * m + retainedLength m) := by
  obtain ⟨⟨i, k⟩, ht, heq⟩ := Finset.mem_image.mp r.property
  rw [← heq]
  apply (patternShift_le_dilation_mul m (dilationPrimeCutoff m) _ i).trans
  exact Nat.mul_le_mul (constructionDilation_le_max m i) (by have hk := k.isLt; omega)

theorem log_constructionModulus_raw (m : ℕ) :
    Real.log (constructionModulus m : ℝ) ≤
      5 * patternSize m * dilationPrimeCutoff m +
      ((patternSize m : ℝ) * retainedLength m) ^ 2 *
        (5 * dilationPrimeCutoff m + (6 * m + retainedLength m)) := by
  have hM : 0 < constructionMaxDilation m * (6 * m + retainedLength m) :=
    Nat.mul_pos (constructionMaxDilation_pos m) (by have h := retainedLength_pos m; omega)
  have hcollision := log_collisionProduct_le (fun r : ConstructionShift m ↦ r.val)
    Subtype.val_injective _ hM (constructionShift_le m)
  have hlogM : Real.log (constructionMaxDilation m * (6 * m + retainedLength m) : ℕ) ≤
      5 * dilationPrimeCutoff m + (6 * m + retainedLength m : ℕ) := by
    have hlen : (0 : ℝ) < (6 * m + retainedLength m : ℕ) := by
      exact_mod_cast (show 0 < 6 * m + retainedLength m by have h := retainedLength_pos m; omega)
    rw [Nat.cast_mul, Real.log_mul (by exact_mod_cast (constructionMaxDilation_pos m).ne') hlen.ne']
    have hloglen := Real.log_le_sub_one_of_pos hlen
    linarith [log_constructionMaxDilation_le m]
  have hcard : (Fintype.card (ConstructionShift m) : ℝ) ≤
      (patternSize m : ℝ) * retainedLength m := by exact_mod_cast constructionShift_card_le m
  have hCl : Real.log (constructionCollisionProduct m : ℝ) ≤
      ((patternSize m : ℝ) * retainedLength m) ^ 2 *
        (5 * dilationPrimeCutoff m + (6 * m + retainedLength m)) := by
    apply hcollision.trans
    gcongr
    exact_mod_cast hlogM
  exact (log_augmentedModulus_le (constructionProduct_pos m)
    (constructionCollisionProduct_pos m)).trans (add_le_add (log_constructionProduct_le m) hCl)

theorem patternSize_pow_five_le_primeCutoff {m : ℕ} (hm : 0 < m) :
    patternSize m ^ 5 ≤ dilationPrimeCutoff m := by
  have hN := patternSize_ge_thirtysix hm
  calc
    patternSize m ^ 5 ≤ (2 ^ patternSize m) ^ 5 :=
      Nat.pow_le_pow_left Nat.lt_two_pow_self.le _
    _ = 2 ^ (patternSize m * 5) := by rw [pow_mul]
    _ ≤ 2 ^ (patternSize m ^ 2) := by
      apply Nat.pow_le_pow_right (by norm_num)
      nlinarith

theorem polynomial_primeCutoff_le_excluded {m : ℕ} (hm : 0 < m) :
    patternSize m ^ 12 * dilationPrimeCutoff m ≤ excludedPrimeCutoff m := by
  have hN := patternSize_ge_thirtysix hm
  have hexp : patternSize m * 12 + patternSize m ^ 2 ≤ patternSize m ^ 3 := by
    have h₁ := Nat.mul_le_mul_right (patternSize m) (show 12 ≤ patternSize m by omega)
    have h₂ := Nat.mul_le_mul_right (patternSize m ^ 2) (show 2 ≤ patternSize m by omega)
    nlinarith
  calc
    _ ≤ (2 ^ patternSize m) ^ 12 * dilationPrimeCutoff m :=
      Nat.mul_le_mul_right _ (Nat.pow_le_pow_left Nat.lt_two_pow_self.le _)
    _ = 2 ^ (patternSize m * 12 + patternSize m ^ 2) := by
      rw [dilationPrimeCutoff, pow_add, pow_mul]
    _ ≤ excludedPrimeCutoff m := Nat.pow_le_pow_right (by norm_num) hexp

theorem total_retainedLength_le_size_pow_five {m : ℕ} (hm : 0 < m) :
    6 * m + retainedLength m ≤ patternSize m ^ 5 := by
  have hN := patternSize_ge_thirtysix hm
  have hpow : patternSize m ≤ patternSize m ^ 4 := by
    simpa using Nat.pow_le_pow_right (patternSize_pos m) (show 1 ≤ 4 by omega)
  have hthree : 3 * patternSize m ^ 4 ≤ patternSize m * patternSize m ^ 4 :=
    Nat.mul_le_mul_right _ (by omega)
  unfold retainedLength fluctuationScale
  have hK := initialLength_le_patternSize m
  calc
    _ ≤ 3 * patternSize m ^ 4 := by omega
    _ ≤ patternSize m * patternSize m ^ 4 := hthree
    _ = patternSize m ^ 5 := by ring

theorem log_constructionModulus_le_size_polynomial {m : ℕ} (hm : 0 < m) :
    Real.log (constructionModulus m : ℝ) ≤ (patternSize m : ℝ) ^ 12 * dilationPrimeCutoff m := by
  let N : ℝ := patternSize m
  let P : ℝ := dilationPrimeCutoff m
  have hN : 36 ≤ N := by dsimp [N]; exact_mod_cast patternSize_ge_thirtysix hm
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have hlen : ((6 * m + retainedLength m : ℕ) : ℝ) ≤ P := by
    dsimp [P]
    exact_mod_cast (total_retainedLength_le_size_pow_five hm).trans
      (patternSize_pow_five_le_primeCutoff hm)
  have hH : (retainedLength m : ℝ) = 2 * N ^ 4 := by
    simp [retainedLength, fluctuationScale, N]
  have hraw := log_constructionModulus_raw m
  have hraw' : Real.log (constructionModulus m : ℝ) ≤
      5 * N * P + (N * (2 * N ^ 4)) ^ 2 * (5 * P + P) := by
    apply hraw.trans
    rw [hH]
    gcongr
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, hH] using hlen
  have hN0 : 0 ≤ N := by linarith
  have hN1 : 1 ≤ N := by linarith
  have hlow : N ^ 2 ≤ N ^ 11 := pow_le_pow_right₀ hN1 (by omega)
  calc
    _ ≤ 5 * N * P + (N * (2 * N ^ 4)) ^ 2 * (5 * P + P) := hraw'
    _ ≤ N ^ 2 * P + (N * (2 * N ^ 4)) ^ 2 * (N * P) := by
      apply add_le_add
      · nlinarith [mul_nonneg (show 0 ≤ N - 5 by linarith) (mul_nonneg hN0 hP)]
      · apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
        nlinarith
    _ = (N ^ 2 + 4 * N ^ 11) * P := by ring
    _ ≤ (5 * N ^ 11) * P := by gcongr; linarith
    _ ≤ N ^ 12 * P := by
      apply mul_le_mul_of_nonneg_right _ hP
      have h := mul_le_mul_of_nonneg_right (show (5 : ℝ) ≤ N by linarith)
        (pow_nonneg hN0 11)
      simpa only [pow_succ', show N ^ (11 + 1) = N ^ 12 by rfl] using h

theorem log_constructionModulus_le_excluded {m : ℕ} (hm : 0 < m) :
    Real.log (constructionModulus m : ℝ) ≤ excludedPrimeCutoff m := by
  apply (log_constructionModulus_le_size_polynomial hm).trans
  exact_mod_cast polynomial_primeCutoff_le_excluded hm

end Erdos69.Elementary
