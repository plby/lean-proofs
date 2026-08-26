import ErdosProblems.Erdos421.MeanValueRootScale

/-! # The geometric defect in the classical complete-system iteration -/

namespace Erdos421

def meanValueTriangle (k : ℕ) : ℕ := k * (k - 1) / 2

noncomputable def meanValueDefect (k r : ℕ) : ℝ :=
  meanValueTriangle k * (1 - (k : ℝ)⁻¹) ^ r

noncomputable def meanValueExponent (k r : ℕ) : ℝ :=
  2 * ((r + 1) * k : ℕ) - (k + meanValueTriangle k : ℕ) + meanValueDefect k r

theorem meanValueTriangle_mul_two (k : ℕ) :
    meanValueTriangle k * 2 = k * (k - 1) := by
  rw [meanValueTriangle, ← Finset.sum_range_id, Finset.sum_range_id_mul_two]

theorem meanValueTriangle_le_square (k : ℕ) : meanValueTriangle k ≤ k ^ 2 := by
  calc
    _ ≤ k * (k - 1) := Nat.div_le_self _ _
    _ ≤ k * k := Nat.mul_le_mul_left k (Nat.sub_le k 1)
    _ = _ := (pow_two k).symm

theorem meanValueTriangle_real {k : ℕ} (hk : 0 < k) :
    (meanValueTriangle k : ℝ) = (k : ℝ) * ((k : ℝ) - 1) / 2 := by
  have ht := meanValueTriangle_mul_two k
  have hsub : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_one]
  have htR : (meanValueTriangle k : ℝ) * 2 = (k : ℝ) * ((k - 1 : ℕ) : ℝ) := by
    exact_mod_cast ht
  rw [hsub] at htR
  linarith

theorem meanValue_contraction_mem_Icc {k : ℕ} (hk : 0 < k) :
    0 ≤ 1 - (k : ℝ)⁻¹ ∧ 1 - (k : ℝ)⁻¹ ≤ 1 := by
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  constructor
  · exact sub_nonneg.mpr ((inv_le_one₀ (by positivity)).mpr hkR)
  · have : (0 : ℝ) ≤ (k : ℝ)⁻¹ := by positivity
    linarith

theorem meanValueDefect_nonneg {k : ℕ} (hk : 0 < k) (r : ℕ) :
    0 ≤ meanValueDefect k r :=
  mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (meanValue_contraction_mem_Icc hk).1 r)

theorem meanValueDefect_le_triangle {k : ℕ} (hk : 0 < k) (r : ℕ) :
    meanValueDefect k r ≤ meanValueTriangle k := by
  have hq := meanValue_contraction_mem_Icc hk
  exact mul_le_of_le_one_right (Nat.cast_nonneg _) (pow_le_one₀ hq.1 hq.2)

theorem meanValueDefect_succ (k r : ℕ) :
    meanValueDefect k (r + 1) = meanValueDefect k r * (1 - (k : ℝ)⁻¹) := by
  simp only [meanValueDefect, pow_succ, mul_assoc]

@[simp] theorem meanValueExponent_zero (k : ℕ) : meanValueExponent k 0 = k := by
  simp only [meanValueExponent, meanValueDefect, zero_add, one_mul, pow_zero,
    mul_one, Nat.cast_add]
  ring

theorem meanValueExponent_succ {k : ℕ} (hk : 0 < k) (r : ℕ) :
    meanValueExponent k (r + 1) = (k : ℝ) + meanValueExponent k r +
      (((2 * ((r + 1) * k) + meanValueTriangle k : ℕ) : ℝ) -
        meanValueExponent k r) * (k : ℝ)⁻¹ := by
  rw [meanValueExponent, meanValueDefect_succ]
  simp only [meanValueExponent, Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat]
  rw [meanValueTriangle_real hk]
  field_simp
  ring

theorem meanValueExponent_le_moment {k : ℕ} (hk : 0 < k) (r : ℕ) :
    meanValueExponent k r ≤ (2 * ((r + 1) * k) : ℕ) := by
  have hdef := meanValueDefect_le_triangle hk r
  dsimp only [meanValueExponent]
  push_cast
  linarith [Nat.cast_nonneg (α := ℝ) k]

theorem meanValueExponent_nonneg {k : ℕ} (hk : 0 < k) (r : ℕ) :
    0 ≤ meanValueExponent k r := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [meanValueExponent_succ hk]
    have hm := meanValueExponent_le_moment hk r
    have hdiff : 0 ≤ ((2 * ((r + 1) * k) + meanValueTriangle k : ℕ) : ℝ) -
        meanValueExponent k r := by
      push_cast
      push_cast at hm
      linarith [Nat.cast_nonneg (α := ℝ) (meanValueTriangle k)]
    positivity

end Erdos421
