import Wikipedia.SmoothSixDPoincare.BumpTranslationDiffeomorph

/-!
# Global Lipschitz control for a cutoff of a locally controlled displacement

Inside the prescribed set, the scalar and vector Lipschitz estimates combine.
Across its boundary, the cutoff vanishes at the exterior point, so its own
Lipschitz estimate controls the displacement without any extension hypothesis
on the original vector-valued map outside that set.
-/

noncomputable section

open Set Function
open scoped NNReal

namespace Wikipedia.SmoothSixDPoincare.SmallPerturbation

variable {P E : Type*} [PseudoMetricSpace P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A bounded cutoff gives a global estimate for a map that is only locally Lipschitz. -/
theorem lipschitzWith_cutoff_smul {u : P → E} {β : P → ℝ} {S : Set P}
    {a b R : ℝ≥0} (hu : LipschitzOnWith a u S)
    (hbound : ∀ x ∈ S, ‖u x‖ ≤ R) (hβ : LipschitzWith b β)
    (hβbound : ∀ x, |β x| ≤ 1) (hzero : ∀ x ∉ S, β x = 0) :
    LipschitzWith (a + b * R) (fun x => β x • u x) := by
  have hcross (x y : P) (hx : x ∈ S) (hy : y ∉ S) :
      dist (β x • u x) (β y • u y) ≤ ((a + b * R : ℝ≥0) : ℝ) * dist x y := by
    have hβx : |β x| ≤ (b : ℝ) * dist x y := by
      have h := hβ.dist_le_mul x y
      simpa only [hzero y hy, Real.dist_eq, sub_zero] using h
    rw [hzero y hy, zero_smul, dist_zero_right, norm_smul, Real.norm_eq_abs]
    calc
      |β x| * ‖u x‖ ≤ ((b : ℝ) * dist x y) * R :=
        mul_le_mul hβx (hbound x hx) (norm_nonneg _) (by positivity)
      _ ≤ ((a + b * R : ℝ≥0) : ℝ) * dist x y := by
        simp only [NNReal.coe_add, NNReal.coe_mul]
        nlinarith [mul_nonneg a.coe_nonneg (dist_nonneg (x := x) (y := y))]
  apply LipschitzWith.of_dist_le_mul
  intro x y
  by_cases hx : x ∈ S
  · by_cases hy : y ∈ S
    · have hu' : ‖u x - u y‖ ≤ (a : ℝ) * dist x y := by
        simpa only [dist_eq_norm] using hu.dist_le_mul x hx y hy
      have hβ' : |β x - β y| ≤ (b : ℝ) * dist x y := by
        simpa only [Real.dist_eq] using hβ.dist_le_mul x y
      have hsplit : β x • u x - β y • u y =
          β x • (u x - u y) + (β x - β y) • u y := by
        rw [smul_sub, sub_smul]
        abel
      rw [dist_eq_norm, hsplit]
      calc
        ‖β x • (u x - u y) + (β x - β y) • u y‖ ≤
            ‖β x • (u x - u y)‖ + ‖(β x - β y) • u y‖ := norm_add_le _ _
        _ = |β x| * ‖u x - u y‖ + |β x - β y| * ‖u y‖ := by
          rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
        _ ≤ 1 * ((a : ℝ) * dist x y) + ((b : ℝ) * dist x y) * R := by
          exact add_le_add
            (mul_le_mul (hβbound x) hu' (norm_nonneg _) (by norm_num))
            (mul_le_mul hβ' (hbound y hy) (norm_nonneg _) (by positivity))
        _ = ((a + b * R : ℝ≥0) : ℝ) * dist x y := by
          simp only [NNReal.coe_add, NNReal.coe_mul]
          ring
    · exact hcross x y hx hy
  · by_cases hy : y ∈ S
    · simpa only [dist_comm] using hcross y x hy hx
    · rw [hzero x hx, hzero y hy, zero_smul, zero_smul, dist_self]
      positivity

end Wikipedia.SmoothSixDPoincare.SmallPerturbation
