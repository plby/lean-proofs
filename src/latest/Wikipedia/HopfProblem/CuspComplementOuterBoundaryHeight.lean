import Wikipedia.HopfProblem.ThreefoldHomologyFinitenessCuspHeight

/-!
# The original logarithmic height of a specified positive cusp radius

Every radius strictly inside the actual cusp filling determines an
allowed height. The original height-product homeomorphism recovers
exactly that radius, without changing any of the four period coordinates.
-/

noncomputable section

open Set Topology

namespace Wikipedia.HopfProblem.CuspComplement.OuterBoundary

open SpecialPeriods.CuspFamily ThreefoldOverlapMappingTorus.Cusp
open ThreefoldHomologyFinitenessCusp CuspUniformization

/-- The literal logarithmic height of a smaller positive radius. -/
def heightAtRadius (D : Data) (η : ℝ) (hη : 0 < η) (hηr : η < D.radius) :
    Height D.radius :=
  ⟨heightThreshold η, by
    change -Real.log D.radius / (2 * Real.pi) < -Real.log η / (2 * Real.pi)
    apply (div_lt_div_iff_of_pos_right (mul_pos (by norm_num) Real.pi_pos)).mpr
    exact neg_lt_neg (Real.log_lt_log hη hηr)⟩

@[simp] theorem heightAtRadius_coe (D : Data) (η : ℝ) (hη : 0 < η)
    (hηr : η < D.radius) :
    (heightAtRadius D η hη hηr : ℝ) = heightThreshold η := rfl

/-- Exponentiating the selected height gives the original radius exactly. -/
theorem heightAtRadius_exp (D : Data) (η : ℝ) (hη : 0 < η) (hηr : η < D.radius) :
    Real.exp (-2 * Real.pi * (heightAtRadius D η hη hηr : ℝ)) = η := by
  have hp : (2 : ℝ) * Real.pi ≠ 0 := ne_of_gt (mul_pos (by norm_num) Real.pi_pos)
  have ht : 2 * Real.pi * heightThreshold η = -Real.log η := by
    unfold heightThreshold
    exact mul_div_cancel₀ _ hp
  have he : -2 * Real.pi * (heightAtRadius D η hη hηr : ℝ) = Real.log η := by
    change -2 * Real.pi * heightThreshold η = Real.log η
    linarith only [ht]
  rw [he, Real.exp_log hη]

/-- The positive original parameter norm determines a unique logarithmic height. -/
theorem exp_height_eq_radius_iff (D : Data) (η : ℝ) (hη : 0 < η)
    (hηr : η < D.radius) (h : Height D.radius) :
    Real.exp (-2 * Real.pi * (h : ℝ)) = η ↔ h = heightAtRadius D η hη hηr := by
  constructor
  · intro he
    have heq := Real.exp_injective (he.trans (heightAtRadius_exp D η hη hηr).symm)
    apply Subtype.ext
    exact mul_left_cancel₀
      (mul_ne_zero (by norm_num : (-2 : ℝ) ≠ 0) (ne_of_gt Real.pi_pos)) heq
  · rintro rfl
    exact heightAtRadius_exp D η hη hηr

end Wikipedia.HopfProblem.CuspComplement.OuterBoundary
