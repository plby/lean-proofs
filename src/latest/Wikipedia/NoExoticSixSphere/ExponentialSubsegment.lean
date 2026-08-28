import Wikipedia.NoExoticSixSphere.OrthogonalSegmentEnergy

/-!
# Exact subdivision of a rescaled exponential segment
-/

namespace NoExoticSixSphere.OrthogonalPathEnergy

open GLOrthonormalization CayleyTransform OrthogonalExponential

variable {n : ℕ}

theorem rescaledSegment_increment (a : OrthogonalOperators n) (K : SkewOperators n)
    (s u α β : ℝ) :
    (rescaledSegment a K s u α)⁻¹ * rescaledSegment a K s u β =
      exp (((β - α) / (u - s)) • K) := by
  apply mul_left_cancel (a := rescaledSegment a K s u α)
  rw [mul_inv_cancel_left]
  simp only [rescaledSegment, mul_assoc, ← exp_add_smul]
  apply congrArg (fun r : ℝ ↦ a * exp (r • K))
  ring

theorem rescaledSegment_subsegment (a : OrthogonalOperators n) (K : SkewOperators n)
    (s u α β t : ℝ) (hαβ : α ≠ β) :
    rescaledSegment (rescaledSegment a K s u α) (((β - α) / (u - s)) • K) α β t =
      rescaledSegment a K s u t := by
  simp only [rescaledSegment, smul_smul, mul_assoc, ← exp_add_smul]
  apply congrArg (fun r : ℝ ↦ a * exp (r • K))
  have hd : β - α ≠ 0 := sub_ne_zero.mpr hαβ.symm
  calc
    (α - s) / (u - s) + (t - α) / (β - α) * ((β - α) / (u - s)) =
        (α - s) / (u - s) + (t - α) / (u - s) := by
      rw [div_mul_div_cancel₀ hd]
    _ = (t - s) / (u - s) := by ring

end NoExoticSixSphere.OrthogonalPathEnergy
