import StackExchange.Puzzling139335.GlideCrossing.Algebra

/-!+# Consequences of the two source support-face height bounds
-/

namespace Puzzling139335.GlideCrossing

theorem sourceFace_angle_bounds (α β a b : ℝ)
    (hβ : 0 < β) (hβα : β ≤ α) (hα : α < Real.pi / 2) (hb : b < 1 / 2)
    (h₁ : 2 * Real.cos α * (1 / 2 - b) ≤ 1 / 2 - a)
    (h₂ : 2 * Real.cos β * (1 / 2 - a) ≤ 1 / 2 - b) :
    Real.pi / 3 ≤ α ∧ 4 * Real.cos α * Real.cos β ≤ 1 := by
  have hπ := Real.pi_pos
  have hα0 : 0 < α := lt_of_lt_of_le hβ hβα
  have hC : 0 < Real.cos α :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith, hα⟩
  have hc : 0 < Real.cos β :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have hprod := faceHeight_product (Real.cos α) (Real.cos β)
    (1 / 2 - a) (1 / 2 - b) hc.le (by linarith) h₁ h₂
  have hCc : Real.cos α ≤ Real.cos β :=
    Real.cos_le_cos_of_nonneg_of_le_pi hβ.le (by linarith) hβα
  have hhalf := smallerCos_le_half (Real.cos α) (Real.cos β) hC.le hCc hprod
  refine ⟨?_, hprod⟩
  by_contra! hlt
  have hcos := Real.cos_lt_cos_of_nonneg_of_le_pi hα0.le
    (show Real.pi / 3 ≤ Real.pi by linarith) hlt
  rw [Real.cos_pi_div_three] at hcos
  linarith

theorem strictAngleDifference (α β : ℝ)
    (hβ : 0 < β) (hβα : β < α) (hα : α < Real.pi / 2) :
    0 < Real.sin (α - β) ∧ 0 < Real.cos (α - β) := by
  have hπ := Real.pi_pos
  constructor
  · exact Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  · exact Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩

/-- The remaining normal gap rules out equality in the angle ordering. -/
theorem sourceFace_strict_order (α β a b : ℝ)
    (hβ : 0 < β) (hβα : β ≤ α) (hα : α < Real.pi / 2) (hb : b < 1 / 2)
    (h₁ : 2 * Real.cos α * (1 / 2 - b) ≤ 1 / 2 - a)
    (h₂ : 2 * Real.cos β * (1 / 2 - a) ≤ 1 / 2 - b)
    (hgap : Real.pi / 3 < Real.pi - α - β) : β < α := by
  have hlo := (sourceFace_angle_bounds α β a b hβ hβα hα hb h₁ h₂).1
  by_contra! hle
  linarith only [hlo, hβα, hle, hgap]

theorem firstCoefficient_trig (α β : ℝ) :
    Real.cos (α - β) * Real.cos β - Real.sin (α - β) * Real.sin β =
      Real.cos α := by
  rw [Real.cos_sub, Real.sin_sub]
  apply firstCoefficient_identity
  nlinarith only [Real.sin_sq_add_cos_sq β]

theorem secondCoefficient_trig (α β : ℝ) :
    Real.sin (α - β) * Real.sin α + Real.cos (α - β) * Real.cos α =
      Real.cos β := by
  rw [Real.cos_sub, Real.sin_sub]
  apply secondCoefficient_identity
  nlinarith only [Real.sin_sq_add_cos_sq α]

end Puzzling139335.GlideCrossing
