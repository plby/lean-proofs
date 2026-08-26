import ErdosProblems.Erdos1148.HorocycleFrames
import ErdosProblems.Erdos1148.FlowCoordinateBounds

/-! # An exp(-S/2) unstable-coordinate bound for a shared returning vector -/

namespace Erdos1148.DukeArithmetic

open scoped MatrixGroups

lemma horocycle_parameter_error_le (g : SL(2, ℝ)) (r x h S C h₀ : ℝ)
    (hh₀ : 0 < h₀) (hh : h₀ ≤ h) (hC : 0 ≤ C) (u v : ℤ)
    (hshort : modularVectorLengthSq
      ((g * unstableHorocycle r * upperTriangularFrame x h (hh₀.trans_le hh).ne') * diagonalFlow S)
        u v ≤ C ^ 2) :
    |(modularVector g u v).2 - r * (modularVector g u v).1| ≤
      C * Real.exp (-(S / 2)) / h₀ := by
  have hcoord := modularVector_second_le_of_flow_lengthSq
    (g * unstableHorocycle r * upperTriangularFrame x h (hh₀.trans_le hh).ne') S C hC u v hshort
  rw [modularVector_horocycle_upper_second, abs_mul, abs_of_pos (hh₀.trans_le hh)] at hcoord
  apply (le_div_iff₀ hh₀).mpr
  calc
    _ = h₀ * |(modularVector g u v).2 - r * (modularVector g u v).1| := mul_comm _ _
    _ ≤ h * |(modularVector g u v).2 - r * (modularVector g u v).1| :=
      mul_le_mul_of_nonneg_right hh (abs_nonneg _)
    _ ≤ _ := hcoord

theorem horocycle_width_of_shared_returning_vector (g : SL(2, ℝ))
    (r₁ r₂ x₁ x₂ h₁ h₂ S C h₀ c : ℝ) (hh₀ : 0 < h₀) (hh₁ : h₀ ≤ h₁) (hh₂ : h₀ ≤ h₂)
    (hC : 0 ≤ C) (hc : 0 < c) (u v : ℤ) (hfirst : c ≤ |(modularVector g u v).1|)
    (hshort₁ : modularVectorLengthSq
      ((g * unstableHorocycle r₁ * upperTriangularFrame x₁ h₁ (hh₀.trans_le hh₁).ne') * diagonalFlow S)
        u v ≤ C ^ 2)
    (hshort₂ : modularVectorLengthSq
      ((g * unstableHorocycle r₂ * upperTriangularFrame x₂ h₂ (hh₀.trans_le hh₂).ne') * diagonalFlow S)
        u v ≤ C ^ 2) :
    |r₁ - r₂| ≤ (2 * C / (h₀ * c)) * Real.exp (-(S / 2)) := by
  have h₁ := horocycle_parameter_error_le g r₁ x₁ h₁ S C h₀ hh₀ hh₁ hC u v hshort₁
  have h₂ := horocycle_parameter_error_le g r₂ x₂ h₂ S C h₀ hh₀ hh₂ hC u v hshort₂
  calc
    _ ≤ 2 * (C * Real.exp (-(S / 2)) / h₀) / c :=
      unstable_parameter_difference_le hc hfirst h₁ h₂
    _ = _ := by ring

end Erdos1148.DukeArithmetic
