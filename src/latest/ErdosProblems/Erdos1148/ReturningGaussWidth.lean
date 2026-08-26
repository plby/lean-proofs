import ErdosProblems.Erdos1148.GaussVectorEnergy

/-! # A uniform unstable diameter for points sharing a bounded returning vector -/

namespace Erdos1148.DukeArithmetic

open scoped MatrixGroups

theorem returning_gauss_width_le (g : SL(2, ℝ)) (r₁ r₂ x₁ x₂ h₁ h₂ S c : ℝ)
    (hx₁ : |x₁| ≤ 1) (hh₁ : 1 / 2 ≤ h₁) (hh₁2 : h₁ ≤ 2)
    (hh₂ : 1 / 2 ≤ h₂) (hc : 0 < c) (u v : ℤ)
    (hlow : c ≤ modularVectorLengthSq
      (g * unstableHorocycle r₁ * upperTriangularFrame x₁ h₁ (by linarith : h₁ ≠ 0)) u v)
    (hreturn₁ : modularVectorLengthSq
      ((g * unstableHorocycle r₁ * upperTriangularFrame x₁ h₁ (by linarith : h₁ ≠ 0)) * diagonalFlow S)
        u v ≤ 1)
    (hreturn₂ : modularVectorLengthSq
      ((g * unstableHorocycle r₂ * upperTriangularFrame x₂ h₂ (by linarith : h₂ ≠ 0)) * diagonalFlow S)
        u v ≤ 1)
    (hsmall : 96 * Real.exp (-S) ≤ c) :
    |r₁ - r₂| ≤ (16 / Real.sqrt c) * Real.exp (-(S / 2)) := by
  have hfirst := gauss_base_first_coordinate_lower g r₁ x₁ h₁ S c hx₁ hh₁ hh₁2 hc.le
    u v hlow hreturn₁ hsmall
  have h := horocycle_width_of_shared_returning_vector g r₁ r₂ x₁ x₂ h₁ h₂ S 1 (1 / 2)
    (Real.sqrt c / 4) (by norm_num) hh₁ hh₂ (by norm_num) (by positivity) u v hfirst
    (by simpa only [one_pow] using hreturn₁) (by simpa only [one_pow] using hreturn₂)
  have heq : 2 * (1 : ℝ) / (1 / 2 * (Real.sqrt c / 4)) = 16 / Real.sqrt c := by ring
  rwa [heq] at h

end Erdos1148.DukeArithmetic
