import Arxiv.Arxiv2407_19026.NumericalProfilesChecks.ULower
import Arxiv.Arxiv2407_19026.NumericalProfilesChecks.VLower
import Arxiv.Arxiv2407_19026.NumericalProfilesChecks.PLower
import Arxiv.Arxiv2407_19026.NumericalProfilesChecks.XLower
import Arxiv.Arxiv2407_19026.NumericalProfilesChecks.Book1
import Arxiv.Arxiv2407_19026.NumericalProfilesChecks.Book2
import Arxiv.Arxiv2407_19026.NumericalProfilesChecks.Book3
import Arxiv.Arxiv2407_19026.NumericalProfilesChecks.Blue
import Arxiv.Arxiv2407_19026.NumericalProfilesChecks.Limit

/-!
# Certified numerical facts for the Section 4 profiles

This module assembles independently checked affine certificates and derives
the semantic numerical bounds used by the remainder of the development.
-/

noncomputable section

namespace Arxiv2407_19026

lemma beta0U_lower :
    ∀ z ∈ Set.Icc (0 : ℝ) 1, (2 / 5 : ℝ) ≤ beta0U z := by
  exact Beta0Affine.u_lower

lemma beta0V_lower :
    ∀ z ∈ Set.Icc (0 : ℝ) 1, (3 / 4 : ℝ) ≤ beta0V z := by
  exact Beta0Affine.v_lower

lemma beta0PolynomialP_lower :
    ∀ z ∈ Set.Icc (0 : ℝ) 1,
      (1 / 2 : ℝ) ≤ beta0PolynomialP z := by
  exact Beta0Affine.p_lower

lemma beta0PolynomialX_lower :
    ∀ z ∈ Set.Icc (0 : ℝ) 1,
      (1 / 5 : ℝ) ≤ beta0PolynomialX z := by
  exact Beta0Affine.x_lower

lemma beta0PolynomialBookMargin_pos :
    ∀ z ∈ Set.Ioc (0 : ℝ) 1,
      0 < beta0PolynomialBookMargin z := by
  intro z hz
  rcases hz with ⟨hz0, hz1⟩
  by_cases h₀z : z ≤ 3 / 1000
  · have hsmall := beta0SmallBookMargin_pos ⟨hz0, h₀z⟩
    have hmargin :
        beta0SmallBookMargin z + z / 10000 =
          beta0PolynomialBookMargin z := by
      rw [beta0SmallBookMargin, beta0PolynomialBookMargin,
        beta0PolynomialX, beta0V, if_pos h₀z]
      rw [add_comm z 1]
      ring
    rw [← hmargin]
    positivity
  by_cases h₁z : z ≤ 1 / 10
  · exact
      NumericalProfilesBook1Bounds.beta0_polynomial_book_margin_pos_one
        z ⟨lt_of_not_ge h₀z, h₁z⟩
  by_cases h₂z : z ≤ 1 / 2
  · exact
      NumericalProfilesBook2Bounds.beta0_polynomial_book_margin_pos_two
        z ⟨lt_of_not_ge h₁z, h₂z⟩
  · exact
      NumericalProfilesBook3Bounds.beta0_polynomial_book_margin_pos_three
        z ⟨lt_of_not_ge h₂z, hz1⟩

lemma beta0PolynomialBlueLogMargin_lower :
    ∀ z ∈ Set.Icc (0 : ℝ) 1,
      (1 / 100000 : ℝ) ≤ beta0PolynomialBlueLogMargin z := by
  exact Beta0Affine.blue_lower

lemma beta0PolynomialLimitLogMargin_pos :
    ∀ z ∈ Set.Ioc (0 : ℝ) 1,
      0 < beta0PolynomialLimitLogMargin z := by
  intro z hz
  by_cases hzsmall : z ≤ 3 / 1000
  · exact beta0PolynomialLimitLogMargin_small_pos ⟨hz.1, hzsmall⟩
  · exact Beta0Affine.limit_pos z
      ⟨lt_of_not_ge hzsmall, hz.2⟩

/-- A form of the last-round diagonal `X` coordinate in which real powers
are expanded into logarithms and exponentials, so it can be checked by
kernel interval arithmetic. -/
def finalOptimizationX : ℝ :=
  Real.exp
      (Real.log (optimizationP (3 / 100) 1) *
        (1 / (1 - optimizationM 1))) *
    (1 - optimizationM 1)

lemma finalOptimizationX_eq :
    finalOptimizationX = optimizationX (3 / 100) 1 := by
  have hslope : 0 < optimizedRamseySlope (3 / 100) 1 :=
    lt_of_lt_of_le (by norm_num)
      (optimizedRamseySlope_beta3_pos 1 (by norm_num))
  have hp : 0 < optimizationP (3 / 100) 1 := by
    unfold optimizationP
    exact sub_pos.mpr
      (Real.exp_lt_one_iff.mpr (neg_neg_of_pos hslope))
  rw [optimizationX, Real.rpow_def_of_pos hp]
  rfl

end Arxiv2407_19026
