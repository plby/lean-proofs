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

namespace Beta0Affine

lemma book_check :
    LeanCert.Validity.checkLowerAffineCover book (1 / 10000000000)
        cfg (3 / 1000) bookBreakpoints₁ = true ∧
      LeanCert.Validity.checkLowerAffineCover book (1 / 10000000000)
        cfg (1 / 10) bookBreakpoints₂ = true ∧
      LeanCert.Validity.checkLowerAffineCover book (1 / 10000000000)
        cfg (1 / 2) bookBreakpoints₃ = true :=
  ⟨book_check₁, book_check₂, book_check₃⟩

end Beta0Affine


lemma beta0U_lower :
    ∀ z ∈ Set.Icc (0 : ℝ) 1, (2 / 5 : ℝ) ≤ beta0U z := by
  have h :=
    LeanCert.Validity.verify_lower_affine_cover
      Beta0Affine.u Beta0Affine.u_supported
      (2 / 5) Beta0Affine.cfg 0
      Beta0Affine.coarseBreakpoints Beta0Affine.coarseBreakpoints_ne
      Beta0Affine.u_lower_check
  rw [Beta0Affine.coarseBreakpoints_last] at h
  intro z hz
  have hz' :
      z ∈ Set.Icc ((0 : ℚ) : ℝ) ((1 : ℚ) : ℝ) := by
    constructor <;> norm_num at hz ⊢ <;> linarith [hz.1, hz.2]
  simpa [Beta0Affine.eval_u] using h z hz'

lemma beta0V_lower :
    ∀ z ∈ Set.Icc (0 : ℝ) 1, (3 / 4 : ℝ) ≤ beta0V z := by
  have h :=
    LeanCert.Validity.verify_lower_affine_cover
      Beta0Affine.v Beta0Affine.v_supported
      (3 / 4) Beta0Affine.cfg 0
      Beta0Affine.coarseBreakpoints Beta0Affine.coarseBreakpoints_ne
      Beta0Affine.v_lower_check
  rw [Beta0Affine.coarseBreakpoints_last] at h
  intro z hz
  by_cases hzsmall : z ≤ 3 / 1000
  · simp [beta0V, if_pos hzsmall]
    norm_num
  · have hz' :
        z ∈ Set.Icc ((0 : ℚ) : ℝ) ((1 : ℚ) : ℝ) := by
      constructor <;> norm_num at hz ⊢ <;> linarith [hz.1, hz.2]
    simpa [Beta0Affine.eval_v, beta0V, if_neg hzsmall] using h z hz'

lemma beta0PolynomialP_lower :
    ∀ z ∈ Set.Icc (0 : ℝ) 1,
      (1 / 2 : ℝ) ≤ beta0PolynomialP z := by
  have h :=
    LeanCert.Validity.verify_lower_affine_cover
      Beta0Affine.p Beta0Affine.p_supported
      (1 / 2) Beta0Affine.cfg 0
      Beta0Affine.coarseBreakpoints Beta0Affine.coarseBreakpoints_ne
      Beta0Affine.p_lower_check
  rw [Beta0Affine.coarseBreakpoints_last] at h
  intro z hz
  have hz' :
      z ∈ Set.Icc ((0 : ℚ) : ℝ) ((1 : ℚ) : ℝ) := by
    constructor <;> norm_num at hz ⊢ <;> linarith [hz.1, hz.2]
  simpa [Beta0Affine.eval_p] using h z hz'

lemma beta0PolynomialX_lower :
    ∀ z ∈ Set.Icc (0 : ℝ) 1,
      (1 / 5 : ℝ) ≤ beta0PolynomialX z := by
  have h :=
    LeanCert.Validity.verify_lower_affine_cover
      Beta0Affine.x Beta0Affine.x_supported
      (1 / 5) Beta0Affine.cfg 0
      Beta0Affine.coarseBreakpoints Beta0Affine.coarseBreakpoints_ne
      Beta0Affine.x_lower_check
  rw [Beta0Affine.coarseBreakpoints_last] at h
  intro z hz
  by_cases hzsmall : z ≤ 3 / 1000
  · simp [beta0PolynomialX, beta0V, if_pos hzsmall]
    linarith [hz.1]
  · have hz' :
        z ∈ Set.Icc ((0 : ℚ) : ℝ) ((1 : ℚ) : ℝ) := by
      constructor <;> norm_num at hz ⊢ <;> linarith [hz.1, hz.2]
    simpa [Beta0Affine.eval_x, beta0PolynomialX, beta0V,
      if_neg hzsmall] using h z hz'

lemma beta0PolynomialBookMargin_pos :
    ∀ z ∈ Set.Ioc (0 : ℝ) 1,
      0 < beta0PolynomialBookMargin z := by
  have h₁ :=
    LeanCert.Validity.verify_lower_affine_cover
      Beta0Affine.book Beta0Affine.book_supported
      (1 / 10000000000) Beta0Affine.cfg (3 / 1000)
      Beta0Affine.bookBreakpoints₁ Beta0Affine.bookBreakpoints₁_ne
      Beta0Affine.book_check.1
  have h₂ :=
    LeanCert.Validity.verify_lower_affine_cover
      Beta0Affine.book Beta0Affine.book_supported
      (1 / 10000000000) Beta0Affine.cfg (1 / 10)
      Beta0Affine.bookBreakpoints₂ Beta0Affine.bookBreakpoints₂_ne
      Beta0Affine.book_check.2.1
  have h₃ :=
    LeanCert.Validity.verify_lower_affine_cover
      Beta0Affine.book Beta0Affine.book_supported
      (1 / 10000000000) Beta0Affine.cfg (1 / 2)
      Beta0Affine.bookBreakpoints₃ Beta0Affine.bookBreakpoints₃_ne
      Beta0Affine.book_check.2.2
  rw [Beta0Affine.bookBreakpoints₁_last] at h₁
  rw [Beta0Affine.bookBreakpoints₂_last] at h₂
  rw [Beta0Affine.bookBreakpoints₃_last] at h₃
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
  · have hzcut : ¬z ≤ 3 / 1000 := h₀z
    have hh := h₁ z (by
      constructor <;> norm_num at h₀z h₁z ⊢ <;> linarith)
    rw [Beta0Affine.eval_book] at hh
    have hmargin :
        (1 / 10000000000 : ℝ) ≤ beta0PolynomialBookMargin z := by
      simpa [beta0PolynomialBookMargin, beta0PolynomialX, beta0V,
        if_neg hzcut] using hh
    positivity
  by_cases h₂z : z ≤ 1 / 2
  · have hzcut : ¬z ≤ 3 / 1000 := by
      linarith
    have hh := h₂ z (by
      constructor <;> norm_num at h₁z h₂z ⊢ <;> linarith)
    rw [Beta0Affine.eval_book] at hh
    have hmargin :
        (1 / 10000000000 : ℝ) ≤ beta0PolynomialBookMargin z := by
      simpa [beta0PolynomialBookMargin, beta0PolynomialX, beta0V,
        if_neg hzcut] using hh
    positivity
  · have hzcut : ¬z ≤ 3 / 1000 := by
      linarith
    have hh := h₃ z (by
      constructor <;> norm_num at h₂z hz1 ⊢ <;> linarith)
    rw [Beta0Affine.eval_book] at hh
    have hmargin :
        (1 / 10000000000 : ℝ) ≤ beta0PolynomialBookMargin z := by
      simpa [beta0PolynomialBookMargin, beta0PolynomialX, beta0V,
        if_neg hzcut] using hh
    positivity

lemma beta0PolynomialBlueLogMargin_lower :
    ∀ z ∈ Set.Icc (0 : ℝ) 1,
      (1 / 100000 : ℝ) ≤ beta0PolynomialBlueLogMargin z := by
  have h :=
    LeanCert.Validity.verify_lower_affine_cover
      Beta0Affine.blue Beta0Affine.blue_supported
      (1 / 100000) Beta0Affine.cfg 0
      Beta0Affine.zeroBreakpoints Beta0Affine.zeroBreakpoints_ne
      Beta0Affine.blue_check
  rw [Beta0Affine.zeroBreakpoints_last] at h
  intro z hz
  have hz' :
      z ∈ Set.Icc ((0 : ℚ) : ℝ) ((1 : ℚ) : ℝ) := by
    constructor <;> norm_num at hz ⊢ <;> linarith [hz.1, hz.2]
  simpa [Beta0Affine.eval_blue] using h z hz'

lemma beta0PolynomialLimitLogMargin_pos :
    ∀ z ∈ Set.Ioc (0 : ℝ) 1,
      0 < beta0PolynomialLimitLogMargin z := by
  have h₁ :=
    LeanCert.Validity.verify_lower_affine_cover
      Beta0Affine.limit Beta0Affine.limit_supported
      (1 / 10000000000) Beta0Affine.cfg (3 / 1000)
      Beta0Affine.positiveBreakpoints Beta0Affine.positiveBreakpoints_ne
      Beta0Affine.limit_check
  rw [Beta0Affine.positiveBreakpoints_last] at h₁
  intro z hz
  by_cases hzsmall : z ≤ 3 / 1000
  · exact beta0PolynomialLimitLogMargin_small_pos ⟨hz.1, hzsmall⟩
  · have hzcut : ¬z ≤ 3 / 1000 := hzsmall
    have hh := h₁ z (by
      constructor <;> norm_num at hz hzsmall ⊢ <;> linarith [hz.2])
    rw [Beta0Affine.eval_limit] at hh
    have hmargin :
        (1 / 10000000000 : ℝ) ≤ beta0PolynomialLimitLogMargin z := by
      simpa [beta0PolynomialLimitLogMargin, beta0PolynomialX, beta0V,
        if_neg hzcut] using hh
    positivity

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
