import Wikipedia.HopfProblem.HolomorphicDolbeaultThreeLocalIntegralBasic

/-!
# Coordinatewise Cauchy–Green solution and commutation identities

Uniform compact support is required only in the integrated coordinate.
The integral solves that coordinate and commutes with every other actual
antiholomorphic coordinate derivative.
-/

noncomputable section

open Complex Set MeasureTheory
open scoped ContDiff

namespace Wikipedia.HopfProblem.HolomorphicDolbeaultThree.Local

open PeriodTorusLineBundleClassification

/-- Smoothness in all three coordinates of the actual coordinate integral. -/
theorem contDiff_coordinateCauchy (i : Fin 3) {n : ℕ∞}
    {f : Coordinates → ℂ} {k : Set ℂ} (hf : ContDiff ℝ n f)
    (hk : IsCompact k) (hfk : ∀ q, q i ∉ k → f q = 0) :
    ContDiff ℝ n (coordinateCauchy i f) := by
  rw [coordinateCauchy_eq]
  exact (contDiff_cauchySecond (contDiff_splitFunction i hf) hk
    (splitFunction_support i hfk)).comp
      ((coordinateSplit i).toContinuousLinearMap.restrictScalars ℝ).contDiff

/-- Cauchy–Green in coordinate `i` solves the actual derivative in that
coordinate. -/
theorem coordinateDbar_coordinateCauchy (i : Fin 3)
    {f : Coordinates → ℂ} {k : Set ℂ} (hf : ContDiff ℝ ∞ f)
    (hk : IsCompact k) (hfk : ∀ q, q i ∉ k → f q = 0) (q : Coordinates) :
    coordinateDbar i (coordinateCauchy i f) q = f q := by
  have hF := contDiff_splitFunction i hf
  have hFk := splitFunction_support i hfk
  have hG := contDiff_cauchySecond hF hk hFk
  rw [coordinateCauchy_eq, coordinateDbar_comp_split i i
    ((hG.differentiable (by simp)) _), coordinateSplit_basis_self]
  rw [← Cauchy.lastDbar_eq_dbar ((hG.differentiable (by simp)) _)]
  rw [Cauchy.lastDbar_cauchySecond
    (hF.of_le (WithTop.coe_le_coe.mpr le_top)) hk hFk]
  exact splitFunction_split i f q

/-- Every other antiholomorphic coordinate derivative commutes with the
actual integral. -/
theorem coordinateDbar_coordinateCauchy_of_ne (i j : Fin 3) (h : j ≠ i)
    {f : Coordinates → ℂ} {k : Set ℂ} (hf : ContDiff ℝ ∞ f)
    (hk : IsCompact k) (hfk : ∀ q, q i ∉ k → f q = 0) (q : Coordinates) :
    coordinateDbar j (coordinateCauchy i f) q =
      coordinateCauchy i (coordinateDbar j f) q := by
  have hF := contDiff_splitFunction i hf
  have hFk := splitFunction_support i hfk
  have hG := contDiff_cauchySecond hF hk hFk
  rw [coordinateCauchy_eq i f, coordinateDbar_comp_split i j
    ((hG.differentiable (by simp)) _), coordinateSplit_basis_of_ne i j h]
  rw [← Cauchy.parameterDbar_eq_dbar]
  rw [Cauchy.parameterDbar_cauchySecond _
    (hF.of_le (WithTop.coe_le_coe.mpr le_top)) hk hFk]
  have he : Cauchy.parameterDbar (coordinateSplit i (basisVector j)).1
      (splitFunction i f) = splitFunction i (coordinateDbar j f) := by
    funext p
    exact parameterDbar_splitFunction i j h ((hf.differentiable (by simp)) _)
  rw [he, coordinateCauchy_eq]
  rfl

/-- Slice-wise vanishing in a different derivative is preserved by the
coordinate integral. -/
theorem coordinateDbar_coordinateCauchy_eq_zero (i j : Fin 3) (h : j ≠ i)
    {f : Coordinates → ℂ} {k : Set ℂ} (hf : ContDiff ℝ ∞ f)
    (hk : IsCompact k) (hfk : ∀ q, q i ∉ k → f q = 0) (q : Coordinates)
    (hd : ∀ z : ℂ, coordinateDbar j f (Function.update q i z) = 0) :
    coordinateDbar j (coordinateCauchy i f) q = 0 := by
  rw [coordinateDbar_coordinateCauchy_of_ne i j h hf hk hfk]
  simp only [coordinateCauchy, HolomorphicCousin.cauchyGreen, hd,
    mul_zero, integral_zero]

end Wikipedia.HopfProblem.HolomorphicDolbeaultThree.Local
