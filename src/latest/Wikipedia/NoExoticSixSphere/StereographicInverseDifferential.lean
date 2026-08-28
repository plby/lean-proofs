import Wikipedia.NoExoticSixSphere.StereographicEquatorCoordinates

/-!
# The actual inverse stereographic differential at the equator

Mathlib's stereographic convention sends twice a unit vector to the
equator. Differentiate the original inverse formula at that point,
retaining the pole and radial components and their signs.
-/

noncomputable section

open scoped ContDiff

namespace NoExoticSixSphere.StereographicEquator

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem stereoInvFunAux_fderiv_double (p x : E) (hx : ‖x‖ = 1) (w : E) :
    fderiv ℝ (stereoInvFunAux p) ((2 : ℝ) • x) w =
      (1 / 2 : ℝ) • (w - (inner ℝ x w) • x + (inner ℝ x w) • p) := by
  have hn : ‖(2 : ℝ) • x‖ ^ 2 = 4 := by
    rw [norm_smul, hx]
    norm_num
  have hN : HasFDerivAt (fun z : E ↦ ‖z‖ ^ 2) ((4 : ℝ) • innerSL ℝ x) ((2 : ℝ) • x) := by
    convert (hasStrictFDerivAt_norm_sq ((2 : ℝ) • x)).hasFDerivAt using 1
    apply ContinuousLinearMap.ext
    intro v
    simp only [smul_apply, innerSL_apply_apply, real_inner_smul_left,
      nsmul_eq_mul, Nat.cast_ofNat, smul_eq_mul]
    ring
  have hI := (hasFDerivAt_inv (show ‖(2 : ℝ) • x‖ ^ 2 + 4 ≠ 0 by rw [hn]; norm_num)).comp
    ((2 : ℝ) • x) (hN.add_const 4)
  have hA := ((hasFDerivAt_const (4 : ℝ) ((2 : ℝ) • x)).smul
    (hasFDerivAt_id ((2 : ℝ) • x))).add
      ((hN.sub_const 4).smul (hasFDerivAt_const p ((2 : ℝ) • x)))
  have h := hI.smul hA
  change HasFDerivAt (stereoInvFunAux p) _ ((2 : ℝ) • x) at h
  rw [h.fderiv]
  simp only [add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.id_apply,
    zero_apply, smul_apply, innerSL_apply_apply, hn]
  norm_num [hn, Function.comp_apply, Pi.add_apply, Pi.smul_apply, smul_smul]
  module

end NoExoticSixSphere.StereographicEquator
