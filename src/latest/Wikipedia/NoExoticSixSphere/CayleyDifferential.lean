import Wikipedia.NoExoticSixSphere.OrthogonalSmoothness

/-!
# The differential of Cayley coordinates at the identity

The numerator of the rational coordinate map vanishes at the identity. The
product rule therefore gives its differential without differentiating the
inverse factor explicitly.
-/

open scoped ContDiff

namespace NoExoticSixSphere.CayleyTransform

open GLOrthonormalization OrthogonalPaths

variable {n : ℕ}

theorem inverse_one_add_one :
    (1 + 1 : Vector n →L[ℝ] Vector n).inverse = (1 / 2 : ℝ) • 1 := by
  apply ContinuousLinearMap.ext
  intro x
  have h := (identity_mem_domain (n := n)).self_apply_inverse x
  change (1 + 1 : Vector n →L[ℝ] Vector n).inverse x +
    (1 + 1 : Vector n →L[ℝ] Vector n).inverse x = x at h
  have hh := congrArg (fun v : Vector n ↦ (1 / 2 : ℝ) • v) h
  simpa only [smul_add, ← add_smul, show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num,
    one_smul, smul_apply, one_apply_eq_self] using hh

theorem fraction_one : fraction (1 : Vector n →L[ℝ] Vector n) = 0 := by
  simp only [fraction, sub_self, ContinuousLinearMap.zero_comp]

theorem hasFDerivAt_fraction_one :
    HasFDerivAt (fraction (n := n))
      ((-(1 / 2) : ℝ) • (1 : (Vector n →L[ℝ] Vector n) →L[ℝ]
        (Vector n →L[ℝ] Vector n))) 1 := by
  have hm : HasFDerivAt (fun A : Vector n →L[ℝ] Vector n ↦ 1 - A)
      (-1 : (Vector n →L[ℝ] Vector n) →L[ℝ] (Vector n →L[ℝ] Vector n)) 1 :=
    (hasFDerivAt_id (𝕜 := ℝ) (1 : Vector n →L[ℝ] Vector n)).const_sub 1
  have hi : ContDiffAt ℝ ∞
      (fun A : Vector n →L[ℝ] Vector n ↦ (1 + A).inverse) 1 :=
    ContDiffAt.comp (f := fun A : Vector n →L[ℝ] Vector n ↦ 1 + A)
      (g := ContinuousLinearMap.inverse) 1
      (identity_mem_domain (n := n)).contDiffAt_map_inverse
      (contDiffAt_const.add contDiffAt_id)
  have hd := hm.clm_comp (hi.differentiableAt (by simp)).hasFDerivAt
  convert! hd using 1
  apply ContinuousLinearMap.ext
  intro A
  apply ContinuousLinearMap.ext
  intro x
  simp [inverse_one_add_one]

end NoExoticSixSphere.CayleyTransform
