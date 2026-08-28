import Wikipedia.NoExoticSixSphere.StereographicProjectionCoordinates

/-!
# Original target-chart differential at the antipode of the pole

At the antipode the chart's scalar factor is one and its transverse
coordinate is zero. The actual ambient derivative is therefore the
fixed orthogonal-coordinate projection, with no chosen derivative value.
-/

noncomputable section

open scoped ContDiff

namespace NoExoticSixSphere.StereographicEquator

theorem project_pole (n : ℕ) : project n (spherePole n).val = 0 := by
  change coordinates n ((ℝ ∙ (spherePole n).val)ᗮ.orthogonalProjectionOnto (spherePole n).val) = 0
  rw [Submodule.orthogonalProjectionOnto_orthogonalComplement_singleton_eq_zero, map_zero]

def ambientChart (n : ℕ) (x : V (n + 1)) : V n :=
  (2 / (1 - inner ℝ (spherePole n).val x)) • project n x

theorem ambientChart_sphere (n : ℕ) (x : Sphere n) :
    ambientChart n x.val = sphereProjection n x := (chart_formula n x).symm

theorem contDiffAt_ambientChart (n : ℕ) (x : V (n + 1))
    (hx : 1 - inner ℝ (spherePole n).val x ≠ 0) : ContDiffAt ℝ ∞ (ambientChart n) x :=
  (contDiffAt_const.div (contDiffAt_const.sub (innerSL ℝ (spherePole n).val).contDiff.contDiffAt)
    hx).smul (project n).contDiff.contDiffAt

theorem inner_pole_antipode (n : ℕ) :
    inner ℝ (spherePole n).val (-(spherePole n).val) = -1 := by
  rw [inner_neg_right, real_inner_self_eq_norm_sq]
  rw [mem_sphere_zero_iff_norm.mp (spherePole n).property]
  norm_num

theorem ambientChart_derivative_antipode (n : ℕ) :
    fderiv ℝ (ambientChart n) (-(spherePole n).val) = project n := by
  have hd : 1 - inner ℝ (spherePole n).val (-(spherePole n).val) ≠ 0 := by
    rw [inner_pole_antipode]
    norm_num
  have hs : ContDiffAt ℝ ∞ (fun x : V (n + 1) ↦
      (2 : ℝ) / (1 - inner ℝ (spherePole n).val x)) (-(spherePole n).val) :=
    contDiffAt_const.div
      (contDiffAt_const.sub (innerSL ℝ (spherePole n).val).contDiff.contDiffAt) hd
  have h := (hs.differentiableAt (by simp)).hasFDerivAt.smul (project n).hasFDerivAt
  change HasFDerivAt (ambientChart n) _ (-(spherePole n).val) at h
  apply ContinuousLinearMap.ext
  intro v
  rw [h.fderiv]
  simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply,
    inner_pole_antipode, map_neg, project_pole, neg_zero, smul_zero, add_zero]
  norm_num

end NoExoticSixSphere.StereographicEquator
