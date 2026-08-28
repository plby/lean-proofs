import Wikipedia.NoExoticSixSphere.StereographicTargetDifferential
import Wikipedia.NoExoticSixSphere.StabilizedPairSphereCoordinates
import Mathlib.Analysis.InnerProductSpace.ProdL2

/-!
# The actual ambient coordinates after stereographic stabilization

The added real coordinate is sent to the original source pole, while
the other coordinates use the original pole-complement orthonormal basis.
The ordinary product has a continuous linear equivalence; its L2 version
has a linear isometry equivalence. The compactification order is retained.
-/

noncomputable section

namespace NoExoticSixSphere.StereographicEquator

theorem lift_project_decomposition (n : ℕ) (x : V (n + 1)) :
    lift n (project n x) + (inner ℝ (spherePole n).val x) • (spherePole n).val = x := by
  have horth : inner ℝ (spherePole n).val
      (x - (inner ℝ (spherePole n).val x) • (spherePole n).val) = 0 := by
    rw [inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq,
      mem_sphere_zero_iff_norm.mp (spherePole n).property]
    ring
  have h := lift_project_of_orthogonal n _ horth
  rw [map_sub, map_smul, project_pole, smul_zero, sub_zero] at h
  rw [h, sub_add_cancel]

def stabilizedForward (n : ℕ) : (V n × ℝ) →L[ℝ] V (n + 1) :=
  (liftL n).comp (ContinuousLinearMap.fst ℝ (V n) ℝ) +
    (ContinuousLinearMap.toSpanSingleton ℝ (spherePole n).val).comp
      (ContinuousLinearMap.snd ℝ (V n) ℝ)

theorem stabilizedForward_apply (n : ℕ) (p : V n × ℝ) :
    stabilizedForward n p = lift n p.1 + p.2 • (spherePole n).val := rfl

def stabilizedBackward (n : ℕ) : V (n + 1) →L[ℝ] (V n × ℝ) :=
  (project n).prod (innerSL ℝ (spherePole n).val)

theorem stabilizedBackward_apply (n : ℕ) (x : V (n + 1)) :
    stabilizedBackward n x = (project n x, inner ℝ (spherePole n).val x) := rfl

theorem stabilizedBackward_forward (n : ℕ) (p : V n × ℝ) :
    stabilizedBackward n (stabilizedForward n p) = p := by
  rw [stabilizedBackward_apply, stabilizedForward_apply]
  apply Prod.ext
  · rw [map_add, project_lift, map_smul, project_pole, smul_zero, add_zero]
  · change inner ℝ (spherePole n).val (lift n p.1 + p.2 • (spherePole n).val) = p.2
    have hp : inner ℝ (spherePole n).val (lift n p.1) = 0 := by
      rw [real_inner_comm]
      exact inner_lift_pole n p.1
    rw [inner_add_right, hp, real_inner_smul_right, real_inner_self_eq_norm_sq,
      mem_sphere_zero_iff_norm.mp (spherePole n).property]
    ring

theorem stabilizedForward_backward (n : ℕ) (x : V (n + 1)) :
    stabilizedForward n (stabilizedBackward n x) = x := by
  change lift n (project n x) + (inner ℝ (spherePole n).val x) • (spherePole n).val = x
  exact lift_project_decomposition n x

def stabilizedEquiv (n : ℕ) : (V n × ℝ) ≃L[ℝ] V (n + 1) :=
  ContinuousLinearEquiv.equivOfInverse (stabilizedForward n) (stabilizedBackward n)
    (stabilizedBackward_forward n) (stabilizedForward_backward n)

theorem stabilizedEquiv_apply (n : ℕ) (p : V n × ℝ) :
    stabilizedEquiv n p = lift n p.1 + p.2 • (spherePole n).val := rfl

theorem stabilizedEquiv_symm_apply (n : ℕ) (x : V (n + 1)) :
    (stabilizedEquiv n).symm x = (project n x, inner ℝ (spherePole n).val x) := rfl

theorem stabilizedEquiv_norm_sq (n : ℕ) (p : V n × ℝ) :
    ‖stabilizedEquiv n p‖ ^ 2 = ‖p.1‖ ^ 2 + ‖p.2‖ ^ 2 := by
  rw [stabilizedEquiv_apply, norm_add_sq_real, norm_lift, real_inner_smul_right,
    inner_lift_pole, norm_smul, mem_sphere_zero_iff_norm.mp (spherePole n).property]
  ring

def hilbertStabilizedEquiv (n : ℕ) : WithLp 2 (V n × ℝ) ≃ₗᵢ[ℝ] V (n + 1) where
  toLinearEquiv := ((WithLp.prodContinuousLinearEquiv 2 ℝ (V n) ℝ).trans
    (stabilizedEquiv n)).toLinearEquiv
  norm_map' p := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    change ‖stabilizedEquiv n (p.fst, p.snd)‖ ^ 2 = ‖p‖ ^ 2
    rw [stabilizedEquiv_norm_sq, WithLp.prod_norm_sq_eq_of_L2]

theorem hilbertStabilizedEquiv_apply (n : ℕ) (p : WithLp 2 (V n × ℝ)) :
    hilbertStabilizedEquiv n p = lift n p.fst + p.snd • (spherePole n).val := rfl

def stabilizedPairCoordinates (n : ℕ) :
    ((V n × ℝ) × (V n × ℝ)) ≃ₜ WithLp 2 (V (n + 1) × V (n + 1)) :=
  ((stabilizedEquiv n).prodCongr (stabilizedEquiv n)).toHomeomorph.trans
    (WithLp.prodContinuousLinearEquiv 2 ℝ (V (n + 1)) (V (n + 1))).symm.toHomeomorph

theorem stabilizedPairCoordinates_apply (n : ℕ) (p : (V n × ℝ) × (V n × ℝ)) :
    stabilizedPairCoordinates n p =
      WithLp.toLp 2 (stabilizedEquiv n p.1, stabilizedEquiv n p.2) := rfl

def stabilizedPairSphereHomeomorph (n : ℕ) :
    OnePoint (WithLp 2 (V (n + 1) × V (n + 1))) ≃ₜ Sphere ((n + 1) + (n + 1)) :=
  (stabilizedPairCoordinates n).symm.onePointCongr.trans
    (SuspensionProductComparison.productPairSphereHomeomorph n)

theorem stabilizedPairSphereHomeomorph_coordinates (n : ℕ)
    (z : OnePoint ((V n × ℝ) × (V n × ℝ))) :
    stabilizedPairSphereHomeomorph n ((stabilizedPairCoordinates n).onePointCongr z) =
      SuspensionProductComparison.productPairSphereHomeomorph n z := by
  change SuspensionProductComparison.productPairSphereHomeomorph n
    ((stabilizedPairCoordinates n).symm.onePointCongr
      ((stabilizedPairCoordinates n).onePointCongr z)) = _
  have h : (stabilizedPairCoordinates n).symm.onePointCongr =
      ((stabilizedPairCoordinates n).onePointCongr).symm := rfl
  rw [h, Homeomorph.symm_apply_apply]

end NoExoticSixSphere.StereographicEquator
