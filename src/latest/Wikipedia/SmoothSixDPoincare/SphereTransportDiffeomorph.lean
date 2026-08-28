import Wikipedia.SmoothSixDPoincare.SpherePositiveTransport
import Wikipedia.SmoothSixDPoincare.LinearSphereHomology

/-!
# The actual positive sphere transport is smooth and acts trivially on homology

Restrict the constructed determinant-one linear isometry to the original
unit sphere. Its native smoothness comes from the ambient linear map, and
the already-proved determinant-sign calculation gives its actual homology
action. No point-moving or homology-preservation assumption is introduced.
-/

noncomputable section

open Set Metric ContinuousMap
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.SpherePoint

open Wikipedia.HopfProblem.SphereHomology
  Wikipedia.HopfProblem.SingularMayerVietoris

section Restriction

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

def sphereHomeomorph (R : V ≃ₗᵢ[ℝ] V) : sphere (0 : V) 1 ≃ₜ sphere (0 : V) 1 :=
  R.toContinuousLinearEquiv.toHomeomorph.subtype (fun x => by
    simp only [mem_sphere_zero_iff_norm]
    change ‖x‖ = 1 ↔ ‖R x‖ = 1
    rw [R.norm_map])

theorem sphereHomeomorph_apply (R : V ≃ₗᵢ[ℝ] V) (x : sphere (0 : V) 1) :
    (sphereHomeomorph R x).val = R x.val := rfl

theorem sphereHomeomorph_eq_normalized (R : V ≃ₗᵢ[ℝ] V) :
    (sphereHomeomorph R).toHomotopyEquiv.toFun =
      LinearSphereAction.sphereMap R.toContinuousLinearEquiv.toContinuousLinearMap R.injective := by
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  change R x.val = ‖R x.val‖⁻¹ • R x.val
  rw [R.norm_map, mem_sphere_zero_iff_norm.mp x.property, inv_one, one_smul]

variable {n : ℕ} [Fact (Module.finrank ℝ V = n + 1)]

theorem contMDiff_sphereHomeomorph (R : V ≃ₗᵢ[ℝ] V) :
    ContMDiff (𝓡 n) (𝓡 n) ∞ (sphereHomeomorph R) := by
  have h : ContMDiff (𝓡 n) 𝓘(ℝ, V) ∞ (fun x : sphere (0 : V) 1 => R x.val) :=
    R.toContinuousLinearEquiv.toContinuousLinearMap.contDiff.contMDiff.comp
      (contMDiff_coe_sphere (m := ∞))
  exact h.codRestrict_sphere (n := n) (fun x => (sphereHomeomorph R x).property)

def sphereDiffeomorph (R : V ≃ₗᵢ[ℝ] V) :
    Diffeomorph (𝓡 n) (𝓡 n) (sphere (0 : V) 1) (sphere (0 : V) 1) ∞ where
  toEquiv := (sphereHomeomorph R).toEquiv
  contMDiff_toFun := contMDiff_sphereHomeomorph R
  contMDiff_invFun := contMDiff_sphereHomeomorph R.symm

end Restriction

theorem sphereHomeomorph_homology_of_det_pos (n : ℕ)
    (R : EuclideanSpace ℝ (Fin (n + 2)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n + 2)))
    (hR : 0 < R.toLinearMap.det) (k : ℕ) (a : SingularHomology (UnitSphere (n + 1)) k) :
    singularHomologyMap (sphereHomeomorph R).toHomotopyEquiv.toFun k a = a := by
  rw [sphereHomeomorph_eq_normalized]
  exact LinearSphereAction.homology_of_det_pos n R.toContinuousLinearEquiv hR k a

theorem positiveTransport_moves (n : ℕ) (v w : UnitSphere (n + 1)) :
    sphereHomeomorph (positiveTransport n v w) v = w :=
  Subtype.ext (positiveTransport_apply n v w)

theorem positiveTransport_homology (n : ℕ) (v w : UnitSphere (n + 1)) (k : ℕ)
    (a : SingularHomology (UnitSphere (n + 1)) k) :
    singularHomologyMap
      (sphereHomeomorph (positiveTransport n v w)).toHomotopyEquiv.toFun k a = a := by
  apply sphereHomeomorph_homology_of_det_pos n _ _ k a
  rw [positiveTransport_det]
  norm_num

end Wikipedia.SmoothSixDPoincare.SpherePoint
