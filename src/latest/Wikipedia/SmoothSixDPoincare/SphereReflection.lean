import Wikipedia.SmoothSixDPoincare.SuspensionReflection
import Wikipedia.HopfProblem.SphereHomologySuspension
import Wikipedia.NoExoticSixSphere.OrthogonalRotations
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

/-!
# First-coordinate reflection of the original Euclidean sphere

The actual orthogonal reflection has determinant minus one and is conjugate
to suspension-height reflection under the original latitude homeomorphism.
-/

noncomputable section

open Set ContinuousMap
open scoped unitInterval

namespace Wikipedia.SmoothSixDPoincare.SphereReflection

open Wikipedia.HopfProblem.SphereHomology Wikipedia.HopfProblem.CuspCentralHomology

def linearReflection (n : ℕ) :
    EuclideanSpace ℝ (Fin (n + 2)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n + 2)) :=
  (ℝ ∙ EuclideanSpace.single (0 : Fin (n + 2)) (1 : ℝ))ᗮ.reflection

theorem linearReflection_apply (n : ℕ) (y : EuclideanSpace ℝ (Fin (n + 2))) :
    linearReflection n y = y - (2 * y 0) • EuclideanSpace.single 0 (1 : ℝ) := by
  change NoExoticSixSphere.hyperplaneReflectionOperator
    (EuclideanSpace.single 0 (1 : ℝ)) y = _
  rw [NoExoticSixSphere.hyperplaneReflectionOperator_apply]
  simp only [PiLp.norm_single, norm_one, one_pow, inv_one, mul_one,
    EuclideanSpace.inner_single_left, map_one, one_mul]

theorem linearReflection_zero (n : ℕ) (y : EuclideanSpace ℝ (Fin (n + 2))) :
    linearReflection n y 0 = -y 0 := by
  rw [linearReflection_apply]
  change y 0 - (2 * y 0) * (EuclideanSpace.single 0 (1 : ℝ)) 0 = _
  simp
  ring

theorem linearReflection_succ (n : ℕ) (y : EuclideanSpace ℝ (Fin (n + 2)))
    (i : Fin (n + 1)) : linearReflection n y i.succ = y i.succ := by
  rw [linearReflection_apply]
  change y i.succ - (2 * y 0) * (EuclideanSpace.single 0 (1 : ℝ)) i.succ = _
  simp

theorem linearReflection_det (n : ℕ) : (linearReflection n).toLinearMap.det = -1 := by
  have hv : (EuclideanSpace.single (0 : Fin (n + 2)) (1 : ℝ)) ≠ 0 := by simp
  change LinearMap.det ((ℝ ∙ EuclideanSpace.single (0 : Fin (n + 2)) (1 : ℝ))ᗮ.reflection
    ).toLinearMap = _
  rw [Submodule.det_reflection, Submodule.orthogonal_orthogonal,
    finrank_span_singleton hv, pow_one]

def sphereMap (n : ℕ) : C(UnitSphere (n + 1), UnitSphere (n + 1)) where
  toFun x := ⟨linearReflection n x.val, by
    rw [Metric.mem_sphere, dist_zero_right, LinearIsometryEquiv.norm_map, unitSphere_norm]⟩
  continuous_toFun := ((linearReflection n).continuous.comp continuous_subtype_val).subtype_mk _

theorem height_symm (t : I) : Latitude.height (unitInterval.symm t) = -Latitude.height t := by
  simp only [Latitude.height, unitInterval.coe_symm_eq]
  ring

theorem radius_symm (t : I) : Latitude.radius (unitInterval.symm t) = Latitude.radius t := by
  simp only [Latitude.radius, height_symm, neg_sq]

theorem sphereMap_latitude (n : ℕ) (t : I) (x : UnitSphere n) :
    sphereMap n (Latitude.point n t x) = Latitude.point n (unitInterval.symm t) x := by
  apply Subtype.ext
  apply PiLp.ext
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · change linearReflection n (Latitude.vector n t x) 0 =
      Latitude.vector n (unitInterval.symm t) x 0
    rw [linearReflection_zero, Latitude.vector_zero, Latitude.vector_zero, height_symm]
  · change linearReflection n (Latitude.vector n t x) j.succ =
      Latitude.vector n (unitInterval.symm t) x j.succ
    rw [linearReflection_succ, Latitude.vector_succ, Latitude.vector_succ, radius_symm]

/-- The conjugacy uses the genuine latitude homeomorphism, not a chosen homology generator. -/
theorem sphereMap_suspension (n : ℕ) (x : Suspension (UnitSphere n)) :
    sphereMap n (suspensionSphereHomeomorph n x) =
      suspensionSphereHomeomorph n (SuspensionReflection.reflect x) := by
  obtain ⟨⟨t, u⟩, rfl⟩ := Suspension.mk_surjective x
  rw [suspensionSphereHomeomorph_mk, sphereMap_latitude,
    SuspensionReflection.reflect_mk, suspensionSphereHomeomorph_mk]

theorem sphereMap_comp_suspension (n : ℕ) :
    (sphereMap n).comp (suspensionSphereHomeomorph n).toHomotopyEquiv.toFun =
      (suspensionSphereHomeomorph n).toHomotopyEquiv.toFun.comp SuspensionReflection.reflect :=
  ContinuousMap.ext (sphereMap_suspension n)

end Wikipedia.SmoothSixDPoincare.SphereReflection
