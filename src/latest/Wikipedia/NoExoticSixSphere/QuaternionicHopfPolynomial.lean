import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicFibration
import Wikipedia.NoExoticSixSphere.SphereCylinderVector

/-!
# The actual smooth quaternionic Hopf polynomial on the standard spheres

The map sends a quaternion pair (a,b) to
(normSq a - normSq b, 2 a conjugate(b)). Its norm identity gives a
genuine smooth map from the standard seven-sphere to the standard
four-sphere. Its native James--Hopf coordinate is not computed here.
-/

noncomputable section

open scoped Quaternion Manifold ContDiff

namespace NoExoticSixSphere.QuaternionicHopf

open Wikipedia.HomotopyGroupsOfSpheres.QuaternionicFibration

abbrev V (n : ℕ) := EuclideanSpace ℝ (Fin n)

local instance : StarModule ℝ ℍ where
  star_smul r q := by simp [Quaternion.star_smul]

def conjugation : ℍ →L[ℝ] ℍ := (starL' ℝ : ℍ ≃L[ℝ] ℍ).toContinuousLinearMap

def first : V 8 →L[ℝ] ℍ :=
  (WithLp.fstL 2 ℝ ℍ ℍ).comp planeCoordinates.symm.toContinuousLinearMap

def second : V 8 →L[ℝ] ℍ :=
  (WithLp.sndL 2 ℝ ℍ ℍ).comp planeCoordinates.symm.toContinuousLinearMap

theorem normSq_sum (x : V 8) : Quaternion.normSq (first x) + Quaternion.normSq (second x) =
    ‖x‖ ^ 2 := by
  have h := norm_sq_plane (planeCoordinates.symm x)
  rw [planeCoordinates.symm.norm_map] at h
  exact h.symm

def polynomial (x : V 8) : V 5 :=
  SphereCylinder.join 3 (Quaternion.normSq (first x) - Quaternion.normSq (second x),
    Quaternion.linearIsometryEquivTuple ((2 : ℝ) • (first x * star (second x))))

theorem norm_sq_eq_normSq (q : ℍ) : ‖q‖ ^ 2 = Quaternion.normSq q := by
  rw [Quaternion.normSq_eq_norm_mul_self, pow_two]

theorem polynomial_norm_sq (x : V 8) :
    ‖polynomial x‖ ^ 2 = (Quaternion.normSq (first x) + Quaternion.normSq (second x)) ^ 2 := by
  rw [polynomial, SphereCylinder.norm_join_sq, Quaternion.linearIsometryEquivTuple.norm_map,
    norm_sq_eq_normSq, Quaternion.normSq_smul, map_mul, Quaternion.normSq_star]
  ring

theorem polynomial_mem_sphere (x : Sphere 7) : polynomial x.val ∈ Sphere 4 := by
  rw [mem_sphere_zero_iff_norm]
  have h := polynomial_norm_sq x.val
  rw [normSq_sum, (mem_sphere_zero_iff_norm.mp x.property)] at h
  nlinarith [norm_nonneg (polynomial x.val)]

theorem contDiff_normSq : ContDiff ℝ ∞ (Quaternion.normSq : ℍ → ℝ) := by
  simpa only [norm_sq_eq_normSq] using (contDiff_norm_sq ℝ :
    ContDiff ℝ ∞ (fun q : ℍ ↦ ‖q‖ ^ 2))

theorem contDiff_polynomial : ContDiff ℝ ∞ polynomial := by
  have hc : ContDiff ℝ ∞ (fun x : V 8 ↦ star (second x)) :=
    conjugation.contDiff.comp second.contDiff
  have hm : ContDiff ℝ ∞ (fun x : V 8 ↦ (2 : ℝ) • (first x * star (second x))) :=
    (contDiff_const : ContDiff ℝ ∞ (fun _ : V 8 ↦ (2 : ℝ))).smul (first.contDiff.mul hc)
  exact (SphereCylinder.join 3).contDiff.comp
    (((contDiff_normSq.comp first.contDiff).sub (contDiff_normSq.comp second.contDiff)).prodMk
      (Quaternion.linearIsometryEquivTuple.contDiff.comp hm))

def sphereMap : C(Sphere 7, Sphere 4) :=
  ⟨fun x ↦ ⟨polynomial x.val, polynomial_mem_sphere x⟩,
    (contDiff_polynomial.continuous.comp continuous_subtype_val).subtype_mk _⟩

theorem sphereMap_val (x : Sphere 7) : (sphereMap x).val = polynomial x.val := rfl

theorem contMDiff_sphereMap : ContMDiff (𝓡 7) (𝓡 4) ∞ sphereMap := by
  let : Fact (Module.finrank ℝ (V 8) = 7 + 1) := ⟨finrank_euclideanSpace_fin⟩
  let : Fact (Module.finrank ℝ (V 5) = 4 + 1) := ⟨finrank_euclideanSpace_fin⟩
  exact (contDiff_polynomial.contMDiff.comp contMDiff_coe_sphere).codRestrict_sphere
    polynomial_mem_sphere

end NoExoticSixSphere.QuaternionicHopf
