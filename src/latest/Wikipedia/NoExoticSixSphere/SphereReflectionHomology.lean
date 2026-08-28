import Wikipedia.NoExoticSixSphere.QuaternionSphereRotations
import Wikipedia.NoExoticSixSphere.QuaternionSphereHomology

/-!
# Actual third homology of the four-dimensional reflection family

The negative reflection family is conjugate to quaternion squaring and
therefore doubles actual third singular homology. Negating its target is a
homeomorphism. Consequently the positive reflection family has image exactly
the even integers under any integral homology marking, without choosing an
orientation or assuming a degree formula.
-/

noncomputable section

open scoped Quaternion

namespace NoExoticSixSphere

open Wikipedia.HopfProblem.SingularMayerVietoris
open Wikipedia.HopfProblem.PeriodTorusHigherHomology

namespace QuaternionSphere

theorem negative_homology (w : Space) (a : SingularHomology Space 3) :
    singularHomologyMap (SphereReflection.negative w) 3 a = a + a := by
  rw [negative_eq_conjugated_square, singularHomologyMap_comp, LinearMap.comp_apply,
    singularHomologyMap_comp, LinearMap.comp_apply, square_homology, map_add]
  have h := (homeomorphHomologyEquiv (unitSphereCongr (rightIsometry w)) 3).apply_symm_apply a
  exact congrArg₂ (· + ·) h h

end QuaternionSphere

namespace SphereReflection

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem negative_homology_of_quaternion_isometry (L : E ≃ₗᵢ[ℝ] ℍ)
    (w : UnitSphere E) (a : SingularHomology (UnitSphere E) 3) :
    singularHomologyMap (negative w) 3 a = a + a := by
  rw [negative_conjugacy L w, singularHomologyMap_comp, LinearMap.comp_apply,
    singularHomologyMap_comp, LinearMap.comp_apply, QuaternionSphere.negative_homology, map_add]
  have h := (homeomorphHomologyEquiv (unitSphereCongr L) 3).symm_apply_apply a
  exact congrArg₂ (· + ·) h h

def antipodalHomeomorph : UnitSphere E ≃ₜ UnitSphere E :=
  unitSphereCongr (LinearIsometryEquiv.neg ℝ)

def positive (w : UnitSphere E) : C(UnitSphere E, UnitSphere E) :=
  (antipodalHomeomorph (E := E) : C(UnitSphere E, UnitSphere E)).comp (negative w)

theorem positive_apply (w x : UnitSphere E) :
    (positive w x).val = w.val - (2 * inner ℝ x.val w.val) • x.val := by
  change -(negative w x).val = _
  rw [negative_apply, neg_sub]

theorem marked_positive_homology (L : E ≃ₗᵢ[ℝ] ℍ) (w : UnitSphere E)
    (e : SingularHomology (UnitSphere E) 3 ≃ₗ[ℤ] ℤ) (a : SingularHomology (UnitSphere E) 3) :
    e (singularHomologyMap (positive w) 3 a) =
      2 * e (homeomorphHomologyEquiv (antipodalHomeomorph (E := E)) 3 a) := by
  change e (singularHomologyMap
    ((antipodalHomeomorph (E := E) : C(UnitSphere E, UnitSphere E)).comp (negative w)) 3 a) = _
  rw [singularHomologyMap_comp, LinearMap.comp_apply,
    negative_homology_of_quaternion_isometry L w, map_add, map_add, two_mul]
  rfl

theorem positive_homology_range (L : E ≃ₗᵢ[ℝ] ℍ) (w : UnitSphere E)
    (e : SingularHomology (UnitSphere E) 3 ≃ₗ[ℤ] ℤ) :
    Set.range (fun a ↦ e (singularHomologyMap (positive w) 3 a)) =
      Set.range (fun z : ℤ ↦ 2 * z) := by
  ext z
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨e (homeomorphHomologyEquiv (antipodalHomeomorph (E := E)) 3 a),
      (marked_positive_homology L w e a).symm⟩
  · rintro ⟨b, rfl⟩
    let a := (homeomorphHomologyEquiv (antipodalHomeomorph (E := E)) 3).symm (e.symm b)
    refine ⟨a, ?_⟩
    change e (singularHomologyMap (positive w) 3 a) = 2 * b
    rw [marked_positive_homology L w e]
    change 2 * e (homeomorphHomologyEquiv (antipodalHomeomorph (E := E)) 3
      ((homeomorphHomologyEquiv (antipodalHomeomorph (E := E)) 3).symm (e.symm b))) = 2 * b
    rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

end SphereReflection

end NoExoticSixSphere
