import Wikipedia.NoExoticSixSphere.ManifoldRegularTimeClamp
import Wikipedia.NoExoticSixSphere.ManifoldPuncturedBoundaryMaps
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCircleHomotopy

/-!
# An actual retraction onto the punctured cylinder

Time clamping followed by finitely many actual chartwise radial pushes gives a
continuous retraction from the original parameter manifold with its intrinsic
singularities removed. It fixes the whole punctured cylinder, not just its
boundary. Thus inclusion of this cylinder is injective on actual integral
singular homology in every degree.
-/

noncomputable section

open Set Function Topology
open scoped Manifold ContDiff

namespace NoExoticSixSphere.SphereFamily.ParityBallSystem

open GLOrthonormalization
open Wikipedia.HopfProblem.SingularMayerVietoris
open Wikipedia.HopfProblem.PeriodTorusHigherHomology

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  {g : ℝ → Sphere 3 → M} (P : ParityBallSystem g)

def inclusionRegular : C(P.puncturedCylinder, RegularParameters g) where
  toFun y := ⟨y.val, fun hs ↦ y.property.2 (P.singular_subset_openHoles hs)⟩
  continuous_toFun := continuous_subtype_val.subtype_mk _

theorem exists_retraction : ∃ R : C(RegularParameters g, P.puncturedCylinder),
    R.comp P.inclusionRegular = ContinuousMap.id P.puncturedCylinder := by
  obtain ⟨r, hfix, havoid, htime⟩ := P.exists_push_all
  let f : C(RegularParameters g, RegularParameters g) := r.comp P.clampRegular
  have hf (y : RegularParameters g) : (f y).val ∈ P.puncturedCylinder :=
    ⟨⟨htime _ (P.clampRegular_mem_Icc y), mem_univ _⟩, havoid _⟩
  let R : C(RegularParameters g, P.puncturedCylinder) := {
    toFun y := ⟨(f y).val, hf y⟩
    continuous_toFun := (continuous_subtype_val.comp f.continuous).subtype_mk hf }
  refine ⟨R, ContinuousMap.ext (fun y ↦ ?_)⟩
  apply Subtype.ext
  change (r (P.clampRegular (P.inclusionRegular y))).val = y.val
  rw [P.clampRegular_fixed (P.inclusionRegular y) y.property.1.1,
    hfix (P.inclusionRegular y) y.property.2]
  rfl

theorem inclusionRegular_homology_injective (n : ℕ) :
    Injective (singularHomologyMap P.inclusionRegular n) := by
  obtain ⟨R, hR⟩ := P.exists_retraction
  have he : (singularHomologyMap R n).comp (singularHomologyMap P.inclusionRegular n) =
      LinearMap.id := by
    rw [← singularHomologyMap_comp, hR, singularHomologyMap_id]
  intro a b hab
  have h := congrArg (singularHomologyMap R n) hab
  change ((singularHomologyMap R n).comp (singularHomologyMap P.inclusionRegular n)) a =
    ((singularHomologyMap R n).comp (singularHomologyMap P.inclusionRegular n)) b at h
  simpa only [he, LinearMap.id_apply] using h

def regularSphereInclusion (i : BoundaryIndex g) : C(Sphere 3, RegularParameters g) :=
  P.inclusionRegular.comp (P.sphereInclusion i)

theorem retraction_sphereInclusion (R : C(RegularParameters g, P.puncturedCylinder))
    (hR : R.comp P.inclusionRegular = ContinuousMap.id P.puncturedCylinder)
    (i : BoundaryIndex g) : R.comp (P.regularSphereInclusion i) = P.sphereInclusion i := by
  change R.comp (P.inclusionRegular.comp (P.sphereInclusion i)) = _
  rw [← ContinuousMap.comp_assoc, hR]
  rfl

end NoExoticSixSphere.SphereFamily.ParityBallSystem
