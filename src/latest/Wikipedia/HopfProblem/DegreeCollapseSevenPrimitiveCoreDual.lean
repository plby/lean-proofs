import Wikipedia.HopfProblem.DegreeCollapseTimeCollarPrimitiveDual
import Wikipedia.HopfProblem.DegreeCollapseSevenCollaredRelativeComparison
import Wikipedia.HopfProblem.DegreeCollapseSevenMeridianLinking

/-!
# The actual primitive attaching core has an integral unit dual

The inverse of the original open-tube cap map normalizes a genuine
core-supported class so its absolute cap is exactly the original core.
Its relative exterior and half classes are the original pullbacks.
For a primitive half-core, ordinary integral duality and the actual
collar splitting give a half fourth-homology class evaluating to one.
No finiteness of third homology or vanishing of fourth homology is used.
-/

noncomputable section

open CategoryTheory Function Set
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery
namespace FramedAttachingProduct.UnitSurgery.ExteriorTwist

open NoExoticSixSphere GLOrthonormalization FirstHurewicz
open SingularMayerVietoris SingularCohomologyFree SphereHomology PeriodTorusHigherHomology

local instance : Fact (Module.finrank ℝ (Vector 7) = 7) := ⟨finrank_euclideanSpace_fin⟩
local instance : Fact (Module.finrank ℝ (Vector 7) = (4 + 2) + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

variable {M : Type} [TopologicalSpace M] [ChartedSpace (Vector 7) M] [CompactSpace M]
  [IsManifold (𝓡 7) ∞ M] [T2Space M] [SimplyConnectedSpace M] {e : EuclideanEmbedding 7 M}
  {a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel} {f : Sphere 3 → M}
  (A : FramedAttachingProduct e a f) (hA : A.radius = 2)

def coreThomClass : IntegralSupportedCohomology.Cohomology
    (IntegralTubeCore.coreSupport A.tubeOpen A.tubeProductHomeomorph : Set M) 4 :=
  (IntegralTubeCore.capEquiv (V := Vector 7) A.tubeOpen A.tubeProductHomeomorph).symm
    (IntegralTubeCore.coreClass A.tubeOpen A.tubeProductHomeomorph)

theorem coreThomClass_cap :
    IntegralTubeCore.capEquiv (V := Vector 7) A.tubeOpen A.tubeProductHomeomorph
      (coreThomClass A) = IntegralTubeCore.coreClass A.tubeOpen A.tubeProductHomeomorph :=
  (IntegralTubeCore.capEquiv (V := Vector 7) A.tubeOpen A.tubeProductHomeomorph).apply_symm_apply _

theorem coreThomClass_generates
    (b : IntegralSupportedCohomology.Cohomology
      (IntegralTubeCore.coreSupport A.tubeOpen A.tubeProductHomeomorph : Set M) 4) :
    ∃ k : ℤ, k • coreThomClass A = b := by
  let m := (IntegralTubeCore.capEquiv (V := Vector 7) A.tubeOpen A.tubeProductHomeomorph).trans
    (IntegralTubeCore.coreMarking A.tubeOpen A.tubeProductHomeomorph)
  have hm : m (coreThomClass A) = 1 := by
    change IntegralTubeCore.coreMarking A.tubeOpen A.tubeProductHomeomorph
      (IntegralTubeCore.capEquiv (V := Vector 7) A.tubeOpen A.tubeProductHomeomorph
        (coreThomClass A)) = 1
    rw [coreThomClass_cap, IntegralTubeCore.coreMarking_coreClass]
  refine ⟨m b, m.injective ?_⟩
  rw [map_zsmul, hm]
  simp only [zsmul_eq_mul, Int.cast_id, mul_one]

def coreThomAbsolute : SingularCohomology M 4 :=
  IntegralSupportedCohomology.toAbsolute
    (IntegralTubeCore.coreSupport A.tubeOpen A.tubeProductHomeomorph : Set M) 4 (coreThomClass A)

theorem coreThomAbsolute_cap :
    IntegralCompactSupportCap.absoluteDualityMap (E := Vector 7) 4 M 4 3 rfl
      (coreThomAbsolute A) =
    singularHomologyMap (closedBoundaryPair A hA).attachingSphere 3 (unitSphereTopClass 2) := by
  change IntegralCompactSupportCap.absoluteDualityMap (E := Vector 7) 4 M 4 3 rfl
    (IntegralSupportedCohomology.toAbsolute _ 4 (coreThomClass A)) = _
  rw [← IntegralTubeCore.capEquiv_inclusion, coreThomClass_cap]
  change singularHomologyMap (subtypeInclusion (A.tubeOpen : Set M)) 3
    (singularHomologyMap (IntegralTubeCore.coreInOpen A.tubeOpen A.tubeProductHomeomorph) 3
      (unitSphereTopClass 2)) = _
  rw [← LinearMap.comp_apply, ← singularHomologyMap_comp]
  have he : (subtypeInclusion (A.tubeOpen : Set M)).comp
      (IntegralTubeCore.coreInOpen A.tubeOpen A.tubeProductHomeomorph) =
      (closedBoundaryPair A hA).attachingSphere := by
    ext s
    exact (A.tubeProductHomeomorph_core s).trans (A.tube_core s).symm
  rw [he]

def coreThomExterior : RelativeIntegralCap.Cohomology (closedExteriorRange A hA) 4 :=
  coreToExterior A hA 4 (coreThomClass A)

theorem coreThomExterior_forget :
    (HomologicalComplex.homologyMap
      (RelativeIntegralCap.toAbsoluteMap (closedExteriorRange A hA)) 4).hom
      (coreThomExterior A hA) = coreThomAbsolute A :=
  RelativeIntegralCap.cohomologyForget_pullback_id (exteriorToCore_mapsTo A hA) 4 (coreThomClass A)

theorem coreThomExterior_generates
    (b : RelativeIntegralCap.Cohomology (closedExteriorRange A hA) 4) :
    ∃ k : ℤ, k • coreThomExterior A hA = b := by
  obtain ⟨c, rfl⟩ := (coreToExterior_bijective A hA 4).2 b
  obtain ⟨k, hk⟩ := coreThomClass_generates A c
  refine ⟨k, ?_⟩
  change k • coreToExterior A hA 4 (coreThomClass A) = coreToExterior A hA 4 c
  rw [← map_zsmul, hk]

variable (T : TimeData A)

def coreThomHalf : RelativeIntegralCap.Cohomology (halfExteriorRange A hA T) 4 :=
  halfToClosedCohomologyPullback A hA T 4 (coreThomExterior A hA)

theorem coreThomHalf_forget :
    (HomologicalComplex.homologyMap
      (RelativeIntegralCap.toAbsoluteMap (halfExteriorRange A hA T)) 4).hom
      (coreThomHalf A hA T) =
      singularCohomologyPullback (halfToClosed A T) 4 (coreThomAbsolute A) := by
  have he := RelativeIntegralCap.cohomologyForget_pullback (halfToClosed A T)
    (halfToClosed_mapsTo A hA T) 4 (coreThomExterior A hA)
  rw [coreThomExterior_forget] at he
  exact he

include hA in
theorem coreThomAbsolute_negative_zero :
    singularCohomologyPullback (TimeCollar.halfInclusion (fun p ↦ -T.time p)) 4
      (coreThomAbsolute A) = 0 := by
  apply TimeCollar.supported_pullback_negative_zero
    (IntegralTubeCore.coreSupport A.tubeOpen A.tubeProductHomeomorph : Set M) _ 4 (coreThomClass A)
  intro p hp
  rw [coreSupport_eq_attachingRange A hA] at hp
  obtain ⟨s, rfl⟩ := hp
  apply T.margin_pos.trans_le
  change T.margin ≤ T.time (A.tube (s, 0))
  exact T.tube_time s 0 (by rw [hA]; simp)

variable {B : Type} [TopologicalSpace B] (C : TimeCollar T.time B)

include C in
theorem coreThomHalf_generates
    (b : RelativeIntegralCap.Cohomology (halfExteriorRange A hA T) 4) :
    ∃ k : ℤ, k • coreThomHalf A hA T = b := by
  obtain ⟨c, rfl⟩ := (collaredHalfToClosedCohomologyPullback_bijective A hA T C).2 b
  obtain ⟨k, hk⟩ := coreThomExterior_generates A hA c
  refine ⟨k, ?_⟩
  change k • halfToClosedCohomologyPullback A hA T 4 (coreThomExterior A hA) =
    halfToClosedCohomologyPullback A hA T 4 c
  rw [← map_zsmul, hk]

include C in
theorem exists_primitive_core_unit_dual
    [Subsingleton (SingularHomology B 2)] [Subsingleton (SingularHomology B 3)]
    [Subsingleton (SingularHomology B 4)]
    (σ : SingularHomology (OldPositiveHalf A T) 3 →ₗ[ℤ] ℤ)
    (hσ : σ (singularHomologyMap (halfBoundaryPair A hA T).attachingSphere 3
      (unitSphereTopClass 2)) = 1) :
    ∃ z : SingularHomology (OldPositiveHalf A T) 4,
      singularEvaluation (OldPositiveHalf A T) 4
        ((HomologicalComplex.homologyMap
          (RelativeIntegralCap.toAbsoluteMap (halfExteriorRange A hA T)) 4).hom
          (coreThomHalf A hA T)) z = 1 := by
  obtain ⟨z, hz⟩ := C.exists_unit_half_dual_of_primitive (E := Vector 7) σ
    (singularHomologyMap (halfBoundaryPair A hA T).attachingSphere 3 (unitSphereTopClass 2)) hσ
    (coreThomAbsolute A) (coreThomAbsolute_negative_zero A hA T)
    ((coreThomAbsolute_cap A hA).trans (halfToClosed_attachingClass A hA T).symm)
  refine ⟨z, ?_⟩
  rw [coreThomHalf_forget]
  exact hz

end FramedAttachingProduct.UnitSurgery.ExteriorTwist
end Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery
