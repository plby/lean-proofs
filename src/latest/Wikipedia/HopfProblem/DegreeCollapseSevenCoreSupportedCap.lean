import Wikipedia.HopfProblem.DegreeCollapseSevenOpenTubeProduct
import Wikipedia.HopfProblem.DegreeCollapseSevenClosedRelativePair
import Wikipedia.HopfProblem.DegreeCollapseIntegralSurgeryComplementPair
import Wikipedia.HopfProblem.DegreeCollapseIntegralRelativeForgetNaturality

/-!
# Original cap of the actual exterior-pair generator

The original closed exterior retracts from the actual core complement.
Thus its original cohomology generator lifts uniquely to cohomology
supported on the original attaching core. Forgetting is unchanged.
The constructed original open tube and the proved integral unit cap
theorem then identify its cap with a unit times the actual attaching class.
-/

noncomputable section

open Function Set
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery
namespace FramedAttachingProduct.UnitSurgery.ExteriorTwist

open NoExoticSixSphere GLOrthonormalization FirstHurewicz
open SingularMayerVietoris SingularCohomologyFree SphereHomology

local instance : Fact (Module.finrank ℝ (Vector 7) = 7) := ⟨finrank_euclideanSpace_fin⟩
local instance : Fact (Module.finrank ℝ (Vector 7) = (4 + 2) + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

variable {M : Type} [TopologicalSpace M] [ChartedSpace (Vector 7) M] [CompactSpace M]
  [IsManifold (𝓡 7) ∞ M] [T2Space M] {e : EuclideanEmbedding 7 M}
  {a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel} {f : Sphere 3 → M}
  (A : FramedAttachingProduct e a f) (hA : A.radius = 2)

omit [IsManifold (𝓡 7) ∞ M] in
theorem coreSupport_eq_attachingRange :
    (IntegralTubeCore.coreSupport A.tubeOpen A.tubeProductHomeomorph : Set M) =
      range (closedBoundaryPair A hA).attachingSphere := by
  have hcore : (fun s ↦ (closedBoundaryPair A hA).attachingSphere s) = f := by
    funext s
    exact A.tube_core s
  exact A.originalTubeCoreSupport.trans (congrArg Set.range hcore).symm

omit [IsManifold (𝓡 7) ∞ M] in
theorem exteriorToCore_mapsTo :
    MapsTo (ContinuousMap.id M) (closedExteriorRange A hA)
      (IntegralTubeCore.coreSupport A.tubeOpen A.tubeProductHomeomorph : Set M)ᶜ := by
  rintro x ⟨r, rfl⟩
  rw [coreSupport_eq_attachingRange]
  exact (closedBoundaryPair A hA).oldExterior_avoids r

theorem exteriorToCore_bijective (k : ℕ) :
    Bijective (RelativeSingularHomology.map (ContinuousMap.id M)
      (exteriorToCore_mapsTo A hA) k) := by
  have transfer (V : Set M) (hV : V = (closedBoundaryPair A hA).OldComplement)
      (hf : MapsTo (ContinuousMap.id M) (closedExteriorRange A hA) V) :
      Bijective (RelativeSingularHomology.map (ContinuousMap.id M) hf k) := by
    subst V
    exact SurgeryExteriorRetraction.exteriorToComplement_bijective (closedBoundaryPair A hA) k
  exact transfer _ (congrArg Set.compl (coreSupport_eq_attachingRange A hA)) _

abbrev coreToExterior (p : ℕ) :
    IntegralSupportedCohomology.Cohomology
      (IntegralTubeCore.coreSupport A.tubeOpen A.tubeProductHomeomorph : Set M) p →ₗ[ℤ]
    RelativeIntegralCap.Cohomology (closedExteriorRange A hA) p :=
  RelativeIntegralCap.cohomologyPullback (ContinuousMap.id M) (exteriorToCore_mapsTo A hA) p

theorem coreToExterior_bijective (p : ℕ) : Bijective (coreToExterior A hA p) :=
  RelativeIntegralCap.cohomologyPullback_bijective_of_homology
    (ContinuousMap.id M) (exteriorToCore_mapsTo A hA) (exteriorToCore_bijective A hA) p

def liftExteriorClass (p : ℕ) (c : RelativeIntegralCap.Cohomology (closedExteriorRange A hA) p) :
    IntegralSupportedCohomology.Cohomology
      (IntegralTubeCore.coreSupport A.tubeOpen A.tubeProductHomeomorph : Set M) p :=
  (LinearEquiv.ofBijective (coreToExterior A hA p) (coreToExterior_bijective A hA p)).symm c

theorem liftExteriorClass_pullback (p : ℕ)
    (c : RelativeIntegralCap.Cohomology (closedExteriorRange A hA) p) :
    coreToExterior A hA p (liftExteriorClass A hA p c) = c := by
  let e := LinearEquiv.ofBijective (coreToExterior A hA p) (coreToExterior_bijective A hA p)
  exact e.apply_symm_apply c

theorem liftExteriorClass_forget (p : ℕ)
    (c : RelativeIntegralCap.Cohomology (closedExteriorRange A hA) p) :
    IntegralSupportedCohomology.toAbsolute
      (IntegralTubeCore.coreSupport A.tubeOpen A.tubeProductHomeomorph : Set M) p
      (liftExteriorClass A hA p c) =
    (HomologicalComplex.homologyMap
      (RelativeIntegralCap.toAbsoluteMap (closedExteriorRange A hA)) p).hom c := by
  have he := RelativeIntegralCap.cohomologyForget_pullback_id (exteriorToCore_mapsTo A hA) p
    (liftExteriorClass A hA p c)
  change (HomologicalComplex.homologyMap
    (RelativeIntegralCap.toAbsoluteMap (closedExteriorRange A hA)) p).hom
      (coreToExterior A hA p (liftExteriorClass A hA p c)) = _ at he
  rw [liftExteriorClass_pullback] at he
  exact he.symm

theorem liftExteriorClass_generates (p : ℕ)
    (c : RelativeIntegralCap.Cohomology (closedExteriorRange A hA) p)
    (hc : ∀ b : RelativeIntegralCap.Cohomology (closedExteriorRange A hA) p,
      ∃ k : ℤ, k • c = b)
    (b : IntegralSupportedCohomology.Cohomology
      (IntegralTubeCore.coreSupport A.tubeOpen A.tubeProductHomeomorph : Set M) p) :
    ∃ k : ℤ, k • liftExteriorClass A hA p c = b := by
  obtain ⟨k, hk⟩ := hc (coreToExterior A hA p b)
  refine ⟨k, (coreToExterior_bijective A hA p).1 ?_⟩
  rw [map_zsmul, liftExteriorClass_pullback]
  exact hk

variable [SimplyConnectedSpace M]

theorem exteriorGenerator_cap_unit
    (c : RelativeIntegralCap.Cohomology (closedExteriorRange A hA) 4)
    (hc : ∀ b : RelativeIntegralCap.Cohomology (closedExteriorRange A hA) 4,
      ∃ k : ℤ, k • c = b) :
    ∃ k : ℤ, IsUnit k ∧
      IntegralCompactSupportCap.absoluteDualityMap (E := Vector 7) 4 M 4 3 rfl
        ((HomologicalComplex.homologyMap
          (RelativeIntegralCap.toAbsoluteMap (closedExteriorRange A hA)) 4).hom c) =
      k • singularHomologyMap (closedBoundaryPair A hA).attachingSphere 3
        (unitSphereTopClass 2) := by
  obtain ⟨k, hk, he⟩ := IntegralTubeCore.absoluteCap_generator_unit (V := Vector 7)
    A.tubeOpen A.tubeProductHomeomorph (liftExteriorClass A hA 4 c)
    (liftExteriorClass_generates A hA 4 c hc)
  have hcore : ((IntegralTubeCore.tubeMap A.tubeOpen A.tubeProductHomeomorph).comp
      (SphereNormalHomology.zeroSection (Vector 4))) =
        (closedBoundaryPair A hA).attachingSphere := by
    apply ContinuousMap.ext
    intro s
    exact (A.tubeProductHomeomorph_core s).trans (A.tube_core s).symm
  rw [liftExteriorClass_forget, hcore] at he
  exact ⟨k, hk, he⟩

end FramedAttachingProduct.UnitSurgery.ExteriorTwist
end Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery
