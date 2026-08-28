import Wikipedia.HopfProblem.DegreeCollapseLowSurgeryHalfBoundaryPair
import Wikipedia.HopfProblem.DegreeCollapseTwoSpherePairSecondHomology

/-!

# Two-sphere surgery on the actual nonnegative half kills exactly its H2 class

Apply the common-body quotient to the already constructed restricted pair.
The attaching class is the class in the original nonnegative half, not its
image in the closed ambient manifold. No homological vanishing or simple
connectivity is assumed to construct the quotient map.
-/

noncomputable section

open Function Set
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.LowSurgery.FramedAttachingProduct.NativeSurgery

open NoExoticSixSphere GLOrthonormalization SingularMayerVietoris SphereHomology

namespace TwoSphereHalf

variable {M : Type} [TopologicalSpace M] [ChartedSpace (Vector 7) M]
  [CompactSpace M] [IsManifold (𝓡 7) ∞ M] {e : EuclideanEmbedding 7 M}
  {a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel}
  {f : Sphere 2 → M} (A : FramedAttachingProduct e a f) (hR : A.radius = 2) (T : TimeData A)

local instance : CompactSpace (OldPositiveHalf A T) := compactSpace_oldPositiveHalf A T
local instance : CompactSpace (PositiveHalf A hR T) := compactSpace_positiveHalf A hR T

theorem positiveHalf_simplyConnected_iff :
    SimplyConnectedSpace (PositiveHalf A hR T) ↔ SimplyConnectedSpace (OldPositiveHalf A T) := by
  let := e.closedEmbedding.isEmbedding.t2Space
  exact SurgeryPairBody.TwoSphere.simplyConnected_iff (halfBoundaryPair A hR T)

def attachingClass : SingularHomology (OldPositiveHalf A T) 2 :=
  SurgeryPairBody.TwoSphere.attachingClass (halfBoundaryPair A hR T)

theorem attachingClass_eq : attachingClass A hR T =
    singularHomologyMap (halfBoundaryPair A hR T).attachingSphere 2 (unitSphereTopClass 1) := rfl

variable [T2Space M]

def secondHomologyMap :
    SingularHomology (OldPositiveHalf A T) 2 →ₗ[ℤ] SingularHomology (PositiveHalf A hR T) 2 :=
  SurgeryPairBody.TwoSphere.secondHomologyMap (halfBoundaryPair A hR T)

theorem secondHomologyMap_surjective : Surjective (secondHomologyMap A hR T) :=
  SurgeryPairBody.TwoSphere.secondHomologyMap_surjective (halfBoundaryPair A hR T)

theorem secondHomologyMap_ker :
    LinearMap.ker (secondHomologyMap A hR T) = Submodule.span ℤ {attachingClass A hR T} :=
  SurgeryPairBody.TwoSphere.secondHomologyMap_ker (halfBoundaryPair A hR T)

theorem secondHomologyMap_attachingClass :
    secondHomologyMap A hR T (attachingClass A hR T) = 0 :=
  SurgeryPairBody.TwoSphere.secondHomologyMap_attachingClass (halfBoundaryPair A hR T)

def secondHomologyQuotient :
    (SingularHomology (OldPositiveHalf A T) 2 ⧸ Submodule.span ℤ {attachingClass A hR T}) ≃ₗ[ℤ]
      SingularHomology (PositiveHalf A hR T) 2 :=
  SurgeryPairBody.TwoSphere.secondHomologyQuotient (halfBoundaryPair A hR T)

theorem secondHomologyQuotient_mk (x : SingularHomology (OldPositiveHalf A T) 2) :
    secondHomologyQuotient A hR T (Submodule.Quotient.mk x) = secondHomologyMap A hR T x :=
  SurgeryPairBody.TwoSphere.secondHomologyQuotient_mk (halfBoundaryPair A hR T) x

omit [T2Space M] in
theorem positiveHalf_secondHomology_of_span_top
    (h : Submodule.span ℤ {attachingClass A hR T} = ⊤) :
    Subsingleton (SingularHomology (PositiveHalf A hR T) 2) := by
  let := e.closedEmbedding.isEmbedding.t2Space
  exact SurgeryPairBody.TwoSphere.target_secondHomology_of_span_top (halfBoundaryPair A hR T) h

omit [T2Space M] in
theorem exists_secondHomologyQuotient :
    ∃ φ : SingularHomology (OldPositiveHalf A T) 2 →ₗ[ℤ]
      SingularHomology (PositiveHalf A hR T) 2,
      Surjective φ ∧ LinearMap.ker φ = Submodule.span ℤ {attachingClass A hR T} := by
  let := e.closedEmbedding.isEmbedding.t2Space
  exact ⟨secondHomologyMap A hR T, secondHomologyMap_surjective A hR T,
    secondHomologyMap_ker A hR T⟩

end TwoSphereHalf
end Wikipedia.HopfProblem.DegreeCollapse.LowSurgery.FramedAttachingProduct.NativeSurgery
