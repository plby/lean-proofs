import Wikipedia.HopfProblem.DegreeCollapseLowSurgeryHalfBoundaryPair
import Wikipedia.HopfProblem.DegreeCollapseSurgeryPairFundamentalGroup
import Wikipedia.NoExoticSixSphere.Topology.SimplyConnectedSphere

/-!

# Circle surgery on the actual nonnegative half

The native restricted pair has attaching sphere S1 and opposite sphere
S5. Its original and new halves have the same path-connectedness status.
At every retained exterior point, the actual endpoint inclusions induce
a surjection whose kernel is exactly the normal closure of the original
attaching-circle homomorphism, with its basepoint moved along the given
path in the old half. No simple-connectivity assumption is imposed.
-/

noncomputable section

open Function Set FundamentalGroup
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.LowSurgery.FramedAttachingProduct.NativeSurgery

open NoExoticSixSphere GLOrthonormalization

namespace OneSphereHalf

variable {M : Type} [TopologicalSpace M] [ChartedSpace (Vector 7) M]
  [CompactSpace M] [IsManifold (𝓡 7) ∞ M] {e : EuclideanEmbedding 7 M}
  {a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel}
  {f : Sphere 1 → M} (A : FramedAttachingProduct e a f) (hR : A.radius = 2) (T : TimeData A)

local instance : CompactSpace (OldPositiveHalf A T) := compactSpace_oldPositiveHalf A T
local instance : CompactSpace (PositiveHalf A hR T) := compactSpace_positiveHalf A hR T
local instance : SimplyConnectedSpace (Sphere 5) := EuclideanSphere.simplyConnectedSpace 3

theorem positiveHalf_pathConnected_iff :
    PathConnectedSpace (PositiveHalf A hR T) ↔ PathConnectedSpace (OldPositiveHalf A T) := by
  let := e.closedEmbedding.isEmbedding.t2Space
  exact SurgeryPairBody.pathConnected_iff (halfBoundaryPair A hR T)

/-- Original attaching-circle loops, moved along an actual path in the old half. -/
def markedAttachingHom (r : HalfExterior A hR T) (u : Sphere 1)
    (p : Path ((halfBoundaryPair A hR T).attachingSphere u)
      ((halfBoundaryPair A hR T).oldExterior r)) :
    FundamentalGroup (Sphere 1) u →*
      FundamentalGroup (OldPositiveHalf A T) ((halfBoundaryPair A hR T).oldExterior r) :=
  (fundamentalGroupMulEquivOfPath p).toMonoidHom.comp
    (FundamentalGroup.map (halfBoundaryPair A hR T).attachingSphere u)

variable [PathConnectedSpace (OldPositiveHalf A T)] [T2Space M]

def fundamentalGroupMap (r : HalfExterior A hR T) :
    FundamentalGroup (OldPositiveHalf A T) ((halfBoundaryPair A hR T).oldExterior r) →*
      FundamentalGroup (PositiveHalf A hR T) ((halfBoundaryPair A hR T).newExterior r) :=
  SurgeryPairBody.fundamentalGroupMap (halfBoundaryPair A hR T) r

theorem fundamentalGroupMap_surjective (r : HalfExterior A hR T) :
    Surjective (fundamentalGroupMap A hR T r) :=
  SurgeryPairBody.fundamentalGroupMap_surjective (halfBoundaryPair A hR T) r

theorem fundamentalGroupMap_ker (r : HalfExterior A hR T) (u : Sphere 1)
    (p : Path ((halfBoundaryPair A hR T).attachingSphere u)
      ((halfBoundaryPair A hR T).oldExterior r)) :
    (fundamentalGroupMap A hR T r).ker =
      Subgroup.normalClosure (range (markedAttachingHom A hR T r u p)) :=
  SurgeryPairBody.fundamentalGroupMap_kernel_normalClosure (halfBoundaryPair A hR T) r u p

theorem fundamentalGroupMap_attaching (r : HalfExterior A hR T) (u : Sphere 1)
    (p : Path ((halfBoundaryPair A hR T).attachingSphere u)
      ((halfBoundaryPair A hR T).oldExterior r)) (g : FundamentalGroup (Sphere 1) u) :
    fundamentalGroupMap A hR T r (markedAttachingHom A hR T r u p g) = 1 := by
  change markedAttachingHom A hR T r u p g ∈ (fundamentalGroupMap A hR T r).ker
  rw [fundamentalGroupMap_ker A hR T r u p]
  exact Subgroup.subset_normalClosure ⟨g, rfl⟩

omit [T2Space M] in
theorem exists_fundamentalGroupQuotient (r : HalfExterior A hR T) (u : Sphere 1)
    (p : Path ((halfBoundaryPair A hR T).attachingSphere u)
      ((halfBoundaryPair A hR T).oldExterior r)) :
    ∃ φ : FundamentalGroup (OldPositiveHalf A T) ((halfBoundaryPair A hR T).oldExterior r) →*
        FundamentalGroup (PositiveHalf A hR T) ((halfBoundaryPair A hR T).newExterior r),
      Surjective φ ∧ φ.ker =
        Subgroup.normalClosure (range (markedAttachingHom A hR T r u p)) := by
  let := e.closedEmbedding.isEmbedding.t2Space
  exact ⟨fundamentalGroupMap A hR T r, fundamentalGroupMap_surjective A hR T r,
    fundamentalGroupMap_ker A hR T r u p⟩

end OneSphereHalf
end Wikipedia.HopfProblem.DegreeCollapse.LowSurgery.FramedAttachingProduct.NativeSurgery
