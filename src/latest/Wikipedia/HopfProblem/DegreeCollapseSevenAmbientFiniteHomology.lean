import Wikipedia.HopfProblem.DegreeCollapseSurgeryPairFiniteHomology
import Wikipedia.HopfProblem.DegreeCollapseSevenSurgeryConnectivity

/-!
# Finite new half homology gives finite new closed ambient homology

The original new belt sphere factors through the actual positive half.
Finite H3 of that half makes its image in the closed new manifold finite.
The original closed endpoint sequences then transfer old ambient H3
finiteness to the actual new ambient manifold.
-/

noncomputable section

open Function
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery.FramedAttachingProduct.UnitSurgery

open NoExoticSixSphere GLOrthonormalization
open SingularMayerVietoris SphereHomology PeriodTorusHigherHomology

variable {M : Type} [TopologicalSpace M] [ChartedSpace (Vector 7) M] [CompactSpace M]
  [IsManifold (𝓡 7) ∞ M] [T2Space M] {e : EuclideanEmbedding 7 M}
  {a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel} {f : Sphere 3 → M}
  (A : FramedAttachingProduct e a f) (hR : A.radius = 2) (T : TimeData A)

local instance : CompactSpace (Target A hR) := compactSpace_target A hR
local instance : CompactSpace (PositiveHalf A hR T) := compactSpace_positiveHalf A hR T

def newHalfToClosed : C(PositiveHalf A hR T, Target A hR) := ⟨Subtype.val, continuous_subtype_val⟩

theorem newHalfToClosed_belt : (newHalfToClosed A hR T).comp (halfBeltSphere A hR T) =
    (closedBoundaryPair A hR).beltSphere := by
  apply ContinuousMap.ext
  intro s
  rfl

theorem closedBelt_range_finite [Finite (SingularHomology (PositiveHalf A hR T) 3)] :
    Finite (LinearMap.range (singularHomologyMap (closedBoundaryPair A hR).beltSphere 3)) := by
  let u := singularHomologyMap (newHalfToClosed A hR T) 3
  let : Finite (LinearMap.range u) := Finite.of_surjective u.rangeRestrict (by
    rintro ⟨y, x, rfl⟩
    exact ⟨x, rfl⟩)
  have hc : singularHomologyMap (closedBoundaryPair A hR).beltSphere 3 =
      u.comp (singularHomologyMap (halfBeltSphere A hR T) 3) := by
    have he := singularHomologyMap_comp (halfBeltSphere A hR T) (newHalfToClosed A hR T) 3
    rw [newHalfToClosed_belt] at he
    exact he
  have hs : LinearMap.range (singularHomologyMap (closedBoundaryPair A hR).beltSphere 3) ≤
      LinearMap.range u := by
    rintro y ⟨x, hx⟩
    refine ⟨singularHomologyMap (halfBeltSphere A hR T) 3 x, ?_⟩
    exact (LinearMap.congr_fun hc x).symm.trans hx
  let inc : LinearMap.range (singularHomologyMap (closedBoundaryPair A hR).beltSphere 3) →
      LinearMap.range u := fun x ↦ ⟨x.val, hs x.property⟩
  apply Finite.of_injective inc
  intro x y he
  apply Subtype.ext
  exact congrArg (fun z : LinearMap.range u ↦ z.val) he

theorem target_third_finite_of_half [Finite (SingularHomology M 3)]
    [Finite (SingularHomology (PositiveHalf A hR T) 3)] :
    Finite (SingularHomology (Target A hR) 3) := by
  let : Finite (LinearMap.range (singularHomologyMap (closedBoundaryPair A hR).beltSphere 3)) :=
    closedBelt_range_finite A hR T
  let : Subsingleton (SingularHomology
      (Wikipedia.SmoothSixDPoincare.PuncturedHandle.UnitSphere (Vector 4)) 2) :=
    unitSphere_homology_subsingleton 2 2 (by decide) (by decide)
  exact SurgeryPairBody.new_homology_finite (closedBoundaryPair A hR) 2

end Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery.FramedAttachingProduct.UnitSurgery
