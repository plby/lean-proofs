import Wikipedia.HopfProblem.DegreeCollapseSevenSurgeryNegativeHalf
import Wikipedia.HopfProblem.DegreeCollapseTimeCollarSplitting
import Wikipedia.HopfProblem.DegreeCollapseSevenSurgeryConnectivity
import Wikipedia.HopfProblem.DegreeCollapseIntegralSevenFourthHomology

/-!
# Recover finite closed homology after surgery on a free positive class

The negative half is unchanged by the actual surgery homeomorphism.
The preserved collar and actual half-sum map therefore give finite
target homology from finite new positive and old negative homology.
Closed integral duality then kills the actual new half's H4. Neither
finite old ambient H3 nor zero old positive-half H4 is assumed.
-/

noncomputable section

open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery.FramedAttachingProduct.UnitSurgery

open NoExoticSixSphere GLOrthonormalization SingularMayerVietoris

local instance : Fact (Module.finrank ℝ (Vector 7) = 7) := ⟨finrank_euclideanSpace_fin⟩

variable {M : Type} [TopologicalSpace M] [ChartedSpace (Vector 7) M] [CompactSpace M]
  [IsManifold (𝓡 7) ∞ M] [T2Space M] {e : EuclideanEmbedding 7 M}
  {a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel} {f : Sphere 3 → M}
  (A : FramedAttachingProduct e a f) (hR : A.radius = 2) (T : TimeData A)
  {B : Type} [TopologicalSpace B] (C : TimeCollar T.time B)

include C in
theorem target_homology_finite_of_collared_halves (k : ℕ)
    [Subsingleton (SingularHomology B k)] [Subsingleton (SingularHomology B (k + 1))]
    [Finite (SingularHomology (TimeCollar.NonnegativeHalf (fun p ↦ -T.time p)) (k + 1))]
    [Finite (SingularHomology (PositiveHalf A hR T) (k + 1))] :
    Finite (SingularHomology (Target A hR) (k + 1)) := by
  let : Finite (SingularHomology
      (TimeCollar.NonnegativeHalf (fun p ↦ -timeFunction A hR T p)) (k + 1)) :=
    negativeHalf_homology_finite A hR T (k + 1)
  exact Finite.of_surjective ((preservedTimeCollar A hR T C).halvesHomologySum (k + 1))
    ((preservedTimeCollar A hR T C).halvesHomologySum_bijective k).2

include C in
theorem positiveHalf_fourth_homology_of_collared_halves
    [SimplyConnectedSpace M] [Subsingleton (SingularHomology M 2)]
    [Subsingleton (SingularHomology B 2)] [Subsingleton (SingularHomology B 3)]
    [Subsingleton (SingularHomology B 4)]
    [Finite (SingularHomology (TimeCollar.NonnegativeHalf (fun p ↦ -T.time p)) 3)]
    [Finite (SingularHomology (PositiveHalf A hR T) 3)] :
    Subsingleton (SingularHomology (PositiveHalf A hR T) 4) := by
  let := targetChartedSpace A hR
  let := target_isManifold A hR
  let := compactSpace_target A hR
  let : SimplyConnectedSpace (Target A hR) := (target_simplyConnected_iff A hR).2 inferInstance
  let : Subsingleton (SingularHomology (Target A hR) 2) := target_second_homology A hR
  let : Finite (SingularHomology (Target A hR) 3) :=
    target_homology_finite_of_collared_halves A hR T C 2
  let : Subsingleton (SingularHomology (Target A hR) 4) :=
    IntegralSevenDuality.fourth_homology_subsingleton (E := Vector 7) (Target A hR)
  exact (preservedTimeCollar A hR T C).half_homology_subsingleton 4

end Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery.FramedAttachingProduct.UnitSurgery
