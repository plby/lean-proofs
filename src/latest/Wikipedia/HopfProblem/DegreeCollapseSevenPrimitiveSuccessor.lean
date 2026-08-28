import Wikipedia.HopfProblem.DegreeCollapseTimeCollarPrimitiveSurgery

/-!
# The actual free first-surgery target admits the required primitive successor

Use the first target's native atlas, induced embedding, full normal frame,
regular time function, and preserved collar. The original finite ambient
homology gives finite negative-half homology, which the first surgery's
actual negative-half homeomorphism preserves. The intermediate positive
half and ambient space are allowed to have infinite third homology.
-/

noncomputable section

open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery.FramedAttachingProduct.UnitSurgery

open NoExoticSixSphere GLOrthonormalization SingularMayerVietoris

variable {M : Type} [TopologicalSpace M] [ChartedSpace (Vector 7) M] [CompactSpace M]
  [IsManifold (𝓡 7) ∞ M] [T2Space M] {e : EuclideanEmbedding 7 M}
  {a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel} {f : Sphere 3 → M}
  (A : FramedAttachingProduct e a f) (hA : A.radius = 2) (T : TimeData A)
  [SimplyConnectedSpace M] [Subsingleton (SingularHomology M 2)] [Finite (SingularHomology M 3)]
  [SimplyConnectedSpace (OldPositiveHalf A T)]
  {B : Type} [TopologicalSpace B] (C : TimeCollar T.time B)
  [Subsingleton (SingularHomology B 2)] [Subsingleton (SingularHomology B 3)]
  [Subsingleton (SingularHomology B 4)]

include C in
theorem primitive_reduction_after_free_coordinate
    (σ : SingularHomology (PositiveHalf A hA T) 3 →+ ℤ) [Finite σ.ker]
    (x : SingularHomology (PositiveHalf A hA T) 3) (hx : σ x = 1)
    (h2 : ∀ y : σ.ker, (2 : ℤ) • y = 0) :
    letI := targetChartedSpace A hA;
    letI := target_isManifold A hA;
    letI := compactSpace_target A hA;
    TimeCollar.HasPrimitiveReduction (inducedEmbedding A hA) (normalFraming A hA)
      (timeFunction A hA T) (Nat.card σ.ker) := by
  let := targetChartedSpace A hA
  let := target_isManifold A hA
  let := compactSpace_target A hA
  let : SimplyConnectedSpace (Target A hA) := (target_simplyConnected_iff A hA).2 inferInstance
  let : Subsingleton (SingularHomology (Target A hA) 2) := target_second_homology A hA
  let : SimplyConnectedSpace (PositiveHalf A hA T) := positiveHalf_simplyConnected A hA T
  let : Finite (SingularHomology (TimeCollar.NonnegativeHalf (fun p ↦ -T.time p)) 3) :=
    C.negative_homology_finite 3
  let : Finite (SingularHomology
      (TimeCollar.NonnegativeHalf (fun p ↦ -timeFunction A hA T p)) 3) :=
    negativeHalf_homology_finite A hA T 3
  exact (preservedTimeCollar A hA T C).primitiveReduction_of_coordinate
    (inducedEmbedding A hA) (normalFraming A hA) (contMDiff_timeFunction A hA T)
    (regular_timeFunction_zero A hA T) σ x hx h2

end Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery.FramedAttachingProduct.UnitSurgery
