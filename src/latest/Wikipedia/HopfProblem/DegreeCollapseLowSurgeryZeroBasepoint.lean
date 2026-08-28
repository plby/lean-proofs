import Wikipedia.HopfProblem.DegreeCollapseLowSurgeryHalfBoundaryPair
import Wikipedia.HopfProblem.DegreeCollapseLowSurgeryTimeCollar

/-!

# The original zero-boundary basepoint lies in the common surgery exterior

The original tube has strictly positive time, so every zero point lies
in the actual closed exterior. At a specified boundary point, the two
restricted exterior maps recover precisely the original collar point
and the preserved native collar point. This supplies the same boundary
marking at every step of a finite surgery sequence.
-/

noncomputable section

open Set Function Metric Topology
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.LowSurgery.FramedAttachingProduct.NativeSurgery

open NoExoticSixSphere GLOrthonormalization SurgeryPair

variable {d : ℕ} {M B : Type} [TopologicalSpace M] [ChartedSpace (Vector 7) M]
  [CompactSpace M] [IsManifold (𝓡 7) ∞ M] [TopologicalSpace B]
  {e : EuclideanEmbedding 7 M}
  {a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel}
  {f : NoExoticSixSphere.Sphere d → M} (A : FramedAttachingProduct e a f)
  (hR : A.radius = 2) (T : TimeData A)

omit [IsManifold (𝓡 7) ∞ M] in
theorem zero_mem_closedExterior {p : M} (hp : T.time p = 0) : p ∈ closedExterior A := by
  rintro ⟨⟨s, v⟩, hv, he⟩
  have ht := T.tube_time s v
    (ball_subset_closedBall ((ball_subset_ball (oldRadius_lt A).le) hv.2))
  rw [he, hp] at ht
  exact (not_le_of_gt T.margin_pos) ht

def zeroHalfExteriorPoint (C : TimeCollar T.time B) (b : B) : HalfExterior A hR T :=
  ⟨⟨(C.zeroPoint b).val, zero_mem_closedExterior A T (C.zeroPoint_time b)⟩,
    (C.zeroPoint_time b).ge⟩

theorem oldExterior_zeroHalfExteriorPoint (C : TimeCollar T.time B) (b : B) :
    (halfBoundaryPair A hR T).oldExterior (zeroHalfExteriorPoint A hR T C b) =
      (⟨(C.zeroPoint b).val, (C.zeroPoint_time b).ge⟩ : OldPositiveHalf A T) := rfl

theorem newExterior_zeroHalfExteriorPoint (C : TimeCollar T.time B) (b : B) :
    (halfBoundaryPair A hR T).newExterior (zeroHalfExteriorPoint A hR T C b) =
      (⟨((preservedTimeCollar A hR T C).zeroPoint b).val,
        ((preservedTimeCollar A hR T C).zeroPoint_time b).ge⟩ : PositiveHalf A hR T) := by
  apply Subtype.ext
  rfl

end Wikipedia.HopfProblem.DegreeCollapse.LowSurgery.FramedAttachingProduct.NativeSurgery
