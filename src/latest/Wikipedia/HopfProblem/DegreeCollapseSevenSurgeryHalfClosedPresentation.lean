import Wikipedia.HopfProblem.DegreeCollapseNonnegativeSurgeryPair
import Wikipedia.HopfProblem.DegreeCollapseSevenSurgeryFramedFilling
import Wikipedia.SmoothSixDPoincare.FramedSurgeryBoundaryPair

/-!
# Exact closed-piece surgery on the original and new seven-dimensional halves

The old attaching piece and the whole closed new handle are positive.
The two exterior nonnegativity conditions agree by the actual time profile.
The native halves therefore retain a full closed surgery presentation with
the original attaching sphere and actual new belt sphere.
-/

noncomputable section

open Function Set Metric
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery.FramedAttachingProduct.UnitSurgery

open NoExoticSixSphere GLOrthonormalization
open Wikipedia.SmoothSixDPoincare PuncturedHandle

local instance : Fact (Module.finrank ℝ (Vector 4) = 3 + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 7) M] [CompactSpace M]
  [IsManifold (𝓡 7) ∞ M] [T2Space M] {e : EuclideanEmbedding 7 M}
  {a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel} {f : Sphere 3 → M}
  (A : FramedAttachingProduct e a f) (hR : A.radius = 2) (T : TimeData A)

theorem timeFunction_oldClosedOverlap (p : Sphere 3 × PuncturedBall (Vector 4)) :
    timeFunction A hR T (FramedSurgery.oldMap (E := Vector 4) (face A hR) 3
      (FramedSurgery.oldClosedOverlap (E := Vector 4) (face A hR) p)) = 1 := by
  change SurgeryTimeProfile.profile T.margin (T.time (A.tube (p.1, p.2.val))) = 1
  apply SurgeryTimeProfile.profile_eq_one T.margin_pos
  apply T.tube_time
  apply closedBall_subset_closedBall (show (1 : ℝ) ≤ A.radius by rw [hR]; norm_num)
  exact mem_closedBall_zero_iff.mpr p.2.property.2

theorem timeFunction_closedNewMap (p : FramedSurgery.ClosedNewFace (Vector 4) (Vector 4)) :
    timeFunction A hR T (FramedSurgery.closedNewMap (E := Vector 4) (face A hR) 3 p) = 1 := by
  by_cases hp : ‖p.1.val‖ < 1
  · have he := FramedSurgery.closedNewMap_open (E := Vector 4) (face A hR) 3
      (⟨p.1.val, mem_ball_zero_iff.mpr hp⟩, p.2)
    exact (congrArg (timeFunction A hR T) he).trans (timeFunction_new A hR T _)
  · have hn : ‖p.1.val‖ = 1 :=
      le_antisymm (mem_closedBall_zero_iff.mp p.1.property) (le_of_not_gt hp)
    let u : Sphere 3 := ⟨p.1.val, mem_sphere_zero_iff_norm.mpr hn⟩
    have he := FramedSurgery.closedNewMap_corner (E := Vector 4) (face A hR) 3 u p.2
    exact (congrArg (timeFunction A hR T) he).trans
      (timeFunction_oldClosedOverlap A hR T (u, PuncturedHandle.boundaryPoint p.2))

def closedBoundaryPair : SurgeryBoundaryPair (Vector 4) (Vector 4)
    (FramedSurgery.Exterior (E := Vector 4) (face A hR)) M (Target A hR) :=
  FramedSurgery.boundaryPair (E := Vector 4) (face A hR) 3

theorem closedBoundaryPair_oldPiece_positive (p : Sphere 3 × UnitBall (Vector 4)) :
    0 < T.time ((closedBoundaryPair A hR).oldPiece p) := by
  change 0 < T.time (A.tube ((FramedSurgery.oldFaceCoordinates (Vector 4) (Vector 4) p).1,
    (FramedSurgery.oldFaceCoordinates (Vector 4) (Vector 4) p).2.val))
  apply T.margin_pos.trans_le
  apply T.tube_time
  exact (closedBall_subset_closedBall (show (1 : ℝ) ≤ A.radius by rw [hR]; norm_num))
    (FramedSurgery.oldFaceCoordinates (Vector 4) (Vector 4) p).2.property

theorem closedBoundaryPair_newPiece_time (p : UnitBall (Vector 4) × Sphere 3) :
    timeFunction A hR T ((closedBoundaryPair A hR).newPiece p) = 1 :=
  timeFunction_closedNewMap A hR T (FramedSurgery.newFaceCoordinates (Vector 4) (Vector 4) p)

theorem closedBoundaryPair_exterior_time
    (p : FramedSurgery.Exterior (E := Vector 4) (face A hR)) :
    timeFunction A hR T ((closedBoundaryPair A hR).newExterior p) =
      SurgeryTimeProfile.profile T.margin (T.time ((closedBoundaryPair A hR).oldExterior p)) := rfl

abbrev OldPositiveHalf := {p : M // 0 ≤ T.time p}

def halfBoundaryPair : SurgeryBoundaryPair (Vector 4) (Vector 4)
    (NonnegativeSurgeryPair.Exterior (closedBoundaryPair A hR) T.time)
    (OldPositiveHalf A T) (PositiveHalf A hR T) :=
  NonnegativeSurgeryPair.pair (closedBoundaryPair A hR) T.time (timeFunction A hR T)
    T.smooth.continuous (fun p ↦ (closedBoundaryPair_oldPiece_positive A hR T p).le)
    (fun p ↦ by rw [closedBoundaryPair_newPiece_time]; norm_num)
    (fun p ↦ by
      rw [closedBoundaryPair_exterior_time]
      exact (SurgeryTimeProfile.profile_nonneg_iff T.margin_pos _).symm)

theorem halfBoundaryPair_attachingSphere (s : Sphere 3) :
    ((halfBoundaryPair A hR T).attachingSphere s).val = f s := by
  change A.tube (s, 0) = f s
  exact A.tube_core s

theorem halfBoundaryPair_beltSphere (s : Sphere 3) :
    ((halfBoundaryPair A hR T).beltSphere s).val =
      FramedSurgery.closedNewMap (E := Vector 4) (face A hR) 3 (⟨0, by simp⟩, s) := rfl

end Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery.FramedAttachingProduct.UnitSurgery
