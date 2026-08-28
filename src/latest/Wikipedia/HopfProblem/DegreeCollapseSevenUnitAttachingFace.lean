import Wikipedia.HopfProblem.DegreeCollapseSevenNormalizedFramedAttachingProduct
import Wikipedia.HopfProblem.DegreeCollapseSevenAttachingTubeCoordinates
import Wikipedia.SmoothSixDPoincare.FramedSurgerySmoothBoundary

/-!
# The original attaching tube supplies the existing canonical surgery construction

Its actual closed unit face is embedded and has the previously constructed
smooth tube chart. For normalized products the surgery radius is exactly
one, so both sides of the radial exchange use the same squared-radius
coordinate. The surgery boundary atlas is constructed independently of
the rounded trace; its identification with the trace end is still needed.
-/

noncomputable section

open Function Set Metric Topology
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery.FramedAttachingProduct

open NoExoticSixSphere GLOrthonormalization Stiefel
open Wikipedia.SmoothSixDPoincare

local instance : Fact (Module.finrank ℝ (Vector 4) = 3 + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 7) M]
  {e : EuclideanEmbedding 7 M}
  {a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel} {f : Sphere 3 → M}
  (A : FramedAttachingProduct e a f) (hR : 1 < A.radius)

def unitClosedFace : SmoothClosedFace (𝓡 3) (𝓡 7) (Sphere 3) (Vector 4) M := by
  have he := GeneralDiskThickening.restrict_closedProduct_embedding A.tube hR.le A.tube_embedded
  exact
    { map := ⟨fun p ↦ A.tube (p.1, p.2.val), he.continuous⟩
      closedEmbedding := he
      chart := A.tubeCoordinates
      source := fun p hp ↦ ⟨mem_univ _, (closedBall_subset_ball hR) hp.2⟩
      point := fun _ _ ↦ rfl }

theorem unitClosedFace_map (p : Sphere 3 × MorseHandle.UnitDisk (Vector 4)) :
    (A.unitClosedFace hR).map p = A.tube (p.1, p.2.val) := rfl

theorem unitClosedFace_core (s : Sphere 3) :
    (A.unitClosedFace hR).map (s, ⟨0, by simp⟩) = f s := A.tube_core s

theorem normalizedRadius_admits_unitFace : 1 < A.normalizedRadius.radius := by
  rw [A.normalizedRadius_radius]
  norm_num

variable [IsManifold (𝓡 7) ∞ M]

theorem nonempty_unitSurgeryBoundaryData :
    letI : T2Space M := e.closedEmbedding.isEmbedding.t2Space;
    Nonempty (FramedSurgery.SmoothBoundaryData (E := Vector 4) (F := Vector 4)
      (m := 3) (A.unitClosedFace hR) 3) := by
  let : T2Space M := e.closedEmbedding.isEmbedding.t2Space
  exact FramedSurgery.nonempty_smoothBoundaryData (E := Vector 4) (F := Vector 4)
    (m := 3) (A.unitClosedFace hR) 3

end Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery.FramedAttachingProduct
