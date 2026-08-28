import Wikipedia.HopfProblem.DegreeCollapseSevenInducedEndNormalFraming
import Wikipedia.HopfProblem.DegreeCollapseSevenRoundedCollarZeroCoordinates
import Wikipedia.NoExoticSixSphere.OpenPreimageDiffeomorph

/-!
# Explicit coordinates on the actual rounded boundary collar

Restrict the sphere-product zero coordinates to the actual open transverse
and height window. The resulting diffeomorphism lands in the real collar
piece of the globally glued native boundary, retaining its ambient map.
-/

noncomputable section

open Function Set Metric Topology TopologicalSpace
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery.FramedAttachingProduct.RoundedTrace

open NoExoticSixSphere GLOrthonormalization Stiefel SevenRoundedHandleCorner SmoothCornerRounding

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 7) M] [CompactSpace M]
  [IsManifold (𝓡 7) ∞ M] {e : EuclideanEmbedding 7 M}
  {a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel} {f : Sphere 3 → M}
  (A : FramedAttachingProduct e a f)

def boundaryCollarParameters : Opens BoundaryParameters := by
  let := (collarZeroAtlas A).chartedSpace
  exact openDiffeomorphPreimage
    (collarZeroDiffeomorph (bump A) (UnroundedTrace.handleRadius_pos A) (pole 3)
      (collarZeroAtlas A))
    (OpenSuperlevelBoundary.zeroWindow
      (collarLevel (bump A) (UnroundedTrace.handleRadius A)) (collarWindow A))

omit [IsManifold (𝓡 7) ∞ M] in
theorem mem_boundaryCollarParameters_iff (p : BoundaryParameters) :
    p ∈ boundaryCollarParameters A ↔
      graphRadius (bump A) (UnroundedTrace.handleRadius A) p.2.2 < A.radius ∧
      graphHeight (bump A) p.2.2 ∈ Ioo (-collarHeight A) (collarHeight A) := by
  change (zeroPoint (bump A) (UnroundedTrace.handleRadius A) p.2).1 ∈
      ball (0 : Vector 4) A.radius ∧
      graphHeight (bump A) p.2.2 ∈ Ioo (-collarHeight A) (collarHeight A) ↔ _
  rw [mem_ball, dist_zero_right, norm_zeroPoint_fst]

def boundaryCollarDiffeomorph : letI := boundaryPieceAtlas A .collar;
    boundaryCollarParameters A ≃ₘ⟮boundaryParameterModel, 𝓡 7⟯
      boundaryPieceDomain A .collar := by
  let := (collarZeroAtlas A).chartedSpace
  let := localBoundaryAtlas A .collar
  let := boundaryPieceAtlas A .collar
  let d := collarZeroDiffeomorph (bump A) (UnroundedTrace.handleRadius_pos A) (pole 3)
    (collarZeroAtlas A)
  let w := OpenSuperlevelBoundary.zeroWindow
    (collarLevel (bump A) (UnroundedTrace.handleRadius A)) (collarWindow A)
  let z : LocalBoundary A .collar ≃ₘ⟮𝓡 7, 𝓡 7⟯ w :=
    OpenSuperlevelBoundary.diffeomorph (collarLevelAtlas A) (collarWindow A)
      (collarWindowHomeomorph A) (collarZeroAtlas A)
  exact ((openPreimageDiffeomorph d w).trans z.symm).trans
    (boundaryPieceDiffeomorph A .collar).symm

theorem boundaryCollarDiffeomorph_coordinates (p : boundaryCollarParameters A) :
    letI := boundaryPieceAtlas A .collar;
    collarBoundaryCoordinates A (boundaryCollarDiffeomorph A p) =
      collarZeroPoint (bump A) (UnroundedTrace.handleRadius A) p.val := by
  let := boundaryPieceAtlas A .collar
  change (collarWindowHomeomorph A
    ((collarWindowHomeomorph A).symm _)).val.val = _
  rw [Homeomorph.apply_symm_apply]
  rfl

theorem boundaryCollarDiffeomorph_ambient (p : boundaryCollarParameters A) :
    letI := boundaryPieceAtlas A .collar;
    (boundaryCollarDiffeomorph A p).val.val.val =
      A.collarSheet (collarZeroPoint (bump A) (UnroundedTrace.handleRadius A) p.val) := by
  let := boundaryPieceAtlas A .collar
  have h := collarHomeomorph_symm_ambient A
    (boundaryTracePoint A .collar (boundaryCollarDiffeomorph A p))
  change A.collarSheet (collarBoundaryCoordinates A (boundaryCollarDiffeomorph A p)) = _ at h
  rw [boundaryCollarDiffeomorph_coordinates] at h
  exact h.symm

end Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery.FramedAttachingProduct.RoundedTrace
