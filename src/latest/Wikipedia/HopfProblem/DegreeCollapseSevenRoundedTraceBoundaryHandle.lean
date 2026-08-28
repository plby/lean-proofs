import Wikipedia.HopfProblem.DegreeCollapseSevenRoundedTraceExteriorWindow
import Wikipedia.HopfProblem.DegreeCollapseEightDimensionalHandleZeroCoordinates

/-!
# The actual handle boundary piece is an open four-ball times a three-sphere

Its zero-fiber atlas is the one used in the native global boundary. Restrict
the explicit sphere coordinates to the exact smaller-ball window and retain
the actual attaching-product map into the ambient Euclidean space.
-/

noncomputable section

open Function Set Metric TopologicalSpace
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery.FramedAttachingProduct.RoundedTrace

open NoExoticSixSphere GLOrthonormalization Stiefel

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 7) M] [CompactSpace M]
  [IsManifold (𝓡 7) ∞ M] {e : EuclideanEmbedding 7 M}
  {a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel} {f : Sphere 3 → M}
  (A : FramedAttachingProduct e a f)

def boundaryHandleParameters : Opens (Vector 4 × Sphere 3) := by
  let := (handleZeroAtlas A).chartedSpace
  exact openDiffeomorphPreimage
    (EightDimensionalHandleSuperlevel.zeroDiffeomorph
      (UnroundedTrace.handleRadius_pos A) (pole 3) (handleZeroAtlas A))
    (OpenSuperlevelBoundary.zeroWindow
      (EightDimensionalHandleSuperlevel.level (UnroundedTrace.handleRadius A))
      (unchangedHandleWindow A))

omit [IsManifold (𝓡 7) ∞ M] in
theorem mem_boundaryHandleParameters_iff (p : Vector 4 × Sphere 3) :
    p ∈ boundaryHandleParameters A ↔ p.1 ∈ ball (0 : Vector 4) (handleCoreRadius A) := by
  let q : HandleSuperlevel A :=
    ⟨EightDimensionalHandleSuperlevel.zeroPoint (UnroundedTrace.handleRadius A) p,
      (EightDimensionalHandleSuperlevel.level_zeroPoint
        (UnroundedTrace.handleRadius_pos A) p).ge⟩
  exact mem_unchangedHandleWindow_iff A q

def boundaryHandleDiffeomorph : letI := boundaryPieceAtlas A .handle;
    boundaryHandleParameters A ≃ₘ⟮(𝓡 4).prod (𝓡 3), 𝓡 7⟯
      boundaryPieceDomain A .handle := by
  let := (handleZeroAtlas A).chartedSpace
  let := localBoundaryAtlas A .handle
  let := boundaryPieceAtlas A .handle
  let d := EightDimensionalHandleSuperlevel.zeroDiffeomorph
    (UnroundedTrace.handleRadius_pos A) (pole 3) (handleZeroAtlas A)
  let w := OpenSuperlevelBoundary.zeroWindow
    (EightDimensionalHandleSuperlevel.level (UnroundedTrace.handleRadius A))
    (unchangedHandleWindow A)
  let z : LocalBoundary A .handle ≃ₘ⟮𝓡 7, 𝓡 7⟯ w :=
    OpenSuperlevelBoundary.diffeomorph (handleLevelAtlas A) (unchangedHandleWindow A)
      (unchangedHandleHomeomorph A) (handleZeroAtlas A)
  exact ((openPreimageDiffeomorph d w).trans z.symm).trans
    (boundaryPieceDiffeomorph A .handle).symm

theorem boundaryHandleDiffeomorph_coordinates (p : boundaryHandleParameters A) :
    letI := boundaryPieceAtlas A .handle;
    handleBoundaryCoordinates A (boundaryHandleDiffeomorph A p) =
      (p.val.1, UnroundedTrace.handleRadius A • p.val.2.val) := by
  let := boundaryPieceAtlas A .handle
  change (unchangedHandleHomeomorph A
    ((unchangedHandleHomeomorph A).symm _)).val.val = _
  rw [Homeomorph.apply_symm_apply]
  rfl

theorem boundaryHandleDiffeomorph_ambient (p : boundaryHandleParameters A) :
    letI := boundaryPieceAtlas A .handle;
    (boundaryHandleDiffeomorph A p).val.val.val =
      A.map (p.val.1, UnroundedTrace.handleRadius A • p.val.2.val) := by
  let := boundaryPieceAtlas A .handle
  have h := unchangedHandleHomeomorph_ambient A
    (boundaryTracePoint A .handle (boundaryHandleDiffeomorph A p))
  change A.map (handleBoundaryCoordinates A (boundaryHandleDiffeomorph A p)) = _ at h
  rw [boundaryHandleDiffeomorph_coordinates] at h
  exact h.symm

omit [IsManifold (𝓡 7) ∞ M] in
def handleCoreBall : Opens (Vector 4) := ⟨ball 0 (handleCoreRadius A), isOpen_ball⟩

omit [IsManifold (𝓡 7) ∞ M] in
def boundaryHandleProductEquiv : boundaryHandleParameters A ≃ handleCoreBall A × Sphere 3 where
  toFun p := (⟨p.val.1, (mem_boundaryHandleParameters_iff A p.val).mp p.property⟩, p.val.2)
  invFun p := ⟨(p.1.val, p.2), (mem_boundaryHandleParameters_iff A _).mpr p.1.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

omit [IsManifold (𝓡 7) ∞ M] in
def boundaryHandleProductDiffeomorph : boundaryHandleParameters A ≃ₘ⟮(𝓡 4).prod (𝓡 3),
    (𝓡 4).prod (𝓡 3)⟯ handleCoreBall A × Sphere 3 := by
  refine
    { toEquiv := boundaryHandleProductEquiv A
      contMDiff_toFun := ?_
      contMDiff_invFun := ?_ }
  · have hv : ContMDiff ((𝓡 4).prod (𝓡 3)) ((𝓡 4).prod (𝓡 3)) ∞
        (Subtype.val : boundaryHandleParameters A → Vector 4 × Sphere 3) := contMDiff_subtype_val
    have hx : ContMDiff ((𝓡 4).prod (𝓡 3)) (𝓡 4) ∞
        (fun p : boundaryHandleParameters A ↦ (boundaryHandleProductEquiv A p).1) := by
      apply (ContMDiff.subtypeVal_comp_iff (handleCoreBall A) _).mp
      exact contMDiff_fst.comp hv
    exact hx.prodMk (contMDiff_snd.comp hv)
  · apply (ContMDiff.subtypeVal_comp_iff (boundaryHandleParameters A) _).mp
    exact (contMDiff_subtype_val.comp contMDiff_fst).prodMk contMDiff_snd

end Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery.FramedAttachingProduct.RoundedTrace
