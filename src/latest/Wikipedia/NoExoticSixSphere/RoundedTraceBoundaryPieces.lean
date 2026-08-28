import Wikipedia.NoExoticSixSphere.RoundedTraceBoundaryLevels

/-!
# Six-dimensional atlases on an open cover of the native trace boundary

The original open trace pieces restrict to an actual open cover of its
native boundary. Reordering the subtype layers and using the proved local
diffeomorphism of each trace-piece inclusion identifies these with the
already constructed local boundaries.
-/

noncomputable section

open Function Set Topology TopologicalSpace
open scoped Manifold ContDiff

namespace NoExoticSixSphere.EuclideanEmbedding.FramedAttachingProduct.RoundedTrace

open GLOrthonormalization Stiefel

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M] [CompactSpace M]
  [IsManifold (𝓡 6) ∞ M] {e : EuclideanEmbedding 6 M}
  {a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel} {f : Sphere 3 → M}
  (A : FramedAttachingProduct e a f)

def boundaryPieceDomain (i : Piece) : Opens (Boundary A) :=
  ⟨Subtype.val ⁻¹' pieceDomain A i, (pieceDomain A i).isOpen.preimage continuous_subtype_val⟩

theorem boundaryPieceDomain_covers (p : Boundary A) : ∃ i, p ∈ boundaryPieceDomain A i :=
  pieceDomain_covers A p.val

def boundaryTracePoint (i : Piece) (p : boundaryPieceDomain A i) : pieceDomain A i :=
  ⟨p.val.val, p.property⟩

def boundaryPieceHomeomorph (i : Piece) : boundaryPieceDomain A i ≃ₜ LocalBoundary A i := by
  let := traceChartedSpace A
  let := pieceAtlas A i
  exact
    { toFun := fun p ↦ ⟨boundaryTracePoint A i p,
        ((openCover A).isBoundaryPoint_inclusion_iff i _).mpr p.val.property⟩
      invFun := fun p ↦ ⟨⟨p.val.val,
        ((openCover A).isBoundaryPoint_inclusion_iff i p.val).mp p.property⟩, p.val.property⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      continuous_toFun :=
        ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _).subtype_mk _
      continuous_invFun :=
        ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _).subtype_mk _ }

theorem boundaryPieceHomeomorph_val (i : Piece) (p : boundaryPieceDomain A i) :
    (boundaryPieceHomeomorph A i p).val = boundaryTracePoint A i p := rfl

@[instance_reducible]
def boundaryPieceAtlas (i : Piece) : ChartedSpace (Vector 6) (boundaryPieceDomain A i) := by
  let := localBoundaryAtlas A i
  exact ModelAtlasTransport.atlas (boundaryPieceHomeomorph A i)

theorem boundaryPiece_isManifold (i : Piece) : letI := boundaryPieceAtlas A i;
    IsManifold (𝓡 6) ∞ (boundaryPieceDomain A i) := by
  let := localBoundaryAtlas A i
  let := localBoundary_isManifold A i
  exact ModelAtlasTransport.isManifold (boundaryPieceHomeomorph A i) (𝓡 6)

def boundaryPieceDiffeomorph (i : Piece) : letI := localBoundaryAtlas A i;
    letI := boundaryPieceAtlas A i;
    boundaryPieceDomain A i ≃ₘ⟮𝓡 6, 𝓡 6⟯ LocalBoundary A i := by
  let := localBoundaryAtlas A i
  exact ModelAtlasTransport.diffeomorph (boundaryPieceHomeomorph A i) (𝓡 6)

theorem contMDiff_boundaryTracePoint (i : Piece) : letI := pieceAtlas A i;
    letI := boundaryPieceAtlas A i;
    ContMDiff (𝓡 6) (ProductHalfSpace.model (Vector 6)) ∞ (boundaryTracePoint A i) := by
  let := pieceAtlas A i
  let := localBoundaryAtlas A i
  let := boundaryPieceAtlas A i
  exact (localBoundary_contMDiff_inclusion A i).comp
    (boundaryPieceDiffeomorph A i).contMDiff_toFun

theorem boundaryPiece_contMDiff_trace (i : Piece) : letI := traceChartedSpace A;
    letI := boundaryPieceAtlas A i;
    ContMDiff (𝓡 6) (ProductHalfSpace.model (Vector 6)) ∞
      (fun p : boundaryPieceDomain A i ↦ p.val.val) := by
  let := traceChartedSpace A
  let := pieceAtlas A i
  let := boundaryPieceAtlas A i
  have hi : ContMDiff (ProductHalfSpace.model (Vector 6)) (ProductHalfSpace.model (Vector 6)) ∞
      (Subtype.val : pieceDomain A i → ambientSet A) := (openCover A).contMDiff_inclusion i
  exact hi.comp (contMDiff_boundaryTracePoint A i)

variable {B H P : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
  [TopologicalSpace H] {J : ModelWithCorners ℝ B H}
  [TopologicalSpace P] [ChartedSpace H P]

theorem contMDiff_boundaryPiece_iff_local (i : Piece) (g : P → boundaryPieceDomain A i) :
    letI := localBoundaryAtlas A i; letI := boundaryPieceAtlas A i;
    ContMDiff J (𝓡 6) ∞ g ↔ ContMDiff J (𝓡 6) ∞ (boundaryPieceHomeomorph A i ∘ g) := by
  let := localBoundaryAtlas A i
  let := boundaryPieceAtlas A i
  constructor
  · intro hg
    exact (boundaryPieceDiffeomorph A i).contMDiff_toFun.comp hg
  · intro hg
    have h := (boundaryPieceDiffeomorph A i).symm.contMDiff_toFun.comp hg
    change ContMDiff J (𝓡 6) ∞
      (fun y ↦ (boundaryPieceHomeomorph A i).symm (boundaryPieceHomeomorph A i (g y))) at h
    simpa only [Homeomorph.symm_apply_apply] using h

end NoExoticSixSphere.EuclideanEmbedding.FramedAttachingProduct.RoundedTrace
