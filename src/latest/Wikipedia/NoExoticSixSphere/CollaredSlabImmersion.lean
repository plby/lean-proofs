import Wikipedia.NoExoticSixSphere.CollaredSlabBoundary
import Wikipedia.NoExoticSixSphere.SlabBoundaryImmersion
import Wikipedia.NoExoticSixSphere.SlabInteriorImmersion
import Wikipedia.NoExoticSixSphere.SmoothOpenCoverImmersion

/-!
# The actual global collared slab is immersed in the original cylinder

The independently constructed left, interior, and right atlases all give
injective ambient differentials. Their inclusions into the glued atlas are
local diffeomorphisms, so injectivity holds on the whole slab, including its
boundary. This is the slab inclusion, not just the boundary inclusion.
-/

open scoped Manifold ContDiff
open Module Function

namespace NoExoticSixSphere.RegularCollaredCylinder

variable {B H M C H' N : Type*}
  [NormedAddCommGroup B] [NormedSpace ℝ B] [FiniteDimensional ℝ B] [TopologicalSpace H]
  {I : ModelWithCorners ℝ B H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [NormedAddCommGroup C] [NormedSpace ℝ C] [FiniteDimensional ℝ C] [TopologicalSpace H']
  {J : ModelWithCorners ℝ C H'} [J.Boundaryless]
  [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N]
  {b : N} {s t : ℝ} (d : RegularCollaredCylinder (M := M) I J b s t)
  (k : ℕ) (hd : finrank ℝ B = finrank ℝ C + k)
  (Φ : PartialDiffeomorph (𝓡 (k + 1)) ((𝓡∂ 1).prod (𝓡 k))
    (EuclideanSpace ℝ (Fin (k + 1)))
    (ModelProd (EuclideanHalfSpace 1) (EuclideanSpace ℝ (Fin k))) ∞)
  (hsource : Φ.source = Set.univ)

theorem piece_injective_mfderiv_ambient (i : Piece) (p : d.pieceDomain i) :
    letI := d.pieceAtlas k hd Φ hsource i;
    Injective (mfderiv ((𝓡∂ 1).prod (𝓡 k)) ((𝓘(ℝ, ℝ)).prod I)
      (fun q : d.pieceDomain i ↦ q.val.val.val) p) := by
  let : Fact (s < t) := ⟨d.time_lt⟩
  cases i with
  | left =>
      exact CylinderFiberSlab.boundaryAtlas_injective_mfderiv_ambient
        d.map d.leftMap d.smooth_left b d.regular_left k hd s t d.leftTimes d.left_eq p
  | middle =>
      exact CylinderFiberSlab.interiorAtlas_injective_mfderiv_ambient d.map d.smooth_map b
        d.regular_map (k + 1) (cylinder_finrank_eq hd) s t Φ hsource p
  | right =>
      exact CylinderFiberSlab.boundaryAtlas_injective_mfderiv_ambient
        d.map d.rightMap d.smooth_right b d.regular_right k hd s t d.rightTimes d.right_eq p

theorem slab_injective_mfderiv_ambient :
    letI := (d.openCover k hd Φ hsource).chartedSpace;
    ∀ p : CylinderFiberSlab.slab d.map b s t,
      Injective (mfderiv ((𝓡∂ 1).prod (𝓡 k)) ((𝓘(ℝ, ℝ)).prod I)
        (fun q : CylinderFiberSlab.slab d.map b s t ↦ q.val.val) p) := by
  let A := d.openCover k hd Φ hsource
  let := A.chartedSpace
  exact A.injective_mfderiv_of_onPieces _
    (d.slab_contMDiff_ambient k hd Φ hsource) (d.piece_injective_mfderiv_ambient k hd Φ hsource)

end NoExoticSixSphere.RegularCollaredCylinder
