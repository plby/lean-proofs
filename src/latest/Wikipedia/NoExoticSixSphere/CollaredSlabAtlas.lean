import Wikipedia.NoExoticSixSphere.RegularCollaredCylinder
import Wikipedia.NoExoticSixSphere.SlabInteriorAtlas
import Wikipedia.NoExoticSixSphere.SlabBoundarySmoothMaps
import Wikipedia.NoExoticSixSphere.SmoothOpenCover

/-!
# A global boundary atlas on an actual regular collared slab

The endpoint and interior pieces use one boundary model. Their ambient
smooth-map criteria prove compatibility of the actual overlap maps. The
open-cover construction then gives the original compact slab topology its
global smooth structure, without assuming such a structure as input.
-/

open scoped Manifold ContDiff
open Module

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

@[instance_reducible]
noncomputable def pieceAtlas (i : Piece) :
    ChartedSpace (ModelProd (EuclideanHalfSpace 1) (EuclideanSpace ℝ (Fin k)))
      (d.pieceDomain i) := by
  let : Fact (s < t) := ⟨d.time_lt⟩
  cases i with
  | left =>
      exact CylinderFiberSlab.boundaryAtlas d.map d.leftMap d.smooth_left b
        d.regular_left k hd s t d.leftTimes d.left_eq
  | middle =>
      exact CylinderFiberSlab.interiorAtlas d.map d.smooth_map b d.regular_map
        (k + 1) (cylinder_finrank_eq hd) s t Φ hsource
  | right =>
      exact CylinderFiberSlab.boundaryAtlas d.map d.rightMap d.smooth_right b
        d.regular_right k hd s t d.rightTimes d.right_eq

theorem piece_isManifold (i : Piece) : letI := d.pieceAtlas k hd Φ hsource i;
    IsManifold ((𝓡∂ 1).prod (𝓡 k)) ∞ (d.pieceDomain i) := by
  let : Fact (s < t) := ⟨d.time_lt⟩
  cases i with
  | left =>
      exact CylinderFiberSlab.boundaryAtlas_isManifold d.map d.leftMap d.smooth_left b
        d.regular_left k hd s t d.leftTimes d.left_eq
  | middle =>
      exact CylinderFiberSlab.interiorAtlas_isManifold d.map d.smooth_map b d.regular_map
        (k + 1) (cylinder_finrank_eq hd) s t Φ hsource
  | right =>
      exact CylinderFiberSlab.boundaryAtlas_isManifold d.map d.rightMap d.smooth_right b
        d.regular_right k hd s t d.rightTimes d.right_eq

theorem piece_contMDiff_ambient (i : Piece) : letI := d.pieceAtlas k hd Φ hsource i;
    ContMDiff ((𝓡∂ 1).prod (𝓡 k)) ((𝓘(ℝ, ℝ)).prod I) ∞
      (fun p : d.pieceDomain i ↦ p.val.val.val) := by
  let : Fact (s < t) := ⟨d.time_lt⟩
  cases i with
  | left =>
      exact CylinderFiberSlab.boundaryAtlas_contMDiff_ambient d.map d.leftMap d.smooth_left b
        d.regular_left k hd s t d.leftTimes d.left_eq
  | middle =>
      exact CylinderFiberSlab.interiorAtlas_contMDiff_ambient d.map d.smooth_map b d.regular_map
        (k + 1) (cylinder_finrank_eq hd) s t Φ hsource
  | right =>
      exact CylinderFiberSlab.boundaryAtlas_contMDiff_ambient d.map d.rightMap d.smooth_right b
        d.regular_right k hd s t d.rightTimes d.right_eq

variable {E H'' P : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H''] {L : ModelWithCorners ℝ E H''}
  [TopologicalSpace P] [ChartedSpace H'' P]

theorem piece_contMDiff_iff_ambient (i : Piece) (g : P → d.pieceDomain i) :
    letI := d.pieceAtlas k hd Φ hsource i;
    ContMDiff L ((𝓡∂ 1).prod (𝓡 k)) ∞ g ↔
      ContMDiff L ((𝓘(ℝ, ℝ)).prod I) ∞ (fun x ↦ (g x).val.val.val) := by
  let : Fact (s < t) := ⟨d.time_lt⟩
  cases i with
  | left =>
      exact CylinderFiberSlab.boundaryAtlas_contMDiff_iff_ambient
        d.map d.leftMap d.smooth_left b d.regular_left k hd s t d.leftTimes d.left_eq g
  | middle =>
      exact CylinderFiberSlab.interiorAtlas_contMDiff_iff_ambient
        d.map d.smooth_map b d.regular_map (k + 1) (cylinder_finrank_eq hd) s t Φ hsource g
  | right =>
      exact CylinderFiberSlab.boundaryAtlas_contMDiff_iff_ambient
        d.map d.rightMap d.smooth_right b d.regular_right k hd s t d.rightTimes d.right_eq g

noncomputable def openCover : SmoothOpenCover ((𝓡∂ 1).prod (𝓡 k)) d.pieceDomain where
  covers := d.pieceDomain_covers
  localAtlas := d.pieceAtlas k hd Φ hsource
  localSmooth := d.piece_isManifold k hd Φ hsource
  overlapSmooth := by
    intro i j
    let := d.pieceAtlas k hd Φ hsource i
    let := d.pieceAtlas k hd Φ hsource j
    apply (d.piece_contMDiff_iff_ambient k hd Φ hsource j
      (OpenOverlap.map (d.pieceDomain i) (d.pieceDomain j))).mpr
    exact (d.piece_contMDiff_ambient k hd Φ hsource i).comp contMDiff_subtype_val

include hd in
theorem exists_slabManifold :
    ∃ c : ChartedSpace (ModelProd (EuclideanHalfSpace 1) (EuclideanSpace ℝ (Fin k)))
        (CylinderFiberSlab.slab d.map b s t),
      letI := c;
      IsManifold ((𝓡∂ 1).prod (𝓡 k)) ∞ (CylinderFiberSlab.slab d.map b s t) := by
  let L : EuclideanSpace ℝ (Fin (k + 1)) ≃L[ℝ]
      (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin k)) :=
    (LinearEquiv.ofFinrankEq _ _ (by simp [finrank_prod, Nat.add_comm])).toContinuousLinearEquiv
  obtain ⟨Ψ, hΨ, _⟩ := exists_fullSource_modelPartialDiffeomorph ((𝓡∂ 1).prod (𝓡 k)) L
  exact ⟨(d.openCover k hd Ψ hΨ).chartedSpace, (d.openCover k hd Ψ hΨ).isManifold⟩

end NoExoticSixSphere.RegularCollaredCylinder
