import Wikipedia.NoExoticSixSphere.CollaredSlabAtlas
import Wikipedia.NoExoticSixSphere.SmoothOpenCoverMaps

/-!
# Smooth inclusion and exact boundary of the global slab

The glued manifold has smooth ambient inclusion. Its manifold boundary is
exactly the two endpoint fibers: the middle piece has no boundary points,
and boundary status on each endpoint piece is preserved by its local
diffeomorphism into the global atlas. Global regularity remains an explicit
input through the actual regular collared cylinder data.
-/

open scoped Manifold ContDiff
open Module Set

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
  (hsource : Φ.source = univ)
  (hinterior : ∀ y ∈ Φ.target,
    ((𝓡∂ 1).prod (𝓡 k)) y ∈ interior (range ((𝓡∂ 1).prod (𝓡 k))))

include hinterior in
theorem piece_isBoundaryPoint_iff (i : Piece) (p : d.pieceDomain i) :
    letI := d.pieceAtlas k hd Φ hsource i;
    ((𝓡∂ 1).prod (𝓡 k)).IsBoundaryPoint p ↔ p.val.val.val.1 = s ∨ p.val.val.val.1 = t := by
  let : Fact (s < t) := ⟨d.time_lt⟩
  cases i with
  | left =>
      exact CylinderFiberSlab.boundaryAtlas_isBoundaryPoint_iff d.map d.leftMap d.smooth_left b
        d.regular_left k hd s t d.leftTimes d.left_eq p
  | middle =>
      let := d.pieceAtlas k hd Φ hsource .middle
      have hp := CylinderFiberSlab.interiorAtlas_isInteriorPoint d.map d.smooth_map b d.regular_map
        (k + 1) (cylinder_finrank_eq hd) s t Φ hsource hinterior p
      have hn := (((𝓡∂ 1).prod (𝓡 k)).isInteriorPoint_iff_not_isBoundaryPoint p).mp hp
      exact iff_of_false hn (not_or.mpr ⟨ne_of_gt p.property.1, ne_of_lt p.property.2⟩)
  | right =>
      exact CylinderFiberSlab.boundaryAtlas_isBoundaryPoint_iff d.map d.rightMap d.smooth_right b
        d.regular_right k hd s t d.rightTimes d.right_eq p

theorem slab_contMDiff_ambient : letI := (d.openCover k hd Φ hsource).chartedSpace;
    ContMDiff ((𝓡∂ 1).prod (𝓡 k)) ((𝓘(ℝ, ℝ)).prod I) ∞
      (fun p : CylinderFiberSlab.slab d.map b s t ↦ p.val.val) := by
  let A := d.openCover k hd Φ hsource
  let := A.chartedSpace
  apply (A.contMDiff_iff_onPieces _).mpr
  exact d.piece_contMDiff_ambient k hd Φ hsource

include hinterior in
theorem slab_isBoundaryPoint_iff (p : CylinderFiberSlab.slab d.map b s t) :
    letI := (d.openCover k hd Φ hsource).chartedSpace;
    ((𝓡∂ 1).prod (𝓡 k)).IsBoundaryPoint p ↔ p.val.val.1 = s ∨ p.val.val.1 = t := by
  let A := d.openCover k hd Φ hsource
  let := A.chartedSpace
  obtain ⟨i, hi⟩ := d.pieceDomain_covers p
  let := d.pieceAtlas k hd Φ hsource i
  let q : d.pieceDomain i := ⟨p, hi⟩
  exact (A.isBoundaryPoint_inclusion_iff i q).symm.trans
    (d.piece_isBoundaryPoint_iff k hd Φ hsource hinterior i q)

include hd in
theorem exists_slabManifoldWithBoundary :
    ∃ c : ChartedSpace (ModelProd (EuclideanHalfSpace 1) (EuclideanSpace ℝ (Fin k)))
        (CylinderFiberSlab.slab d.map b s t),
      letI := c;
      IsManifold ((𝓡∂ 1).prod (𝓡 k)) ∞ (CylinderFiberSlab.slab d.map b s t) ∧
      ContMDiff ((𝓡∂ 1).prod (𝓡 k)) ((𝓘(ℝ, ℝ)).prod I) ∞
        (fun p : CylinderFiberSlab.slab d.map b s t ↦ p.val.val) ∧
      ∀ p : CylinderFiberSlab.slab d.map b s t,
        ((𝓡∂ 1).prod (𝓡 k)).IsBoundaryPoint p ↔ p.val.val.1 = s ∨ p.val.val.1 = t := by
  let L : EuclideanSpace ℝ (Fin (k + 1)) ≃L[ℝ]
      (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin k)) :=
    (LinearEquiv.ofFinrankEq _ _ (by simp [finrank_prod, Nat.add_comm])).toContinuousLinearEquiv
  obtain ⟨Ψ, hΨ, hΨint⟩ := exists_fullSource_modelPartialDiffeomorph ((𝓡∂ 1).prod (𝓡 k)) L
  exact ⟨(d.openCover k hd Ψ hΨ).chartedSpace, (d.openCover k hd Ψ hΨ).isManifold,
    d.slab_contMDiff_ambient k hd Ψ hΨ, d.slab_isBoundaryPoint_iff k hd Ψ hΨ hΨint⟩

end NoExoticSixSphere.RegularCollaredCylinder
