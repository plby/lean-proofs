import Wikipedia.NoExoticSixSphere.CollaredSlabEndpointSmoothness

/-!
# The smooth boundary as the disjoint union of endpoint fibers

The boundary is the subtype defined by the global slab's `IsBoundaryPoint`
predicate. Its atlas is transported from the independently constructed
regular-fiber atlases at the two ends. The resulting diffeomorphism has the
actual endpoint values, and the boundary inclusion into the slab is smooth.
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

noncomputable def boundaryHomeomorph :
    letI := (d.openCover k hd Φ hsource).chartedSpace;
    ({x : M // d.leftMap x = b} ⊕ {x : M // d.rightMap x = b}) ≃ₜ
      {p : CylinderFiberSlab.slab d.map b s t // ((𝓡∂ 1).prod (𝓡 k)).IsBoundaryPoint p} := by
  let := (d.openCover k hd Φ hsource).chartedSpace
  exact d.endpointHomeomorph.trans (Homeomorph.setCongr (by
    ext p
    exact (d.slab_isBoundaryPoint_iff k hd Φ hsource hinterior p).symm))

theorem boundaryHomeomorph_inl_val (x : {x : M // d.leftMap x = b}) :
    letI := (d.openCover k hd Φ hsource).chartedSpace;
    (d.boundaryHomeomorph k hd Φ hsource hinterior (Sum.inl x)).val =
      (d.leftEndpoint x).val := rfl

theorem boundaryHomeomorph_inr_val (x : {x : M // d.rightMap x = b}) :
    letI := (d.openCover k hd Φ hsource).chartedSpace;
    (d.boundaryHomeomorph k hd Φ hsource hinterior (Sum.inr x)).val =
      (d.rightEndpoint x).val := rfl

@[instance_reducible]
noncomputable def boundaryAtlas :
    letI := (d.openCover k hd Φ hsource).chartedSpace;
    ChartedSpace (EuclideanSpace ℝ (Fin k))
      {p : CylinderFiberSlab.slab d.map b s t // ((𝓡∂ 1).prod (𝓡 k)).IsBoundaryPoint p} := by
  let := (d.openCover k hd Φ hsource).chartedSpace
  let := regularFiberAtlas d.leftMap d.smooth_left b d.regular_left k hd
  let := regularFiberAtlas d.rightMap d.smooth_right b d.regular_right k hd
  exact ModelAtlasTransport.atlas (H := EuclideanSpace ℝ (Fin k))
    (d.boundaryHomeomorph k hd Φ hsource hinterior).symm

theorem boundary_isManifold :
    letI := (d.openCover k hd Φ hsource).chartedSpace;
    letI := d.boundaryAtlas k hd Φ hsource hinterior;
    IsManifold (𝓡 k) ∞
      {p : CylinderFiberSlab.slab d.map b s t // ((𝓡∂ 1).prod (𝓡 k)).IsBoundaryPoint p} := by
  let := (d.openCover k hd Φ hsource).chartedSpace
  let := regularFiberAtlas d.leftMap d.smooth_left b d.regular_left k hd
  let := regularFiberAtlas d.rightMap d.smooth_right b d.regular_right k hd
  let := regularFiber_isManifold d.leftMap d.smooth_left b d.regular_left k hd
  let := regularFiber_isManifold d.rightMap d.smooth_right b d.regular_right k hd
  exact ModelAtlasTransport.isManifold
    (d.boundaryHomeomorph k hd Φ hsource hinterior).symm (𝓡 k)

noncomputable def boundaryDiffeomorph :
    letI := (d.openCover k hd Φ hsource).chartedSpace;
    letI := d.boundaryAtlas k hd Φ hsource hinterior;
    letI := regularFiberAtlas d.leftMap d.smooth_left b d.regular_left k hd;
    letI := regularFiberAtlas d.rightMap d.smooth_right b d.regular_right k hd;
    ({x : M // d.leftMap x = b} ⊕ {x : M // d.rightMap x = b}) ≃ₘ⟮𝓡 k, 𝓡 k⟯
      {p : CylinderFiberSlab.slab d.map b s t // ((𝓡∂ 1).prod (𝓡 k)).IsBoundaryPoint p} := by
  let := (d.openCover k hd Φ hsource).chartedSpace
  let := d.boundaryAtlas k hd Φ hsource hinterior
  let := regularFiberAtlas d.leftMap d.smooth_left b d.regular_left k hd
  let := regularFiberAtlas d.rightMap d.smooth_right b d.regular_right k hd
  exact (ModelAtlasTransport.diffeomorph
    (d.boundaryHomeomorph k hd Φ hsource hinterior).symm (𝓡 k)).symm

theorem boundaryDiffeomorph_inl_val (x : {x : M // d.leftMap x = b}) :
    letI := (d.openCover k hd Φ hsource).chartedSpace;
    letI := d.boundaryAtlas k hd Φ hsource hinterior;
    letI := regularFiberAtlas d.leftMap d.smooth_left b d.regular_left k hd;
    letI := regularFiberAtlas d.rightMap d.smooth_right b d.regular_right k hd;
    (d.boundaryDiffeomorph k hd Φ hsource hinterior (Sum.inl x)).val =
      (d.leftEndpoint x).val := rfl

theorem boundaryDiffeomorph_inr_val (x : {x : M // d.rightMap x = b}) :
    letI := (d.openCover k hd Φ hsource).chartedSpace;
    letI := d.boundaryAtlas k hd Φ hsource hinterior;
    letI := regularFiberAtlas d.leftMap d.smooth_left b d.regular_left k hd;
    letI := regularFiberAtlas d.rightMap d.smooth_right b d.regular_right k hd;
    (d.boundaryDiffeomorph k hd Φ hsource hinterior (Sum.inr x)).val =
      (d.rightEndpoint x).val := rfl

theorem contMDiff_boundaryInclusion :
    letI := (d.openCover k hd Φ hsource).chartedSpace;
    letI := d.boundaryAtlas k hd Φ hsource hinterior;
    ContMDiff (𝓡 k) ((𝓡∂ 1).prod (𝓡 k)) ∞
      (Subtype.val :
        {p : CylinderFiberSlab.slab d.map b s t // ((𝓡∂ 1).prod (𝓡 k)).IsBoundaryPoint p} →
          CylinderFiberSlab.slab d.map b s t) := by
  let := (d.openCover k hd Φ hsource).chartedSpace
  let := d.boundaryAtlas k hd Φ hsource hinterior
  let := regularFiberAtlas d.leftMap d.smooth_left b d.regular_left k hd
  let := regularFiberAtlas d.rightMap d.smooth_right b d.regular_right k hd
  let e := d.boundaryDiffeomorph k hd Φ hsource hinterior
  have hs := (d.contMDiff_leftEndpoint_inclusion k hd Φ hsource).sumElim
    (d.contMDiff_rightEndpoint_inclusion k hd Φ hsource)
  have he : ContMDiff (𝓡 k) ((𝓡∂ 1).prod (𝓡 k)) ∞ (fun x ↦ (e x).val) := by
    convert hs using 1
    funext x
    cases x <;> rfl
  have h := he.comp e.symm.contMDiff
  simpa only [Function.comp_def, Diffeomorph.apply_symm_apply] using h

end NoExoticSixSphere.RegularCollaredCylinder
