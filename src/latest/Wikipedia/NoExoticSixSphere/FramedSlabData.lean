import Wikipedia.NoExoticSixSphere.FramedCollaredSlab
import Wikipedia.NoExoticSixSphere.CollaredSlabBoundaryImmersion

/-!
# Complete geometric data for a compact framed slab

The data retain the actual slab, its Euclidean embedding, the global boundary
atlas, a normal frame, and the original endpoint-fiber atlases. The boundary
diffeomorphism has the specified endpoint values, and the normal frame agrees
there with the endpoint frames. The constructor chooses all auxiliary model
coordinates internally.
-/

open scoped Manifold ContDiff
open Module Function Set Topology

namespace NoExoticSixSphere.RegularCollaredCylinder

variable {m n : ℕ} {b : Sphere n} {s t : ℝ}
  (d : RegularCollaredCylinder (M := Sphere m) (𝓡 m) (𝓡 n) b s t)

theorem isClosedEmbedding_slabEuclideanInclusion : IsClosedEmbedding d.slabEuclideanInclusion := by
  let : CompactSpace (CylinderFiberSlab.slab d.map b s t) :=
    CylinderFiberSlab.compactSpace d.map b s t
  have hi : Continuous (fun p : CylinderFiberSlab.slab d.map b s t ↦ p.val.val) :=
    continuous_subtype_val.comp continuous_subtype_val
  have hc : Continuous d.slabEuclideanInclusion :=
    (WithLp.prodContinuousLinearEquiv 2 ℝ ℝ
      (EuclideanSpace ℝ (Fin (m + 1)))).symm.continuous.comp
        (hi.fst.prodMk (continuous_subtype_val.comp hi.snd))
  apply hc.isClosedEmbedding
  intro p q hpq
  have he : (p.val.val.1, p.val.val.2.val) = (q.val.val.1, q.val.val.2.val) :=
    congrArg WithLp.ofLp hpq
  have ht : p.val.val.1 = q.val.val.1 :=
    congrArg (fun z : ℝ × EuclideanSpace ℝ (Fin (m + 1)) ↦ z.1) he
  have hx : p.val.val.2.val = q.val.val.2.val :=
    congrArg (fun z : ℝ × EuclideanSpace ℝ (Fin (m + 1)) ↦ z.2) he
  apply Subtype.ext
  apply Subtype.ext
  exact Prod.ext ht (Subtype.ext hx)

structure FramedSlabData (k : ℕ) (hd : m = n + k) (a : Sphere m) where
  atlas : ChartedSpace (ModelProd (EuclideanHalfSpace 1) (EuclideanSpace ℝ (Fin k)))
    (CylinderFiberSlab.slab d.map b s t)
  manifold : letI := atlas;
    IsManifold ((𝓡∂ 1).prod (𝓡 k)) ∞ (CylinderFiberSlab.slab d.map b s t)
  smooth_inclusion : letI := atlas;
    ContMDiff ((𝓡∂ 1).prod (𝓡 k))
      𝓘(ℝ, WithLp 2 (ℝ × EuclideanSpace ℝ (Fin (m + 1)))) ∞ d.slabEuclideanInclusion
  injective_differential : letI := atlas; ∀ p,
    Injective (NormalFrameOfEquations.ambientDifferential ((𝓡∂ 1).prod (𝓡 k))
      d.slabEuclideanInclusion p)
  boundary_iff : letI := atlas; ∀ p : CylinderFiberSlab.slab d.map b s t,
    ((𝓡∂ 1).prod (𝓡 k)).IsBoundaryPoint p ↔ p.val.val.1 = s ∨ p.val.val.1 = t
  frame : letI := atlas;
    SmoothRangeFrame ((𝓡∂ 1).prod (𝓡 k))
      (fun p : CylinderFiberSlab.slab d.map b s t ↦
        (NormalFrameOfEquations.ambientDifferential ((𝓡∂ 1).prod (𝓡 k))
          d.slabEuclideanInclusion p).rangeᗮ.starProjection)
      (WithLp 2 (ℝ × EuclideanSpace ℝ (Fin n)))
  frame_left : letI := atlas;
    letI := regularFiberAtlas d.leftMap d.smooth_left b d.regular_left k (by simpa using hd);
    ∀ x : {x : Sphere m // d.leftMap x = b}, frame.ambient (d.leftEndpoint x).val =
      CylinderNormalFrame.liftFrame
        ((SphereFiberNormalFrame.normalFrame d.leftMap d.smooth_left b
          d.regular_left k hd a).ambient x)
  frame_right : letI := atlas;
    letI := regularFiberAtlas d.rightMap d.smooth_right b d.regular_right k (by simpa using hd);
    ∀ x : {x : Sphere m // d.rightMap x = b}, frame.ambient (d.rightEndpoint x).val =
      CylinderNormalFrame.liftFrame
        ((SphereFiberNormalFrame.normalFrame d.rightMap d.smooth_right b
          d.regular_right k hd a).ambient x)
  boundaryAtlas : letI := atlas;
    ChartedSpace (EuclideanSpace ℝ (Fin k))
      {p : CylinderFiberSlab.slab d.map b s t // ((𝓡∂ 1).prod (𝓡 k)).IsBoundaryPoint p}
  boundaryManifold : letI := atlas; letI := boundaryAtlas;
    IsManifold (𝓡 k) ∞
      {p : CylinderFiberSlab.slab d.map b s t // ((𝓡∂ 1).prod (𝓡 k)).IsBoundaryPoint p}
  boundaryDiffeomorph : letI := atlas; letI := boundaryAtlas;
    letI := regularFiberAtlas d.leftMap d.smooth_left b d.regular_left k (by simpa using hd);
    letI := regularFiberAtlas d.rightMap d.smooth_right b d.regular_right k (by simpa using hd);
    ({x : Sphere m // d.leftMap x = b} ⊕ {x : Sphere m // d.rightMap x = b}) ≃ₘ⟮𝓡 k, 𝓡 k⟯
      {p : CylinderFiberSlab.slab d.map b s t // ((𝓡∂ 1).prod (𝓡 k)).IsBoundaryPoint p}
  boundary_left : ∀ x, (boundaryDiffeomorph (Sum.inl x)).val = (d.leftEndpoint x).val
  boundary_right : ∀ x, (boundaryDiffeomorph (Sum.inr x)).val = (d.rightEndpoint x).val
  smooth_boundaryInclusion : letI := atlas; letI := boundaryAtlas;
    ContMDiff (𝓡 k) ((𝓡∂ 1).prod (𝓡 k)) ∞
      (Subtype.val :
        {p : CylinderFiberSlab.slab d.map b s t // ((𝓡∂ 1).prod (𝓡 k)).IsBoundaryPoint p} →
          CylinderFiberSlab.slab d.map b s t)
  injective_boundaryDifferential : letI := atlas; letI := boundaryAtlas;
    ∀ p : {p : CylinderFiberSlab.slab d.map b s t // ((𝓡∂ 1).prod (𝓡 k)).IsBoundaryPoint p},
      Injective (mfderiv (𝓡 k) ((𝓡∂ 1).prod (𝓡 k)) Subtype.val p)

noncomputable def framedSlabDataOfModel (k : ℕ) (hd : m = n + k)
    (Φ : PartialDiffeomorph (𝓡 (k + 1)) ((𝓡∂ 1).prod (𝓡 k))
      (EuclideanSpace ℝ (Fin (k + 1)))
      (ModelProd (EuclideanHalfSpace 1) (EuclideanSpace ℝ (Fin k))) ∞)
    (hsource : Φ.source = univ)
    (hinterior : ∀ y ∈ Φ.target,
      ((𝓡∂ 1).prod (𝓡 k)) y ∈ interior (range ((𝓡∂ 1).prod (𝓡 k))))
    (a : Sphere m) : d.FramedSlabData k hd a := by
  let := (d.openCover k (by simpa using hd) Φ hsource).chartedSpace
  let := d.boundaryAtlas k (by simpa using hd) Φ hsource hinterior
  let := regularFiberAtlas d.leftMap d.smooth_left b d.regular_left k (by simpa using hd)
  let := regularFiberAtlas d.rightMap d.smooth_right b d.regular_right k (by simpa using hd)
  exact
    { atlas := (d.openCover k (by simpa using hd) Φ hsource).chartedSpace
      manifold := (d.openCover k (by simpa using hd) Φ hsource).isManifold
      smooth_inclusion := d.contMDiff_slabEuclideanInclusion k hd Φ hsource
      injective_differential := d.injective_slabEuclideanDifferential k hd Φ hsource
      boundary_iff := d.slab_isBoundaryPoint_iff k (by simpa using hd) Φ hsource hinterior
      frame := d.slabNormalFrame k hd Φ hsource a
      frame_left := d.slabNormalFrame_left k hd Φ hsource a
      frame_right := d.slabNormalFrame_right k hd Φ hsource a
      boundaryAtlas := d.boundaryAtlas k (by simpa using hd) Φ hsource hinterior
      boundaryManifold := d.boundary_isManifold k (by simpa using hd) Φ hsource hinterior
      boundaryDiffeomorph := d.boundaryDiffeomorph k (by simpa using hd) Φ hsource hinterior
      boundary_left := d.boundaryDiffeomorph_inl_val k (by simpa using hd) Φ hsource hinterior
      boundary_right := d.boundaryDiffeomorph_inr_val k (by simpa using hd) Φ hsource hinterior
      smooth_boundaryInclusion := d.contMDiff_boundaryInclusion k
        (by simpa using hd) Φ hsource hinterior
      injective_boundaryDifferential := d.injective_mfderiv_boundaryInclusion k
        (by simpa using hd) Φ hsource hinterior }

theorem nonempty_framedSlabData (k : ℕ) (hd : m = n + k) (a : Sphere m) :
    Nonempty (d.FramedSlabData k hd a) := by
  let L : EuclideanSpace ℝ (Fin (k + 1)) ≃L[ℝ]
      (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin k)) :=
    (LinearEquiv.ofFinrankEq _ _ (by simp [finrank_prod, Nat.add_comm])).toContinuousLinearEquiv
  obtain ⟨Φ, hΦ, hΦint⟩ := exists_fullSource_modelPartialDiffeomorph ((𝓡∂ 1).prod (𝓡 k)) L
  exact ⟨d.framedSlabDataOfModel k hd Φ hΦ hΦint a⟩

end NoExoticSixSphere.RegularCollaredCylinder
