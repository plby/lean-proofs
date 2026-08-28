import Wikipedia.NoExoticSixSphere.FramedSlabSingleBoundary

/-!
# Geometric framed fillings of regular sphere fibers

The filling is a genuine compact manifold with boundary. Its Euclidean
inclusion is a smooth closed embedding with injective differential. Its normal
frame restricts to the specified induced frame of the original regular fiber,
and the latter is diffeomorphic to the entire actual manifold boundary.

This data type does not assert existence for arbitrary fibers.
-/

open scoped Manifold ContDiff

namespace NoExoticSixSphere

structure SphereFiberFramedFilling {m n : ℕ} (f : C(Sphere m, Sphere n))
    (hf : ContMDiff (𝓡 m) (𝓡 n) ∞ f) (b : Sphere n)
    (hreg : ∀ x, f x = b → Function.Surjective (mfderiv (𝓡 m) (𝓡 n) f x))
    (k : ℕ) (hd : m = n + k) (a : Sphere m) where
  W : Type
  [topology : TopologicalSpace W]
  [hausdorff : T2Space W]
  [secondCountable : SecondCountableTopology W]
  [compact : CompactSpace W]
  [atlas : ChartedSpace (ModelProd (EuclideanHalfSpace 1) (EuclideanSpace ℝ (Fin k))) W]
  [manifold : IsManifold ((𝓡∂ 1).prod (𝓡 k)) ∞ W]
  inclusion : W → WithLp 2 (ℝ × EuclideanSpace ℝ (Fin (m + 1)))
  closed_embedding : Topology.IsClosedEmbedding inclusion
  smooth_inclusion : ContMDiff ((𝓡∂ 1).prod (𝓡 k))
    𝓘(ℝ, WithLp 2 (ℝ × EuclideanSpace ℝ (Fin (m + 1)))) ∞ inclusion
  injective_differential : ∀ w,
    Function.Injective (NormalFrameOfEquations.ambientDifferential
      ((𝓡∂ 1).prod (𝓡 k)) inclusion w)
  frame : SmoothRangeFrame ((𝓡∂ 1).prod (𝓡 k))
    (fun w ↦ (NormalFrameOfEquations.ambientDifferential
      ((𝓡∂ 1).prod (𝓡 k)) inclusion w).rangeᗮ.starProjection)
    (WithLp 2 (ℝ × EuclideanSpace ℝ (Fin n)))
  boundaryAtlas : ChartedSpace (EuclideanSpace ℝ (Fin k))
    {w : W // ((𝓡∂ 1).prod (𝓡 k)).IsBoundaryPoint w}
  boundaryManifold : letI := boundaryAtlas;
    IsManifold (𝓡 k) ∞ {w : W // ((𝓡∂ 1).prod (𝓡 k)).IsBoundaryPoint w}
  boundaryDiffeomorph : letI := boundaryAtlas;
    letI := regularFiberAtlas f hf b hreg k (by simpa using hd);
    {x : Sphere m // f x = b} ≃ₘ⟮𝓡 k, 𝓡 k⟯
      {w : W // ((𝓡∂ 1).prod (𝓡 k)).IsBoundaryPoint w}
  boundary_value : ∀ x, inclusion (boundaryDiffeomorph x).val =
    WithLp.toLp 2 (0, x.val.val)
  boundary_frame : letI := regularFiberAtlas f hf b hreg k (by simpa using hd);
    ∀ x, frame.ambient (boundaryDiffeomorph x).val =
      CylinderNormalFrame.liftFrame
        ((SphereFiberNormalFrame.normalFrame f hf b hreg k hd a).ambient x)
  smooth_boundaryInclusion : letI := boundaryAtlas;
    ContMDiff (𝓡 k) ((𝓡∂ 1).prod (𝓡 k)) ∞
      (Subtype.val : {w : W // ((𝓡∂ 1).prod (𝓡 k)).IsBoundaryPoint w} → W)
  injective_boundaryDifferential : letI := boundaryAtlas;
    ∀ w : {w : W // ((𝓡∂ 1).prod (𝓡 k)).IsBoundaryPoint w},
      Function.Injective (mfderiv (𝓡 k) ((𝓡∂ 1).prod (𝓡 k)) Subtype.val w)

namespace RegularCollaredCylinder.FramedSlabData

variable {m n k : ℕ} {b : Sphere n}
  {d : RegularCollaredCylinder (M := Sphere m) (𝓡 m) (𝓡 n) b 0 1}
  {hd : m = n + k} {a : Sphere m} (A : d.FramedSlabData k hd a)

noncomputable def toSphereFiberFramedFilling (hmiss : ∀ x, d.rightMap x ≠ b) :
    SphereFiberFramedFilling d.leftMap d.smooth_left b d.regular_left k hd a := by
  letI := A.atlas
  letI := A.manifold
  letI := A.boundaryAtlas
  letI := regularFiberAtlas d.leftMap d.smooth_left b d.regular_left k (by simpa using hd)
  refine
    { W := CylinderFiberSlab.slab d.map b 0 1
      topology := inferInstance
      hausdorff := inferInstance
      secondCountable := inferInstance
      compact := CylinderFiberSlab.compactSpace d.map b 0 1
      atlas := A.atlas
      manifold := A.manifold
      inclusion := d.slabEuclideanInclusion
      closed_embedding := d.isClosedEmbedding_slabEuclideanInclusion
      smooth_inclusion := A.smooth_inclusion
      injective_differential := A.injective_differential
      frame := A.frame
      boundaryAtlas := A.boundaryAtlas
      boundaryManifold := A.boundaryManifold
      boundaryDiffeomorph := A.leftBoundaryDiffeomorph hmiss
      boundary_value := ?_
      boundary_frame := A.leftBoundaryDiffeomorph_frame hmiss
      smooth_boundaryInclusion := A.smooth_boundaryInclusion
      injective_boundaryDifferential := A.injective_boundaryDifferential }
  intro x
  rw [A.leftBoundaryDiffeomorph_val hmiss x]
  rfl

end RegularCollaredCylinder.FramedSlabData

end NoExoticSixSphere
