import Wikipedia.NoExoticSixSphere.NormalFrameOfEquations
import Wikipedia.NoExoticSixSphere.GLOrthonormalization
import Wikipedia.NoExoticSixSphere.ProductHalfSpaceModel
import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
import Mathlib.Geometry.Manifold.Instances.Real

/-!
# Geometric framed seven-dimensional fillings with the original boundary atlas

This record retains a genuine compact manifold with boundary, its smooth
closed Euclidean embedding, a full normal frame, and a diffeomorphism from
the specified original boundary manifold. It does not assert existence for
an arbitrary boundary or prescribe an external boundary normal framing.
-/

noncomputable section

open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse

open NoExoticSixSphere GLOrthonormalization

universe u v

variable {B H : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] [TopologicalSpace H]

structure FramedSevenFilling (I : ModelWithCorners ℝ B H) (L : Type u)
    [TopologicalSpace L] [ChartedSpace H L] where
  W : Type v
  [topology : TopologicalSpace W]
  [hausdorff : T2Space W]
  [secondCountable : SecondCountableTopology W]
  [compact : CompactSpace W]
  [atlas : ChartedSpace (ProductHalfSpace.Space (Vector 6)) W]
  [manifold : IsManifold (ProductHalfSpace.model (Vector 6)) ∞ W]
  ambientDimension : ℕ
  inclusion : W → Vector ambientDimension
  closed_embedding : Topology.IsClosedEmbedding inclusion
  smooth_inclusion : ContMDiff (ProductHalfSpace.model (Vector 6)) (𝓡 ambientDimension) ∞ inclusion
  injective_differential : ∀ w, Function.Injective
    (NormalFrameOfEquations.ambientDifferential (ProductHalfSpace.model (Vector 6)) inclusion w)
  frame : SmoothRangeFrame (ProductHalfSpace.model (Vector 6))
    (fun w ↦ (NormalFrameOfEquations.ambientDifferential
      (ProductHalfSpace.model (Vector 6)) inclusion w).rangeᗮ.starProjection)
    (Vector (ambientDimension - 7))
  boundaryAtlas : ChartedSpace (Vector 6)
    {w : W // (ProductHalfSpace.model (Vector 6)).IsBoundaryPoint w}
  boundaryManifold : letI := boundaryAtlas;
    IsManifold (𝓡 6) ∞ {w : W // (ProductHalfSpace.model (Vector 6)).IsBoundaryPoint w}
  boundaryDiffeomorph : letI := boundaryAtlas;
    L ≃ₘ⟮I, 𝓡 6⟯ {w : W // (ProductHalfSpace.model (Vector 6)).IsBoundaryPoint w}
  smooth_boundaryInclusion : letI := boundaryAtlas;
    ContMDiff (𝓡 6) (ProductHalfSpace.model (Vector 6)) ∞
      (Subtype.val : {w : W // (ProductHalfSpace.model (Vector 6)).IsBoundaryPoint w} → W)
  injective_boundaryDifferential : letI := boundaryAtlas;
    ∀ w : {w : W // (ProductHalfSpace.model (Vector 6)).IsBoundaryPoint w},
      Function.Injective (mfderiv (𝓡 6) (ProductHalfSpace.model (Vector 6)) Subtype.val w)

namespace FramedSevenFilling

variable {I : ModelWithCorners ℝ B H} {L : Type u} [TopologicalSpace L] [ChartedSpace H L]
  (W : FramedSevenFilling I L)
  {B' H' L' : Type*} [NormedAddCommGroup B'] [NormedSpace ℝ B'] [TopologicalSpace H']
  {J : ModelWithCorners ℝ B' H'} [TopologicalSpace L'] [ChartedSpace H' L']

def reparametrizeBoundary (d : L' ≃ₘ⟮J, I⟯ L) : FramedSevenFilling J L' := by
  let := W.topology
  let := W.atlas
  let := W.boundaryAtlas
  exact { W with boundaryDiffeomorph := d.trans W.boundaryDiffeomorph }

end FramedSevenFilling

end Wikipedia.HopfProblem.DegreeCollapse
