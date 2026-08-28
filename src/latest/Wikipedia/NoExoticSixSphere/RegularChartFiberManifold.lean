import Wikipedia.NoExoticSixSphere.ChartFiberRegularity
import Wikipedia.NoExoticSixSphere.ChartFiberAtlas

/-!
# The actual fiber of a regular manifold-valued map

The zero fiber inside the valid chart preimage is homeomorphic to the original
fiber. Pulling its constructed level atlas back along this subspace
homeomorphism gives the original fiber its smooth structure and smooth
inclusion. This does not modify a pre-existing candidate sphere's atlas.
-/

open scoped Manifold ContDiff
open Set Module

namespace NoExoticSixSphere

variable {B H M C H' N F : Type*}
  [NormedAddCommGroup B] [NormedSpace ℝ B] [FiniteDimensional ℝ B] [TopologicalSpace H]
  {I : ModelWithCorners ℝ B H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [NormedAddCommGroup C] [NormedSpace ℝ C] [TopologicalSpace H']
  {J : ModelWithCorners ℝ C H'} [TopologicalSpace N] [ChartedSpace H' N]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

theorem exists_regularChartFiberManifold (f : ContinuousMap M N)
    (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞)
    (hf : ContMDiff I J ∞ f) (b : N) (hb : b ∈ c.source)
    (hreg : ∀ x, f x = b → Function.Surjective (mfderiv I J f x))
    (k : ℕ) (hd : finrank ℝ B = finrank ℝ F + k) :
    ∃ atlas : ChartedSpace (EuclideanSpace ℝ (Fin k)) {x : M // f x = b},
      letI := atlas;
      IsManifold (𝓡 k) ∞ {x : M // f x = b} ∧
      ContMDiff (𝓡 k) I ∞ ((↑) : {x : M // f x = b} → M) := by
  obtain ⟨A⟩ := ChartFiber.nonempty_levelAtlas f c hf b hb hreg k hd
  exact ⟨ChartFiber.atlas f c b hb A, ChartFiber.isManifold f c b hb A,
    ChartFiber.contMDiff_subtype_val f c b hb A⟩

end NoExoticSixSphere
