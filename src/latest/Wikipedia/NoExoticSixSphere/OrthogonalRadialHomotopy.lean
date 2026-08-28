import Wikipedia.NoExoticSixSphere.OrthogonalPartialGradientCoordinates
import Wikipedia.NoExoticSixSphere.PartialGradientRadialEnergy

/-!
# The negative-fiber radial homotopy as actual polygon vertices

The verified coordinate homotopy is transported through the genuine product
Cayley inverse chart. It remains admissible, fixes the outer fiber boundary,
and never increases the actual polygon energy.

The domain excludes the partial-critical center slice. Avoiding that slice
in low-dimensional families and assembling a critical-level comparison remain
separate tasks.
-/

open Set unitInterval
open scoped ContDiff Manifold

namespace NoExoticSixSphere.OrthogonalPolygon

open GLOrthonormalization OrthogonalVertexSpace

variable {n m d : ℕ} (a b : OrthogonalOperators n) (τ : Fin (m + 2) → ℝ) (v : Space n m)
  {L : (Fin d → ℝ) →L[ℝ] Model n m}
  (C : PartialGradientCoordinates.LocalData (localEnergy a b τ v) L (localAdmissible a b v))

noncomputable def radialVertices (r : ℝ) : C(C.radialDomain r, Space n m) :=
  ⟨fun z ↦ (atVertices v).symm z.1,
    (contMDiff_atVertices_symm v).continuous.comp continuous_subtype_val⟩

noncomputable def radialVertexHomotopy (r : ℝ) (hr : 0 < r)
    (hball : Metric.ball (0 : Model n m) (3 * r) ⊆ C.chart.source) :
    ContinuousMap.HomotopyRel (radialVertices a b τ v C r)
      ((radialVertices a b τ v C r).comp (C.radialEndpoint r hr hball))
      {z : C.radialDomain r | ‖z.1 - C.center z.1‖ = r} :=
  ((C.radialHomotopy r hr hball).compContinuousMap (radialVertices a b τ v C r)).cast
    (by ext z; rfl) rfl

theorem radialVertexHomotopy_admissible (r : ℝ) (hr : 0 < r)
    (hball : Metric.ball (0 : Model n m) (3 * r) ⊆ C.chart.source)
    (s : I) (z : C.radialDomain r) :
    radialVertexHomotopy a b τ v C r hr hball (s, z) ∈ admissible a b m := by
  change (atVertices v).symm (C.radial r (s, z.1)) ∈ admissible a b m
  exact C.source_subset (C.radial_mem_source r hr hball z.2 s)

theorem radialVertexHomotopy_energy_le (r : ℝ) (hr : 0 < r)
    (hball : Metric.ball (0 : Model n m) (3 * r) ⊆ C.chart.source)
    (s : I) (z : C.radialDomain r) :
    energy a b τ (radialVertexHomotopy a b τ v C r hr hball (s, z)) ≤
      energy a b τ (radialVertices a b τ v C r z) := by
  change localEnergy a b τ v (C.radial r (s, z.1)) ≤ localEnergy a b τ v z.1
  exact C.energy_radial_le (isOpen_localAdmissible a b v) (contDiffOn_localEnergy a b τ v)
    r hr hball z.2 s

end NoExoticSixSphere.OrthogonalPolygon
