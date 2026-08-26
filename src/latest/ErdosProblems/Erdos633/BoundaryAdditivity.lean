import ErdosProblems.Erdos633.BoundaryDensity
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Signed boundary additivity for actual triangle dissections

Integrating the verified pointwise boundary cancellation against
one-dimensional Hausdorff measure proves the full boundary identity. The odd
direction function is arbitrary; no continuity, measurability, edge matching,
or assumed internal cancellation is required.
-/

namespace Erdos633

open MeasureTheory
open scoped BigOperators ENNReal

noncomputable def Triangle.signedBoundary (P : Triangle) (φ : ℂ → ℝ) : ℝ :=
  ∑ k : Fin 3, P.sideLength k * φ (P.unitEdgeVector k)

theorem Triangle.integrable_edgeDensity (P : Triangle) (φ : ℂ → ℝ) (k : Fin 3) :
    Integrable (P.edgeDensity φ k) (μH[1] : Measure ℂ) := by
  rw [Triangle.edgeDensity, integrable_indicator_iff (P.measurableSet_edge k)]
  have hfinite : (μH[1] : Measure ℂ) (P.edge k) ≠ ⊤ := by
    rw [P.hausdorffMeasure_edge]
    exact ENNReal.ofReal_ne_top
  exact integrableOn_const hfinite

theorem Triangle.integrable_boundaryDensity (P : Triangle) (φ : ℂ → ℝ) :
    Integrable (P.boundaryDensity φ) (μH[1] : Measure ℂ) := by
  exact integrable_finsetSum Finset.univ (fun k _ => P.integrable_edgeDensity φ k)

theorem Triangle.integral_edgeDensity (P : Triangle) (φ : ℂ → ℝ) (k : Fin 3) :
    (∫ z, P.edgeDensity φ k z ∂(μH[1] : Measure ℂ)) =
      P.sideLength k * φ (P.unitEdgeVector k) := by
  rw [Triangle.edgeDensity, integral_indicator_const _ (P.measurableSet_edge k)]
  change ((μH[1] : Measure ℂ) (P.edge k)).toReal * φ (P.unitEdgeVector k) = _
  rw [P.hausdorffMeasure_edge_toReal]

theorem Triangle.integral_boundaryDensity (P : Triangle) (φ : ℂ → ℝ) :
    (∫ z, P.boundaryDensity φ z ∂(μH[1] : Measure ℂ)) = P.signedBoundary φ := by
  unfold Triangle.boundaryDensity Triangle.signedBoundary
  rw [integral_finsetSum Finset.univ (fun k _ => P.integrable_edgeDensity φ k)]
  exact Finset.sum_congr rfl (fun k _ => P.integral_edgeDensity φ k)

theorem TriangleDissection.boundaryDensity_ae_eq_sum
    {P : Triangle} {N : ℕ} (T : TriangleDissection P N)
    (φ : ℂ → ℝ) (hodd : ∀ w, φ (-w) = -φ w) :
    P.boundaryDensity φ =ᵐ[(μH[1] : Measure ℂ)]
      fun z => ∑ i : Fin N, (T.tile i).boundaryDensity φ z := by
  let : NullSingletonClass (μH[1] : Measure ℂ) :=
    Measure.nullSingletonClass_hausdorff ℂ (by norm_num)
  have hv := T.vertexFinset.finite_toSet.countable.ae_notMem (μH[1] : Measure ℂ)
  filter_upwards [hv] with z hz
  exact T.boundaryDensity_eq_sum_of_not_vertex φ hodd hz

/-- The signed boundary identity is extracted from the geometric tiling itself.
It holds for every odd function on unit directions. -/
theorem TriangleDissection.signedBoundary_eq_sum
    {P : Triangle} {N : ℕ} (T : TriangleDissection P N)
    (φ : ℂ → ℝ) (hodd : ∀ w, φ (-w) = -φ w) :
    P.signedBoundary φ = ∑ i : Fin N, (T.tile i).signedBoundary φ := by
  rw [← P.integral_boundaryDensity φ,
    integral_congr_ae (T.boundaryDensity_ae_eq_sum φ hodd),
    integral_finsetSum Finset.univ (fun i _ => (T.tile i).integrable_boundaryDensity φ)]
  exact Finset.sum_congr rfl (fun i _ => (T.tile i).integral_boundaryDensity φ)

theorem CongruentTiling.signedBoundary_eq_sum
    {P R : Triangle} {N : ℕ} (T : CongruentTiling P R N)
    (φ : ℂ → ℝ) (hodd : ∀ w, φ (-w) = -φ w) :
    P.signedBoundary φ = ∑ i : Fin N, (T.labelledTile i).signedBoundary φ :=
  T.labelledDissection.signedBoundary_eq_sum φ hodd

end Erdos633
