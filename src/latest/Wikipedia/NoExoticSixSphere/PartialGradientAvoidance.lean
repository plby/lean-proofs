import Wikipedia.NoExoticSixSphere.OpenZeroSliceAvoidance
import Wikipedia.NoExoticSixSphere.PartialGradientLocalData

/-!
# Relative avoidance of the partial-critical slice

Within one verified negative-family chart, a compact parameter family of
dimension smaller than the negative-family dimension can be deformed off the
partial-critical slice. The homotopy stays in any prescribed open subset of
the chart source, fixes a compact already-safe parameter set, and preserves
the complementary coordinate.
-/

open Set Module
open scoped Manifold ContDiff Topology

namespace NoExoticSixSphere.PartialGradientCoordinates.LocalData

variable {B H M D E : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
  [FiniteDimensional ℝ B] [TopologicalSpace H] {I : ModelWithCorners ℝ B H}
  [I.Boundaryless] [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [T2Space M]
  [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  {f : E → ℝ} {L : D →L[ℝ] E} {U : Set E} (C : LocalData f L U)

include I

theorem exists_gradient_avoiding_homotopy (p : C(M, E)) (V : Set E)
    (hV : IsOpen V) (hsource : V ⊆ C.chart.source) (hmem : ∀ x, p x ∈ V)
    (S : Set M) (hS : IsCompact S) (hSafe : ∀ x ∈ S, gradient f L (p x) ≠ 0)
    (hd : finrank ℝ B < finrank ℝ D) :
    ∃ q : C(M, E), (∀ x, gradient f L (q x) ≠ 0) ∧
      ∃ G : ContinuousMap.HomotopyRel p q S,
        ∀ t x, G (t, x) ∈ V ∧ (C.chart (G (t, x))).2 = (C.chart (p x)).2 := by
  have hdim : finrank ℝ D = finrank ℝ (D →L[ℝ] ℝ) := by
    calc
      finrank ℝ D = finrank ℝ (D →ₗ[ℝ] ℝ) := Subspace.dual_finrank_eq.symm
      _ = finrank ℝ (D →L[ℝ] ℝ) :=
        (LinearMap.toContinuousLinearMap : (D →ₗ[ℝ] ℝ) ≃ₗ[ℝ] (D →L[ℝ] ℝ)).finrank_eq
  obtain ⟨q, hq, G, hG⟩ := exists_zeroSlice_avoiding_chart_homotopy (I := I)
    C.chart.toOpenPartialHomeomorph p V hV hsource hmem S hS
    (fun x hx ↦ by
      change (C.chart (p x)).1 ≠ 0
      rw [C.map_fst]
      exact hSafe x hx) (hd.trans_eq hdim)
  refine ⟨q, fun x ↦ ?_, G, hG⟩
  have hh : (C.chart (q x)).1 ≠ 0 := hq x
  simpa only [C.map_fst] using hh

end NoExoticSixSphere.PartialGradientCoordinates.LocalData
