import Wikipedia.NoExoticSixSphere.PartialGradientLocalCrossing
import Wikipedia.NoExoticSixSphere.PartialGradientFiberCore

/-!
# A local crossing that does not enter a smaller fiber core

The avoidance tolerance is chosen independently of the radial radius and of
the initial crossing domain. Every point starting outside a given fiber core
stays outside the corresponding smaller core throughout the whole crossing.
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

theorem exists_core_nonentering_crossing (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U)
    (r : ℝ) (hr : 0 < r) (hball : Metric.ball (0 : E) (3 * r) ⊆ C.chart.source)
    (a b η : ℝ) (hη : 0 < η) (δ l k e : ℝ) (hlk : l < k)
    (hgap : ∀ z ∈ C.radialDomain r, f (C.radial r (1, z)) ≤ f (C.center z) - δ)
    (p : C(M, E)) (hp : ∀ x, p x ∈ C.crossingDomain r l (k + δ) e)
    (S : Set M) (hS : IsCompact S) (hLow : ∀ x ∈ S, f (p x) ≤ l)
    (hd : finrank ℝ B < finrank ℝ D) :
    ∃ q : C(M, E), (∀ x, f (q x) < k) ∧
      ∃ G : ContinuousMap.HomotopyRel p q S,
        ∀ t x, G (t, x) ∈ C.chart.source ∧ f (G (t, x)) < e ∧
          (p x ∉ C.fiberCore a b → G (t, x) ∉ C.fiberCore a (b - η)) := by
  obtain ⟨q, hq, G, hG⟩ := C.exists_crossing_homotopy_with_fiber_control (I := I)
    hU hf r hr hball η hη δ l k e hlk hgap p hp S hS hLow hd
  exact ⟨q, hq, G, fun t x ↦ ⟨(hG t x).1, (hG t x).2.1,
    fun hx ↦ C.notMem_fiberCore_of_control (hp x).1 hx (hG t x).2.2.2.1 (hG t x).2.2.2.2⟩⟩

end NoExoticSixSphere.PartialGradientCoordinates.LocalData
