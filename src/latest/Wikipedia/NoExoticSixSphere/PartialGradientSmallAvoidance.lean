import Wikipedia.NoExoticSixSphere.SmallChartZeroAvoidance
import Wikipedia.NoExoticSixSphere.PartialGradientCenter

/-!
# Small center-preserving avoidance of a partial-critical slice

The avoidance homotopy is uniformly small in the ambient normed model space.
It preserves both the complementary chart coordinate and the actual fiber
center, and is fixed on the prescribed compact safe parameter set.
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

theorem exists_relational_gradient_avoiding_homotopy (p : C(M, E)) (V : Set E)
    (hV : IsOpen V) (hsource : V ⊆ C.chart.source) (hmem : ∀ x, p x ∈ V)
    (R : Set (E × E)) (hR : IsOpen R) (hdiag : ∀ x, (p x, p x) ∈ R)
    (S : Set M) (hS : IsCompact S)
    (hSafe : ∀ x ∈ S, gradient f L (p x) ≠ 0) (hd : finrank ℝ B < finrank ℝ D) :
    ∃ q : C(M, E), (∀ x, gradient f L (q x) ≠ 0) ∧
      ∃ G : ContinuousMap.HomotopyRel p q S,
        ∀ t x, G (t, x) ∈ V ∧ (C.chart (G (t, x))).2 = (C.chart (p x)).2 ∧
          C.center (G (t, x)) = C.center (p x) ∧ (G (t, x), p x) ∈ R := by
  have hdim : finrank ℝ D = finrank ℝ (D →L[ℝ] ℝ) := by
    calc
      finrank ℝ D = finrank ℝ (D →ₗ[ℝ] ℝ) := Subspace.dual_finrank_eq.symm
      _ = finrank ℝ (D →L[ℝ] ℝ) :=
        (LinearMap.toContinuousLinearMap : (D →ₗ[ℝ] ℝ) ≃ₗ[ℝ] (D →L[ℝ] ℝ)).finrank_eq
  obtain ⟨q, hq, G, hG⟩ := exists_relational_zeroSlice_avoiding_chart_homotopy (I := I)
    C.chart.toOpenPartialHomeomorph p V hV hsource hmem R hR hdiag S hS
    (fun x hx ↦ by
      change (C.chart (p x)).1 ≠ 0
      rw [C.map_fst]
      exact hSafe x hx) (hd.trans_eq hdim)
  refine ⟨q, fun x ↦ ?_, G, fun t x ↦ ?_⟩
  · have hh : (C.chart (q x)).1 ≠ 0 := hq x
    simpa only [C.map_fst] using hh
  · have hs : (C.chart (G (t, x))).2 = (C.chart (p x)).2 := (hG t x).2.1
    refine ⟨(hG t x).1, hs, ?_, (hG t x).2.2⟩
    change C.chart.symm (0, (C.chart (G (t, x))).2) = C.chart.symm (0, (C.chart (p x)).2)
    rw [hs]

theorem exists_small_gradient_avoiding_homotopy (p : C(M, E)) (V : Set E)
    (hV : IsOpen V) (hsource : V ⊆ C.chart.source) (hmem : ∀ x, p x ∈ V)
    (ε : ℝ) (hε : 0 < ε) (S : Set M) (hS : IsCompact S)
    (hSafe : ∀ x ∈ S, gradient f L (p x) ≠ 0) (hd : finrank ℝ B < finrank ℝ D) :
    ∃ q : C(M, E), (∀ x, gradient f L (q x) ≠ 0) ∧
      ∃ G : ContinuousMap.HomotopyRel p q S,
        ∀ t x, G (t, x) ∈ V ∧ (C.chart (G (t, x))).2 = (C.chart (p x)).2 ∧
          C.center (G (t, x)) = C.center (p x) ∧ dist (G (t, x)) (p x) < ε :=
  C.exists_relational_gradient_avoiding_homotopy (I := I) p V hV hsource hmem
    {z | dist z.1 z.2 < ε}
    (isOpen_lt (continuous_fst.dist continuous_snd) continuous_const)
    (fun _ ↦ by simpa only [mem_ofPred_eq, dist_self] using hε) S hS hSafe hd

end NoExoticSixSphere.PartialGradientCoordinates.LocalData
