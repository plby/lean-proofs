import ErdosProblems.Erdos19.ColorIncidence
import ErdosProblems.Erdos19.MatchingHypergraphCompletion

/-! # Completing a sparse coloring of the large edges

The graph-degree budget here follows from linearity and pair completeness;
it is not an extra completion hypothesis.
-/

namespace Erdos19.SetHypergraph

attribute [local instance] Classical.propDecidable

theorem eventually_color_of_sparse_large_coloring (zeta : ℝ) (hzeta : 0 < zeta) :
    ∃ delta : ℝ, 0 < delta ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ H : SetHypergraph (Fin n), H.IsLinear → H.IsPairComplete →
      (∀ e : H, 2 ≤ e.1.ncard) →
      (∀ v, (1 - delta) * n ≤ (H.twoGraph.degree v : ℝ)) →
      ∀ m : ℕ, (m : ℝ) ≤ (1 - zeta) * n →
      ∀ c : H.largePart.EdgeColoring (Fin m),
      (∀ i, m + (H.largePart.colorCovered c i).ncard ≤ H.largePart.vertexSupport.ncard) →
      (∀ i, ((H.largePart.colorCovered c i).ncard : ℝ) ≤ delta * n) →
      (∀ v, (H.largeDegree v : ℝ) ≤ delta * n) → H.EdgeColorable n := by
  obtain ⟨delta, hd, N, hN⟩ := eventually_extend_coloring_with_sparse_classes zeta hzeta
  refine ⟨delta, hd, N, ?_⟩
  intro n hn H hlinear hcomplete hsize hG m hm c hroom hsmall hlarge
  have hrest : ∀ e : H, e.1 ∉ H.largePart → e.1.ncard = 2 := by
    intro e he
    have hmin := hsize e
    have hnot : ¬3 ≤ e.1.ncard := fun h ↦ he ⟨e.2, h⟩
    omega
  apply hN n hn H H.largePart (fun _ h ↦ h.1) hrest hG m hm c
    H.largePart.vertexSupport (H.largePart.colorCovered c)
  · intro e v hv
    exact ⟨e, rfl, hv⟩
  · intro i v hv
    obtain ⟨e, _, he⟩ := hv
    exact ⟨e, he⟩
  · exact hroom
  · exact hsmall
  · intro v
    rw [colorCovered_count, largePart_incident_ncard]
    exact hlarge v
  · intro v
    simpa only [Fintype.card_fin] using
      H.large_coloring_parity_degree_budget hlinear hcomplete hsize c v

#print axioms eventually_color_of_sparse_large_coloring

end Erdos19.SetHypergraph
