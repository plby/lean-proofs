import ErdosProblems.Erdos19.NearCompleteRegular
import ErdosProblems.Erdos19.SmallSupportColoring

/-! # The uniformly dense graph case

The small-support and large-support arguments cover all support sizes.
Pair completion then removes the auxiliary pair-completeness hypothesis.
-/

namespace Erdos19.SetHypergraph

open _root_.SimpleGraph

attribute [local instance] Classical.propDecidable

theorem eventually_color_pairComplete_of_dense_twoGraph :
    ∃ delta : ℝ, 0 < delta ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ H : SetHypergraph (Fin n), H.IsLinear → H.IsPairComplete →
      (∀ e : H, 2 ≤ e.1.ncard) →
      (∀ v, (1 - delta) * n ≤ (H.twoGraph.degree v : ℝ)) → H.EdgeColorable n := by
  obtain ⟨delta, hd, N₀, hN₀⟩ := eventually_color_of_dense_twoGraph_and_large_support
  refine ⟨delta, hd, max N₀ 1, ?_⟩
  intro n hn H hlinear hcomplete hsize hG
  by_cases hsmall : 8 * H.largePart.vertexSupport.ncard ≤ n
  · simpa only [Fintype.card_fin] using H.edgeColorable_of_support_at_most_eighth hlinear
      hcomplete hsize (by simpa only [Fintype.card_fin] using (show 0 < n by omega))
      (by simpa only [Fintype.card_fin] using hsmall)
  · exact hN₀ n ((le_max_left _ _).trans hn) H hlinear hcomplete hsize hG (by omega)

theorem twoGraph_mono {V : Type*} {H J : SetHypergraph V} (hHJ : H ⊆ J) :
    H.twoGraph ≤ J.twoGraph := fun _ _ h ↦ ⟨h.1, hHJ h.2⟩

theorem eventually_color_of_dense_twoGraph :
    ∃ delta : ℝ, 0 < delta ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ H : SetHypergraph (Fin n), H.IsLinear →
      (∀ e : H, 2 ≤ e.1.ncard) →
      (∀ v, (1 - delta) * n ≤ (H.twoGraph.degree v : ℝ)) → H.EdgeColorable n := by
  obtain ⟨delta, hd, N, hN⟩ := eventually_color_pairComplete_of_dense_twoGraph
  refine ⟨delta, hd, N, ?_⟩
  intro n hn H hlinear hsize hG
  have hJlinear : H.pairCompletion.IsLinear := pairCompletion_isLinear hlinear
  have hJsize : ∀ e : H.pairCompletion, 2 ≤ e.1.ncard := fun e ↦
    pairCompletion_min_size (fun e he ↦ hsize ⟨e, he⟩) e.1 e.2
  have hJdegree : ∀ v, (1 - delta) * n ≤ (H.pairCompletion.twoGraph.degree v : ℝ) := by
    intro v
    have hmono := Set.ncard_le_ncard
      (show H.twoGraph.neighborSet v ⊆ H.pairCompletion.twoGraph.neighborSet v from
        fun _ h ↦ twoGraph_mono H.subset_pairCompletion h)
    have hd : H.twoGraph.degree v ≤ H.pairCompletion.twoGraph.degree v := by
      simpa only [← card_neighborSet_eq_degree, Set.fintypeCard_eq_ncard] using hmono
    exact (hG v).trans (by exact_mod_cast hd)
  have hc := hN n hn H.pairCompletion hJlinear H.pairCompletion_isPairComplete hJsize hJdegree
  exact hc.of_subset H.subset_pairCompletion

#print axioms eventually_color_of_dense_twoGraph

end Erdos19.SetHypergraph
