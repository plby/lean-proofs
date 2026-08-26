import ErdosProblems.Erdos19.LargeEdgeDichotomy
import ErdosProblems.Erdos19.InducedCounting

/-! # The exact eventual coloring bound when all hyperedges are large -/

namespace Erdos19.SetHypergraph

open Finset

attribute [local instance] Classical.propDecidable

theorem edgeColorable_of_projective_peelable_core {V : Type*} [Fintype V]
    (H : SetHypergraph V) (hlinear : H.IsLinear) (n : ℕ)
    (hvertices : Fintype.card V = n) (hn : 0 < n)
    (hscale : 65536 ≤ projectiveScale n) (S : Finset H) (k : ℕ) (hk : k ≤ n)
    (hpeel : IsPeelableOutside H.lineGraph univ S k)
    (hmin : ∀ e ∈ S, projectiveScale n - projectiveScale n / 1024 ≤ e.1.ncard) :
    H.EdgeColorable n := by
  classical
  let J := H.restrictEdges (S : Set H)
  have hJmin (e : J) : projectiveScale n - projectiveScale n / 1024 ≤ e.1.ncard := by
    obtain ⟨f, hf, hfe⟩ := e.2
    rw [← hfe]
    exact hmin f hf
  have hJcolor := J.edgeColorable_of_fixedFraction_projectiveScale_edges
    (H.restrictEdges_linear hlinear _) n hvertices hscale hJmin
  have hcore : (H.lineGraph.induce (S : Set H)).Colorable n :=
    _root_.SimpleGraph.Colorable.of_hom (H.restrictEdgesLineGraphIso (S : Set H)).toHom
      ((J.edgeColorable_iff_lineGraph_colorable n).mp hJcolor)
  have hpeel' : IsPeelableOutside H.lineGraph univ S n := by
    intro T hT hne
    obtain ⟨v, hv, hdeg⟩ := hpeel T hT hne
    exact ⟨v, hv, hdeg.trans_le hk⟩
  exact (H.edgeColorable_iff_lineGraph_colorable n).mpr
    (colorable_of_colorable_peelable_core H.lineGraph S n hn hpeel' hcore)

theorem eventually_edgeColorable_of_large_minimum_size :
    ∃ r₀ N : ℕ, 2 ≤ r₀ ∧ ∀ n : ℕ, N ≤ n →
      ∀ H : SetHypergraph (Fin n), H.IsLinear → (∀ e : H, r₀ ≤ e.1.ncard) →
      H.EdgeColorable n := by
  obtain ⟨b, hb, _, N₀, hbN, hN₀⟩ := eventually_large_edge_saving_or_projective_core 0
  refine ⟨b ^ 4, max N₀ (65536 * 65536 + 65536 + 2), ?_, ?_⟩
  · have h := Nat.pow_le_pow_left hb 4
    norm_num at h
    omega
  intro n hn H hlinear hmin
  have hn₀ : N₀ ≤ n := (le_max_left _ _).trans hn
  have hnscale : 65536 * 65536 + 65536 + 2 ≤ n := (le_max_right _ _).trans hn
  have hscale := projectiveScale_ge_of_large_card 65536 n hnscale
  rcases hN₀ n hn₀ H hlinear hmin with hc |
    ⟨S, W, r, _, _, _, _, hpeel, hr, hminS, _, _⟩
  · exact hc.mono (Nat.sub_le _ _)
  · exact H.edgeColorable_of_projective_peelable_core hlinear n (Fintype.card_fin n)
      (by omega) hscale S (n - n / b ^ 4) (Nat.sub_le _ _) hpeel
      (fun e he ↦ hr.trans (hminS e he))

#print axioms eventually_edgeColorable_of_large_minimum_size

end Erdos19.SetHypergraph
