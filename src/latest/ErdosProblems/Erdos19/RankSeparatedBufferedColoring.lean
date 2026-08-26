import ErdosProblems.Erdos19.RankSeparation
import ErdosProblems.Erdos19.EventualBufferedLists

/-! # Buffer-preserving coloring around a precolored larger-rank palette -/

namespace Erdos19.SetHypergraph

open Finset

attribute [local instance] Classical.propDecidable

theorem eventually_buffered_coloring_around_large_palette (R s t : ℕ)
    (hR : 0 < R) (hs : 2 ≤ s) (ht : 0 < t) (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ ell N : ℕ, 2 ≤ ell ∧ ∀ n : ℕ, N ≤ n →
      ∀ L K : SetHypergraph (Fin n), L.IsLinear → K.IsLinear →
      ∀ m : ℕ, ∀ color : L.EdgeColoring (Fin m), ∀ palette : Finset (Fin m),
        (∀ e : L, color e ∈ palette → ell * R ≤ e.1.ncard) →
        (∀ e : K, e.1.ncard ≤ R) → ∀ D : ℕ, n ≤ 2 * D → D ≤ n →
        (∀ v, (K.incidentEdges v).ncard ≤ D) →
        ∀ (I : Type) [Fintype I] [DecidableEq I], ∀ B : I → Finset (Fin n),
          (Pairwise fun i j ↦ Disjoint (B i) (B j)) → (∀ i, n / t ≤ (B i).card) →
          (∀ i v, v ∈ B i → (K.incidentEdges v).ncard ≤ D - n / s) →
          (1 + epsilon) * (D : ℝ) ≤ palette.card →
          ∃ c : K.EdgeColoring palette,
            (∀ e : K, ∀ f : L, (e.1 ∩ f.1).Nonempty → (c e).1 ≠ color f) ∧
            ∀ i a, n / (16 * s * t) ≤
              (B i \ (K.coveredVertices {e | c e = a}).toFinset).card := by
  classical
  obtain ⟨delta, hdelta, N, hN⟩ :=
    eventually_bounded_rank_buffered_lists R s t hR hs ht epsilon hepsilon
  obtain ⟨ell, hell, hsep⟩ := exists_rank_separation_for_forbidden_colors R hR delta hdelta
  refine ⟨ell, N, hell, ?_⟩
  intro n hn L K hL hK m color palette hmin hmax D hDlow hDhigh hdegree I _ _ B
    hB hBsize hlow hpalette
  let F : K → Finset palette := fun e ↦ L.forbiddenReservedColors color e.1 palette
  have hF : ∀ e, ((F e).card : ℝ) ≤ delta * n :=
    fun e ↦ hsep n L hL m color palette hmin e.1 (hmax e)
  obtain ⟨c, hcF, hbuffer⟩ := hN n hn K hK hmax D hDlow hDhigh hdegree I palette B
    hB hBsize hlow F hF (by simpa only [Fintype.card_coe] using hpalette)
  refine ⟨c, ?_, hbuffer⟩
  intro e f hinter heq
  exact hcF e (mem_filter.mpr ⟨mem_univ _, f, heq.symm, hinter⟩)

#print axioms eventually_buffered_coloring_around_large_palette

end Erdos19.SetHypergraph
