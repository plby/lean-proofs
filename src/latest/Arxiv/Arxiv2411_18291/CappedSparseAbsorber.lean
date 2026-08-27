import Arxiv.Arxiv2411_18291.UnconditionalFirstElimination
import Arxiv.Arxiv2411_18291.CappedFurtherElimination
import Arxiv.Arxiv2411_18291.VariableSignedAbsorption
import Arxiv.Arxiv2411_18291.RankOneAbsorber

/-! # Unconditional sparse absorption at the original paper threshold

The capped generators, weighted decoder placements, variable splitting,
and both universal cancellation stages are all constructed from the sparse
source graph. No bounded-multiplicity flattening threshold is needed.
-/

open Finset

noncomputable section

namespace Arxiv2411_18291

theorem exists_capped_sparse_absorber_paper_threshold {q r n : ℕ}
    (hqr : r + 1 < q) (hq : 3 ≤ q) (hn : paperSizeThreshold q (r + 1) ≤ n)
    (B : Hypergraph (Fin n) (r + 1))
    (hB : IsGraphBounded B ((n : ℝ) ^ (-paperRho q (r + 1)))) :
    ∃ H : Hypergraph (Fin n) (r + 1), IsAbsorber q H B ∧
      IsGraphBounded H ((n : ℝ) ^ (-(paperAlpha q (r + 1) / 4))) := by
  obtain ⟨D, _, _, S, A, hA, hcross, hlocal, Z, hZ, F, hF, hcap,
    T, N₀, e₀, hpair, hT, hw, E, _, hout⟩ :=
    exists_unconditional_first_elimination_paper_threshold hqr hq hn B hB
  obtain ⟨L⟩ := exists_variable_further_elimination_pairs F hA E hpair
  obtain ⟨G⟩ := exists_capped_further_elimination_paper_threshold
    hA F hqr hn hF hcap T.system N₀ e₀ hpair hw hT E L
  let H := cliqueSupport (r + 1) (variableFinalNegative F E L G)
  have hBB : B ⊆ cliqueCoverGraph (r := r) Z := by
    intro e he
    exact hZ.root_mem ⟨e, mem_union_left _ he⟩
  have hdis : Disjoint H B :=
    Disjoint.mono_right hBB (variableFinalNegative_avoids_original F E L G hpair)
  have hn1 : (1 : ℝ) ≤ n := by
    exact_mod_cast (paperSizeThreshold_one_lt hqr).le.trans hn
  have hα := paperAlpha_pos hqr
  have hbound : IsGraphBounded H ((n : ℝ) ^ (-(paperAlpha q (r + 1) / 4))) :=
    (variableFinalNegative_bounded F E L G hpair).mono
      (Real.rpow_le_rpow_of_exponent_le hn1 (by linarith only [hα]))
  refine ⟨H, ⟨hdis, ?_⟩, hbound⟩
  intro J hJB hJ
  obtain ⟨P, N, hP, hN, _, hb, M, _, _, _⟩ := hout J hJB hJ
  exact M.two_stage_absorbs hA hlocal hcross E L G hpair hqr.le hP hN J
    (hJB.trans hBB) hb

theorem exists_sparse_absorber_paper_threshold {q r n : ℕ}
    (hqr : r + 1 < q) (hn : paperSizeThreshold q (r + 1) ≤ n)
    (B : Hypergraph (Fin n) (r + 1))
    (hB : IsGraphBounded B ((n : ℝ) ^ (-paperRho q (r + 1)))) :
    ∃ H : Hypergraph (Fin n) (r + 1), IsAbsorber q H B ∧
      IsGraphBounded H ((n : ℝ) ^ (-(paperAlpha q (r + 1) / 4))) := by
  by_cases hr : r = 0
  · subst r
    have hn0 : (0 : ℝ) < n := by
      exact_mod_cast Nat.zero_lt_one.trans ((paperSizeThreshold_one_lt hqr).trans_le hn)
    refine ⟨∅, empty_isAbsorber_one q B, ?_⟩
    intro s
    simp only [filter_empty, card_empty, Nat.cast_zero, Fintype.card_fin]
    exact mul_pos (Real.rpow_pos_of_pos hn0 _) hn0
  · exact exists_capped_sparse_absorber_paper_threshold hqr (by omega) hn B hB

end Arxiv2411_18291
