import Arxiv.Arxiv2411_18291.DesignCompletion
import Arxiv.Arxiv2411_18291.NearCompleteDensity
import Arxiv.Arxiv2411_18291.NibblePaperParameters
import Arxiv.Arxiv2411_18291.ConstantComplementBoost
import Arxiv.Arxiv2411_18291.PaperThresholdAssembly
import Arxiv.Arxiv2411_18291.ReserveCover
import Arxiv.Arxiv2411_18291.SparseAbsorberExistence

/-! # Unconditional design existence in rank at least two -/

open Finset Filter
open scoped Topology

noncomputable section

namespace Arxiv2411_18291

theorem hasDecomposition_complete_succ_explicit {q r n : ℕ}
    (hr : 1 ≤ r) (hqr : r + 1 < q)
    (hn : boundedIntegralGeneratorThreshold q r ≤ n) :
    Divisible q (complete (Fin n) (r + 1)) →
      HasDecomposition q (complete (Fin n) (r + 1)) := by
  have hnI : integralGeneratorThreshold q r ≤ n := (le_max_left _ _).trans hn
  have hn0 : paperSizeThreshold q (r + 1) ≤ n := (le_max_left _ _).trans hnI
  intro hdiv
  obtain ⟨R, hR, hcover⟩ := exists_reserve_cover_decompositions_paper_threshold q r n hqr hn0
  obtain ⟨A, habs, hA⟩ := exists_sparse_absorber_explicit hqr hn R hR
  let G := complete (Fin n) (r + 1) \ (A ∪ R)
  have hhost := paper_threshold_regular_host hqr
    (by simpa only [Fintype.card_fin] using hn0) A R
    (by simpa only [Fintype.card_fin, paperAlpha, paperRho] using hA)
    (by simpa only [Fintype.card_fin, paperRho] using hR)
  obtain ⟨hG, hdense⟩ := hhost
  obtain ⟨H, hHG, hdegrees⟩ := regularity_boost_paper_threshold q r n hqr hn0 G hG
  have hcliques : ∀ Q ∈ H, cliqueEdges (r + 1) Q ⊆ G := by
    intro Q hQ
    exact (mem_filter.mp (hHG hQ)).2
  obtain ⟨D, hDH, hD, hleave⟩ := exists_nibble_paper_threshold_of_three_le q r n hqr
    (three_le_clique_size (by omega) hqr) hn0 G H
    (by simpa only [Fintype.card_fin] using hdense) hcliques hdegrees
  have hDG : cliqueSupport (r + 1) D ⊆ G := by
    intro e he
    obtain ⟨Q, hQ, heQ⟩ := mem_biUnion.mp he
    exact hcliques Q (hDH hQ) heQ
  have hLR : Disjoint (G \ cliqueSupport (r + 1) D) R := by
    apply disjoint_left.mpr
    intro e he heR
    exact (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp he).1).2 (mem_union_right _ heR)
  obtain ⟨C, E, hLC, hCL, hC, _⟩ := hcover _ hLR hleave
  exact complete_of_packing_cover_absorber hqr.le hdiv habs ⟨D, hD⟩ ⟨E, hC⟩ hDG hLC hCL

/-- The reserve, absorber, regularity boost, nibble, and cover constructions
together imply the eventual existence of every divisible complete design
of rank at least two. No auxiliary existence assumptions remain. -/
theorem eventually_hasDecomposition_complete_succ (q r : ℕ)
    (hr : 1 ≤ r) (hqr : r + 1 < q) :
    ∀ᶠ n : ℕ in atTop, Divisible q (complete (Fin n) (r + 1)) →
      HasDecomposition q (complete (Fin n) (r + 1)) := by
  filter_upwards [eventually_ge_atTop (boundedIntegralGeneratorThreshold q r)] with n hn
  exact hasDecomposition_complete_succ_explicit hr hqr hn

end Arxiv2411_18291
