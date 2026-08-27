import Arxiv.Arxiv2411_18291.DesignExistence
import Arxiv.Arxiv2411_18291.CappedSparseAbsorber

/-! # Design existence at the original explicit threshold

The variable-capacity absorber completes the finite reserve, boost,
nibble, cover, and absorption argument at n0 = (4q)^(90q/alpha).
Rank one uses the existing partition proof and needs no lower size bound.
-/

open Finset

noncomputable section

namespace Arxiv2411_18291

theorem hasDecomposition_complete_succ_paper_threshold {q r n : ℕ}
    (hr : 1 ≤ r) (hqr : r + 1 < q)
    (hn : paperSizeThreshold q (r + 1) ≤ n) :
    Divisible q (complete (Fin n) (r + 1)) →
      HasDecomposition q (complete (Fin n) (r + 1)) := by
  intro hdiv
  obtain ⟨R, hR, hcover⟩ := exists_reserve_cover_decompositions_paper_threshold q r n hqr hn
  obtain ⟨A, habs, hA⟩ := exists_sparse_absorber_paper_threshold hqr hn R hR
  let G := complete (Fin n) (r + 1) \ (A ∪ R)
  have hhost := paper_threshold_regular_host hqr
    (by simpa only [Fintype.card_fin] using hn) A R
    (by simpa only [Fintype.card_fin, paperAlpha, paperRho] using hA)
    (by simpa only [Fintype.card_fin, paperRho] using hR)
  obtain ⟨hG, hdense⟩ := hhost
  obtain ⟨H, hHG, hdegrees⟩ := regularity_boost_paper_threshold q r n hqr hn G hG
  have hcliques : ∀ Q ∈ H, cliqueEdges (r + 1) Q ⊆ G := by
    intro Q hQ
    exact (mem_filter.mp (hHG hQ)).2
  obtain ⟨D, hDH, hD, hleave⟩ := exists_nibble_paper_threshold_of_three_le q r n hqr
    (three_le_clique_size (by omega) hqr) hn G H
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

theorem design_existence_paper_threshold {q r n : ℕ} (hr : 1 ≤ r) (hqr : r < q)
    (hn : paperSizeThreshold q r ≤ n) :
    Divisible q (complete (Fin n) r) → HasDecomposition q (complete (Fin n) r) := by
  cases r with
  | zero => omega
  | succ r =>
    by_cases hr0 : r = 0
    · subst r
      exact hasDecomposition_complete_one_of_divisible
    · exact hasDecomposition_complete_succ_paper_threshold (by omega) hqr hn

theorem hasDecomposition_iff_binomial_divisibility_paper_threshold {q r n : ℕ}
    (hr : 1 ≤ r) (hqr : r < q) (hn : paperSizeThreshold q r ≤ n) :
    HasDecomposition q (complete (Fin n) r) ↔
      ∀ i ≤ r, (q - i).choose (r - i) ∣ (n - i).choose (r - i) := by
  have hqn : q + r ≤ n := by
    calc
      _ ≤ 4 * q := by omega
      _ = (4 * q) ^ 1 := (pow_one _).symm
      _ ≤ (4 * q) ^ 2 := Nat.pow_le_pow_right (by omega) (by omega)
      _ ≤ paperSizeThreshold q r := paperSizeThreshold_ge_square hqr
      _ ≤ n := hn
  have hcriterion := complete_divisible_iff (V := Fin n) hqr.le
    (by simpa only [Fintype.card_fin] using hqn)
  simp only [Fintype.card_fin] at hcriterion
  exact ⟨fun h => hcriterion.mp h.divisible,
    fun h => design_existence_paper_threshold hr hqr hn (hcriterion.mpr h)⟩

end Arxiv2411_18291
