import Arxiv.Arxiv2411_18291.GeneratorSplittingExistence
import Arxiv.Arxiv2411_18291.FiniteUniformGreedy

/-! # Finite generator splitting uniformly over the working density range -/

noncomputable section

namespace Arxiv2411_18291

theorem exists_generator_splitting_paper_threshold
    {W : Type*} [Fintype W] [DecidableEq W] {q r n : ℕ}
    (S : ExchangeSystem W q (r + 1)) (hqr : r + 1 < q)
    (hn : paperSizeThreshold q (r + 1) ≤ n)
    (hw : Fintype.card W ≤ (4 * q) ^ (2 * q))
    (hS : S.graph.card ≤ (4 * q) ^ (2 * q)) {θ : ℝ}
    (hlo : (n : ℝ) ^ (-(1 / 2 : ℝ)) ≤ θ)
    (hhi : θ ≤ (4 * q : ℝ) ^ (24 * q) * (n : ℝ) ^ (-(paperAlpha q (r + 1) / 3)))
    (D : Finset (Block (Fin n) q)) (hD : IsCliqueFamilyBounded r D θ) :
    Nonempty (GeneratorSplitting S D (θ + S.graph.card * (4 * (r + 1).factorial * θ))) := by
  have hadm := admissible_clique_root S.graph S.base hqr.le
    (S.positive_decomposition.clique_subset S.base_mem)
  have hnW : Fintype.card W ≤ n := hw.trans
    ((Nat.pow_le_pow_right (by omega) (by omega : 2 * q ≤ 90 * q)).trans
      ((boost_threshold_le_paper_threshold hqr).trans hn))
  have hθ : 0 ≤ θ := (Real.rpow_nonneg (Nat.cast_nonneg n) _).trans hlo
  apply exists_generator_splitting_of_greedy S hqr.le n hθ hnW _ D hD
  intro t Φ B hB hroots
  exact exists_small_pattern_uniform_greedy_family hqr hn hw S.graph hS hadm
    hlo hhi t Φ B hB hroots

end Arxiv2411_18291
