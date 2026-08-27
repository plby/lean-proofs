import Arxiv.Arxiv2411_18291.GeneratorSplittingExistence
import Arxiv.Arxiv2411_18291.UniformGreedyEmbedding

/-!
# Splitting generators at every density in an interval

Repeated reduction rounds use the same ambient size while their degree
bound increases. The splitting construction works uniformly throughout
any fixed polynomial density interval inside `(0,1)`.
-/

open Finset Filter
open scoped Topology

noncomputable section

namespace Arxiv2411_18291

variable {W : Type*} [Fintype W] [DecidableEq W] {q r : ℕ}

theorem eventually_exists_uniform_generator_splitting (S : ExchangeSystem W q (r + 1))
    (hqr : r + 1 ≤ q) {σ ρ : ℝ} (hσ : 0 < σ) (hσρ : σ ≤ ρ) (hρ1 : ρ < 1) :
    ∀ᶠ n : ℕ in atTop, ∀ θ : ℝ, (n : ℝ) ^ (-ρ) ≤ θ → θ ≤ (n : ℝ) ^ (-σ) →
      ∀ D : Finset (Block (Fin n) q), IsCliqueFamilyBounded r D θ →
      Nonempty (GeneratorSplitting S D (θ + S.graph.card * (4 * (r + 1).factorial * θ))) := by
  have hadm := admissible_clique_root S.graph S.base hqr
    (S.positive_decomposition.clique_subset S.base_mem)
  filter_upwards [eventually_exists_uniform_greedy_family S.graph hadm hσ hσρ hρ1,
    eventually_ge_atTop (Fintype.card W)] with n hplace hn
  intro θ hlo hhi D hD
  exact exists_generator_splitting_of_greedy S hqr n
    ((Real.rpow_nonneg (Nat.cast_nonneg n) _).trans hlo) hn (hplace θ hlo hhi) D hD

end Arxiv2411_18291
