import Arxiv.Arxiv2411_18291.ConstantComplementCliqueCounts
import Arxiv.Arxiv2411_18291.FractionalBoostFromCounts

/-! # Fractional regularity boosting with a fixed positive complement bound -/

open Finset Filter
open scoped Topology

noncomputable section

namespace Arxiv2411_18291

theorem fractional_boost_constant_parameters {K A B : ℝ}
    (hK : 0 ≤ K) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    let ε := 1 / (4 * (K + 1))
    let θ := ε / (2 * (A + B + 1))
    0 < θ ∧ 0 < ε ∧ ε ≤ 1 / 2 ∧ K * ε ≤ 1 / 2 ∧ A * θ < ε ∧ B * θ < ε := by
  dsimp only
  let ε := 1 / (4 * (K + 1))
  let θ := ε / (2 * (A + B + 1))
  have hε : 0 < ε := by dsimp only [ε]; positivity
  have hθ : 0 < θ := by dsimp only [θ]; positivity
  have heq : (K + 1) * ε = 1 / 4 := by dsimp only [ε]; field_simp
  have htq : (A + B + 1) * θ = ε / 2 := by dsimp only [θ]; field_simp
  have hKε := mul_nonneg hK hε.le
  have hAθ := mul_nonneg hA hθ.le
  have hBθ := mul_nonneg hB hθ.le
  change 0 < θ ∧ 0 < ε ∧ ε ≤ 1 / 2 ∧ K * ε ≤ 1 / 2 ∧ A * θ < ε ∧ B * θ < ε
  refine ⟨hθ, hε, ?_, ?_, ?_, ?_⟩ <;>
    nlinarith only [heq, htq, hε, hθ, hKε, hAθ, hBθ]

theorem exists_constant_complement_fractional_boost (q r : ℕ) (hqr : r + 1 ≤ q) :
    ∃ θ : ℝ, 0 < θ ∧ ∀ᶠ n : ℕ in atTop, ∀ G : Hypergraph (Fin n) (r + 1),
      IsGraphBounded (complete (Fin n) (r + 1) \ G) θ →
      ∃ p : Block (Fin n) q → ℝ, (∀ Q, 0 ≤ p Q ∧ p Q ≤ 1) ∧
        (∀ Q, ¬cliqueEdges (r + 1) Q ⊆ G → p Q = 0) ∧
        boundary (r + 1) p = fun e => if e ∈ G then
          ((n : ℝ) ^ (q - (r + 1)) / (q - (r + 1)).factorial) / 2 else 0 := by
  let K := fractionalBoostConstant q (r + 1)
  let A : ℝ := (q + 1 : ℝ) * (q.choose r : ℝ)
  let B : ℝ := ((q + (r + 1) : ℕ) + 1 : ℝ) * ((q + (r + 1)).choose r : ℝ)
  let ε := 1 / (4 * (K + 1))
  let θ := ε / (2 * (A + B + 1))
  obtain ⟨hθ, hε, hhalf, hcost, hA, hB⟩ := fractional_boost_constant_parameters
    (fractionalBoostConstant_nonneg q (r + 1))
    (show 0 ≤ A by dsimp only [A]; positivity) (show 0 ≤ B by dsimp only [B]; positivity)
  change 0 < θ at hθ
  change 0 < ε at hε
  have hε1 : ε ≤ 1 := hhalf.trans (by norm_num)
  refine ⟨θ, hθ, ?_⟩
  filter_upwards [eventually_rootedClique_count_of_constant_complement q r (r + 1)
      hqr hθ.le hε hε1 hA,
    eventually_rootedClique_count_of_constant_complement (q + (r + 1)) r (r + 1)
      (by omega) hθ.le hε hε1 hB,
    eventually_ge_atTop (1 : ℕ)] with n hcount hdecode hn
  intro G hG
  apply exists_fractional_boost_of_relative_counts q r n hqr (by omega) G hε.le hhalf hcost
  · intro e _
    exact hcount G hG e
  · intro e _
    simpa only [Nat.add_sub_cancel_right] using hdecode G hG e

end Arxiv2411_18291
