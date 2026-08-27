import Arxiv.Arxiv2411_18291.SeparatedGreedyExistence
import Arxiv.Arxiv2411_18291.AsymptoticGreedyEmbedding

/-!
# Separated greedy placements at polynomial density

For any fixed pattern, conflict bound, and constant `C ≥ 1`, the finite
criterion holds eventually at density `C*n^(-ρ)`, `0<ρ<1`. Fixed constant
losses are retained rather than spent by weakening the density exponent.
-/

open Finset Filter
open scoped Topology

noncomputable section

namespace Arxiv2411_18291

theorem eventually_separated_greedy_numerics (w M r d : ℕ) {C ρ : ℝ}
    (hC : 1 ≤ C) (hρ : 0 < ρ) (hρ1 : ρ < 1) :
    ∀ᶠ n : ℕ in atTop, 0 < n ∧ 4 * w ^ 2 ≤ n ∧ 4 * w * (d * w) ≤ n ∧
      (M : ℝ) * (C * (n : ℝ) ^ (-ρ) + M *
        (8 * (r + 1).factorial * (C * (n : ℝ) ^ (-ρ)))) ≤ 1 / 4 ∧
      (M : ℝ) * (n.choose r : ℝ) *
        Real.exp (-(4 * (r + 1).factorial * (C * (n : ℝ) ^ (-ρ)) * n / 3)) < 1 := by
  have hθlim : Tendsto (fun n : ℕ => C * (n : ℝ) ^ (-ρ)) atTop (𝓝 0) := by
    have hbase : Tendsto (fun n : ℕ => (n : ℝ) ^ (-ρ)) atTop (𝓝 0) :=
      (tendsto_rpow_neg_atTop hρ).comp (tendsto_natCast_atTop_atTop (R := ℝ))
    simpa only [mul_zero] using hbase.const_mul C
  have hs : Tendsto (fun n : ℕ => (M : ℝ) * (C * (n : ℝ) ^ (-ρ) + M *
      (8 * (r + 1).factorial * (C * (n : ℝ) ^ (-ρ))))) atTop (𝓝 0) := by
    simpa only [mul_zero, zero_add] using
      (hθlim.add ((hθlim.const_mul (8 * ((r + 1).factorial : ℝ))).const_mul (M : ℝ))).const_mul
        (M : ℝ)
  filter_upwards [eventually_gt_atTop (0 : ℕ), eventually_ge_atTop (4 * w ^ 2),
    eventually_ge_atTop (4 * w * (d * w)),
    hs.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4)),
    (greedyFailure_power_tendsto M r hρ1).eventually
      (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))] with n hn hw hd hsmall hfail
  refine ⟨hn, hw, hd, hsmall.le, ?_⟩
  have hnonneg : (0 : ℝ) ≤ (r + 1).factorial * (n : ℝ) ^ (-ρ) * n := by positivity
  have hscale := mul_le_mul_of_nonneg_right hC hnonneg
  have hexp : Real.exp (-(4 * (r + 1).factorial * (C * (n : ℝ) ^ (-ρ)) * n / 3)) ≤
      Real.exp (-(2 * (r + 1).factorial * (n : ℝ) ^ (-ρ) * n / 3)) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  have hcoef : (M : ℝ) * (n.choose r : ℝ) ≤ M * (n : ℝ) ^ r := by
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg M)
    exact_mod_cast Nat.choose_le_pow n r
  exact (mul_le_mul hcoef hexp (Real.exp_pos _).le (by positivity)).trans_lt hfail

variable {W : Type*} [Fintype W] [DecidableEq W] {F : Finset W} {r : ℕ}

theorem eventually_exists_separated_greedy_family (H : Hypergraph W (r + 1))
    (hadm : IsAdmissible H F) (d : ℕ) {C ρ : ℝ} (hC : 1 ≤ C) (hρ : 0 < ρ) (hρ1 : ρ < 1) :
    ∀ᶠ n : ℕ in atTop, ∀ t : ℕ, ∀ Φ : ℕ → F ↪ Fin n, ∀ Rel : ℕ → ℕ → Prop,
      ∀ B : Hypergraph (Fin n) (r + 1),
      IsGraphBounded B (C * (n : ℝ) ^ (-ρ)) →
      (∀ i < t, (priorRelated Rel i).card ≤ d) →
      (∀ f ∈ H, ∀ hf : f.val ⊆ F,
        IsEdgeFamilyBounded (fun i : Fin t => rootImage (Φ i) f hf) (C * (n : ℝ) ^ (-ρ))) →
      ∃ Ψ : (i : Fin t) → EmbeddingExtension (Φ i),
        IsGreedyFamily (fun i => Φ i) H B Ψ (8 * (r + 1).factorial * (C * (n : ℝ) ^ (-ρ))) ∧
        ∀ i j : Fin t, i < j → Rel i j →
          Disjoint ((univ \ F).map (Ψ i).val) ((univ \ F).map (Ψ j).val) := by
  filter_upwards [eventually_separated_greedy_numerics (Fintype.card W) H.card r d hC hρ hρ1]
    with n hn
  intro t Φ Rel B hB hrel hroots
  have hCnonneg : 0 ≤ C := by linarith
  apply exists_separated_greedy_family Φ Rel H B hB (by positivity) t d hrel
    (by simpa only [Fintype.card_fin] using hn.1)
    (by simpa only [Fintype.card_fin] using hn.2.1)
    (by simpa only [Fintype.card_fin] using hn.2.2.1) hn.2.2.2.1 hadm hroots
  simpa only [Block, Fintype.card_finset_len, Fintype.card_fin] using hn.2.2.2.2

end Arxiv2411_18291
