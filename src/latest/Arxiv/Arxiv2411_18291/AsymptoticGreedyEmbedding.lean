import Arxiv.Arxiv2411_18291.GreedyEmbeddingExistence
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Greedy extension families at polynomially small density

For every fixed admissible pattern and exponent `0 < ρ < 1`, the explicit
finite greedy criterion holds for all sufficiently large ambient sizes
at `θ = n^(-ρ)`. Thus the numerical probability and choice-count conditions
are discharged, uniformly in the number of root maps and in their values.
-/

open Filter
open scoped Topology

noncomputable section

namespace Arxiv2411_18291

theorem greedyFailure_power_tendsto (M r : ℕ) {ρ : ℝ} (hρ : ρ < 1) :
    Tendsto (fun n : ℕ => (M : ℝ) * (n : ℝ) ^ r *
      Real.exp (-(2 * (r + 1).factorial * (n : ℝ) ^ (-ρ) * n / 3))) atTop (𝓝 0) := by
  have hα : 0 < 1 - ρ := by linarith
  have hC : 0 < 2 * ((r + 1).factorial : ℝ) / 3 := by positivity
  have ht := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
    ((r : ℝ) / (1 - ρ)) (2 * (r + 1).factorial / 3) hC).comp (tendsto_rpow_atTop hα)
  have hp : Tendsto (fun x : ℝ => x ^ r *
      Real.exp (-(2 * (r + 1).factorial * x ^ (-ρ) * x / 3))) atTop (𝓝 0) := by
    apply ht.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    dsimp only [Function.comp_def]
    rw [← Real.rpow_mul hx.le,
      show (1 - ρ) * ((r : ℝ) / (1 - ρ)) = r by field_simp, Real.rpow_natCast]
    rw [show 1 - ρ = -ρ + 1 by ring, Real.rpow_add hx, Real.rpow_one]
    congr 2
    ring
  simpa only [Function.comp_def, mul_zero, mul_assoc] using
    (hp.comp (tendsto_natCast_atTop_atTop (R := ℝ))).const_mul (M : ℝ)

theorem eventually_greedy_numerics (w M r : ℕ) {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ < 1) :
    ∀ᶠ n : ℕ in atTop, 0 < n ∧ 4 * w ^ 2 ≤ n ∧
      (M : ℝ) * ((n : ℝ) ^ (-ρ) + M * (4 * (r + 1).factorial * (n : ℝ) ^ (-ρ))) ≤ 1 / 4 ∧
      (M : ℝ) * (n.choose r : ℝ) *
        Real.exp (-(2 * (r + 1).factorial * (n : ℝ) ^ (-ρ) * n / 3)) < 1 := by
  have hθlim : Tendsto (fun n : ℕ => (n : ℝ) ^ (-ρ)) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop hρ).comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hsmall : Tendsto (fun n : ℕ => (M : ℝ) * ((n : ℝ) ^ (-ρ) +
      M * (4 * (r + 1).factorial * (n : ℝ) ^ (-ρ)))) atTop (𝓝 0) := by
    simpa only [mul_zero, zero_add] using
      (hθlim.add ((hθlim.const_mul (4 * ((r + 1).factorial : ℝ))).const_mul (M : ℝ))).const_mul
        (M : ℝ)
  filter_upwards [eventually_ge_atTop (max 1 (4 * w ^ 2)),
    hsmall.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4)),
    (greedyFailure_power_tendsto M r hρ1).eventually
      (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))] with n hn hs hf
  refine ⟨by have := (le_max_left 1 (4 * w ^ 2)).trans hn; omega,
    (le_max_right 1 (4 * w ^ 2)).trans hn, hs.le, ?_⟩
  apply lt_of_le_of_lt _ hf
  apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg M)
  exact_mod_cast Nat.choose_le_pow n r

variable {W : Type*} [Fintype W] [DecidableEq W] {F : Finset W} {r : ℕ}

omit [Fintype W] in
/-- Unconditional construction from bounded input data, for all sufficiently large sizes. -/
theorem eventually_exists_greedy_family [Finite W]
    (H : Hypergraph W (r + 1)) (hA : IsAdmissible H F)
    {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ < 1) :
    ∀ᶠ n : ℕ in atTop, ∀ t : ℕ, ∀ Φ : ℕ → F ↪ Fin n, ∀ B : Hypergraph (Fin n) (r + 1),
      IsGraphBounded B ((n : ℝ) ^ (-ρ)) →
      (∀ f ∈ H, ∀ hf : f.val ⊆ F,
        IsEdgeFamilyBounded (fun i : Fin t => rootImage (Φ i) f hf) ((n : ℝ) ^ (-ρ))) →
      ∃ Ψ : (i : Fin t) → EmbeddingExtension (Φ i),
        IsGreedyFamily (fun i => Φ i) H B Ψ (4 * (r + 1).factorial * (n : ℝ) ^ (-ρ)) := by
  let : Fintype W := Fintype.ofFinite W
  filter_upwards [eventually_greedy_numerics (Fintype.card W) H.card r hρ hρ1] with n hn
  intro t Φ B hB hroots
  apply exists_greedy_family Φ H B hB (Real.rpow_nonneg (Nat.cast_nonneg n) _)
    (by simpa only [Fintype.card_fin] using hn.2.1)
    (by simpa only [Fintype.card_fin] using hn.1)
    (by simpa only [Fintype.card_fin] using hn.2.2.1) t hA hroots
  simpa only [Block, Fintype.card_finset_len, Fintype.card_fin] using hn.2.2.2

end Arxiv2411_18291
