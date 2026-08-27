import Arxiv.Arxiv2411_18291.GreedySuccessProbability
import Arxiv.Arxiv2411_18291.GreedyHighProbabilityNumerics

/-!
# High-probability construction of actual greedy extension families

The lower density bound may vary with n. A conservative explicit upper
density bound ensures the finite choice-count inequalities. The resulting
success probability is uniform in all root maps and their number.
-/

open Finset MeasureTheory Filter
open scoped Topology

noncomputable section

namespace Arxiv2411_18291

variable {W : Type*} [Fintype W] [DecidableEq W] {F : Finset W} {r : ℕ}

theorem eventually_greedy_success_probability (H : Hypergraph W (r + 1))
    (hA : IsAdmissible H F) {ρ β : ℝ} (hρ : ρ < 1) (hβ : β < 1 - ρ) :
    ∀ᶠ n : ℕ in atTop, ∀ t : ℕ, ∀ Φ : ℕ → F ↪ Fin n,
      ∀ B : Hypergraph (Fin n) (r + 1), ∀ θ : ℝ,
        (n : ℝ) ^ (-ρ) ≤ θ → θ ≤ greedyDensityBound H.card r →
        IsGraphBounded B θ →
        (∀ f ∈ H, ∀ hf : f.val ⊆ F,
          IsEdgeFamilyBounded (fun i : Fin t => rootImage (Φ i) f hf) θ) →
        1 - Real.exp (-((n : ℝ) ^ β)) <
          (greedyProbability Φ H B (4 * (r + 1).factorial * θ)).real
            (greedyFamilyEvent Φ H B (4 * (r + 1).factorial * θ) t) := by
  filter_upwards [eventually_ge_atTop (max 1 (4 * (Fintype.card W) ^ 2)),
    eventually_greedy_failure_lt_stretched_exp H.card r hρ hβ] with n hn htail
  intro t Φ B θ hlower hupper hB hroots
  have hn1 : 1 ≤ n := (le_max_left _ _).trans hn
  have hsize : 4 * (Fintype.card W) ^ 2 ≤ n := (le_max_right _ _).trans hn
  have hθ : 0 ≤ θ := (Real.rpow_nonneg (Nat.cast_nonneg n) _).trans hlower
  have hs := greedy_family_success_probability Φ H B hB hθ
    (by simpa only [Fintype.card_fin] using hsize)
    (by simpa only [Fintype.card_fin] using (show 0 < n by omega))
    (greedy_smallness_of_density_bound H.card r hupper) t hA hroots
  simp only [Block, Fintype.card_finset_len, Fintype.card_fin] at hs
  have hf := htail θ hlower
  exact (sub_lt_sub_left hf 1).trans_le hs

/-- The paper's lower density range with a valid stretched-exponential rate. -/
theorem eventually_greedy_whp_corrected (H : Hypergraph W (r + 1))
    (hA : IsAdmissible H F) :
    ∀ᶠ n : ℕ in atTop, ∀ t : ℕ, ∀ Φ : ℕ → F ↪ Fin n,
      ∀ B : Hypergraph (Fin n) (r + 1), ∀ θ : ℝ,
        (n : ℝ) ^ (-(1 / 2 : ℝ)) ≤ θ → θ ≤ greedyDensityBound H.card r →
        IsGraphBounded B θ →
        (∀ f ∈ H, ∀ hf : f.val ⊆ F,
          IsEdgeFamilyBounded (fun i : Fin t => rootImage (Φ i) f hf) θ) →
        1 - Real.exp (-((n : ℝ) ^ (1 / 10 : ℝ))) <
          (greedyProbability Φ H B (4 * (r + 1).factorial * θ)).real
            (greedyFamilyEvent Φ H B (4 * (r + 1).factorial * θ) t) :=
  eventually_greedy_success_probability H hA (by norm_num) (by norm_num)

end Arxiv2411_18291
