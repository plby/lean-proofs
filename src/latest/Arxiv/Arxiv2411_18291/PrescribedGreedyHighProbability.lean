import Arxiv.Arxiv2411_18291.PrescribedGreedySuccessProbability
import Arxiv.Arxiv2411_18291.GreedyHighProbabilityNumerics
import Arxiv.Arxiv2411_18291.AsymptoticPrescribedGreedy

/-!
# High-probability greedy embeddings at separate polynomial density scales

The event includes actual candidate membership, even when candidates depend
on the previous history. Every exponent below `1-(b-a)` is available in
the stretched-exponential failure bound.
-/

open Finset MeasureTheory Filter
open scoped Topology

noncomputable section

namespace Arxiv2411_18291

variable {W : Type*} [Fintype W] [DecidableEq W] {F : Finset W} {r : ℕ}

theorem eventually_prescribed_greedy_success_probability (H : Hypergraph W (r + 1))
    (hadm : IsAdmissible H F) {a b c β : ℝ}
    (hba : 2 * a < b) (hca : a < c) (hb1 : b - a < 1) (hβ : β < 1 - (b - a)) :
    ∀ᶠ n : ℕ in atTop, ∀ t : ℕ, ∀ Φ : ℕ → F ↪ Fin n, ∀ A : CandidateFamilies Φ,
      ∀ B : Hypergraph (Fin n) (r + 1), IsGraphBounded B ((n : ℝ) ^ (-c)) →
      (∀ f ∈ H, ∀ hf : f.val ⊆ F,
        IsEdgeFamilyBounded (fun i : Fin t => rootImage (Φ i) f hf) ((n : ℝ) ^ (-b))) →
      HasCandidateLowerBound Φ A H (4 * (r + 1).factorial * (n : ℝ) ^ (-(b - a)))
        ((n : ℝ) ^ (-a)) t →
      1 - Real.exp (-((n : ℝ) ^ β)) <
        (prescribedGreedyProbability Φ A H B
          (4 * (r + 1).factorial * (n : ℝ) ^ (-(b - a)))).real
            (prescribedGreedyFamilyEvent Φ A H B
              (4 * (r + 1).factorial * (n : ℝ) ^ (-(b - a))) t) := by
  filter_upwards [eventually_prescribed_greedy_numerics H.card r hba hca hb1,
    eventually_greedy_failure_lt_stretched_exp H.card r hb1 hβ] with n hn htail
  intro t Φ A B hB hroots hA
  have hx : (0 : ℝ) < n := by exact_mod_cast hn.1
  have hscale : 4 * ((r + 1).factorial : ℝ) * (n : ℝ) ^ (-b) / (n : ℝ) ^ (-a) =
      4 * (r + 1).factorial * (n : ℝ) ^ (-(b - a)) := by
    rw [mul_div_assoc, rpow_density_ratio hx a b]
  have hA' : HasCandidateLowerBound Φ A H
      (4 * (r + 1).factorial * (n : ℝ) ^ (-b) / (n : ℝ) ^ (-a)) ((n : ℝ) ^ (-a)) t := by
    rw [hscale]
    exact hA
  have hs := prescribed_greedy_family_success_probability Φ A H B hB
    (Real.rpow_nonneg (Nat.cast_nonneg n) _) (Real.rpow_nonneg (Nat.cast_nonneg n) _)
    (Real.rpow_pos_of_pos hx _) (by simpa only [Fintype.card_fin] using hn.1)
    (by simpa only [Fintype.card_fin] using hn.2.1) t hA' hadm hroots
  simp only [Block, Fintype.card_finset_len, Fintype.card_fin, hscale] at hs
  have hratio : 2 * ((r + 1).factorial : ℝ) * (n : ℝ) ^ (-b) * n / (n : ℝ) ^ (-a) =
      2 * (r + 1).factorial * (n : ℝ) ^ (-(b - a)) * n := by
    calc
      _ = 2 * ((r + 1).factorial : ℝ) * ((n : ℝ) ^ (-b) / (n : ℝ) ^ (-a)) * n := by ring
      _ = _ := by rw [rpow_density_ratio hx a b]
  rw [hratio] at hs
  have hf := htail ((n : ℝ) ^ (-(b - a))) le_rfl
  exact (sub_lt_sub_left hf 1).trans_le hs

end Arxiv2411_18291
