import Arxiv.Arxiv2411_18291.AsymptoticGreedyEmbedding

/-!
# Greedy placements uniformly over a density interval

The upper end of the density interval controls forbidden-edge collisions;
the lower end controls the concentration failure probability. Both finite
criteria therefore hold uniformly as the density increases during repeated
multiplicity-reduction rounds.
-/

open Finset Filter
open scoped Topology

noncomputable section

namespace Arxiv2411_18291

theorem eventually_uniform_greedy_numerics (w M r : ℕ) {σ ρ : ℝ}
    (hσ : 0 < σ) (hσρ : σ ≤ ρ) (hρ1 : ρ < 1) :
    ∀ᶠ n : ℕ in atTop, 0 < n ∧ 4 * w ^ 2 ≤ n ∧ ∀ θ : ℝ,
      (n : ℝ) ^ (-ρ) ≤ θ → θ ≤ (n : ℝ) ^ (-σ) →
      (M : ℝ) * (θ + M * (4 * (r + 1).factorial * θ)) ≤ 1 / 4 ∧
      (M : ℝ) * (n.choose r : ℝ) *
        Real.exp (-(2 * (r + 1).factorial * θ * n / 3)) < 1 := by
  filter_upwards [eventually_greedy_numerics w M r hσ (hσρ.trans_lt hρ1),
    eventually_greedy_numerics w M r (hσ.trans_le hσρ) hρ1] with n hupper hlower
  refine ⟨hupper.1, hupper.2.1, fun θ hlo hhi => ⟨?_, ?_⟩⟩
  · apply le_trans _ hupper.2.2.1
    gcongr
  · apply lt_of_le_of_lt _ hlower.2.2.2
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Real.exp_le_exp.mpr
    apply neg_le_neg
    have h := mul_le_mul_of_nonneg_right hlo
      (show 0 ≤ 2 * ((r + 1).factorial : ℝ) * n / 3 by positivity)
    nlinarith only [h]

variable {W : Type*} [Fintype W] [DecidableEq W] {F : Finset W} {r : ℕ}

omit [Fintype W] in
theorem eventually_exists_uniform_greedy_family [Finite W]
    (H : Hypergraph W (r + 1)) (hA : IsAdmissible H F) {σ ρ : ℝ}
    (hσ : 0 < σ) (hσρ : σ ≤ ρ) (hρ1 : ρ < 1) :
    ∀ᶠ n : ℕ in atTop, ∀ θ : ℝ, (n : ℝ) ^ (-ρ) ≤ θ → θ ≤ (n : ℝ) ^ (-σ) →
      ∀ t : ℕ, ∀ Φ : ℕ → F ↪ Fin n, ∀ B : Hypergraph (Fin n) (r + 1),
      IsGraphBounded B θ →
      (∀ f ∈ H, ∀ hf : f.val ⊆ F,
        IsEdgeFamilyBounded (fun i : Fin t => rootImage (Φ i) f hf) θ) →
      ∃ Ψ : (i : Fin t) → EmbeddingExtension (Φ i),
        IsGreedyFamily (fun i => Φ i) H B Ψ (4 * (r + 1).factorial * θ) := by
  let : Fintype W := Fintype.ofFinite W
  filter_upwards [eventually_uniform_greedy_numerics (Fintype.card W) H.card r hσ hσρ hρ1]
    with n hn
  intro θ hlo hhi t Φ B hB hroots
  have hθ : 0 ≤ θ := (Real.rpow_nonneg (Nat.cast_nonneg n) _).trans hlo
  obtain ⟨hsmall, hfail⟩ := hn.2.2 θ hlo hhi
  apply exists_greedy_family Φ H B hB hθ
    (by simpa only [Fintype.card_fin] using hn.2.1)
    (by simpa only [Fintype.card_fin] using hn.1)
    (by simpa only [Fintype.card_fin] using hsmall) t hA hroots
  simpa only [Block, Fintype.card_finset_len, Fintype.card_fin] using hfail

end Arxiv2411_18291
