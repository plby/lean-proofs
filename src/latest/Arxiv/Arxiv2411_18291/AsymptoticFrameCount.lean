import Arxiv.Arxiv2411_18291.FrameEmbeddingCount
import Arxiv.Arxiv2411_18291.FrameCountNumerics

/-!
# Polynomial density of eligible frame embeddings

Rooted clique families of density `c*n^(-γ)` give full pattern embeddings
of density `(3/4)*(c/2)^t*n^(-γ*t)`. Only the base map is fixed, and all
eligible frame assignments contribute to this lower bound.
-/

open Finset Filter
open scoped Topology

noncomputable section

namespace Arxiv2411_18291

variable {W : Type*} [Fintype W] [DecidableEq W] {a q t : ℕ}

theorem eventually_frameCandidateExtensions_density (F : Finset W) (Q : Fin t → Block W q)
    (haq : a < q)
    (hQ : Pairwise fun i j => Disjoint ((Q i).val \ F) ((Q j).val \ F))
    (hQsize : ∀ i, ((Q i).val \ F).card = q - a) {c γ : ℝ} (hc : 0 < c) (hγ : γ < 1) :
    ∀ᶠ n : ℕ in atTop, ∀ φ : F ↪ Fin n, ∀ e : ℕ → Block (Fin n) a,
      ∀ D : ℕ → Finset (Block (Fin n) q),
      (∀ i : Fin t, ∀ x : F, x.val ∈ (Q i).val → φ x ∈ (e i).val) →
      (∀ i, (e i).val ⊆ usedVertices φ) →
      (∀ i, ∀ T ∈ D i, (e i).val ⊆ T.val) →
      (∀ i < t, c * (n : ℝ) ^ (-γ) * (n : ℝ) ^ (q - a) ≤ (D i).card) →
      (((3 / 4 : ℝ) * (c / 2) ^ t) * (n : ℝ) ^ (-(γ * t))) *
        (n : ℝ) ^ (Fintype.card W - F.card) ≤
          (frameCandidateExtensions φ Q (fun i => D i)).card := by
  have hframe : (frameDomain F Q).card = F.card + t * (q - a) := by
    simpa only [Fintype.card_fin] using frameDomain_card F Q (q - a) hQ hQsize
  have hfw := card_le_univ (frameDomain F Q)
  have hexp : (q - a) * t + (Fintype.card W - (frameDomain F Q).card) =
      Fintype.card W - F.card := by
    rw [Nat.mul_comm (q - a) t]
    omega
  filter_upwards [eventually_ge_atTop (1 : ℕ),
    eventually_ge_atTop (4 * (Fintype.card W) ^ 2),
    eventually_frame_collision_bound (F.card + t * q) (q - a) (by omega) hc hγ]
      with n hn hnlarge hsmall
  intro φ e D hφ heB hD hsize
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hL : (0 : ℝ) ≤ c * (n : ℝ) ^ (-γ) * (n : ℝ) ^ (q - a) := by positivity
  have hb := frameCandidateExtensions_card_lower φ Q e D haq hQ hQsize hφ heB hD hL hsize
    (by simpa only [Fintype.card_fin] using hsmall)
    (by simpa only [Fintype.card_fin] using hnlarge)
  simp only [Fintype.card_fin] at hb
  rw [frame_completion_scale hnpos c γ (q - a) t, hexp] at hb
  exact hb

end Arxiv2411_18291
