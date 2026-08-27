import Arxiv.Arxiv2411_18291.PrescribedGreedyExistence
import Arxiv.Arxiv2411_18291.AsymptoticGreedyEmbedding

/-!
# Polynomial density scales for prescribed greedy choices

Write `η = n^(-a)` for candidate density, `θ = n^(-b)` for input root
density, and `θB = n^(-c)` for forbidden density. The finite criterion holds
eventually when `2*a < b`, `a < c`, and `b-a < 1`. The output degree scale
is then `4*r!*n^(-(b-a))` in the paper's rank notation.
-/

open Filter
open scoped Topology

noncomputable section

namespace Arxiv2411_18291

theorem rpow_density_ratio {x : ℝ} (hx : 0 < x) (a b : ℝ) :
    x ^ (-b) / x ^ (-a) = x ^ (-(b - a)) := by
  rw [← Real.rpow_sub hx]
  congr 1
  ring

theorem prescribed_smallness_scale {x : ℝ} (hx : 0 < x) (M C a b c : ℝ) :
    (M * (x ^ (-c) + M * (C * x ^ (-b) / x ^ (-a)))) / x ^ (-a) =
      M * (x ^ (-(c - a)) + M * (C * x ^ (-(b - 2 * a)))) := by
  have hratio : x ^ (-b) / x ^ (-a) / x ^ (-a) = x ^ (-(b - 2 * a)) := by
    rw [rpow_density_ratio hx a b, rpow_density_ratio hx a (b - a)]
    congr 1
    ring
  calc
    _ = M * (x ^ (-c) / x ^ (-a) + M * (C * (x ^ (-b) / x ^ (-a) / x ^ (-a)))) := by ring
    _ = _ := by rw [rpow_density_ratio hx a c, hratio]

theorem eventually_prescribed_greedy_numerics (M r : ℕ) {a b c : ℝ}
    (hba : 2 * a < b) (hca : a < c) (hb1 : b - a < 1) :
    ∀ᶠ n : ℕ in atTop, 0 < n ∧
      (M : ℝ) * ((n : ℝ) ^ (-c) + M *
        (4 * (r + 1).factorial * (n : ℝ) ^ (-b) / (n : ℝ) ^ (-a))) ≤ (n : ℝ) ^ (-a) / 2 ∧
      (M : ℝ) * (n.choose r : ℝ) *
        Real.exp (-((2 * (r + 1).factorial * (n : ℝ) ^ (-b) * n / (n : ℝ) ^ (-a)) / 3)) < 1 := by
  have hc : Tendsto (fun n : ℕ => (n : ℝ) ^ (-(c - a))) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (by linarith : 0 < c - a)).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
  have hb : Tendsto (fun n : ℕ => (n : ℝ) ^ (-(b - 2 * a))) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (by linarith : 0 < b - 2 * a)).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
  have hs : Tendsto (fun n : ℕ => (M : ℝ) * ((n : ℝ) ^ (-(c - a)) +
      M * (4 * (r + 1).factorial * (n : ℝ) ^ (-(b - 2 * a))))) atTop (𝓝 0) := by
    simpa only [mul_zero, zero_add] using
      (hc.add ((hb.const_mul (4 * ((r + 1).factorial : ℝ))).const_mul (M : ℝ))).const_mul (M : ℝ)
  filter_upwards [eventually_gt_atTop (0 : ℕ),
    hs.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)),
    (greedyFailure_power_tendsto M r hb1).eventually
      (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))] with n hn hsmall hfail
  have hx : (0 : ℝ) < n := by exact_mod_cast hn
  have hη : 0 < (n : ℝ) ^ (-a) := Real.rpow_pos_of_pos hx _
  refine ⟨hn, ?_, ?_⟩
  · have hdiv : ((M : ℝ) * ((n : ℝ) ^ (-c) + M *
        (4 * (r + 1).factorial * (n : ℝ) ^ (-b) / (n : ℝ) ^ (-a)))) / (n : ℝ) ^ (-a) ≤
        1 / 2 := by
      rw [prescribed_smallness_scale hx]
      exact hsmall.le
    have hm := (div_le_iff₀ hη).mp hdiv
    linarith
  · have hratio : 2 * ((r + 1).factorial : ℝ) * (n : ℝ) ^ (-b) * n / (n : ℝ) ^ (-a) =
        2 * (r + 1).factorial * (n : ℝ) ^ (-(b - a)) * n := by
      calc
        _ = 2 * ((r + 1).factorial : ℝ) * ((n : ℝ) ^ (-b) / (n : ℝ) ^ (-a)) * n := by ring
        _ = _ := by rw [rpow_density_ratio hx a b]
    rw [hratio]
    apply lt_of_le_of_lt _ hfail
    apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg M)
    exact_mod_cast Nat.choose_le_pow n r

variable {W : Type*} [Fintype W] [DecidableEq W] {F : Finset W} {r : ℕ}

theorem eventually_exists_prescribed_greedy_family (H : Hypergraph W (r + 1))
    (hadm : IsAdmissible H F) {a b c : ℝ} (hba : 2 * a < b) (hca : a < c) (hb1 : b - a < 1) :
    ∀ᶠ n : ℕ in atTop, ∀ t : ℕ, ∀ Φ : ℕ → F ↪ Fin n, ∀ A : CandidateFamilies Φ,
      ∀ B : Hypergraph (Fin n) (r + 1), IsGraphBounded B ((n : ℝ) ^ (-c)) →
      (∀ f ∈ H, ∀ hf : f.val ⊆ F,
        IsEdgeFamilyBounded (fun i : Fin t => rootImage (Φ i) f hf) ((n : ℝ) ^ (-b))) →
      HasCandidateLowerBound Φ A H (4 * (r + 1).factorial * (n : ℝ) ^ (-(b - a)))
        ((n : ℝ) ^ (-a)) t →
      ∃ ω : ℕ → EmbeddingState W (Fin n), ∃ Ψ : (i : Fin t) → EmbeddingExtension (Φ i),
        IsGreedyFamily (fun i => Φ i) H B Ψ (4 * (r + 1).factorial * (n : ℝ) ^ (-(b - a))) ∧
        (∀ i : Fin t, Ψ i ∈ A i (Preorder.frestrictLe (i : ℕ) ω)) ∧
        ∀ i : Fin t, ω (i + 1) = chosenEmbedding (Ψ i).val := by
  filter_upwards [eventually_prescribed_greedy_numerics H.card r hba hca hb1] with n hn
  intro t Φ A B hB hroots hA
  have hx : (0 : ℝ) < n := by exact_mod_cast hn.1
  have hscale : 4 * ((r + 1).factorial : ℝ) * (n : ℝ) ^ (-b) / (n : ℝ) ^ (-a) =
      4 * (r + 1).factorial * (n : ℝ) ^ (-(b - a)) := by
    rw [mul_div_assoc, rpow_density_ratio hx a b]
  have hA' : HasCandidateLowerBound Φ A H
      (4 * (r + 1).factorial * (n : ℝ) ^ (-b) / (n : ℝ) ^ (-a)) ((n : ℝ) ^ (-a)) t := by
    rw [hscale]
    exact hA
  obtain ⟨ω, Ψ, hΨ, hmem, hmatch⟩ := exists_prescribed_greedy_family Φ A H B hB
    (Real.rpow_nonneg (Nat.cast_nonneg n) _) (Real.rpow_nonneg (Nat.cast_nonneg n) _)
    (Real.rpow_pos_of_pos hx _) (by simpa only [Fintype.card_fin] using hn.1)
    (by simpa only [Fintype.card_fin] using hn.2.1) t hA' hadm hroots
    (by simpa only [Block, Fintype.card_finset_len, Fintype.card_fin] using hn.2.2)
  exact ⟨ω, Ψ, by simpa only [hscale] using hΨ, hmem, hmatch⟩

theorem eventually_exists_greedy_family_in_candidates (H : Hypergraph W (r + 1))
    (hadm : IsAdmissible H F) {a b c : ℝ} (hba : 2 * a < b) (hca : a < c) (hb1 : b - a < 1) :
    ∀ᶠ n : ℕ in atTop, ∀ t : ℕ, ∀ Φ : ℕ → F ↪ Fin n,
      ∀ A : (i : ℕ) → Finset (EmbeddingExtension (Φ i)),
      ∀ B : Hypergraph (Fin n) (r + 1), IsGraphBounded B ((n : ℝ) ^ (-c)) →
      (∀ f ∈ H, ∀ hf : f.val ⊆ F,
        IsEdgeFamilyBounded (fun i : Fin t => rootImage (Φ i) f hf) ((n : ℝ) ^ (-b))) →
      (∀ i < t, (n : ℝ) ^ (-a) * (n : ℝ) ^ (Fintype.card W - F.card) ≤ (A i).card) →
      ∃ Ψ : (i : Fin t) → EmbeddingExtension (Φ i),
        IsGreedyFamily (fun i => Φ i) H B Ψ (4 * (r + 1).factorial * (n : ℝ) ^ (-(b - a))) ∧
        ∀ i : Fin t, Ψ i ∈ A i := by
  filter_upwards [eventually_exists_prescribed_greedy_family H hadm hba hca hb1] with n hn
  intro t Φ A B hB hroots hsize
  have hA : HasCandidateLowerBound Φ (fun i _ => A i) H
      (4 * (r + 1).factorial * (n : ℝ) ^ (-(b - a))) ((n : ℝ) ^ (-a)) t := by
    intro i hi _ _ _
    simpa only [Fintype.card_fin] using hsize i hi
  obtain ⟨ω, Ψ, hΨ, hmem, _⟩ := hn t Φ (fun i _ => A i) B hB hroots hA
  exact ⟨Ψ, hΨ, hmem⟩

end Arxiv2411_18291
