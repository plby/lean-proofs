import Arxiv.Arxiv2411_18291.SmallPatternGreedy

/-! # Finite greedy embeddings uniformly over a density interval -/

noncomputable section

namespace Arxiv2411_18291

theorem small_pattern_uniform_greedy_numerics {q r n w M : ℕ}
    (hqr : r + 1 < q) (hn : paperSizeThreshold q (r + 1) ≤ n)
    (hw : w ≤ (4 * q) ^ (2 * q)) (hM : M ≤ (4 * q) ^ (2 * q))
    {θ : ℝ} (hlo : (n : ℝ) ^ (-(1 / 2 : ℝ)) ≤ θ)
    (hhi : θ ≤ (4 * q : ℝ) ^ (24 * q) * (n : ℝ) ^ (-(paperAlpha q (r + 1) / 3))) :
    0 < n ∧ 4 * w ^ 2 ≤ n ∧
      (M : ℝ) * (θ + M * (4 * (r + 1).factorial * θ)) ≤ 1 / 4 ∧
      (M : ℝ) * n.choose r * Real.exp (-(2 * (r + 1).factorial * θ * n / 3)) < 1 := by
  have hA : (1 : ℝ) ≤ (4 * q : ℝ) ^ (24 * q) :=
    one_le_pow₀ (by exact_mod_cast (show 1 ≤ 4 * q by omega))
  have hαupper := (paperAlpha_le_rho hqr).trans (paperRho_le_one_div_36 hqr)
  obtain ⟨hnpos, hsize, hsmall, _⟩ := small_pattern_greedy_numerics hqr hn hw hM
    hA le_rfl (ρ := paperAlpha q (r + 1) / 3) le_rfl (by linarith only [hαupper])
  have hθ : 0 ≤ θ := (Real.rpow_nonneg (Nat.cast_nonneg n) _).trans hlo
  refine ⟨hnpos, hsize, ?_, ?_⟩
  · apply le_trans _ hsmall
    gcongr
  · have hMsize : M ≤ n := hM.trans
      ((Nat.pow_le_pow_right (by omega) (by omega : 2 * q ≤ 90 * q)).trans
        ((boost_threshold_le_paper_threshold hqr).trans hn))
    exact absorber_greedy_failure_lt_one hqr hn hMsize hlo

theorem exists_small_pattern_uniform_greedy_family
    {W : Type*} [Fintype W] [DecidableEq W] {F : Finset W} {q r n : ℕ}
    (hqr : r + 1 < q) (hn : paperSizeThreshold q (r + 1) ≤ n)
    (hw : Fintype.card W ≤ (4 * q) ^ (2 * q))
    (H : Hypergraph W (r + 1)) (hH : H.card ≤ (4 * q) ^ (2 * q))
    (hadm : IsAdmissible H F) {θ : ℝ}
    (hlo : (n : ℝ) ^ (-(1 / 2 : ℝ)) ≤ θ)
    (hhi : θ ≤ (4 * q : ℝ) ^ (24 * q) * (n : ℝ) ^ (-(paperAlpha q (r + 1) / 3)))
    (t : ℕ) (Φ : ℕ → F ↪ Fin n) (B : Hypergraph (Fin n) (r + 1))
    (hB : IsGraphBounded B θ)
    (hroots : ∀ f ∈ H, ∀ hf : f.val ⊆ F,
      IsEdgeFamilyBounded (fun i : Fin t => rootImage (Φ i) f hf) θ) :
    ∃ Ψ : (i : Fin t) → EmbeddingExtension (Φ i),
      IsGreedyFamily (fun i => Φ i) H B Ψ (4 * (r + 1).factorial * θ) := by
  obtain ⟨hnpos, hsize, hsmall, hfailure⟩ :=
    small_pattern_uniform_greedy_numerics hqr hn hw hH hlo hhi
  have hθ : 0 ≤ θ := (Real.rpow_nonneg (Nat.cast_nonneg n) _).trans hlo
  exact exists_greedy_family Φ H B hB hθ
    (by simpa only [Fintype.card_fin] using hsize)
    (by simpa only [Fintype.card_fin] using hnpos) hsmall t hadm hroots
    (by simpa only [Block, Fintype.card_finset_len, Fintype.card_fin] using hfailure)

end Arxiv2411_18291
