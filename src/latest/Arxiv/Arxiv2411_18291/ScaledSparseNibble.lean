import Arxiv.Arxiv2411_18291.ScaledNibbleFloors
import Arxiv.Arxiv2411_18291.FiniteGeneralNibble

/-!
# Section 9 with uniform leave constant sixteen at the printed threshold

A larger stopping density preserves the original degree-error scale. This
reduces the earlier uniform constant 432 to 16 without increasing n0.
The previously proved ranges with constant three are unchanged.
-/

open Finset

noncomputable section

namespace Arxiv2411_18291

theorem exists_sparse_nibble_all_ranks_at_floor_paper_threshold {q r n : ℕ}
    (hqr : r + 1 < q) (hk : 3 ≤ q.choose (r + 1))
    (hn : paperSizeThreshold q (r + 1) ≤ n) {ε p₀ : ℝ}
    (hεhi : ε ≤ 2 / 5)
    (hp : (n : ℝ) ^ (-(ε / (3 * (q.choose (r + 1) : ℝ)))) ≤ p₀) (hp₁ : p₀ ≤ 1)
    (hF : NibbleFloorConditions (q.choose (r + 1)) ((n : ℝ) ^ (-(ε / 3))) p₀)
    (G : Hypergraph (Fin n) (r + 1)) (H : Finset (Block (Fin n) q))
    (φ τ : ℝ) (hG : (G.card : ℝ) = φ * (n.choose (r + 1) : ℝ))
    (hφ : (n : ℝ) ^ (-((r + 1 : ℕ) : ℝ) / 3) ≤ φ)
    (hτ : (n : ℝ) ^ (-(1 / 3 : ℝ)) ≤ τ)
    (hHG : ∀ Q ∈ H, cliqueEdges (r + 1) Q ⊆ G)
    (hd : ∀ e ∈ G,
      |((H.filter fun Q => e.val ⊆ Q.val).card : ℝ) - τ * (n.choose (q - (r + 1)) : ℝ)| ≤
        (n : ℝ) ^ (-ε) * (τ * (n.choose (q - (r + 1)) : ℝ))) :
    ∃ C : Finset (Block (Fin n) q), C ⊆ H ∧
      IsDecomposition (cliqueSupport (r + 1) C) C ∧
        IsGraphBounded (G \ cliqueSupport (r + 1) C)
          (3 * p₀) := by
  by_cases hr : 1 ≤ r
  · exact exists_sparse_nibble_at_floor_paper_threshold hr hqr hn hεhi hp hp₁ hF
      G H φ τ hG hφ hτ hHG hd
  · have hr0 : r = 0 := by omega
    subst r
    have hq : 3 ≤ q := by simpa only [Nat.zero_add, Nat.choose_one_right] using hk
    simpa only [Nat.zero_add, Nat.choose_one_right] using
      exists_sparse_rankOne_nibble_at_floor_paper_threshold hq hn hεhi
        (by simpa only [Nat.zero_add, Nat.choose_one_right] using hp) hp₁
        (by simpa only [Nat.zero_add, Nat.choose_one_right] using hF) G H τ hτ hHG hd


theorem exists_sparse_nibble_paper_threshold_sixteen {q r n : ℕ}
    (hqr : r + 1 < q)
    (hn : paperSizeThreshold q (r + 1) ≤ n) {ε : ℝ} (hεhi : ε ≤ 2 / 5)
    (G : Hypergraph (Fin n) (r + 1)) (H : Finset (Block (Fin n) q))
    (φ τ : ℝ) (hG : (G.card : ℝ) = φ * (n.choose (r + 1) : ℝ))
    (hφ : (n : ℝ) ^ (-((r + 1 : ℕ) : ℝ) / 3) ≤ φ)
    (hτ : (n : ℝ) ^ (-(1 / 3 : ℝ)) ≤ τ)
    (hHG : ∀ Q ∈ H, cliqueEdges (r + 1) Q ⊆ G)
    (hd : ∀ e ∈ G,
      |((H.filter fun Q => e.val ⊆ Q.val).card : ℝ) - τ * (n.choose (q - (r + 1)) : ℝ)| ≤
        (n : ℝ) ^ (-ε) * (τ * (n.choose (q - (r + 1)) : ℝ))) :
    ∃ C : Finset (Block (Fin n) q), C ⊆ H ∧
      IsDecomposition (cliqueSupport (r + 1) C) C ∧
        IsGraphBounded (G \ cliqueSupport (r + 1) C)
          (16 * (n : ℝ) ^ (-(ε / (3 * (q.choose (r + 1) : ℝ))))) := by
  have hnNat : 1 ≤ n := (paperSizeThreshold_one_lt hqr).le.trans hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hnNat
  have hle : 3 * (n : ℝ) ^ (-(ε / (3 * (q.choose (r + 1) : ℝ)))) ≤
      16 * (n : ℝ) ^ (-(ε / (3 * (q.choose (r + 1) : ℝ)))) :=
    mul_le_mul_of_nonneg_right (by norm_num) (Real.rpow_nonneg hn0.le _)
  by_cases hcovered : ε ≤ 0 ∨
      3 * (q.choose (r + 1) : ℝ) * paperRho q (r + 1) ≤ ε ∨ q = 2 ∨
        15 ≤ q.choose (r + 1)
  · obtain ⟨C, hC, hdec, hbound⟩ := exists_sparse_nibble_paper_threshold_of_covered_parameters
      hqr hn hεhi hcovered G H φ τ hG hφ hτ hHG hd
    exact ⟨C, hC, hdec, hbound.mono hle⟩
  · have hq3 : 3 ≤ q := by
      by_contra hh
      have hq2 : q = 2 := by omega
      exact hcovered (Or.inr (Or.inr (Or.inl hq2)))
    have hk : 3 ≤ q.choose (r + 1) := by
      by_cases hr : 1 ≤ r
      · exact three_le_clique_size (by omega) hqr
      · have hr0 : r = 0 := by omega
        simpa only [hr0, Nat.zero_add, Nat.choose_one_right] using hq3
    by_cases hp : (n : ℝ) ^ (-(ε / (3 * q.choose (r + 1)))) ≤ 1 / 16
    · have hF := sparse_nibble_floor_of_scaled_leave hnNat hk hp
      have hp0 := Real.rpow_nonneg hn0.le (-(ε / (3 * q.choose (r + 1))))
      obtain ⟨C, hC, hdec, hbound⟩ := exists_sparse_nibble_all_ranks_at_floor_paper_threshold
        hqr hk hn hεhi (by linarith only [hp0]) (by linarith only [hp])
        hF G H φ τ hG hφ hτ hHG hd
      refine ⟨C, hC, hdec, ?_⟩
      convert hbound using 1
      ring
    · exact exists_nibble_of_one_lt_leave hnNat (by linarith only [lt_of_not_ge hp]) G H


end Arxiv2411_18291
