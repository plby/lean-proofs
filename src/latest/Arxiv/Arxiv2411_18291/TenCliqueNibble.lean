import Arxiv.Arxiv2411_18291.SharpFiniteNibble
import Arxiv.Arxiv2411_18291.TwiceNibbleFloor

/-! # The original finite leave constant for every k at least ten -/

open Finset

noncomputable section

namespace Arxiv2411_18291

theorem exists_sparse_nibble_all_ranks_at_floor_sharp_paper_threshold {q r n : ℕ}
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
          (p₀ + (128 * (q.choose (r + 1) : ℝ) + 1) * (n : ℝ) ^ (-(ε / 3))) := by
  by_cases hr : 1 ≤ r
  · exact exists_sparse_nibble_at_floor_sharp_paper_threshold hr hqr hn hεhi hp hp₁ hF
      G H φ τ hG hφ hτ hHG hd
  · have hr0 : r = 0 := by omega
    subst r
    have hq : 3 ≤ q := by simpa only [Nat.zero_add, Nat.choose_one_right] using hk
    simpa only [Nat.zero_add, Nat.choose_one_right] using
      exists_sparse_rankOne_nibble_at_floor_sharp_paper_threshold hq hn hεhi
        (by simpa only [Nat.zero_add, Nat.choose_one_right] using hp) hp₁
        (by simpa only [Nat.zero_add, Nat.choose_one_right] using hF) G H τ hτ hHG hd

theorem exists_sparse_nibble_of_ten_le_clique_paper_threshold {q r n : ℕ}
    (hqr : r + 1 < q) (hk : 10 ≤ q.choose (r + 1))
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
          (3 * (n : ℝ) ^ (-(ε / (3 * (q.choose (r + 1) : ℝ))))) := by
  have hnNat : 1 ≤ n := (paperSizeThreshold_one_lt hqr).le.trans hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hnNat
  by_cases hp : (n : ℝ) ^ (-(ε / (3 * q.choose (r + 1)))) ≤ 1 / 3
  · obtain ⟨hF, hfinal⟩ := sparse_nibble_floor_of_twice_leave hnNat hk hp
    have hp0 := Real.rpow_nonneg hn0.le (-(ε / (3 * q.choose (r + 1))))
    obtain ⟨C, hC, hdec, hbound⟩ :=
      exists_sparse_nibble_all_ranks_at_floor_sharp_paper_threshold hqr (by omega) hn hεhi
        (by linarith only [hp0]) (by linarith only [hp]) hF G H φ τ hG hφ hτ hHG hd
    exact ⟨C, hC, hdec, hbound.mono hfinal⟩
  · exact exists_nibble_of_one_lt_leave hnNat (by linarith only [lt_of_not_ge hp]) G H

theorem exists_sparse_nibble_paper_threshold_of_extended_parameters {q r n : ℕ}
    (hqr : r + 1 < q)
    (hn : paperSizeThreshold q (r + 1) ≤ n) {ε : ℝ} (hεhi : ε ≤ 2 / 5)
    (hcovered : ε ≤ 0 ∨
      3 * (q.choose (r + 1) : ℝ) * paperRho q (r + 1) ≤ ε ∨ q = 2 ∨
        10 ≤ q.choose (r + 1))
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
          (3 * (n : ℝ) ^ (-(ε / (3 * (q.choose (r + 1) : ℝ))))) := by
  have hnNat : 1 ≤ n := (paperSizeThreshold_one_lt hqr).le.trans hn
  rcases hcovered with hε | hε | hq | hk
  · exact exists_nibble_of_nonpositive_error hnNat hε G H
  · exact exists_sparse_nibble_all_ranks_paper_threshold hqr hn hε hεhi
      G H φ τ hG hφ hτ hHG hd
  · subst q
    have hr0 : r = 0 := by omega
    subst r
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hnNat
    have hsize : (n : ℝ) ^ (2 / 3 : ℝ) ≤ G.card := by
      have hprod : (n : ℝ) ^ (2 / 3 : ℝ) = (n : ℝ) ^ (-(1 / 3 : ℝ)) * n := by
        rw [← Real.rpow_add_one hn0.ne']
        norm_num
      rw [hprod, hG]
      simpa only [Nat.zero_add, Nat.choose_one_right, Nat.cast_one, neg_div] using
        mul_le_mul_of_nonneg_right hφ hn0.le
    have hdegrees : ∀ e ∈ G,
        |((H.filter fun Q => e.val ⊆ Q.val).card : ℝ) - τ * n| ≤
          (n : ℝ) ^ (-ε) * (τ * n) := by
      simpa only [Nat.zero_add, Nat.reduceSub, Nat.choose_one_right] using hd
    simpa only [Nat.zero_add, Nat.choose_one_right, Nat.cast_ofNat,
      show (3 : ℝ) * 2 = 6 by norm_num] using
        exists_pair_nibble_paper_threshold hn hεhi G H τ hsize hτ hHG hdegrees
  · exact exists_sparse_nibble_of_ten_le_clique_paper_threshold hqr hk hn hεhi
      G H φ τ hG hφ hτ hHG hd

end Arxiv2411_18291
