import Arxiv.Arxiv2411_18291.FiniteSparseNibble

/-! # Finite nibble results without an error cutoff -/

open Finset

noncomputable section

namespace Arxiv2411_18291

theorem exists_sparse_nibble_all_ranks_of_floor_paper_threshold {q r n : ℕ}
    (hqr : r + 1 < q) (hk : 3 ≤ q.choose (r + 1))
    (hn : paperSizeThreshold q (r + 1) ≤ n) {ε : ℝ}
    (hε0 : 0 < ε) (hεhi : ε ≤ 2 / 5)
    (hF : NibbleFloorConditions (q.choose (r + 1)) ((n : ℝ) ^ (-(ε / 3)))
      ((n : ℝ) ^ (-(ε / (3 * q.choose (r + 1))))))
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
  by_cases hr : 1 ≤ r
  · exact exists_sparse_nibble_of_floor_paper_threshold hr hqr hn hε0 hεhi hF
      G H φ τ hG hφ hτ hHG hd
  · have hr0 : r = 0 := by omega
    subst r
    have hq : 3 ≤ q := by simpa only [Nat.zero_add, Nat.choose_one_right] using hk
    simpa only [Nat.zero_add, Nat.choose_one_right] using
      exists_sparse_rankOne_nibble_of_floor_paper_threshold hq hn hε0 hεhi
        (by simpa only [Nat.zero_add, Nat.choose_one_right] using hF) G H τ hτ hHG hd

theorem exists_sparse_nibble_of_large_clique_paper_threshold {q r n : ℕ}
    (hqr : r + 1 < q) (hk : 15 ≤ q.choose (r + 1))
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
  by_cases hε0 : 0 < ε
  · by_cases hp : (n : ℝ) ^ (-(ε / (3 * q.choose (r + 1)))) ≤ 1 / 3
    · exact exists_sparse_nibble_all_ranks_of_floor_paper_threshold hqr (by omega) hn
        hε0 hεhi (sparse_nibble_floor_of_small_leave hnNat hk hp)
        G H φ τ hG hφ hτ hHG hd
    · exact exists_nibble_of_one_lt_leave hnNat (by linarith only [lt_of_not_ge hp]) G H
  · exact exists_nibble_of_nonpositive_error hnNat (le_of_not_gt hε0) G H

theorem exists_sparse_nibble_paper_threshold_of_covered_parameters {q r n : ℕ}
    (hqr : r + 1 < q)
    (hn : paperSizeThreshold q (r + 1) ≤ n) {ε : ℝ} (hεhi : ε ≤ 2 / 5)
    (hcovered : ε ≤ 0 ∨
      3 * (q.choose (r + 1) : ℝ) * paperRho q (r + 1) ≤ ε ∨ q = 2 ∨
        15 ≤ q.choose (r + 1))
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
  · exact exists_sparse_nibble_of_large_clique_paper_threshold hqr hk hn hεhi
      G H φ τ hG hφ hτ hHG hd

theorem exists_sparse_nibble_paper_threshold_weaker {q r n : ℕ}
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
          (432 * (n : ℝ) ^ (-(ε / (3 * (q.choose (r + 1) : ℝ))))) := by
  have hnNat : 1 ≤ n := (paperSizeThreshold_one_lt hqr).le.trans hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hnNat
  have hle : 3 * (n : ℝ) ^ (-(ε / (3 * (q.choose (r + 1) : ℝ)))) ≤
      432 * (n : ℝ) ^ (-(ε / (3 * (q.choose (r + 1) : ℝ)))) :=
    mul_le_mul_of_nonneg_right (by norm_num) (Real.rpow_nonneg hn0.le _)
  by_cases hcovered : ε ≤ 0 ∨
      3 * (q.choose (r + 1) : ℝ) * paperRho q (r + 1) ≤ ε ∨ q = 2 ∨
        15 ≤ q.choose (r + 1)
  · obtain ⟨C, hC, hdec, hbound⟩ := exists_sparse_nibble_paper_threshold_of_covered_parameters
      hqr hn hεhi hcovered G H φ τ hG hφ hτ hHG hd
    exact ⟨C, hC, hdec, hbound.mono hle⟩
  · have hε0 : 0 < ε := by
      by_contra hh
      exact hcovered (Or.inl (le_of_not_gt hh))
    have hq3 : 3 ≤ q := by
      by_contra hh
      have hq2 : q = 2 := by omega
      exact hcovered (Or.inr (Or.inr (Or.inl hq2)))
    have hk : 3 ≤ q.choose (r + 1) := by
      by_cases hr : 1 ≤ r
      · exact three_le_clique_size (by omega) hqr
      · have hr0 : r = 0 := by omega
        simpa only [hr0, Nat.zero_add, Nat.choose_one_right] using hq3
    by_cases hp : (n : ℝ) ^ (-(ε / (3 * q.choose (r + 1)))) ≤ 1 / 432
    · have hF := sparse_nibble_floor_of_leave_le_one_div_432 hnNat hk hp
      obtain ⟨C, hC, hdec, hbound⟩ := exists_sparse_nibble_all_ranks_of_floor_paper_threshold
        hqr hk hn hε0 hεhi hF G H φ τ hG hφ hτ hHG hd
      exact ⟨C, hC, hdec, hbound.mono hle⟩
    · exact exists_nibble_of_one_lt_leave hnNat (by linarith only [lt_of_not_ge hp]) G H

end Arxiv2411_18291
