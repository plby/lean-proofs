import Arxiv.Arxiv2411_18291.SixCliqueNibble
import Arxiv.Arxiv2411_18291.SmallLeaveNibbleFloors

/-! # Constant three for every clique size in the small-leave regime -/

open Finset

noncomputable section

namespace Arxiv2411_18291

theorem exists_sparse_nibble_of_small_leave_of_three_le {q r n : ℕ}
    (hqr : r + 1 < q) (hk : 3 ≤ q.choose (r + 1))
    (hn : paperSizeThreshold q (r + 1) ≤ n) {ε : ℝ} (hεhi : ε ≤ 2 / 5)
    (hpleave : (n : ℝ) ^ (-(ε / (3 * (q.choose (r + 1) : ℝ)))) ≤ 1 / 15)
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
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hnNat
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hnNat
  let k := q.choose (r + 1)
  have hK : (3 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < k := by linarith only [hK]
  by_cases hεsmall : ε ≤ 1 / 4
  · let p := (n : ℝ) ^ (-(ε / (3 * (k : ℝ))))
    have hp0 : 0 < p := Real.rpow_pos_of_pos hn0 _
    have hp : p ≤ 1 / 15 := hpleave
    let η := scaledNibbleExponent n k ε
    obtain ⟨hεη, hηhi, hηa⟩ := scaled_nibble_exponent_paper_threshold
      (Nat.succ_le_iff.mpr (Nat.succ_pos r)) hqr hn hεsmall
    have hpow : p ^ k = (n : ℝ) ^ (-(ε / 3)) := by
      dsimp only [p]
      rw [← Real.rpow_mul_natCast hn0.le]
      congr 1
      field_simp
    have hb : (n : ℝ) ^ (-ε) = (p ^ k) ^ 3 := by
      rw [hpow, ← Real.rpow_mul_natCast hn0.le]
      congr 1
      ring
    have ha : (n : ℝ) ^ (-(η / 3)) = scaledNibbleError k p := by
      change (n : ℝ) ^ (-(η / 3)) = 2 / (5 * (k : ℝ)) * p ^ k
      rw [hpow]
      exact hηa
    obtain ⟨hF, hfinal, hb1, hcount, hedge⟩ := scaled_nibble_small_leave_conditions hk hp0 hp
    rw [← ha] at hF hfinal hcount hedge
    rw [← hb] at hb1 hcount hedge
    have hpη : (n : ℝ) ^ (-(η / (3 * (k : ℝ)))) ≤ 2 * p := by
      calc
        _ ≤ p := Real.rpow_le_rpow_of_exponent_le hn1
          (neg_le_neg (div_le_div_of_nonneg_right hεη (by positivity)))
        _ ≤ _ := by linarith only [hp0]
    obtain ⟨C, hC, hdec, hbound⟩ :=
      exists_sparse_nibble_all_ranks_at_floor_flexible_paper_threshold hqr (by omega) hn
        hηhi hpη (by linarith only [hp]) hF hb1 hcount hedge G H φ τ hG hφ hτ hHG hd
    exact ⟨C, hC, hdec, hbound.mono hfinal⟩
  · have hcut : 3 * (k : ℝ) * paperRho q (r + 1) ≤ 1 / 4 := by
      change 3 * (k : ℝ) * (1 / (6 * (k : ℝ)) ^ 2) ≤ 1 / 4
      rw [← mul_div_assoc, mul_one]
      apply (div_le_iff₀ (by positivity)).mpr
      nlinarith only [hK]
    exact exists_sparse_nibble_all_ranks_paper_threshold hqr hn
      (hcut.trans (le_of_not_ge hεsmall)) hεhi G H φ τ hG hφ hτ hHG hd

theorem exists_sparse_nibble_paper_threshold_of_small_leave {q r n : ℕ}
    (hqr : r + 1 < q)
    (hn : paperSizeThreshold q (r + 1) ≤ n) {ε : ℝ} (hεhi : ε ≤ 2 / 5)
    (hpleave : (n : ℝ) ^ (-(ε / (3 * (q.choose (r + 1) : ℝ)))) ≤ 1 / 15)
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
  by_cases hq : q = 2
  · exact exists_sparse_nibble_paper_threshold_of_improved_parameters hqr hn hεhi
      (Or.inr (Or.inr (Or.inl hq))) G H φ τ hG hφ hτ hHG hd
  · have hk : 3 ≤ q.choose (r + 1) := by
      by_cases hr : 1 ≤ r
      · exact three_le_clique_size (by omega) hqr
      · have hr0 : r = 0 := by omega
        simp only [hr0, Nat.zero_add, Nat.choose_one_right]
        omega
    exact exists_sparse_nibble_of_small_leave_of_three_le hqr hk hn hεhi hpleave
      G H φ τ hG hφ hτ hHG hd

end Arxiv2411_18291
