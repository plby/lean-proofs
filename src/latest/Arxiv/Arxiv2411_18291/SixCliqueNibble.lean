import Arxiv.Arxiv2411_18291.FlexibleFiniteNibble
import Arxiv.Arxiv2411_18291.ScaledNibbleExponent

/-! # The original finite nibble leave for every k at least six -/

open Finset

noncomputable section

namespace Arxiv2411_18291

theorem exists_sparse_nibble_of_six_le_clique_paper_threshold {q r n : ℕ}
    (hqr : r + 1 < q) (hk : 6 ≤ q.choose (r + 1))
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
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hnNat
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hnNat
  let k := q.choose (r + 1)
  have hK : (6 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < k := by linarith only [hK]
  by_cases hεsmall : ε ≤ 1 / 4
  · let p := (n : ℝ) ^ (-(ε / (3 * (k : ℝ))))
    have hp0 : 0 < p := Real.rpow_pos_of_pos hn0 _
    by_cases hp : p ≤ 1 / 3
    · let η := scaledNibbleExponent n k ε
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
      obtain ⟨hF, hfinal⟩ := scaled_nibble_floor hk hp0.le hp
      obtain ⟨hb1, hcount, hedge⟩ := scaled_nibble_initial_margins hk hp0 hp
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
    · exact exists_nibble_of_one_lt_leave hnNat (by linarith only [lt_of_not_ge hp]) G H
  · have hcut : 3 * (k : ℝ) * paperRho q (r + 1) ≤ 1 / 4 := by
      change 3 * (k : ℝ) * (1 / (6 * (k : ℝ)) ^ 2) ≤ 1 / 4
      rw [← mul_div_assoc, mul_one]
      apply (div_le_iff₀ (by positivity)).mpr
      nlinarith only [hK]
    exact exists_sparse_nibble_all_ranks_paper_threshold hqr hn
      (hcut.trans (le_of_not_ge hεsmall)) hεhi G H φ τ hG hφ hτ hHG hd

theorem exists_sparse_nibble_paper_threshold_of_improved_parameters {q r n : ℕ}
    (hqr : r + 1 < q)
    (hn : paperSizeThreshold q (r + 1) ≤ n) {ε : ℝ} (hεhi : ε ≤ 2 / 5)
    (hcovered : ε ≤ 0 ∨
      3 * (q.choose (r + 1) : ℝ) * paperRho q (r + 1) ≤ ε ∨ q = 2 ∨
        6 ≤ q.choose (r + 1))
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
  · exact exists_sparse_nibble_of_six_le_clique_paper_threshold hqr hk hn hεhi
      G H φ τ hG hφ hτ hHG hd

end Arxiv2411_18291
