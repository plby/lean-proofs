import Arxiv.Arxiv2411_18291.SmallLeaveNibble

/-! # An explicit sufficient threshold for the exact Section 9 leave constant -/

open Finset

noncomputable section

namespace Arxiv2411_18291

theorem nibble_leave_le_one_div_fifteen {n k : ℕ} {ε : ℝ}
    (hk : 0 < k) (hε : 0 < ε)
    (hscale : (15 : ℝ) ^ (3 * (k : ℝ) / ε) ≤ n) :
    (n : ℝ) ^ (-(ε / (3 * (k : ℝ)))) ≤ 1 / 15 := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have heq : ((15 : ℝ) ^ (3 * (k : ℝ) / ε)) ^ (ε / (3 * (k : ℝ))) = 15 := by
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 15)]
    convert Real.rpow_one (15 : ℝ) using 1
    congr 1
    field_simp
  have hp : (15 : ℝ) ≤ (n : ℝ) ^ (ε / (3 * (k : ℝ))) := by
    rw [← heq]
    exact Real.rpow_le_rpow (Real.rpow_nonneg (by norm_num) _) hscale (by positivity)
  rw [Real.rpow_neg (Nat.cast_nonneg n)]
  simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 15) hp

def nibbleExactLeaveThreshold (q r : ℕ) (ε : ℝ) : ℕ :=
  max (paperSizeThreshold q r) ⌈(15 : ℝ) ^ (3 * (q.choose r : ℝ) / ε)⌉₊

theorem exists_sparse_nibble_exact_explicit {q r n : ℕ} {ε : ℝ}
    (hqr : r + 1 < q) (hn : nibbleExactLeaveThreshold q (r + 1) ε ≤ n)
    (hεhi : ε ≤ 2 / 5)
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
  have hn0 : paperSizeThreshold q (r + 1) ≤ n := (le_max_left _ _).trans hn
  by_cases hε : 0 < ε
  · have hceil : ⌈(15 : ℝ) ^ (3 * (q.choose (r + 1) : ℝ) / ε)⌉₊ ≤ n :=
      (le_max_right _ _).trans hn
    have hscale : (15 : ℝ) ^ (3 * (q.choose (r + 1) : ℝ) / ε) ≤ n :=
      (Nat.le_ceil _).trans (by exact_mod_cast hceil)
    exact exists_sparse_nibble_paper_threshold_of_small_leave hqr hn0 hεhi
      (nibble_leave_le_one_div_fifteen (Nat.choose_pos hqr.le) hε hscale)
      G H φ τ hG hφ hτ hHG hd
  · exact exists_nibble_of_nonpositive_error
      ((paperSizeThreshold_one_lt hqr).le.trans hn0) (le_of_not_gt hε) G H

end Arxiv2411_18291
