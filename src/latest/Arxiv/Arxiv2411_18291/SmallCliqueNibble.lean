import Arxiv.Arxiv2411_18291.FiniteLogNibble

/-! # Constant-three finite nibble for clique sizes three, four, and five -/

open Finset

noncomputable section

namespace Arxiv2411_18291

theorem log_nibble_endpoint_le_three {k : ℕ} (hk : 3 ≤ k) {p : ℝ}
    (hp0 : 0 ≤ p) (hp : p ≤ 1 / 3) : (5 / 2 : ℝ) * p + 3 * p ^ k ≤ 3 * p := by
  have hpk : p ^ k ≤ p ^ 3 :=
    pow_le_pow_of_le_one hp0 (hp.trans (by norm_num)) hk
  have hp2 : p ^ 2 ≤ (1 / 9 : ℝ) := by
    have hh := pow_le_pow_left₀ hp0 hp 2
    norm_num at hh
    exact hh
  have hp3 := mul_le_mul_of_nonneg_right hp2 hp0
  nlinarith only [hpk, hp3, hp0]

theorem exists_sparse_nibble_of_small_clique_paper_threshold {q r n : ℕ}
    (hqr : r + 1 < q) (hk : 3 ≤ q.choose (r + 1)) (hk5 : q.choose (r + 1) ≤ 5)
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
  let k := q.choose (r + 1)
  let p := (n : ℝ) ^ (-(ε / (3 * (k : ℝ))))
  have hp0 : 0 < p := Real.rpow_pos_of_pos hn0 _
  by_cases hp : p ≤ 1 / 3
  · have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by dsimp [k]; omega)
    have hpow : p ^ k = (n : ℝ) ^ (-(ε / 3)) := by
      dsimp only [p]
      rw [← Real.rpow_mul_natCast hn0.le]
      congr 1
      field_simp
    have hfloor : p ≤ (2 / 5 : ℝ) * ((5 / 2 : ℝ) * p) := by linarith
    have hfloor1 : (5 / 2 : ℝ) * p ≤ 1 := by linarith only [hp]
    have hfinal : (5 / 2 : ℝ) * p + 3 * (n : ℝ) ^ (-(ε / 3)) ≤ 3 * p := by
      rw [← hpow]
      exact log_nibble_endpoint_le_three hk hp0.le hp
    have hpacking : ∃ C : Finset (Block (Fin n) q), C ⊆ H ∧
        IsDecomposition (cliqueSupport (r + 1) C) C ∧
          IsGraphBounded (G \ cliqueSupport (r + 1) C)
            ((5 / 2 : ℝ) * p + 3 * (n : ℝ) ^ (-(ε / 3))) := by
      by_cases hr : 1 ≤ r
      · exact exists_sparse_log_nibble_at_floor_paper_threshold hr hqr hk5 hn hεhi
          hfloor hfloor1 G H φ τ hG hφ hτ hHG hd
      · have hr0 : r = 0 := by omega
        subst r
        have hq : 3 ≤ q := by simpa only [Nat.zero_add, Nat.choose_one_right] using hk
        have hq5 : q ≤ 5 := by simpa only [Nat.zero_add, Nat.choose_one_right] using hk5
        simpa only [Nat.zero_add, Nat.choose_one_right] using
          exists_sparse_rankOne_log_nibble_at_floor_paper_threshold hq hq5 hn hεhi
            (by simpa only [p, k, Nat.zero_add, Nat.choose_one_right] using hfloor)
            hfloor1 G H τ hτ hHG hd
    obtain ⟨C, hC, hdec, hbound⟩ := hpacking
    exact ⟨C, hC, hdec, hbound.mono hfinal⟩
  · exact exists_nibble_of_one_lt_leave hnNat (by linarith only [lt_of_not_ge hp]) G H

end Arxiv2411_18291
