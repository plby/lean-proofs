import Arxiv.Arxiv2411_18291.RankOnePairNibble
import Arxiv.Arxiv2411_18291.ExplicitNibbleMargins

/-! # The finite pair case of the paper's nibble -/

open Finset

noncomputable section

namespace Arxiv2411_18291

theorem exists_rankOne_pair_nibble_paper_threshold (n : ℕ)
    (hn : paperSizeThreshold 2 1 ≤ n) (G : Hypergraph (Fin n) 1)
    (H : Finset (Block (Fin n) 2)) (hHG : ∀ Q ∈ H, cliqueEdges 1 Q ⊆ G)
    (hd : ∀ e ∈ G, |((H.filter fun Q => e.val ⊆ Q.val).card : ℝ) - (n : ℝ) / 2| ≤
      (n : ℝ) ^ (-(1 / 3 : ℝ)) * ((n : ℝ) / 2)) :
    ∃ D : Finset (Block (Fin n) 2), D ⊆ H ∧ IsDecomposition (cliqueSupport 1 D) D ∧
      IsGraphBounded (G \ cliqueSupport 1 D) ((n : ℝ) ^ (-(1 / 24 : ℝ))) := by
  have hρ := paperRho_le_one_div_36 (by norm_num : 1 < 2)
  have hscale : 2 * (n : ℝ) ^ (-(1 / 3 : ℝ)) ≤ (n : ℝ) ^ (-(1 / 24 : ℝ)) := by
    simpa only [pow_zero, Nat.factorial_zero, Nat.cast_one, Nat.cast_ofNat, mul_one] using
      paper_nibble_scaled_monomial (C := 2) (j := 0) (d := 0)
        (by norm_num : 1 ≤ 1) (by norm_num : 1 < 2) hn
        (by norm_num) (by norm_num) (by norm_num) (u := -(1 / 3)) (v := -(1 / 24))
        (by linarith only [hρ])
  have hone : (2 : ℝ) ≤ (n : ℝ) ^ (1 - (1 / 24 : ℝ)) := by
    simpa only [pow_zero, Nat.factorial_zero, Nat.cast_one, Nat.cast_ofNat,
      mul_one, Real.rpow_zero] using
      paper_nibble_scaled_monomial (C := 2) (j := 0) (d := 0)
        (by norm_num : 1 ≤ 1) (by norm_num : 1 < 2) hn
        (by norm_num) (by norm_num) (by norm_num) (u := 0) (v := 1 - 1 / 24)
        (by linarith only [hρ])
  let δ := (1 - (n : ℝ) ^ (-(1 / 3 : ℝ))) * n / 2
  have hdegree : ∀ e ∈ G, δ ≤ ((H.filter fun Q => e.val ⊆ Q.val).card : ℝ) := by
    intro e he
    have hh := (abs_le.mp (hd e he)).1
    dsimp only [δ]
    linarith only [hh]
  obtain ⟨D, hDH, hD, hleave⟩ := exists_rankOne_pair_packing_leave_bound G H hHG δ hdegree
  refine ⟨D, hDH, hD, (isGraphBounded_one_iff _ _).mpr ?_⟩
  simp only [Fintype.card_fin]
  have hn0 : (0 : ℝ) < n := by
    exact_mod_cast Nat.zero_lt_one.trans
      ((paperSizeThreshold_one_lt (by norm_num : 1 < 2)).trans_le hn)
  have hprod : (n : ℝ) ^ (-(1 / 24 : ℝ)) * n = (n : ℝ) ^ (1 - (1 / 24 : ℝ)) := by
    rw [show (1 - (1 / 24 : ℝ)) = -(1 / 24) + 1 by ring,
      Real.rpow_add hn0, Real.rpow_one]
  have hpos : (0 : ℝ) < (n : ℝ) ^ (-(1 / 24 : ℝ)) * n := by positivity
  have hGcard : (G.card : ℝ) ≤ n := by
    exact_mod_cast (by simpa only [Fintype.card_fin] using card_rankOne_le G)
  have hscaled := mul_le_mul_of_nonneg_right hscale hn0.le
  apply hleave.trans_lt
  apply max_lt
  · rw [hprod]
    linarith only [hone]
  · dsimp only [δ]
    nlinarith only [hGcard, hscaled, hpos]

end Arxiv2411_18291
