import Arxiv.Arxiv2411_18291.RankOnePairPacking
import Arxiv.Arxiv2411_18291.AsymptoticNibbleParameters

/-! # The pair case of the paper's nibble lemma -/

open Finset Filter
open scoped Topology

noncomputable section

namespace Arxiv2411_18291

/-- Pair degrees near n/2 leave at most O(n^(2/3)) unmatched vertices.
Thus every fixed leave exponent below 1/3 is available eventually. -/
theorem eventually_exists_rankOne_pair_nibble {β : ℝ} (hβ : β < 1 / 3) :
    ∀ᶠ n : ℕ in atTop, ∀ (G : Hypergraph (Fin n) 1) (H : Finset (Block (Fin n) 2)),
      (∀ Q ∈ H, cliqueEdges 1 Q ⊆ G) →
      (∀ e ∈ G, |((H.filter fun Q => e.val ⊆ Q.val).card : ℝ) - (n : ℝ) / 2| ≤
        (n : ℝ) ^ (-(1 / 3 : ℝ)) * ((n : ℝ) / 2)) →
      ∃ D : Finset (Block (Fin n) 2), D ⊆ H ∧ IsDecomposition (cliqueSupport 1 D) D ∧
        IsGraphBounded (G \ cliqueSupport 1 D) ((n : ℝ) ^ (-β)) := by
  filter_upwards [eventually_ge_atTop (1 : ℕ),
    eventually_scaled_rpow_le 2 (by norm_num : (0 : ℝ) < 1)
      (show -(1 / 3 : ℝ) < -β by linarith only [hβ]),
    eventually_scaled_rpow_le 2 (by norm_num : (0 : ℝ) < 1)
      (show (0 : ℝ) < 1 - β by linarith only [hβ])]
    with n hn hscale hone
  simp only [Real.rpow_zero, mul_one, one_mul] at hscale hone
  intro G H hHG hd
  let δ := (1 - (n : ℝ) ^ (-(1 / 3 : ℝ))) * n / 2
  have hdegree : ∀ e ∈ G, δ ≤ ((H.filter fun Q => e.val ⊆ Q.val).card : ℝ) := by
    intro e he
    have hh := (abs_le.mp (hd e he)).1
    dsimp only [δ]
    linarith only [hh]
  obtain ⟨D, hDH, hD, hleave⟩ := exists_rankOne_pair_packing_leave_bound G H hHG δ hdegree
  refine ⟨D, hDH, hD, (isGraphBounded_one_iff _ _).mpr ?_⟩
  simp only [Fintype.card_fin]
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hprod : (n : ℝ) ^ (-β) * n = (n : ℝ) ^ (1 - β) := by
    rw [show 1 - β = -β + 1 by ring, Real.rpow_add hn0, Real.rpow_one]
  have hpos : (0 : ℝ) < (n : ℝ) ^ (-β) * n := by positivity
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
