import Arxiv.Arxiv2411_18291.FractionalBoostCountBounds
import Arxiv.Arxiv2411_18291.FractionalBoostMassNumerics

/-! # Fractional regularization with the sharp decoder mass cost -/

open Finset

noncomputable section

namespace Arxiv2411_18291

theorem exists_fractional_boost_of_mass_counts (q r n : ℕ) (hqr : r + 1 < q)
    (hn : 0 < n) (G : Hypergraph (Fin n) (r + 1)) {ε : ℝ} (hε : 0 ≤ ε)
    (hcost : (2 : ℝ) ^ (r + 1) * q.choose (r + 1) * ε ≤ 1 / 2)
    (hcount : ∀ e ∈ G,
      |((rootedCliques G e q).card : ℝ) -
        (n : ℝ) ^ (q - (r + 1)) / (q - (r + 1)).factorial| ≤
          ε * ((n : ℝ) ^ (q - (r + 1)) / (q - (r + 1)).factorial))
    (hdecode : ∀ e ∈ G,
      |((rootedCliques G e (q + (r + 1))).card : ℝ) - (n : ℝ) ^ q / q.factorial| ≤
        (1 / 2) * ((n : ℝ) ^ q / q.factorial)) :
    ∃ p : Block (Fin n) q → ℝ, (∀ Q, 0 ≤ p Q ∧ p Q ≤ 1) ∧
      (∀ Q, ¬cliqueEdges (r + 1) Q ⊆ G → p Q = 0) ∧
      boundary (r + 1) p = fun e => if e ∈ G then
        ((n : ℝ) ^ (q - (r + 1)) / (q - (r + 1)).factorial) / 2 else 0 := by
  let d : ℝ := (n : ℝ) ^ (q - (r + 1)) / (q - (r + 1)).factorial
  let L : ℝ := (n : ℝ) ^ q / (2 * q.factorial)
  let Z (e : Block (Fin n) (r + 1)) :=
    (cliqueFamily G (q + (r + 1))).filter fun z => e.val ⊆ z.val
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hd : 0 ≤ d := by dsimp only [d]; positivity
  have hL : 0 < L := by dsimp only [L]; positivity
  obtain ⟨hroot, hZG, hsize, hcounts⟩ := fractional_boost_count_bounds q r n G hcount hdecode
  have hsmall : (ε * d / 2) / L *
      ((2 : ℝ) ^ (r + 1) * (Fintype.card (Fin n) - q).choose (r + 1)) ≤ 1 / 2 := by
    simpa only [d, L, Fintype.card_fin] using
      (fractionalBoost_mass_error_bound hqr.le hn hε).trans hcost
  exact exists_fractional_boost_of_decoder_mass hqr G Z hroot hZG
    (div_nonneg (mul_nonneg hε hd) (by norm_num)) hL hsize hcounts hsmall

end Arxiv2411_18291
