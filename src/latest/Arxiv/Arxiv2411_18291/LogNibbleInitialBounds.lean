import Arxiv.Arxiv2411_18291.LogNibbleGoodTrend
import Arxiv.Arxiv2411_18291.NibbleInitialBounds

/-! # Original degree regularity starts every logarithmic track below its window -/

open Finset

noncomputable section

namespace Arxiv2411_18291

namespace CliqueRemovalProcess

variable {V : Type*} [Fintype V] [DecidableEq V] {q r : ℕ}

theorem log_nibble_initial_below_critical (hqr : r + 1 < q) (G : Hypergraph V (r + 1))
    (H : Finset (Block V q)) (hHG : ∀ Q ∈ H, cliqueEdges (r + 1) Q ⊆ G) {a D p₀ : ℝ}
    (P : LogNibbleParameters (q.choose (r + 1)) a G.card D p₀
      ((Fintype.card V : ℝ) ^ (q - (r + 1) - 1)))
    (hd : ∀ e ∈ G, |((H.filter fun Q => e.val ⊆ Q.val).card : ℝ) - D| ≤ a ^ 3 * D)
    (t : NibbleTrack V r) (ω : ℕ → State V q) :
    logNibbleTrackedProcess G H a D t 0 ω < -nibbleCriticalWidth G a D t := by
  let k := q.choose (r + 1)
  have hk : (3 : ℝ) ≤ k := by exact_mod_cast P.rank
  have hk0 : (0 : ℝ) < k := by linarith only [hk]
  have ha := P.error_pos
  have hD := P.degree_pos
  have hg := P.graph_pos
  have ha1 : a ≤ 1 := P.error_le_one
  have wE : 0 < a ^ 2 * D := by positivity
  have wH : 0 < a ^ 3 * D * (G.card : ℝ) := by positivity
  have hwidth : a ^ 3 * D ≤ a ^ 2 * D := by
    have h := mul_le_mul_of_nonneg_right ha1 (sq_nonneg a)
    have h' := mul_le_mul_of_nonneg_right h hD.le
    nlinarith only [h']
  have hcount := clique_count_deviation_of_degrees hqr.le G H hHG D (a ^ 3 * D) hd
  have hfrac : a ^ 3 * D * (G.card : ℝ) / (k : ℝ) ≤ a ^ 3 * D * G.card := by
    apply (div_le_iff₀ hk0).mpr
    have h := mul_le_mul_of_nonneg_left (by linarith only [hk] : (1 : ℝ) ≤ k) wH.le
    simpa only [mul_one] using h
  have hcmargin : 2 * (a ^ 3 * D * (G.card : ℝ)) <
      4 * (a ^ 3 * D * G.card) := by
    exact mul_lt_mul_of_pos_right (by nlinarith only [hk] : (2 : ℝ) < 4) wH
  have hcstart := initial_tracking_sides (hcount.trans hfrac) hcmargin
  rcases t with b | (⟨e, b⟩ | f)
  · cases b
    · change -cliqueCountProcess (r + 1) H (logNibbleCliqueLowerComparison k a G.card D) 0 ω < _
      rw [cliqueCountProcess_zero]
      simp only [nibbleCriticalWidth, logNibbleCliqueLowerComparison, removalDensity_zero,
        logNibbleCliqueLower, nibbleCliqueMain, logNibbleCliqueError, nibbleLogFactor,
        Real.log_one, mul_zero, sub_zero,
        one_pow, mul_one]
      nlinarith only [hcstart.2]
    · change cliqueCountProcess (r + 1) H (logNibbleCliqueUpperComparison k a G.card D) 0 ω < _
      rw [cliqueCountProcess_zero]
      simp only [nibbleCriticalWidth, logNibbleCliqueUpperComparison, removalDensity_zero,
        logNibbleCliqueUpper, nibbleCliqueMain, logNibbleCliqueError, nibbleLogFactor,
        Real.log_one, mul_zero, sub_zero,
        one_pow, mul_one]
      nlinarith only [hcstart.1]
  · by_cases heG : e ∈ G
    · rw [logNibbleTrackedProcess_edge G H a D e b 0 heG]
      have hmargin : 2 * (a ^ 2 * D) < 3 * (a ^ 2 * D) :=
        mul_lt_mul_of_pos_right (by linarith only [hk]) wE
      have hstart := initial_tracking_sides ((hd e heG).trans hwidth) hmargin
      cases b <;>
        simp only [Bool.false_eq_true, if_false, if_true, frozenEdgeProcess, range_zero,
          sum_empty, add_zero, nibbleCriticalWidth, logNibbleDegreeLowerComparison,
          logNibbleDegreeUpperComparison, removalDensity_zero, logNibbleDegreeLower,
          logNibbleDegreeUpper,
          nibbleDegreeMain, logNibbleDegreeError, nibbleLogFactor, Real.log_one, mul_zero, sub_zero,
          one_pow, mul_one]
      · nlinarith only [hstart.2]
      · nlinarith only [hstart.1]
    · rw [logNibbleTrackedProcess_nonedge G H a D e b 0 heG]
      change -2 * (a ^ 2 * D) < -(a ^ 2 * D)
      linarith only [wE]
  · obtain ⟨e, _⟩ := card_pos.mp (by exact_mod_cast hg : 0 < G.card)
    have hepos : 0 < e.val.card := by rw [e.property]; omega
    have hn : (0 : ℝ) < Fintype.card V := by exact_mod_cast hepos.trans_le (card_le_univ e.val)
    have hmargin := mul_lt_mul_of_pos_right (by linarith only [hk] : (1 : ℝ) < 2)
      (mul_pos ha hn)
    change faceCountProcess G f _ 0 ω < _
    rw [faceCountProcess_zero]
    simp only [nibbleCriticalWidth, logNibbleFaceUpperComparison, removalDensity_zero,
      logNibbleFaceUpper, one_mul]
    nlinarith only [hmargin]

end CliqueRemovalProcess

end Arxiv2411_18291
