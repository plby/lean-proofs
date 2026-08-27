import Arxiv.Arxiv2411_18291.InitialCliqueCount
import Arxiv.Arxiv2411_18291.NibbleGoodTrend

/-! # All tracks start below their critical intervals under initial degree regularity -/

open Finset

noncomputable section

namespace Arxiv2411_18291

theorem initial_tracking_sides {x M u w : ℝ} (hdev : |x - M| ≤ w) (hu : 2 * w < u) :
    x - (M + u) < -w ∧ -(x - (M - u)) < -w := by
  obtain ⟨hlo, hhi⟩ := abs_le.mp hdev
  constructor <;> linarith only [hlo, hhi, hu]

theorem initial_degree_upper_bound {V : Type*} [Fintype V] [DecidableEq V] {q r : ℕ}
    (G : Hypergraph V r) (H : Finset (Block V q)) (hHG : ∀ Q ∈ H, cliqueEdges r Q ⊆ G)
    {D b : ℝ} (hD : 0 ≤ D) (hb : b ≤ 1)
    (hd : ∀ e ∈ G, |((H.filter fun Q => e.val ⊆ Q.val).card : ℝ) - D| ≤ b * D) :
    ∀ e : Block V r, ((H.filter fun Q => e.val ⊆ Q.val).card : ℝ) ≤ 2 * D := by
  intro e
  by_cases he : e ∈ G
  · have h := (abs_le.mp (hd e he)).2
    have hbD := mul_le_mul_of_nonneg_right hb hD
    nlinarith only [h, hbD]
  · rw [clique_degree_zero_outside_graph G H hHG e he, Nat.cast_zero]
    positivity

namespace CliqueRemovalProcess

variable {V : Type*} [Fintype V] [DecidableEq V] {q r : ℕ}

theorem nibble_initial_below_critical (hqr : r + 1 < q) (G : Hypergraph V (r + 1))
    (H : Finset (Block V q)) (hHG : ∀ Q ∈ H, cliqueEdges (r + 1) Q ⊆ G) {a D p₀ : ℝ}
    (P : NibbleComparisonParameters (q.choose (r + 1)) a G.card D p₀
      ((Fintype.card V : ℝ) ^ (q - (r + 1) - 1)))
    (hd : ∀ e ∈ G, |((H.filter fun Q => e.val ⊆ Q.val).card : ℝ) - D| ≤ a ^ 3 * D)
    (t : NibbleTrack V r) (ω : ℕ → State V q) :
    nibbleTrackedProcess G H a D t 0 ω < -nibbleCriticalWidth G a D t := by
  let k := q.choose (r + 1)
  have hk : (3 : ℝ) ≤ k := by exact_mod_cast P.rank
  have hk0 : (0 : ℝ) < k := by linarith only [hk]
  have ha := P.error_pos
  have hD := P.degree_pos
  have hg := P.graph_pos
  have ha1 : a ≤ 1 := P.error_half.trans (by norm_num)
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
      16 * (k : ℝ) ^ 2 * (a ^ 3 * D * G.card) := by
    exact mul_lt_mul_of_pos_right (by nlinarith only [hk] : (2 : ℝ) < 16 * (k : ℝ) ^ 2) wH
  have hcstart := initial_tracking_sides (hcount.trans hfrac) hcmargin
  rcases t with b | (⟨e, b⟩ | f)
  · cases b
    · change -cliqueCountProcess (r + 1) H (nibbleCliqueLowerComparison k a G.card D) 0 ω < _
      rw [cliqueCountProcess_zero]
      simp only [nibbleCriticalWidth, nibbleCliqueLowerComparison, removalDensity_zero,
        nibbleCliqueLower, nibbleCliqueMain, nibbleCliqueError, one_pow, mul_one, div_one]
      nlinarith only [hcstart.2]
    · change cliqueCountProcess (r + 1) H (nibbleCliqueUpperComparison k a G.card D) 0 ω < _
      rw [cliqueCountProcess_zero]
      simp only [nibbleCriticalWidth, nibbleCliqueUpperComparison, removalDensity_zero,
        nibbleCliqueUpper, nibbleCliqueMain, nibbleCliqueError, one_pow, mul_one, div_one]
      nlinarith only [hcstart.1]
  · by_cases heG : e ∈ G
    · rw [nibbleTrackedProcess_edge G H a D e b 0 heG]
      have hmargin : 2 * (a ^ 2 * D) < 16 * (k : ℝ) * (a ^ 2 * D) :=
        mul_lt_mul_of_pos_right (by linarith only [hk]) wE
      have hstart := initial_tracking_sides ((hd e heG).trans hwidth) hmargin
      cases b <;>
        simp only [Bool.false_eq_true, if_false, if_true, frozenEdgeProcess, range_zero,
          sum_empty, add_zero, nibbleCriticalWidth, nibbleDegreeLowerComparison,
          nibbleDegreeUpperComparison, removalDensity_zero, nibbleDegreeLower, nibbleDegreeUpper,
          nibbleDegreeMain, nibbleDegreeError, nibbleEdgeScale, one_pow, mul_one, div_one]
      · nlinarith only [hstart.2]
      · nlinarith only [hstart.1]
    · rw [nibbleTrackedProcess_nonedge G H a D e b 0 heG]
      change -2 * (a ^ 2 * D) < -(a ^ 2 * D)
      linarith only [wE]
  · obtain ⟨e, _⟩ := card_pos.mp (by exact_mod_cast hg : 0 < G.card)
    have hepos : 0 < e.val.card := by rw [e.property]; omega
    have hn : (0 : ℝ) < Fintype.card V := by exact_mod_cast hepos.trans_le (card_le_univ e.val)
    have hmargin := mul_lt_mul_of_pos_right (by linarith only [hk] : (1 : ℝ) < 128 * k)
      (mul_pos ha hn)
    change faceCountProcess G f _ 0 ω < _
    rw [faceCountProcess_zero]
    simp only [nibbleCriticalWidth, nibbleFaceUpperComparison, removalDensity_zero,
      nibbleFaceUpper, one_mul]
    nlinarith only [hmargin]

end CliqueRemovalProcess

end Arxiv2411_18291
