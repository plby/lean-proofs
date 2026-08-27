import Arxiv.Arxiv2411_18291.NibbleInitialBounds
import Arxiv.Arxiv2411_18291.SharpNibbleEndpoint

/-! # Initial nibble regularity with separate comparison and input errors -/

open Finset

noncomputable section

namespace Arxiv2411_18291

theorem initial_tracking_sides_of_separate_error {x M u w b : ℝ}
    (hdev : |x - M| ≤ b) (hu : b + w < u) :
    x - (M + u) < -w ∧ -(x - (M - u)) < -w := by
  obtain ⟨hlo, hhi⟩ := abs_le.mp hdev
  constructor <;> linarith only [hlo, hhi, hu]

namespace CliqueRemovalProcess

variable {V : Type*} [Fintype V] [DecidableEq V] {q r : ℕ}

theorem nibble_initial_below_critical_of_error (hqr : r + 1 < q) (G : Hypergraph V (r + 1))
    (H : Finset (Block V q)) (hHG : ∀ Q ∈ H, cliqueEdges (r + 1) Q ⊆ G) {a D p₀ b : ℝ}
    (P : NibbleComparisonParameters (q.choose (r + 1)) a G.card D p₀
      ((Fintype.card V : ℝ) ^ (q - (r + 1) - 1)))
    (hcount : b < (q.choose (r + 1) : ℝ) *
      (16 * (q.choose (r + 1) : ℝ) ^ 2 - 1) * a ^ 3)
    (hedge : b < (16 * (q.choose (r + 1) : ℝ) - 1) * a ^ 2)
    (hd : ∀ e ∈ G, |((H.filter fun Q => e.val ⊆ Q.val).card : ℝ) - D| ≤ b * D)
    (t : NibbleTrack V r) (ω : ℕ → State V q) :
    nibbleTrackedProcess G H a D t 0 ω < -nibbleCriticalWidth G a D t := by
  let k := q.choose (r + 1)
  have hk : (3 : ℝ) ≤ k := by exact_mod_cast P.rank
  have hk0 : (0 : ℝ) < k := by linarith only [hk]
  have ha := P.error_pos
  have hD := P.degree_pos
  have hg := P.graph_pos
  have wE : 0 < a ^ 2 * D := by positivity
  have hc : b / (k : ℝ) < (16 * (k : ℝ) ^ 2 - 1) * a ^ 3 := by
    apply (div_lt_iff₀ hk0).mpr
    nlinarith only [hcount]
  have hcmargin : b * D * (G.card : ℝ) / (k : ℝ) + a ^ 3 * D * G.card <
      16 * (k : ℝ) ^ 2 * (a ^ 3 * D * G.card) := by
    have hh : b / (k : ℝ) + a ^ 3 < 16 * (k : ℝ) ^ 2 * a ^ 3 := by
      linarith only [hc]
    have hh' := mul_lt_mul_of_pos_right hh (mul_pos hD hg)
    simp only [div_eq_mul_inv] at hh' ⊢
    nlinarith only [hh']
  have hdev := clique_count_deviation_of_degrees hqr.le G H hHG D (b * D) hd
  have hcstart := initial_tracking_sides_of_separate_error hdev hcmargin
  rcases t with side | (⟨e, side⟩ | f)
  · cases side
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
    · rw [nibbleTrackedProcess_edge G H a D e side 0 heG]
      have hmargin : b * D + a ^ 2 * D < 16 * (k : ℝ) * (a ^ 2 * D) := by
        have hh : b + a ^ 2 < 16 * (k : ℝ) * a ^ 2 := by linarith only [hedge]
        have hh' := mul_lt_mul_of_pos_right hh hD
        nlinarith only [hh']
      have hstart := initial_tracking_sides_of_separate_error (hd e heG) hmargin
      cases side <;>
        simp only [Bool.false_eq_true, if_false, if_true, frozenEdgeProcess, range_zero,
          sum_empty, add_zero, nibbleCriticalWidth, nibbleDegreeLowerComparison,
          nibbleDegreeUpperComparison, removalDensity_zero, nibbleDegreeLower, nibbleDegreeUpper,
          nibbleDegreeMain, nibbleDegreeError, nibbleEdgeScale, one_pow, mul_one, div_one]
      · nlinarith only [hstart.2]
      · nlinarith only [hstart.1]
    · rw [nibbleTrackedProcess_nonedge G H a D e side 0 heG]
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


theorem exists_packing_at_nibble_horizon_of_error (hqr : r + 1 < q)
    (G : Hypergraph V (r + 1)) (H : Finset (Block V q))
    (hHG : ∀ Q ∈ H, cliqueEdges (r + 1) Q ⊆ G) {a D p₀ b : ℝ}
    (P : NibbleComparisonParameters (q.choose (r + 1)) a G.card D p₀
      ((Fintype.card V : ℝ) ^ (q - (r + 1) - 1)))
    (Q : NibbleCountConditions (q.choose (r + 1)) a G.card D p₀
      ((Fintype.card V : ℝ) ^ (q - (r + 1) - 1)))
    (R : NibbleEndConditions (q.choose (r + 1)) a G.card (Fintype.card V) p₀ (q - r))
    (hb : b ≤ 1)
    (hcount : b < (q.choose (r + 1) : ℝ) *
      (16 * (q.choose (r + 1) : ℝ) ^ 2 - 1) * a ^ 3)
    (hedge : b < (16 * (q.choose (r + 1) : ℝ) - 1) * a ^ 2)
    (hd : ∀ e ∈ G, |((H.filter fun Q => e.val ⊆ Q.val).card : ℝ) - D| ≤ b * D)
    (hsmall : nibbleFailureBound q G a D (nibbleHorizon (q.choose (r + 1)) G.card p₀) < 1) :
    ∃ C : Finset (Block V q), C ⊆ H ∧ C.card = nibbleHorizon (q.choose (r + 1)) G.card p₀ ∧
      IsDecomposition (cliqueSupport (r + 1) C) C ∧
        IsGraphBounded (G \ cliqueSupport (r + 1) C)
          (p₀ + (128 * (q.choose (r + 1) : ℝ) + 1) * a) := by
  have hk : 0 < q.choose (r + 1) := by have h := P.rank; omega
  have hglobal := initial_degree_upper_bound G H hHG P.degree_pos.le hb hd
  exact exists_packing_of_nibble_bounds hqr G H hHG P Q hglobal _
    (nibbleHorizon_density_ge hk P.graph_pos P.floor_le_one)
    (nibble_all_width_gaps hqr G P R)
    (nibble_initial_below_critical_of_error hqr G H hHG P hcount hedge hd)
    hsmall P.horizon_face_density_lt_error.le

end CliqueRemovalProcess

end Arxiv2411_18291
