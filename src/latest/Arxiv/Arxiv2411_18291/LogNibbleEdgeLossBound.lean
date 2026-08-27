import Arxiv.Arxiv2411_18291.LogNibbleParameters
import Arxiv.Arxiv2411_18291.NibbleEdgeLossBound

/-! # Uniform increment and average-loss scales for logarithmic frozen edges -/

namespace Arxiv2411_18291.LogNibbleParameters

variable {k : ℕ} {a g D p₀ L : ℝ} (P : LogNibbleParameters k a g D p₀ L)

include P

theorem degree_step_abs (i : ℕ) (hi : p₀ ≤ removalDensity k g (i + 1)) :
    |logNibbleDegreeUpperComparison k a g D (i + 1) -
        logNibbleDegreeUpperComparison k a g D i| ≤
        2 * nibbleEdgeSlope k g D (removalDensity k g i) ∧
      |logNibbleDegreeLowerComparison k a g D (i + 1) -
        logNibbleDegreeLowerComparison k a g D i| ≤
        2 * nibbleEdgeSlope k g D (removalDensity k g i) := by
  have hstep := removalDensity_difference k g i
  obtain ⟨hs, hsp, hhalf, hp⟩ := P.consecutive_bounds hi hstep
  have hp1 := removalDensity_le_one k P.graph_pos i
  have hlarge : 8 * (k : ℝ) ^ 3 ≤ a ^ 2 * g := by
    have hh := P.many_edges
    have hpos : 0 ≤ (k : ℝ) ^ 3 := by positivity
    linarith only [hh, hpos]
  obtain ⟨hu, _, _, hl, _⟩ := logNibbleDegree_step_control P.rank P.graph_pos
    P.degree_pos.le hs hsp hp1 hhalf hstep (P.point_conditions hp hp1) hlarge
  exact ⟨hu, hl⟩

theorem clique_step_abs (i : ℕ) (hi : p₀ ≤ removalDensity k g (i + 1)) :
    |logNibbleCliqueUpperComparison k a g D (i + 1) -
        logNibbleCliqueUpperComparison k a g D i| ≤ 130 * (k : ℝ) ^ 3 * D ∧
      |logNibbleCliqueLowerComparison k a g D (i + 1) -
        logNibbleCliqueLowerComparison k a g D i| ≤ 130 * (k : ℝ) ^ 3 * D := by
  obtain ⟨_, _, hu, hl⟩ := P.clique_steps i hi
  have hB : 0 ≤ (k : ℝ) ^ 3 * D := by have h := P.degree_pos; positivity
  constructor <;> nlinarith only [hu, hl, hB]

theorem edge_increment_scale_le {p δ : ℝ}
    (hp : p₀ ≤ p) (hp1 : p ≤ 1) (hδ : |δ| ≤ 2 * nibbleEdgeSlope k g D p) :
    (k : ℝ) * L + |δ| ≤ nibbleEdgeStepBound k g D L := by
  have hmain := nibbleEdgeSlope_le k P.graph_pos P.degree_pos.le
    (P.floor_pos.trans_le hp).le hp1
  unfold nibbleEdgeStepBound
  apply add_le_add le_rfl
  calc
    _ ≤ 2 * nibbleEdgeSlope k g D p := hδ
    _ ≤ 2 * ((k : ℝ) ^ 2 * D / g) := mul_le_mul_of_nonneg_left hmain (by norm_num)
    _ = _ := by ring

theorem edge_average_loss_le {p x h : ℝ}
    (hp : p₀ ≤ p) (hp1 : p ≤ 1)
    (hx : x ≤ nibbleDegreeMain k D p + logNibbleDegreeError k a D p)
    (hhalf : nibbleCliqueMain k g D p / 2 ≤ h) :
    (x / h) * ((k - 1 : ℕ) : ℝ) *
      (nibbleDegreeMain k D p + logNibbleDegreeError k a D p) ≤ 8 * nibbleEdgeSlope k g D p := by
  have hk : 0 < k := by have h := P.rank; omega
  have hp0 := P.floor_pos.trans_le hp
  have hm := nibbleDegreeMain_pos (k := k) P.degree_pos hp0
  have hL := nibbleLogFactor_one_le k hp0 hp1
  have hu : 0 ≤ logNibbleDegreeError k a D p := by
    have hD := P.degree_pos
    unfold logNibbleDegreeError
    positivity
  have hum := ((P.point_conditions hp hp1).degree_bounds P.degree_pos.le).1
  have hh₀ := nibbleCliqueMain_pos hk P.graph_pos P.degree_pos hp0
  have hh := (half_pos hh₀).trans_le hhalf
  have hdegree : nibbleDegreeMain k D p + logNibbleDegreeError k a D p ≤
      2 * nibbleDegreeMain k D p := by linarith only [hum, hm]
  have hprod := mul_le_mul (hx.trans hdegree) hdegree (add_nonneg hm.le hu)
    (mul_nonneg (by norm_num) hm.le)
  have hprod' := mul_le_mul_of_nonneg_left hprod (Nat.cast_nonneg (k - 1) : (0 : ℝ) ≤ _)
  have hN := mul_le_mul_of_nonneg_right hprod' hh₀.le
  have hh' := mul_le_mul_of_nonneg_left hhalf
    (mul_nonneg (Nat.cast_nonneg (k - 1) : (0 : ℝ) ≤ _) (sq_nonneg (nibbleDegreeMain k D p)))
  rw [nibbleEdgeSlope_eq_main_ratio (by have h := P.rank; omega)
    P.graph_pos.ne' P.degree_pos.ne' hp0.ne']
  calc
    _ = (x * ((k - 1 : ℕ) : ℝ) *
        (nibbleDegreeMain k D p + logNibbleDegreeError k a D p)) / h := by ring
    _ ≤ (8 * ((k - 1 : ℕ) : ℝ) * nibbleDegreeMain k D p ^ 2) /
        nibbleCliqueMain k g D p := by
      apply (div_le_div_iff₀ hh hh₀).mpr
      nlinarith only [hN, hh']
    _ = _ := by ring

end Arxiv2411_18291.LogNibbleParameters
