import Mathlib.Tactic
import Mathlib.Analysis.Normed.Affine.AddTorsor
import Util.IncidenceGeometry.Basic

open Classical
noncomputable section

lemma OneEdgeMiddleParametersFromEndpointRadii
    (a b : EuclideanSpace ℝ (Fin 2))
    (ra rb : ℝ)
    (hab : a ≠ b)
    (hra_pos : 0 < ra) (hrb_pos : 0 < rb)
    (hradii_sum_lt : ra + rb < dist a b) :
    ∃ t0 t1 : ℝ,
      0 < t0 ∧ t0 < t1 ∧ t1 < 1 ∧
        t0 * dist a b < ra ∧
        (1 - t1) * dist a b < rb ∧
        AffineMap.lineMap a b t0 ∈ Metric.ball a ra ∧
        AffineMap.lineMap a b t1 ∈ Metric.ball b rb ∧
        (∀ t : ℝ, t ∈ Set.Icc t0 t1 → t ∈ Set.Ioo (0 : ℝ) 1) := by
  classical
  have hdist_pos : 0 < dist a b := dist_pos.mpr hab
  have hden_pos : 0 < 2 * dist a b := by positivity
  let t0 : ℝ := ra / (2 * dist a b)
  let t1 : ℝ := 1 - rb / (2 * dist a b)
  have ht0_pos : 0 < t0 := by
    dsimp [t0]
    exact div_pos hra_pos hden_pos
  have hright_frac_pos : 0 < rb / (2 * dist a b) := by
    exact div_pos hrb_pos hden_pos
  have ht1_lt : t1 < 1 := by
    dsimp [t1]
    linarith
  have hsum_div_lt_one : (ra + rb) / (2 * dist a b) < 1 := by
    have hsum_lt_den : ra + rb < 2 * dist a b := by
      linarith
    exact (div_lt_one hden_pos).2 hsum_lt_den
  have ht0_lt_t1 : t0 < t1 := by
    have hsum_halves_lt_one :
        ra / (2 * dist a b) + rb / (2 * dist a b) < 1 := by
      rw [← add_div]
      exact hsum_div_lt_one
    dsimp [t0, t1]
    linarith
  have ht0_mul_eq : t0 * dist a b = ra / 2 := by
    dsimp [t0]
    field_simp [hdist_pos.ne']
  have ht0_mul_lt : t0 * dist a b < ra := by
    rw [ht0_mul_eq]
    linarith
  have hright_mul_eq : (1 - t1) * dist a b = rb / 2 := by
    dsimp [t1]
    field_simp [hdist_pos.ne']
    ring
  have hright_mul_lt : (1 - t1) * dist a b < rb := by
    rw [hright_mul_eq]
    linarith
  have hline_t0_ball_a : AffineMap.lineMap a b t0 ∈ Metric.ball a ra := by
    rw [Metric.mem_ball, dist_lineMap_left]
    simpa [Real.norm_eq_abs, abs_of_pos ht0_pos] using ht0_mul_lt
  have hline_t1_ball_b : AffineMap.lineMap a b t1 ∈ Metric.ball b rb := by
    rw [Metric.mem_ball, dist_lineMap_right]
    simpa [Real.norm_eq_abs, abs_of_pos (sub_pos.mpr ht1_lt)] using hright_mul_lt
  have hinterval_open :
      ∀ t : ℝ, t ∈ Set.Icc t0 t1 → t ∈ Set.Ioo (0 : ℝ) 1 := by
    intro t ht
    exact ⟨lt_of_lt_of_le ht0_pos ht.1, lt_of_le_of_lt ht.2 ht1_lt⟩
  exact ⟨t0, t1, ht0_pos, ht0_lt_t1, ht1_lt, ht0_mul_lt,
    hright_mul_lt, hline_t0_ball_a, hline_t1_ball_b, hinterval_open⟩
