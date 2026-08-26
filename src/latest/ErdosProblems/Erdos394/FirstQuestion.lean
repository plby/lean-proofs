import ErdosProblems.Erdos394.SqrtParameters

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Completion of the first question in Erdős Problem 394
-/

open Nat Finset Filter Asymptotics
open scoped Topology

namespace Erdos394

/-- Natural logarithm to every fixed base bigger than one tends to infinity. -/
theorem tendsto_natLog_atTop {b : ℕ} (hb : 1 < b) :
    Tendsto (Nat.log b) atTop atTop := by
  apply Filter.tendsto_atTop.mpr
  intro k
  filter_upwards [eventually_ge_atTop (b ^ k)] with n hn
  have hn0 : n ≠ 0 := by
    intro hnz
    subst n
    have : 0 < b ^ k := Nat.pow_pos (by omega)
    omega
  exact Nat.le_log_of_pow_le hb hn

/-- Grid exponent immediately above a real cutoff. -/
noncomputable def gridIndex (x : ℝ) : ℕ :=
  Nat.log 16 ⌊x⌋₊ + 1

/-- The grid exponent tends to infinity with the cutoff. -/
theorem tendsto_gridIndex_atTop : Tendsto gridIndex atTop atTop := by
  unfold gridIndex
  exact (Filter.tendsto_add_atTop_nat 1).comp <|
    (tendsto_natLog_atTop (b := 16) (by norm_num)).comp
      tendsto_nat_floor_atTop

/-- Pull the power-grid theorem back to arbitrary real cutoffs. -/
theorem eventually_Tsum_two_log_saving :
    ∀ᶠ x : ℝ in atTop,
      Tsum 2 x ≤
        7680 * x ^ 2 * Real.exp (-Real.log (Real.log x) / 2048) := by
  have hgrid := tendsto_gridIndex_atTop.eventually
    eventually_sum_t_two_pow_sixteen_le
  filter_upwards [eventually_ge_atTop (Real.exp 16), hgrid] with x hx hgrid
  let n : ℕ := ⌊x⌋₊
  let N : ℕ := gridIndex x
  have hxpos : 0 < x := (Real.exp_pos 16).trans_le hx
  have hxone : 1 < x :=
    (Real.one_lt_exp_iff.mpr (by norm_num : (0 : ℝ) < 16)).trans_le hx
  have hx1 : 1 ≤ x := hxone.le
  have hnpos : 0 < n := by
    dsimp [n]
    exact Nat.floor_pos.mpr hx1
  have hn0 : n ≠ 0 := hnpos.ne'
  have hNdef : N = Nat.log 16 n + 1 := rfl
  have hn_grid_lt : n < 16 ^ N := by
    dsimp [N, gridIndex, n]
    exact Nat.lt_pow_succ_log_self (by norm_num) _
  have hn_grid : n ≤ 16 ^ N := hn_grid_lt.le
  have hgrid_le_n : 16 ^ N ≤ 16 * n := by
    rw [hNdef, Nat.pow_succ']
    have hpow := Nat.pow_log_le_self 16 hn0
    nlinarith
  have hn_le_x : (n : ℝ) ≤ x := by
    dsimp [n]
    exact Nat.floor_le hxpos.le
  have hgrid_le_x : ((16 ^ N : ℕ) : ℝ) ≤ 16 * x := by
    exact (by exact_mod_cast hgrid_le_n : ((16 ^ N : ℕ) : ℝ) ≤ 16 * (n : ℝ)) |>.trans
      (mul_le_mul_of_nonneg_left hn_le_x (by norm_num))
  have hx_lt_floor : x < (n : ℝ) + 1 := by
    dsimp [n]
    exact Nat.lt_floor_add_one x
  have hfloor_succ_grid : n + 1 ≤ 16 ^ N := by omega
  have hx_grid : x < (16 ^ N : ℕ) :=
    hx_lt_floor.trans_le (by exact_mod_cast hfloor_succ_grid)
  have hlogx0 : 0 < Real.log x := Real.log_pos hxone
  have hlog_grid : Real.log x ≤ Real.log ((16 ^ N : ℕ) : ℝ) :=
    Real.log_le_log hxpos (le_of_lt hx_grid)
  have hlog16 : Real.log (16 : ℝ) = 4 * Real.log 2 := by
    rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]
    norm_num
  have hlog16lt : Real.log (16 : ℝ) < 4 := by
    rw [hlog16]
    have hlog2lt : Real.log 2 < 1 := by
      rw [Real.log_lt_iff_lt_exp (by norm_num : (0 : ℝ) < 2)]
      exact Real.exp_one_gt_two
    linarith
  have hlog_grid_eq : Real.log ((16 ^ N : ℕ) : ℝ) =
      (N : ℝ) * Real.log 16 := by
    rw [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]
  rw [hlog_grid_eq] at hlog_grid
  have hlogx_le_fourN : Real.log x ≤ 4 * (N : ℝ) := by
    have hN0 : (0 : ℝ) ≤ N := by positivity
    nlinarith
  have hlogx16 : (16 : ℝ) ≤ Real.log x := by
    have h := Real.log_le_log (Real.exp_pos 16) hx
    simpa using h
  have hsqrt_le_quarter : Real.sqrt (Real.log x) ≤ Real.log x / 4 := by
    have hsqrt0 := Real.sqrt_nonneg (Real.log x)
    have hsquare := Real.sq_sqrt hlogx0.le
    nlinarith
  have hsqrt_le_N : Real.sqrt (Real.log x) ≤ (N : ℝ) := by
    nlinarith
  have hNpos : (0 : ℝ) < N := lt_of_lt_of_le (Real.sqrt_pos.mpr hlogx0) hsqrt_le_N
  have hlogN_lower : Real.log (Real.log x) / 2 ≤ Real.log N := by
    rw [← Real.log_sqrt hlogx0.le]
    exact Real.log_le_log (Real.sqrt_pos.mpr hlogx0) hsqrt_le_N
  have hsaving : gridSaving N ≤
      Real.exp (-Real.log (Real.log x) / 2048) := by
    unfold gridSaving
    apply Real.exp_le_exp.mpr
    nlinarith
  have hTsumGrid : Tsum 2 x ≤
      ∑ m ∈ Finset.Icc 1 (16 ^ N), (t 2 m : ℝ) := by
    unfold Tsum
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro m hm
      have hm' := Finset.mem_Icc.mp hm
      exact Finset.mem_Icc.mpr ⟨hm'.1, hm'.2.trans hn_grid⟩
    · intro m hm hnot
      positivity
  calc
    Tsum 2 x ≤ ∑ m ∈ Finset.Icc 1 (16 ^ N), (t 2 m : ℝ) := hTsumGrid
    _ ≤ 30 * ((16 ^ N : ℕ) : ℝ) ^ 2 * gridSaving N := hgrid
    _ ≤ 30 * ((16 ^ N : ℕ) : ℝ) ^ 2 *
        Real.exp (-Real.log (Real.log x) / 2048) :=
      mul_le_mul_of_nonneg_left hsaving (by positivity)
    _ ≤ 7680 * x ^ 2 * Real.exp (-Real.log (Real.log x) / 2048) := by
      have hsquare : ((16 ^ N : ℕ) : ℝ) ^ 2 ≤ (16 * x) ^ 2 :=
        pow_le_pow_left₀ (by positivity) hgrid_le_x 2
      have hE0 : 0 ≤ Real.exp (-Real.log (Real.log x) / 2048) :=
        (Real.exp_pos _).le
      nlinarith [mul_le_mul_of_nonneg_right hsquare hE0]

/-- The first question has an affirmative answer, with the explicit choice
`c=1/2048`. -/
theorem erdos394_first_question_proved : FirstQuestion := by
  refine ⟨(1 : ℝ) / 2048, by norm_num, ?_⟩
  apply Asymptotics.IsBigO.of_bound 7680
  filter_upwards [eventually_Tsum_two_log_saving,
    eventually_ge_atTop (Real.exp 16)] with x hx hlarge
  have hxpos : 0 < x := (Real.exp_pos 16).trans_le hlarge
  have hlogx : 0 < Real.log x := Real.log_pos
    ((Real.one_lt_exp_iff.mpr (by norm_num : (0 : ℝ) < 16)).trans_le hlarge)
  have hT0 : 0 ≤ Tsum 2 x := by
    unfold Tsum
    positivity
  have htarget0 : 0 ≤ x ^ 2 / (Real.log x) ^ ((1 : ℝ) / 2048) := by
    positivity
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hT0,
    abs_of_nonneg htarget0]
  have heq : x ^ 2 / (Real.log x) ^ ((1 : ℝ) / 2048) =
      x ^ 2 * Real.exp (-Real.log (Real.log x) / 2048) := by
    rw [Real.rpow_def_of_pos hlogx, div_eq_mul_inv, ← Real.exp_neg]
    congr 2
    ring
  rw [heq]
  simpa [mul_assoc] using hx

end Erdos394
