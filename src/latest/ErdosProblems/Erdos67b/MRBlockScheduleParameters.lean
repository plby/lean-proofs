import ErdosProblems.Erdos67b.MRBlockSchedule

/-!
# Consequences and feasibility of the uniform block schedule

The strengthened initial regime gives all scalar bounds needed by the
first-small-block class estimate. Its feasibility with arbitrarily small
initial logarithmic ratio follows from the proved little-oh logarithm bound.
-/

open Filter

namespace Erdos67b

theorem mrSchedule_delta_pos {eta : ℝ} (heta : 0 < eta) {j : ℕ} (hj : 1 ≤ j) :
    0 < eta / (2 * (j : ℝ) ^ 2) := by positivity

theorem mrSchedule_delta_le_one {eta : ℝ} (heta : eta ≤ 1 / 12)
    {j : ℕ} (hj : 1 ≤ j) : eta / (2 * (j : ℝ) ^ 2) ≤ 1 := by
  have hjr : (1 : ℝ) ≤ j := by exact_mod_cast hj
  apply (div_le_iff₀ (by positivity : 0 < 2 * (j : ℝ) ^ 2)).mpr
  nlinarith

theorem mrLogSchedule_block_gap
    {eta p₁ q₁ : ℝ} (heta : eta ≤ 1 / 12) (hp : 2 ≤ p₁)
    (hq : 1 ≤ q₁) (hlogq : 1 ≤ Real.log q₁)
    (hbudget : 4096 * Real.log q₁ ≤ eta * p₁) {j : ℕ} (hj : 2 ≤ j) :
    mrLogScheduleUpper q₁ (j - 1) + 1 ≤ mrLogScheduleLower p₁ q₁ j := by
  have hsep := mrLogSchedule_gap_separation hq hlogq hbudget hj
  have hd := mrSchedule_delta_le_one heta (show 1 ≤ j by omega)
  have hcur : 2 ≤ mrLogScheduleLower p₁ q₁ j :=
    hp.trans (mrLogScheduleLower_ge (by linarith) hq (by omega))
  have hlogq0 : 0 < q₁ := by linarith
  have hqbig : 2 ≤ q₁ := by
    have hl := Real.log_le_sub_one_of_pos hlogq0
    linarith
  have hprev : 2 ≤ mrLogScheduleUpper q₁ (j - 1) :=
    hqbig.trans (mrLogScheduleUpper_ge hq (by omega))
  have hlogj : 0 ≤ Real.log (j : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ j))
  have hm := mul_le_mul_of_nonneg_right hd (show 0 ≤ mrLogScheduleLower p₁ q₁ j by linarith)
  nlinarith

theorem mrLogScheduleUpper_mono_positive
    {eta p₁ q₁ : ℝ} (heta : eta ≤ 1 / 12) (hp : 2 ≤ p₁)
    (hq : 1 ≤ q₁) (hpq : p₁ ≤ q₁) (hlogq : 1 ≤ Real.log q₁)
    (hbudget : 4096 * Real.log q₁ ≤ eta * p₁) {i j : ℕ} (hi : 1 ≤ i) (hij : i ≤ j) :
    mrLogScheduleUpper q₁ i ≤ mrLogScheduleUpper q₁ j := by
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ k hik ih =>
    have hgap := mrLogSchedule_block_gap heta hp hq hlogq hbudget (j := k + 1) (by omega)
    simp only [Nat.add_sub_cancel] at hgap
    have hcur := mrLogScheduleLower_le_upper hq hpq (j := k + 1) (by omega)
    exact ih.trans (by linarith)

/-- Adjacent separation extends to every pair of distinct positive
block indices, so the full prime blocks are disjoint. -/
theorem mrLogSchedule_separated_of_lt
    {eta p₁ q₁ : ℝ} (heta : eta ≤ 1 / 12) (hp : 2 ≤ p₁)
    (hq : 1 ≤ q₁) (hpq : p₁ ≤ q₁) (hlogq : 1 ≤ Real.log q₁)
    (hbudget : 4096 * Real.log q₁ ≤ eta * p₁) {i j : ℕ} (hi : 1 ≤ i) (hij : i < j) :
    mrLogScheduleUpper q₁ i + 1 ≤ mrLogScheduleLower p₁ q₁ j := by
  have hprev := mrLogScheduleUpper_mono_positive heta hp hq hpq hlogq hbudget hi
    (show i ≤ j - 1 by omega)
  have hgap := mrLogSchedule_block_gap heta hp hq hlogq hbudget (j := j) (by omega)
  linarith

/-- The logarithmic size of the next upper endpoint is small compared
with the preceding upper endpoint, uniformly in the index. -/
theorem mrLogSchedule_upper_log_small
    {eta p₁ q₁ : ℝ} (heta0 : 0 < eta) (heta1 : eta ≤ 1 / 12)
    (hp : 2 ≤ p₁) (hq : 1 ≤ q₁) (hpq : p₁ ≤ q₁) (hlogq : 1 ≤ Real.log q₁)
    (hbudget : 4096 * Real.log q₁ ≤ eta * p₁) {j : ℕ} (hj : 2 ≤ j) :
    3 * Real.log (mrLogScheduleUpper q₁ j) ≤ mrLogScheduleUpper q₁ (j - 1) / 2 := by
  have hcost := mrLogSchedule_cost_separation heta0 hp hq hlogq hbudget hj
  have hpPrev : 2 ≤ mrLogScheduleLower p₁ q₁ (j - 1) :=
    hp.trans (mrLogScheduleLower_ge (by linarith) hq (by omega))
  have hpqPrev := mrLogScheduleLower_le_upper hq hpq (show 1 ≤ j - 1 by omega)
  have hdelta := mrSchedule_delta_le_one heta1 (show 1 ≤ j by omega)
  have hqcur : 1 ≤ mrLogScheduleUpper q₁ j := hq.trans (mrLogScheduleUpper_ge hq (by omega))
  have hlog : Real.log (mrLogScheduleUpper q₁ j) ≤ Real.log (2 * mrLogScheduleUpper q₁ j) :=
    Real.log_le_log (by linarith) (by linarith)
  have hc := (div_le_iff₀ (by linarith : 0 < mrLogScheduleLower p₁ q₁ (j - 1) - 1)).mp hcost
  have hd := mul_le_mul_of_nonneg_right hdelta
    (show 0 ≤ mrLogScheduleLower p₁ q₁ (j - 1) - 1 by linarith)
  nlinarith

theorem mrLogSchedule_resolution_base_nonneg
    {eta p₁ q₁ : ℝ} (heta : eta ≤ 1 / 12) (hp : 0 ≤ p₁) (hlogq : 1 ≤ Real.log q₁)
    (hbudget : 4096 * Real.log q₁ ≤ eta * p₁) :
    0 ≤ (1 / 6 - eta) * p₁ - Real.log q₁ / 3 := by
  have he := mul_le_mul_of_nonneg_right heta hp
  nlinarith

theorem mrLogSchedule_resolution_one_le
    {eta p₁ q₁ : ℝ} (heta : eta ≤ 1 / 12) (hp : 0 ≤ p₁) (hlogq : 1 ≤ Real.log q₁)
    (hbudget : 4096 * Real.log q₁ ≤ eta * p₁) {j : ℕ} (hj : 1 ≤ j) :
    1 ≤ mrLogBlockResolution eta p₁ q₁ (j : ℝ) :=
  mrLogBlockResolution_one_le (by exact_mod_cast hj)
    (mrLogSchedule_resolution_base_nonneg heta hp hlogq hbudget)

/-- The strengthened budget also pays for a genuinely narrow prime
subblock: every resolution is at least two. -/
theorem mrLogSchedule_resolution_two_le
    {eta p₁ q₁ : ℝ} (heta : eta ≤ 1 / 12) (hp : 0 ≤ p₁) (hlogq : 1 ≤ Real.log q₁)
    (hbudget : 4096 * Real.log q₁ ≤ eta * p₁) {j : ℕ} (hj : 1 ≤ j) :
    2 ≤ mrLogBlockResolution eta p₁ q₁ (j : ℝ) := by
  have he := mul_le_mul_of_nonneg_right heta hp
  have hbase : 1 ≤ (1 / 6 - eta) * p₁ - Real.log q₁ / 3 := by nlinarith
  have hexp := Real.add_one_le_exp ((1 / 6 - eta) * p₁ - Real.log q₁ / 3)
  have hjpow : (1 : ℝ) ≤ (j : ℝ) ^ 2 := one_le_pow₀ (by exact_mod_cast hj)
  have hm := mul_le_mul_of_nonneg_right hjpow
    (Real.exp_pos ((1 / 6 - eta) * p₁ - Real.log q₁ / 3)).le
  unfold mrLogBlockResolution
  nlinarith

theorem exp_inv_resolution_le_two {H : ℝ} (hH : 2 ≤ H) : Real.exp (1 / H) ≤ 2 := by
  have hH0 : 0 < H := by linarith
  have hhalf : 1 / H ≤ (1 : ℝ) / 2 :=
    one_div_le_one_div_of_le (by norm_num) hH
  have hlog2 : (1 : ℝ) / 2 ≤ Real.log 2 := by
    have hh := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at hh
    exact hh
  calc
    Real.exp (1 / H) ≤ Real.exp (Real.log 2) := Real.exp_le_exp.mpr (hhalf.trans hlog2)
    _ = 2 := Real.exp_log (by norm_num)

/-- The same initial budget gives the resolution needed for the common
thin boundary bands with relative width at most one half. -/
theorem mrLogSchedule_resolution_four_le
    {eta p₁ q₁ : ℝ} (heta : eta ≤ 1 / 12) (hp : 0 ≤ p₁) (hlogq : 1 ≤ Real.log q₁)
    (hbudget : 4096 * Real.log q₁ ≤ eta * p₁) {j : ℕ} (hj : 1 ≤ j) :
    4 ≤ mrLogBlockResolution eta p₁ q₁ (j : ℝ) := by
  have he := mul_le_mul_of_nonneg_right heta hp
  have hbase : 3 ≤ (1 / 6 - eta) * p₁ - Real.log q₁ / 3 := by nlinarith
  have hexp := Real.add_one_le_exp ((1 / 6 - eta) * p₁ - Real.log q₁ / 3)
  have hjpow : (1 : ℝ) ≤ (j : ℝ) ^ 2 := one_le_pow₀ (by exact_mod_cast hj)
  have hm := mul_le_mul_of_nonneg_right hjpow
    (Real.exp_pos ((1 / 6 - eta) * p₁ - Real.log q₁ / 3)).le
  unfold mrLogBlockResolution
  nlinarith

theorem exp_le_one_add_two_mul_of_le_half {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 2) :
    Real.exp x ≤ 1 + 2 * x := by
  have hxlt : x < 1 := by linarith
  apply (Real.exp_bound_div_one_sub_of_interval hx0 hxlt).trans
  apply (div_le_iff₀ (by linarith : 0 < 1 - x)).mpr
  nlinarith

theorem exp_inv_resolution_le_one_add {H : ℝ} (hH : 2 ≤ H) :
    Real.exp (1 / H) ≤ 1 + 2 / H := by
  have hH0 : 0 < H := by linarith
  have hhalf : 1 / H ≤ (1 : ℝ) / 2 := one_div_le_one_div_of_le (by norm_num) hH
  have hh := exp_le_one_add_two_mul_of_le_half (by positivity : 0 ≤ 1 / H) hhalf
  convert hh using 1
  ring

theorem exp_next_subblock_le_double {H : ℝ} (hH : 2 ≤ H) (r : ℕ) :
    Real.exp (((r + 1 : ℕ) : ℝ) / H) ≤ 2 * Real.exp ((r : ℝ) / H) := by
  push_cast
  rw [add_div, Real.exp_add]
  have hh := mul_le_mul_of_nonneg_left (exp_inv_resolution_le_two hH)
    (Real.exp_pos ((r : ℝ) / H)).le
  simpa only [mul_comm] using hh

theorem mrLogSchedule_resolution_prefactor
    {eta p₁ q₁ : ℝ} (heta0 : 0 < eta) (heta1 : eta ≤ 1 / 12)
    (hp : 2 ≤ p₁) (hq : 1 ≤ q₁) (hpq : p₁ ≤ q₁) (hlogq : 1 ≤ Real.log q₁)
    (hbudget : 4096 * Real.log q₁ ≤ eta * p₁) {j : ℕ} (hj : 2 ≤ j) :
    mrLogBlockResolution eta p₁ q₁ (j : ℝ) ^ 3 * mrLogScheduleUpper q₁ j ^ 3 ≤
      (j : ℝ) ^ 6 * Real.exp (mrLogScheduleUpper q₁ (j - 1)) := by
  apply mrLogBlockResolution_prefactor_le heta0.le (by linarith) hq
    (hpq.trans (mrLogScheduleUpper_ge hq (by omega)))
    (hq.trans (mrLogScheduleUpper_ge hq (by omega)))
  exact mrLogSchedule_upper_log_small heta0 heta1 hp hq hpq hlogq hbudget hj

/-- The actual schedule threshold gap, with natural-index subtraction
converted explicitly to the real formula. -/
theorem mrLogSchedule_threshold_gap {eta : ℝ} (heta : 0 ≤ eta) {j : ℕ} (hj : 2 ≤ j) :
    eta / (2 * (j : ℝ) ^ 2) ≤
      mrThresholdExponent eta (j : ℝ) - mrThresholdExponent eta ((j - 1 : ℕ) : ℝ) := by
  have h := mrThresholdExponent_gap heta (by exact_mod_cast hj : (2 : ℝ) ≤ j)
  simpa only [Nat.cast_sub (show 1 ≤ j by omega), Nat.cast_one] using h

/-- Every positive target ratio permits the strengthened initial budget
for all sufficiently large logarithmic upper endpoints. -/
theorem exists_eventually_mrLogSchedule_initial
    {eta epsilon : ℝ} (heta : 0 < eta) (hepsilon : 0 < epsilon) :
    ∃ rho : ℝ, 0 < rho ∧ rho ≤ epsilon ∧ rho ≤ 1 ∧
      ∀ᶠ q : ℝ in atTop,
        Real.exp 1 ≤ q ∧ 2 ≤ rho * q ∧ rho * q ≤ q ∧
          4096 * Real.log q ≤ eta * (rho * q) := by
  let rho : ℝ := min epsilon 1
  have hrho : 0 < rho := lt_min hepsilon zero_lt_one
  have hrhoE : rho ≤ epsilon := min_le_left _ _
  have hrho1 : rho ≤ 1 := min_le_right _ _
  refine ⟨rho, hrho, hrhoE, hrho1, ?_⟩
  have hsmall := Real.isLittleO_log_id_atTop.bound
    (show 0 < eta * rho / 4096 by positivity)
  filter_upwards [hsmall, eventually_ge_atTop (Real.exp 1), eventually_ge_atTop (2 / rho)] with q hs hqe hqp
  have hq0 : 0 < q := (Real.exp_pos 1).trans_le hqe
  have hq1 : 1 ≤ q := (Real.one_le_exp_iff.mpr (by norm_num : (0 : ℝ) ≤ 1)).trans hqe
  have hlog0 : 0 ≤ Real.log q := Real.log_nonneg hq1
  change ‖Real.log q‖ ≤ (eta * rho / 4096) * ‖q‖ at hs
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hlog0, abs_of_nonneg hq0.le] at hs
  refine ⟨hqe, ?_, ?_, ?_⟩
  · have hp := (div_le_iff₀ hrho).mp hqp
    nlinarith
  · have hp := mul_le_mul_of_nonneg_right hrho1 hq0.le
    simpa only [one_mul] using hp
  · calc
      4096 * Real.log q ≤ 4096 * ((eta * rho / 4096) * q) := by gcongr
      _ = eta * (rho * q) := by ring

/-- Initial parameters exist beyond any prescribed threshold and with
arbitrarily small logarithmic ratio. This discharges nonvacuity of the
strengthened schedule assumptions. -/
theorem exists_mrLogSchedule_initial
    {eta epsilon : ℝ} (heta : 0 < eta) (hepsilon : 0 < epsilon) (Q : ℝ) :
    ∃ p q : ℝ, Q ≤ q ∧ Real.exp 1 ≤ q ∧ 2 ≤ p ∧ p ≤ q ∧ p / q ≤ epsilon ∧
      4096 * Real.log q ≤ eta * p := by
  obtain ⟨rho, hrho, hrhoE, hrho1, heventual⟩ := exists_eventually_mrLogSchedule_initial heta hepsilon
  obtain ⟨q, hq, hQ⟩ := (heventual.and (eventually_ge_atTop Q)).exists
  refine ⟨rho * q, q, hQ, hq.1, hq.2.1, hq.2.2.1, ?_, hq.2.2.2⟩
  have hq0 : 0 < q := (Real.exp_pos 1).trans_le hq.1
  simpa only [mul_div_cancel_right₀ _ hq0.ne'] using hrhoE

end Erdos67b
