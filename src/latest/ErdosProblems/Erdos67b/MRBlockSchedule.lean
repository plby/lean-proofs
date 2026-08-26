import ErdosProblems.Erdos67b.MRSmallBlockParameters

/-!
# Uniform logarithmic prime-block schedule

The original schedule shape is retained, with a larger explicit initial
logarithmic budget to pay the elementary factorial estimate. Both
separation inequalities are proved uniformly in the block index.
-/

namespace Erdos67b

noncomputable section

def mrLogScheduleWeight (q₁ : ℝ) (j : ℕ) : ℝ :=
  (j : ℝ) ^ (4 * j) * q₁ ^ (j - 1)

def mrLogScheduleLower (p₁ q₁ : ℝ) (j : ℕ) : ℝ :=
  mrLogScheduleWeight q₁ j * p₁

def mrLogScheduleUpper (q₁ : ℝ) (j : ℕ) : ℝ :=
  (j : ℝ) ^ (4 * j + 2) * q₁ ^ j

theorem mrLogScheduleWeight_one_le {q₁ : ℝ} (hq : 1 ≤ q₁) {j : ℕ} (hj : 1 ≤ j) :
    1 ≤ mrLogScheduleWeight q₁ j := by
  have hjr : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have ha := one_le_pow₀ (n := 4 * j) hjr
  have hb := one_le_pow₀ (n := j - 1) hq
  unfold mrLogScheduleWeight
  nlinarith

theorem mrLogScheduleLower_ge {p₁ q₁ : ℝ} (hp : 0 ≤ p₁) (hq : 1 ≤ q₁)
    {j : ℕ} (hj : 1 ≤ j) : p₁ ≤ mrLogScheduleLower p₁ q₁ j := by
  have h := mul_le_mul_of_nonneg_right (mrLogScheduleWeight_one_le hq hj) hp
  unfold mrLogScheduleLower
  simpa only [one_mul] using h

theorem mrLogScheduleUpper_ge {q₁ : ℝ} (hq : 1 ≤ q₁) {j : ℕ} (hj : 1 ≤ j) :
    q₁ ≤ mrLogScheduleUpper q₁ j := by
  have hjr : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have ha := one_le_pow₀ (n := 4 * j + 2) hjr
  have hpow : q₁ ≤ q₁ ^ j := by
    simpa only [pow_one] using pow_le_pow_right₀ hq hj
  unfold mrLogScheduleUpper
  have hq0 : 0 ≤ q₁ ^ j := by positivity
  nlinarith

theorem mrLogScheduleLower_le_upper {p₁ q₁ : ℝ}
    (hq : 1 ≤ q₁) (hpq : p₁ ≤ q₁) {j : ℕ} (hj : 1 ≤ j) :
    mrLogScheduleLower p₁ q₁ j ≤ mrLogScheduleUpper q₁ j := by
  have hjr : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hsq : (1 : ℝ) ≤ (j : ℝ) ^ 2 := one_le_pow₀ hjr
  have hweight : 0 ≤ mrLogScheduleWeight q₁ j := (by
    have := mrLogScheduleWeight_one_le hq hj
    linarith)
  calc
    _ ≤ mrLogScheduleWeight q₁ j * q₁ := mul_le_mul_of_nonneg_left hpq hweight
    _ ≤ mrLogScheduleWeight q₁ j * ((j : ℝ) ^ 2 * q₁) := by
      apply mul_le_mul_of_nonneg_left ?_ hweight
      nlinarith
    _ = mrLogScheduleUpper q₁ j := by
      unfold mrLogScheduleWeight mrLogScheduleUpper
      rw [pow_add, show q₁ ^ j = q₁ ^ (j - 1) * q₁ by
        rw [← pow_succ, Nat.sub_add_cancel hj]]
      ring

/-- A coarse uniform logarithm bound sufficient for the factorial cost. -/
theorem log_two_mrLogScheduleUpper_le {q₁ : ℝ}
    (hq : 1 ≤ q₁) (hlogq : 1 ≤ Real.log q₁) {j : ℕ} (hj : 2 ≤ j) :
    Real.log (2 * mrLogScheduleUpper q₁ j) ≤ 7 * (j : ℝ) ^ 2 * Real.log q₁ := by
  have hjr : (2 : ℝ) ≤ j := by exact_mod_cast hj
  have hj0 : (0 : ℝ) < j := by positivity
  have hq0 : 0 < q₁ := by linarith
  have hjlog0 : 0 ≤ Real.log (j : ℝ) := Real.log_nonneg (by linarith)
  have hjlog : Real.log (j : ℝ) ≤ j := (Real.log_le_sub_one_of_pos hj0).trans (by linarith)
  have hlog2 : Real.log 2 ≤ 1 := by
    calc
      Real.log 2 ≤ 2 - 1 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      _ = 1 := by norm_num
  have hformula : Real.log (2 * mrLogScheduleUpper q₁ j) =
      Real.log 2 + (4 * (j : ℝ) + 2) * Real.log (j : ℝ) + (j : ℝ) * Real.log q₁ := by
    unfold mrLogScheduleUpper
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_pow, Real.log_pow]
    push_cast
    ring
  have hterm : (4 * (j : ℝ) + 2) * Real.log (j : ℝ) ≤ 5 * (j : ℝ) ^ 2 := by
    have hm := mul_le_mul (by linarith : 4 * (j : ℝ) + 2 ≤ 5 * j) hjlog hjlog0 (by positivity)
    nlinarith
  have hL0 : 0 ≤ Real.log q₁ := by linarith
  have hquad : (j : ℝ) ≤ (j : ℝ) ^ 2 := by nlinarith
  have hscale := mul_le_mul_of_nonneg_left hlogq (sq_nonneg (j : ℝ))
  have hlinear := mul_le_mul_of_nonneg_right hquad hL0
  rw [hformula]
  nlinarith

/-- The fourth power of the current index is dominated by the preceding
schedule weight, uniformly even at the first transition `j = 2`. -/
theorem fourth_le_mrLogScheduleWeight_prev {q₁ : ℝ} (hq : 1 ≤ q₁)
    {j : ℕ} (hj : 2 ≤ j) :
    (j : ℝ) ^ 4 ≤ 16 * mrLogScheduleWeight q₁ (j - 1) := by
  have hk : 1 ≤ j - 1 := by omega
  have hkr : (1 : ℝ) ≤ (j - 1 : ℕ) := by exact_mod_cast hk
  have hjk : (j : ℝ) ≤ 2 * ((j - 1 : ℕ) : ℝ) := by
    exact_mod_cast (by omega : j ≤ 2 * (j - 1))
  have hfour : (((j - 1 : ℕ) : ℝ) ^ 4) ≤
      mrLogScheduleWeight q₁ (j - 1) := by
    have hpow : (((j - 1 : ℕ) : ℝ) ^ 4) ≤ ((j - 1 : ℕ) : ℝ) ^ (4 * (j - 1)) :=
      pow_le_pow_right₀ hkr (by omega)
    have hqpow := one_le_pow₀ (n := (j - 1) - 1) hq
    unfold mrLogScheduleWeight
    have hb : 0 ≤ ((j - 1 : ℕ) : ℝ) ^ (4 * (j - 1)) := by positivity
    nlinarith
  calc
    _ ≤ (2 * ((j - 1 : ℕ) : ℝ)) ^ 4 := pow_le_pow_left₀ (by positivity) hjk 4
    _ = 16 * ((j - 1 : ℕ) : ℝ) ^ 4 := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hfour (by norm_num)

/-- The extra endpoint shift needed by the enlarged cofactor rectangle
is absorbed by one more unit of the logarithmic schedule bound. -/
theorem log_two_mrLogScheduleUpper_add_one_le {q₁ : ℝ}
    (hq : 1 ≤ q₁) (hlogq : 1 ≤ Real.log q₁) {j : ℕ} (hj : 2 ≤ j) :
    Real.log (2 * (mrLogScheduleUpper q₁ j + 1)) ≤ 8 * (j : ℝ) ^ 2 * Real.log q₁ := by
  have hQ : 1 ≤ mrLogScheduleUpper q₁ j :=
    hq.trans (mrLogScheduleUpper_ge hq (by omega))
  have hjr : (2 : ℝ) ≤ j := by exact_mod_cast hj
  have hlog2 : Real.log 2 ≤ 1 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hscale := mul_le_mul_of_nonneg_left hlogq (sq_nonneg (j : ℝ))
  calc
    _ ≤ Real.log (2 * (2 * mrLogScheduleUpper q₁ j)) :=
      Real.log_le_log (by positivity) (by linarith)
    _ = Real.log 2 + Real.log (2 * mrLogScheduleUpper q₁ j) :=
      Real.log_mul (by norm_num) (by positivity)
    _ ≤ 8 * (j : ℝ) ^ 2 * Real.log q₁ := by
      have hh := log_two_mrLogScheduleUpper_le hq hlogq hj
      nlinarith

/-- Uniform separation also pays for the shifted cofactor endpoint at
every transition in the schedule. -/
theorem mrLogSchedule_shifted_cost_separation
    {eta p₁ q₁ : ℝ} (heta : 0 < eta) (hp : 2 ≤ p₁)
    (hq : 1 ≤ q₁) (hlogq : 1 ≤ Real.log q₁)
    (hbudget : 4096 * Real.log q₁ ≤ eta * p₁) {j : ℕ} (hj : 2 ≤ j) :
    6 * Real.log (2 * (mrLogScheduleUpper q₁ j + 1)) / (mrLogScheduleLower p₁ q₁ (j - 1) - 1) ≤
      eta / (2 * (j : ℝ) ^ 2) := by
  let A := mrLogScheduleWeight q₁ (j - 1)
  have hA : 1 ≤ A := mrLogScheduleWeight_one_le hq (by omega)
  have hA0 : 0 ≤ A := by linarith
  have hL0 : 0 ≤ Real.log q₁ := by linarith
  have hprev : 2 ≤ mrLogScheduleLower p₁ q₁ (j - 1) :=
    hp.trans (mrLogScheduleLower_ge (by linarith) hq (by omega))
  have hhalf : A * p₁ / 2 ≤ mrLogScheduleLower p₁ q₁ (j - 1) - 1 := by
    change A * p₁ / 2 ≤ A * p₁ - 1
    nlinarith
  have hlog := log_two_mrLogScheduleUpper_add_one_le hq hlogq hj
  have hfour := fourth_le_mrLogScheduleWeight_prev hq hj
  have hpaid : 4096 * (A * Real.log q₁) ≤ eta * (A * p₁) := by
    calc
      _ = A * (4096 * Real.log q₁) := by ring
      _ ≤ A * (eta * p₁) := mul_le_mul_of_nonneg_left hbudget hA0
      _ = _ := by ring
  have hkey : 12 * (j : ℝ) ^ 2 * Real.log (2 * (mrLogScheduleUpper q₁ j + 1)) ≤
      eta * (mrLogScheduleLower p₁ q₁ (j - 1) - 1) := by
    calc
      _ ≤ 12 * (j : ℝ) ^ 2 * (8 * (j : ℝ) ^ 2 * Real.log q₁) := by gcongr
      _ = 96 * (j : ℝ) ^ 4 * Real.log q₁ := by ring
      _ ≤ 1536 * A * Real.log q₁ := by
        have hm := mul_le_mul_of_nonneg_right hfour (by positivity : 0 ≤ 96 * Real.log q₁)
        dsimp only [A]
        nlinarith
      _ ≤ eta * (A * p₁) / 2 := by nlinarith [mul_nonneg hA0 hL0]
      _ ≤ eta * (mrLogScheduleLower p₁ q₁ (j - 1) - 1) := by
        have hh := mul_le_mul_of_nonneg_left hhalf heta.le
        nlinarith
  apply (div_le_div_iff₀ (by linarith : 0 < mrLogScheduleLower p₁ q₁ (j - 1) - 1)
    (by positivity : 0 < 2 * (j : ℝ) ^ 2)).mpr
  nlinarith

/-- The original unshifted separation is a consequence of the stronger
endpoint estimate. -/
theorem mrLogSchedule_cost_separation
    {eta p₁ q₁ : ℝ} (heta : 0 < eta) (hp : 2 ≤ p₁)
    (hq : 1 ≤ q₁) (hlogq : 1 ≤ Real.log q₁)
    (hbudget : 4096 * Real.log q₁ ≤ eta * p₁) {j : ℕ} (hj : 2 ≤ j) :
    6 * Real.log (2 * mrLogScheduleUpper q₁ j) / (mrLogScheduleLower p₁ q₁ (j - 1) - 1) ≤
      eta / (2 * (j : ℝ) ^ 2) := by
  apply le_trans ?_ (mrLogSchedule_shifted_cost_separation heta hp hq hlogq hbudget hj)
  have hQ : 1 ≤ mrLogScheduleUpper q₁ j :=
    hq.trans (mrLogScheduleUpper_ge hq (by omega))
  have hP : 2 ≤ mrLogScheduleLower p₁ q₁ (j - 1) :=
    hp.trans (mrLogScheduleLower_ge (by linarith) hq (by omega))
  apply div_le_div_of_nonneg_right ?_ (by linarith)
  exact mul_le_mul_of_nonneg_left (Real.log_le_log (by positivity) (by linarith)) (by norm_num)

/-- The same initial regime gives the large separation needed to absorb
all finite covering costs. -/
theorem mrLogSchedule_gap_separation
    {eta p₁ q₁ : ℝ} (hq : 1 ≤ q₁) (hlogq : 1 ≤ Real.log q₁)
    (hbudget : 4096 * Real.log q₁ ≤ eta * p₁) {j : ℕ} (hj : 2 ≤ j) :
    4 * mrLogScheduleUpper q₁ (j - 1) + 8 * Real.log (j : ℝ) ≤
      (eta / (2 * (j : ℝ) ^ 2)) * mrLogScheduleLower p₁ q₁ j := by
  let B : ℝ := (j : ℝ) ^ (4 * j - 2) * q₁ ^ (j - 1)
  have hjr : (2 : ℝ) ≤ j := by exact_mod_cast hj
  have hj0 : (0 : ℝ) < j := by positivity
  have hB0 : 0 ≤ B := by dsimp only [B]; positivity
  have hprev : mrLogScheduleUpper q₁ (j - 1) ≤ B := by
    unfold mrLogScheduleUpper
    rw [show 4 * (j - 1) + 2 = 4 * j - 2 by omega]
    dsimp only [B]
    gcongr
    exact_mod_cast Nat.sub_le j 1
  have hjB : (j : ℝ) ≤ B := by
    have hpow : (j : ℝ) ≤ (j : ℝ) ^ (4 * j - 2) := by
      simpa only [pow_one] using pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ j)
        (by omega : 1 ≤ 4 * j - 2)
    have hqpow := one_le_pow₀ (n := j - 1) hq
    dsimp only [B]
    nlinarith [show 0 ≤ (j : ℝ) ^ (4 * j - 2) by positivity]
  have hlogB : Real.log (j : ℝ) ≤ B :=
    (Real.log_le_sub_one_of_pos hj0).trans (by linarith)
  have hidentity : (eta / (2 * (j : ℝ) ^ 2)) * mrLogScheduleLower p₁ q₁ j =
      (eta * p₁ / 2) * B := by
    unfold mrLogScheduleLower mrLogScheduleWeight
    rw [show 4 * j = (4 * j - 2) + 2 by omega, pow_add]
    dsimp only [B]
    field_simp
  rw [hidentity]
  have hcoeff : 12 ≤ eta * p₁ / 2 := by linarith
  calc
    _ ≤ 12 * B := by linarith
    _ ≤ (eta * p₁ / 2) * B := mul_le_mul_of_nonneg_right hcoeff hB0

end

end Erdos67b
