import Arxiv.Arxiv2407_19026.TangentBackwardCoordBounds
import Arxiv.Arxiv2407_19026.IntegerPowerPolynomial

/-!
# Semantic bounds for the backward book comparisons

These estimates replace the executable affine-cover checks on the backward
book intervals.  The only numerical input left to the round-specific files is
an exact polynomial upper bound for the blue coordinate and an exact
Bernstein certificate for the resulting rational book margin.
-/

namespace Arxiv2407_19026

noncomputable section

def integerHornerInterval :
    List ℤ → LeanCert.Core.IntervalRat →
      LeanCert.Core.IntervalRat
  | [], _ => LeanCert.Core.IntervalRat.singleton 0
  | coefficient :: coefficients, interval =>
      LeanCert.Core.IntervalRat.add
        (LeanCert.Core.IntervalRat.singleton coefficient)
        (LeanCert.Core.IntervalRat.mul interval
          (integerHornerInterval coefficients interval))

lemma eval_integer_power_mem_horner
    (coefficients : List ℤ)
    (interval : LeanCert.Core.IntervalRat)
    {x : ℝ} (hx : x ∈ interval) :
    evalIntegerPower coefficients x ∈
      integerHornerInterval coefficients interval := by
  induction coefficients with
  | nil =>
      simp [evalIntegerPower, integerHornerInterval,
        LeanCert.Core.IntervalRat.mem_def,
        LeanCert.Core.IntervalRat.singleton]
  | cons coefficient coefficients ih =>
      exact LeanCert.Core.IntervalRat.mem_add
        (by
          simp [LeanCert.Core.IntervalRat.mem_def,
            LeanCert.Core.IntervalRat.singleton])
        (LeanCert.Core.IntervalRat.mem_mul hx ih)

lemma eval_integer_power_pos_of_interval
    (coefficients : List ℤ)
    (interval : LeanCert.Core.IntervalRat)
    {x : ℝ} (hx : x ∈ interval)
    (hlower :
      0 <
        (integerHornerInterval coefficients interval).lo) :
    0 < evalIntegerPower coefficients x := by
  have hmem :=
    eval_integer_power_mem_horner coefficients interval hx
  rw [LeanCert.Core.IntervalRat.mem_def] at hmem
  exact lt_of_lt_of_le (by exact_mod_cast hlower) hmem.1

def backwardQUpper (β z : ℝ) : ℝ :=
  -mediumCorrectionPolynomial β z *
      KernelBounds.expNegTaylor9 z +
    (1 / 4) * KernelBounds.expNegError10 z

def backwardExpQUpper (β z : ℝ) : ℝ :=
  let q := backwardQUpper β z
  1 + q + q ^ 2 / 2 + q ^ 3 / 6 + q ^ 4 / 24 +
    (13 / 50 : ℝ) ^ 5 / 100

def backwardBlueRawUpper (β z : ℝ) : ℝ :=
  z / (1 + z) * backwardExpQUpper β z

def backwardMuUpperNine (z : ℝ) : ℝ :=
  z * (KernelBounds.expNegTaylor9 z +
    KernelBounds.expNegError10 z)

def backwardLogLowerAboveFive (x : ℝ) : ℝ :=
  let y := (x - 1) / (x + 1)
  2 * (y + y ^ 3 / 3 + y ^ 5 / 5 +
    y ^ 7 / 7 + y ^ 9 / 9)

def backwardXLogLowerFour (B z : ℝ) : ℝ :=
  let M := backwardMuUpperNine z
  backwardLogLowerBelowFour (1 - B) * (1 - M)⁻¹ +
    backwardLogLowerBelowFour (1 - M)

def backwardXLogLowerThree (B z : ℝ) : ℝ :=
  let M := backwardMuUpperNine z
  backwardLogLowerBelowThree (1 - B) * (1 - M)⁻¹ +
    backwardLogLowerBelowThree (1 - M)

def backwardXLogLowerTwo (B z : ℝ) : ℝ :=
  let M := backwardMuUpperNine z
  mediumLogLowerBelow (1 - B) * (1 - M)⁻¹ +
    mediumLogLowerBelow (1 - M)

def backwardALogLower (β t : ℝ) : ℝ :=
  let coefficient :=
    t ^ 2 *
      (1 / 4 + β + (4 / 25 - β) * t -
        (2 / 25) * t ^ 2)
  (-tangentCoordLogUpper (1 + t) +
      coefficient * backwardExpLower5 t)

def backwardBookLower
    (β₀ β₁ t B z : ℝ) : ℝ :=
  (1 + z) * backwardLogLowerAboveFive (1 + z) +
    (-(1 / 4) * z + β₁ * z ^ 2 + 2 / 25 * z ^ 3) *
      (KernelBounds.expNegTaylor9 z +
        KernelBounds.expNegError10 z) +
    (backwardXLogLowerFour B z - z ^ 2 +
      z * (backwardALogLower β₀ t -
        backwardLogUpperBelowSeven z)) / 2

def backwardBookLowerThree
    (β₀ β₁ t B z : ℝ) : ℝ :=
  (1 + z) * backwardLogLowerAboveFive (1 + z) +
    (-(1 / 4) * z + β₁ * z ^ 2 + 2 / 25 * z ^ 3) *
      (KernelBounds.expNegTaylor9 z +
        KernelBounds.expNegError10 z) +
    (backwardXLogLowerThree B z - z ^ 2 +
      z * (backwardALogLower β₀ t -
        backwardLogUpperBelowSeven z)) / 2

def backwardBookLowerTwo
    (β₀ β₁ t B z : ℝ) : ℝ :=
  (1 + z) * backwardLogLowerAboveFive (1 + z) +
    (-(1 / 4) * z + β₁ * z ^ 2 + 2 / 25 * z ^ 3) *
      (KernelBounds.expNegTaylor9 z +
        KernelBounds.expNegError10 z) +
    (backwardXLogLowerTwo B z - z ^ 2 +
      z * (backwardALogLower β₀ t -
        backwardLogUpperBelowSeven z)) / 2

def backwardBookLowerTwoClosed
    (β₀ β₁ t B z : ℝ) : ℝ :=
  let M := backwardMuUpperNine z
  (1 + z) * backwardLogLowerAboveFive (1 + z) +
    (-(1 / 4) * z + β₁ * z ^ 2 + 2 / 25 * z ^ 3) *
      (KernelBounds.expNegTaylor9 z +
        KernelBounds.expNegError10 z) +
    (plateauLogLowerBelowOneSub B * (1 - M)⁻¹ +
      plateauLogLowerBelowOneSub M - z ^ 2 +
      z * (backwardALogLower β₀ t -
        backwardLogUpperBelowSeven z)) / 2

lemma backward_q_le_upper {β z : ℝ}
    (hβ : β ∈ Set.Icc 0 (2 / 25))
    (hz : z ∈ Set.Icc 0 1) :
    -mediumCorrectionPolynomial β z * Real.exp (-z) ≤
      backwardQUpper β z := by
  have happrox := KernelBounds.exp_neg_approx hz
  have hP := medium_correction_abs_le_quarter hβ hz
  have herror : 0 ≤ KernelBounds.expNegError10 z := by
    dsimp [KernelBounds.expNegError10]
    positivity
  have hproduct :
      -mediumCorrectionPolynomial β z *
          (Real.exp (-z) -
            KernelBounds.expNegTaylor9 z) ≤
        (1 / 4) * KernelBounds.expNegError10 z := by
    calc
      _ ≤
          |-mediumCorrectionPolynomial β z *
            (Real.exp (-z) -
              KernelBounds.expNegTaylor9 z)| :=
        le_abs_self _
      _ =
          |mediumCorrectionPolynomial β z| *
            |Real.exp (-z) -
              KernelBounds.expNegTaylor9 z| := by
        rw [abs_mul, abs_neg]
      _ ≤ (1 / 4) * KernelBounds.expNegError10 z :=
        mul_le_mul hP happrox (abs_nonneg _) (by norm_num)
  dsimp [backwardQUpper]
  linarith

private lemma backward_q_upper_abs {β z : ℝ}
    (hβ : β ∈ Set.Icc 0 (2 / 25))
    (hz : z ∈ Set.Icc 0 1) :
    |backwardQUpper β z| ≤ 13 / 50 := by
  have hP := medium_correction_abs_le_quarter hβ hz
  have happrox := KernelBounds.exp_neg_approx hz
  have hexp : Real.exp (-z) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by linarith [hz.1])
  have he0 : 0 ≤ KernelBounds.expNegError10 z := by
    dsimp [KernelBounds.expNegError10]
    positivity
  have hzpow : z ^ 10 ≤ 1 := pow_le_one₀ hz.1 hz.2
  have he1 :
      KernelBounds.expNegError10 z ≤ 1 / 1000000 := by
    dsimp [KernelBounds.expNegError10]
    norm_num [Nat.factorial]
    nlinarith
  have hT :
      |KernelBounds.expNegTaylor9 z| ≤
        1 + 1 / 1000000 := by
    calc
      _ ≤ |Real.exp (-z)| +
          |Real.exp (-z) -
            KernelBounds.expNegTaylor9 z| := by
        have htri := abs_add_le (Real.exp (-z))
          (KernelBounds.expNegTaylor9 z - Real.exp (-z))
        rw [show
          Real.exp (-z) +
              (KernelBounds.expNegTaylor9 z - Real.exp (-z)) =
            KernelBounds.expNegTaylor9 z by ring,
          abs_sub_comm] at htri
        exact htri
      _ ≤ 1 + 1 / 1000000 := by
        have habsexp : |Real.exp (-z)| ≤ 1 := by
          rw [abs_of_pos (Real.exp_pos _)]
          exact hexp
        linarith
  have hproduct :
      |mediumCorrectionPolynomial β z *
          KernelBounds.expNegTaylor9 z| ≤
        (1 / 4) * (1 + 1 / 1000000) := by
    rw [abs_mul]
    exact mul_le_mul hP hT (abs_nonneg _) (by norm_num)
  calc
    |backwardQUpper β z| ≤
        |mediumCorrectionPolynomial β z *
          KernelBounds.expNegTaylor9 z| +
          (1 / 4) * KernelBounds.expNegError10 z := by
      dsimp [backwardQUpper]
      calc
        _ ≤
            |-mediumCorrectionPolynomial β z *
              KernelBounds.expNegTaylor9 z| +
              |(1 / 4) *
                KernelBounds.expNegError10 z| :=
          abs_add_le _ _
        _ = _ := by
          simp only [abs_mul, abs_neg,
            abs_of_nonneg he0]
          norm_num
    _ ≤ 13 / 50 := by nlinarith

lemma exp_backward_q_le_upper {β z : ℝ}
    (hβ : β ∈ Set.Icc 0 (2 / 25))
    (hz : z ∈ Set.Icc 0 1) :
    Real.exp (backwardQUpper β z) ≤
      backwardExpQUpper β z := by
  have hq := backward_q_upper_abs hβ hz
  have hbound := Real.exp_bound
    (x := backwardQUpper β z) (n := 5)
    (hq.trans (by norm_num)) (by norm_num)
  have hupper := (abs_le.mp hbound).2
  have hpow :
      |backwardQUpper β z| ^ 5 ≤
        (13 / 50 : ℝ) ^ 5 :=
    pow_le_pow_left₀ (abs_nonneg _) hq 5
  norm_num [Finset.sum_range_succ, Nat.factorial,
    backwardExpQUpper] at hupper ⊢
  nlinarith

lemma tangent_blue_le_backward_raw_upper {β z : ℝ}
    (hβ : β ∈ Set.Icc 0 (2 / 25))
    (hz : z ∈ Set.Icc 0 1) :
    tangentBlue β z ≤ backwardBlueRawUpper β z := by
  have hzplus : 0 < 1 + z := by linarith [hz.1]
  have hq := backward_q_le_upper hβ hz
  have hexp :
      Real.exp
          (-mediumCorrectionPolynomial β z * Real.exp (-z)) ≤
        Real.exp (backwardQUpper β z) :=
    Real.exp_le_exp.mpr hq
  have hratio : 0 ≤ z / (1 + z) :=
    div_nonneg hz.1 hzplus.le
  calc
    tangentBlue β z =
        z / (1 + z) *
          Real.exp
            (-mediumCorrectionPolynomial β z *
              Real.exp (-z)) := by
      unfold tangentBlue tangentCorrectionSlope
        mediumCorrectionPolynomial
      rw [show
        -Real.log (1 + z) -
            (-(1 / 4) + 2 * β * z + 6 / 25 * z ^ 2 -
              (-(1 / 4) * z + β * z ^ 2 +
                2 / 25 * z ^ 3)) * Real.exp (-z) =
          -Real.log (1 + z) +
            (-(mediumCorrectionPolynomial β z) *
              Real.exp (-z)) by
        unfold mediumCorrectionPolynomial
        ring]
      rw [Real.exp_add, Real.exp_neg,
        Real.exp_log hzplus]
      field_simp [hzplus.ne']
      congr 2
      unfold mediumCorrectionPolynomial
      ring
    _ ≤ z / (1 + z) *
          Real.exp (backwardQUpper β z) :=
      mul_le_mul_of_nonneg_left hexp hratio
    _ ≤ backwardBlueRawUpper β z :=
      mul_le_mul_of_nonneg_left
        (exp_backward_q_le_upper hβ hz) hratio

private lemma backward_exp_q_upper_le_three_halves {β z : ℝ}
    (hβ : β ∈ Set.Icc 0 (2 / 25))
    (hz : z ∈ Set.Icc 0 1) :
    backwardExpQUpper β z ≤ 3 / 2 := by
  let q := backwardQUpper β z
  have hq : |q| ≤ 13 / 50 := by
    exact backward_q_upper_abs hβ hz
  have hpow (i : ℕ) :
      q ^ i ≤ (13 / 50 : ℝ) ^ i := by
    calc
      q ^ i ≤ |q ^ i| := le_abs_self _
      _ = |q| ^ i := abs_pow q i
      _ ≤ (13 / 50 : ℝ) ^ i :=
        pow_le_pow_left₀ (abs_nonneg q) hq i
  dsimp [backwardExpQUpper, q]
  nlinarith [hpow 1, hpow 2, hpow 3, hpow 4]

lemma backward_blue_raw_upper_bounds {β z : ℝ}
    (hβ : β ∈ Set.Icc 0 (2 / 25))
    (hz : z ∈ Set.Icc 0 1) :
    0 ≤ backwardBlueRawUpper β z ∧
      backwardBlueRawUpper β z < 1 := by
  have hzplus : 0 < 1 + z := by linarith [hz.1]
  have hratio0 : 0 ≤ z / (1 + z) :=
    div_nonneg hz.1 hzplus.le
  have hratio :
      z / (1 + z) ≤ 1 / 2 := by
    rw [div_le_iff₀ hzplus]
    linarith [hz.2]
  have hexp0 :
      0 < backwardExpQUpper β z :=
    (Real.exp_pos _).trans_le
      (exp_backward_q_le_upper hβ hz)
  have hexp :=
    backward_exp_q_upper_le_three_halves hβ hz
  unfold backwardBlueRawUpper
  constructor
  · positivity
  · calc
      z / (1 + z) * backwardExpQUpper β z ≤
          (1 / 2 : ℝ) * (3 / 2) :=
        mul_le_mul hratio hexp hexp0.le (by norm_num)
      _ < 1 := by norm_num

private lemma backward_exp_upper_nine_le {z : ℝ}
    (hz : z ∈ Set.Icc 0 1) :
    KernelBounds.expNegTaylor9 z +
        KernelBounds.expNegError10 z ≤
      1 - z / 2 := by
  have hz2 : z ^ 2 ≤ z :=
    by
      have hmul :=
        mul_nonneg hz.1 (sub_nonneg.mpr hz.2)
      nlinarith
  have h34 : z ^ 4 ≤ 4 * z ^ 3 := by
    have := mul_le_mul_of_nonneg_left hz.2
      (pow_nonneg hz.1 3)
    nlinarith
  have h56 : z ^ 6 ≤ 6 * z ^ 5 := by
    have := mul_le_mul_of_nonneg_left hz.2
      (pow_nonneg hz.1 5)
    nlinarith
  have h78 : z ^ 8 ≤ 8 * z ^ 7 := by
    have := mul_le_mul_of_nonneg_left hz.2
      (pow_nonneg hz.1 7)
    nlinarith
  have h910 : z ^ 10 ≤ z ^ 9 := by
    simpa [pow_succ] using
      mul_le_mul_of_nonneg_left hz.2
        (pow_nonneg hz.1 9)
  norm_num [KernelBounds.expNegTaylor9,
    KernelBounds.expNegError10, Finset.sum_range_succ,
    Nat.factorial]
  nlinarith

lemma backward_mu_upper_nine_bounds {z : ℝ}
    (hz : z ∈ Set.Icc 0 1) :
    optimizationM z ≤ backwardMuUpperNine z ∧
      0 ≤ backwardMuUpperNine z ∧
      backwardMuUpperNine z < 1 := by
  have happrox := KernelBounds.exp_neg_approx hz
  have hupper :
      Real.exp (-z) ≤
        KernelBounds.expNegTaylor9 z +
          KernelBounds.expNegError10 z := by
    linarith [abs_le.mp happrox]
  have hnonneg :
      0 ≤ KernelBounds.expNegTaylor9 z +
        KernelBounds.expNegError10 z :=
    (Real.exp_pos _).le.trans hupper
  have hcoarse := backward_exp_upper_nine_le hz
  have hquadratic :
      z * (1 - z / 2) ≤ 1 / 2 := by
    nlinarith [sq_nonneg (z - 1)]
  unfold optimizationM backwardMuUpperNine
  constructor
  · exact mul_le_mul_of_nonneg_left hupper hz.1
  constructor
  · exact mul_nonneg hz.1 hnonneg
  · calc
      z * (KernelBounds.expNegTaylor9 z +
          KernelBounds.expNegError10 z) ≤
          z * (1 - z / 2) :=
        mul_le_mul_of_nonneg_left hcoarse hz.1
      _ ≤ 1 / 2 := hquadratic
      _ < 1 := by norm_num

lemma backward_log_lower_above_five {x : ℝ}
    (hx : 1 ≤ x) :
    backwardLogLowerAboveFive x ≤ Real.log x := by
  let y : ℝ := (x - 1) / (x + 1)
  have hxp1 : 0 < x + 1 := by positivity
  have hy0 : 0 ≤ y :=
    div_nonneg (sub_nonneg.mpr hx) hxp1.le
  have hy1 : y < 1 := by
    rw [div_lt_one hxp1]
    linarith
  have hyabs : |y| < 1 := by
    simpa [abs_of_nonneg hy0] using hy1
  have hs := Real.hasSum_log_sub_log_of_abs_lt_one hyabs
  have hpartial :=
    hs.summable.sum_le_tsum (Finset.range 5) (by
      intro i hi
      positivity)
  rw [hs.tsum_eq] at hpartial
  have hlog :
      Real.log x =
        Real.log (1 + y) - Real.log (1 - y) := by
    rw [← Real.log_div]
    · congr 1
      dsimp [y]
      field_simp
      ring
    · dsimp [y]
      field_simp
      linarith
    · dsimp [y]
      field_simp
      linarith
  rw [hlog]
  norm_num [Finset.sum_range_succ,
    backwardLogLowerAboveFive, y] at hpartial ⊢
  nlinarith

lemma backward_log_lower_below_two {x : ℝ}
    (hx : 0 < x) (hx1 : x ≤ 1) :
    mediumLogLowerBelow x ≤ Real.log x := by
  let y : ℝ := (1 - x) / (1 + x)
  have hxplus : 0 < 1 + x := by linarith
  have hy0 : 0 ≤ y :=
    div_nonneg (sub_nonneg.mpr hx1) hxplus.le
  have hy1 : y < 1 := by
    rw [div_lt_one hxplus]
    linarith
  have h := Real.log_div_le_sum_range_add hy0 hy1 2
  have hratio : (1 + y) / (1 - y) = x⁻¹ := by
    dsimp [y]
    field_simp [hx.ne', hxplus.ne']
    ring
  rw [hratio, Real.log_inv] at h
  norm_num [Finset.sum_range_succ,
    mediumLogLowerBelow, y] at h ⊢
  linarith

lemma backward_log_lower_below_two_closed {x : ℝ}
    (hx0 : 0 ≤ x) (hx1 : x < 1) :
    mediumLogLowerBelow (1 - x) =
      plateauLogLowerBelowOneSub x := by
  have htwo : 0 < 2 - x := by linarith
  have hone : 0 < 1 - x := by linarith
  have hy0 : 0 ≤ x / (2 - x) :=
    div_nonneg hx0 htwo.le
  have hy1 : x / (2 - x) < 1 := by
    rw [div_lt_one htwo]
    linarith
  have hysquare :
      0 < 1 - (x / (2 - x)) ^ 2 := by
    nlinarith [mul_nonneg hy0
      (sub_nonneg.mpr hy1.le)]
  dsimp [mediumLogLowerBelow,
    plateauLogLowerBelowOneSub]
  field_simp [htwo.ne', hone.ne', hysquare.ne']
  ring_nf
  field_simp [hone.ne']
  ring

lemma backwardBookLowerTwo_eq_closed
    (β₀ β₁ t B z : ℝ)
    (hB0 : 0 ≤ B) (hB1 : B < 1)
    (hM0 : 0 ≤ backwardMuUpperNine z)
    (hM1 : backwardMuUpperNine z < 1) :
    backwardBookLowerTwo β₀ β₁ t B z =
      backwardBookLowerTwoClosed β₀ β₁ t B z := by
  dsimp [backwardBookLowerTwo, backwardXLogLowerTwo,
    backwardBookLowerTwoClosed]
  rw [backward_log_lower_below_two_closed hB0 hB1,
    backward_log_lower_below_two_closed hM0 hM1]

private lemma backward_xlog_lower_aux
    (logLower : ℝ → ℝ)
    (hlogLower :
      ∀ {x : ℝ}, 0 < x → x ≤ 1 →
        logLower x ≤ Real.log x)
    {β B z : ℝ}
    (hβ : 0 ≤ β) (hz : z ∈ Set.Icc (0 : ℝ) 1)
    (hB0 : 0 ≤ B) (hB : tangentBlue β z ≤ B)
    (hB1 : B < 1) :
    logLower (1 - B) *
          (1 - backwardMuUpperNine z)⁻¹ +
        logLower (1 - backwardMuUpperNine z) ≤
      tangentXLog β z := by
  obtain ⟨hM, hM0, hM1⟩ :=
    backward_mu_upper_nine_bounds hz
  let p : ℝ := 1 - tangentBlue β z
  let om : ℝ := 1 - optimizationM z
  let pB : ℝ := 1 - B
  let omM : ℝ := 1 - backwardMuUpperNine z
  have hp : 0 < p :=
    sub_pos.mpr (tangentBlue_lt_one hβ hz.1 hz.2)
  have hom : 0 < om :=
    sub_pos.mpr
      (optimizationM_lt_one_of_Icc hz.1 hz.2)
  have hpB : 0 < pB := by dsimp [pB]; linarith
  have homM : 0 < omM := by dsimp [omM]; linarith
  have hpB_le : pB ≤ p := by
    dsimp [p, pB]
    linarith
  have homM_le : omM ≤ om := by
    dsimp [om, omM]
    linarith
  have hlogp :
      logLower pB ≤ Real.log p :=
    (hlogLower hpB (by
      dsimp [pB]
      linarith)).trans
        (Real.strictMonoOn_log.monotoneOn hpB hp hpB_le)
  have hlogom :
      logLower omM ≤ Real.log om :=
    (hlogLower homM (by
      dsimp [omM]
      linarith)).trans
        (Real.strictMonoOn_log.monotoneOn homM hom homM_le)
  have hlbp :
      logLower pB ≤ 0 :=
    (hlogLower hpB (by
      dsimp [pB]
      linarith)).trans
        (Real.log_nonpos hpB.le (by
          dsimp [pB]
          linarith))
  have hinv : om⁻¹ ≤ omM⁻¹ :=
    (inv_le_inv₀ hom homM).mpr homM_le
  have hfirst :
      logLower pB * omM⁻¹ ≤
        Real.log p * om⁻¹ := by
    calc
      _ ≤ logLower pB * om⁻¹ :=
        mul_le_mul_of_nonpos_left hinv hlbp
      _ ≤ Real.log p * om⁻¹ :=
        mul_le_mul_of_nonneg_right hlogp
          (inv_nonneg.mpr hom.le)
  unfold tangentXLog
  dsimp only
  rw [Real.exp_neg, Real.exp_log hom]
  dsimp [p, om, pB, omM] at hfirst hlogom ⊢
  linarith

lemma backward_xlog_lower_four_le {β B z : ℝ}
    (hβ : 0 ≤ β) (hz : z ∈ Set.Icc (0 : ℝ) 1)
    (hB0 : 0 ≤ B) (hB : tangentBlue β z ≤ B)
    (hB1 : B < 1) :
    backwardXLogLowerFour B z ≤ tangentXLog β z := by
  exact backward_xlog_lower_aux
    backwardLogLowerBelowFour
    (fun hx hx1 => backward_log_lower_below_four hx hx1)
    hβ hz hB0 hB hB1

lemma backward_xlog_lower_three_le {β B z : ℝ}
    (hβ : 0 ≤ β) (hz : z ∈ Set.Icc (0 : ℝ) 1)
    (hB0 : 0 ≤ B) (hB : tangentBlue β z ≤ B)
    (hB1 : B < 1) :
    backwardXLogLowerThree B z ≤ tangentXLog β z := by
  exact backward_xlog_lower_aux
    backwardLogLowerBelowThree
    (fun hx hx1 => backward_log_lower_below_three hx hx1)
    hβ hz hB0 hB hB1

lemma backward_xlog_lower_two_le {β B z : ℝ}
    (hβ : 0 ≤ β) (hz : z ∈ Set.Icc (0 : ℝ) 1)
    (hB0 : 0 ≤ B) (hB : tangentBlue β z ≤ B)
    (hB1 : B < 1) :
    backwardXLogLowerTwo B z ≤ tangentXLog β z := by
  exact backward_xlog_lower_aux
    mediumLogLowerBelow
    (fun hx hx1 => backward_log_lower_below_two hx hx1)
    hβ hz hB0 hB hB1

lemma backward_alog_lower_le {β t : ℝ}
    (hβ : β ∈ Set.Icc 0 (2 / 25))
    (ht : t ∈ Set.Icc 0 1) :
    backwardALogLower β t ≤ tangentALog β t := by
  have hlog := tangent_coord_log_upper_backward
    (show 1 + t ∈ Set.Icc (1 : ℝ) 2 by
      constructor <;> linarith [ht.1, ht.2])
  have happrox := backward_exp_approx5 ht
  have hexp :
      backwardExpLower5 t ≤ Real.exp (-t) := by
    unfold backwardExpLower5
    linarith [abs_le.mp happrox]
  have hq :
      0 ≤ 1 / 4 + β + (4 / 25 - β) * t -
        (2 / 25) * t ^ 2 := by
    have hcoefficient :
        0 ≤ 4 / 25 - β - (2 / 25) * t := by
      nlinarith [hβ.2, ht.2]
    have hprod :
        0 ≤ t * (4 / 25 - β - (2 / 25) * t) :=
      mul_nonneg ht.1 hcoefficient
    nlinarith [hβ.1]
  have hcoefficient :
      0 ≤ t ^ 2 *
        (1 / 4 + β + (4 / 25 - β) * t -
          (2 / 25) * t ^ 2) :=
    mul_nonneg (sq_nonneg t) hq
  have hproduct :=
    mul_le_mul_of_nonneg_left hexp hcoefficient
  unfold backwardALogLower tangentALog
  dsimp only
  linarith

lemma backward_book_lower_le
    {β₀ β₁ t B z : ℝ}
    (hβ₀ : β₀ ∈ Set.Icc 0 (2 / 25))
    (hβ₁ : β₁ ∈ Set.Icc 0 (2 / 25))
    (hz : z ∈ Set.Icc (0 : ℝ) 1) (hz0 : 0 < z)
    (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (hB0 : 0 ≤ B) (hB : tangentBlue β₁ z ≤ B)
    (hB1 : B < 1) :
    backwardBookLower β₀ β₁ t B z ≤
      tangentCleanBookMargin β₁ z
        (tangentALog β₀ t - Real.log z) := by
  have hentropy := backward_log_lower_above_five
    (show (1 : ℝ) ≤ 1 + z by linarith [hz.1])
  have happrox := KernelBounds.exp_neg_approx hz
  have hexp :
      Real.exp (-z) ≤
        KernelBounds.expNegTaylor9 z +
          KernelBounds.expNegError10 z := by
    linarith [abs_le.mp happrox]
  have hramseyCoefficient :
      -(1 / 4) * z + β₁ * z ^ 2 +
          2 / 25 * z ^ 3 ≤ 0 := by
    have hz2 : z ^ 2 ≤ z :=
      by
        have hmul :=
          mul_nonneg hz.1 (sub_nonneg.mpr hz.2)
        nlinarith
    rw [show
      -(1 / 4) * z + β₁ * z ^ 2 +
          2 / 25 * z ^ 3 =
        z * (-(1 / 4) + β₁ * z +
          2 / 25 * z ^ 2) by ring]
    apply mul_nonpos_of_nonneg_of_nonpos hz.1
    have hβz :
        β₁ * z ≤ (2 / 25 : ℝ) * 1 :=
      mul_le_mul hβ₁.2 hz.2 hz.1 (by norm_num)
    nlinarith
  have hramsey :
      (-(1 / 4) * z + β₁ * z ^ 2 +
          2 / 25 * z ^ 3) *
          (KernelBounds.expNegTaylor9 z +
            KernelBounds.expNegError10 z) ≤
        ramseyCorrection β₁ z := by
    unfold ramseyCorrection
    exact mul_le_mul_of_nonpos_left hexp
      hramseyCoefficient
  have hx := backward_xlog_lower_four_le
    hβ₁.1 hz hB0 hB hB1
  have ha := backward_alog_lower_le hβ₀ ht
  have hlog := backward_log_upper_below_seven
    hz0 hz.2
  have hy :
      backwardALogLower β₀ t -
          backwardLogUpperBelowSeven z ≤
        tangentALog β₀ t - Real.log z := by
    linarith
  unfold tangentCleanBookMargin backwardBookLower
  nlinarith [mul_le_mul_of_nonneg_left hentropy
      (show (0 : ℝ) ≤ 1 + z by linarith [hz.1]),
    mul_le_mul_of_nonneg_left hy hz.1]

lemma backward_book_lower_three_le
    {β₀ β₁ t B z : ℝ}
    (hβ₀ : β₀ ∈ Set.Icc 0 (2 / 25))
    (hβ₁ : β₁ ∈ Set.Icc 0 (2 / 25))
    (hz : z ∈ Set.Icc (0 : ℝ) 1) (hz0 : 0 < z)
    (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (hB0 : 0 ≤ B) (hB : tangentBlue β₁ z ≤ B)
    (hB1 : B < 1) :
    backwardBookLowerThree β₀ β₁ t B z ≤
      tangentCleanBookMargin β₁ z
        (tangentALog β₀ t - Real.log z) := by
  have hentropy := backward_log_lower_above_five
    (show (1 : ℝ) ≤ 1 + z by linarith [hz.1])
  have happrox := KernelBounds.exp_neg_approx hz
  have hexp :
      Real.exp (-z) ≤
        KernelBounds.expNegTaylor9 z +
          KernelBounds.expNegError10 z := by
    linarith [abs_le.mp happrox]
  have hramseyCoefficient :
      -(1 / 4) * z + β₁ * z ^ 2 +
          2 / 25 * z ^ 3 ≤ 0 := by
    have hz2 : z ^ 2 ≤ z := by
      have hmul :=
        mul_nonneg hz.1 (sub_nonneg.mpr hz.2)
      nlinarith
    rw [show
      -(1 / 4) * z + β₁ * z ^ 2 +
          2 / 25 * z ^ 3 =
        z * (-(1 / 4) + β₁ * z +
          2 / 25 * z ^ 2) by ring]
    apply mul_nonpos_of_nonneg_of_nonpos hz.1
    have hβz :
        β₁ * z ≤ (2 / 25 : ℝ) * 1 :=
      mul_le_mul hβ₁.2 hz.2 hz.1 (by norm_num)
    nlinarith
  have hramsey :
      (-(1 / 4) * z + β₁ * z ^ 2 +
          2 / 25 * z ^ 3) *
          (KernelBounds.expNegTaylor9 z +
            KernelBounds.expNegError10 z) ≤
        ramseyCorrection β₁ z := by
    unfold ramseyCorrection
    exact mul_le_mul_of_nonpos_left hexp
      hramseyCoefficient
  have hx := backward_xlog_lower_three_le
    hβ₁.1 hz hB0 hB hB1
  have ha := backward_alog_lower_le hβ₀ ht
  have hlog := backward_log_upper_below_seven
    hz0 hz.2
  have hy :
      backwardALogLower β₀ t -
          backwardLogUpperBelowSeven z ≤
        tangentALog β₀ t - Real.log z := by
    linarith
  unfold tangentCleanBookMargin backwardBookLowerThree
  nlinarith [mul_le_mul_of_nonneg_left hentropy
      (show (0 : ℝ) ≤ 1 + z by linarith [hz.1]),
    mul_le_mul_of_nonneg_left hy hz.1]

lemma backward_book_lower_two_le
    {β₀ β₁ t B z : ℝ}
    (hβ₀ : β₀ ∈ Set.Icc 0 (2 / 25))
    (hβ₁ : β₁ ∈ Set.Icc 0 (2 / 25))
    (hz : z ∈ Set.Icc (0 : ℝ) 1) (hz0 : 0 < z)
    (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (hB0 : 0 ≤ B) (hB : tangentBlue β₁ z ≤ B)
    (hB1 : B < 1) :
    backwardBookLowerTwo β₀ β₁ t B z ≤
      tangentCleanBookMargin β₁ z
        (tangentALog β₀ t - Real.log z) := by
  have hentropy := backward_log_lower_above_five
    (show (1 : ℝ) ≤ 1 + z by linarith [hz.1])
  have happrox := KernelBounds.exp_neg_approx hz
  have hexp :
      Real.exp (-z) ≤
        KernelBounds.expNegTaylor9 z +
          KernelBounds.expNegError10 z := by
    linarith [abs_le.mp happrox]
  have hramseyCoefficient :
      -(1 / 4) * z + β₁ * z ^ 2 +
          2 / 25 * z ^ 3 ≤ 0 := by
    have hz2 : z ^ 2 ≤ z := by
      have hmul :=
        mul_nonneg hz.1 (sub_nonneg.mpr hz.2)
      nlinarith
    rw [show
      -(1 / 4) * z + β₁ * z ^ 2 +
          2 / 25 * z ^ 3 =
        z * (-(1 / 4) + β₁ * z +
          2 / 25 * z ^ 2) by ring]
    apply mul_nonpos_of_nonneg_of_nonpos hz.1
    have hβz :
        β₁ * z ≤ (2 / 25 : ℝ) * 1 :=
      mul_le_mul hβ₁.2 hz.2 hz.1 (by norm_num)
    nlinarith
  have hramsey :
      (-(1 / 4) * z + β₁ * z ^ 2 +
          2 / 25 * z ^ 3) *
          (KernelBounds.expNegTaylor9 z +
            KernelBounds.expNegError10 z) ≤
        ramseyCorrection β₁ z := by
    unfold ramseyCorrection
    exact mul_le_mul_of_nonpos_left hexp
      hramseyCoefficient
  have hx := backward_xlog_lower_two_le
    hβ₁.1 hz hB0 hB hB1
  have ha := backward_alog_lower_le hβ₀ ht
  have hlog := backward_log_upper_below_seven
    hz0 hz.2
  have hy :
      backwardALogLower β₀ t -
          backwardLogUpperBelowSeven z ≤
        tangentALog β₀ t - Real.log z := by
    linarith
  unfold tangentCleanBookMargin backwardBookLowerTwo
  nlinarith [mul_le_mul_of_nonneg_left hentropy
      (show (0 : ℝ) ≤ 1 + z by linarith [hz.1]),
    mul_le_mul_of_nonneg_left hy hz.1]

end

end Arxiv2407_19026
