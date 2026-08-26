import ErdosProblems.Erdos327.Analytic.SieveScheduleAsymptotic
import ErdosProblems.Erdos327.Analytic.EulerProductBounds

/-!
# Error bounds for the finite-sieve schedule

This file verifies the quantitative error estimates attached to the exact
schedule in `SieveSchedule`.  In particular, the reciprocal-prime mass is
small enough for the elementary factorial-tail lemma with the unchanged
choice `R = 128 h²`.
-/

namespace Erdos327.Analytic

open Filter Real Asymptotics

open scoped BigOperators

noncomputable section

/-- The prime cutoff never exceeds the ambient dyadic scale. -/
theorem sieveCutoff_le_dyadicScale (j : ℕ) :
    sieveCutoff j ≤ dyadicScale j := by
  unfold sieveCutoff dyadicScale sieveCutoffExponent
  exact Nat.pow_le_pow_right (by norm_num) (Nat.div_le_self _ _)

/-- Monotonicity of the reciprocal-prime sum. -/
theorem primeInvSum_mono {L X : ℕ} (hLX : L ≤ X) :
    primeInvSum L ≤ primeInvSum X := by
  unfold primeInvSum
  apply Finset.sum_le_sum_of_subset_of_nonneg (primesLE_mono hLX)
  intro p _ _
  positivity

/-- A fixed reserve for the constant and explicit error in Mertens'
reciprocal-prime estimate once the argument is at least four. -/
def sievePrimeReserve : ℝ :=
  |Mertens.Weight.M (f := Mertens.Weight.prime)| +
    (log 4 + 3) / log 4

theorem sievePrimeReserve_nonneg :
    0 ≤ sievePrimeReserve := by
  unfold sievePrimeReserve
  positivity [Real.log_pos (by norm_num : (1 : ℝ) < 4)]

/-- Pointwise Mertens bound in terms of the schedule height, apart from a
fixed additive reserve. -/
theorem primeInvSum_sieveCutoff_le_height_add_reserve
    {j : ℕ} (hdom : 32 * sieveRadius j ≤ j) :
    primeInvSum (sieveCutoff j) ≤
      (sieveHeight j : ℝ) + sievePrimeReserve := by
  have hk : 2 ≤ sieveCutoffExponent j :=
    two_le_sieveCutoffExponent hdom
  have hz4 : 4 ≤ sieveCutoff j := by
    unfold sieveCutoff
    calc
      4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ sieveCutoffExponent j :=
        Nat.pow_le_pow_right (by norm_num) hk
  have hzpos : (0 : ℝ) < sieveCutoff j := by positivity
  have hjpos : (0 : ℝ) < j := by
    have hR := sieveRadius_pos j
    exact_mod_cast (show 0 < j by omega)
  have hlogzpos : 0 < log (sieveCutoff j : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < sieveCutoff j by omega))
  have hlog4pos : 0 < log (4 : ℝ) :=
    Real.log_pos (by norm_num)
  have hlogz_ge :
      log (4 : ℝ) ≤ log (sieveCutoff j : ℝ) :=
    Real.strictMonoOn_log.monotoneOn
      (by norm_num)
      (by simpa only [Set.mem_Ioi] using hzpos)
      (by exact_mod_cast hz4)
  have hlog2lt : log (2 : ℝ) < 1 := by
    linarith [Real.log_two_lt_d9]
  have hlogz_le_j :
      log (sieveCutoff j : ℝ) ≤ (j : ℝ) := by
    have hzscale := sieveCutoff_le_dyadicScale j
    have hscalePos : (0 : ℝ) < dyadicScale j := by
      simp [dyadicScale]
    have hmono :
        log (sieveCutoff j : ℝ) ≤ log (dyadicScale j : ℝ) :=
      Real.strictMonoOn_log.monotoneOn
        (by simpa only [Set.mem_Ioi] using hzpos)
        (by simpa only [Set.mem_Ioi] using hscalePos)
        (by exact_mod_cast hzscale)
    have hscaleLog :
        log (dyadicScale j : ℝ) = (j : ℝ) * log 2 := by
      simp [dyadicScale, Real.log_pow]
    rw [hscaleLog] at hmono
    nlinarith [Real.log_pos (by norm_num : (1 : ℝ) < 2)]
  have hloglog_le :
      log (log (sieveCutoff j : ℝ)) ≤ log (j : ℝ) :=
    Real.strictMonoOn_log.monotoneOn
      (by simpa only [Set.mem_Ioi] using hlogzpos)
      (by simpa only [Set.mem_Ioi] using hjpos)
      hlogz_le_j
  have hj_lt_pow :
      (j : ℝ) < ((2 ^ sieveHeight j : ℕ) : ℝ) := by
    exact_mod_cast
      (show j < 2 ^ sieveHeight j by
        exact (Nat.lt_succ_self j).trans (lt_pow_sieveHeight j))
  have hlogj_lt :
      log (j : ℝ) < (sieveHeight j : ℝ) * log 2 := by
    have hpowpos : (0 : ℝ) < ((2 ^ sieveHeight j : ℕ) : ℝ) := by
      positivity
    have h :=
      Real.strictMonoOn_log
        (by simpa only [Set.mem_Ioi] using hjpos)
        (by simpa only [Set.mem_Ioi] using hpowpos)
        hj_lt_pow
    simpa [Real.log_pow] using h
  have hlogj_le_height :
      log (j : ℝ) ≤ (sieveHeight j : ℝ) := by
    have hh : (0 : ℝ) < sieveHeight j := by
      exact_mod_cast sieveHeight_pos j
    nlinarith
  have herr :
      (log 4 + 3) / log (sieveCutoff j : ℝ) ≤
        (log 4 + 3) / log 4 := by
    exact div_le_div_of_nonneg_left
      (by positivity [Real.log_pos (by norm_num : (1 : ℝ) < 4)])
      hlog4pos hlogz_ge
  have hm :
      Mertens.Weight.M (f := Mertens.Weight.prime) ≤
        |Mertens.Weight.M (f := Mertens.Weight.prime)| :=
    le_abs_self _
  have hbase := primeInvSum_le (show 2 ≤ sieveCutoff j by omega)
  unfold sievePrimeReserve
  linarith

/-- The binary height tends to infinity. -/
theorem tendsto_sieveHeight_atTop :
    Tendsto sieveHeight atTop atTop := by
  refine tendsto_atTop.2 ?_
  intro C
  filter_upwards [eventually_ge_atTop (2 ^ C)] with j hj
  have hpow : 2 ^ C ≤ j + 1 := hj.trans (Nat.le_succ j)
  have hlog :
      C ≤ Nat.log 2 (j + 1) :=
    (Nat.le_log_of_pow_le (by norm_num) hpow)
  unfold sieveHeight
  omega

/-- Eventually the additive Mertens reserve is at most half the schedule
height. -/
theorem eventually_two_mul_sievePrimeReserve_le_height :
    ∀ᶠ j : ℕ in atTop,
      2 * sievePrimeReserve ≤ (sieveHeight j : ℝ) := by
  obtain ⟨C, hC⟩ :=
    exists_nat_ge (2 * sievePrimeReserve)
  have hevent :
      ∀ᶠ j : ℕ in atTop, C ≤ sieveHeight j :=
    (tendsto_sieveHeight_atTop.eventually (eventually_ge_atTop C))
  filter_upwards [hevent] with j hj
  exact hC.trans (by exact_mod_cast hj)

/-- Strong reciprocal-prime estimate for the scheduled cutoff.  The
coefficient `9/2` is deliberately retained: unlike the coarser `6`, it is
strong enough for `R = 128 h²` in `FactorialTailBound`. -/
theorem eventually_three_mul_primeInvSum_sieveCutoff_le :
    ∀ᶠ j : ℕ in atTop,
      3 * primeInvSum (sieveCutoff j) ≤
        (9 / 2 : ℝ) * sieveHeight j := by
  filter_upwards
    [eventually_sieveSchedule_dominates,
      eventually_two_mul_sievePrimeReserve_le_height] with j hdom hreserve
  have hprime :=
    primeInvSum_sieveCutoff_le_height_add_reserve hdom
  linarith

/-- The advertised coarser reciprocal-prime bound. -/
theorem eventually_three_mul_primeInvSum_sieveCutoff_le_six_height :
    ∀ᶠ j : ℕ in atTop,
      3 * primeInvSum (sieveCutoff j) ≤
        6 * sieveHeight j := by
  filter_upwards
    [eventually_three_mul_primeInvSum_sieveCutoff_le] with j hj
  have hh : (0 : ℝ) ≤ sieveHeight j := by positivity
  linarith

/-- The Bonferroni factorial tail at the scheduled parameters. -/
def scheduledFactorialTail (j : ℕ) : ℝ :=
  (3 * primeInvSum (sieveCutoff j)) ^ (2 * sieveRadius j + 1) /
    ((2 * sieveRadius j + 1).factorial : ℝ)

/-- The stronger reciprocal-prime estimate needed by the unchanged
`128 h²` radius implies the geometric factorial-tail bound. -/
theorem scheduledFactorialTail_le_quarter_pow
    {j : ℕ}
    (hμ :
      3 * primeInvSum (sieveCutoff j) ≤
        (9 / 2 : ℝ) * sieveHeight j) :
    scheduledFactorialTail j ≤
      (1 / 4 : ℝ) ^ sieveRadius j := by
  let μ : ℝ := 3 * primeInvSum (sieveCutoff j)
  let R : ℕ := sieveRadius j
  have hμ0 : 0 ≤ μ := by
    dsimp [μ]
    exact mul_nonneg (by norm_num) (primeInvSum_nonneg _)
  have hh : (1 : ℝ) ≤ sieveHeight j := by
    exact_mod_cast sieveHeight_pos j
  have hR : 1 ≤ R := by
    dsimp [R]
    exact sieveRadius_pos j
  have hRcast :
      (R : ℝ) = 128 * (sieveHeight j : ℝ) ^ 2 := by
    simp [R, sieveRadius]
  have hμR : μ ≤ (R : ℝ) := by
    dsimp [μ] at hμ ⊢
    rw [hRcast]
    nlinarith [sq_nonneg ((sieveHeight j : ℝ) - 1)]
  have hμsq : μ ^ 2 ≤ (R : ℝ) / 4 := by
    have hμ' : μ ≤ (9 / 2 : ℝ) * sieveHeight j := by
      simpa [μ] using hμ
    have hsquare :
        μ ^ 2 ≤ ((9 / 2 : ℝ) * sieveHeight j) ^ 2 :=
      (sq_le_sq₀ hμ0
        (mul_nonneg (by norm_num)
          (by positivity : 0 ≤ (sieveHeight j : ℝ)))).2 hμ'
    rw [hRcast]
    nlinarith [sq_nonneg (sieveHeight j : ℝ)]
  have htail :=
    pow_div_factorial_two_mul_add_one_le
      hμ0 hR hμR hμsq
  change
    (3 * primeInvSum (sieveCutoff j)) ^
          (2 * sieveRadius j + 1) /
        ((2 * sieveRadius j + 1).factorial : ℝ) ≤
      (1 / 4 : ℝ) ^ sieveRadius j at htail
  exact htail

/-- The scheduled factorial tail is eventually at most `4⁻ᴿ`. -/
theorem eventually_scheduledFactorialTail_le_quarter_pow :
    ∀ᶠ j : ℕ in atTop,
      scheduledFactorialTail j ≤
        (1 / 4 : ℝ) ^ sieveRadius j := by
  filter_upwards
    [eventually_three_mul_primeInvSum_sieveCutoff_le] with j hj
  exact scheduledFactorialTail_le_quarter_pow hj

/-- The geometric radius bound is already stronger than the required
eighth inverse power of the dyadic index. -/
theorem quarter_pow_sieveRadius_le_inv_add_one_pow_eight (j : ℕ) :
    (1 / 4 : ℝ) ^ sieveRadius j ≤
      1 / ((j + 1 : ℕ) : ℝ) ^ 8 := by
  have hhpos := sieveHeight_pos j
  have hexp :
      8 * sieveHeight j ≤ 2 * sieveRadius j := by
    simp only [sieveRadius]
    nlinarith [show 1 ≤ sieveHeight j by omega]
  have hnat :
      (j + 1) ^ 8 ≤ 4 ^ sieveRadius j := by
    calc
      (j + 1) ^ 8 ≤ (2 ^ sieveHeight j) ^ 8 :=
        Nat.pow_le_pow_left (Nat.le_of_lt (lt_pow_sieveHeight j)) _
      _ = 2 ^ (8 * sieveHeight j) := by
        rw [← pow_mul]
        congr 1
        omega
      _ ≤ 2 ^ (2 * sieveRadius j) :=
        Nat.pow_le_pow_right (by norm_num) hexp
      _ = 4 ^ sieveRadius j := by
        rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul]
  have hleft : (0 : ℝ) < (4 : ℝ) ^ sieveRadius j :=
    pow_pos (by norm_num) _
  have hright : (0 : ℝ) < (((j + 1 : ℕ) : ℝ) ^ 8) :=
    pow_pos (by exact_mod_cast (Nat.zero_lt_succ j)) _
  rw [div_pow]
  norm_num only [one_pow]
  apply (div_le_div_iff₀ hleft hright).2
  norm_num only [one_mul]
  exact_mod_cast hnat

/-- The complete scheduled factorial tail has the desired polynomial
decay. -/
theorem eventually_scheduledFactorialTail_le_inv_add_one_pow_eight :
    ∀ᶠ j : ℕ in atTop,
      scheduledFactorialTail j ≤
        1 / ((j + 1 : ℕ) : ℝ) ^ 8 := by
  filter_upwards
    [eventually_scheduledFactorialTail_le_quarter_pow] with j hj
  exact hj.trans (quarter_pow_sieveRadius_le_inv_add_one_pow_eight j)

/-- Real eighth-root form of the cutoff boundary lemma. -/
theorem sieveCutoff_boundary_le_dyadic_rpow_eighth (j : ℕ) :
    ((sieveCutoff j ^ (2 * sieveRadius j) : ℕ) : ℝ) ≤
      (dyadicScale j : ℝ) ^ (1 / 8 : ℝ) := by
  rw [show (1 / 8 : ℝ) = (8 : ℝ)⁻¹ by norm_num]
  apply (Real.le_rpow_inv_iff_of_pos
    (by positivity : 0 ≤
      ((sieveCutoff j ^ (2 * sieveRadius j) : ℕ) : ℝ))
    (by positivity : 0 ≤ (dyadicScale j : ℝ))
    (by norm_num : (0 : ℝ) < 8)).2
  exact_mod_cast sieveCutoff_boundary_pow_eight_le j

/-- Real eighth-root form of the `3^(2R)` boundary lemma. -/
theorem three_boundary_le_dyadic_rpow_eighth
    {j : ℕ} (hdom : 32 * sieveRadius j ≤ j) :
    (((3 : ℕ) ^ (2 * sieveRadius j) : ℕ) : ℝ) ≤
      (dyadicScale j : ℝ) ^ (1 / 8 : ℝ) := by
  rw [show (1 / 8 : ℝ) = (8 : ℝ)⁻¹ by norm_num]
  apply (Real.le_rpow_inv_iff_of_pos
    (by positivity : 0 ≤
      (((3 : ℕ) ^ (2 * sieveRadius j) : ℕ) : ℝ))
    (by positivity : 0 ≤ (dyadicScale j : ℝ))
    (by norm_num : (0 : ℝ) < 8)).2
  exact_mod_cast three_boundary_pow_eight_le hdom

/-- The cutoff boundary factor itself is at most the dyadic scale. -/
theorem sieveCutoff_boundary_le_dyadicScale (j : ℕ) :
    sieveCutoff j ^ (2 * sieveRadius j) ≤ dyadicScale j := by
  have hpow := sieveCutoff_boundary_pow_eight_le j
  have hone :
      1 ≤ sieveCutoff j ^ (2 * sieveRadius j) := by
    have hpos :
        0 < sieveCutoff j ^ (2 * sieveRadius j) :=
      Nat.pow_pos (by simp [sieveCutoff])
    omega
  exact (le_self_pow hone (by norm_num : (8 : ℕ) ≠ 0)).trans hpow

/-- The exact polynomial boundary supplied by the truncated finite sieve. -/
def scheduledPolynomialBoundary (j : ℕ) : ℝ :=
  ((2 * sieveRadius j + 1 : ℕ) : ℝ) *
    ((sieveCutoff j : ℝ) ^ (2 * sieveRadius j)) *
    ((3 : ℝ) ^ (2 * sieveRadius j)) *
    (9 * (dyadicScale j : ℝ) +
      (sieveCutoff j : ℝ) ^ (2 * sieveRadius j))

/-- Exponential domination in the exact strength needed after multiplying
the polynomial boundary by `(j+1)^8`. -/
theorem eventually_boundary_polynomial_le_dyadic_rpow_three_quarters :
    ∀ᶠ j : ℕ in atTop,
      2570 * (((j + 1 : ℕ) : ℝ) ^ 10) ≤
        (dyadicScale j : ℝ) ^ (3 / 4 : ℝ) := by
  have hb : 0 < log (2 : ℝ) / 2 := by
    positivity [Real.log_pos (by norm_num : (1 : ℝ) < 2)]
  have hlo :
      (fun x : ℝ ↦ 2570 * x ^ 10)
          =o[atTop]
        (fun x : ℝ ↦ exp ((log 2 / 2) * x)) :=
    (isLittleO_pow_exp_pos_mul_atTop 10 hb).const_mul_left 2570
  have hsmall :
      ∀ᶠ x : ℝ in atTop,
        ‖2570 * x ^ 10‖ ≤
          ‖exp ((log 2 / 2) * x)‖ :=
    hlo.eventuallyLE
  have hcast :
      Tendsto (fun j : ℕ ↦ ((j + 1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have hsmallNat :
      ∀ᶠ j : ℕ in atTop,
        ‖2570 * (((j + 1 : ℕ) : ℝ) ^ 10)‖ ≤
          ‖exp ((log 2 / 2) * ((j + 1 : ℕ) : ℝ))‖ :=
    hsmall.filter_mono hcast
  filter_upwards [hsmallNat, eventually_ge_atTop 2] with j hsmallj hj
  have hpoly0 :
      0 ≤ 2570 * (((j + 1 : ℕ) : ℝ) ^ 10) := by positivity
  have hexp0 :
      0 < exp ((log 2 / 2) * ((j + 1 : ℕ) : ℝ)) :=
    exp_pos _
  have hsmallj' :
      2570 * (((j + 1 : ℕ) : ℝ) ^ 10) ≤
        exp ((log 2 / 2) * ((j + 1 : ℕ) : ℝ)) := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg hpoly0,
      abs_of_pos hexp0] using hsmallj
  have hlog2 : 0 < log (2 : ℝ) :=
    Real.log_pos (by norm_num)
  have hjr : (2 : ℝ) ≤ j := by exact_mod_cast hj
  have hproduct :
      0 ≤ ((j : ℝ) - 2) * log 2 :=
    mul_nonneg (sub_nonneg.mpr hjr) hlog2.le
  have hexponent :
      (log 2 / 2) * ((j + 1 : ℕ) : ℝ) ≤
        (3 / 4 : ℝ) * ((j : ℝ) * log 2) := by
    push_cast
    nlinarith
  have hscalePos : (0 : ℝ) < (dyadicScale j : ℝ) := by
    simp [dyadicScale]
  have hrpow :
      (dyadicScale j : ℝ) ^ (3 / 4 : ℝ) =
        exp ((3 / 4 : ℝ) * ((j : ℝ) * log 2)) := by
    rw [Real.rpow_def_of_pos hscalePos]
    congr 1
    simp [dyadicScale, Real.log_pow]
    ring
  rw [hrpow]
  exact hsmallj'.trans (Real.exp_le_exp.mpr hexponent)

/-- Pointwise assembly of the full polynomial boundary from the two
eighth-power estimates and the exponential-over-polynomial comparison. -/
theorem scheduledPolynomialBoundary_le_dyadic_sq_div_add_one_pow_eight
    {j : ℕ}
    (hdom : 32 * sieveRadius j ≤ j)
    (hpoly :
      2570 * (((j + 1 : ℕ) : ℝ) ^ 10) ≤
        (dyadicScale j : ℝ) ^ (3 / 4 : ℝ)) :
    scheduledPolynomialBoundary j ≤
      (dyadicScale j : ℝ) ^ 2 /
        (((j + 1 : ℕ) : ℝ) ^ 8) := by
  have hXpos : (0 : ℝ) < (dyadicScale j : ℝ) := by
    simp [dyadicScale]
  have hjpos : (0 : ℝ) < ((j + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.zero_lt_succ j
  have hDroot :
      (sieveCutoff j : ℝ) ^ (2 * sieveRadius j) ≤
        (dyadicScale j : ℝ) ^ (1 / 8 : ℝ) := by
    simpa only [Nat.cast_pow] using
      sieveCutoff_boundary_le_dyadic_rpow_eighth j
  have hQroot :
      (3 : ℝ) ^ (2 * sieveRadius j) ≤
        (dyadicScale j : ℝ) ^ (1 / 8 : ℝ) := by
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using
      three_boundary_le_dyadic_rpow_eighth hdom
  have hDscale :
      (sieveCutoff j : ℝ) ^ (2 * sieveRadius j) ≤
        (dyadicScale j : ℝ) := by
    exact_mod_cast sieveCutoff_boundary_le_dyadicScale j
  have hmNat :
      2 * sieveRadius j + 1 ≤ 257 * (j + 1) ^ 2 := by
    have hh := sieveHeight_le_add_one j
    have hsq :
        sieveHeight j ^ 2 ≤ (j + 1) ^ 2 :=
      Nat.pow_le_pow_left hh 2
    have hheightSqPos :
        1 ≤ sieveHeight j ^ 2 := by
      have := sieveHeight_pos j
      nlinarith
    calc
      2 * sieveRadius j + 1 =
          256 * sieveHeight j ^ 2 + 1 := by
            simp [sieveRadius]
            ring
      _ ≤ 257 * sieveHeight j ^ 2 := by
        omega
      _ ≤ 257 * (j + 1) ^ 2 :=
        Nat.mul_le_mul_left 257 hsq
  have hm :
      (((2 * sieveRadius j + 1 : ℕ) : ℝ)) ≤
        257 * (((j + 1 : ℕ) : ℝ) ^ 2) := by
    exact_mod_cast hmNat
  have hbracket :
      9 * (dyadicScale j : ℝ) +
          (sieveCutoff j : ℝ) ^ (2 * sieveRadius j) ≤
        10 * (dyadicScale j : ℝ) := by
    linarith
  have hrpowProduct :
      (dyadicScale j : ℝ) ^ (1 / 8 : ℝ) *
          (dyadicScale j : ℝ) ^ (1 / 8 : ℝ) *
          (dyadicScale j : ℝ) =
        (dyadicScale j : ℝ) ^ (5 / 4 : ℝ) := by
    calc
      (dyadicScale j : ℝ) ^ (1 / 8 : ℝ) *
            (dyadicScale j : ℝ) ^ (1 / 8 : ℝ) *
            (dyadicScale j : ℝ)
          =
        (dyadicScale j : ℝ) ^ ((1 / 8 : ℝ) + 1 / 8) *
            (dyadicScale j : ℝ) ^ (1 : ℝ) := by
              rw [Real.rpow_add hXpos, Real.rpow_one]
      _ = (dyadicScale j : ℝ) ^
            (((1 / 8 : ℝ) + 1 / 8) + 1) := by
              rw [← Real.rpow_add hXpos]
      _ = (dyadicScale j : ℝ) ^ (5 / 4 : ℝ) := by
              congr 1
              norm_num
  have hmajor :
      scheduledPolynomialBoundary j ≤
        2570 * (((j + 1 : ℕ) : ℝ) ^ 2) *
          (dyadicScale j : ℝ) ^ (5 / 4 : ℝ) := by
    unfold scheduledPolynomialBoundary
    calc
      (((2 * sieveRadius j + 1 : ℕ) : ℝ)) *
            (sieveCutoff j : ℝ) ^ (2 * sieveRadius j) *
            (3 : ℝ) ^ (2 * sieveRadius j) *
            (9 * (dyadicScale j : ℝ) +
              (sieveCutoff j : ℝ) ^ (2 * sieveRadius j))
          ≤
        (257 * (((j + 1 : ℕ) : ℝ) ^ 2)) *
            (sieveCutoff j : ℝ) ^ (2 * sieveRadius j) *
            (3 : ℝ) ^ (2 * sieveRadius j) *
            (9 * (dyadicScale j : ℝ) +
              (sieveCutoff j : ℝ) ^ (2 * sieveRadius j)) := by
              gcongr
      _ ≤
        (257 * (((j + 1 : ℕ) : ℝ) ^ 2)) *
            (dyadicScale j : ℝ) ^ (1 / 8 : ℝ) *
            (dyadicScale j : ℝ) ^ (1 / 8 : ℝ) *
            (10 * (dyadicScale j : ℝ)) := by
              gcongr
      _ =
        2570 * (((j + 1 : ℕ) : ℝ) ^ 2) *
          (dyadicScale j : ℝ) ^ (5 / 4 : ℝ) := by
            rw [← hrpowProduct]
            ring
  apply (le_div_iff₀ (pow_pos hjpos 8)).2
  calc
    scheduledPolynomialBoundary j *
          (((j + 1 : ℕ) : ℝ) ^ 8)
        ≤
      (2570 * (((j + 1 : ℕ) : ℝ) ^ 2) *
          (dyadicScale j : ℝ) ^ (5 / 4 : ℝ)) *
        (((j + 1 : ℕ) : ℝ) ^ 8) :=
      mul_le_mul_of_nonneg_right hmajor (by positivity)
    _ =
      (2570 * (((j + 1 : ℕ) : ℝ) ^ 10)) *
        (dyadicScale j : ℝ) ^ (5 / 4 : ℝ) := by ring
    _ ≤
      (dyadicScale j : ℝ) ^ (3 / 4 : ℝ) *
        (dyadicScale j : ℝ) ^ (5 / 4 : ℝ) :=
      mul_le_mul_of_nonneg_right hpoly (Real.rpow_nonneg (by positivity) _)
    _ = (dyadicScale j : ℝ) ^ 2 := by
      rw [← Real.rpow_add hXpos]
      norm_num [Real.rpow_natCast]

/-- The full four-factor polynomial boundary is eventually at most the
target dyadic square divided by `(j+1)^8`. -/
theorem eventually_scheduledPolynomialBoundary_le :
    ∀ᶠ j : ℕ in atTop,
      scheduledPolynomialBoundary j ≤
        (dyadicScale j : ℝ) ^ 2 /
          (((j + 1 : ℕ) : ℝ) ^ 8) := by
  filter_upwards
    [eventually_sieveSchedule_dominates,
      eventually_boundary_polynomial_le_dyadic_rpow_three_quarters]
      with j hdom hpoly
  exact
    scheduledPolynomialBoundary_le_dyadic_sq_div_add_one_pow_eight
      hdom hpoly

end

end Erdos327.Analytic
