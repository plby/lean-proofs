import ErdosProblems.Erdos1002.NearResonantCarrierLeakageQuantitative

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# The growing derivative order in the near-carrier leakage estimate

The manuscript chooses `j = ceil(2 L^(2/3))`, where `L = log N`.
This file records that choice literally, bounds the ceiling with its full
constant, absorbs the factorial by `j! ≤ j^j`, and proves the elementary
exponential-win calculation used after the dyadic block estimate.
-/

open Filter MeasureTheory Set
open scoped BigOperators Real

namespace Erdos1002

noncomputable section

/-- The derivative order used for low-denominator carrier leakage. -/
def nearLeakageDerivativeOrder (L : ℝ) : ℕ :=
  ⌈2 * L ^ (2 / 3 : ℝ)⌉₊

theorem two_mul_rpow_le_nearLeakageDerivativeOrder (L : ℝ) :
    2 * L ^ (2 / 3 : ℝ) ≤ (nearLeakageDerivativeOrder L : ℝ) := by
  exact Nat.le_ceil _

/-- The ceiling changes the selected order by at most a harmless factor
`3/2` once `L ≥ 1`. -/
theorem nearLeakageDerivativeOrder_le_three_mul_rpow
    (L : ℝ) (hL : 1 ≤ L) :
    (nearLeakageDerivativeOrder L : ℝ) ≤
      3 * L ^ (2 / 3 : ℝ) := by
  have hu : 1 ≤ L ^ (2 / 3 : ℝ) := by
    simpa only [Real.one_rpow] using!
      Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1) hL
        (by norm_num : (0 : ℝ) ≤ 2 / 3)
  have hnonneg : 0 ≤ 2 * L ^ (2 / 3 : ℝ) := by positivity
  have hceil := Nat.ceil_lt_add_one hnonneg
  dsimp [nearLeakageDerivativeOrder]
  linarith

/-- The displayed `j!` dependence is absorbed into the same `j`-th power
as the dilation and the fixed Gevrey constant. -/
theorem gevrey_factorial_scale_le_power
    (a : ℝ) (j : ℕ) (ha : 0 < a) :
    (192 : ℝ) ^ j * (j.factorial : ℝ) ^ 2 * a⁻¹ ^ j ≤
      (192 * (j : ℝ) ^ 2 / a) ^ j := by
  have hfac : (j.factorial : ℝ) ≤ (j : ℝ) ^ j := by
    exact_mod_cast Nat.factorial_le_pow j
  have hfacSq : (j.factorial : ℝ) ^ 2 ≤ ((j : ℝ) ^ j) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hfac 2
  calc
    (192 : ℝ) ^ j * (j.factorial : ℝ) ^ 2 * a⁻¹ ^ j ≤
        (192 : ℝ) ^ j * ((j : ℝ) ^ j) ^ 2 * a⁻¹ ^ j := by
      gcongr
    _ = (192 * (j : ℝ) ^ 2 / a) ^ j := by
      rw [div_pow, mul_pow, div_eq_mul_inv, ← inv_pow]
      congr 2
      rw [← pow_mul, ← pow_mul]
      congr 1
      omega

/-- Combining the low-denominator cutoff `P/N ≤ exp(-L^(1/3))`
with an eventual upper bound for the Gevrey/factorial base leaves the
strict exponent `-(7/8)L^(1/3)`. -/
theorem nearLeakage_combined_base_le
    (L P N a : ℝ) (j : ℕ) (ha : 0 < a)
    (hPN : P / N ≤ Real.exp (-L ^ (1 / 3 : ℝ)))
    (hgevrey : 192 * (j : ℝ) ^ 2 / a ≤
      Real.exp ((1 / 8 : ℝ) * L ^ (1 / 3 : ℝ))) :
    (P / N) * (192 * (j : ℝ) ^ 2 / a) ≤
      Real.exp (-(7 / 8 : ℝ) * L ^ (1 / 3 : ℝ)) := by
  calc
    (P / N) * (192 * (j : ℝ) ^ 2 / a) ≤
        Real.exp (-L ^ (1 / 3 : ℝ)) *
          Real.exp ((1 / 8 : ℝ) * L ^ (1 / 3 : ℝ)) :=
      mul_le_mul hPN hgevrey (by positivity) (Real.exp_pos _).le
    _ = Real.exp (-(7 / 8 : ℝ) * L ^ (1 / 3 : ℝ)) := by
      rw [← Real.exp_add]
      congr 1
      ring

/-- The numerical core of the manuscript's leakage logarithm.  The main
base contributes at most `exp(-(7/8)L^(1/3))`; the chosen derivative order
therefore contributes `exp(-(7/2)L)`.  Even after allowing a complete
`exp L` prefactor, the squared leakage is at most `exp(-(5/2)L)`.

The hypotheses are deliberately scalar and unpacked, so later assembly can
verify the cutoff, Gevrey-base, and prefactor inequalities separately. -/
theorem nearLeakage_exponential_win
    (L base prefactor : ℝ) (j : ℕ) (hL : 0 < L)
    (hbase0 : 0 ≤ base)
    (hbase : base ≤
      Real.exp (-(7 / 8 : ℝ) * L ^ (1 / 3 : ℝ)))
    (hj : 2 * L ^ (2 / 3 : ℝ) ≤ (j : ℝ))
    (hprefactor : prefactor ≤ Real.exp L) :
    prefactor * base ^ (2 * j) ≤
      Real.exp (-(5 / 2 : ℝ) * L) := by
  have hv : 0 ≤ L ^ (1 / 3 : ℝ) := Real.rpow_nonneg hL.le _
  have hu : L ^ (2 / 3 : ℝ) * L ^ (1 / 3 : ℝ) = L := by
    rw [← Real.rpow_add hL]
    norm_num [Real.rpow_one]
  have hjv : 2 * L ≤ (j : ℝ) * L ^ (1 / 3 : ℝ) := by
    have hmul := mul_le_mul_of_nonneg_right hj hv
    nlinarith
  have hpow := pow_le_pow_left₀ hbase0 hbase (2 * j)
  calc
    prefactor * base ^ (2 * j) ≤
        Real.exp L *
          (Real.exp (-(7 / 8 : ℝ) * L ^ (1 / 3 : ℝ))) ^ (2 * j) :=
      mul_le_mul hprefactor hpow (pow_nonneg hbase0 _) (Real.exp_pos _).le
    _ = Real.exp
        (L + ((2 * j : ℕ) : ℝ) *
          (-(7 / 8 : ℝ) * L ^ (1 / 3 : ℝ))) := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]
    _ ≤ Real.exp (-(5 / 2 : ℝ) * L) := by
      apply Real.exp_le_exp.mpr
      push_cast
      nlinarith

/-- The preceding exponential win with the paper's literal ceiling choice. -/
theorem nearLeakage_exponential_win_at_selected_order
    (L base prefactor : ℝ) (hL : 0 < L)
    (hbase0 : 0 ≤ base)
    (hbase : base ≤
      Real.exp (-(7 / 8 : ℝ) * L ^ (1 / 3 : ℝ)))
    (hprefactor : prefactor ≤ Real.exp L) :
    prefactor * base ^ (2 * nearLeakageDerivativeOrder L) ≤
      Real.exp (-(5 / 2 : ℝ) * L) :=
  nearLeakage_exponential_win L base prefactor
    (nearLeakageDerivativeOrder L) hL hbase0 hbase
      (two_mul_rpow_le_nearLeakageDerivativeOrder L) hprefactor

/-! ## The exact block estimate in factored scalar form -/

/-- The raw right side of the physical block leakage estimate, after
division by the elementary carrier scale, has exactly the paper's
`prefactor * base^(2j)` form.  This lemma performs all cancellation in
`ℝ`; the next theorem transports it back to coefficient energy. -/
theorem nearLeakage_raw_scalar_le_factored
    (N P j : ℕ) (ell : ℤ) (a : ℝ)
    (hN : 0 < N) (hP : 0 < P) (ha : 0 < a) :
    (P : ℝ) ^ 2 *
        (‖bernoulliMarkFourierCoefficient ell‖ ^ 2 *
          ((2 / (P : ℝ)) * (P : ℝ) ^ (4 * j)) *
            ((2 * nearGevreyProfileConstant * 192 ^ j *
              (j.factorial : ℝ) ^ 2 * a⁻¹ ^ j) ^ 2 * (32 / a))) ≤
      (((N : ℝ) * (P : ℝ)) ^ (2 * j)) *
        (‖bernoulliMarkFourierCoefficient ell‖ ^ 2 *
          (256 * nearGevreyProfileConstant ^ 2 * (P : ℝ) / a) *
            (((P : ℝ) / (N : ℝ)) *
              (192 * (j : ℝ) ^ 2 / a)) ^ (2 * j)) := by
  let F : ℝ := (192 : ℝ) ^ j * (j.factorial : ℝ) ^ 2 * a⁻¹ ^ j
  let G : ℝ := 192 * (j : ℝ) ^ 2 / a
  let C : ℝ := ‖bernoulliMarkFourierCoefficient ell‖ ^ 2 *
    (256 * nearGevreyProfileConstant ^ 2 * (P : ℝ) / a)
  have hF : F ≤ G ^ j := by
    dsimp [F, G]
    exact gevrey_factorial_scale_le_power a j ha
  have hF0 : 0 ≤ F := by dsimp [F]; positivity
  have hG0 : 0 ≤ G := by dsimp [G]; positivity
  have hFsq : F ^ 2 ≤ G ^ (2 * j) := by
    calc
      F ^ 2 ≤ (G ^ j) ^ 2 := pow_le_pow_left₀ hF0 hF 2
      _ = G ^ (2 * j) := by rw [← pow_mul]; congr 1; omega
  have hC0 : 0 ≤ C := by dsimp [C]; positivity
  have hPpow : (P : ℝ) ^ (4 * j) =
      (P : ℝ) ^ (2 * j) * (P : ℝ) ^ (2 * j) := by
    rw [← pow_add]
    congr 1
    omega
  have hleft :
      (P : ℝ) ^ 2 *
          (‖bernoulliMarkFourierCoefficient ell‖ ^ 2 *
            ((2 / (P : ℝ)) * (P : ℝ) ^ (4 * j)) *
              ((2 * nearGevreyProfileConstant * 192 ^ j *
                (j.factorial : ℝ) ^ 2 * a⁻¹ ^ j) ^ 2 * (32 / a))) =
        C * (P : ℝ) ^ (4 * j) * F ^ 2 := by
    dsimp [C, F]
    field_simp
    ring
  have hright :
      (((N : ℝ) * (P : ℝ)) ^ (2 * j)) *
          (C * ((((P : ℝ) / (N : ℝ)) * G) ^ (2 * j))) =
        C * (P : ℝ) ^ (4 * j) * G ^ (2 * j) := by
    rw [mul_pow, mul_pow, div_pow, hPpow]
    field_simp
  rw [hleft]
  calc
    C * (P : ℝ) ^ (4 * j) * F ^ 2 ≤
        C * (P : ℝ) ^ (4 * j) * G ^ (2 * j) := by
      exact mul_le_mul_of_nonneg_left hFsq
        (mul_nonneg hC0 (by positivity))
    _ = (((N : ℝ) * (P : ℝ)) ^ (2 * j)) *
        (‖bernoulliMarkFourierCoefficient ell‖ ^ 2 *
          (256 * nearGevreyProfileConstant ^ 2 * (P : ℝ) / a) *
            (((P : ℝ) / (N : ℝ)) *
              (192 * (j : ℝ) ^ 2 / a)) ^ (2 * j)) := by
      dsimp [C, G]
      exact hright.symm

/-- Unscaled leakage energy of one actual physical dyadic block.  The
right side is now precisely a nonnegative prefactor times the combined
Gevrey/carrier base to the power `2j`, ready for the selected-order
exponential lemma. -/
theorem coefficientEnergy_physicalNearCarrierBlock_le_factored
    (N P j : ℕ) (ell : ℤ) (a ε : ℝ)
    (hN : 0 < N) (hP : 4 ≤ P) (hell : ell ≠ 0)
    (ha : 0 < a) (hε : 0 < ε) (haε : a ≤ ε / 4)
    (hεhalf : ε < 1 / 2) :
    coefficientEnergy
        (physicalNearCarrierBlockLeakageCoefficients N ell a ε P) ≤
      ENNReal.ofReal
        (‖bernoulliMarkFourierCoefficient ell‖ ^ 2 *
          (256 * nearGevreyProfileConstant ^ 2 * (P : ℝ) / a) *
            ((((P : ℝ) / (N : ℝ)) *
              (192 * (j : ℝ) ^ 2 / a)) ^ (2 * j))) := by
  let S : ℝ := ((N : ℝ) * (P : ℝ)) ^ (2 * j)
  let T : ℝ :=
    ‖bernoulliMarkFourierCoefficient ell‖ ^ 2 *
      (256 * nearGevreyProfileConstant ^ 2 * (P : ℝ) / a) *
        ((((P : ℝ) / (N : ℝ)) *
          (192 * (j : ℝ) ^ 2 / a)) ^ (2 * j))
  let R : ℝ :=
    ‖bernoulliMarkFourierCoefficient ell‖ ^ 2 *
      ((2 / (P : ℝ)) * (P : ℝ) ^ (4 * j)) *
        ((2 * nearGevreyProfileConstant * 192 ^ j *
          (j.factorial : ℝ) ^ 2 * a⁻¹ ^ j) ^ 2 * (32 / a))
  let scale : ℝ :=
    (2 * Real.pi * (nearCarrierScale N ell P / 4)) ^ (2 * j)
  have hscaled :=
    coefficientEnergy_physicalNearCarrierBlock_scaled_le_scalarGevrey
      N P j ell a ε hN hP hell ha hε haε hεhalf
  have hellOne : (1 : ℝ) ≤ |(ell : ℝ)| := by
    exact_mod_cast Int.one_le_abs hell
  have hpiHalf : (1 : ℝ) ≤ Real.pi / 2 := by
    nlinarith [Real.pi_gt_three]
  have hfactor : (1 : ℝ) ≤ (Real.pi / 2) * |(ell : ℝ)| := by
    calc
      (1 : ℝ) = 1 * 1 := by ring
      _ ≤ (Real.pi / 2) * |(ell : ℝ)| :=
        mul_le_mul hpiHalf hellOne (by norm_num) (by positivity)
  have hNP0 : 0 ≤ (N : ℝ) * (P : ℝ) := by positivity
  have hbase : (N : ℝ) * (P : ℝ) ≤
      2 * Real.pi * (nearCarrierScale N ell P / 4) := by
    calc
      (N : ℝ) * (P : ℝ) =
          1 * ((N : ℝ) * (P : ℝ)) := by ring
      _ ≤ ((Real.pi / 2) * |(ell : ℝ)|) *
          ((N : ℝ) * (P : ℝ)) :=
        mul_le_mul_of_nonneg_right hfactor hNP0
      _ = 2 * Real.pi * (nearCarrierScale N ell P / 4) := by
        unfold nearCarrierScale
        ring
  have hSscale : S ≤ scale := by
    dsimp [S, scale]
    exact pow_le_pow_left₀ hNP0 hbase (2 * j)
  have hSpos : 0 < S := by dsimp [S]; positivity
  have hT0 : 0 ≤ T := by dsimp [T]; positivity
  have hR0 : 0 ≤ R := by dsimp [R]; positivity
  have hraw : (P : ℝ) ^ 2 * R ≤ S * T := by
    dsimp [R, S, T]
    exact nearLeakage_raw_scalar_le_factored N P j ell a hN (by omega) ha
  have hRenn : (P : ENNReal) ^ 2 * ENNReal.ofReal R ≤
      ENNReal.ofReal (S * T) := by
    calc
      (P : ENNReal) ^ 2 * ENNReal.ofReal R =
          ENNReal.ofReal ((P : ℝ) ^ 2 * R) := by
        rw [ENNReal.ofReal_mul (sq_nonneg (P : ℝ)),
          ENNReal.ofReal_pow (by positivity : (0 : ℝ) ≤ (P : ℝ))]
        simp
      _ ≤ ENNReal.ofReal (S * T) := ENNReal.ofReal_le_ofReal hraw
  have hmul : ENNReal.ofReal S *
      coefficientEnergy
        (physicalNearCarrierBlockLeakageCoefficients N ell a ε P) ≤
      ENNReal.ofReal S * ENNReal.ofReal T := by
    calc
      ENNReal.ofReal S *
          coefficientEnergy
            (physicalNearCarrierBlockLeakageCoefficients N ell a ε P) ≤
        ENNReal.ofReal scale *
          coefficientEnergy
            (physicalNearCarrierBlockLeakageCoefficients N ell a ε P) :=
        by gcongr
      _ ≤ (P : ENNReal) ^ 2 * ENNReal.ofReal R := by
        simpa only [scale, R] using! hscaled
      _ ≤ ENNReal.ofReal (S * T) := hRenn
      _ = ENNReal.ofReal S * ENNReal.ofReal T := by
        rw [ENNReal.ofReal_mul hSpos.le]
  have hSzero : ENNReal.ofReal S ≠ 0 :=
    ENNReal.ofReal_ne_zero_iff.mpr hSpos
  have hcancel :=
    (ENNReal.mul_le_mul_iff_right hSzero ENNReal.ofReal_ne_top).mp hmul
  simpa only [T] using! hcancel

/-- One-block leakage at the manuscript's literal growing derivative order.
The only remaining hypotheses are the three transparent scalar inequalities:
the low-denominator cutoff, factorial-base absorption, and an `exp L`
prefactor bound. -/
theorem coefficientEnergy_physicalNearCarrierBlock_selected_le_exp
    (N P : ℕ) (ell : ℤ) (a ε L : ℝ)
    (hN : 0 < N) (hP : 4 ≤ P) (hell : ell ≠ 0)
    (ha : 0 < a) (hε : 0 < ε) (haε : a ≤ ε / 4)
    (hεhalf : ε < 1 / 2) (hL : 0 < L)
    (hPN : (P : ℝ) / (N : ℝ) ≤
      Real.exp (-L ^ (1 / 3 : ℝ)))
    (hgevrey : 192 * (nearLeakageDerivativeOrder L : ℝ) ^ 2 / a ≤
      Real.exp ((1 / 8 : ℝ) * L ^ (1 / 3 : ℝ)))
    (hprefactor :
      ‖bernoulliMarkFourierCoefficient ell‖ ^ 2 *
        (256 * nearGevreyProfileConstant ^ 2 * (P : ℝ) / a) ≤
          Real.exp L) :
    coefficientEnergy
        (physicalNearCarrierBlockLeakageCoefficients N ell a ε P) ≤
      ENNReal.ofReal (Real.exp (-(5 / 2 : ℝ) * L)) := by
  let j := nearLeakageDerivativeOrder L
  let base : ℝ := ((P : ℝ) / (N : ℝ)) *
    (192 * (j : ℝ) ^ 2 / a)
  let prefactor : ℝ :=
    ‖bernoulliMarkFourierCoefficient ell‖ ^ 2 *
      (256 * nearGevreyProfileConstant ^ 2 * (P : ℝ) / a)
  have hblock := coefficientEnergy_physicalNearCarrierBlock_le_factored
    N P j ell a ε hN hP hell ha hε haε hεhalf
  have hbase0 : 0 ≤ base := by dsimp [base]; positivity
  have hbase : base ≤
      Real.exp (-(7 / 8 : ℝ) * L ^ (1 / 3 : ℝ)) := by
    dsimp [base, j]
    exact nearLeakage_combined_base_le
      L (P : ℝ) (N : ℝ) a (nearLeakageDerivativeOrder L)
        ha hPN hgevrey
  have hreal : prefactor * base ^ (2 * j) ≤
      Real.exp (-(5 / 2 : ℝ) * L) := by
    exact nearLeakage_exponential_win_at_selected_order
      L base prefactor hL hbase0 hbase (by simpa only [prefactor] using! hprefactor)
  exact hblock.trans (by
    apply ENNReal.ofReal_le_ofReal
    simpa only [j, base, prefactor] using! hreal)

/-- Carrier-sensitive version of the selected-order estimate.  Keeping the
Bernoulli coefficient outside the exponential bound is what permits the
final absolutely summable carrier-mode aggregation. -/
theorem coefficientEnergy_physicalNearCarrierBlock_selected_le_coeff_mul_exp
    (N P : ℕ) (ell : ℤ) (a ε L : ℝ)
    (hN : 0 < N) (hP : 4 ≤ P) (hell : ell ≠ 0)
    (ha : 0 < a) (hε : 0 < ε) (haε : a ≤ ε / 4)
    (hεhalf : ε < 1 / 2) (hL : 0 < L)
    (hPN : (P : ℝ) / (N : ℝ) ≤
      Real.exp (-L ^ (1 / 3 : ℝ)))
    (hgevrey : 192 * (nearLeakageDerivativeOrder L : ℝ) ^ 2 / a ≤
      Real.exp ((1 / 8 : ℝ) * L ^ (1 / 3 : ℝ)))
    (hprefactor :
      256 * nearGevreyProfileConstant ^ 2 * (P : ℝ) / a ≤
        Real.exp L) :
    coefficientEnergy
        (physicalNearCarrierBlockLeakageCoefficients N ell a ε P) ≤
      ENNReal.ofReal
        (‖bernoulliMarkFourierCoefficient ell‖ ^ 2 *
          Real.exp (-(5 / 2 : ℝ) * L)) := by
  let j := nearLeakageDerivativeOrder L
  let base : ℝ := ((P : ℝ) / (N : ℝ)) *
    (192 * (j : ℝ) ^ 2 / a)
  let prefactor : ℝ :=
    256 * nearGevreyProfileConstant ^ 2 * (P : ℝ) / a
  have hblock := coefficientEnergy_physicalNearCarrierBlock_le_factored
    N P j ell a ε hN hP hell ha hε haε hεhalf
  have hbase0 : 0 ≤ base := by dsimp [base]; positivity
  have hbase : base ≤
      Real.exp (-(7 / 8 : ℝ) * L ^ (1 / 3 : ℝ)) := by
    dsimp [base, j]
    exact nearLeakage_combined_base_le
      L (P : ℝ) (N : ℝ) a (nearLeakageDerivativeOrder L)
        ha hPN hgevrey
  have hreal : prefactor * base ^ (2 * j) ≤
      Real.exp (-(5 / 2 : ℝ) * L) := by
    exact nearLeakage_exponential_win_at_selected_order
      L base prefactor hL hbase0 hbase
        (by simpa only [prefactor] using! hprefactor)
  exact hblock.trans (by
    apply ENNReal.ofReal_le_ofReal
    have hcoeff0 : 0 ≤ ‖bernoulliMarkFourierCoefficient ell‖ ^ 2 :=
      sq_nonneg _
    have hm := mul_le_mul_of_nonneg_left hreal hcoeff0
    simpa only [j, base, prefactor, mul_assoc] using! hm)

/-! ## Discharging the eventual scalar hypotheses -/

/-- A fixed nonnegative multiple of a polynomial is eventually dominated
by any positive exponential. -/
theorem eventually_const_mul_pow_le_exp
    (C : ℝ) (k : ℕ) (b : ℝ) (hC : 0 ≤ C) (hb : 0 < b) :
    ∀ᶠ x : ℝ in atTop, C * x ^ k ≤ Real.exp (b * x) := by
  have hlittle :=
    (isLittleO_pow_exp_pos_mul_atTop k hb).const_mul_left C
  have hbound := hlittle.bound (by norm_num : (0 : ℝ) < 1)
  filter_upwards [hbound, eventually_ge_atTop (0 : ℝ)] with x hx hx0
  have hleft : 0 ≤ C * x ^ k := mul_nonneg hC (by positivity)
  simpa only [Real.norm_eq_abs, abs_of_nonneg hleft,
    abs_of_pos (Real.exp_pos _), one_mul] using! hx

/-- For fixed `A>0`, the selected derivative order satisfies the Gevrey
base inequality required above once `L` is large.  The proof makes the
polynomial degree `7` explicit after putting `x=L^(1/3)`. -/
theorem eventually_nearLeakage_selected_gevrey_base
    (A : ℝ) (hA : 0 < A) :
    ∀ᶠ L : ℝ in atTop,
      192 * (nearLeakageDerivativeOrder L : ℝ) ^ 2 / (A / L) ≤
        Real.exp ((1 / 8 : ℝ) * L ^ (1 / 3 : ℝ)) := by
  let C : ℝ := 1728 / A
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hxEventually : ∀ᶠ x : ℝ in atTop,
      C * x ^ 7 ≤ Real.exp ((1 / 8 : ℝ) * x) :=
    eventually_const_mul_pow_le_exp C 7 (1 / 8) hC (by norm_num)
  have hrpow : Tendsto (fun L : ℝ ↦ L ^ (1 / 3 : ℝ)) atTop atTop :=
    tendsto_rpow_atTop (by norm_num)
  have hpoly := hrpow.eventually hxEventually
  filter_upwards [hpoly, eventually_ge_atTop (1 : ℝ)] with L hpoly hL
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hj := nearLeakageDerivativeOrder_le_three_mul_rpow L hL
  have hj0 : 0 ≤ (nearLeakageDerivativeOrder L : ℝ) := by positivity
  have hL23 : 0 ≤ L ^ (2 / 3 : ℝ) := Real.rpow_nonneg hLpos.le _
  have hjSq : (nearLeakageDerivativeOrder L : ℝ) ^ 2 ≤
      9 * L ^ (4 / 3 : ℝ) := by
    have hsquare := pow_le_pow_left₀ hj0 hj 2
    calc
      (nearLeakageDerivativeOrder L : ℝ) ^ 2 ≤
          (3 * L ^ (2 / 3 : ℝ)) ^ 2 := hsquare
      _ = 9 * L ^ (4 / 3 : ℝ) := by
        rw [mul_pow, show (3 : ℝ) ^ 2 = 9 by norm_num,
          ← Real.rpow_natCast, ← Real.rpow_mul hLpos.le]
        norm_num
  have hLpower : L ^ (4 / 3 : ℝ) * L = L ^ (7 / 3 : ℝ) := by
    calc
      L ^ (4 / 3 : ℝ) * L =
          L ^ (4 / 3 : ℝ) * L ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = L ^ (4 / 3 + 1 : ℝ) := (Real.rpow_add hLpos  _ _).symm
      _ = L ^ (7 / 3 : ℝ) := by norm_num
  have hxpower : (L ^ (1 / 3 : ℝ)) ^ 7 = L ^ (7 / 3 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hLpos.le]
    norm_num
  calc
    192 * (nearLeakageDerivativeOrder L : ℝ) ^ 2 / (A / L) =
        (192 / A) * (nearLeakageDerivativeOrder L : ℝ) ^ 2 * L := by
      field_simp
    _ ≤ (192 / A) * (9 * L ^ (4 / 3 : ℝ)) * L := by
      gcongr
    _ = C * (L ^ (1 / 3 : ℝ)) ^ 7 := by
      dsimp [C]
      rw [hxpower, ← hLpower]
      ring
    _ ≤ Real.exp ((1 / 8 : ℝ) * L ^ (1 / 3 : ℝ)) := hpoly

/-- A coarse uniform bound for every Bernoulli carrier coefficient. -/
theorem norm_bernoulliMarkFourierCoefficient_le_one (ell : ℤ) :
    ‖bernoulliMarkFourierCoefficient ell‖ ≤ 1 := by
  by_cases hell : ell = 0
  · subst ell
    norm_num [bernoulliMarkFourierCoefficient]
  · rw [bernoulliMarkFourierCoefficient, if_neg hell, norm_neg, norm_div]
    simp only [norm_one, norm_mul, norm_pow, Complex.norm_intCast,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    rw [show ‖(4 : ℂ)‖ = (4 : ℝ) by norm_num]
    have hellOne : (1 : ℝ) ≤ |(ell : ℝ)| := by
      exact_mod_cast Int.one_le_abs hell
    have hden : (1 : ℝ) ≤ 4 * Real.pi ^ 2 * |(ell : ℝ)| ^ 2 := by
      have hpi : (1 : ℝ) ≤ 4 * Real.pi ^ 2 := by
        nlinarith [Real.pi_gt_three]
      nlinarith [sq_nonneg (|(ell : ℝ)| - 1)]
    simpa only [div_eq_mul_inv, one_mul] using!
      (inv_le_one_of_one_le₀ hden)

/-- The low-denominator cutoff also absorbs the whole scalar prefactor,
uniformly in the nonzero carrier mode, once `L` is large and
`exp L = N`. -/
theorem eventually_nearLeakage_prefactor_le_exp
    (A : ℝ) (hA : 0 < A) :
    ∀ᶠ L : ℝ in atTop, ∀ (N P : ℕ) (ell : ℤ),
      0 < N →
      Real.exp L = (N : ℝ) →
      (P : ℝ) / (N : ℝ) ≤ Real.exp (-L ^ (1 / 3 : ℝ)) →
      ‖bernoulliMarkFourierCoefficient ell‖ ^ 2 *
          (256 * nearGevreyProfileConstant ^ 2 * (P : ℝ) / (A / L)) ≤
        Real.exp L := by
  let C : ℝ := 256 * nearGevreyProfileConstant ^ 2 / A
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hxEventually : ∀ᶠ x : ℝ in atTop,
      C * x ^ 3 ≤ Real.exp x := by
    simpa only [one_mul] using!
      eventually_const_mul_pow_le_exp C 3 1 hC (by norm_num)
  have hrpow : Tendsto (fun L : ℝ ↦ L ^ (1 / 3 : ℝ)) atTop atTop :=
    tendsto_rpow_atTop (by norm_num)
  have hpoly := hrpow.eventually hxEventually
  filter_upwards [hpoly, eventually_ge_atTop (1 : ℝ)] with L hpoly hL
  intro N P ell hN hNL hPN
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL
  let x : ℝ := L ^ (1 / 3 : ℝ)
  have hx0 : 0 ≤ x := by dsimp [x]; positivity
  have hxpow : x ^ 3 = L := by
    dsimp [x]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hLpos.le]
    norm_num [Real.rpow_one]
  have hpolyL : C * L ≤ Real.exp x := by
    rw [← hxpow]
    exact hpoly
  have hNR : 0 < (N : ℝ) := by exact_mod_cast hN
  have hPcut : (P : ℝ) ≤ (N : ℝ) * Real.exp (-x) := by
    change (P : ℝ) / (N : ℝ) ≤ Real.exp (-x) at hPN
    rw [div_le_iff₀ hNR] at hPN
    simpa only [mul_comm] using! hPN
  have hcoeffSq : ‖bernoulliMarkFourierCoefficient ell‖ ^ 2 ≤ 1 := by
    simpa only [one_pow] using! pow_le_pow_left₀
      (norm_nonneg _) (norm_bernoulliMarkFourierCoefficient_le_one ell) 2
  calc
    ‖bernoulliMarkFourierCoefficient ell‖ ^ 2 *
        (256 * nearGevreyProfileConstant ^ 2 * (P : ℝ) / (A / L)) ≤
      1 * (256 * nearGevreyProfileConstant ^ 2 * (P : ℝ) / (A / L)) := by
        gcongr
    _ = C * (P : ℝ) * L := by
      dsimp [C]
      field_simp
    _ ≤ C * ((N : ℝ) * Real.exp (-x)) * L := by
      gcongr
    _ = (N : ℝ) * (C * L * Real.exp (-x)) := by ring
    _ ≤ (N : ℝ) * (Real.exp x * Real.exp (-x)) := by
      gcongr
    _ = (N : ℝ) := by
      rw [← Real.exp_add]
      simp
    _ = Real.exp L := hNL.symm

/-- The same eventual prefactor estimate before multiplying by the carrier
coefficient. -/
theorem eventually_nearLeakage_prefactor_no_coeff_le_exp
    (A : ℝ) (hA : 0 < A) :
    ∀ᶠ L : ℝ in atTop, ∀ (N P : ℕ),
      0 < N →
      Real.exp L = (N : ℝ) →
      (P : ℝ) / (N : ℝ) ≤ Real.exp (-L ^ (1 / 3 : ℝ)) →
      256 * nearGevreyProfileConstant ^ 2 * (P : ℝ) / (A / L) ≤
        Real.exp L := by
  let C : ℝ := 256 * nearGevreyProfileConstant ^ 2 / A
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hxEventually : ∀ᶠ x : ℝ in atTop,
      C * x ^ 3 ≤ Real.exp x := by
    simpa only [one_mul] using!
      eventually_const_mul_pow_le_exp C 3 1 hC (by norm_num)
  have hrpow : Tendsto (fun L : ℝ ↦ L ^ (1 / 3 : ℝ)) atTop atTop :=
    tendsto_rpow_atTop (by norm_num)
  have hpoly := hrpow.eventually hxEventually
  filter_upwards [hpoly, eventually_ge_atTop (1 : ℝ)] with L hpoly hL
  intro N P hN hNL hPN
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL
  let x : ℝ := L ^ (1 / 3 : ℝ)
  have hxpow : x ^ 3 = L := by
    dsimp [x]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hLpos.le]
    norm_num [Real.rpow_one]
  have hpolyL : C * L ≤ Real.exp x := by
    rw [← hxpow]
    exact hpoly
  have hNR : 0 < (N : ℝ) := by exact_mod_cast hN
  have hPcut : (P : ℝ) ≤ (N : ℝ) * Real.exp (-x) := by
    change (P : ℝ) / (N : ℝ) ≤ Real.exp (-x) at hPN
    rw [div_le_iff₀ hNR] at hPN
    simpa only [mul_comm] using! hPN
  calc
    256 * nearGevreyProfileConstant ^ 2 * (P : ℝ) / (A / L) =
        C * (P : ℝ) * L := by
      dsimp [C]
      field_simp
    _ ≤ C * ((N : ℝ) * Real.exp (-x)) * L := by
      gcongr
    _ = (N : ℝ) * (C * L * Real.exp (-x)) := by ring
    _ ≤ (N : ℝ) * (Real.exp x * Real.exp (-x)) := by
      gcongr
    _ = (N : ℝ) := by
      rw [← Real.exp_add]
      simp
    _ = Real.exp L := hNL.symm

/-- Complete eventual one-block leakage estimate with `a=A/L`.  No scalar
Gevrey or prefactor premise remains: uniformly over every admissible block
and every nonzero carrier, the squared leakage is at most
`exp(-(5/2)L)`. -/
theorem eventually_coefficientEnergy_physicalNearCarrierBlock_le_exp
    (A ε : ℝ) (hA : 0 < A) (hε : 0 < ε) (hεhalf : ε < 1 / 2) :
    ∀ᶠ L : ℝ in atTop, ∀ (N P : ℕ) (ell : ℤ),
      0 < N → 4 ≤ P → ell ≠ 0 →
      Real.exp L = (N : ℝ) →
      (P : ℝ) / (N : ℝ) ≤ Real.exp (-L ^ (1 / 3 : ℝ)) →
      coefficientEnergy
          (physicalNearCarrierBlockLeakageCoefficients
            N ell (A / L) ε P) ≤
        ENNReal.ofReal (Real.exp (-(5 / 2 : ℝ) * L)) := by
  have hgevrey := eventually_nearLeakage_selected_gevrey_base A hA
  have hprefactor := eventually_nearLeakage_prefactor_le_exp A hA
  filter_upwards [hgevrey, hprefactor,
      eventually_ge_atTop (max (1 : ℝ) (4 * A / ε))] with
      L hgevreyL hprefactorL hL
  intro N P ell hN hP hell hNL hPN
  have hLone : (1 : ℝ) ≤ L := (le_max_left _ _).trans hL
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hLone
  have ha : 0 < A / L := div_pos hA hLpos
  have hthreshold : 4 * A / ε ≤ L := (le_max_right _ _).trans hL
  have haε : A / L ≤ ε / 4 := by
    rw [div_le_iff₀ hLpos]
    have hfour : 4 * A ≤ ε * L := by
      have := mul_le_mul_of_nonneg_left hthreshold hε.le
      field_simp at this
      nlinarith
    nlinarith
  exact coefficientEnergy_physicalNearCarrierBlock_selected_le_exp
    N P ell (A / L) ε L hN hP hell ha hε haε hεhalf hLpos
      hPN hgevreyL (hprefactorL N P ell hN hNL hPN)

/-- Coefficient-sensitive complete eventual block estimate. -/
theorem eventually_coefficientEnergy_physicalNearCarrierBlock_le_coeff_mul_exp
    (A ε : ℝ) (hA : 0 < A) (hε : 0 < ε) (hεhalf : ε < 1 / 2) :
    ∀ᶠ L : ℝ in atTop, ∀ (N P : ℕ) (ell : ℤ),
      0 < N → 4 ≤ P → ell ≠ 0 →
      Real.exp L = (N : ℝ) →
      (P : ℝ) / (N : ℝ) ≤ Real.exp (-L ^ (1 / 3 : ℝ)) →
      coefficientEnergy
          (physicalNearCarrierBlockLeakageCoefficients
            N ell (A / L) ε P) ≤
        ENNReal.ofReal
          (‖bernoulliMarkFourierCoefficient ell‖ ^ 2 *
            Real.exp (-(5 / 2 : ℝ) * L)) := by
  have hgevrey := eventually_nearLeakage_selected_gevrey_base A hA
  have hprefactor := eventually_nearLeakage_prefactor_no_coeff_le_exp A hA
  filter_upwards [hgevrey, hprefactor,
      eventually_ge_atTop (max (1 : ℝ) (4 * A / ε))] with
      L hgevreyL hprefactorL hL
  intro N P ell hN hP hell hNL hPN
  have hLone : (1 : ℝ) ≤ L := (le_max_left _ _).trans hL
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hLone
  have ha : 0 < A / L := div_pos hA hLpos
  have hthreshold : 4 * A / ε ≤ L := (le_max_right _ _).trans hL
  have haε : A / L ≤ ε / 4 := by
    rw [div_le_iff₀ hLpos]
    have hfour : 4 * A ≤ ε * L := by
      have := mul_le_mul_of_nonneg_left hthreshold hε.le
      field_simp at this
      nlinarith
    nlinarith
  exact coefficientEnergy_physicalNearCarrierBlock_selected_le_coeff_mul_exp
    N P ell (A / L) ε L hN hP hell ha hε haε hεhalf hLpos
      hPN hgevreyL (hprefactorL N P hN hNL hPN)

end

end Erdos1002
