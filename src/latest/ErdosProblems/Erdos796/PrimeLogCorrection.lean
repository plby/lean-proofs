import ErdosProblems.Erdos796.MeisselMertensProof
import Mathlib.NumberTheory.AbelSummation

/- Ported to Lean/Mathlib 4.33.0; imports and tactic elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# The logarithmic correction in the semiprime sum

This file proves that

`sum_{p <= sqrt n} log p / (p * log (n / p))`

tends to `log 2`.  The proof is Abel summation together with the clean
two-sided first-Mertens bounds for `sum (log p) / p`.
-/

namespace Erdos796

open Filter Topology Asymptotics
open Real Finset Interval MeasureTheory
open scoped BigOperators Nat.Prime

/-- The logarithmic correction which occurs after expanding
`log n / log (n / p)`.  The difference-of-logarithms form is convenient for
Abel summation. -/
noncomputable def primeLogCorrection (n : ℕ) : ℝ :=
  ∑ p ∈ Nat.primesLE n.sqrt,
    (Real.log (p : ℝ) / (p : ℝ)) /
      (Real.log (n : ℝ) - Real.log (p : ℝ))

/-- The elementary main term obtained after replacing
`sum_{p <= x} (log p) / p` by `log x`. -/
noncomputable def primeLogCorrectionMain (n : ℕ) : ℝ :=
  let L := Real.log (n : ℝ);
  -1 + L / (L - Real.log 2) +
    Real.log (L - Real.log 2) - Real.log (L / 2)

private noncomputable def primeLogBound : ℝ :=
  Real.log 4 + 6 + Mertens.E₁

private theorem primeLogBound_pos : 0 < primeLogBound := by
  unfold primeLogBound
  have hlog : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hE := Mertens.E₁.nonneg
  linarith

private theorem E₁p_abs_le_primeLogBound {x : ℝ} (hx : 1 ≤ x) :
    |Mertens.E₁p x| ≤ primeLogBound := by
  rw [abs_le']
  constructor
  · have hle := Mertens.E₁p.le hx
    have hE := Mertens.E₁.nonneg
    unfold primeLogBound
    linarith
  · have hge := Mertens.E₁p.ge hx
    have hlog : 0 ≤ Real.log 4 := (Real.log_pos (by norm_num)).le
    unfold primeLogBound
    linarith

private theorem primesLE_eq_filter_Icc (m : ℕ) :
    Nat.primesLE m = (Finset.Icc 0 m).filter Nat.Prime := by
  ext p
  simp only [Nat.mem_primesLE, Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨hpm, hp⟩
    exact ⟨⟨Nat.zero_le p, hpm⟩, hp⟩
  · rintro ⟨⟨_, hpm⟩, hp⟩
    exact ⟨hpm, hp⟩

private theorem logDenom_pos {n : ℕ} (hn : 4 ≤ n)
    {t : ℝ} (ht : t ∈ Set.Icc 2 (Real.sqrt (n : ℝ))) :
    0 < Real.log (n : ℝ) - Real.log t := by
  have hnpos : 0 < (n : ℝ) := by positivity
  have hLpos : 0 < Real.log (n : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  have htpos : 0 < t := by linarith [ht.1]
  have hlogs : Real.log t ≤ Real.log (Real.sqrt (n : ℝ)) :=
    Real.log_le_log htpos ht.2
  rw [Real.log_sqrt hnpos.le] at hlogs
  linarith

private theorem deriv_primeLogWeight {n : ℕ} (hn : 4 ≤ n)
    {t : ℝ} (ht : t ∈ Set.Icc 2 (Real.sqrt (n : ℝ))) :
    deriv (fun y : ℝ =>
      (Real.log (n : ℝ) - Real.log y)⁻¹) t =
      1 / (t * (Real.log (n : ℝ) - Real.log t) ^ 2) := by
  have htne : t ≠ 0 := by linarith [ht.1]
  have hden : Real.log (n : ℝ) - Real.log t ≠ 0 :=
    ne_of_gt (logDenom_pos hn ht)
  have hbase : HasDerivAt
      (fun y : ℝ => Real.log (n : ℝ) - Real.log y)
      (-(1 / t)) t := by
    convert! (hasDerivAt_const t (Real.log (n : ℝ))).sub
      (Real.hasDerivAt_log htne) using 1
    ring
  convert! (hbase.inv hden).deriv using 1
  field_simp

private theorem intervalIntegrable_primeLogWeightDeriv {n : ℕ}
    (hn : 4 ≤ n) :
    IntervalIntegrable
      (deriv (fun y : ℝ =>
        (Real.log (n : ℝ) - Real.log y)⁻¹))
      MeasureTheory.volume 2 (Real.sqrt (n : ℝ)) := by
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le]
  · let d : ℝ → ℝ := fun t =>
      1 / (t * (Real.log (n : ℝ) - Real.log t) ^ 2)
    have hd : IntegrableOn d (Set.Icc 2 (Real.sqrt (n : ℝ))) :=
      ContinuousOn.integrableOn_Icc fun t ht =>
        ContinuousAt.continuousWithinAt (by
          have htne : t ≠ 0 := by linarith [ht.1]
          have hden : Real.log (n : ℝ) - Real.log t ≠ 0 :=
            ne_of_gt (logDenom_pos hn ht)
          dsimp [d]
          exact continuousAt_const.div
            (continuousAt_id.mul
              ((continuousAt_const.sub (Real.continuousAt_log htne)).pow 2))
            (mul_ne_zero htne (pow_ne_zero 2 hden)))
    apply hd.congr
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with t ht
    exact (deriv_primeLogWeight hn ht).symm
  · have : (2 : ℝ) ^ 2 ≤ n := by exact_mod_cast hn
    exact (Real.le_sqrt (by norm_num) (by positivity)).2 (by simpa using! this)

private theorem integral_primeLogWeightDeriv {n : ℕ} (hn : 4 ≤ n) :
    ∫ t in 2..Real.sqrt (n : ℝ),
        1 / (t * (Real.log (n : ℝ) - Real.log t) ^ 2) =
      2 / Real.log (n : ℝ) -
        1 / (Real.log (n : ℝ) - Real.log 2) := by
  let f : ℝ → ℝ := fun t =>
    (Real.log (n : ℝ) - Real.log t)⁻¹
  have hsqrt : 2 ≤ Real.sqrt (n : ℝ) := by
    rw [Real.le_sqrt (by norm_num) (by positivity)]
    exact_mod_cast hn
  have hdiff : ∀ t ∈ Set.Icc (2 : ℝ) (Real.sqrt (n : ℝ)),
      DifferentiableAt ℝ f t := by
    intro t ht
    have htne : t ≠ 0 := by linarith [ht.1]
    have hden : Real.log (n : ℝ) - Real.log t ≠ 0 :=
      ne_of_gt (logDenom_pos hn ht)
    dsimp [f]
    fun_prop
  have hdiff' : ∀ t ∈ [[(2 : ℝ), Real.sqrt (n : ℝ)]],
      DifferentiableAt ℝ f t := by
    intro t ht
    rw [Set.uIcc_of_le hsqrt] at ht
    exact hdiff t ht
  have hint := intervalIntegral.integral_deriv_eq_sub hdiff'
    (intervalIntegrable_primeLogWeightDeriv hn)
  have heq :
      (∫ t in 2..Real.sqrt (n : ℝ),
        1 / (t * (Real.log (n : ℝ) - Real.log t) ^ 2)) =
        f (Real.sqrt (n : ℝ)) - f 2 := by
    rw [← hint]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le hsqrt, Set.mem_Icc] at ht
    exact deriv_primeLogWeight hn ht |>.symm
  rw [heq]
  have hnpos : 0 < (n : ℝ) := by positivity
  have hL : Real.log (n : ℝ) ≠ 0 := by
    exact ne_of_gt (Real.log_pos (by exact_mod_cast (show 1 < n by omega)))
  dsimp [f]
  rw [Real.log_sqrt hnpos.le]
  field_simp
  ring_nf

private theorem deriv_primeLogMainAntideriv {n : ℕ} (hn : 4 ≤ n)
    {t : ℝ} (ht : t ∈ Set.Icc 2 (Real.sqrt (n : ℝ))) :
    deriv (fun y : ℝ =>
      Real.log (n : ℝ) /
          (Real.log (n : ℝ) - Real.log y) +
        Real.log (Real.log (n : ℝ) - Real.log y)) t =
      Real.log t /
        (t * (Real.log (n : ℝ) - Real.log t) ^ 2) := by
  have htne : t ≠ 0 := by linarith [ht.1]
  have hden : Real.log (n : ℝ) - Real.log t ≠ 0 :=
    ne_of_gt (logDenom_pos hn ht)
  have hbase : HasDerivAt
      (fun y : ℝ => Real.log (n : ℝ) - Real.log y)
      (-(1 / t)) t := by
    convert! (hasDerivAt_const t (Real.log (n : ℝ))).sub
      (Real.hasDerivAt_log htne) using 1
    ring
  have hquot := (hasDerivAt_const t (Real.log (n : ℝ))).div hbase hden
  have hlog := hbase.log hden
  convert! (hquot.add hlog).deriv using 1
  field_simp
  ring

private theorem integral_primeLogMain {n : ℕ} (hn : 4 ≤ n) :
    ∫ t in 2..Real.sqrt (n : ℝ),
        Real.log t /
          (t * (Real.log (n : ℝ) - Real.log t) ^ 2) =
      (Real.log (n : ℝ) /
          (Real.log (n : ℝ) -
            Real.log (Real.sqrt (n : ℝ))) +
        Real.log (Real.log (n : ℝ) -
          Real.log (Real.sqrt (n : ℝ)))) -
      (Real.log (n : ℝ) /
          (Real.log (n : ℝ) - Real.log 2) +
        Real.log (Real.log (n : ℝ) - Real.log 2)) := by
  let F : ℝ → ℝ := fun t =>
    Real.log (n : ℝ) /
        (Real.log (n : ℝ) - Real.log t) +
      Real.log (Real.log (n : ℝ) - Real.log t)
  have hsqrt : 2 ≤ Real.sqrt (n : ℝ) := by
    rw [Real.le_sqrt (by norm_num) (by positivity)]
    exact_mod_cast hn
  have hdiff : ∀ t ∈ [[(2 : ℝ), Real.sqrt (n : ℝ)]],
      DifferentiableAt ℝ F t := by
    intro t ht
    rw [Set.uIcc_of_le hsqrt] at ht
    have htne : t ≠ 0 := by linarith [ht.1]
    have hden : Real.log (n : ℝ) - Real.log t ≠ 0 :=
      ne_of_gt (logDenom_pos hn ht)
    dsimp [F]
    fun_prop
  have hdcont : ContinuousOn
      (fun t : ℝ => Real.log t /
        (t * (Real.log (n : ℝ) - Real.log t) ^ 2))
      (Set.Icc 2 (Real.sqrt (n : ℝ))) := by
    intro t ht
    have htne : t ≠ 0 := by linarith [ht.1]
    have hden : Real.log (n : ℝ) - Real.log t ≠ 0 :=
      ne_of_gt (logDenom_pos hn ht)
    exact ContinuousAt.continuousWithinAt
      ((Real.continuousAt_log htne).div
        (continuousAt_id.mul
          ((continuousAt_const.sub (Real.continuousAt_log htne)).pow 2))
        (mul_ne_zero htne (pow_ne_zero 2 hden)))
  have hdint : IntervalIntegrable (deriv F) MeasureTheory.volume
      2 (Real.sqrt (n : ℝ)) := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hsqrt]
    apply (hdcont.integrableOn_Icc).congr
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with t ht
    exact (deriv_primeLogMainAntideriv hn ht).symm
  have hint := intervalIntegral.integral_deriv_eq_sub hdiff hdint
  change _ = F (Real.sqrt (n : ℝ)) - F 2
  rw [← hint]
  apply intervalIntegral.integral_congr
  intro t ht
  rw [Set.uIcc_of_le hsqrt, Set.mem_Icc] at ht
  exact (deriv_primeLogMainAntideriv hn ht).symm

private theorem primeLogCorrectionMain_eq_integral {n : ℕ} (hn : 4 ≤ n) :
    primeLogCorrectionMain n =
      Real.log (Real.sqrt (n : ℝ)) /
          (Real.log (n : ℝ) - Real.log (Real.sqrt (n : ℝ))) -
        ∫ t in 2..Real.sqrt (n : ℝ),
          Real.log t /
            (t * (Real.log (n : ℝ) - Real.log t) ^ 2) := by
  rw [integral_primeLogMain hn]
  unfold primeLogCorrectionMain
  have hnpos : 0 < (n : ℝ) := by positivity
  have hL : Real.log (n : ℝ) ≠ 0 :=
    ne_of_gt (Real.log_pos (by exact_mod_cast (show 1 < n by omega)))
  rw [Real.log_sqrt hnpos.le]
  field_simp
  ring_nf

private noncomputable def logPrimeCoeff (k : ℕ) : ℝ :=
  if k.Prime then Real.log (k : ℝ) / (k : ℝ) else 0

@[simp] private theorem logPrimeCoeff_zero : logPrimeCoeff 0 = 0 := by
  simp [logPrimeCoeff, Nat.not_prime_zero]

@[simp] private theorem logPrimeCoeff_one : logPrimeCoeff 1 = 0 := by
  simp [logPrimeCoeff, Nat.not_prime_one]

private theorem sum_logPrimeCoeff (x : ℝ) :
    ∑ k ∈ Finset.Icc 0 ⌊x⌋₊, logPrimeCoeff k =
      Real.log x + Mertens.E₁p x := by
  have hsets :
      (Finset.Icc 0 ⌊x⌋₊).filter Nat.Prime =
        (Finset.Ioc 0 ⌊x⌋₊).filter Nat.Prime := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc]
    constructor
    · rintro ⟨⟨_, hkx⟩, hk⟩
      exact ⟨⟨hk.pos, hkx⟩, hk⟩
    · rintro ⟨⟨_, hkx⟩, hk⟩
      exact ⟨⟨Nat.zero_le k, hkx⟩, hk⟩
  unfold logPrimeCoeff
  rw [← Finset.sum_filter, hsets]
  exact Mertens.sum_log_prime_div_eq x

private theorem primeLogCorrection_abel {n : ℕ} (hn : 4 ≤ n) :
    primeLogCorrection n =
      (Real.log (n : ℝ) -
          Real.log (Real.sqrt (n : ℝ)))⁻¹ *
        (Real.log (Real.sqrt (n : ℝ)) +
          Mertens.E₁p (Real.sqrt (n : ℝ))) -
      ∫ t in 2..Real.sqrt (n : ℝ),
        (1 / (t * (Real.log (n : ℝ) - Real.log t) ^ 2)) *
          (Real.log t + Mertens.E₁p t) := by
  let f : ℝ → ℝ := fun t =>
    (Real.log (n : ℝ) - Real.log t)⁻¹
  let s : ℝ := Real.sqrt (n : ℝ)
  have hsqrt : 2 ≤ s := by
    dsimp [s]
    rw [Real.le_sqrt (by norm_num) (by positivity)]
    exact_mod_cast hn
  have hdiff : ∀ t ∈ Set.Icc (2 : ℝ) s,
      DifferentiableAt ℝ f t := by
    intro t ht
    have htne : t ≠ 0 := by linarith [ht.1]
    have hden : Real.log (n : ℝ) - Real.log t ≠ 0 := by
      apply ne_of_gt
      apply logDenom_pos hn
      simpa [s] using! ht
    dsimp [f]
    fun_prop
  have hfint : IntegrableOn (deriv f) (Set.Icc (2 : ℝ) s) := by
    have hi := intervalIntegrable_primeLogWeightDeriv hn
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hsqrt] at hi
    simpa [f, s] using! hi
  have hab := sum_mul_eq_sub_integral_mul₁ logPrimeCoeff
    (f := f) logPrimeCoeff_zero logPrimeCoeff_one s hdiff hfint
  rw [← intervalIntegral.integral_of_le hsqrt] at hab
  have hab' :
      ∑ k ∈ Finset.Icc 0 ⌊s⌋₊, f k * logPrimeCoeff k =
        f s * (Real.log s + Mertens.E₁p s) -
          ∫ t in 2..s,
            (1 / (t * (Real.log (n : ℝ) - Real.log t) ^ 2)) *
              (Real.log t + Mertens.E₁p t) := by
    rw [hab, sum_logPrimeCoeff]
    apply congrArg (fun z : ℝ =>
      f s * (Real.log s + Mertens.E₁p s) - z)
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le hsqrt, Set.mem_Icc] at ht
    dsimp [f]
    rw [deriv_primeLogWeight hn (by simpa [s] using! ht),
      sum_logPrimeCoeff]
  rw [← hab']
  dsimp [s, f]
  unfold primeLogCorrection
  rw [Real.nat_floor_real_sqrt_eq_nat_sqrt, primesLE_eq_filter_Icc]
  simp only [Finset.sum_filter, logPrimeCoeff]
  apply Finset.sum_congr rfl
  intro p hp
  simp only [Finset.mem_Icc] at hp
  by_cases hprime : p.Prime
  · simp only [hprime, if_true]
    simp [div_eq_mul_inv, mul_comm, mul_assoc]
  · simp only [hprime, if_false]
    simp

private theorem primeLogError_intervalIntegrable {n : ℕ} (hn : 4 ≤ n) :
    IntervalIntegrable
      (fun t : ℝ =>
        (1 / (t * (Real.log (n : ℝ) - Real.log t) ^ 2)) *
          Mertens.E₁p t)
      MeasureTheory.volume 2 (Real.sqrt (n : ℝ)) := by
  have hsqrt : 2 ≤ Real.sqrt (n : ℝ) := by
    rw [Real.le_sqrt (by norm_num) (by positivity)]
    exact_mod_cast hn
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hsqrt]
  let d : ℝ → ℝ := fun t =>
    1 / (t * (Real.log (n : ℝ) - Real.log t) ^ 2)
  have hdcont : ContinuousOn d
      (Set.Icc 2 (Real.sqrt (n : ℝ))) := by
    intro t ht
    have htne : t ≠ 0 := by linarith [ht.1]
    have hden : Real.log (n : ℝ) - Real.log t ≠ 0 :=
      ne_of_gt (logDenom_pos hn ht)
    exact ContinuousAt.continuousWithinAt (by
      dsimp [d]
      exact continuousAt_const.div
        (continuousAt_id.mul
          ((continuousAt_const.sub (Real.continuousAt_log htne)).pow 2))
        (mul_ne_zero htne (pow_ne_zero 2 hden)))
  have hmajor : IntegrableOn (fun t => primeLogBound * d t)
      (Set.Icc 2 (Real.sqrt (n : ℝ))) :=
    (continuousOn_const.mul hdcont).integrableOn_Icc
  refine MeasureTheory.Integrable.mono hmajor ?_ ?_
  · exact Measurable.aestronglyMeasurable (by
      fun_prop)
  · filter_upwards
      [MeasureTheory.ae_restrict_mem measurableSet_Icc] with t ht
    have hdnonneg : 0 ≤ d t := by
      dsimp [d]
      exact one_div_nonneg.mpr
        (mul_nonneg (by linarith [ht.1]) (sq_nonneg _))
    have hE := E₁p_abs_le_primeLogBound (show 1 ≤ t by linarith [ht.1])
    simp only [norm_mul, norm_eq_abs]
    rw [abs_of_nonneg hdnonneg, abs_of_pos primeLogBound_pos]
    simpa [mul_comm] using! mul_le_mul_of_nonneg_left hE hdnonneg

private theorem primeLogCorrection_sub_main {n : ℕ} (hn : 4 ≤ n) :
    primeLogCorrection n - primeLogCorrectionMain n =
      (2 / Real.log (n : ℝ)) *
          Mertens.E₁p (Real.sqrt (n : ℝ)) -
        ∫ t in 2..Real.sqrt (n : ℝ),
          (1 / (t * (Real.log (n : ℝ) - Real.log t) ^ 2)) *
            Mertens.E₁p t := by
  have hsqrt : 2 ≤ Real.sqrt (n : ℝ) := by
    rw [Real.le_sqrt (by norm_num) (by positivity)]
    exact_mod_cast hn
  have hmainInt : IntervalIntegrable
      (fun t : ℝ =>
        (1 / (t * (Real.log (n : ℝ) - Real.log t) ^ 2)) *
          Real.log t)
      MeasureTheory.volume 2 (Real.sqrt (n : ℝ)) := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hsqrt]
    apply ContinuousOn.integrableOn_Icc
    intro t ht
    have htne : t ≠ 0 := by linarith [ht.1]
    have hden : Real.log (n : ℝ) - Real.log t ≠ 0 :=
      ne_of_gt (logDenom_pos hn ht)
    exact ContinuousAt.continuousWithinAt (by
      exact (continuousAt_const.div
        (continuousAt_id.mul
          ((continuousAt_const.sub (Real.continuousAt_log htne)).pow 2))
        (mul_ne_zero htne (pow_ne_zero 2 hden))).mul
          (Real.continuousAt_log htne))
  have herrorInt := primeLogError_intervalIntegrable hn
  have hsplit :
      (∫ t in 2..Real.sqrt (n : ℝ),
        (1 / (t * (Real.log (n : ℝ) - Real.log t) ^ 2)) *
          (Real.log t + Mertens.E₁p t)) =
      (∫ t in 2..Real.sqrt (n : ℝ),
        (1 / (t * (Real.log (n : ℝ) - Real.log t) ^ 2)) *
          Real.log t) +
      ∫ t in 2..Real.sqrt (n : ℝ),
        (1 / (t * (Real.log (n : ℝ) - Real.log t) ^ 2)) *
          Mertens.E₁p t := by
    rw [← intervalIntegral.integral_add hmainInt herrorInt]
    apply intervalIntegral.integral_congr
    intro t _
    ring
  rw [primeLogCorrection_abel hn, primeLogCorrectionMain_eq_integral hn,
    hsplit]
  have hnpos : 0 < (n : ℝ) := by positivity
  have hL : Real.log (n : ℝ) ≠ 0 :=
    ne_of_gt (Real.log_pos (by exact_mod_cast (show 1 < n by omega)))
  rw [Real.log_sqrt hnpos.le]
  field_simp
  ring

private theorem primeLogCorrection_error_bound {n : ℕ} (hn : 4 ≤ n) :
    |primeLogCorrection n - primeLogCorrectionMain n| ≤
      4 * primeLogBound / Real.log (n : ℝ) := by
  have hsqrt : 2 ≤ Real.sqrt (n : ℝ) := by
    rw [Real.le_sqrt (by norm_num) (by positivity)]
    exact_mod_cast hn
  have hLpos : 0 < Real.log (n : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  have hden2 : 0 < Real.log (n : ℝ) - Real.log 2 := by
    exact sub_pos.mpr (Real.strictMonoOn_log (by norm_num)
      (show (n : ℝ) ∈ Set.Ioi 0 by
        simp only [Set.mem_Ioi]
        exact_mod_cast (show 0 < n by omega))
      (by exact_mod_cast (show 2 < n by omega)))
  let d : ℝ → ℝ := fun t =>
    1 / (t * (Real.log (n : ℝ) - Real.log t) ^ 2)
  have hdcont : ContinuousOn d
      (Set.Icc 2 (Real.sqrt (n : ℝ))) := by
    intro t ht
    have htne : t ≠ 0 := by linarith [ht.1]
    have hden : Real.log (n : ℝ) - Real.log t ≠ 0 :=
      ne_of_gt (logDenom_pos hn ht)
    exact ContinuousAt.continuousWithinAt (by
      dsimp [d]
      exact continuousAt_const.div
        (continuousAt_id.mul
          ((continuousAt_const.sub (Real.continuousAt_log htne)).pow 2))
        (mul_ne_zero htne (pow_ne_zero 2 hden)))
  have hmajorInt : IntervalIntegrable (fun t => primeLogBound * d t)
      MeasureTheory.volume 2 (Real.sqrt (n : ℝ)) := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hsqrt]
    exact (continuousOn_const.mul hdcont).integrableOn_Icc
  have hintegral :
      ‖∫ t in 2..Real.sqrt (n : ℝ), d t * Mertens.E₁p t‖ ≤
        primeLogBound *
          (2 / Real.log (n : ℝ) -
            1 / (Real.log (n : ℝ) - Real.log 2)) := by
    calc
      _ ≤ ∫ t in 2..Real.sqrt (n : ℝ), primeLogBound * d t := by
        apply intervalIntegral.norm_integral_le_of_norm_le hsqrt
        · filter_upwards with t ht
          have ht' : t ∈ Set.Icc 2 (Real.sqrt (n : ℝ)) :=
            ⟨ht.1.le, ht.2⟩
          have hdnonneg : 0 ≤ d t := by
            dsimp [d]
            exact one_div_nonneg.mpr
              (mul_nonneg (by linarith [ht.1]) (sq_nonneg _))
          have hE := E₁p_abs_le_primeLogBound
            (show 1 ≤ t by linarith [ht.1])
          simp only [norm_mul, norm_eq_abs]
          rw [abs_of_nonneg hdnonneg]
          simpa [mul_comm] using! mul_le_mul_of_nonneg_left hE hdnonneg
        · exact hmajorInt
      _ = primeLogBound *
          (2 / Real.log (n : ℝ) -
            1 / (Real.log (n : ℝ) - Real.log 2)) := by
        rw [intervalIntegral.integral_const_mul]
        congr 1
        simpa [d] using! integral_primeLogWeightDeriv hn
  have hintegral' :
      ‖∫ t in 2..Real.sqrt (n : ℝ), d t * Mertens.E₁p t‖ ≤
        2 * primeLogBound / Real.log (n : ℝ) := by
    calc
      _ ≤ primeLogBound *
          (2 / Real.log (n : ℝ) -
            1 / (Real.log (n : ℝ) - Real.log 2)) := hintegral
      _ ≤ 2 * primeLogBound / Real.log (n : ℝ) := by
        have hK := primeLogBound_pos.le
        have hrecip : 0 ≤
            1 / (Real.log (n : ℝ) - Real.log 2) := by positivity
        calc
          _ ≤ primeLogBound * (2 / Real.log (n : ℝ)) := by
            gcongr
            linarith
          _ = _ := by ring
  rw [primeLogCorrection_sub_main hn]
  calc
    |(2 / Real.log (n : ℝ)) *
          Mertens.E₁p (Real.sqrt (n : ℝ)) -
        ∫ t in 2..Real.sqrt (n : ℝ), d t * Mertens.E₁p t| ≤
        |(2 / Real.log (n : ℝ)) *
          Mertens.E₁p (Real.sqrt (n : ℝ))| +
        ‖∫ t in 2..Real.sqrt (n : ℝ), d t * Mertens.E₁p t‖ := by
      exact abs_sub _ _
    _ ≤ 2 * primeLogBound / Real.log (n : ℝ) +
        2 * primeLogBound / Real.log (n : ℝ) := by
      gcongr
      rw [abs_mul, abs_of_pos (show 0 < 2 / Real.log (n : ℝ) by positivity)]
      have hE := E₁p_abs_le_primeLogBound
        (show 1 ≤ Real.sqrt (n : ℝ) by linarith)
      calc
        (2 / Real.log (n : ℝ)) *
            |Mertens.E₁p (Real.sqrt (n : ℝ))| ≤
            (2 / Real.log (n : ℝ)) * primeLogBound := by gcongr
        _ = _ := by ring
    _ = 4 * primeLogBound / Real.log (n : ℝ) := by ring

/-- The elementary main term tends to `log 2`. -/
theorem primeLogCorrectionMain_tendsto_log_two :
    Tendsto primeLogCorrectionMain atTop (nhds (Real.log 2)) := by
  have hLtop : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hinvL : Tendsto
      (fun n : ℕ => (Real.log (n : ℝ))⁻¹) atTop (nhds 0) :=
    hLtop.inv_tendsto_atTop
  have hu : Tendsto
      (fun n : ℕ => 1 - Real.log 2 * (Real.log (n : ℝ))⁻¹)
      atTop (nhds 1) := by
    have hone : Tendsto (fun _n : ℕ => (1 : ℝ)) atTop (nhds 1) :=
      tendsto_const_nhds
    have hlogtwo : Tendsto (fun _n : ℕ => Real.log 2)
        atTop (nhds (Real.log 2)) := tendsto_const_nhds
    have := hone.sub (hlogtwo.mul hinvL)
    simpa using! this
  have huinv : Tendsto
      (fun n : ℕ =>
        (1 - Real.log 2 * (Real.log (n : ℝ))⁻¹)⁻¹)
      atTop (nhds 1) := by
    simpa using! hu.inv₀ one_ne_zero
  have htwou : Tendsto
      (fun n : ℕ =>
        2 * (1 - Real.log 2 * (Real.log (n : ℝ))⁻¹))
      atTop (nhds 2) := by
    simpa using! tendsto_const_nhds.mul hu
  have hlog : Tendsto
      (fun n : ℕ => Real.log
        (2 * (1 - Real.log 2 * (Real.log (n : ℝ))⁻¹)))
      atTop (nhds (Real.log 2)) :=
    (Real.continuousAt_log (by norm_num)).tendsto.comp htwou
  have hsimple : Tendsto
      (fun n : ℕ =>
        -1 +
          (1 - Real.log 2 * (Real.log (n : ℝ))⁻¹)⁻¹ +
          Real.log
            (2 * (1 - Real.log 2 * (Real.log (n : ℝ))⁻¹)))
      atTop (nhds (Real.log 2)) := by
    have hminus : Tendsto (fun _n : ℕ => (-1 : ℝ))
        atTop (nhds (-1)) := tendsto_const_nhds
    have := (hminus.add huinv).add hlog
    simpa using! this
  have heq : ∀ᶠ n : ℕ in atTop,
      primeLogCorrectionMain n =
        -1 +
          (1 - Real.log 2 * (Real.log (n : ℝ))⁻¹)⁻¹ +
          Real.log
            (2 * (1 - Real.log 2 * (Real.log (n : ℝ))⁻¹)) := by
    filter_upwards [eventually_ge_atTop 4] with n hn
    have hLpos : 0 < Real.log (n : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < n by omega))
    have hden : 0 < Real.log (n : ℝ) - Real.log 2 := by
      exact sub_pos.mpr (Real.strictMonoOn_log (by norm_num)
        (show (n : ℝ) ∈ Set.Ioi 0 by
          simp only [Set.mem_Ioi]
          exact_mod_cast (show 0 < n by omega))
        (by exact_mod_cast (show 2 < n by omega)))
    have hfrac :
        Real.log (n : ℝ) /
            (Real.log (n : ℝ) - Real.log 2) =
          (1 - Real.log 2 * (Real.log (n : ℝ))⁻¹)⁻¹ := by
      field_simp
    have hratio :
        (Real.log (n : ℝ) - Real.log 2) /
            (Real.log (n : ℝ) / 2) =
          2 * (1 - Real.log 2 * (Real.log (n : ℝ))⁻¹) := by
      field_simp
    have hhalf : Real.log (n : ℝ) / 2 ≠ 0 := by positivity
    have hlogeq :
        Real.log (Real.log (n : ℝ) - Real.log 2) -
            Real.log (Real.log (n : ℝ) / 2) =
          Real.log
            (2 * (1 - Real.log 2 * (Real.log (n : ℝ))⁻¹)) := by
      rw [← Real.log_div (ne_of_gt hden) hhalf, hratio]
    dsimp [primeLogCorrectionMain]
    rw [hfrac, ← hlogeq]
    ring
  exact hsimple.congr' (heq.mono fun _ h => h.symm)

private theorem primeLogCorrection_sub_main_tendsto_zero :
    Tendsto
      (fun n : ℕ => primeLogCorrection n - primeLogCorrectionMain n)
      atTop (nhds 0) := by
  have hLtop : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hupper : Tendsto
      (fun n : ℕ => 4 * primeLogBound / Real.log (n : ℝ))
      atTop (nhds 0) := tendsto_const_nhds.div_atTop hLtop
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero'
  · exact Eventually.of_forall fun _ => norm_nonneg _
  · filter_upwards [eventually_ge_atTop 4] with n hn
    simpa [Real.norm_eq_abs] using! primeLogCorrection_error_bound hn
  · exact hupper

/-- The logarithmic prime correction has the limiting mass `log 2`. -/
theorem primeLogCorrection_tendsto_log_two :
    Tendsto primeLogCorrection atTop (nhds (Real.log 2)) := by
  have hsum := primeLogCorrectionMain_tendsto_log_two.add
    primeLogCorrection_sub_main_tendsto_zero
  simpa only [add_zero] using! hsum.congr'
    (Eventually.of_forall fun n => by ring)

/-- The logarithm of the natural square root has asymptotic ratio `1/2`
with the logarithm of its argument. -/
theorem log_natSqrt_div_log_tendsto_half :
    Tendsto
      (fun n : ℕ =>
        Real.log (n.sqrt : ℝ) / Real.log (n : ℝ))
      atTop (nhds (1 / 2 : ℝ)) := by
  have hLtop : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hsmall : Tendsto
      (fun n : ℕ => Real.log 2 / Real.log (n : ℝ))
      atTop (nhds 0) := tendsto_const_nhds.div_atTop hLtop
  have hlower : Tendsto
      (fun n : ℕ => (1 / 2 : ℝ) -
        Real.log 2 / Real.log (n : ℝ))
      atTop (nhds (1 / 2 : ℝ)) := by
    have hhalf : Tendsto (fun _n : ℕ => (1 / 2 : ℝ))
        atTop (nhds (1 / 2 : ℝ)) := tendsto_const_nhds
    simpa using! hhalf.sub hsmall
  have hupper : Tendsto (fun _n : ℕ => (1 / 2 : ℝ))
      atTop (nhds (1 / 2 : ℝ)) := tendsto_const_nhds
  apply hlower.squeeze' hupper
  · filter_upwards [eventually_ge_atTop 4] with n hn
    have hs : 2 ≤ n.sqrt := by
      rw [Nat.le_sqrt]
      omega
    have hspos : 0 < (n.sqrt : ℝ) := by positivity
    have hnpos : 0 < (n : ℝ) := by positivity
    have hLpos : 0 < Real.log (n : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < n by omega))
    have hsqrtlt : Real.sqrt (n : ℝ) < 2 * (n.sqrt : ℝ) := by
      calc
        Real.sqrt (n : ℝ) < (n.sqrt : ℝ) + 1 :=
          Real.real_sqrt_lt_nat_sqrt_succ
        _ ≤ 2 * (n.sqrt : ℝ) := by
          exact_mod_cast (show n.sqrt + 1 ≤ 2 * n.sqrt by omega)
    have hlogsLower :
        Real.log (n : ℝ) / 2 - Real.log 2 ≤
          Real.log (n.sqrt : ℝ) := by
      have hstrict := Real.strictMonoOn_log
        (show Real.sqrt (n : ℝ) ∈ Set.Ioi 0 by
          simp only [Set.mem_Ioi]
          positivity)
        (show 2 * (n.sqrt : ℝ) ∈ Set.Ioi 0 by
          simp only [Set.mem_Ioi]
          positivity)
        hsqrtlt
      rw [Real.log_sqrt hnpos.le,
        Real.log_mul (by norm_num : (2 : ℝ) ≠ 0)
          (ne_of_gt hspos)] at hstrict
      linarith
    rw [le_div_iff₀ hLpos]
    calc
      ((1 / 2 : ℝ) - Real.log 2 / Real.log (n : ℝ)) *
          Real.log (n : ℝ) =
          Real.log (n : ℝ) / 2 - Real.log 2 := by field_simp
      _ ≤ Real.log (n.sqrt : ℝ) := hlogsLower
  · filter_upwards [eventually_ge_atTop 4] with n hn
    have hs : 2 ≤ n.sqrt := by
      rw [Nat.le_sqrt]
      omega
    have hspos : 0 < (n.sqrt : ℝ) := by positivity
    have hnpos : 0 < (n : ℝ) := by positivity
    have hLpos : 0 < Real.log (n : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < n by omega))
    have hlogle :
        Real.log (n.sqrt : ℝ) ≤ Real.log (n : ℝ) / 2 := by
      have h := Real.log_le_log hspos
        (Real.nat_sqrt_le_real_sqrt (a := n))
      simpa [Real.log_sqrt hnpos.le] using! h
    rw [div_le_iff₀ hLpos]
    calc
      Real.log (n.sqrt : ℝ) ≤ Real.log (n : ℝ) / 2 := hlogle
      _ = (1 / 2 : ℝ) * Real.log (n : ℝ) := by ring

/-- The change from `log log (sqrt n)` to `log log n` contributes
`-log 2`. -/
theorem loglog_natSqrt_sub_loglog_tendsto_neg_log_two :
    Tendsto
      (fun n : ℕ =>
        Real.log (Real.log (n.sqrt : ℝ)) -
          Real.log (Real.log (n : ℝ)))
      atTop (nhds (-Real.log 2)) := by
  have hratio := log_natSqrt_div_log_tendsto_half
  have hlogratio : Tendsto
      (fun n : ℕ => Real.log
        (Real.log (n.sqrt : ℝ) / Real.log (n : ℝ)))
      atTop (nhds (Real.log (1 / 2 : ℝ))) :=
    (Real.continuousAt_log (by norm_num)).tendsto.comp hratio
  have heq : ∀ᶠ n : ℕ in atTop,
      Real.log (Real.log (n.sqrt : ℝ)) -
          Real.log (Real.log (n : ℝ)) =
        Real.log
          (Real.log (n.sqrt : ℝ) / Real.log (n : ℝ)) := by
    filter_upwards [eventually_ge_atTop 4] with n hn
    have hs : 2 ≤ n.sqrt := by
      rw [Nat.le_sqrt]
      omega
    have hlogs : Real.log (n.sqrt : ℝ) ≠ 0 :=
      ne_of_gt (Real.log_pos (by exact_mod_cast (show 1 < n.sqrt by omega)))
    have hlogn : Real.log (n : ℝ) ≠ 0 :=
      ne_of_gt (Real.log_pos (by exact_mod_cast (show 1 < n by omega)))
    exact (Real.log_div hlogs hlogn).symm
  have hvalue : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
    rw [Real.log_div (by norm_num : (1 : ℝ) ≠ 0)
      (by norm_num : (2 : ℝ) ≠ 0)]
    simp
  rw [← hvalue]
  exact hlogratio.congr' (heq.mono fun _ h => h.symm)

/-- The prime harmonic sum below the square-root cutoff, normalized by
`log log n`, has constant term `M - log 2`. -/
theorem primeHarmonic_sqrt_sub_loglog_n_tendsto :
    Tendsto
      (fun n : ℕ =>
        primeHarmonic n.sqrt - Real.log (Real.log (n : ℝ)))
      atTop (nhds (Mertens.M - Real.log 2)) := by
  have hM : Tendsto
      (fun n : ℕ =>
        primeHarmonic n.sqrt -
          Real.log (Real.log (n.sqrt : ℝ)))
      atTop (nhds Mertens.M) :=
    meisselMertensConstant.comp tendsto_natSqrt_atTop
  have hsum := hM.add loglog_natSqrt_sub_loglog_tendsto_neg_log_two
  simpa only [sub_eq_add_neg] using! hsum.congr'
    (Eventually.of_forall fun n => by ring)

/-- The prime sum which results from replacing each `pi(n / p)` by
`(n / p) / log (n / p)` and normalizing by `n / log n`. -/
noncomputable def primeQuotientMainSum (n : ℕ) : ℝ :=
  ∑ p ∈ Nat.primesLE n.sqrt,
    Real.log (n : ℝ) /
      ((p : ℝ) * Real.log ((n : ℝ) / (p : ℝ)))

/-- Exact decomposition of the normalized PNT main sum into the prime
harmonic sum and the logarithmic correction. -/
theorem primeQuotientMainSum_eq_harmonic_add_correction
    {n : ℕ} (hn : 4 ≤ n) :
    primeQuotientMainSum n =
      primeHarmonic n.sqrt + primeLogCorrection n := by
  unfold primeQuotientMainSum primeHarmonic primeLogCorrection
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  have hp' := Nat.mem_primesLE.mp hp
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp'.2.ne_zero
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have htp : (p : ℝ) ∈ Set.Icc 2 (Real.sqrt (n : ℝ)) := by
    constructor
    · exact_mod_cast hp'.2.two_le
    · exact (show (p : ℝ) ≤ (n.sqrt : ℝ) by exact_mod_cast hp'.1) |>.trans
        Real.nat_sqrt_le_real_sqrt
  have hden : Real.log (n : ℝ) - Real.log (p : ℝ) ≠ 0 :=
    ne_of_gt (logDenom_pos hn htp)
  rw [Real.log_div hn0 hp0]
  field_simp
  ring

/-- The complete normalized prime main sum has constant term `M`: the
`-log 2` from the square-root harmonic cutoff is exactly cancelled by the
logarithmic correction. -/
theorem primeQuotientMainSum_sub_loglog_tendsto :
    Tendsto
      (fun n : ℕ =>
        primeQuotientMainSum n - Real.log (Real.log (n : ℝ)))
      atTop (nhds Mertens.M) := by
  have hsum := primeHarmonic_sqrt_sub_loglog_n_tendsto.add
    primeLogCorrection_tendsto_log_two
  have heq : ∀ᶠ n : ℕ in atTop,
      (primeHarmonic n.sqrt - Real.log (Real.log (n : ℝ))) +
          primeLogCorrection n =
        primeQuotientMainSum n - Real.log (Real.log (n : ℝ)) := by
    filter_upwards [eventually_ge_atTop 4] with n hn
    rw [primeQuotientMainSum_eq_harmonic_add_correction hn]
    ring
  have ht := hsum.congr' heq
  convert! ht using 1
  ring_nf

/-- For positive `n`, the difference-of-logarithms definition agrees with
the conventional `log (n / p)` denominator. -/
theorem primeLogCorrection_eq_sum_log_div {n : ℕ} (hn : 0 < n) :
    primeLogCorrection n =
      ∑ p ∈ Nat.primesLE n.sqrt,
        Real.log (p : ℝ) /
          ((p : ℝ) * Real.log ((n : ℝ) / (p : ℝ))) := by
  unfold primeLogCorrection
  apply Finset.sum_congr rfl
  intro p hp
  have hpprime := (Nat.mem_primesLE.mp hp).2
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hpprime.ne_zero
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  rw [Real.log_div hn0 hp0]
  simp [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]

end Erdos796
