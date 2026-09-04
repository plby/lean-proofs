import ErdosProblems.Erdos520.HarperPrimeBlockWindow
import Mathlib.Analysis.Complex.ExponentialBounds

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open Set Function Filter Finset MeasureTheory Topology
open scoped BigOperators Interval

noncomputable section

namespace Erdos
namespace Problem520

/-!
# Asymptotic variance of scheduled Harper blocks

This file sharpens the constant prime-block bounds to their limiting value.
The reciprocal-prime mass of `(A,A²]` tends to `log 2`; oscillatory mass and
the variance lost to the tilted bias both vanish.  Consequently the diagonal
block variance tends uniformly to `(log 2) / 2` on each fixed noncentral
frequency window.
-/

/-- The Abel kernel which converts Chebyshev theta into reciprocal-prime
mass. -/
noncomputable def reciprocalPrimeKernel (x : ℝ) : ℝ :=
  (x * Real.log x)⁻¹

noncomputable def reciprocalPrimeKernelDeriv (x : ℝ) : ℝ :=
  -(Real.log x + 1) / (x ^ 2 * Real.log x ^ 2)

theorem hasDerivAt_reciprocalPrimeKernel
    {x : ℝ} (hx : x ≠ 0) (hlog : Real.log x ≠ 0) :
    HasDerivAt reciprocalPrimeKernel (reciprocalPrimeKernelDeriv x) x := by
  have hprod : HasDerivAt (fun y : ℝ ↦ y * Real.log y)
      (Real.log x + 1) x := by
    simpa [hx] using! (hasDerivAt_id x).mul (Real.hasDerivAt_log hx)
  have hinv := hprod.inv (mul_ne_zero hx hlog)
  unfold reciprocalPrimeKernel reciprocalPrimeKernelDeriv
  convert! hinv using 1
  field_simp

theorem deriv_reciprocalPrimeKernel
    {x : ℝ} (hx : x ≠ 0) (hlog : Real.log x ≠ 0) :
    deriv reciprocalPrimeKernel x = reciprocalPrimeKernelDeriv x :=
  (hasDerivAt_reciprocalPrimeKernel hx hlog).deriv

theorem integral_reciprocalPrimeKernel
    {A B : ℝ} (hA : 1 < A) (hAB : A ≤ B) :
    (∫ x in A..B, reciprocalPrimeKernel x) =
      Real.log (Real.log B) - Real.log (Real.log A) := by
  have hlogA : 0 < Real.log A := Real.log_pos hA
  have hB : 1 < B := hA.trans_le hAB
  have hlogB : 0 < Real.log B := Real.log_pos hB
  have hint : IntervalIntegrable reciprocalPrimeKernel volume A B := by
    apply ContinuousOn.intervalIntegrable
    intro x hx
    apply ContinuousAt.continuousWithinAt
    have hxIcc : x ∈ Set.Icc A B := by
      simpa [Set.uIcc_of_le hAB] using! hx
    have hx1 : 1 < x := hA.trans_le hxIcc.1
    have hx0 : x ≠ 0 := ne_of_gt (zero_lt_one.trans hx1)
    have hlogx : Real.log x ≠ 0 := (Real.log_pos hx1).ne'
    unfold reciprocalPrimeKernel
    exact (continuousAt_id.mul (Real.continuousAt_log hx0)).inv₀
      (mul_ne_zero hx0 hlogx)
  have hfund := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := A) (b := B)
    (f := fun x : ℝ ↦ Real.log (Real.log x))
    (f' := reciprocalPrimeKernel)
    (fun x hx ↦ by
      have hxIcc : x ∈ Set.Icc A B := by
        simpa [Set.uIcc_of_le hAB] using! hx
      have hx1 : 1 < x := hA.trans_le hxIcc.1
      have hx0 : x ≠ 0 := ne_of_gt (zero_lt_one.trans hx1)
      have hlogx : Real.log x ≠ 0 := (Real.log_pos hx1).ne'
      unfold reciprocalPrimeKernel
      convert! (Real.hasDerivAt_log hx0).log hlogx using 1 <;> field_simp)
    hint
  exact hfund

set_option maxHeartbeats 800000 in
-- The identity expands the Abel integrability witnesses and one integration
-- by parts, so it needs the same budget as the oscillatory theta identity.
theorem freshReciprocalSum_eq_thetaError_abel
    {A B : ℕ} (hA : 2 ≤ A) (hAB : A ≤ B) :
    freshReciprocalSum A B =
      (Real.log (Real.log (B : ℝ)) -
          Real.log (Real.log (A : ℝ))) +
        reciprocalPrimeKernel B * thetaError B -
        reciprocalPrimeKernel A * thetaError A -
        ∫ x in (A : ℝ)..B,
          reciprocalPrimeKernelDeriv x * thetaError x := by
  have hAreal : (1 : ℝ) < A := by exact_mod_cast hA
  have hApos : (0 : ℝ) < A := zero_lt_one.trans hAreal
  have hBreal : (1 : ℝ) < B := hAreal.trans_le (by exact_mod_cast hAB)
  have hBpos : (0 : ℝ) < B := zero_lt_one.trans hBreal
  have hABreal : (A : ℝ) ≤ B := by exact_mod_cast hAB
  have hdiff : ∀ x ∈ Set.Icc (A : ℝ) B,
      DifferentiableAt ℝ reciprocalPrimeKernel x := by
    intro x hx
    have hx1 : 1 < x := hAreal.trans_le hx.1
    exact (hasDerivAt_reciprocalPrimeKernel
      (ne_of_gt (zero_lt_one.trans hx1))
      (ne_of_gt (Real.log_pos hx1))).differentiableAt
  have hderivEq : ∀ x ∈ Set.Icc (A : ℝ) B,
      deriv reciprocalPrimeKernel x = reciprocalPrimeKernelDeriv x := by
    intro x hx
    have hx1 : 1 < x := hAreal.trans_le hx.1
    exact deriv_reciprocalPrimeKernel
      (ne_of_gt (zero_lt_one.trans hx1))
      (ne_of_gt (Real.log_pos hx1))
  have hDcont : ContinuousOn reciprocalPrimeKernelDeriv
      (Set.Icc (A : ℝ) B) := by
    intro x hx
    apply ContinuousAt.continuousWithinAt
    have hx1 : 1 < x := hAreal.trans_le hx.1
    have hx0 : x ≠ 0 := ne_of_gt (zero_lt_one.trans hx1)
    have hlog : Real.log x ≠ 0 := ne_of_gt (Real.log_pos hx1)
    unfold reciprocalPrimeKernelDeriv
    exact ((Real.continuousAt_log hx0).add continuousAt_const).neg.div
      ((continuousAt_id.pow 2).mul ((Real.continuousAt_log hx0).pow 2))
      (mul_ne_zero (pow_ne_zero 2 hx0) (pow_ne_zero 2 hlog))
  have hfint : IntegrableOn (deriv reciprocalPrimeKernel)
      (Set.Icc (A : ℝ) B) :=
    hDcont.integrableOn_Icc.congr_fun
      (fun x hx ↦ (hderivEq x hx).symm) measurableSet_Icc
  have habel := sum_mul_eq_sub_sub_integral_mul'
    primeLogCoeff hAB hdiff hfint
  rw [sum_primeLogCoeff_Icc_nat, sum_primeLogCoeff_Icc_nat] at habel
  simp_rw [sum_primeLogCoeff_Icc] at habel
  rw [← intervalIntegral.integral_of_le hABreal] at habel
  have hthetaInt : IntegrableOn
      (fun x : ℝ ↦ reciprocalPrimeKernelDeriv x * Chebyshev.theta x)
      (Set.Icc (A : ℝ) B) := by
    have hbase := integrableOn_mul_sum_Icc (m := 0) primeLogCoeff
      (show (0 : ℝ) ≤ A by positivity) hfint
    exact hbase.congr_fun (fun x hx ↦ by
      dsimp only
      rw [hderivEq x hx, sum_primeLogCoeff_Icc]) measurableSet_Icc
  have hxInt : IntegrableOn
      (fun x : ℝ ↦ reciprocalPrimeKernelDeriv x * x)
      (Set.Icc (A : ℝ) B) :=
    (hDcont.mul continuousOn_id).integrableOn_Icc
  have herrInt : IntegrableOn
      (fun x : ℝ ↦ reciprocalPrimeKernelDeriv x * thetaError x)
      (Set.Icc (A : ℝ) B) := by
    have hsub := hthetaInt.sub hxInt
    exact hsub.congr_fun (fun x hx ↦ by
      change reciprocalPrimeKernelDeriv x * Chebyshev.theta x -
          reciprocalPrimeKernelDeriv x * x =
        reciprocalPrimeKernelDeriv x * thetaError x
      unfold thetaError
      ring) measurableSet_Icc
  have hkernelInt : IntegrableOn reciprocalPrimeKernel
      (Set.Icc (A : ℝ) B) := by
    apply ContinuousOn.integrableOn_Icc
    intro x hx
    have hx1 : 1 < x := hAreal.trans_le hx.1
    exact (hasDerivAt_reciprocalPrimeKernel
      (ne_of_gt (zero_lt_one.trans hx1))
      (ne_of_gt (Real.log_pos hx1))).continuousAt.continuousWithinAt
  have hDinterval : IntervalIntegrable reciprocalPrimeKernelDeriv volume
      (A : ℝ) B := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hABreal]
    exact hDcont.integrableOn_Icc
  have hxInterval : IntervalIntegrable
      (fun x : ℝ ↦ reciprocalPrimeKernelDeriv x * x) volume (A : ℝ) B := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hABreal]
    exact hxInt
  have herrInterval : IntervalIntegrable
      (fun x : ℝ ↦ reciprocalPrimeKernelDeriv x * thetaError x)
      volume (A : ℝ) B := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hABreal]
    exact herrInt
  have hkernelInterval : IntervalIntegrable reciprocalPrimeKernel volume
      (A : ℝ) B := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hABreal]
    exact hkernelInt
  have hibp :
      (∫ x in (A : ℝ)..B,
          reciprocalPrimeKernelDeriv x * x + reciprocalPrimeKernel x) =
        reciprocalPrimeKernel B * B - reciprocalPrimeKernel A * A := by
    have hibp' := intervalIntegral.integral_deriv_mul_eq_sub
      (a := (A : ℝ)) (b := (B : ℝ))
      (u := reciprocalPrimeKernel) (v := fun x : ℝ ↦ x)
      (u' := reciprocalPrimeKernelDeriv) (v' := fun _ : ℝ ↦ 1)
      (fun x hx ↦ hasDerivAt_reciprocalPrimeKernel
        (ne_of_gt (zero_lt_one.trans <|
          lt_of_lt_of_le (lt_min hAreal hBreal) hx.1))
        (ne_of_gt (Real.log_pos <|
          lt_of_lt_of_le (lt_min hAreal hBreal) hx.1)))
      (fun x _ ↦ hasDerivAt_id x)
      hDinterval continuousOn_const.intervalIntegrable
    simpa only [mul_one] using! hibp'
  have hsplit :
      (∫ x in (A : ℝ)..B,
          reciprocalPrimeKernelDeriv x * Chebyshev.theta x) =
        (∫ x in (A : ℝ)..B, reciprocalPrimeKernelDeriv x * x) +
          ∫ x in (A : ℝ)..B,
            reciprocalPrimeKernelDeriv x * thetaError x := by
    rw [← intervalIntegral.integral_add hxInterval herrInterval]
    apply intervalIntegral.integral_congr
    intro x hx
    unfold thetaError
    ring
  have hderivIntegral :
      (∫ x in (A : ℝ)..B,
          deriv reciprocalPrimeKernel x * Chebyshev.theta x) =
        ∫ x in (A : ℝ)..B,
          reciprocalPrimeKernelDeriv x * Chebyshev.theta x := by
    apply intervalIntegral.integral_congr
    intro x hx
    change deriv reciprocalPrimeKernel x * Chebyshev.theta x =
      reciprocalPrimeKernelDeriv x * Chebyshev.theta x
    rw [hderivEq x (by
      simpa [Set.uIcc_of_le hABreal] using! hx)]
  have hmain := integral_reciprocalPrimeKernel hAreal hABreal
  have hsum : freshReciprocalSum A B =
      ∑ n ∈ Finset.Ioc A B,
        reciprocalPrimeKernel n * primeLogCoeff n := by
    rw [freshReciprocalSum, freshPrimes_eq_Ioc_filter_prime,
      Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro n hn
    by_cases hp : n.Prime
    · simp only [hp, if_true, primeLogCoeff, reciprocalPrimeKernel]
      have hnPos : (0 : ℝ) < n := by exact_mod_cast hp.pos
      have hlog : Real.log (n : ℝ) ≠ 0 := (Real.log_pos <| by
        exact_mod_cast hp.one_lt).ne'
      field_simp
    · simp [hp, primeLogCoeff]
  rw [hderivIntegral] at habel
  rw [hsplit] at habel
  rw [intervalIntegral.integral_add hxInterval hkernelInterval] at hibp
  have hxEval :
      (∫ x in (A : ℝ)..B, reciprocalPrimeKernelDeriv x * x) =
        reciprocalPrimeKernel B * B - reciprocalPrimeKernel A * A -
          ∫ x in (A : ℝ)..B, reciprocalPrimeKernel x := by
    linarith [hibp]
  rw [hsum, habel, hxEval, hmain]
  unfold thetaError
  ring

theorem log_log_nat_square_sub_log_log_eq_log_two
    {A : ℕ} (hA : 1 < A) :
    Real.log (Real.log ((A ^ 2 : ℕ) : ℝ)) -
        Real.log (Real.log (A : ℝ)) = Real.log 2 := by
  have hlog : Real.log (A : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast hA)).ne'
  push_cast
  rw [Real.log_pow]
  norm_num
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hlog]
  ring

theorem invLog_nat_square_eq_half
    {A : ℕ} (hA : 1 < A) :
    invLog ((A ^ 2 : ℕ) : ℝ) = (1 / 2 : ℝ) * invLog A := by
  have hlog : Real.log (A : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast hA)).ne'
  push_cast
  unfold invLog
  rw [Real.log_pow]
  norm_num
  field_simp

noncomputable def reciprocalPrimeErrorPrimitive (x : ℝ) : ℝ :=
  Real.log (Real.log x) - invLog x

theorem hasDerivAt_reciprocalPrimeErrorPrimitive
    {x : ℝ} (hx : 1 < x) :
    HasDerivAt reciprocalPrimeErrorPrimitive
      (-reciprocalPrimeKernelDeriv x * x) x := by
  have hx0 : x ≠ 0 := ne_of_gt (zero_lt_one.trans hx)
  have hlog : Real.log x ≠ 0 := (Real.log_pos hx).ne'
  have hloglog : HasDerivAt (fun y : ℝ ↦ Real.log (Real.log y))
      (reciprocalPrimeKernel x) x := by
    unfold reciprocalPrimeKernel
    convert! (Real.hasDerivAt_log hx0).log hlog using 1
    field_simp
  have hinv := hasDerivAt_invLog hx0 hlog
  unfold reciprocalPrimeErrorPrimitive
  convert! hloglog.sub hinv using 1
  unfold reciprocalPrimeKernel reciprocalPrimeKernelDeriv invLogDeriv
  field_simp
  ring

theorem integral_neg_reciprocalPrimeKernelDeriv_mul_id_square
    {A : ℕ} (hA : 2 ≤ A) :
    (∫ x in (A : ℝ)..(A ^ 2 : ℕ),
        -reciprocalPrimeKernelDeriv x * x) =
      Real.log 2 + (1 / 2 : ℝ) * invLog A := by
  have hAone : 1 < A := by omega
  have hAoneReal : (1 : ℝ) < A := by exact_mod_cast hAone
  have hAB : (A : ℝ) ≤ (A ^ 2 : ℕ) := by
    exact_mod_cast (show A ≤ A ^ 2 by nlinarith)
  have hint : IntervalIntegrable
      (fun x : ℝ ↦ -reciprocalPrimeKernelDeriv x * x)
      volume (A : ℝ) (A ^ 2 : ℕ) := by
    apply ContinuousOn.intervalIntegrable
    intro x hx
    apply ContinuousAt.continuousWithinAt
    have hxIcc := hx
    rw [Set.uIcc_of_le hAB] at hxIcc
    have hx1 : 1 < x := hAoneReal.trans_le hxIcc.1
    have hx0 : x ≠ 0 := ne_of_gt (zero_lt_one.trans hx1)
    have hlog : Real.log x ≠ 0 := (Real.log_pos hx1).ne'
    unfold reciprocalPrimeKernelDeriv
    fun_prop (disch := aesop)
  have hfund := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (A : ℝ)) (b := ((A ^ 2 : ℕ) : ℝ))
    (f := reciprocalPrimeErrorPrimitive)
    (f' := fun x : ℝ ↦ -reciprocalPrimeKernelDeriv x * x)
    (fun x hx ↦ by
      have hxIcc := hx
      rw [Set.uIcc_of_le hAB] at hxIcc
      exact hasDerivAt_reciprocalPrimeErrorPrimitive
        (hAoneReal.trans_le hxIcc.1))
    hint
  rw [hfund]
  unfold reciprocalPrimeErrorPrimitive
  have hlogDiff := log_log_nat_square_sub_log_log_eq_log_two hAone
  have hinvSq := invLog_nat_square_eq_half hAone
  rw [hinvSq]
  linarith

theorem reciprocalPrimeKernelDeriv_nonpos
    {x : ℝ} (hx : 1 < x) :
    reciprocalPrimeKernelDeriv x ≤ 0 := by
  unfold reciprocalPrimeKernelDeriv
  have hlogpos : 0 < Real.log x := Real.log_pos hx
  have hnum : 0 ≤ Real.log x + 1 :=
    add_nonneg hlogpos.le (by norm_num)
  have hden : 0 ≤ x ^ 2 * Real.log x ^ 2 :=
    mul_nonneg (sq_nonneg x) (sq_nonneg (Real.log x))
  simpa only [neg_div] using! neg_nonpos.mpr (div_nonneg hnum hden)

theorem abs_reciprocalPrimeKernel_mul_thetaError_le
    {x delta : ℝ} (hx : 1 < x) (hdelta : 0 ≤ delta)
    (herror : |thetaError x| ≤ delta * x) :
    |reciprocalPrimeKernel x * thetaError x| ≤ delta * invLog x := by
  have hxpos : 0 < x := zero_lt_one.trans hx
  have hlogpos : 0 < Real.log x := Real.log_pos hx
  have hkernel : 0 < reciprocalPrimeKernel x := by
    unfold reciprocalPrimeKernel
    positivity
  rw [abs_mul, abs_of_pos hkernel]
  calc
    reciprocalPrimeKernel x * |thetaError x| ≤
        reciprocalPrimeKernel x * (delta * x) :=
      mul_le_mul_of_nonneg_left herror hkernel.le
    _ = delta * invLog x := by
      unfold reciprocalPrimeKernel invLog
      field_simp

/-- A relative theta error `delta` gives a quantitative Mertens estimate on
the exact square block.  The coarse constant `4` is chosen to keep the later
uniform convergence proof simple. -/
theorem abs_freshReciprocalSum_square_sub_log_two_le_of_thetaError
    {A : ℕ} (hA : 2 ≤ A)
    (hlogA : (1 : ℝ) ≤ Real.log (A : ℝ))
    {delta : ℝ} (hdelta : 0 ≤ delta)
    (herror : ∀ x ∈ Set.Icc (A : ℝ) (A ^ 2 : ℕ),
      |thetaError x| ≤ delta * x) :
    |freshReciprocalSum A (A ^ 2) - Real.log 2| ≤ 4 * delta := by
  have hAone : 1 < A := by omega
  have hAoneReal : (1 : ℝ) < A := by exact_mod_cast hAone
  have hApos : (0 : ℝ) < A := zero_lt_one.trans hAoneReal
  have hABNat : A ≤ A ^ 2 := by nlinarith
  have hAB : (A : ℝ) ≤ (A ^ 2 : ℕ) := by exact_mod_cast hABNat
  have hlogApos : 0 < Real.log (A : ℝ) := Real.log_pos hAoneReal
  have hinvApos : 0 < invLog (A : ℝ) := invLog_pos hAoneReal
  have hinvAle : invLog (A : ℝ) ≤ 1 := by
    unfold invLog
    exact (inv_le_one₀ hlogApos).2 hlogA
  have hmain := freshReciprocalSum_eq_thetaError_abel hA hABNat
  rw [log_log_nat_square_sub_log_log_eq_log_two hAone] at hmain
  have hA_mem : (A : ℝ) ∈ Set.Icc (A : ℝ) (A ^ 2 : ℕ) :=
    ⟨le_rfl, hAB⟩
  have hB_mem : ((A ^ 2 : ℕ) : ℝ) ∈
      Set.Icc (A : ℝ) (A ^ 2 : ℕ) := ⟨hAB, le_rfl⟩
  have hboundA :
      |reciprocalPrimeKernel A * thetaError A| ≤ delta := by
    have h := abs_reciprocalPrimeKernel_mul_thetaError_le
      hAoneReal hdelta (herror A hA_mem)
    exact h.trans (by nlinarith)
  have hBone : 1 < (A ^ 2 : ℕ) := hAone.trans_le hABNat
  have hboundB :
      |reciprocalPrimeKernel (A ^ 2 : ℕ) * thetaError (A ^ 2 : ℕ)| ≤
        delta := by
    have h := abs_reciprocalPrimeKernel_mul_thetaError_le
      (by exact_mod_cast hBone) hdelta (herror (A ^ 2 : ℕ) hB_mem)
    rw [invLog_nat_square_eq_half hAone] at h
    exact h.trans (by nlinarith)
  have hmajorInt : IntervalIntegrable
      (fun x : ℝ ↦ delta * (-reciprocalPrimeKernelDeriv x * x))
      volume (A : ℝ) (A ^ 2 : ℕ) := by
    apply ContinuousOn.intervalIntegrable
    intro x hx
    apply ContinuousAt.continuousWithinAt
    have hxIcc := hx
    rw [Set.uIcc_of_le hAB] at hxIcc
    have hx1 : 1 < x := hAoneReal.trans_le hxIcc.1
    have hx0 : x ≠ 0 := ne_of_gt (zero_lt_one.trans hx1)
    have hlog : Real.log x ≠ 0 := (Real.log_pos hx1).ne'
    unfold reciprocalPrimeKernelDeriv
    fun_prop (disch := aesop)
  have hpoint : ∀ x ∈ Set.Ioc (A : ℝ) (A ^ 2 : ℕ),
      |reciprocalPrimeKernelDeriv x * thetaError x| ≤
        delta * (-reciprocalPrimeKernelDeriv x * x) := by
    intro x hx
    have hxIcc : x ∈ Set.Icc (A : ℝ) (A ^ 2 : ℕ) := ⟨hx.1.le, hx.2⟩
    have hx1 : 1 < x := hAoneReal.trans hx.1
    have hDnonpos := reciprocalPrimeKernelDeriv_nonpos hx1
    rw [abs_mul, abs_of_nonpos hDnonpos]
    calc
      -reciprocalPrimeKernelDeriv x * |thetaError x| ≤
          -reciprocalPrimeKernelDeriv x * (delta * x) :=
        mul_le_mul_of_nonneg_left (herror x hxIcc)
          (neg_nonneg.mpr hDnonpos)
      _ = delta * (-reciprocalPrimeKernelDeriv x * x) := by ring
  have hinterr :
      |∫ x in (A : ℝ)..(A ^ 2 : ℕ),
          reciprocalPrimeKernelDeriv x * thetaError x| ≤ 2 * delta := by
    have hnorm :
        ‖∫ x in (A : ℝ)..(A ^ 2 : ℕ),
            reciprocalPrimeKernelDeriv x * thetaError x‖ ≤
          ∫ x in (A : ℝ)..(A ^ 2 : ℕ),
            delta * (-reciprocalPrimeKernelDeriv x * x) :=
      intervalIntegral.norm_integral_le_of_norm_le
        (μ := volume) hAB
        (Filter.Eventually.of_forall fun x ↦ by
          intro hx
          simpa only [Real.norm_eq_abs] using! hpoint x hx)
        hmajorInt
    rw [intervalIntegral.integral_const_mul,
      integral_neg_reciprocalPrimeKernelDeriv_mul_id_square hA] at hnorm
    rw [Real.norm_eq_abs] at hnorm
    have hlogTwo : Real.log 2 ≤ 1 :=
      (Real.log_le_sub_one_of_pos (by norm_num)).trans_eq (by norm_num)
    exact hnorm.trans (by nlinarith)
  rw [hmain]
  have htri :
      |(Real.log 2 + reciprocalPrimeKernel ↑(A ^ 2) * thetaError ↑(A ^ 2) -
          reciprocalPrimeKernel ↑A * thetaError ↑A -
          ∫ x in (A : ℝ)..↑(A ^ 2),
            reciprocalPrimeKernelDeriv x * thetaError x) - Real.log 2| ≤
        |reciprocalPrimeKernel ↑(A ^ 2) * thetaError ↑(A ^ 2)| +
          |reciprocalPrimeKernel ↑A * thetaError ↑A| +
          |∫ x in (A : ℝ)..↑(A ^ 2),
            reciprocalPrimeKernelDeriv x * thetaError x| := by
    calc
      |(Real.log 2 + reciprocalPrimeKernel ↑(A ^ 2) * thetaError ↑(A ^ 2) -
          reciprocalPrimeKernel ↑A * thetaError ↑A -
          ∫ x in (A : ℝ)..↑(A ^ 2),
            reciprocalPrimeKernelDeriv x * thetaError x) - Real.log 2| =
        |reciprocalPrimeKernel ↑(A ^ 2) * thetaError ↑(A ^ 2) -
          reciprocalPrimeKernel ↑A * thetaError ↑A -
          ∫ x in (A : ℝ)..↑(A ^ 2),
            reciprocalPrimeKernelDeriv x * thetaError x| := by ring_nf
      _ ≤ |reciprocalPrimeKernel ↑(A ^ 2) * thetaError ↑(A ^ 2) -
          reciprocalPrimeKernel ↑A * thetaError ↑A| +
          |∫ x in (A : ℝ)..↑(A ^ 2),
            reciprocalPrimeKernelDeriv x * thetaError x| := abs_sub _ _
      _ ≤ (|reciprocalPrimeKernel ↑(A ^ 2) * thetaError ↑(A ^ 2)| +
          |reciprocalPrimeKernel ↑A * thetaError ↑A|) +
          |∫ x in (A : ℝ)..↑(A ^ 2),
            reciprocalPrimeKernelDeriv x * thetaError x| := by
        gcongr
        exact abs_sub _ _
      _ = _ := by ring
  exact htri.trans (by linarith)

/-- Strong PNT implies the sharp Mertens limit on the square blocks used by
the Harper schedule. -/
theorem tendsto_square_primeReciprocalBlock_log_two :
    Tendsto (fun A : ℕ ↦ freshReciprocalSum A (A ^ 2))
      atTop (𝓝 (Real.log 2)) := by
  obtain ⟨c, hc, C, hC, X₀, hX₀two, htheta⟩ := exists_mediumThetaError
  let delta : ℕ → ℝ := fun A ↦ mediumThetaBlockDelta c C A (A ^ 2)
  have hdelta : Tendsto delta atTop (𝓝 0) := by
    have htReal := tendsto_mediumThetaSquareDelta_zero (C := C) hc
    have htNat := htReal.comp tendsto_natCast_atTop_atTop
    apply htNat.congr'
    filter_upwards [] with A
    dsimp [delta]
    rw [mediumThetaBlockDelta_square_eq]
  obtain ⟨NX, hNX⟩ := exists_nat_ge X₀
  obtain ⟨Ne, hNe⟩ := exists_nat_ge (Real.exp 1)
  let N := max 2 (max NX Ne)
  have hbound : ∀ᶠ A : ℕ in atTop,
      |freshReciprocalSum A (A ^ 2) - Real.log 2| ≤ 4 * delta A := by
    filter_upwards [eventually_ge_atTop N] with A hNA
    have hA2 : 2 ≤ A := (le_max_left 2 _).trans hNA
    have hANX : NX ≤ A :=
      (le_max_left NX Ne).trans ((le_max_right 2 _).trans hNA)
    have hANe : Ne ≤ A :=
      (le_max_right NX Ne).trans ((le_max_right 2 _).trans hNA)
    have hApos : (0 : ℝ) < A := by positivity
    have hAB : A ≤ A ^ 2 := by nlinarith
    have hX₀A : X₀ ≤ (A : ℝ) := hNX.trans (by exact_mod_cast hANX)
    have hexpA : Real.exp 1 ≤ (A : ℝ) :=
      hNe.trans (by exact_mod_cast hANe)
    have hlogA : (1 : ℝ) ≤ Real.log (A : ℝ) := by
      have := Real.log_le_log (Real.exp_pos 1) hexpA
      simpa using! this
    have hdeltaNonneg : 0 ≤ delta A := by
      dsimp [delta]
      unfold mediumThetaBlockDelta
      positivity
    apply abs_freshReciprocalSum_square_sub_log_two_le_of_thetaError
      hA2 hlogA hdeltaNonneg
    intro x hx
    exact thetaError_le_mediumThetaBlockDelta hc hC.le htheta
      hA2 hAB hX₀A hx
  apply tendsto_iff_norm_sub_tendsto_zero.2
  apply squeeze_zero'
    (Filter.Eventually.of_forall fun A ↦
      norm_nonneg (freshReciprocalSum A (A ^ 2) - Real.log 2))
    (by
      filter_upwards [hbound] with A hA
      simpa only [Real.norm_eq_abs] using! hA)
  have hfour : Tendsto (fun _ : ℕ ↦ (4 : ℝ)) atTop (nhds 4) :=
    tendsto_const_nhds
  convert! hfour.mul hdelta using 1 <;> norm_num

/-- The reciprocal mass of every sufficiently late scheduled block is
uniformly close to `log 2`, independently of the ambient cutoff containing
the block. -/
theorem exists_eventually_harperScheduledPrimeBlock_inv_close_log_two
    {ε : ℝ} (hε : 0 < ε) :
    ∃ J : ℕ, ∀ j : ℕ, J ≤ j → ∀ y : ℕ,
      harperBlockEndpoint (j + 1) ≤ y →
        |∑ p ∈ harperScheduledPrimeBlock y j, (p.1 : ℝ)⁻¹ -
            Real.log 2| < ε := by
  have ht : Tendsto
      (fun j : ℕ ↦ freshReciprocalSum (harperBlockEndpoint j)
        (harperBlockEndpoint j ^ 2)) atTop (𝓝 (Real.log 2)) :=
    tendsto_square_primeReciprocalBlock_log_two.comp
      strictMono_harperBlockEndpoint.tendsto_atTop
  have hnorm : Tendsto
      (fun j : ℕ ↦
        ‖freshReciprocalSum (harperBlockEndpoint j)
            (harperBlockEndpoint j ^ 2) - Real.log 2‖)
      atTop (𝓝 0) := tendsto_iff_norm_sub_tendsto_zero.1 ht
  have hevent : ∀ᶠ j : ℕ in atTop,
      |freshReciprocalSum (harperBlockEndpoint j)
          (harperBlockEndpoint j ^ 2) - Real.log 2| < ε := by
    have hlt := (tendsto_order.mp hnorm).2 ε hε
    simpa only [Real.norm_eq_abs] using! hlt
  obtain ⟨J, hJ⟩ := Filter.eventually_atTop.1 hevent
  refine ⟨J, ?_⟩
  intro j hj y hy
  rw [sum_harperScheduledPrimeBlock_inv_eq_freshReciprocalSum hy,
    harperBlockEndpoint_succ]
  exact hJ j hj

/-- The part of the fair-sign diagonal variance removed by the tilted mean.
It is nonnegative and, on late scheduled blocks, uniformly negligible. -/
noncomputable def harperScheduledVarianceBiasLoss
    (y j : ℕ) (t : ℝ) : ℝ :=
  ∑ p ∈ harperScheduledPrimeBlock y j,
    (Real.cos (t * Real.log (p.1 : ℝ)) ^ 2 / p.1) *
      harperTiltBias p.1 t ^ 2

theorem harperScheduledVarianceBiasLoss_nonneg
    (y j : ℕ) (t : ℝ) :
    0 ≤ harperScheduledVarianceBiasLoss y j t := by
  unfold harperScheduledVarianceBiasLoss
  exact Finset.sum_nonneg fun p hp ↦
    mul_nonneg (div_nonneg (sq_nonneg _) (by positivity)) (sq_nonneg _)

theorem harperScheduledDiagonalVariance_eq_cosineMass_sub_biasLoss
    (y j : ℕ) (t : ℝ) :
    harperLinearBlockVariance y (harperScheduledPrimeBlock y j) t t =
      (∑ p ∈ harperScheduledPrimeBlock y j,
        Real.cos (t * Real.log (p.1 : ℝ)) ^ 2 / p.1) -
        harperScheduledVarianceBiasLoss y j t := by
  unfold harperLinearBlockVariance harperScheduledVarianceBiasLoss
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  unfold harperLinearPrimeCenteredVariance
  rw [harperPrimeCoefficient_sq (by
    have := sixteen_le_prime_of_mem_harperScheduledPrimeBlock hp
    omega)]
  ring

/-- The tilt-bias loss is bounded by `4/A` times the reciprocal mass, where
`A` is the lower endpoint of the scheduled block. -/
theorem harperScheduledVarianceBiasLoss_le
    (y j : ℕ) (t : ℝ) :
    harperScheduledVarianceBiasLoss y j t ≤
      (4 / (harperBlockEndpoint j : ℝ)) *
        ∑ p ∈ harperScheduledPrimeBlock y j, (p.1 : ℝ)⁻¹ := by
  unfold harperScheduledVarianceBiasLoss
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro p hp
  have hpNat : 0 < p.1 := by
    have := sixteen_le_prime_of_mem_harperScheduledPrimeBlock hp
    omega
  have hpReal : (0 : ℝ) < p.1 := by exact_mod_cast hpNat
  have hANat : 0 < harperBlockEndpoint j := by
    have := harperBlockEndpoint_ge_sixteen j
    omega
  have hAReal : (0 : ℝ) < harperBlockEndpoint j := by exact_mod_cast hANat
  have hApNat : harperBlockEndpoint j ≤ p.1 :=
    ((mem_harperScheduledPrimeBlock p).mp hp).1.le
  have hApReal : (harperBlockEndpoint j : ℝ) ≤ p.1 := by
    exact_mod_cast hApNat
  have hcosSq : Real.cos (t * Real.log (p.1 : ℝ)) ^ 2 ≤ 1 := by
    nlinarith [Real.neg_one_le_cos (t * Real.log (p.1 : ℝ)),
      Real.cos_le_one (t * Real.log (p.1 : ℝ))]
  have hcoeffNonneg :
      0 ≤ Real.cos (t * Real.log (p.1 : ℝ)) ^ 2 / p.1 :=
    div_nonneg (sq_nonneg _) hpReal.le
  have hcoeffLe :
      Real.cos (t * Real.log (p.1 : ℝ)) ^ 2 / p.1 ≤
        (p.1 : ℝ)⁻¹ := by
    rw [inv_eq_one_div]
    exact (div_le_div_iff_of_pos_right hpReal).2 hcosSq
  have hfourDiv : 4 / (p.1 : ℝ) ≤
      4 / (harperBlockEndpoint j : ℝ) := by
    exact div_le_div_of_nonneg_left (by norm_num) hAReal hApReal
  calc
    (Real.cos (t * Real.log (p.1 : ℝ)) ^ 2 / p.1) *
        harperTiltBias p.1 t ^ 2 ≤
      (Real.cos (t * Real.log (p.1 : ℝ)) ^ 2 / p.1) *
        (4 / (p.1 : ℝ)) :=
      mul_le_mul_of_nonneg_left
        (harperTiltBias_sq_le_four_div hpNat t) hcoeffNonneg
    _ ≤ (p.1 : ℝ)⁻¹ * (4 / (p.1 : ℝ)) :=
      mul_le_mul_of_nonneg_right hcoeffLe (by positivity)
    _ ≤ (p.1 : ℝ)⁻¹ *
        (4 / (harperBlockEndpoint j : ℝ)) :=
      mul_le_mul_of_nonneg_left hfourDiv (by positivity)
    _ = (4 / (harperBlockEndpoint j : ℝ)) * (p.1 : ℝ)⁻¹ := by
      ring

/-- The variance loss caused by the tilted coordinate means vanishes
uniformly in the frequency and in the ambient cutoff. -/
theorem exists_eventually_harperScheduledVarianceBiasLoss_lt
    {ε : ℝ} (hε : 0 < ε) :
    ∃ J : ℕ, ∀ j : ℕ, J ≤ j → ∀ y : ℕ,
      harperBlockEndpoint (j + 1) ≤ y → ∀ t : ℝ,
        harperScheduledVarianceBiasLoss y j t < ε := by
  obtain ⟨Jmass, hmass⟩ :=
    exists_eventually_harperScheduledPrimeBlock_inv_bounds
  have hend : Tendsto harperBlockEndpoint atTop atTop :=
    strictMono_harperBlockEndpoint.tendsto_atTop
  have hcast : Tendsto (fun j : ℕ ↦ (harperBlockEndpoint j : ℝ))
      atTop atTop := tendsto_natCast_atTop_atTop.comp hend
  have hinv : Tendsto
      (fun j : ℕ ↦ (harperBlockEndpoint j : ℝ)⁻¹)
      atTop (𝓝 0) := tendsto_inv_atTop_zero.comp hcast
  have hsixConst : Tendsto (fun _ : ℕ ↦ (6 : ℝ)) atTop (𝓝 6) :=
    tendsto_const_nhds
  have hsix : Tendsto
      (fun j : ℕ ↦ 6 * (harperBlockEndpoint j : ℝ)⁻¹)
      atTop (𝓝 0) := by
    convert! hsixConst.mul hinv using 1 <;> norm_num
  have hevent : ∀ᶠ j : ℕ in atTop,
      6 * (harperBlockEndpoint j : ℝ)⁻¹ < ε :=
    (tendsto_order.mp hsix).2 ε hε
  obtain ⟨Jsmall, hsmall⟩ := Filter.eventually_atTop.1 hevent
  refine ⟨max Jmass Jsmall, ?_⟩
  intro j hj y hy t
  have hjmass : Jmass ≤ j := (le_max_left Jmass Jsmall).trans hj
  have hjsmall : Jsmall ≤ j := (le_max_right Jmass Jsmall).trans hj
  have hApos : (0 : ℝ) < harperBlockEndpoint j := by
    exact_mod_cast (show 0 < harperBlockEndpoint j by
      have := harperBlockEndpoint_ge_sixteen j
      omega)
  calc
    harperScheduledVarianceBiasLoss y j t ≤
        (4 / (harperBlockEndpoint j : ℝ)) *
          ∑ p ∈ harperScheduledPrimeBlock y j, (p.1 : ℝ)⁻¹ :=
      harperScheduledVarianceBiasLoss_le y j t
    _ ≤ (4 / (harperBlockEndpoint j : ℝ)) * (3 / 2 : ℝ) :=
      mul_le_mul_of_nonneg_left (hmass j hjmass y hy).2 (by positivity)
    _ = 6 * (harperBlockEndpoint j : ℝ)⁻¹ := by ring
    _ < ε := hsmall j hjsmall

/-- On every fixed noncentral frequency window, the scheduled diagonal
variance converges uniformly to the fixed value `(log 2) / 2`. -/
theorem exists_eventually_harperScheduledDiagonalVariance_close
    (M : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ J : ℕ, ∀ j : ℕ, J ≤ j → ∀ y : ℕ,
      harperBlockEndpoint (j + 1) ≤ y →
        ∀ t : ℝ, 1 ≤ |t| → |t| ≤ M →
          |harperLinearBlockVariance y
              (harperScheduledPrimeBlock y j) t t - Real.log 2 / 2| < ε := by
  have hhalf : 0 < ε / 2 := by positivity
  obtain ⟨Jmass, hmass⟩ :=
    exists_eventually_harperScheduledPrimeBlock_inv_close_log_two hhalf
  obtain ⟨Josc, hosc⟩ :=
    exists_eventually_harperScheduledPrimeOscillation_le M hhalf
  obtain ⟨Jloss, hloss⟩ :=
    exists_eventually_harperScheduledVarianceBiasLoss_lt hhalf
  refine ⟨max Jmass (max Josc Jloss), ?_⟩
  intro j hj y hy t htLower htUpper
  have hjmass : Jmass ≤ j :=
    (le_max_left Jmass (max Josc Jloss)).trans hj
  have hjosc : Josc ≤ j :=
    (le_max_left Josc Jloss).trans
      ((le_max_right Jmass (max Josc Jloss)).trans hj)
  have hjloss : Jloss ≤ j :=
    (le_max_right Josc Jloss).trans
      ((le_max_right Jmass (max Josc Jloss)).trans hj)
  let reciprocalMass : ℝ :=
    ∑ p ∈ harperScheduledPrimeBlock y j, (p.1 : ℝ)⁻¹
  let oscillatoryMass : ℝ :=
    ∑ p ∈ harperScheduledPrimeBlock y j,
      Real.cos ((2 * t) * Real.log (p.1 : ℝ)) / p.1
  let biasLoss : ℝ := harperScheduledVarianceBiasLoss y j t
  have hmassj : |reciprocalMass - Real.log 2| < ε / 2 := by
    exact hmass j hjmass y hy
  have habsTwo : |2 * t| = 2 * |t| := by
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  have htauLower : 2 ≤ |2 * t| := by rw [habsTwo]; linarith
  have htauUpper : |2 * t| ≤ 2 * M := by
    rw [habsTwo]
    exact mul_le_mul_of_nonneg_left htUpper (by norm_num)
  have hoscj : |oscillatoryMass| ≤ ε / 2 := by
    exact hosc j hjosc y hy (2 * t) htauLower htauUpper
  have hlossj : biasLoss < ε / 2 := by
    exact hloss j hjloss y hy t
  have hlossNonneg : 0 ≤ biasLoss := by
    exact harperScheduledVarianceBiasLoss_nonneg y j t
  have hvarianceIdentity :
      harperLinearBlockVariance y
          (harperScheduledPrimeBlock y j) t t =
        (1 / 2 : ℝ) * (reciprocalMass + oscillatoryMass) - biasLoss := by
    rw [harperScheduledDiagonalVariance_eq_cosineMass_sub_biasLoss,
      sum_harperScheduledPrimeBlock_cos_sq_div]
  rw [hvarianceIdentity, abs_lt]
  have hmassLower := neg_lt_of_abs_lt hmassj
  have hmassUpper := lt_of_abs_lt hmassj
  have hoscLower := neg_le_of_abs_le hoscj
  have hoscUpper := le_of_abs_le hoscj
  constructor <;> nlinarith

/-- A convenient fully numerical consequence of the sharp variance limit.
The interval is deliberately generous for later Gaussian-comparison use. -/
theorem exists_eventually_harperScheduledDiagonalVariance_third_threeEighths
    (M : ℕ) :
    ∃ J : ℕ, ∀ j : ℕ, J ≤ j → ∀ y : ℕ,
      harperBlockEndpoint (j + 1) ≤ y →
        ∀ t : ℝ, 1 ≤ |t| → |t| ≤ M →
          (1 / 3 : ℝ) <
              harperLinearBlockVariance y
                (harperScheduledPrimeBlock y j) t t ∧
            harperLinearBlockVariance y
                (harperScheduledPrimeBlock y j) t t < 3 / 8 := by
  obtain ⟨J, hJ⟩ :=
    exists_eventually_harperScheduledDiagonalVariance_close M
      (by norm_num : (0 : ℝ) < 1 / 100)
  refine ⟨J, ?_⟩
  intro j hj y hy t htLower htUpper
  have hclose := hJ j hj y hy t htLower htUpper
  have hlower := neg_lt_of_abs_lt hclose
  have hupper := lt_of_abs_lt hclose
  constructor <;> nlinarith [Real.log_two_gt_d9, Real.log_two_lt_d9]

end Problem520
end Erdos
