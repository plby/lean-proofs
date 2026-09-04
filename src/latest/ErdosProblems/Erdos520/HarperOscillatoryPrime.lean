import ErdosProblems.Erdos49.PNT.MediumPNT
import Mathlib.NumberTheory.AbelSummation

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open Set Function Filter Finset MeasureTheory
open scoped Chebyshev BigOperators Interval

noncomputable section

namespace Erdos
namespace Problem520

noncomputable def oscKernel (tau x : ℝ) : ℝ :=
  Real.cos (tau * Real.log x) / x

noncomputable def oscKernelDeriv (tau x : ℝ) : ℝ :=
  -(tau * Real.sin (tau * Real.log x) + Real.cos (tau * Real.log x)) / x ^ 2

theorem hasDerivAt_oscKernel (tau : ℝ) {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (oscKernel tau) (oscKernelDeriv tau x) x := by
  unfold oscKernel oscKernelDeriv
  convert!
    ((Real.hasDerivAt_cos (tau * Real.log x)).comp x
      ((Real.hasDerivAt_log hx).const_mul tau)).div
        (hasDerivAt_id x) hx using 1
  all_goals try simp only [Function.comp_apply, id_eq]
  all_goals field_simp [hx]
  all_goals ring

theorem deriv_oscKernel (tau : ℝ) {x : ℝ} (hx : x ≠ 0) :
    deriv (oscKernel tau) x = oscKernelDeriv tau x :=
  (hasDerivAt_oscKernel tau hx).deriv

theorem abs_oscKernel_le_inv {tau x : ℝ} (hx : 0 < x) :
    |oscKernel tau x| ≤ x⁻¹ := by
  rw [oscKernel, abs_div, abs_of_pos hx]
  rw [div_le_iff₀ hx]
  simpa [hx.ne'] using! (Real.abs_cos_le_one (tau * Real.log x))

theorem abs_oscKernelDeriv_le {tau x : ℝ} (hx : 0 < x) :
    |oscKernelDeriv tau x| ≤ (1 + |tau|) / x ^ 2 := by
  rw [oscKernelDeriv, abs_div, abs_neg, abs_pow, abs_of_pos hx]
  have htri := abs_add_le
    (tau * Real.sin (tau * Real.log x))
    (Real.cos (tau * Real.log x))
  calc
    |tau * Real.sin (tau * Real.log x) + Real.cos (tau * Real.log x)| / x ^ 2 ≤
        (|tau * Real.sin (tau * Real.log x)| +
          |Real.cos (tau * Real.log x)|) / x ^ 2 := by gcongr
    _ ≤ (|tau| * 1 + 1) / x ^ 2 := by
      gcongr
      · rw [abs_mul]
        gcongr
        exact Real.abs_sin_le_one _
      · exact Real.abs_cos_le_one _
    _ = (1 + |tau|) / x ^ 2 := by ring

noncomputable def oscPrimitive (tau x : ℝ) : ℝ :=
  Real.sin (tau * Real.log x) / tau

theorem hasDerivAt_oscPrimitive {tau x : ℝ} (htau : tau ≠ 0) (hx : x ≠ 0) :
    HasDerivAt (oscPrimitive tau) (oscKernel tau x) x := by
  unfold oscPrimitive oscKernel
  convert!
    (((Real.hasDerivAt_sin (tau * Real.log x)).comp x
      ((Real.hasDerivAt_log hx).const_mul tau)).div_const tau) using 1
  all_goals field_simp [htau, hx]

theorem integral_oscKernel {A B tau : ℝ}
    (hA : 0 < A) (hB : 0 < B) (htau : tau ≠ 0) :
    (∫ x in A..B, oscKernel tau x) =
      oscPrimitive tau B - oscPrimitive tau A := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro x hx
    exact hasDerivAt_oscPrimitive htau
      (ne_of_gt (lt_of_lt_of_le (lt_min hA hB) hx.1))
  · apply ContinuousOn.intervalIntegrable
    intro x hx
    exact (hasDerivAt_oscKernel tau
      (ne_of_gt (lt_of_lt_of_le (lt_min hA hB) hx.1))).continuousAt.continuousWithinAt

theorem abs_integral_oscKernel_le {A B tau : ℝ}
    (hA : 0 < A) (hB : 0 < B) (htau : tau ≠ 0) :
    |(∫ x in A..B, oscKernel tau x)| ≤ 2 / |tau| := by
  rw [integral_oscKernel hA hB htau, oscPrimitive, oscPrimitive,
    abs_sub_comm, ← sub_div, abs_div]
  have htauAbs : 0 < |tau| := abs_pos.mpr htau
  apply (div_le_div_iff_of_pos_right htauAbs).2
  calc
    |Real.sin (tau * Real.log A) - Real.sin (tau * Real.log B)| ≤
        |Real.sin (tau * Real.log A)| + |Real.sin (tau * Real.log B)| :=
      abs_sub _ _
    _ ≤ 1 + 1 := add_le_add (Real.abs_sin_le_one _) (Real.abs_sin_le_one _)
    _ = 2 := by norm_num

noncomputable def primeLogCoeff (n : ℕ) : ℝ :=
  if n.Prime then Real.log (n : ℝ) else 0

theorem sum_primeLogCoeff_Icc (x : ℝ) :
    ∑ n ∈ Finset.Icc 0 ⌊x⌋₊, primeLogCoeff n = Chebyshev.theta x := by
  rw [Chebyshev.theta_eq_sum_Icc, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n hn
  simp [primeLogCoeff]

theorem sum_primeLogCoeff_Icc_nat (N : ℕ) :
    ∑ n ∈ Finset.Icc 0 N, primeLogCoeff n = Chebyshev.theta N := by
  simpa using! sum_primeLogCoeff_Icc (N : ℝ)

noncomputable def thetaError (x : ℝ) : ℝ :=
  Chebyshev.theta x - x

set_option maxHeartbeats 800000 in
-- Abel summation plus interval integration needs a larger elaboration budget.
theorem weightedPrimeOscillation_abel_identity
    {A B : ℕ} (hA : 1 ≤ A) (hAB : A ≤ B) (tau : ℝ) :
    (∑ n ∈ Finset.Ioc A B, oscKernel tau n * primeLogCoeff n) =
      (∫ x in (A : ℝ)..B, oscKernel tau x) +
        oscKernel tau B * thetaError B -
        oscKernel tau A * thetaError A -
        ∫ x in (A : ℝ)..B, oscKernelDeriv tau x * thetaError x := by
  have hAreal : (0 : ℝ) < A := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hA)
  have hBreal : (0 : ℝ) < B := hAreal.trans_le (by exact_mod_cast hAB)
  have hABreal : (A : ℝ) ≤ B := by exact_mod_cast hAB
  have hdiff : ∀ x ∈ Set.Icc (A : ℝ) B,
      DifferentiableAt ℝ (oscKernel tau) x := by
    intro x hx
    exact (hasDerivAt_oscKernel tau
      (ne_of_gt (hAreal.trans_le hx.1))).differentiableAt
  have hderivEq : ∀ x ∈ Set.Icc (A : ℝ) B,
      deriv (oscKernel tau) x = oscKernelDeriv tau x := by
    intro x hx
    exact deriv_oscKernel tau (ne_of_gt (hAreal.trans_le hx.1))
  have hDcont : ContinuousOn (oscKernelDeriv tau) (Set.Icc (A : ℝ) B) := by
    intro x hx
    apply ContinuousAt.continuousWithinAt
    unfold oscKernelDeriv
    have hx0 : x ≠ 0 := ne_of_gt (hAreal.trans_le hx.1)
    fun_prop (disch := positivity)
  have hfint : IntegrableOn (deriv (oscKernel tau)) (Set.Icc (A : ℝ) B) := by
    exact hDcont.integrableOn_Icc.congr_fun
      (fun x hx ↦ (hderivEq x hx).symm) measurableSet_Icc
  have habel := sum_mul_eq_sub_sub_integral_mul'
    primeLogCoeff hAB hdiff hfint
  rw [sum_primeLogCoeff_Icc_nat, sum_primeLogCoeff_Icc_nat] at habel
  simp_rw [sum_primeLogCoeff_Icc] at habel
  rw [← intervalIntegral.integral_of_le hABreal] at habel
  have hthetaInt : IntegrableOn
      (fun x : ℝ ↦ oscKernelDeriv tau x * Chebyshev.theta x)
      (Set.Icc (A : ℝ) B) := by
    have hbase := integrableOn_mul_sum_Icc (m := 0) primeLogCoeff
      (show (0 : ℝ) ≤ A by positivity) hfint
    exact hbase.congr_fun (fun x hx ↦ by
      dsimp only
      rw [hderivEq x hx, sum_primeLogCoeff_Icc]) measurableSet_Icc
  have hxInt : IntegrableOn
      (fun x : ℝ ↦ oscKernelDeriv tau x * x)
      (Set.Icc (A : ℝ) B) := by
    exact (hDcont.mul continuousOn_id).integrableOn_Icc
  have herrInt : IntegrableOn
      (fun x : ℝ ↦ oscKernelDeriv tau x * thetaError x)
      (Set.Icc (A : ℝ) B) := by
    have hsub := hthetaInt.sub hxInt
    exact hsub.congr_fun (fun x hx ↦ by
      change oscKernelDeriv tau x * Chebyshev.theta x -
          oscKernelDeriv tau x * x = oscKernelDeriv tau x * thetaError x
      unfold thetaError
      ring) measurableSet_Icc
  have hkernelInt : IntegrableOn (oscKernel tau) (Set.Icc (A : ℝ) B) := by
    apply ContinuousOn.integrableOn_Icc
    intro x hx
    exact (hasDerivAt_oscKernel tau
      (ne_of_gt (hAreal.trans_le hx.1))).continuousAt.continuousWithinAt
  have hDinterval : IntervalIntegrable (oscKernelDeriv tau) volume (A : ℝ) B := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hABreal]
    exact hDcont.integrableOn_Icc
  have hxInterval : IntervalIntegrable
      (fun x : ℝ ↦ oscKernelDeriv tau x * x) volume (A : ℝ) B := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hABreal]
    exact hxInt
  have herrInterval : IntervalIntegrable
      (fun x : ℝ ↦ oscKernelDeriv tau x * thetaError x)
      volume (A : ℝ) B := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hABreal]
    exact herrInt
  have hkernelInterval : IntervalIntegrable (oscKernel tau) volume (A : ℝ) B := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hABreal]
    exact hkernelInt
  have hibp :
      (∫ x in (A : ℝ)..B,
          oscKernelDeriv tau x * x + oscKernel tau x) =
        oscKernel tau B * B - oscKernel tau A * A := by
    have hibp' := intervalIntegral.integral_deriv_mul_eq_sub
      (a := (A : ℝ)) (b := (B : ℝ))
      (u := oscKernel tau) (v := fun x : ℝ ↦ x)
      (u' := oscKernelDeriv tau) (v' := fun _ : ℝ ↦ 1)
      (fun x hx ↦ hasDerivAt_oscKernel tau
        (ne_of_gt (lt_of_lt_of_le (lt_min hAreal hBreal) hx.1)))
      (fun x _ ↦ hasDerivAt_id x)
      hDinterval continuousOn_const.intervalIntegrable
    simpa only [mul_one] using! hibp'
  have hsplit :
      (∫ x in (A : ℝ)..B, oscKernelDeriv tau x * Chebyshev.theta x) =
        (∫ x in (A : ℝ)..B, oscKernelDeriv tau x * x) +
          ∫ x in (A : ℝ)..B, oscKernelDeriv tau x * thetaError x := by
    rw [← intervalIntegral.integral_add hxInterval herrInterval]
    apply intervalIntegral.integral_congr
    intro x hx
    unfold thetaError
    ring
  have hderivIntegral :
      (∫ x in (A : ℝ)..B, deriv (oscKernel tau) x * Chebyshev.theta x) =
        ∫ x in (A : ℝ)..B, oscKernelDeriv tau x * Chebyshev.theta x := by
    apply intervalIntegral.integral_congr
    intro x hx
    change deriv (oscKernel tau) x * Chebyshev.theta x =
      oscKernelDeriv tau x * Chebyshev.theta x
    rw [hderivEq x (by
      simpa [Set.uIcc_of_le hABreal] using! hx)]
  rw [hderivIntegral] at habel
  rw [hsplit] at habel
  rw [intervalIntegral.integral_add hxInterval hkernelInterval] at hibp
  rw [habel]
  unfold thetaError
  linarith

set_option maxHeartbeats 800000 in
-- The explicit integral majorant produces a large arithmetic proof term.
theorem abs_weightedPrimeOscillation_le_of_thetaError
    {A B : ℕ} (hA : 1 ≤ A) (hAB : A ≤ B) {tau delta : ℝ}
    (htau : tau ≠ 0)
    (herror : ∀ x ∈ Set.Icc (A : ℝ) B,
      |thetaError x| ≤ delta * x) :
    |∑ n ∈ Finset.Ioc A B, oscKernel tau n * primeLogCoeff n| ≤
      2 / |tau| + 2 * delta +
        delta * (1 + |tau|) * Real.log ((B : ℝ) / A) := by
  have hAreal : (0 : ℝ) < A := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hA)
  have hBreal : (0 : ℝ) < B := hAreal.trans_le (by exact_mod_cast hAB)
  have hABreal : (A : ℝ) ≤ B := by exact_mod_cast hAB
  have hA_mem : (A : ℝ) ∈ Set.Icc (A : ℝ) B := ⟨le_rfl, hABreal⟩
  have hB_mem : (B : ℝ) ∈ Set.Icc (A : ℝ) B := ⟨hABreal, le_rfl⟩
  have hboundA : |oscKernel tau A * thetaError A| ≤ delta := by
    rw [abs_mul]
    calc
      |oscKernel tau A| * |thetaError A| ≤
          (A : ℝ)⁻¹ * (delta * A) :=
        mul_le_mul (abs_oscKernel_le_inv hAreal) (herror A hA_mem)
          (abs_nonneg _) (by positivity)
      _ = delta := by field_simp
  have hboundB : |oscKernel tau B * thetaError B| ≤ delta := by
    rw [abs_mul]
    calc
      |oscKernel tau B| * |thetaError B| ≤
          (B : ℝ)⁻¹ * (delta * B) :=
        mul_le_mul (abs_oscKernel_le_inv hBreal) (herror B hB_mem)
          (abs_nonneg _) (by positivity)
      _ = delta := by field_simp
  have hgInt : IntervalIntegrable
      (fun x : ℝ ↦ delta * (1 + |tau|) / x) volume (A : ℝ) B := by
    apply ContinuousOn.intervalIntegrable
    intro x hx
    apply ContinuousAt.continuousWithinAt
    have hx0 : x ≠ 0 := ne_of_gt
      (lt_of_lt_of_le (lt_min hAreal hBreal) hx.1)
    exact continuousAt_const.div continuousAt_id hx0
  have hpoint : ∀ x ∈ Set.Ioc (A : ℝ) B,
      |oscKernelDeriv tau x * thetaError x| ≤
        delta * (1 + |tau|) / x := by
    intro x hx
    have hxpos : 0 < x := hAreal.trans hx.1
    have hxIcc : x ∈ Set.Icc (A : ℝ) B := ⟨hx.1.le, hx.2⟩
    rw [abs_mul]
    calc
      |oscKernelDeriv tau x| * |thetaError x| ≤
          ((1 + |tau|) / x ^ 2) * (delta * x) :=
        mul_le_mul (abs_oscKernelDeriv_le hxpos) (herror x hxIcc)
          (abs_nonneg _) (by positivity)
      _ = delta * (1 + |tau|) / x := by field_simp
  have hinterr :
      |∫ x in (A : ℝ)..B, oscKernelDeriv tau x * thetaError x| ≤
        delta * (1 + |tau|) * Real.log ((B : ℝ) / A) := by
    have hnorm :
        ‖∫ x in (A : ℝ)..B, oscKernelDeriv tau x * thetaError x‖ ≤
          ∫ x in (A : ℝ)..B, delta * (1 + |tau|) / x :=
      intervalIntegral.norm_integral_le_of_norm_le
      (μ := volume) hABreal
      (Filter.Eventually.of_forall fun x ↦ by
        intro hx
        simpa only [Real.norm_eq_abs] using! hpoint x hx)
      hgInt
    simp only [div_eq_mul_inv] at hnorm
    rw [intervalIntegral.integral_const_mul,
      integral_inv_of_pos hAreal hBreal] at hnorm
    simpa [div_eq_mul_inv, mul_assoc] using! hnorm
  rw [weightedPrimeOscillation_abel_identity hA hAB tau]
  have hmain := abs_integral_oscKernel_le hAreal hBreal htau
  have htri :
      |(∫ x in (A : ℝ)..B, oscKernel tau x) +
          oscKernel tau B * thetaError B -
          oscKernel tau A * thetaError A -
          ∫ x in (A : ℝ)..B, oscKernelDeriv tau x * thetaError x| ≤
        |(∫ x in (A : ℝ)..B, oscKernel tau x)| +
          |oscKernel tau B * thetaError B| +
          |oscKernel tau A * thetaError A| +
          |∫ x in (A : ℝ)..B, oscKernelDeriv tau x * thetaError x| := by
    calc
      |(∫ x in (A : ℝ)..B, oscKernel tau x) +
          oscKernel tau B * thetaError B -
          oscKernel tau A * thetaError A -
          ∫ x in (A : ℝ)..B, oscKernelDeriv tau x * thetaError x| ≤
        |(∫ x in (A : ℝ)..B, oscKernel tau x) +
          oscKernel tau B * thetaError B -
          oscKernel tau A * thetaError A| +
          |∫ x in (A : ℝ)..B, oscKernelDeriv tau x * thetaError x| := abs_sub _ _
      _ ≤ (|(∫ x in (A : ℝ)..B, oscKernel tau x) +
          oscKernel tau B * thetaError B| +
          |oscKernel tau A * thetaError A|) +
          |∫ x in (A : ℝ)..B, oscKernelDeriv tau x * thetaError x| := by
        gcongr
        exact abs_sub _ _
      _ ≤ ((|(∫ x in (A : ℝ)..B, oscKernel tau x)| +
          |oscKernel tau B * thetaError B|) +
          |oscKernel tau A * thetaError A|) +
          |∫ x in (A : ℝ)..B, oscKernelDeriv tau x * thetaError x| := by
        gcongr
        exact abs_add_le _ _
      _ = _ := by ring
  exact htri.trans (by linarith)

noncomputable def blockWeightedCoeff (A : ℕ) (tau : ℝ) (n : ℕ) : ℝ :=
  if A < n then oscKernel tau n * primeLogCoeff n else 0

theorem sum_blockWeightedCoeff_Icc (A : ℕ) (tau : ℝ) (N : ℕ) :
    ∑ n ∈ Finset.Icc 0 N, blockWeightedCoeff A tau n =
      ∑ n ∈ Finset.Ioc A N, oscKernel tau n * primeLogCoeff n := by
  calc
    (∑ n ∈ Finset.Icc 0 N, blockWeightedCoeff A tau n) =
        ∑ n ∈ Finset.Ioc A N, blockWeightedCoeff A tau n := by
      symm
      apply Finset.sum_subset
      · intro n hn
        have hn' := Finset.mem_Ioc.mp hn
        exact Finset.mem_Icc.mpr ⟨Nat.zero_le n, hn'.2⟩
      · intro n hnIcc hnNot
        have hnIcc' := Finset.mem_Icc.mp hnIcc
        have hnle : n ≤ A := by
          by_contra h
          exact hnNot (Finset.mem_Ioc.mpr ⟨Nat.lt_of_not_ge h, hnIcc'.2⟩)
        simp [blockWeightedCoeff, Nat.not_lt.mpr hnle]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro n hn
      have hn' := Finset.mem_Ioc.mp hn
      simp [blockWeightedCoeff, hn'.1]

theorem invLog_mul_blockWeightedCoeff_sum_eq_primeOscillation
    {A B : ℕ} (tau : ℝ) :
    (∑ n ∈ Finset.Ioc A B,
        (Real.log (n : ℝ))⁻¹ * blockWeightedCoeff A tau n) =
      ∑ n ∈ (Finset.Ioc A B).filter Nat.Prime, oscKernel tau n := by
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n hn
  have hn' := Finset.mem_Ioc.mp hn
  rw [blockWeightedCoeff, if_pos hn'.1, primeLogCoeff]
  by_cases hp : n.Prime
  · simp only [hp, if_true]
    have hlog : Real.log (n : ℝ) ≠ 0 := ne_of_gt <|
      Real.log_pos (by exact_mod_cast hp.one_lt)
    field_simp [hlog]
  · simp [hp]

noncomputable def invLog (x : ℝ) : ℝ := (Real.log x)⁻¹

noncomputable def invLogDeriv (x : ℝ) : ℝ :=
  -x⁻¹ / Real.log x ^ 2

theorem hasDerivAt_invLog {x : ℝ} (hx : x ≠ 0) (hlog : Real.log x ≠ 0) :
    HasDerivAt invLog (invLogDeriv x) x := by
  unfold invLog invLogDeriv
  exact (Real.hasDerivAt_log hx).inv hlog

theorem deriv_invLog {x : ℝ} (hx : x ≠ 0) (hlog : Real.log x ≠ 0) :
    deriv invLog x = invLogDeriv x :=
  (hasDerivAt_invLog hx hlog).deriv

theorem neg_invLogDeriv_eq {x : ℝ} (hx : 0 < x) :
    -invLogDeriv x = 1 / (x * Real.log x ^ 2) := by
  unfold invLogDeriv
  field_simp

theorem invLog_pos {x : ℝ} (hx : 1 < x) : 0 < invLog x := by
  unfold invLog
  exact inv_pos.mpr (Real.log_pos hx)

set_option maxHeartbeats 800000 in
-- The second Abel summation expands several integrability witnesses.
theorem abs_primeOscillation_le_of_weightedPartial
    {A B : ℕ} (hA : 2 ≤ A) (hAB : A ≤ B) {tau K : ℝ}
    (hpartial : ∀ x ∈ Set.Icc (A : ℝ) B,
      |∑ n ∈ Finset.Ioc A ⌊x⌋₊,
          oscKernel tau n * primeLogCoeff n| ≤ K) :
    |∑ n ∈ (Finset.Ioc A B).filter Nat.Prime, oscKernel tau n| ≤
      K * invLog A := by
  have hAreal : (1 : ℝ) < A := by exact_mod_cast hA
  have hApos : (0 : ℝ) < A := zero_lt_one.trans hAreal
  have hBreal : (1 : ℝ) < B := hAreal.trans_le (by exact_mod_cast hAB)
  have hBpos : (0 : ℝ) < B := zero_lt_one.trans hBreal
  have hABreal : (A : ℝ) ≤ B := by exact_mod_cast hAB
  have hdiff : ∀ x ∈ Set.Icc (A : ℝ) B,
      DifferentiableAt ℝ invLog x := by
    intro x hx
    have hx1 : 1 < x := hAreal.trans_le hx.1
    exact (hasDerivAt_invLog (ne_of_gt (zero_lt_one.trans hx1))
      (ne_of_gt (Real.log_pos hx1))).differentiableAt
  have hderivEq : ∀ x ∈ Set.Icc (A : ℝ) B,
      deriv invLog x = invLogDeriv x := by
    intro x hx
    have hx1 : 1 < x := hAreal.trans_le hx.1
    exact deriv_invLog (ne_of_gt (zero_lt_one.trans hx1))
      (ne_of_gt (Real.log_pos hx1))
  have hDcont : ContinuousOn invLogDeriv (Set.Icc (A : ℝ) B) := by
    intro x hx
    apply ContinuousAt.continuousWithinAt
    have hx1 : 1 < x := hAreal.trans_le hx.1
    have hx0 : x ≠ 0 := ne_of_gt (zero_lt_one.trans hx1)
    have hlog : Real.log x ≠ 0 := ne_of_gt (Real.log_pos hx1)
    unfold invLogDeriv
    exact (continuousAt_id.inv₀ hx0).neg.div
      ((Real.continuousAt_log hx0).pow 2) (pow_ne_zero 2 hlog)
  have hfint : IntegrableOn (deriv invLog) (Set.Icc (A : ℝ) B) :=
    hDcont.integrableOn_Icc.congr_fun
      (fun x hx ↦ (hderivEq x hx).symm) measurableSet_Icc
  have habel := sum_mul_eq_sub_sub_integral_mul'
    (blockWeightedCoeff A tau) hAB hdiff hfint
  simp_rw [sum_blockWeightedCoeff_Icc] at habel
  rw [← intervalIntegral.integral_of_le hABreal] at habel
  have hderivIntegral :
      (∫ x in (A : ℝ)..B, deriv invLog x *
          ∑ n ∈ Finset.Ioc A ⌊x⌋₊,
            oscKernel tau n * primeLogCoeff n) =
        ∫ x in (A : ℝ)..B, invLogDeriv x *
          ∑ n ∈ Finset.Ioc A ⌊x⌋₊,
            oscKernel tau n * primeLogCoeff n := by
    apply intervalIntegral.integral_congr
    intro x hx
    change deriv invLog x * _ = invLogDeriv x * _
    rw [hderivEq x (by simpa [Set.uIcc_of_le hABreal] using! hx)]
  rw [hderivIntegral] at habel
  have hQB :
      |∑ n ∈ Finset.Ioc A B, oscKernel tau n * primeLogCoeff n| ≤ K := by
    simpa using! hpartial (B : ℝ) ⟨hABreal, le_rfl⟩
  have hgInt : IntervalIntegrable
      (fun x : ℝ ↦ K / (x * Real.log x ^ 2)) volume (A : ℝ) B := by
    apply ContinuousOn.intervalIntegrable
    intro x hx
    apply ContinuousAt.continuousWithinAt
    have hx1 : 1 < x := lt_of_lt_of_le (lt_min hAreal hBreal) hx.1
    have hx0 : x ≠ 0 := ne_of_gt (zero_lt_one.trans hx1)
    have hlog : Real.log x ≠ 0 := ne_of_gt (Real.log_pos hx1)
    exact continuousAt_const.div
      (continuousAt_id.mul ((Real.continuousAt_log hx0).pow 2))
      (mul_ne_zero hx0 (pow_ne_zero 2 hlog))
  have hpoint : ∀ x ∈ Set.Ioc (A : ℝ) B,
      |invLogDeriv x *
          ∑ n ∈ Finset.Ioc A ⌊x⌋₊,
            oscKernel tau n * primeLogCoeff n| ≤
        K / (x * Real.log x ^ 2) := by
    intro x hx
    have hx1 : 1 < x := hAreal.trans hx.1
    have hxpos : 0 < x := zero_lt_one.trans hx1
    have hxIcc : x ∈ Set.Icc (A : ℝ) B := ⟨hx.1.le, hx.2⟩
    have hQ := hpartial x hxIcc
    have hlog : Real.log x ≠ 0 := ne_of_gt (Real.log_pos hx1)
    have hdenpos : 0 < x * Real.log x ^ 2 :=
      mul_pos hxpos (sq_pos_of_ne_zero hlog)
    have hDneg : invLogDeriv x ≤ 0 := by
      rw [← neg_nonneg]
      rw [neg_invLogDeriv_eq hxpos]
      positivity
    rw [abs_mul, abs_of_nonpos hDneg, neg_invLogDeriv_eq hxpos]
    calc
      (1 / (x * Real.log x ^ 2)) *
          |∑ n ∈ Finset.Ioc A ⌊x⌋₊,
            oscKernel tau n * primeLogCoeff n| ≤
          (1 / (x * Real.log x ^ 2)) * K := by
        gcongr
      _ = K / (x * Real.log x ^ 2) := by ring
  have hnegDInt : IntervalIntegrable (fun x : ℝ ↦ -invLogDeriv x)
      volume (A : ℝ) B := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hABreal]
    exact hDcont.neg.integrableOn_Icc
  have hnegDeval :
      (∫ x in (A : ℝ)..B, -invLogDeriv x) = invLog A - invLog B := by
    have hfund := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (a := (A : ℝ)) (b := (B : ℝ))
      (f := fun x ↦ -invLog x) (f' := fun x ↦ -invLogDeriv x)
      (fun x hx ↦ by
        have hx1 : 1 < x := lt_of_lt_of_le (lt_min hAreal hBreal) hx.1
        exact (hasDerivAt_invLog (ne_of_gt (zero_lt_one.trans hx1))
          (ne_of_gt (Real.log_pos hx1))).neg)
      hnegDInt
    simpa [sub_eq_add_neg, add_comm] using! hfund
  have hgeval :
      (∫ x in (A : ℝ)..B, K / (x * Real.log x ^ 2)) =
        K * (invLog A - invLog B) := by
    calc
      (∫ x in (A : ℝ)..B, K / (x * Real.log x ^ 2)) =
          ∫ x in (A : ℝ)..B, K * (-invLogDeriv x) := by
        apply intervalIntegral.integral_congr
        intro x hx
        have hxpos : 0 < x := zero_lt_one.trans <|
          lt_of_lt_of_le (lt_min hAreal hBreal) hx.1
        change K / (x * Real.log x ^ 2) = K * (-invLogDeriv x)
        rw [neg_invLogDeriv_eq hxpos]
        ring
      _ = K * (∫ x in (A : ℝ)..B, -invLogDeriv x) := by
        rw [intervalIntegral.integral_const_mul]
      _ = _ := by rw [hnegDeval]
  have hinterr :
      |∫ x in (A : ℝ)..B, invLogDeriv x *
          ∑ n ∈ Finset.Ioc A ⌊x⌋₊,
            oscKernel tau n * primeLogCoeff n| ≤
        K * (invLog A - invLog B) := by
    have hnorm :
        ‖∫ x in (A : ℝ)..B, invLogDeriv x *
            ∑ n ∈ Finset.Ioc A ⌊x⌋₊,
              oscKernel tau n * primeLogCoeff n‖ ≤
          ∫ x in (A : ℝ)..B, K / (x * Real.log x ^ 2) :=
      intervalIntegral.norm_integral_le_of_norm_le
        (μ := volume) hABreal
        (Filter.Eventually.of_forall fun x ↦ by
          intro hx
          simpa only [Real.norm_eq_abs] using! hpoint x hx)
        hgInt
    rw [Real.norm_eq_abs, hgeval] at hnorm
    exact hnorm
  rw [← invLog_mul_blockWeightedCoeff_sum_eq_primeOscillation
    tau]
  change |∑ n ∈ Finset.Ioc A B,
    invLog n * blockWeightedCoeff A tau n| ≤ K * invLog A
  rw [habel]
  simp only [Finset.Ioc_self, Finset.sum_empty, mul_zero, sub_zero]
  have hlogB : 0 < invLog B := invLog_pos hBreal
  calc
    |invLog B *
        ∑ n ∈ Finset.Ioc A B, oscKernel tau n * primeLogCoeff n -
        ∫ x in (A : ℝ)..B, invLogDeriv x *
          ∑ n ∈ Finset.Ioc A ⌊x⌋₊,
            oscKernel tau n * primeLogCoeff n| ≤
        |invLog B *
          ∑ n ∈ Finset.Ioc A B, oscKernel tau n * primeLogCoeff n| +
          |∫ x in (A : ℝ)..B, invLogDeriv x *
            ∑ n ∈ Finset.Ioc A ⌊x⌋₊,
              oscKernel tau n * primeLogCoeff n| := abs_sub _ _
    _ ≤ invLog B * K + K * (invLog A - invLog B) := by
      gcongr
      rw [abs_mul, abs_of_pos hlogB]
      gcongr
    _ = K * invLog A := by ring

set_option maxHeartbeats 800000 in
-- Combining the two Abel estimates requires the expanded endpoint bounds.
theorem abs_primeOscillation_le_of_thetaError
    {A B : ℕ} (hA : 2 ≤ A) (hAB : A ≤ B) {tau delta : ℝ}
    (htau : tau ≠ 0) (hdelta : 0 ≤ delta)
    (herror : ∀ x ∈ Set.Icc (A : ℝ) B,
      |thetaError x| ≤ delta * x) :
    |∑ n ∈ (Finset.Ioc A B).filter Nat.Prime, oscKernel tau n| ≤
      (2 / |tau| + 2 * delta +
        delta * (1 + |tau|) * Real.log ((B : ℝ) / A)) * invLog A := by
  let K : ℝ := 2 / |tau| + 2 * delta +
    delta * (1 + |tau|) * Real.log ((B : ℝ) / A)
  have hApos : (0 : ℝ) < A := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_two hA)
  have hBpos : (0 : ℝ) < B := hApos.trans_le (by exact_mod_cast hAB)
  have hratioOne : (1 : ℝ) ≤ (B : ℝ) / A := by
    rw [le_div_iff₀ hApos]
    simpa using! (show (A : ℝ) ≤ B by exact_mod_cast hAB)
  have hlognonneg : 0 ≤ Real.log ((B : ℝ) / A) :=
    Real.log_nonneg hratioOne
  apply abs_primeOscillation_le_of_weightedPartial hA hAB
  intro x hx
  have hxnonneg : (0 : ℝ) ≤ x := hApos.le.trans hx.1
  have hAN : A ≤ ⌊x⌋₊ := Nat.le_floor hx.1
  have hNB : ⌊x⌋₊ ≤ B := by
    simpa using! Nat.floor_le_floor hx.2
  have herrorN : ∀ y ∈ Set.Icc (A : ℝ) (⌊x⌋₊ : ℝ),
      |thetaError y| ≤ delta * y := by
    intro y hy
    apply herror y
    exact ⟨hy.1, hy.2.trans (by exact_mod_cast hNB)⟩
  have hweighted := abs_weightedPrimeOscillation_le_of_thetaError
    (show 1 ≤ A by omega) hAN htau herrorN
  apply hweighted.trans
  have hratio : ((⌊x⌋₊ : ℝ) / A) ≤ (B : ℝ) / A := by
    exact div_le_div_of_nonneg_right (by exact_mod_cast hNB) hApos.le
  have hleftpos : 0 < ((⌊x⌋₊ : ℝ) / A) := by
    apply div_pos _ hApos
    exact hApos.trans_le (by exact_mod_cast hAN)
  have hrightpos : 0 < ((B : ℝ) / A) := by positivity
  have hlog : Real.log ((⌊x⌋₊ : ℝ) / A) ≤
      Real.log ((B : ℝ) / A) :=
    Real.strictMonoOn_log.monotoneOn hleftpos hrightpos hratio
  gcongr

theorem exists_mediumThetaError :
    ∃ c > 0, ∃ C > 0, ∃ X₀ : ℝ, 2 ≤ X₀ ∧
      ∀ x ≥ X₀,
        |thetaError x| ≤
          (C * Real.exp (-c * Real.log x ^ ((1 : ℝ) / 10)) +
            2 * Real.log x / Real.sqrt x) * x := by
  obtain ⟨c, hc, hpnt⟩ := MediumPNT
  obtain ⟨C, hC, hbig⟩ := hpnt.exists_pos
  obtain ⟨X, hX⟩ := Filter.eventually_atTop.1 hbig.bound
  refine ⟨c, hc, C, hC, max X 2, le_max_right _ _, ?_⟩
  intro x hx
  have hxX : X ≤ x := (le_max_left X 2).trans hx
  have hx2 : 2 ≤ x := (le_max_right X 2).trans hx
  have hxpos : 0 < x := zero_lt_two.trans_le hx2
  have hpsiRaw := hX x hxX
  have hpsi : |Chebyshev.psi x - x| ≤
      C * (x * Real.exp (-c * Real.log x ^ ((1 : ℝ) / 10))) := by
    simpa [Pi.sub_apply, Real.norm_eq_abs, abs_of_pos hxpos,
      abs_of_pos (Real.exp_pos _)] using! hpsiRaw
  have hpsitheta := Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log
    (show 1 ≤ x by linarith)
  have htri : |thetaError x| ≤
      |Chebyshev.psi x - x| + |Chebyshev.psi x - Chebyshev.theta x| := by
    unfold thetaError
    have := abs_add_le (Chebyshev.theta x - Chebyshev.psi x)
      (Chebyshev.psi x - x)
    rw [abs_sub_comm (Chebyshev.theta x) (Chebyshev.psi x)] at this
    convert! this using 1 <;> ring_nf
  have hsqrtpos : 0 < Real.sqrt x := Real.sqrt_pos.2 hxpos
  calc
    |thetaError x| ≤
        |Chebyshev.psi x - x| + |Chebyshev.psi x - Chebyshev.theta x| := htri
    _ ≤ C * (x * Real.exp (-c * Real.log x ^ ((1 : ℝ) / 10))) +
        2 * Real.sqrt x * Real.log x := add_le_add hpsi hpsitheta
    _ = (C * Real.exp (-c * Real.log x ^ ((1 : ℝ) / 10)) +
          2 * Real.log x / Real.sqrt x) * x := by
      field_simp [hsqrtpos.ne']
      ring_nf
      rw [Real.sq_sqrt hxpos.le]

noncomputable def mediumThetaBlockDelta (c C : ℝ) (A B : ℕ) : ℝ :=
  C * Real.exp (-c * Real.log (A : ℝ) ^ ((1 : ℝ) / 10)) +
    2 * Real.log (B : ℝ) / Real.sqrt A

set_option maxHeartbeats 800000 in
-- Monotonicity of the effective theta error generates a sizeable term.
theorem thetaError_le_mediumThetaBlockDelta
    {c C X₀ : ℝ} (hc : 0 < c) (hC : 0 ≤ C)
    (htheta : ∀ x ≥ X₀,
      |thetaError x| ≤
        (C * Real.exp (-c * Real.log x ^ ((1 : ℝ) / 10)) +
          2 * Real.log x / Real.sqrt x) * x)
    {A B : ℕ} (hA : 2 ≤ A) (hAB : A ≤ B) (hX₀ : X₀ ≤ A)
    {x : ℝ} (hx : x ∈ Set.Icc (A : ℝ) B) :
    |thetaError x| ≤ mediumThetaBlockDelta c C A B * x := by
  have hApos : (0 : ℝ) < A := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_two hA)
  have hAone : (1 : ℝ) < A := by exact_mod_cast hA
  have hBpos : (0 : ℝ) < B := hApos.trans_le (by exact_mod_cast hAB)
  have hxpos : 0 < x := hApos.trans_le hx.1
  have hxone : 1 < x := hAone.trans_le hx.1
  have hthetaX := htheta x (hX₀.trans hx.1)
  apply hthetaX.trans
  apply mul_le_mul_of_nonneg_right _ hxpos.le
  have hlogAx : Real.log (A : ℝ) ≤ Real.log x :=
    Real.strictMonoOn_log.monotoneOn hApos hxpos hx.1
  have hlogA0 : 0 ≤ Real.log (A : ℝ) := Real.log_nonneg hAone.le
  have hrpow : Real.log (A : ℝ) ^ ((1 : ℝ) / 10) ≤
      Real.log x ^ ((1 : ℝ) / 10) :=
    Real.rpow_le_rpow hlogA0 hlogAx (by norm_num)
  have hexp : Real.exp (-c * Real.log x ^ ((1 : ℝ) / 10)) ≤
      Real.exp (-c * Real.log (A : ℝ) ^ ((1 : ℝ) / 10)) := by
    rw [Real.exp_le_exp]
    exact mul_le_mul_of_nonpos_left hrpow (neg_nonpos.mpr hc.le)
  have hlogxB : Real.log x ≤ Real.log (B : ℝ) :=
    Real.strictMonoOn_log.monotoneOn hxpos hBpos hx.2
  have hsqrtApos : 0 < Real.sqrt (A : ℝ) := Real.sqrt_pos.2 hApos
  have hsqrtAx : Real.sqrt (A : ℝ) ≤ Real.sqrt x := Real.sqrt_le_sqrt hx.1
  have hlogB0 : 0 ≤ Real.log (B : ℝ) := by
    exact Real.log_nonneg (by exact_mod_cast (show 1 ≤ B by omega))
  have hdiv : Real.log x / Real.sqrt x ≤
      Real.log (B : ℝ) / Real.sqrt A :=
    div_le_div₀ hlogB0 hlogxB hsqrtApos hsqrtAx
  unfold mediumThetaBlockDelta
  have hdiv2 := mul_le_mul_of_nonneg_left hdiv (by norm_num : (0 : ℝ) ≤ 2)
  exact add_le_add (mul_le_mul_of_nonneg_left hexp hC)
    (by simpa [mul_div_assoc] using! hdiv2)

theorem exists_mediumPNT_primeOscillation_bound :
    ∃ c > 0, ∃ C > 0, ∃ X₀ : ℝ, 2 ≤ X₀ ∧
      ∀ (A B : ℕ), X₀ ≤ A → 2 ≤ A → A ≤ B →
        ∀ tau : ℝ, tau ≠ 0 →
          |∑ p ∈ (Finset.Ioc A B).filter Nat.Prime,
              Real.cos (tau * Real.log (p : ℝ)) / p| ≤
            (2 / |tau| + 2 * mediumThetaBlockDelta c C A B +
              mediumThetaBlockDelta c C A B * (1 + |tau|) *
                Real.log ((B : ℝ) / A)) * invLog A := by
  obtain ⟨c, hc, C, hC, X₀, hX₀two, htheta⟩ := exists_mediumThetaError
  refine ⟨c, hc, C, hC, X₀, hX₀two, ?_⟩
  intro A B hX₀A hA hAB tau htau
  have hdelta : 0 ≤ mediumThetaBlockDelta c C A B := by
    unfold mediumThetaBlockDelta
    have hApos : (0 : ℝ) < A := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_two hA)
    have hlogB : 0 ≤ Real.log (B : ℝ) :=
      Real.log_nonneg (by exact_mod_cast (show 1 ≤ B by omega))
    have hsqrtA : 0 < Real.sqrt (A : ℝ) := Real.sqrt_pos.2 hApos
    positivity
  have h := abs_primeOscillation_le_of_thetaError
    hA hAB htau hdelta
    (fun x hx ↦ thetaError_le_mediumThetaBlockDelta
      hc hC.le htheta hA hAB hX₀A hx)
  simpa only [oscKernel] using! h

end Problem520
end Erdos
