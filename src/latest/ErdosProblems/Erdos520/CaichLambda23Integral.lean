import ErdosProblems.Erdos520.CaichLambda23Moments
import ErdosProblems.Erdos520.CaichAuxiliaryAssembly
import ErdosProblems.Erdos520.MinkowskiIntegral
import ErdosProblems.Erdos520.OrthogonalMaximal
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open Filter Finset MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal NNReal Topology

namespace Erdos
namespace Problem520

/-!
# Outer integral and finite-test assembly for `lambda^(2)` and `lambda^(3)`

This file performs the measure-theoretic part of Caich's auxiliary estimate.
The fixed-cutoff fourth moments come from `CaichLambda23Moments`; integral
Minkowski (equivalently, the Cauchy--Schwarz step used in the paper) moves the
outer cutoff integral through the `L²(Omega)` norm.  The final section gives
the exact Markov/finite-union/summability wrapper for all test points and all
prime blocks.
-/

/-! ## Kernels and their fixed-parameter moments -/

/-- The nonnegative largest-prime running-maximum kernel used by
`lambda^(2)`. -/
noncomputable def caichLambda2Kernel
    {Z : Type*} (height lower upper : Z → ℕ) (z : Z)
    (omega : Omega) : ℝ :=
  finiteRunningMax
    (fun k omega ↦
      |caichLambda2ConcretePath (height z) (lower z) (upper z) k omega| ^ 2)
    (upper z) omega

/-- The terminal nonnegative kernel used by `lambda^(3)`. -/
noncomputable def caichLambda3Kernel
    {Z : Type*} (height lower upper : Z → ℕ) (z : Z)
    (omega : Omega) : ℝ :=
  |caichLambda2Terminal (height z) (lower z) (upper z) omega| ^ 2

theorem caichLambda2Kernel_nonneg
    {Z : Type*} (height lower upper : Z → ℕ) (z : Z) (omega : Omega) :
    0 ≤ caichLambda2Kernel height lower upper z omega := by
  unfold caichLambda2Kernel finiteRunningMax
  have hzero : 0 ∈ Finset.range (upper z + 1) := by simp
  exact (sq_nonneg
    |caichLambda2ConcretePath (height z) (lower z) (upper z) 0 omega|).trans
      (Finset.le_sup'
        (fun k ↦
          |caichLambda2ConcretePath (height z) (lower z) (upper z) k omega| ^ 2)
        hzero)

theorem caichLambda3Kernel_nonneg
    {Z : Type*} (height lower upper : Z → ℕ) (z : Z) (omega : Omega) :
    0 ≤ caichLambda3Kernel height lower upper z omega := by
  exact sq_nonneg _

/-- The deterministic root-moment budget common to both kernels. -/
noncomputable def caichLambdaTerminalRootBudget
    {Z : Type*} (height lower upper : Z → ℕ) (z : Z) : ℝ :=
  3 * (height z : ℝ) * (2 * Real.log (height z : ℝ)) ^ 2 *
    freshReciprocalSum (lower z) (upper z)

theorem caichLambdaTerminalRootBudget_nonneg
    {Z : Type*} (height lower upper : Z → ℕ) (z : Z) :
    0 ≤ caichLambdaTerminalRootBudget height lower upper z := by
  unfold caichLambdaTerminalRootBudget freshReciprocalSum
  exact mul_nonneg
    (mul_nonneg (mul_nonneg (by positivity) (by positivity)) (sq_nonneg _))
    (Finset.sum_nonneg fun p hp ↦ inv_nonneg.mpr (by positivity))

/-- A smooth sum contains at most `height` terms of absolute value at most
one.  Unlike the powerset bound, this estimate is uniform in the prime
cutoff. -/
theorem abs_Psi_le_height (omega : Omega) (height cutoff : ℕ) :
    |Ψ omega height cutoff| ≤ height := by
  unfold Ψ
  calc
    |∑ n ∈ Nat.smoothNumbersUpTo height (cutoff + 1), f omega n| ≤
        ∑ n ∈ Nat.smoothNumbersUpTo height (cutoff + 1), |f omega n| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _n ∈ Nat.smoothNumbersUpTo height (cutoff + 1), (1 : ℝ) := by
      gcongr with n hn
      exact abs_f_le_one omega n
    _ = (Nat.smoothNumbersUpTo height (cutoff + 1)).card := by simp
    _ ≤ height := by
      have hcard : (Nat.smoothNumbersUpTo height (cutoff + 1)).card ≤ height := by
        have hsub : Nat.smoothNumbersUpTo height (cutoff + 1) ⊆
            Finset.Ioc 0 height := by
          intro n hn
          rw [Nat.mem_smoothNumbersUpTo] at hn
          exact Finset.mem_Ioc.mpr
            ⟨Nat.pos_of_ne_zero (Nat.ne_zero_of_mem_smoothNumbers hn.2), hn.1⟩
        simpa using! Finset.card_le_card hsub
      exact_mod_cast hcard

/-- Uniform pointwise bound for the running-maximum kernel. -/
theorem caichLambda2Kernel_le_height
    {Z : Type*} (height lower upper : Z → ℕ) (z : Z) (omega : Omega) :
    caichLambda2Kernel height lower upper z omega ≤
      (2 * (height z : ℝ)) ^ 2 := by
  unfold caichLambda2Kernel finiteRunningMax
  apply Finset.sup'_le Finset.nonempty_range_add_one
  intro k hk
  apply pow_le_pow_left₀ (abs_nonneg _)
  calc
    |caichLambda2ConcretePath (height z) (lower z) (upper z) k omega| ≤
        |Ψ omega (height z) (min k (upper z))| +
          |Ψ omega (height z) (lower z)| := by
      unfold caichLambda2ConcretePath
      split_ifs
      · exact abs_sub _ _
      · simp only [abs_zero]
        positivity
    _ ≤ (height z : ℝ) + (height z : ℝ) :=
      add_le_add (abs_Psi_le_height omega _ _)
        (abs_Psi_le_height omega _ _)
    _ = 2 * (height z : ℝ) := by ring

/-- Uniform pointwise bound for the terminal kernel. -/
theorem caichLambda3Kernel_le_height
    {Z : Type*} (height lower upper : Z → ℕ) (z : Z) (omega : Omega) :
    caichLambda3Kernel height lower upper z omega ≤
      (2 * (height z : ℝ)) ^ 2 := by
  unfold caichLambda3Kernel caichLambda2Terminal
  apply pow_le_pow_left₀ (abs_nonneg _)
  calc
    |Ψ omega (height z) (upper z) - Ψ omega (height z) (lower z)| ≤
        |Ψ omega (height z) (upper z)| +
          |Ψ omega (height z) (lower z)| := abs_sub _ _
    _ ≤ (height z : ℝ) + (height z : ℝ) :=
      add_le_add (abs_Psi_le_height omega _ _)
        (abs_Psi_le_height omega _ _)
    _ = 2 * (height z : ℝ) := by ring

/-- Joint measurability of the largest-prime running-maximum kernel whenever
the three natural-valued parameter functions are measurable. -/
theorem measurable_caichLambda2Kernel
    {Z : Type*} [MeasurableSpace Z]
    {height lower upper : Z → ℕ}
    (hheight : Measurable height) (hlower : Measurable lower)
    (hupper : Measurable upper) :
    Measurable (fun x : Z × Omega ↦
      caichLambda2Kernel height lower upper x.1 x.2) := by
  let G : (((ℕ × ℕ) × ℕ) × Omega) → ℝ := fun x ↦
    finiteRunningMax
      (fun k omega ↦
        |caichLambda2ConcretePath x.1.1.1 x.1.1.2 x.1.2 k omega| ^ 2)
      x.1.2 x.2
  have hG : Measurable G := by
    apply measurable_from_prod_countable_right
    intro hαb
    dsimp only [G]
    unfold finiteRunningMax
    have hmeas : Measurable
      ((Finset.range (hαb.2 + 1)).sup' Finset.nonempty_range_add_one
        (fun k omega ↦
          |caichLambda2ConcretePath hαb.1.1 hαb.1.2 hαb.2 k omega| ^ 2)) := by
      apply Finset.measurable_sup' Finset.nonempty_range_add_one
      intro k hk
      unfold caichLambda2ConcretePath
      split_ifs
      · exact (((stronglyMeasurable_Ψ_filtration hαb.1.1
            (min k hαb.2)).mono (εFiltration.le _)).measurable.sub
          ((stronglyMeasurable_Ψ_filtration hαb.1.1 hαb.1.2).mono
            (εFiltration.le _)).measurable).abs.pow_const 2
      · exact measurable_const
    convert! hmeas using 1
    funext omega
    rw [Finset.sup'_apply]
  have hparams : Measurable fun z : Z ↦ ((height z, lower z), upper z) :=
    (hheight.prodMk hlower).prodMk hupper
  simpa only [G, caichLambda2Kernel] using!
    hG.comp ((hparams.comp measurable_fst).prodMk measurable_snd)

/-- Joint measurability of the terminal kernel. -/
theorem measurable_caichLambda3Kernel
    {Z : Type*} [MeasurableSpace Z]
    {height lower upper : Z → ℕ}
    (hheight : Measurable height) (hlower : Measurable lower)
    (hupper : Measurable upper) :
    Measurable (fun x : Z × Omega ↦
      caichLambda3Kernel height lower upper x.1 x.2) := by
  let G : (((ℕ × ℕ) × ℕ) × Omega) → ℝ := fun x ↦
    |Ψ x.2 x.1.1.1 x.1.2 - Ψ x.2 x.1.1.1 x.1.1.2| ^ 2
  have hG : Measurable G := by
    apply measurable_from_prod_countable_right
    intro hαb
    exact (((stronglyMeasurable_Ψ_filtration hαb.1.1 hαb.2).mono
        (εFiltration.le _)).measurable.sub
      ((stronglyMeasurable_Ψ_filtration hαb.1.1 hαb.1.2).mono
        (εFiltration.le _)).measurable).abs.pow_const 2
  have hparams : Measurable fun z : Z ↦ ((height z, lower z), upper z) :=
    (hheight.prodMk hlower).prodMk hupper
  simpa only [G, caichLambda3Kernel, caichLambda2Terminal] using!
    hG.comp ((hparams.comp measurable_fst).prodMk measurable_snd)

/-- Every fixed section of the running-maximum kernel has an integrable
square. -/
theorem integrable_sq_caichLambda2Kernel
    {Z : Type*} [MeasurableSpace Z]
    {height lower upper : Z → ℕ}
    (hheight : Measurable height) (hlower : Measurable lower)
    (hupper : Measurable upper) (z : Z) :
    Integrable (fun omega ↦ caichLambda2Kernel height lower upper z omega ^ 2) μ := by
  have hmeas : Measurable
      (fun omega ↦ caichLambda2Kernel height lower upper z omega) := by
    unfold caichLambda2Kernel finiteRunningMax
    have hsup : Measurable
        ((Finset.range (upper z + 1)).sup' Finset.nonempty_range_add_one
          (fun k omega ↦
            |caichLambda2ConcretePath (height z) (lower z) (upper z) k omega| ^ 2)) := by
      apply Finset.measurable_sup' Finset.nonempty_range_add_one
      intro k hk
      unfold caichLambda2ConcretePath
      split_ifs
      · exact (((stronglyMeasurable_Ψ_filtration (height z)
            (min k (upper z))).mono (εFiltration.le _)).measurable.sub
          ((stronglyMeasurable_Ψ_filtration (height z) (lower z)).mono
            (εFiltration.le _)).measurable).abs.pow_const 2
      · exact measurable_const
    convert! hsup using 1
    funext omega
    rw [Finset.sup'_apply]
  apply Integrable.of_bound (hmeas.pow_const 2).aestronglyMeasurable
    ((2 * (height z : ℝ)) ^ 4)
  exact ae_of_all μ fun omega ↦ by
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    calc
      caichLambda2Kernel height lower upper z omega ^ 2 ≤
          ((2 * (height z : ℝ)) ^ 2) ^ 2 :=
        pow_le_pow_left₀ (caichLambda2Kernel_nonneg _ _ _ _ _)
          (caichLambda2Kernel_le_height _ _ _ _ _) 2
      _ = (2 * (height z : ℝ)) ^ 4 := by ring

/-- Every fixed section of the terminal kernel has an integrable square. -/
theorem integrable_sq_caichLambda3Kernel
    {Z : Type*} [MeasurableSpace Z]
    {height lower upper : Z → ℕ}
    (hheight : Measurable height) (hlower : Measurable lower)
    (hupper : Measurable upper) (z : Z) :
    Integrable (fun omega ↦ caichLambda3Kernel height lower upper z omega ^ 2) μ := by
  have hmeas : Measurable
      (fun omega ↦ caichLambda3Kernel height lower upper z omega) := by
    unfold caichLambda3Kernel caichLambda2Terminal
    exact (((stronglyMeasurable_Ψ_filtration (height z) (upper z)).mono
        (εFiltration.le _)).measurable.sub
      ((stronglyMeasurable_Ψ_filtration (height z) (lower z)).mono
        (εFiltration.le _)).measurable).abs.pow_const 2
  apply Integrable.of_bound (hmeas.pow_const 2).aestronglyMeasurable
    ((2 * (height z : ℝ)) ^ 4)
  exact ae_of_all μ fun omega ↦ by
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    calc
      caichLambda3Kernel height lower upper z omega ^ 2 ≤
          ((2 * (height z : ℝ)) ^ 2) ^ 2 :=
        pow_le_pow_left₀ (caichLambda3Kernel_nonneg _ _ _ _ _)
          (caichLambda3Kernel_le_height _ _ _ _ _) 2
      _ = (2 * (height z : ℝ)) ^ 4 := by ring

/-- Fixed-parameter `L²(Omega)` budget for the running-maximum kernel. -/
theorem caichLambda2Kernel_secondMoment_sqrt_le
    {Z : Type*} (height lower upper : Z → ℕ) (z : Z)
    (hz : 3 ≤ height z) (hcut : lower z ≤ upper z) :
    (∫ omega, caichLambda2Kernel height lower upper z omega ^ 2 ∂μ) ^
        (1 / (2 : ℝ)) ≤
      2 * caichLambdaTerminalRootBudget height lower upper z := by
  have hraw := integral_caichLambda2Concrete_max_four_le_reciprocal
    (height z) hz hcut
  let I : ℝ := ∫ omega,
    caichLambda2Kernel height lower upper z omega ^ 2 ∂μ
  let B : ℝ := caichLambdaTerminalRootBudget height lower upper z
  have hI : 0 ≤ I := integral_nonneg fun omega => by positivity
  have hB : 0 ≤ B := by
    have hrecip : 0 ≤ freshReciprocalSum (lower z) (upper z) := by
      unfold freshReciprocalSum
      exact Finset.sum_nonneg fun p hp ↦ inv_nonneg.mpr (by positivity)
    unfold B caichLambdaTerminalRootBudget
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) (by positivity)) (sq_nonneg _))
      hrecip
  have hraw' : I ≤ 4 * B ^ 2 := by
    simpa only [I, B, caichLambda2Kernel] using! hraw
  rw [← Real.sqrt_eq_rpow]
  have hsqrt := Real.sqrt_le_sqrt hraw'
  calc
    √I ≤ √(4 * B ^ 2) := hsqrt
    _ = 2 * B := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← mul_pow,
        Real.sqrt_sq_eq_abs, abs_of_nonneg (mul_nonneg (by norm_num) hB)]

/-- Fixed-parameter `L²(Omega)` budget for the terminal kernel. -/
theorem caichLambda3Kernel_secondMoment_sqrt_le
    {Z : Type*} (height lower upper : Z → ℕ) (z : Z)
    (hz : 3 ≤ height z) (hcut : lower z ≤ upper z) :
    (∫ omega, caichLambda3Kernel height lower upper z omega ^ 2 ∂μ) ^
        (1 / (2 : ℝ)) ≤
      caichLambdaTerminalRootBudget height lower upper z := by
  simpa only [caichLambda3Kernel, caichLambdaTerminalRootBudget, ← pow_mul,
    show 2 * 2 = 4 by norm_num] using!
      caichLambda2Terminal_fourthMoment_sqrt_le_reciprocal
        (height z) hz hcut

/-- A pointwise reciprocal-prime estimate turns the terminal budget into a
linear function of the real cutoff.  This is the deterministic cancellation
with the inverse-square weight in the outer integral. -/
theorem caichLambdaTerminalRootBudget_le_linear
    {Z : Type*} (height lower upper : Z → ℕ) (realHeight : Z → ℝ)
    {L R : ℝ} (z : Z)
    (hheight : (height z : ℝ) ≤ realHeight z)
    (hrealHeight : 0 ≤ realHeight z)
    (hlog : Real.log (height z : ℝ) ≤ L)
    (hrecip : freshReciprocalSum (lower z) (upper z) ≤ R) :
    caichLambdaTerminalRootBudget height lower upper z ≤
      3 * realHeight z * (2 * L) ^ 2 * R := by
  have hlogSq : (2 * Real.log (height z : ℝ)) ^ 2 ≤ (2 * L) ^ 2 := by
    apply pow_le_pow_left₀
    · have hheightNonneg : 0 ≤ Real.log (height z : ℝ) := by
        by_cases hh : height z = 0
        · simp [hh]
        exact Real.log_nonneg (by
          exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hh))
      positivity
    · exact mul_le_mul_of_nonneg_left hlog (by norm_num)
  have hrecip0 : 0 ≤ freshReciprocalSum (lower z) (upper z) := by
    unfold freshReciprocalSum
    exact Finset.sum_nonneg fun p hp ↦ inv_nonneg.mpr (by positivity)
  have hrealFactor : 0 ≤ 3 * realHeight z :=
    mul_nonneg (by norm_num) hrealHeight
  unfold caichLambdaTerminalRootBudget
  calc
    3 * (height z : ℝ) * (2 * Real.log (height z : ℝ)) ^ 2 *
        freshReciprocalSum (lower z) (upper z) ≤
        3 * realHeight z * (2 * Real.log (height z : ℝ)) ^ 2 *
          freshReciprocalSum (lower z) (upper z) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hheight (by norm_num))
          (sq_nonneg _)) hrecip0
    _ ≤ 3 * realHeight z * (2 * L) ^ 2 *
          freshReciprocalSum (lower z) (upper z) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hlogSq hrealFactor) hrecip0
    _ ≤ 3 * realHeight z * (2 * L) ^ 2 * R := by
      exact mul_le_mul_of_nonneg_left hrecip
        (mul_nonneg hrealFactor (sq_nonneg _))

/-! ## The inverse-square normalization -/

/-- On a positive interval, a kernel bounded by `D*z` cancels one power of
the inverse-square weight and integrates to the exact logarithmic length. -/
theorem setIntegral_inv_sq_mul_le_mul_log_div
    {B : ℝ → ℝ} {a b D : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (hBint : IntegrableOn (fun z ↦ (z ^ 2)⁻¹ * B z) (Set.Ioc a b))
    (hlinear : ∀ z ∈ Set.Ioc a b, B z ≤ D * z) :
    (∫ z in Set.Ioc a b, (z ^ 2)⁻¹ * B z) ≤
      D * Real.log (b / a) := by
  have hb : 0 < b := ha.trans_le hab
  have hright : IntegrableOn (fun z : ℝ ↦ D * (1 / z)) (Set.Ioc a b) := by
    have hint : IntervalIntegrable (fun z : ℝ ↦ 1 / z) volume a b :=
      intervalIntegral.intervalIntegrable_one_div
        (fun z hz ↦ by
          rw [Set.mem_uIcc] at hz
          rcases hz with hz | hz <;> linarith)
        continuousOn_id
    have hset : IntegrableOn (fun z : ℝ ↦ 1 / z) (Set.Ioc a b) := by
      simpa only [intervalIntegrable_iff, hab, uIoc_of_le, true_and,
        integral_Icc_eq_integral_Ioc] using! hint.1
    exact hset.const_mul D
  calc
    (∫ z in Set.Ioc a b, (z ^ 2)⁻¹ * B z) ≤
        ∫ z in Set.Ioc a b, D * (1 / z) := by
      apply setIntegral_mono_on hBint hright measurableSet_Ioc
      intro z hz
      have hzpos : 0 < z := lt_trans ha hz.1
      calc
        (z ^ 2)⁻¹ * B z ≤ (z ^ 2)⁻¹ * (D * z) :=
          mul_le_mul_of_nonneg_left (hlinear z hz) (by positivity)
        _ = D * (1 / z) := by field_simp
    _ = D * (∫ z in Set.Ioc a b, 1 / z) := by
      rw [integral_const_mul]
    _ = D * Real.log (b / a) := by
      congr 1
      rw [← intervalIntegral.integral_of_le hab,
        integral_one_div_of_pos ha hb]

/-! ## Moving the outer integral through the probability norm -/

/-- A normalized nonnegative weighted integral.  Choosing
`w z = z⁻²` and restricting `nu` to Caich's cutoff interval gives exactly
the two auxiliary lambda integrals. -/
noncomputable def caichLambdaWeighted
    {Z : Type*} [MeasurableSpace Z] (nu : Measure Z)
    (c : ℝ) (w : Z → ℝ) (H : Z → Omega → ℝ)
    (omega : Omega) : ℝ :=
  c * ∫ z, w z * H z omega ∂nu

/-- Integral Minkowski at exponent two, in the exact normalized weighted
form used for both auxiliary lambda terms. -/
theorem caichLambdaWeighted_secondMoment_sqrt_le
    {Z : Type*} [MeasurableSpace Z] {nu : Measure Z} [SFinite nu]
    {c : ℝ} {w : Z → ℝ} {H : Z → Omega → ℝ}
    (hH : Measurable (fun x : Z × Omega ↦ H x.1 x.2))
    (hw : Measurable w)
    (hH_nonneg : ∀ z omega, 0 ≤ H z omega)
    (hw_nonneg : ∀ z, 0 ≤ w z)
    (hc : 0 ≤ c)
    (hinner : ∀ omega, Integrable (fun z ↦ w z * H z omega) nu)
    (houter : Integrable
      (fun omega ↦ (∫ z, w z * H z omega ∂nu) ^ 2) μ)
    (hslice : ∀ z, Integrable (fun omega ↦ H z omega ^ 2) μ)
    (hrhs : Integrable
      (fun z ↦ w z *
        (∫ omega, H z omega ^ 2 ∂μ) ^ (1 / (2 : ℝ))) nu) :
    (∫ omega, (caichLambdaWeighted nu c w H omega) ^ 2 ∂μ) ^
        (1 / (2 : ℝ)) ≤
      c * ∫ z, w z *
        (∫ omega, H z omega ^ 2 ∂μ) ^ (1 / (2 : ℝ)) ∂nu := by
  simpa only [caichLambdaWeighted] using!
    (IntegralMinkowski.integral_Lp_const_mul_weighted_integral_le
      hH hw hH_nonneg hw_nonneg (r := 2) (by norm_num) hc
      hinner houter hslice hrhs)

/-- Deterministic domination of the section norms may be inserted under the
outer integral without any loss. -/
theorem caichLambdaWeighted_secondMoment_sqrt_le_budget
    {Z : Type*} [MeasurableSpace Z] {nu : Measure Z} [SFinite nu]
    {c : ℝ} {w B : Z → ℝ} {H : Z → Omega → ℝ}
    (hH : Measurable (fun x : Z × Omega ↦ H x.1 x.2))
    (hw : Measurable w)
    (hH_nonneg : ∀ z omega, 0 ≤ H z omega)
    (hw_nonneg : ∀ z, 0 ≤ w z)
    (hc : 0 ≤ c)
    (hinner : ∀ omega, Integrable (fun z ↦ w z * H z omega) nu)
    (houter : Integrable
      (fun omega ↦ (∫ z, w z * H z omega ∂nu) ^ 2) μ)
    (hslice : ∀ z, Integrable (fun omega ↦ H z omega ^ 2) μ)
    (hrhs : Integrable
      (fun z ↦ w z *
        (∫ omega, H z omega ^ 2 ∂μ) ^ (1 / (2 : ℝ))) nu)
    (hBint : Integrable (fun z ↦ w z * B z) nu)
    (hsection : ∀ᵐ z ∂nu,
      (∫ omega, H z omega ^ 2 ∂μ) ^ (1 / (2 : ℝ)) ≤ B z) :
    (∫ omega, (caichLambdaWeighted nu c w H omega) ^ 2 ∂μ) ^
        (1 / (2 : ℝ)) ≤
      c * ∫ z, w z * B z ∂nu := by
  have hmain := caichLambdaWeighted_secondMoment_sqrt_le
    hH hw hH_nonneg hw_nonneg hc hinner houter hslice hrhs
  refine hmain.trans (mul_le_mul_of_nonneg_left ?_ hc)
  apply integral_mono_ae hrhs hBint
  filter_upwards [hsection] with z hz
  exact mul_le_mul_of_nonneg_left hz (hw_nonneg z)

/-- Direct outer-integral assembly for `lambda^(2)`.  All arithmetic content
is now the explicit reciprocal-prime budget in the right-hand integral. -/
theorem caichLambda2Weighted_secondMoment_sqrt_le
    {Z : Type*} [MeasurableSpace Z] {nu : Measure Z} [SFinite nu]
    (height lower upper : Z → ℕ)
    {c : ℝ} {w : Z → ℝ}
    (hH : Measurable (fun x : Z × Omega ↦
      caichLambda2Kernel height lower upper x.1 x.2))
    (hw : Measurable w) (hw_nonneg : ∀ z, 0 ≤ w z) (hc : 0 ≤ c)
    (hheight : ∀ z, 3 ≤ height z)
    (hcut : ∀ z, lower z ≤ upper z)
    (hinner : ∀ omega, Integrable
      (fun z ↦ w z * caichLambda2Kernel height lower upper z omega) nu)
    (houter : Integrable (fun omega ↦
      (∫ z, w z * caichLambda2Kernel height lower upper z omega ∂nu) ^ 2) μ)
    (hslice : ∀ z, Integrable (fun omega ↦
      caichLambda2Kernel height lower upper z omega ^ 2) μ)
    (hrhs : Integrable (fun z ↦ w z *
      (∫ omega, caichLambda2Kernel height lower upper z omega ^ 2 ∂μ) ^
        (1 / (2 : ℝ))) nu)
    (hBint : Integrable (fun z ↦ w z *
      (2 * caichLambdaTerminalRootBudget height lower upper z)) nu) :
    (∫ omega,
        (caichLambdaWeighted nu c w
          (caichLambda2Kernel height lower upper) omega) ^ 2 ∂μ) ^
        (1 / (2 : ℝ)) ≤
      c * ∫ z, w z *
        (2 * caichLambdaTerminalRootBudget height lower upper z) ∂nu := by
  exact caichLambdaWeighted_secondMoment_sqrt_le_budget
    hH hw (caichLambda2Kernel_nonneg height lower upper) hw_nonneg hc
    hinner houter hslice hrhs hBint
    (ae_of_all nu fun z ↦ caichLambda2Kernel_secondMoment_sqrt_le
      height lower upper z (hheight z) (hcut z))

/-- Direct outer-integral assembly for `lambda^(3)`. -/
theorem caichLambda3Weighted_secondMoment_sqrt_le
    {Z : Type*} [MeasurableSpace Z] {nu : Measure Z} [SFinite nu]
    (height lower upper : Z → ℕ)
    {c : ℝ} {w : Z → ℝ}
    (hH : Measurable (fun x : Z × Omega ↦
      caichLambda3Kernel height lower upper x.1 x.2))
    (hw : Measurable w) (hw_nonneg : ∀ z, 0 ≤ w z) (hc : 0 ≤ c)
    (hheight : ∀ z, 3 ≤ height z)
    (hcut : ∀ z, lower z ≤ upper z)
    (hinner : ∀ omega, Integrable
      (fun z ↦ w z * caichLambda3Kernel height lower upper z omega) nu)
    (houter : Integrable (fun omega ↦
      (∫ z, w z * caichLambda3Kernel height lower upper z omega ∂nu) ^ 2) μ)
    (hslice : ∀ z, Integrable (fun omega ↦
      caichLambda3Kernel height lower upper z omega ^ 2) μ)
    (hrhs : Integrable (fun z ↦ w z *
      (∫ omega, caichLambda3Kernel height lower upper z omega ^ 2 ∂μ) ^
        (1 / (2 : ℝ))) nu)
    (hBint : Integrable (fun z ↦ w z *
      caichLambdaTerminalRootBudget height lower upper z) nu) :
    (∫ omega,
        (caichLambdaWeighted nu c w
          (caichLambda3Kernel height lower upper) omega) ^ 2 ∂μ) ^
        (1 / (2 : ℝ)) ≤
      c * ∫ z, w z *
        caichLambdaTerminalRootBudget height lower upper z ∂nu := by
  exact caichLambdaWeighted_secondMoment_sqrt_le_budget
    hH hw (caichLambda3Kernel_nonneg height lower upper) hw_nonneg hc
    hinner houter hslice hrhs hBint
    (ae_of_all nu fun z ↦ caichLambda3Kernel_secondMoment_sqrt_le
      height lower upper z (hheight z) (hcut z))

/-! ## Markov, finite unions, and summability -/

/-- A nonnegative random variable with a finite second moment has the usual
strict-threshold Markov bound. -/
theorem measureReal_lt_le_secondMoment
    {Y : Omega → ℝ} {t M : ℝ}
    (hY : ∀ omega, 0 ≤ Y omega) (ht : 0 < t)
    (hYsq : Integrable (fun omega ↦ Y omega ^ 2) μ)
    (hmoment : (∫ omega, Y omega ^ 2 ∂μ) ≤ M) :
    μ.real {omega | t < Y omega} ≤ M / t ^ 2 := by
  have hmarkov := mul_meas_ge_le_integral_of_nonneg
    (μ := μ) (ae_of_all μ fun omega ↦ sq_nonneg (Y omega)) hYsq (t ^ 2)
  have hsubset : {omega | t < Y omega} ⊆ {omega | t ^ 2 ≤ Y omega ^ 2} := by
    intro omega homega
    exact le_of_lt ((sq_lt_sq₀ ht.le (hY omega)).mpr homega)
  have hmul : t ^ 2 * μ.real {omega | t < Y omega} ≤ M :=
    calc
      t ^ 2 * μ.real {omega | t < Y omega} ≤
          t ^ 2 * μ.real {omega | t ^ 2 ≤ Y omega ^ 2} :=
        mul_le_mul_of_nonneg_left (measureReal_mono hsubset) (sq_nonneg t)
      _ ≤ ∫ omega, Y omega ^ 2 ∂μ := hmarkov
      _ ≤ M := hmoment
  exact (le_div_iff₀ (sq_pos_of_pos ht)).2 (by
    simpa [mul_comm] using! hmul)

/-- Maximum over the finitely many prime blocks attached to one test point. -/
noncomputable def caichLambdaBlockMax
    (J : ℕ → ℕ) (value : ℕ → ℕ → ℕ → Omega → ℝ)
    (ell r : ℕ) (omega : Omega) : ℝ :=
  (Finset.range (J ell + 1)).sup' Finset.nonempty_range_add_one
    (fun j ↦ value ell r j omega)

/-- Exact second-moment union budget over test points and prime blocks. -/
noncomputable def caichLambdaFiniteUnionBudget
    (tests : ℕ → Finset ℕ) (J : ℕ → ℕ)
    (moment : ℕ → ℕ → ℕ → ℝ)
    (threshold : ℕ → ℝ) (ell : ℕ) : ℝ :=
  ∑ r ∈ tests ell, ∑ j ∈ Finset.range (J ell + 1),
    moment ell r j / threshold ell ^ 2

/-- Markov plus the honest finite union over every selected test point and
every prime block. -/
theorem measureReal_caichAuxiliaryComponentFailure_blockMax_le
    (tests : ℕ → Finset ℕ) (J : ℕ → ℕ)
    (value : ℕ → ℕ → ℕ → Omega → ℝ)
    (moment : ℕ → ℕ → ℕ → ℝ)
    (threshold : ℕ → ℝ)
    (hvalue : ∀ ell r j omega, 0 ≤ value ell r j omega)
    (hthreshold : ∀ ell, 0 < threshold ell)
    (hintegrable : ∀ ell r j,
      Integrable (fun omega ↦ value ell r j omega ^ 2) μ)
    (hmoment : ∀ ell r j,
      (∫ omega, value ell r j omega ^ 2 ∂μ) ≤ moment ell r j)
    (ell : ℕ) :
    μ.real (caichAuxiliaryComponentFailure tests
      (caichLambdaBlockMax J value) threshold ell) ≤
      caichLambdaFiniteUnionBudget tests J moment threshold ell := by
  let point : ℕ → ℕ → Set Omega := fun r j ↦
    {omega | threshold ell < value ell r j omega}
  have hfailure :
      caichAuxiliaryComponentFailure tests
          (caichLambdaBlockMax J value) threshold ell =
        ⋃ r ∈ tests ell, ⋃ j ∈ Finset.range (J ell + 1), point r j := by
    ext omega
    simp only [caichAuxiliaryComponentFailure,
      caichAuxiliaryComponentGoodAtScale, Set.mem_setOf_eq, not_forall,
      not_le, Set.mem_iUnion, exists_prop, point]
    constructor
    · rintro ⟨r, hr⟩
      obtain ⟨hrmem, hmax⟩ := hr
      rw [caichLambdaBlockMax, Finset.lt_sup'_iff] at hmax
      obtain ⟨j, hj, hjlt⟩ := hmax
      exact ⟨r, hrmem, j, hj, hjlt⟩
    · rintro ⟨r, hr, j, hj, hjlt⟩
      refine ⟨r, hr, ?_⟩
      exact hjlt.trans_le (Finset.le_sup'
        (fun q ↦ value ell r q omega) hj)
  rw [hfailure]
  calc
    μ.real (⋃ r ∈ tests ell,
        ⋃ j ∈ Finset.range (J ell + 1), point r j) ≤
        ∑ r ∈ tests ell,
          μ.real (⋃ j ∈ Finset.range (J ell + 1), point r j) :=
      measureReal_biUnion_finset_le _ _
    _ ≤ ∑ r ∈ tests ell,
        ∑ j ∈ Finset.range (J ell + 1), μ.real (point r j) := by
      gcongr with r hr
      exact measureReal_biUnion_finset_le _ _
    _ ≤ ∑ r ∈ tests ell,
        ∑ j ∈ Finset.range (J ell + 1),
          moment ell r j / threshold ell ^ 2 := by
      gcongr with r hr j hj
      exact measureReal_lt_le_secondMoment
        (hvalue ell r j) (hthreshold ell) (hintegrable ell r j)
          (hmoment ell r j)
    _ = caichLambdaFiniteUnionBudget tests J moment threshold ell := rfl

/-- Any summable deterministic finite-union budget makes the corresponding
auxiliary component failures summable. -/
theorem summable_measureReal_caichAuxiliaryComponentFailure_blockMax
    (tests : ℕ → Finset ℕ) (J : ℕ → ℕ)
    (value : ℕ → ℕ → ℕ → Omega → ℝ)
    (moment : ℕ → ℕ → ℕ → ℝ)
    (threshold : ℕ → ℝ)
    (hvalue : ∀ ell r j omega, 0 ≤ value ell r j omega)
    (hthreshold : ∀ ell, 0 < threshold ell)
    (hintegrable : ∀ ell r j,
      Integrable (fun omega ↦ value ell r j omega ^ 2) μ)
    (hmoment : ∀ ell r j,
      (∫ omega, value ell r j omega ^ 2 ∂μ) ≤ moment ell r j)
    (hbudget : Summable (caichLambdaFiniteUnionBudget
      tests J moment threshold)) :
    Summable fun ell ↦ μ.real (caichAuxiliaryComponentFailure tests
      (caichLambdaBlockMax J value) threshold ell) := by
  apply Summable.of_nonneg_of_le (fun _ ↦ measureReal_nonneg) _ hbudget
  intro ell
  exact measureReal_caichAuxiliaryComponentFailure_blockMax_le
    tests J value moment threshold hvalue hthreshold hintegrable hmoment ell

/-- A convenient fully explicit test-point summability criterion.  The
combined test/block entropy may consume half of `U`; if `U ≥ 2*ell`, the
remaining half is bounded by the summable geometric budget `exp(-ell)`. -/
theorem summable_caichLambdaFiniteUnionBudget_of_exp
    (tests : ℕ → Finset ℕ) (J : ℕ → ℕ)
    (moment : ℕ → ℕ → ℕ → ℝ)
    (threshold : ℕ → ℝ) (U : ℕ → ℝ)
    (hterm : ∀ ell r, r ∈ tests ell → ∀ j, j ∈ Finset.range (J ell + 1) →
      moment ell r j / threshold ell ^ 2 ≤ Real.exp (-U ell))
    (hterm_nonneg : ∀ ell r j, 0 ≤ moment ell r j / threshold ell ^ 2)
    (hentropy : ∀ ell,
      ((tests ell).card : ℝ) * (J ell + 1 : ℕ) ≤ Real.exp (U ell / 2))
    (hlinear : ∀ ell : ℕ, 2 * (ell : ℝ) ≤ U ell) :
    Summable (caichLambdaFiniteUnionBudget tests J moment threshold) := by
  apply Summable.of_nonneg_of_le
  · intro ell
    unfold caichLambdaFiniteUnionBudget
    exact Finset.sum_nonneg fun r hr ↦
      Finset.sum_nonneg fun j hj ↦ hterm_nonneg ell r j
  · intro ell
    unfold caichLambdaFiniteUnionBudget
    calc
      (∑ r ∈ tests ell, ∑ j ∈ Finset.range (J ell + 1),
          moment ell r j / threshold ell ^ 2) ≤
          ∑ _r ∈ tests ell, ∑ _j ∈ Finset.range (J ell + 1),
            Real.exp (-U ell) := by
        gcongr with r hr j hj
        exact hterm ell r hr j hj
      _ = ((tests ell).card : ℝ) * (J ell + 1 : ℕ) *
          Real.exp (-U ell) := by
        simp
        ring
      _ ≤ Real.exp (U ell / 2) * Real.exp (-U ell) :=
        mul_le_mul_of_nonneg_right (hentropy ell) (Real.exp_pos _).le
      _ = Real.exp (-U ell / 2) := by
        rw [← Real.exp_add]
        congr 1
        ring
      _ ≤ Real.exp (-(ell : ℝ)) := by
        apply Real.exp_le_exp.mpr
        linarith [hlinear ell]
  · exact Real.summable_exp_neg_nat

end Problem520
end Erdos
