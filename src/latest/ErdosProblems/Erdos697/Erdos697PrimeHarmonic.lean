/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import BoundedGaps.Maynard.PrimeMertens
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Reciprocal-prime Mertens estimate for Erdős Problem 697

The pinned analytic dependency proves Mertens' estimate with logarithmic
prime weights.  Finite Abel summation removes that logarithm here.  The
result is the bounded-error form

`∑_{p ≤ x} 1/p = log (log x) + O(1)`,

with all constants quantified and no additional assumptions.
-/

open MeasureTheory Set
open scoped BigOperators

namespace Erdos697.PrimeHarmonic

noncomputable section

/-- The reciprocal-prime sum up to a natural endpoint. -/
def sum (x : ℕ) : ℝ :=
  ∑ p ∈ Nat.primesLE x, (1 : ℝ) / p

/-- Abel summation converts the logarithmically weighted prime sum into the
ordinary reciprocal-prime sum. -/
theorem sum_eq_primeLogHarmonic_abel {x : ℕ} (hx : 2 ≤ x) :
    sum x =
      BoundedGaps.Maynard.primeLogHarmonicSum x / Real.log (x : ℝ) +
        ∫ t in (2 : ℝ)..(x : ℝ),
          BoundedGaps.Maynard.primeLogHarmonicSum ⌊t⌋₊ /
            (t * Real.log t ^ 2) := by
  classical
  let c : ℕ → ℝ := fun n =>
    if n.Prime then Real.log (n : ℝ) / (n : ℝ) else 0
  have hCumulative (m : ℕ) :
      (∑ n ∈ Finset.Icc 0 m, c n) =
        BoundedGaps.Maynard.primeLogHarmonicSum m := by
    unfold BoundedGaps.Maynard.primeLogHarmonicSum
    calc
      (∑ n ∈ Finset.Icc 0 m, c n) =
          ∑ n ∈ (Finset.Icc 0 m).filter Nat.Prime,
            Real.log (n : ℝ) / (n : ℝ) := by
              simp [c, Finset.sum_filter]
      _ = ∑ p ∈ Nat.primesLE m,
            Real.log (p : ℝ) / (p : ℝ) := by
              rw [Nat.primesLE_eq_filter_Icc_zero]
  have hWeighted :
      (∑ n ∈ Finset.Icc 0 x, (Real.log (n : ℝ))⁻¹ * c n) = sum x := by
    unfold sum
    calc
      (∑ n ∈ Finset.Icc 0 x, (Real.log (n : ℝ))⁻¹ * c n) =
          ∑ n ∈ (Finset.Icc 0 x).filter Nat.Prime,
            (1 : ℝ) / n := by
              rw [Finset.sum_filter]
              apply Finset.sum_congr rfl
              intro n hn
              by_cases hp : n.Prime
              · have hlog : Real.log (n : ℝ) ≠ 0 := hp.log_ne_zero
                simp [c, hp, hlog]
                field_simp
              · simp [c, hp]
      _ = ∑ p ∈ Nat.primesLE x, (1 : ℝ) / p := by
            rw [Nat.primesLE_eq_filter_Icc_zero]
  have hxReal : (2 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx
  have hDifferentiable : ∀ t ∈ Set.Icc (2 : ℝ) (x : ℝ),
      DifferentiableAt ℝ (fun u : ℝ => (Real.log u)⁻¹) t := by
    intro t ht
    exact Real.differentiableAt_inv_log (by linarith [ht.1])
      (by linarith [ht.1]) (by linarith [ht.1])
  have hDerivIntegrable : IntegrableOn
      (deriv fun t : ℝ => (Real.log t)⁻¹)
      (Set.Icc (2 : ℝ) (x : ℝ)) := by
    refine ContinuousOn.integrableOn_Icc fun t ht =>
      ContinuousWithinAt.congr ?_
        (fun _ _ => Real.deriv_inv_log_apply) Real.deriv_inv_log_apply
    have ht0 : t ≠ 0 := by linarith [ht.1]
    have hlog : Real.log t ^ 2 ≠ 0 := by
      refine pow_ne_zero 2 (Real.log_ne_zero_of_pos_of_ne_one ?_ ?_)
      · linarith [ht.1]
      · linarith [ht.1]
    exact ContinuousAt.continuousWithinAt (by fun_prop)
  have hAbel := sum_mul_eq_sub_integral_mul₁ c
    (f := fun t : ℝ => (Real.log t)⁻¹)
    (by norm_num [c]) (by norm_num [c]) (x : ℝ)
    hDifferentiable hDerivIntegrable
  rw [← intervalIntegral.integral_of_le hxReal] at hAbel
  have hIntegral :
      (∫ t in (2 : ℝ)..(x : ℝ),
          deriv (fun u : ℝ => (Real.log u)⁻¹) t *
            ∑ n ∈ Finset.Icc 0 ⌊t⌋₊, c n) =
        -(∫ t in (2 : ℝ)..(x : ℝ),
          BoundedGaps.Maynard.primeLogHarmonicSum ⌊t⌋₊ /
            (t * Real.log t ^ 2)) := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro t ht
    have htIcc : t ∈ Set.Icc (2 : ℝ) (x : ℝ) := by
      simpa [Set.uIcc_of_le hxReal] using ht
    change deriv (fun u : ℝ => (Real.log u)⁻¹) t *
        (∑ n ∈ Finset.Icc 0 ⌊t⌋₊, c n) =
      -(BoundedGaps.Maynard.primeLogHarmonicSum ⌊t⌋₊ /
        (t * Real.log t ^ 2))
    rw [hCumulative, Real.deriv_inv_log_apply]
    have ht0 : t ≠ 0 := by linarith [htIcc.1]
    have hlog : Real.log t ≠ 0 :=
      Real.log_ne_zero_of_pos_of_ne_one (by linarith [htIcc.1])
        (by linarith [htIcc.1])
    field_simp
  rw [Nat.floor_natCast, hWeighted, hCumulative, hIntegral] at hAbel
  calc
    sum x =
        (Real.log (x : ℝ))⁻¹ *
            BoundedGaps.Maynard.primeLogHarmonicSum x -
          -(∫ t in (2 : ℝ)..(x : ℝ),
            BoundedGaps.Maynard.primeLogHarmonicSum ⌊t⌋₊ /
              (t * Real.log t ^ 2)) := hAbel
    _ = BoundedGaps.Maynard.primeLogHarmonicSum x /
          Real.log (x : ℝ) +
        ∫ t in (2 : ℝ)..(x : ℝ),
          BoundedGaps.Maynard.primeLogHarmonicSum ⌊t⌋₊ /
            (t * Real.log t ^ 2) := by
      simp only [div_eq_mul_inv]
      ring

private theorem intervalIntegrable_primeLogHarmonic_div
    {x : ℕ} (hx : 2 ≤ x) :
    IntervalIntegrable
      (fun t : ℝ =>
        BoundedGaps.Maynard.primeLogHarmonicSum ⌊t⌋₊ /
          (t * Real.log t ^ 2))
      volume (2 : ℝ) (x : ℝ) := by
  classical
  let c : ℕ → ℝ := fun n =>
    if n.Prime then Real.log (n : ℝ) / (n : ℝ) else 0
  have hCumulative (m : ℕ) :
      (∑ n ∈ Finset.Icc 0 m, c n) =
        BoundedGaps.Maynard.primeLogHarmonicSum m := by
    unfold BoundedGaps.Maynard.primeLogHarmonicSum
    calc
      (∑ n ∈ Finset.Icc 0 m, c n) =
          ∑ n ∈ (Finset.Icc 0 m).filter Nat.Prime,
            Real.log (n : ℝ) / (n : ℝ) := by
              simp [c, Finset.sum_filter]
      _ = ∑ p ∈ Nat.primesLE m,
            Real.log (p : ℝ) / (p : ℝ) := by
              rw [Nat.primesLE_eq_filter_Icc_zero]
  have hxReal : (2 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx
  have hDerivIntegrable : IntegrableOn
      (deriv fun t : ℝ => (Real.log t)⁻¹)
      (Set.Icc (2 : ℝ) (x : ℝ)) := by
    refine ContinuousOn.integrableOn_Icc fun t ht =>
      ContinuousWithinAt.congr ?_
        (fun _ _ => Real.deriv_inv_log_apply) Real.deriv_inv_log_apply
    have ht0 : t ≠ 0 := by linarith [ht.1]
    have hlog : Real.log t ^ 2 ≠ 0 := by
      refine pow_ne_zero 2 (Real.log_ne_zero_of_pos_of_ne_one ?_ ?_)
      · linarith [ht.1]
      · linarith [ht.1]
    exact ContinuousAt.continuousWithinAt (by fun_prop)
  have hProductIntegrable : IntegrableOn
      (fun t : ℝ =>
        deriv (fun u : ℝ => (Real.log u)⁻¹) t *
          ∑ n ∈ Finset.Icc 0 ⌊t⌋₊, c n)
      (Set.Icc (2 : ℝ) (x : ℝ)) :=
    integrableOn_mul_sum_Icc c (a := (2 : ℝ)) (b := (x : ℝ))
      (m := 0) (by norm_num) hDerivIntegrable
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hxReal]
  apply hProductIntegrable.neg.congr_fun _ measurableSet_Icc
  intro t ht
  change -(deriv (fun u : ℝ => (Real.log u)⁻¹) t *
      (∑ n ∈ Finset.Icc 0 ⌊t⌋₊, c n)) = _
  rw [hCumulative, Real.deriv_inv_log_apply]
  have ht0 : t ≠ 0 := by linarith [ht.1]
  have hlog : Real.log t ≠ 0 :=
    Real.log_ne_zero_of_pos_of_ne_one (by linarith [ht.1])
      (by linarith [ht.1])
  field_simp

/-- Mertens' reciprocal-prime theorem with one uniform absolute constant. -/
theorem exists_uniform_abs_sum_sub_log_log :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℕ, 2 ≤ x →
      |sum x - Real.log (Real.log (x : ℝ))| ≤ C := by
  obtain ⟨C₀, hC₀⟩ :=
    BoundedGaps.Maynard.exists_uniform_abs_primeLogHarmonicSum_sub_log
  let C : ℝ :=
    |1 - Real.log (Real.log 2)| +
      C₀ / Real.log 2 + (C₀ + Real.log 2) / Real.log 2
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hC₀nonneg : 0 ≤ C₀ := by
    exact (abs_nonneg
      (BoundedGaps.Maynard.primeLogHarmonicSum 2 - Real.log 2)).trans
        (hC₀ 2)
  have hCnonneg : 0 ≤ C := by
    dsimp [C]
    positivity
  refine ⟨C, hCnonneg, ?_⟩
  intro x hx
  have hxReal : (2 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx
  have hxOne : (1 : ℝ) < x := by exact_mod_cast (show 1 < x by omega)
  have hlogx : 0 < Real.log (x : ℝ) := Real.log_pos hxOne
  rw [sum_eq_primeLogHarmonic_abel hx]
  let E : ℕ → ℝ := fun n =>
    BoundedGaps.Maynard.primeLogHarmonicSum n - Real.log n
  have hE (n : ℕ) : |E n| ≤ C₀ := hC₀ n
  let B : ℝ := C₀ + Real.log 2
  have hBnonneg : 0 ≤ B := by dsimp [B]; positivity
  have hsplitEndpoint :
      BoundedGaps.Maynard.primeLogHarmonicSum x /
          Real.log (x : ℝ) =
        1 + E x / Real.log (x : ℝ) := by
    dsimp [E]
    field_simp
    ring
  have hfloorLogError (t : ℝ) (ht : t ∈ Set.Icc (2 : ℝ) (x : ℝ)) :
      |Real.log (⌊t⌋₊ : ℝ) - Real.log t| ≤ Real.log 2 := by
    have hfloorNat : 2 ≤ ⌊t⌋₊ := Nat.le_floor ht.1
    have hfloorPos : (0 : ℝ) < ⌊t⌋₊ := by exact_mod_cast (by omega : 0 < ⌊t⌋₊)
    have htPos : 0 < t := by linarith [ht.1]
    have hfloorLe : (⌊t⌋₊ : ℝ) ≤ t := Nat.floor_le (by linarith [ht.1])
    have htLt : t < (⌊t⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one t
    have haddLe : (⌊t⌋₊ : ℝ) + 1 ≤ 2 * (⌊t⌋₊ : ℝ) := by
      exact_mod_cast (show ⌊t⌋₊ + 1 ≤ 2 * ⌊t⌋₊ by omega)
    have htLe : t ≤ 2 * (⌊t⌋₊ : ℝ) := (le_of_lt htLt).trans haddLe
    have hlogFloorLe : Real.log (⌊t⌋₊ : ℝ) ≤ Real.log t :=
      Real.strictMonoOn_log.monotoneOn
        (by simp only [Set.mem_Ioi]; exact hfloorPos)
        (by simp only [Set.mem_Ioi]; exact htPos) hfloorLe
    have htwoFloorPos : 0 < 2 * (⌊t⌋₊ : ℝ) := mul_pos (by norm_num) hfloorPos
    have hlogTLe : Real.log t ≤ Real.log (2 * (⌊t⌋₊ : ℝ)) :=
      Real.strictMonoOn_log.monotoneOn
        (by simp only [Set.mem_Ioi]; exact htPos)
        (by simp only [Set.mem_Ioi]; exact htwoFloorPos) htLe
    rw [abs_of_nonpos (sub_nonpos.mpr hlogFloorLe)]
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hfloorPos.ne'] at hlogTLe
    linarith
  have hFloorNumerator (t : ℝ) (ht : t ∈ Set.Icc (2 : ℝ) (x : ℝ)) :
      |BoundedGaps.Maynard.primeLogHarmonicSum ⌊t⌋₊ - Real.log t| ≤ B := by
    have htri := abs_sub_le
      (BoundedGaps.Maynard.primeLogHarmonicSum ⌊t⌋₊)
      (Real.log (⌊t⌋₊ : ℝ)) (Real.log t)
    dsimp [B]
    exact htri.trans (add_le_add (hC₀ ⌊t⌋₊) (hfloorLogError t ht))
  have hMainIntegrable : IntervalIntegrable
      (fun t : ℝ => Real.log t / (t * Real.log t ^ 2))
      volume (2 : ℝ) (x : ℝ) := by
    refine ContinuousOn.intervalIntegrable fun t ht =>
      ContinuousAt.continuousWithinAt ?_
    have htIcc : t ∈ Set.Icc (2 : ℝ) (x : ℝ) := by
      simpa [Set.uIcc_of_le hxReal] using ht
    have ht0 : t ≠ 0 := by linarith [htIcc.1]
    have hlog : Real.log t ≠ 0 :=
      Real.log_ne_zero_of_pos_of_ne_one (by linarith [htIcc.1])
        (by linarith [htIcc.1])
    have hden : t * Real.log t ^ 2 ≠ 0 :=
      mul_ne_zero ht0 (pow_ne_zero 2 hlog)
    fun_prop
  have hErrorIntegrable : IntervalIntegrable
      (fun t : ℝ =>
        (BoundedGaps.Maynard.primeLogHarmonicSum ⌊t⌋₊ -
          Real.log t) / (t * Real.log t ^ 2))
      volume (2 : ℝ) (x : ℝ) := by
    convert (intervalIntegrable_primeLogHarmonic_div hx).sub hMainIntegrable using 1
    ext t
    ring
  have hIntegralSplit :
      (∫ t in (2 : ℝ)..(x : ℝ),
        BoundedGaps.Maynard.primeLogHarmonicSum ⌊t⌋₊ /
          (t * Real.log t ^ 2)) =
      (∫ t in (2 : ℝ)..(x : ℝ),
        (Real.log t) / (t * Real.log t ^ 2)) +
      (∫ t in (2 : ℝ)..(x : ℝ),
        (BoundedGaps.Maynard.primeLogHarmonicSum ⌊t⌋₊ -
          Real.log t) / (t * Real.log t ^ 2)) := by
    rw [← intervalIntegral.integral_add hMainIntegrable hErrorIntegrable]
    · apply intervalIntegral.integral_congr
      intro t _
      ring
  have hMainIntegral :
      (∫ t in (2 : ℝ)..(x : ℝ),
        Real.log t / (t * Real.log t ^ 2)) =
      Real.log (Real.log (x : ℝ)) - Real.log (Real.log 2) := by
    calc
      (∫ t in (2 : ℝ)..(x : ℝ),
          Real.log t / (t * Real.log t ^ 2)) =
          ∫ t in (2 : ℝ)..(x : ℝ), t⁻¹ / Real.log t := by
            apply intervalIntegral.integral_congr
            intro t _
            by_cases ht0 : t = 0
            · simp [ht0]
            by_cases hlog : Real.log t = 0
            · simp [hlog]
            field_simp
      _ = Real.log (Real.log (x : ℝ)) - Real.log (Real.log 2) :=
        integral_inv_div_log (a := (2 : ℝ)) (b := (x : ℝ))
          (by norm_num) hxOne
  have hKernelIntegral :
      (∫ t in (2 : ℝ)..(x : ℝ), (t * Real.log t ^ 2)⁻¹) =
        (Real.log 2)⁻¹ - (Real.log (x : ℝ))⁻¹ := by
    calc
      (∫ t in (2 : ℝ)..(x : ℝ), (t * Real.log t ^ 2)⁻¹) =
          ∫ t in (2 : ℝ)..(x : ℝ), t⁻¹ / Real.log t ^ 2 := by
            apply intervalIntegral.integral_congr
            intro t _
            by_cases ht0 : t = 0
            · simp [ht0]
            by_cases hlog : Real.log t = 0
            · simp [hlog]
            field_simp
      _ = (Real.log 2)⁻¹ - (Real.log (x : ℝ))⁻¹ :=
        integral_inv_div_log_sq (a := (2 : ℝ)) (b := (x : ℝ))
          (by norm_num) hxOne
  have hKernelIntegrable : IntervalIntegrable
      (fun t : ℝ => (t * Real.log t ^ 2)⁻¹)
      volume (2 : ℝ) (x : ℝ) := by
    refine ContinuousOn.intervalIntegrable fun t ht =>
      ContinuousAt.continuousWithinAt ?_
    have htIcc : t ∈ Set.Icc (2 : ℝ) (x : ℝ) := by
      simpa [Set.uIcc_of_le hxReal] using ht
    have ht0 : t ≠ 0 := by linarith [htIcc.1]
    have hlog : Real.log t ≠ 0 :=
      Real.log_ne_zero_of_pos_of_ne_one (by linarith [htIcc.1])
        (by linarith [htIcc.1])
    have hden : t * Real.log t ^ 2 ≠ 0 :=
      mul_ne_zero ht0 (pow_ne_zero 2 hlog)
    fun_prop
  have hErrorIntegral :
      |∫ t in (2 : ℝ)..(x : ℝ),
        (BoundedGaps.Maynard.primeLogHarmonicSum ⌊t⌋₊ -
          Real.log t) / (t * Real.log t ^ 2)| ≤ B / Real.log 2 := by
    have hMajorant := hKernelIntegrable.const_mul B
    have hPointwise (t : ℝ) (ht : t ∈ Set.Icc (2 : ℝ) (x : ℝ)) :
        ‖(BoundedGaps.Maynard.primeLogHarmonicSum ⌊t⌋₊ -
            Real.log t) / (t * Real.log t ^ 2)‖ ≤
          B * (t * Real.log t ^ 2)⁻¹ := by
      have htOne : 1 < t := by linarith [ht.1]
      have hdenPos : 0 < t * Real.log t ^ 2 :=
        mul_pos (by linarith [ht.1]) (sq_pos_of_pos (Real.log_pos htOne))
      rw [Real.norm_eq_abs, abs_div, abs_of_pos hdenPos, div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right (hFloorNumerator t ht)
        (inv_nonneg.mpr hdenPos.le)
    calc
      |∫ t in (2 : ℝ)..(x : ℝ),
          (BoundedGaps.Maynard.primeLogHarmonicSum ⌊t⌋₊ -
            Real.log t) / (t * Real.log t ^ 2)| =
          ‖∫ t in (2 : ℝ)..(x : ℝ),
            (BoundedGaps.Maynard.primeLogHarmonicSum ⌊t⌋₊ -
              Real.log t) / (t * Real.log t ^ 2)‖ := by
            rw [Real.norm_eq_abs]
      _ ≤ ∫ t in (2 : ℝ)..(x : ℝ),
          ‖(BoundedGaps.Maynard.primeLogHarmonicSum ⌊t⌋₊ -
            Real.log t) / (t * Real.log t ^ 2)‖ :=
            intervalIntegral.norm_integral_le_integral_norm hxReal
      _ ≤ ∫ t in (2 : ℝ)..(x : ℝ),
          B * (t * Real.log t ^ 2)⁻¹ :=
            intervalIntegral.integral_mono_on hxReal hErrorIntegrable.norm
              hMajorant hPointwise
      _ = B * ((Real.log 2)⁻¹ - (Real.log (x : ℝ))⁻¹) := by
            rw [intervalIntegral.integral_const_mul, hKernelIntegral]
      _ ≤ B / Real.log 2 := by
            have hinvx : 0 ≤ (Real.log (x : ℝ))⁻¹ := inv_nonneg.mpr hlogx.le
            have := mul_le_mul_of_nonneg_left
              (sub_le_self (Real.log 2)⁻¹ hinvx) hBnonneg
            simpa [div_eq_mul_inv] using this
  have hEndpointError : |E x / Real.log (x : ℝ)| ≤ C₀ / Real.log 2 := by
    rw [abs_div, abs_of_pos hlogx]
    apply div_le_div₀ hC₀nonneg (hE x) hlog2
    exact Real.strictMonoOn_log.monotoneOn
      (by simp only [Set.mem_Ioi]; norm_num)
      (by simp only [Set.mem_Ioi]; positivity)
      (by exact_mod_cast hx)
  rw [hsplitEndpoint, hIntegralSplit, hMainIntegral]
  have hrewrite :
      1 + E x / Real.log (x : ℝ) +
          (Real.log (Real.log (x : ℝ)) - Real.log (Real.log 2) +
            (∫ t in (2 : ℝ)..(x : ℝ),
              (BoundedGaps.Maynard.primeLogHarmonicSum ⌊t⌋₊ -
                Real.log t) / (t * Real.log t ^ 2))) -
          Real.log (Real.log (x : ℝ)) =
        (1 - Real.log (Real.log 2)) +
          E x / Real.log (x : ℝ) +
          (∫ t in (2 : ℝ)..(x : ℝ),
            (BoundedGaps.Maynard.primeLogHarmonicSum ⌊t⌋₊ -
              Real.log t) / (t * Real.log t ^ 2)) := by ring
  rw [hrewrite]
  calc
    |(1 - Real.log (Real.log 2)) + E x / Real.log (x : ℝ) +
        (∫ t in (2 : ℝ)..(x : ℝ),
          (BoundedGaps.Maynard.primeLogHarmonicSum ⌊t⌋₊ -
            Real.log t) / (t * Real.log t ^ 2))| ≤
      |1 - Real.log (Real.log 2)| + |E x / Real.log (x : ℝ)| +
        |∫ t in (2 : ℝ)..(x : ℝ),
          (BoundedGaps.Maynard.primeLogHarmonicSum ⌊t⌋₊ -
            Real.log t) / (t * Real.log t ^ 2)| := by
        exact (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ |1 - Real.log (Real.log 2)| + C₀ / Real.log 2 +
        B / Real.log 2 := by linarith
    _ = C := by rfl

end

end Erdos697.PrimeHarmonic
