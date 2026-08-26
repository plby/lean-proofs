import ErdosProblems.Erdos520.CaichScheduledResidualMoments
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open Finset MeasureTheory Set
open scoped BigOperators Interval

namespace Erdos
namespace Problem520

/-!
# Deterministic bounds for the residual first moments

This file separates the analytic input needed for the aligned `L12` and
`L2` tails from their measure-theoretic wrappers.  A time-window reciprocal
mass is introduced so that a uniform smooth-number density estimate can be
multiplied directly by the effective-PNT short-window estimate.
-/

noncomputable def caichTimeWindowReciprocalMass
    (X : ℝ) (a b : ℕ) (t : ℝ) : ℝ := by
  classical
  exact ∑ p ∈ freshPrimes a b,
    if t / (1 + 1 / X) < (p : ℝ) ∧ (p : ℝ) ≤ t then
      (p : ℝ)⁻¹ else 0

theorem caichTimeWindowReciprocalMass_nonneg
    (X : ℝ) (a b : ℕ) (t : ℝ) :
    0 ≤ caichTimeWindowReciprocalMass X a b t := by
  classical
  unfold caichTimeWindowReciprocalMass
  exact Finset.sum_nonneg fun p hp ↦ by split_ifs <;> positivity

private theorem caich_time_short_window_iff
    {X t : ℝ} {x p : ℕ} (hX : X ≠ 0) (hx : 0 < x) (ht : t ≠ 0) :
    (t / (1 + 1 / X) < (p : ℝ) ∧ (p : ℝ) ≤ t) ↔
      caichShortWindowCondition X x p ((x : ℝ) / t) := by
  have hxR : (x : ℝ) ≠ 0 := by exact_mod_cast hx.ne'
  unfold caichShortWindowCondition
  have hleft :
      (x : ℝ) / (((x : ℝ) / t) * (1 + 1 / X)) =
        t / (1 + 1 / X) := by
    field_simp
  have hright : (x : ℝ) / ((x : ℝ) / t) = t := by
    field_simp
  rw [hleft, hright]

theorem caichTimeWindowReciprocalMass_eq_shortWindow
    {X t : ℝ} {x a b : ℕ} (hX : X ≠ 0) (hx : 0 < x) (ht : t ≠ 0) :
    caichTimeWindowReciprocalMass X a b t =
      caichShortWindowReciprocalMass X x a b ((x : ℝ) / t) := by
  classical
  unfold caichTimeWindowReciprocalMass caichShortWindowReciprocalMass
  apply Finset.sum_congr rfl
  intro p hp
  have heq := caich_time_short_window_iff (p := p) hX hx ht
  by_cases hwindow : t / (1 + 1 / X) < (p : ℝ) ∧ (p : ℝ) ≤ t
  · simp only [if_pos hwindow, if_pos (heq.mp hwindow)]
  · simp only [if_neg hwindow, if_neg (fun h ↦ hwindow (heq.mpr h))]

/-- If every smooth-number section in the active prime window has size at
most `Z`, the whole first-moment kernel is at most `Z` times the reciprocal
mass of that window. -/
theorem caichCoreTimeFirstMomentKernel_le_mul_timeWindowMass
    {X t Z : ℝ} {x a b : ℕ} (hZ : 0 ≤ Z)
    (hcard : ∀ p ∈ freshPrimes a b,
      t / (1 + 1 / X) < (p : ℝ) ∧ (p : ℝ) ≤ t →
        ((Nat.smoothNumbersUpTo
          (Nat.floor ((x : ℝ) / t)) p).card : ℝ) ≤ Z) :
    caichCoreTimeFirstMomentKernel X x a b t ≤
      Z * caichTimeWindowReciprocalMass X a b t := by
  classical
  unfold caichCoreTimeFirstMomentKernel caichTimeWindowReciprocalMass
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro p hp
  split_ifs with hwindow
  · simpa only [mul_comm] using!
      mul_le_mul_of_nonneg_left (hcard p hp hwindow)
        (show 0 ≤ (p : ℝ)⁻¹ by positivity)
  · simp

/-- Integrating a pointwise `A/t` bound over one core block produces the
exact logarithmic width. -/
theorem caichCoreAveragedBlockFirstMoment_le_mul_log
    {X A : ℝ} {x a b : ℕ}
    (hX : 0 ≤ X) (hA : 0 ≤ A) (ha : 1 ≤ a) (hab : a ≤ b)
    (hpoint : ∀ t ∈ Ioc (a : ℝ) (b : ℝ),
      caichCoreTimeFirstMomentKernel X x a b t ≤ A / t) :
    caichCoreAveragedBlockFirstMoment X x a b ≤
      X * A * Real.log ((b : ℝ) / (a : ℝ)) := by
  have haR : (0 : ℝ) < (a : ℝ) := by positivity
  have hbR : (0 : ℝ) < (b : ℝ) := haR.trans_le (by exact_mod_cast hab)
  have hleft : IntegrableOn
      (caichCoreTimeFirstMomentKernel X x a b)
      (Ioc (a : ℝ) (b : ℝ)) := by
    exact integrable_caichCoreTimeFirstMomentKernel_Ioc X x a b
      (u := (a : ℝ)) (v := (b : ℝ)) (by exact_mod_cast ha)
  have hright : IntegrableOn (fun t : ℝ ↦ A / t)
      (Ioc (a : ℝ) (b : ℝ)) := by
    have hcont : ContinuousOn (fun t : ℝ ↦ A / t)
        (Icc (a : ℝ) (b : ℝ)) := by
      apply ContinuousOn.div continuousOn_const continuousOn_id
      intro t ht
      exact ne_of_gt (haR.trans_le ht.1)
    exact hcont.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hint :
      (∫ t in Ioc (a : ℝ) (b : ℝ),
          caichCoreTimeFirstMomentKernel X x a b t) ≤
        ∫ t in Ioc (a : ℝ) (b : ℝ), A / t := by
    exact setIntegral_mono_on hleft hright measurableSet_Ioc hpoint
  unfold caichCoreAveragedBlockFirstMoment
  calc
    X * (∫ t in Ioc (a : ℝ) (b : ℝ),
        caichCoreTimeFirstMomentKernel X x a b t) ≤
      X * (∫ t in Ioc (a : ℝ) (b : ℝ), A / t) :=
        mul_le_mul_of_nonneg_left hint hX
    _ = X * A * Real.log ((b : ℝ) / (a : ℝ)) := by
      rw [← intervalIntegral.integral_of_le (by exact_mod_cast hab)]
      rw [show (fun t : ℝ ↦ A / t) = fun t ↦ A * (1 / t) by
        funext t; ring,
        intervalIntegral.integral_const_mul,
        integral_one_div_of_pos haR hbR]
      ring

/-- The boundary interval has logarithmic width at most `1/X`; hence the
normalizing factor `X` cancels completely. -/
theorem caichBoundaryAveragedBlockFirstMoment_le
    {X A : ℝ} {x a b : ℕ}
    (hX : 0 < X) (hA : 0 ≤ A) (hb : 1 ≤ b)
    (hpoint : ∀ t ∈ Ioc (b : ℝ) ((b : ℝ) * (1 + 1 / X)),
      caichCoreTimeFirstMomentKernel X x a b t ≤ A / t) :
    caichBoundaryAveragedBlockFirstMoment X x a b ≤ A := by
  have hbR : (0 : ℝ) < (b : ℝ) := by positivity
  have hfactor : 1 ≤ 1 + 1 / X := by
    have : 0 ≤ 1 / X := by positivity
    linarith
  have hbq : (b : ℝ) ≤ (b : ℝ) * (1 + 1 / X) := by
    simpa only [mul_one] using! mul_le_mul_of_nonneg_left hfactor hbR.le
  have hleft : IntegrableOn
      (caichCoreTimeFirstMomentKernel X x a b)
      (Ioc (b : ℝ) ((b : ℝ) * (1 + 1 / X))) := by
    exact integrable_caichCoreTimeFirstMomentKernel_Ioc X x a b
      (u := (b : ℝ)) (v := (b : ℝ) * (1 + 1 / X))
      (by exact_mod_cast hb)
  have hright : IntegrableOn (fun t : ℝ ↦ A / t)
      (Ioc (b : ℝ) ((b : ℝ) * (1 + 1 / X))) := by
    have hcont : ContinuousOn (fun t : ℝ ↦ A / t)
        (Icc (b : ℝ) ((b : ℝ) * (1 + 1 / X))) := by
      apply ContinuousOn.div continuousOn_const continuousOn_id
      intro t ht
      exact ne_of_gt (hbR.trans_le ht.1)
    exact hcont.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hint :
      (∫ t in Ioc (b : ℝ) ((b : ℝ) * (1 + 1 / X)),
          caichCoreTimeFirstMomentKernel X x a b t) ≤
        ∫ t in Ioc (b : ℝ) ((b : ℝ) * (1 + 1 / X)), A / t :=
    setIntegral_mono_on hleft hright measurableSet_Ioc hpoint
  unfold caichBoundaryAveragedBlockFirstMoment
  calc
    X * (∫ t in Ioc (b : ℝ) ((b : ℝ) * (1 + 1 / X)),
        caichCoreTimeFirstMomentKernel X x a b t) ≤
      X * (∫ t in Ioc (b : ℝ) ((b : ℝ) * (1 + 1 / X)), A / t) :=
        mul_le_mul_of_nonneg_left hint hX.le
    _ = X * A * Real.log (1 + 1 / X) := by
      rw [← intervalIntegral.integral_of_le hbq]
      rw [show (fun t : ℝ ↦ A / t) = fun t ↦ A * (1 / t) by
        funext t; ring,
        intervalIntegral.integral_const_mul,
        integral_one_div_of_pos hbR (mul_pos hbR (by positivity))]
      have hratio :
          ((b : ℝ) * (1 + 1 / X)) / (b : ℝ) = 1 + 1 / X := by
        field_simp
      rw [hratio]
      ring
    _ ≤ X * A * (1 / X) := by
      gcongr
      convert! Real.log_le_sub_one_of_pos
        (by positivity : 0 < 1 + 1 / X) using 1 <;> ring
    _ = A := by field_simp

end Problem520
end Erdos
