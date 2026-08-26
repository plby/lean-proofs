import ErdosProblems.Erdos520.CaichScheduledEnergyScaling

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open Finset MeasureTheory Set
open scoped BigOperators Interval

namespace Erdos
namespace Problem520

/-!
# Main-term cleanup with one scheduled endpoint beyond the test point

The least thin endpoint above a test point is usually not the test point
itself.  Capping that last endpoint changes the block energy.  A cleaner
exact treatment is to retain the scheduled endpoint: every prime beyond
`x` contributes zero to the averaged main term, so the chain may overshoot
`x` without changing it.  This keeps every block energy literally equal to
the selected Harper schedule's energy.
-/

theorem caichShortPrimeAverage_strictSmooth_eq_zero_of_x_lt_p
    {X : ℝ} (hX : 0 < X) (omega : Omega)
    {x p : ℕ} (hxp : x < p) :
    caichShortPrimeAverage X p
      (fun t ↦ |caichStrictSmoothReal omega ((x : ℝ) / t) p| ^ 2) = 0 := by
  have hp : 0 < p := Nat.zero_lt_of_lt hxp
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have hpq : (p : ℝ) ≤ (p : ℝ) * (1 + 1 / X) := by
    have hinv : 0 ≤ 1 / X := by positivity
    nlinarith
  unfold caichShortPrimeAverage
  have hint : (∫ t in (p : ℝ)..(p : ℝ) * (1 + 1 / X),
      |caichStrictSmoothReal omega ((x : ℝ) / t) p| ^ 2) = 0 := by
    apply intervalIntegral.integral_zero_ae
    filter_upwards with t
    intro ht
    rw [Set.uIoc_of_le hpq] at ht
    have htpos : (0 : ℝ) < t := hpR.trans ht.1
    have hxt : (x : ℝ) < t := by
      exact (by exact_mod_cast hxp : (x : ℝ) < (p : ℝ)).trans ht.1
    have hdiv : (x : ℝ) / t < 1 := (div_lt_one htpos).2 hxt
    unfold caichStrictSmoothReal
    rw [ΨReal_eq_zero_of_lt_one omega _ _ hdiv, abs_zero, zero_pow]
    norm_num
  rw [hint, mul_zero]

/-- Extending the upper prime endpoint beyond `x` does not change the
averaged main term. -/
theorem caichInitialSmoothedMain_eq_of_right_ge_testPoint
    {X : ℝ} (hX : 0 < X) (omega : Omega)
    {x a b : ℕ} (hax : a ≤ x) (hxb : x ≤ b) :
    caichInitialSmoothedMain X omega x a b =
      caichInitialSmoothedMain X omega x a x := by
  rw [caichInitialSmoothedMain_add X omega x hax hxb]
  have hzero : caichInitialSmoothedMain X omega x x b = 0 := by
    unfold caichInitialSmoothedMain
    apply Finset.sum_eq_zero
    intro p hp
    exact caichShortPrimeAverage_strictSmooth_eq_zero_of_x_lt_p
      hX omega (mem_freshPrimes.mp hp).2.1
  rw [hzero, add_zero]

/-- Exact core-plus-boundary decomposition along a monotone scheduled chain
whose final endpoint is merely at least `x`. -/
theorem caichInitialSmoothedMain_eq_sum_core_boundary_of_final_ge
    {X : ℝ} (hX : 0 < X) (omega : Omega) {x : ℕ} (hx : 0 < x)
    (endpoint : ℕ → ℕ) (N : ℕ)
    (hmono : Monotone endpoint)
    (hone : ∀ j ≤ N, 1 ≤ endpoint j)
    (hstart : endpoint 0 ≤ x)
    (hfinal : x ≤ endpoint N) :
    caichInitialSmoothedMain X omega x (endpoint 0) x =
      ∑ j ∈ Finset.range N,
        (caichCoreAveragedBlockMain X omega x
            (endpoint j) (endpoint (j + 1)) +
          caichBoundaryAveragedBlockMain X omega x
            (endpoint j) (endpoint (j + 1))) := by
  have hover := caichInitialSmoothedMain_eq_of_right_ge_testPoint
    hX omega hstart hfinal
  have hchain := caichInitialSmoothedMain_eq_sum_chain
    X omega x endpoint N hmono
  rw [← hover, hchain]
  apply Finset.sum_congr rfl
  intro j hj
  have hjN : j < N := Finset.mem_range.mp hj
  exact caichInitialSmoothedMain_eq_core_add_boundary
    hX omega x hx (hone j hjN.le) (hmono (Nat.le_succ j))

/-- Uncapped deterministic schedule cleanup. -/
theorem caichInitialSmoothedMain_le_nearMax_add_residuals_of_final_ge
    {X C : ℝ} {x ell : ℕ}
    (J : ℕ → ℕ) (U : ℕ → ℕ → Omega → ℝ)
    (endpoint : ℕ → ℕ) (N : ℕ)
    (near : ℕ → Prop) [DecidablePred near]
    (blockIndex : ℕ → ℕ)
    (hX : 0 < X) (hx : 0 < x) (hC : 0 ≤ C) (omega : Omega)
    (hmono : Monotone endpoint)
    (hone : ∀ j ≤ N, 1 ≤ endpoint j)
    (hstart : endpoint 0 ≤ x)
    (hfinal : x ≤ endpoint N)
    (hJ : ∀ j ∈ Finset.range N, near j → blockIndex j ≤ J ell)
    (hright : ∀ j ∈ Finset.range N, near j → 2 ≤ endpoint (j + 1))
    (hU : ∀ j ∈ Finset.range N, near j →
      realSmoothBlockEnergy (endpoint j) (endpoint (j + 1)) omega ≤
        U ell (blockIndex j) omega)
    (hshort : ∀ j ∈ Finset.range N, near j → ∀ z ∈
      Ioc ((x : ℝ) / (endpoint (j + 1) : ℝ))
        ((x : ℝ) / (endpoint j : ℝ)),
      caichShortWindowReciprocalMass X x
          (endpoint j) (endpoint (j + 1)) z ≤
        C / (X * Real.log (endpoint (j + 1) : ℝ))) :
    caichInitialSmoothedMain X omega x (endpoint 0) x ≤
      (((Finset.range N).filter near).card : ℝ) * C * (x : ℝ) *
          caichBlockEnergyMax J U ell omega +
        caichLongRatioAveragedMain X omega x (Finset.range N)
          endpoint (fun j ↦ endpoint (j + 1)) near +
        caichBoundaryAveragedMain X omega x (Finset.range N)
          endpoint (fun j ↦ endpoint (j + 1)) := by
  let blocks := Finset.range N
  let right : ℕ → ℕ := fun j ↦ endpoint (j + 1)
  have hdecomp := caichInitialSmoothedMain_eq_sum_core_boundary_of_final_ge
    hX omega hx endpoint N hmono hone hstart hfinal
  have hpartition := caichNear_add_longRatio_eq_coreSum
    X omega x blocks endpoint right near
  have hnear := caichNearRatioAveragedMain_le_card_mul_blockEnergyMax
    J U blocks endpoint right near blockIndex hX hx hC omega hJ
    (fun j hj hjNear ↦ hone j (Finset.mem_range.mp hj).le)
    (fun j hj hjNear ↦ hmono (Nat.le_succ j)) hright hU hshort
  rw [hdecomp]
  unfold caichBoundaryAveragedMain
  dsimp only [blocks, right] at hpartition hnear ⊢
  rw [Finset.sum_add_distrib, ← hpartition]
  linarith

/-- Honest scaled-energy version of the uncapped cleanup. -/
theorem caichUnaccountedSmoothedMain_le_scaledScheduledL12_add_L2_of_final_ge
    {X C D0 : ℝ} {x ell : ℕ}
    (J : ℕ → ℕ) (U : ℕ → ℕ → Omega → ℝ)
    (endpoint : ℕ → ℕ) (N : ℕ)
    (near : ℕ → Prop) [DecidablePred near]
    (blockIndex : ℕ → ℕ)
    (hX : 0 < X) (hx : 0 < x) (hC : 0 ≤ C) (hD0 : 0 ≤ D0)
    (omega : Omega)
    (hmono : Monotone endpoint)
    (hone : ∀ j ≤ N, 1 ≤ endpoint j)
    (hstart : endpoint 0 ≤ x)
    (hfinal : x ≤ endpoint N)
    (hJ : ∀ j ∈ Finset.range N, near j → blockIndex j ≤ J ell)
    (hright : ∀ j ∈ Finset.range N, near j → 2 ≤ endpoint (j + 1))
    (hU : ∀ j ∈ Finset.range N, near j →
      realSmoothBlockEnergy (endpoint j) (endpoint (j + 1)) omega ≤
        U ell (blockIndex j) omega)
    (hshort : ∀ j ∈ Finset.range N, near j → ∀ z ∈
      Ioc ((x : ℝ) / (endpoint (j + 1) : ℝ))
        ((x : ℝ) / (endpoint j : ℝ)),
      caichShortWindowReciprocalMass X x
          (endpoint j) (endpoint (j + 1)) z ≤
        C / (X * Real.log (endpoint (j + 1) : ℝ)))
    (hmax : 0 ≤ caichBlockEnergyMax J U ell omega)
    (hbudget : (((Finset.range N).filter near).card : ℝ) * C ≤
      D0 * caichAuxiliaryLogFactor ell) :
    caichUnaccountedSmoothedMain X J (caichScaledBlockEnergy D0 U)
        ell omega x (endpoint 0) x ≤
      caichScheduledL12 X omega x (Finset.range N)
          endpoint (fun j ↦ endpoint (j + 1)) near +
        caichScheduledL2 X omega x (Finset.range N)
          endpoint (fun j ↦ endpoint (j + 1)) := by
  let blocks := Finset.range N
  let right : ℕ → ℕ := fun j ↦ endpoint (j + 1)
  let M : ℝ := caichBlockEnergyMax J U ell omega
  let Mscaled : ℝ :=
    caichBlockEnergyMax J (caichScaledBlockEnergy D0 U) ell omega
  have hscale : Mscaled = D0 * M := by
    simpa only [Mscaled, M] using!
      caichBlockEnergyMax_scaled (J := J) (U := U) hD0 ell omega
  have hcleanup := caichInitialSmoothedMain_le_nearMax_add_residuals_of_final_ge
    J U endpoint N near blockIndex hX hx hC omega hmono hone hstart hfinal
      hJ hright hU hshort
  have hcoeff :
      (((Finset.range N).filter near).card : ℝ) * C * (x : ℝ) * M ≤
        caichAuxiliaryLogFactor ell * (x : ℝ) * Mscaled := by
    calc
      (((Finset.range N).filter near).card : ℝ) * C * (x : ℝ) * M ≤
          (D0 * caichAuxiliaryLogFactor ell) * (x : ℝ) * M := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hbudget (by positivity)) hmax
      _ = caichAuxiliaryLogFactor ell * (x : ℝ) * Mscaled := by
        rw [hscale]
        ring
  have hcleanupScaled :
      caichInitialSmoothedMain X omega x (endpoint 0) x ≤
        caichAuxiliaryLogFactor ell * (x : ℝ) * Mscaled +
          caichLongRatioAveragedMain X omega x blocks endpoint right near +
          caichBoundaryAveragedMain X omega x blocks endpoint right := by
    calc
      caichInitialSmoothedMain X omega x (endpoint 0) x ≤
          (((Finset.range N).filter near).card : ℝ) * C * (x : ℝ) * M +
            caichLongRatioAveragedMain X omega x blocks endpoint right near +
            caichBoundaryAveragedMain X omega x blocks endpoint right := by
        simpa only [blocks, right, M] using! hcleanup
      _ ≤ caichAuxiliaryLogFactor ell * (x : ℝ) * Mscaled +
            caichLongRatioAveragedMain X omega x blocks endpoint right near +
            caichBoundaryAveragedMain X omega x blocks endpoint right := by
        gcongr
  have hmaxScaled : 0 ≤ Mscaled := by
    rw [hscale]
    exact mul_nonneg hD0 hmax
  exact caichUnaccountedSmoothedMain_le_scheduledL12_add_L2
    J (caichScaledBlockEnergy D0 U) blocks endpoint right near hX.le hx omega
      hmaxScaled le_rfl (by
        simpa only [Mscaled] using! hcleanupScaled)

end Problem520
end Erdos
