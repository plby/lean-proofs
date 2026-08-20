/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import CebotarevDensity.NumberFieldEulerProduct
import ErdosProblems.Erdos980.NaturalChebotarev.PrimeIdealTheorem.Deweighting
import ErdosProblems.Erdos980.NaturalChebotarev.PrimeIdealTheorem.PrimePowerTail
import ErdosProblems.Erdos980.NaturalChebotarev.PrimeIdealTheorem.WeightedBridge
import ErdosProblems.Erdos980.NaturalChebotarev.PrimeIdealTheorem.WeightedPrimeIdealTheorem

/-!
# The unweighted prime ideal theorem

This file specializes the weighted Dedekind prime ideal theorem to the
inclusive natural cutoffs used in the natural-density Chebotarev argument.
-/

namespace Erdos980.NaturalChebotarev.PrimeIdealTheorem

open Asymptotics BigOperators Filter
open scoped Topology

noncomputable section

/-- The inclusive prime-ideal von Mangoldt sum. -/
def idealMangoldtInclusive
    (K : Type*) [Field K] [NumberField K] (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.range (N + 1), IdealMangoldt.idealMangoldt K n

/-- Inclusive and strict endpoint conventions give the same linear main
term for the ideal Mangoldt sum. -/
theorem idealMangoldtInclusive_div_tendsto_one
    (K : Type*) [Field K] [NumberField K] :
    Tendsto (fun N : ℕ ↦ idealMangoldtInclusive K N / (N : ℝ))
      atTop (nhds 1) := by
  have hshift :
      Tendsto
        (fun N : ℕ ↦
          (∑ n ∈ Finset.range (N + 1), IdealMangoldt.idealMangoldt K n) /
            ((N + 1 : ℕ) : ℝ))
        atTop (nhds 1) :=
    (idealMangoldt_sum_range_div_tendsto K).comp (tendsto_add_atTop_nat 1)
  have hscale : Tendsto (fun N : ℕ ↦ (((N + 1 : ℕ) : ℝ) / (N : ℝ)))
      atTop (nhds 1) := by
    have hlim : Tendsto (fun N : ℕ ↦ 1 + 1 / (N : ℝ))
        atTop (nhds (1 + 0)) :=
      tendsto_const_nhds.add tendsto_one_div_atTop_nhds_zero_nat
    have heq :
        (fun N : ℕ ↦ (((N + 1 : ℕ) : ℝ) / (N : ℝ))) =ᶠ[atTop]
          (fun N : ℕ ↦ 1 + 1 / (N : ℝ)) := by
      filter_upwards [eventually_ge_atTop 1] with N hN
      have hN0 : (N : ℝ) ≠ 0 := by positivity
      push_cast
      field_simp
    simpa using hlim.congr' heq.symm
  have hprod := hshift.mul hscale
  have hprod' :
      Tendsto
        (fun N : ℕ ↦
          (∑ n ∈ Finset.range (N + 1), IdealMangoldt.idealMangoldt K n) /
              ((N + 1 : ℕ) : ℝ) * (((N + 1 : ℕ) : ℝ) / (N : ℝ)))
        atTop (nhds 1) := by simpa using hprod
  apply hprod'.congr'
  filter_upwards [eventually_ge_atTop 1] with N hN
  rw [idealMangoldtInclusive]
  have hN0 : (N : ℝ) ≠ 0 := by positivity
  have hN10 : ((N + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp

/-- Asymptotic-equivalence form of the inclusive weighted theorem. -/
theorem idealMangoldtInclusive_isEquivalent
    (K : Type*) [Field K] [NumberField K] :
    idealMangoldtInclusive K ~[atTop] (fun N : ℕ ↦ (N : ℝ)) := by
  have hden : ∀ᶠ N : ℕ in atTop, (N : ℝ) ≠ 0 := by
    filter_upwards [eventually_ge_atTop 1] with N hN
    positivity
  apply (isEquivalent_iff_tendsto_one hden).2
  change Tendsto (fun N : ℕ ↦ idealMangoldtInclusive K N / (N : ℝ))
    atTop (nhds 1)
  exact idealMangoldtInclusive_div_tendsto_one K

/-- Shifting a natural endpoint by one does not change its linear asymptotic scale. -/
theorem natSuccCast_isEquivalent_natCast :
    (fun N : ℕ ↦ ((N + 1 : ℕ) : ℝ)) ~[atTop]
      (fun N : ℕ ↦ (N : ℝ)) := by
  have hone : (fun _N : ℕ ↦ (1 : ℝ)) =o[atTop]
      (fun N : ℕ ↦ (N : ℝ)) := by
    simpa [Function.comp_def] using
      (isLittleO_const_id_atTop (1 : ℝ)).comp_tendsto
        (tendsto_natCast_atTop_atTop (R := ℝ))
  have hadd :=
    (Asymptotics.IsEquivalent.refl :
      (fun N : ℕ ↦ (N : ℝ)) ~[atTop]
        (fun N : ℕ ↦ (N : ℝ))).add_isLittleO hone
  exact hadd.congr_left (Eventually.of_forall fun N ↦ by simp)

/-- The norm-fiber definition of theta used in the prime-power estimate agrees exactly
with the norm-multiplicity definition used in partial summation. -/
theorem primeNormTheta_eq_primeIdealTheta
    (K : Type*) [Field K] [NumberField K] (N : ℕ) :
    primeNormTheta K N = primeIdealTheta K N := by
  rw [primeNormTheta, primeIdealTheta]
  apply Finset.sum_congr rfl
  intro n _
  change exponentOnePart K n =
    (primeNormMultiplicity K n : ℝ) * Real.log (n : ℝ)
  exact exponentOnePart_eq_primeNormMultiplicity_mul_log K n

/-- The prime-ideal theta function is asymptotic to its endpoint.  This is the elementary
`psi_K -> theta_K` step: the proper prime powers are negligible. -/
theorem primeIdealTheta_isEquivalent
    (K : Type*) [Field K] [NumberField K] :
    primeIdealTheta K ~[atTop] (fun N : ℕ ↦ (N : ℝ)) := by
  have htheta : primeNormTheta K ~[atTop] (fun N : ℕ ↦ (N : ℝ)) :=
    weighted_isEquivalent_of_mangoldt
      (idealMangoldt_sum_range_isEquivalent K)
      (sum_idealMangoldt_sub_primeNormTheta_isLittleO K)
  exact htheta.congr_left <|
    Eventually.of_forall fun N ↦ primeNormTheta_eq_primeIdealTheta K N

/-- Inclusive logarithmically weighted prime-ideal counts satisfy the same linear
asymptotic. -/
theorem multiplicityChebyshev_primeNormMultiplicity_isEquivalent
    (K : Type*) [Field K] [NumberField K] :
    multiplicityChebyshev
        (fun n ↦ (primeNormMultiplicity K n : ℝ)) ~[atTop]
      (fun N : ℕ ↦ (N : ℝ)) := by
  have hshift := (primeIdealTheta_isEquivalent K).comp_tendsto
    (tendsto_add_atTop_nat 1)
  have hshift' :
      (fun N : ℕ ↦ primeIdealTheta K (N + 1)) ~[atTop]
        (fun N : ℕ ↦ ((N + 1 : ℕ) : ℝ)) := by
    simpa [Function.comp_def] using hshift
  exact (hshift'.trans natSuccCast_isEquivalent_natCast).congr_left <|
    Eventually.of_forall fun N ↦
      (multiplicityChebyshev_primeNormMultiplicity K N).symm

/-- The unconditional prime ideal theorem for every number field, on the inclusive
natural endpoint convention used by `SplitTransfer.primeIdealCount`. -/
theorem primeIdealCount_isEquivalent
    (K : Type*) [Field K] [NumberField K] :
    (fun N : ℕ ↦ (SplitTransfer.primeIdealCount K N : ℝ)) ~[atTop]
      pntScale 1 := by
  have hcount := multiplicityCount_isEquivalent_of_multiplicityChebyshev
    (a := fun n ↦ (primeNormMultiplicity K n : ℝ))
    (fun _ ↦ Nat.cast_nonneg _)
    (multiplicityChebyshev_primeNormMultiplicity_isEquivalent K)
  exact hcount.congr_left <|
    Eventually.of_forall fun N ↦ multiplicityCount_primeNormMultiplicity K N

/-- Explicit `N / log N` form of the prime ideal theorem. -/
theorem primeIdealCount_isEquivalent_natCast_div_log
    (K : Type*) [Field K] [NumberField K] :
    (fun N : ℕ ↦ (SplitTransfer.primeIdealCount K N : ℝ)) ~[atTop]
      (fun N : ℕ ↦ (N : ℝ) / Real.log (N : ℝ)) := by
  exact (primeIdealCount_isEquivalent K).congr_right <|
    Eventually.of_forall fun N ↦ by simp [pntScale, endpointLog]

end

end Erdos980.NaturalChebotarev.PrimeIdealTheorem
