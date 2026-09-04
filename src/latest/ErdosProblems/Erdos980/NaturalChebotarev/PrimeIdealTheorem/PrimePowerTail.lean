/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import CebotarevDensity.NumberFieldEulerProduct
import ErdosProblems.Erdos980.NaturalChebotarev.IdealMangoldt.Basic
import ErdosProblems.Erdos980.NaturalChebotarev.PrimeIdealTheorem.IdealCounting
import ErdosProblems.Erdos980.NaturalChebotarev.PrimeIdealTheorem.IdealCountBounds
import ErdosProblems.Erdos980.NaturalChebotarev.PrimeIdealTheorem.PrimePowerBounds

/-!
# The higher-prime-power tail in the prime ideal theorem

This file separates the exponent-one part of the canonical number-field von Mangoldt
coefficient from the terms with exponent at least two.  The latter have cumulative mass
`o(N)`.  The proof is elementary: a contributing prime ideal has norm at most `sqrt N`,
there are `O(sqrt N)` integral ideals up to that norm, and there are only `O(log N)`
possible exponents, each of weight at most `log N`.
-/

namespace Erdos980.NaturalChebotarev.PrimeIdealTheorem

open Asymptotics Filter NumberField
open scoped BigOperators

noncomputable section

variable (K : Type*) [Field K] [NumberField K]

open IdealMangoldt

/-- The contribution at norm `n` from prime ideals themselves (exponent one). -/
def primeNormThetaCoeff (n : ℕ) : ℝ :=
  ∑ x : normFiber K n, if x.1.exponent = 1 then x.1.weight else 0

/-- The strict-endpoint prime-ideal Chebyshev sum `θ_K(N)`. -/
def primeNormTheta (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.range N, primeNormThetaCoeff K n

/-- The contribution at norm `n` from proper prime-ideal powers. -/
def higherPrimePowerCoeff (n : ℕ) : ℝ :=
  ∑ x : normFiber K n, if 2 ≤ x.1.exponent then x.1.weight else 0

/-- The strict-endpoint cumulative mass of proper prime-ideal powers. -/
def higherPrimePowerMass (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.range N, higherPrimePowerCoeff K n

theorem idealMangoldt_eq_thetaCoeff_add_higherPrimePowerCoeff (n : ℕ) :
    idealMangoldt K n =
      primeNormThetaCoeff K n + higherPrimePowerCoeff K n := by
  classical
  rw [idealMangoldt, primeNormThetaCoeff, higherPrimePowerCoeff, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _
  have hx := x.1.exponent_pos
  by_cases h : x.1.exponent = 1
  · simp [h]
  · have hx2 : 2 ≤ x.1.exponent := by omega
    simp [h, hx2]

theorem sum_idealMangoldt_eq_primeNormTheta_add_higherPrimePowerMass (N : ℕ) :
    (∑ n ∈ Finset.range N, idealMangoldt K n) =
      primeNormTheta K N + higherPrimePowerMass K N := by
  simp_rw [idealMangoldt_eq_thetaCoeff_add_higherPrimePowerCoeff K,
    Finset.sum_add_distrib, primeNormTheta, higherPrimePowerMass]

theorem primeNormTheta_nonneg (N : ℕ) : 0 ≤ primeNormTheta K N := by
  apply Finset.sum_nonneg
  intro n _
  apply Finset.sum_nonneg
  intro x _
  split_ifs
  · exact x.1.weight_nonneg
  · exact le_rfl

theorem higherPrimePowerMass_nonneg (N : ℕ) : 0 ≤ higherPrimePowerMass K N := by
  apply Finset.sum_nonneg
  intro n _
  apply Finset.sum_nonneg
  intro x _
  split_ifs
  · exact x.1.weight_nonneg
  · exact le_rfl

/-- The finite dependent index set occurring in `higherPrimePowerMass`. -/
def higherPrimePowerIndex (N : ℕ) :
    Finset (Sigma fun n : ℕ ↦ normFiber K n) :=
  (Finset.range N).sigma fun n ↦
    Finset.univ.filter fun x : normFiber K n ↦ 2 ≤ x.1.exponent

theorem higherPrimePowerMass_eq_sum_index (N : ℕ) :
    higherPrimePowerMass K N =
      ∑ y ∈ higherPrimePowerIndex K N, y.2.1.weight := by
  classical
  rw [higherPrimePowerMass, higherPrimePowerIndex, Finset.sum_sigma]
  apply Finset.sum_congr rfl
  intro n _
  rw [higherPrimePowerCoeff, Finset.sum_filter]

/-- Proper prime powers below `N`, as a finite subtype. -/
abbrev HigherPrimePowerData (N : ℕ) :=
  {y : Sigma fun n : ℕ ↦ normFiber K n // y ∈ higherPrimePowerIndex K N}

/-- Nonzero integral ideals with norm at most the natural square root of `N`. -/
abbrev IdealsToSqrt (N : ℕ) :=
  {I : Chebotarev.NonzeroIdeal K // Ideal.absNorm I.1 ≤ Nat.sqrt N}

/-- Exponents which can occur in a proper prime power of norm at most `N`. -/
abbrev HigherExponentRange (N : ℕ) :=
  {m : ℕ // m ∈ Finset.Icc 2 (Nat.log 2 N)}

/-- A proper prime power of norm below `N` is determined by its underlying prime ideal and
its exponent.  The prime ideal has norm at most `sqrt N`, and the exponent is at most
`log₂ N`. -/
def higherPrimePowerToBoundedData (N : ℕ) :
    HigherPrimePowerData K N → IdealsToSqrt K N × HigherExponentRange N := fun y ↦ by
  rcases y with ⟨⟨n, x⟩, hy⟩
  have hy' := Finset.mem_sigma.mp hy
  have hn : n < N := Finset.mem_range.mp hy'.1
  have hm2 : 2 ≤ x.1.exponent := (Finset.mem_filter.mp hy'.2).2
  have hqpos : 0 < Ideal.absNorm x.1.prime :=
    lt_of_lt_of_le (by omega) x.1.two_le_absNorm
  have hpow2 : Ideal.absNorm x.1.prime ^ 2 ≤ N := by
    calc
      Ideal.absNorm x.1.prime ^ 2 ≤
          Ideal.absNorm x.1.prime ^ x.1.exponent :=
        Nat.pow_le_pow_right hqpos hm2
      _ = n := x.2
      _ ≤ N := hn.le
  have hqSqrt : Ideal.absNorm x.1.prime ≤ Nat.sqrt N := Nat.le_sqrt'.2 hpow2
  have htwoPow : 2 ^ x.1.exponent ≤ N := by
    calc
      2 ^ x.1.exponent ≤ Ideal.absNorm x.1.prime ^ x.1.exponent :=
        Nat.pow_le_pow_left x.1.two_le_absNorm _
      _ = n := x.2
      _ ≤ N := hn.le
  exact
    ⟨⟨⟨x.1.prime, x.1.prime_ne_bot⟩, hqSqrt⟩,
      ⟨x.1.exponent, Finset.mem_Icc.mpr
        ⟨hm2, Nat.le_log_of_pow_le (by omega) htwoPow⟩⟩⟩

theorem higherPrimePowerToBoundedData_injective (N : ℕ) :
    Function.Injective (higherPrimePowerToBoundedData K N) := by
  rintro ⟨⟨n, x⟩, hxmem⟩ ⟨⟨n', x'⟩, hx'mem⟩ h
  have hP : x.1.prime = x'.1.prime := by
    exact congrArg (fun z ↦ z.1.1.1) h
  have hm : x.1.exponent = x'.1.exponent := by
    exact congrArg (fun z ↦ z.2.1) h
  have hn : n = n' := by
    calc
      n = x.1.norm := x.2.symm
      _ = x'.1.norm := by simp only [PrimeIdealPower.norm, hP, hm]
      _ = n' := x'.2
  subst n'
  have hxx : x = x' := by
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext
      exact hP
    · exact hm
  apply Subtype.ext
  exact Sigma.ext rfl (heq_of_eq hxx)

theorem card_higherPrimePowerIndex_le (N : ℕ) :
    (higherPrimePowerIndex K N).card ≤
      Nat.card (IdealsToSqrt K N) * (Nat.log 2 N + 1) := by
  classical
  let : Finite (IdealsToSqrt K N) := by
    let : Finite {I : Ideal (𝓞 K) // Ideal.absNorm I ≤ Nat.sqrt N} :=
      (Ideal.finite_setOfPred_absNorm_le (S := 𝓞 K) (Nat.sqrt N)).to_subtype
    apply Finite.of_injective
      (f := fun I : IdealsToSqrt K N ↦
        (⟨I.1.1, I.2⟩ : {I : Ideal (𝓞 K) // Ideal.absNorm I ≤ Nat.sqrt N}))
    intro I J h
    have hIJ : I.1.1 = J.1.1 := congrArg
      (fun Z : {I : Ideal (𝓞 K) // Ideal.absNorm I ≤ Nat.sqrt N} ↦ Z.1) h
    exact Subtype.ext (Subtype.ext hIJ)
  have hcard := Nat.card_le_card_of_injective
    (higherPrimePowerToBoundedData K N)
    (higherPrimePowerToBoundedData_injective K N)
  rw [Nat.card_prod] at hcard
  have hsource : Nat.card (HigherPrimePowerData K N) =
      (higherPrimePowerIndex K N).card := by
    simp only [Nat.card_eq_fintype_card, Fintype.card_coe]
  have hexp : Nat.card (HigherExponentRange N) ≤ Nat.log 2 N + 1 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_coe]
    rw [Nat.card_Icc]
    omega
  rw [hsource] at hcard
  exact hcard.trans (Nat.mul_le_mul_left _ hexp)

/-- A quantitative square-root/log-squared majorant for the higher-power mass. -/
theorem higherPrimePowerMass_le_allIdealCount_mul_log_sq
    {N : ℕ} (hN : 2 ≤ N) :
    higherPrimePowerMass K N ≤
      (allIdealCount K (Nat.sqrt N) : ℝ) * (Nat.log 2 N + 1 : ℕ) *
        Real.log (N : ℝ) := by
  classical
  have hlogN : 0 ≤ Real.log (N : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (one_le_two.trans hN))
  have hterm : ∀ y ∈ higherPrimePowerIndex K N,
      y.2.1.weight ≤ Real.log (N : ℝ) := by
    rintro ⟨n, x⟩ hy
    have hy' := Finset.mem_sigma.mp hy
    have hn : n < N := Finset.mem_range.mp hy'.1
    have hqN : Ideal.absNorm x.1.prime ≤ N := by
      exact x.1.absNorm_prime_le_norm.trans_eq x.2 |>.trans hn.le
    have hqpos : (0 : ℝ) < (Ideal.absNorm x.1.prime : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 2) x.1.two_le_absNorm)
    have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 2) hN)
    exact Real.strictMonoOn_log.monotoneOn hqpos hNpos (by exact_mod_cast hqN)
  rw [higherPrimePowerMass_eq_sum_index]
  calc
    (∑ y ∈ higherPrimePowerIndex K N, y.2.1.weight) ≤
        ∑ _y ∈ higherPrimePowerIndex K N, Real.log (N : ℝ) :=
      Finset.sum_le_sum hterm
    _ = ((higherPrimePowerIndex K N).card : ℝ) * Real.log (N : ℝ) := by
      simp [nsmul_eq_mul]
    _ ≤ (Nat.card (IdealsToSqrt K N) : ℝ) * (Nat.log 2 N + 1 : ℕ) *
        Real.log (N : ℝ) := by
      apply mul_le_mul_of_nonneg_right _ hlogN
      exact_mod_cast card_higherPrimePowerIndex_le K N
    _ = (allIdealCount K (Nat.sqrt N) : ℝ) * (Nat.log 2 N + 1 : ℕ) *
        Real.log (N : ℝ) := by
      rw [allIdealCount_eq_nonzeroIdeal_card]

theorem natLog_two_add_one_le_two_mul_log_div_log_two
    {N : ℕ} (hN : 2 ≤ N) :
    ((Nat.log 2 N + 1 : ℕ) : ℝ) ≤
      2 * Real.log (N : ℝ) / Real.log 2 := by
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2le : Real.log 2 ≤ Real.log (N : ℝ) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hN)
  have hone : (1 : ℝ) ≤ Real.log (N : ℝ) / Real.log 2 :=
    (le_div_iff₀ hlog2pos).2 (by simpa using hlog2le)
  have hnat : (Nat.log 2 N : ℝ) ≤ Real.log (N : ℝ) / Real.log 2 := by
    have h := Real.log2_le_logb N
    simpa [Nat.log2_eq_log_two, Real.logb] using h
  calc
    ((Nat.log 2 N + 1 : ℕ) : ℝ) = (Nat.log 2 N : ℝ) + 1 := by norm_num
    _ ≤ Real.log (N : ℝ) / Real.log 2 + 1 := by linarith
    _ ≤ Real.log (N : ℝ) / Real.log 2 +
        Real.log (N : ℝ) / Real.log 2 := by linarith
    _ = 2 * Real.log (N : ℝ) / Real.log 2 := by ring

/-- `sqrt N · log(N)^2` is negligible compared with `N`, on natural endpoints. -/
theorem sqrt_mul_log_sq_isLittleO_nat :
    (fun N : ℕ ↦ Real.sqrt (N : ℝ) * Real.log (N : ℝ) ^ 2) =o[atTop]
      (fun N : ℕ ↦ (N : ℝ)) := by
  have hlog :
      (fun N : ℕ ↦ Real.log (N : ℝ) ^ 2) =o[atTop]
        (fun N : ℕ ↦ (N : ℝ) ^ ((1 : ℝ) / 2)) := by
    simpa only [Function.comp_def, Real.rpow_ofNat] using
      (isLittleO_log_rpow_rpow_atTop 2
        (by norm_num : (0 : ℝ) < (1 : ℝ) / 2)).natCast_atTop
  have hsqrt :
      (fun N : ℕ ↦ Real.sqrt (N : ℝ)) =O[atTop]
        (fun N : ℕ ↦ (N : ℝ) ^ ((1 : ℝ) / 2)) := by
    simpa only [Real.sqrt_eq_rpow] using
      (isBigO_refl (fun N : ℕ ↦ (N : ℝ) ^ ((1 : ℝ) / 2)) atTop)
  have hmul := hsqrt.mul_isLittleO hlog
  refine hmul.congr' EventuallyEq.rfl ?_
  filter_upwards [eventually_gt_atTop 0] with N hN
  rw [← Real.rpow_add (by exact_mod_cast hN)]
  norm_num

/-- The total contribution of prime-ideal powers with exponent at least two is `o(N)`. -/
theorem higherPrimePowerMass_isLittleO :
    higherPrimePowerMass K =o[atTop] (fun N : ℕ ↦ (N : ℝ)) := by
  obtain ⟨C, hC, hcount⟩ := exists_allIdealCount_le_linear K
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hO : higherPrimePowerMass K =O[atTop]
      (fun N : ℕ ↦ Real.sqrt (N : ℝ) * Real.log (N : ℝ) ^ 2) := by
    apply IsBigO.of_bound (2 * C / Real.log 2)
    filter_upwards [eventually_ge_atTop 2] with N hN
    have hlogN : 0 ≤ Real.log (N : ℝ) :=
      Real.log_nonneg (by exact_mod_cast (one_le_two.trans hN))
    have hsqrt : (Nat.sqrt N : ℝ) ≤ Real.sqrt (N : ℝ) := by
      rw [Real.le_sqrt (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
      exact_mod_cast (show Nat.sqrt N ^ 2 ≤ N by
        simpa [pow_two] using Nat.sqrt_le N)
    have hcount' : (allIdealCount K (Nat.sqrt N) : ℝ) ≤
        C * Real.sqrt (N : ℝ) :=
      (hcount (Nat.sqrt N)).trans (mul_le_mul_of_nonneg_left hsqrt hC)
    have hlogBound := natLog_two_add_one_le_two_mul_log_div_log_two hN
    rw [Real.norm_eq_abs, abs_of_nonneg (higherPrimePowerMass_nonneg K N),
      Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg _)
        (sq_nonneg _))]
    calc
      higherPrimePowerMass K N ≤
          (allIdealCount K (Nat.sqrt N) : ℝ) * (Nat.log 2 N + 1 : ℕ) *
            Real.log (N : ℝ) :=
        higherPrimePowerMass_le_allIdealCount_mul_log_sq K hN
      _ ≤ (C * Real.sqrt (N : ℝ)) *
          (2 * Real.log (N : ℝ) / Real.log 2) * Real.log (N : ℝ) := by
        gcongr
      _ = (2 * C / Real.log 2) *
          (Real.sqrt (N : ℝ) * Real.log (N : ℝ) ^ 2) := by
        field_simp
  exact hO.trans_isLittleO sqrt_mul_log_sq_isLittleO_nat

/-- The exact `ψ_K - θ_K` difference is therefore `o(N)`. -/
theorem sum_idealMangoldt_sub_primeNormTheta_isLittleO :
    ((fun N : ℕ ↦ ∑ n ∈ Finset.range N, idealMangoldt K n) -
        primeNormTheta K) =o[atTop] (fun N : ℕ ↦ (N : ℝ)) := by
  refine (higherPrimePowerMass_isLittleO K).congr' ?_ EventuallyEq.rfl
  filter_upwards with N
  rw [Pi.sub_apply, sum_idealMangoldt_eq_primeNormTheta_add_higherPrimePowerMass]
  ring

end

end Erdos980.NaturalChebotarev.PrimeIdealTheorem
