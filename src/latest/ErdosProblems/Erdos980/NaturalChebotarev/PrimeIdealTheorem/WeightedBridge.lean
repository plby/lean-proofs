/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import CebotarevDensity.NumberFieldEulerProduct
import ErdosProblems.Erdos980.NaturalChebotarev.IdealMangoldt.Basic
import ErdosProblems.Erdos980.NaturalChebotarev.PrimeIdealTheorem.PrimeNormMultiplicity
import ErdosProblems.Erdos980.NaturalChebotarev.PrimeIdealTheorem.CountingConversion

/-!
# The prime-ideal part of the number-field von Mangoldt coefficient

This file separates the exponent-one terms in the canonical coefficient
`IdealMangoldt.idealMangoldt K n` from the terms coming from proper prime-ideal powers.
The exponent-one term is exactly

`primeNormMultiplicity K n * log n`,

where `primeNormMultiplicity K n` counts nonzero prime ideals of absolute norm `n`.
Summing the pointwise identity gives the exact finite decomposition `psi = theta + R` used in
the passage from the weighted prime ideal theorem to the prime-ideal counting theorem.
-/

open NumberField
open scoped BigOperators

namespace Erdos980.NaturalChebotarev.PrimeIdealTheorem

noncomputable section

variable (K : Type*) [Field K] [NumberField K]

/-- The part of `idealMangoldt K n` contributed by prime ideals to the first power. -/
def exponentOnePart (n : ℕ) : ℝ :=
  ∑ x : IdealMangoldt.normFiber K n,
    if x.1.exponent = 1 then x.1.weight else 0

/-- The part of `idealMangoldt K n` contributed by powers with exponent at least two. -/
def higherPrimePowerPart (n : ℕ) : ℝ :=
  ∑ x : IdealMangoldt.normFiber K n,
    if 2 ≤ x.1.exponent then x.1.weight else 0

/-- Every positive prime-power exponent is either one or at least two, giving a pointwise
decomposition of the canonical number-field von Mangoldt coefficient. -/
theorem idealMangoldt_eq_exponentOnePart_add_higherPrimePowerPart (n : ℕ) :
    IdealMangoldt.idealMangoldt K n =
      exponentOnePart K n + higherPrimePowerPart K n := by
  classical
  rw [IdealMangoldt.idealMangoldt, exponentOnePart, higherPrimePowerPart,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _
  by_cases h₁ : x.1.exponent = 1
  · simp [h₁]
  · have h₂ : 2 ≤ x.1.exponent := by
      have := x.1.exponent_pos
      omega
    simp [h₁, h₂]

/-- Exponent-one elements of the canonical norm fiber are exactly prime ideals of norm `n`. -/
private def exponentOneNormFiberEquiv (n : ℕ) :
    {x : IdealMangoldt.normFiber K n // x.1.exponent = 1} ≃ primeNormFiber K n where
  toFun x :=
    ⟨⟨x.1.1.prime, x.1.1.prime_isPrime, x.1.1.prime_ne_bot⟩, by
      simpa [IdealMangoldt.PrimeIdealPower.norm, x.2] using x.1.2⟩
  invFun 𝔭 :=
    let x : IdealMangoldt.PrimeIdealPower K :=
      ⟨(𝔭.1, 1), by simp⟩
    ⟨⟨x, by
      simpa [x, IdealMangoldt.PrimeIdealPower.norm,
        IdealMangoldt.PrimeIdealPower.prime,
        IdealMangoldt.PrimeIdealPower.exponent] using 𝔭.2⟩, rfl⟩
  left_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext
      rfl
    · exact x.2.symm
  right_inv 𝔭 := by
    apply Subtype.ext
    rfl

/-- The exponent-one part is the prime-norm multiplicity times the common logarithmic weight. -/
theorem exponentOnePart_eq_primeNormMultiplicity_mul_log (n : ℕ) :
    exponentOnePart K n =
      (primeNormMultiplicity K n : ℝ) * Real.log (n : ℝ) := by
  classical
  let : Fintype (primeNormFiber K n) := Fintype.ofFinite _
  rw [exponentOnePart, ← Finset.sum_filter]
  rw [Finset.sum_subtype
    (p := fun x : IdealMangoldt.normFiber K n ↦ x.1.exponent = 1)
    (Finset.univ.filter fun x : IdealMangoldt.normFiber K n ↦ x.1.exponent = 1)
    (fun _ ↦ by simp)
    (fun x ↦ x.1.weight)]
  calc
    (∑ x : {x : IdealMangoldt.normFiber K n // x.1.exponent = 1}, x.1.1.weight) =
        ∑ 𝔭 : primeNormFiber K n, Real.log (n : ℝ) := by
      exact Fintype.sum_equiv (exponentOneNormFiberEquiv K n)
        (fun x : {x : IdealMangoldt.normFiber K n // x.1.exponent = 1} ↦ x.1.1.weight)
        (fun _ : primeNormFiber K n ↦ Real.log (n : ℝ)) fun x ↦ by
          rw [IdealMangoldt.PrimeIdealPower.weight]
          have hnorm : Ideal.absNorm x.1.1.prime = n := by
            simpa [IdealMangoldt.PrimeIdealPower.norm, x.2] using x.1.2
          rw [hnorm]
    _ = (primeNormMultiplicity K n : ℝ) * Real.log (n : ℝ) := by
      simp [primeNormMultiplicity, Nat.card_eq_fintype_card]

/-- Pointwise `Lambda_K = theta_K +` the contribution of proper prime-ideal powers. -/
theorem idealMangoldt_eq_primeNormMultiplicity_mul_log_add_higherPrimePowerPart (n : ℕ) :
    IdealMangoldt.idealMangoldt K n =
      (primeNormMultiplicity K n : ℝ) * Real.log (n : ℝ) +
        higherPrimePowerPart K n := by
  rw [idealMangoldt_eq_exponentOnePart_add_higherPrimePowerPart,
    exponentOnePart_eq_primeNormMultiplicity_mul_log]

/-- Proper prime-ideal powers contribute a nonnegative amount. -/
theorem higherPrimePowerPart_nonneg (n : ℕ) :
    0 ≤ higherPrimePowerPart K n := by
  rw [higherPrimePowerPart]
  exact Finset.sum_nonneg fun x _ ↦ by
    split_ifs
    · exact x.1.weight_nonneg
    · exact le_rfl

/-- The strict-endpoint prime-ideal Chebyshev function built from norm multiplicities. -/
def primeIdealTheta (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.range N,
    (primeNormMultiplicity K n : ℝ) * Real.log (n : ℝ)

/-- The generic logarithmically weighted coefficient count is the prime-ideal Chebyshev
function when its coefficient is the prime-norm multiplicity. -/
theorem coefficientLogWeightedCount_primeNormMultiplicity (N : ℕ) :
    coefficientLogWeightedCount (primeNormMultiplicity K) N = primeIdealTheta K N :=
  rfl

/-- The corresponding unweighted coefficient count through `N` is exactly the number of
nonzero prime ideals of norm at most `N`. -/
theorem coefficientCount_primeNormMultiplicity_eq_primeIdealCount (N : ℕ) :
    coefficientCount (primeNormMultiplicity K) (N + 1) =
      SplitTransfer.primeIdealCount K N :=
  coefficientCount_primeNormMultiplicity K N

/-- The strict-endpoint cumulative contribution of proper prime-ideal powers. -/
def higherPrimePowerChebyshev (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.range N, higherPrimePowerPart K n

/-- Exact cumulative `psi_K = theta_K + R_K` decomposition at every natural endpoint. -/
theorem sum_range_idealMangoldt_eq_primeNormTheta_add_higherPrimePowerChebyshev (N : ℕ) :
    (∑ n ∈ Finset.range N, IdealMangoldt.idealMangoldt K n) =
      primeIdealTheta K N + higherPrimePowerChebyshev K N := by
  simp_rw [idealMangoldt_eq_primeNormMultiplicity_mul_log_add_higherPrimePowerPart]
  simp only [primeIdealTheta, higherPrimePowerChebyshev, Finset.sum_add_distrib]

/-- The cumulative proper-prime-power contribution is nonnegative. -/
theorem higherPrimePowerChebyshev_nonneg (N : ℕ) :
    0 ≤ higherPrimePowerChebyshev K N := by
  rw [higherPrimePowerChebyshev]
  exact Finset.sum_nonneg fun n _ ↦ higherPrimePowerPart_nonneg K n

/-- Uniform boundedness of the norm multiplicity in the Galois situation used by the natural
Chebotarev application. -/
theorem primeNormMultiplicity_le_finrank
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L] [IsGalois ℚ L] (n : ℕ) :
    primeNormMultiplicity L n ≤ Module.finrank ℚ L :=
  PrimeNormMultiplicity.primeNormMultiplicity_le_degree L n

/-- There is no nonzero prime ideal whose norm is smaller than two. -/
theorem primeNormMultiplicity_eq_zero_of_lt_two {n : ℕ} (hn : n < 2) :
    primeNormMultiplicity K n = 0 := by
  let : IsEmpty (primeNormFiber K n) := ⟨fun 𝔭 ↦ by
    have hzero : Ideal.absNorm 𝔭.1.1 ≠ 0 :=
      fun h ↦ 𝔭.1.2.2 (Ideal.absNorm_eq_zero_iff.mp h)
    have hone : Ideal.absNorm 𝔭.1.1 ≠ 1 :=
      fun h ↦ 𝔭.1.2.1.ne_top (Ideal.absNorm_eq_one_iff.mp h)
    have hnorm := 𝔭.2
    omega⟩
  simp [primeNormMultiplicity]

/-- The generic multiplicity Chebyshev sum at an inclusive endpoint is the strict-endpoint
prime-ideal theta function at the successor. -/
theorem multiplicityChebyshev_primeNormMultiplicity (N : ℕ) :
    multiplicityChebyshev (fun n ↦ (primeNormMultiplicity K n : ℝ)) N =
      primeIdealTheta K (N + 1) := by
  rw [multiplicityChebyshev, primeIdealTheta, Nat.range_succ_eq_Icc_zero]
  apply Finset.sum_subset
  · intro n hn
    exact Finset.mem_Icc.mpr ⟨Nat.zero_le n, (Finset.mem_Icc.mp hn).2⟩
  · intro n hn hn'
    have hn2 : n < 2 := lt_of_not_ge fun h2 ↦
      hn' (Finset.mem_Icc.mpr ⟨h2, (Finset.mem_Icc.mp hn).2⟩)
    rw [primeNormMultiplicity_eq_zero_of_lt_two K hn2]
    simp

/-- The generic multiplicity count at an inclusive endpoint is the inclusive bounded
prime-ideal count. -/
theorem multiplicityCount_primeNormMultiplicity (N : ℕ) :
    multiplicityCount (fun n ↦ (primeNormMultiplicity K n : ℝ)) N =
      (SplitTransfer.primeIdealCount K N : ℝ) := by
  calc
    multiplicityCount (fun n ↦ (primeNormMultiplicity K n : ℝ)) N =
        ∑ n ∈ Finset.range (N + 1), (primeNormMultiplicity K n : ℝ) := by
      rw [multiplicityCount, Nat.range_succ_eq_Icc_zero]
      apply Finset.sum_subset
      · intro n hn
        exact Finset.mem_Icc.mpr ⟨Nat.zero_le n, (Finset.mem_Icc.mp hn).2⟩
      · intro n hn hn'
        have hn2 : n < 2 := lt_of_not_ge fun h2 ↦
          hn' (Finset.mem_Icc.mpr ⟨h2, (Finset.mem_Icc.mp hn).2⟩)
        rw [primeNormMultiplicity_eq_zero_of_lt_two K hn2]
        simp
    _ = (coefficientCount (primeNormMultiplicity K) (N + 1) : ℝ) := by
      simp [coefficientCount]
    _ = (SplitTransfer.primeIdealCount K N : ℝ) := by
      exact_mod_cast coefficientCount_primeNormMultiplicity_eq_primeIdealCount K N

end

end Erdos980.NaturalChebotarev.PrimeIdealTheorem
