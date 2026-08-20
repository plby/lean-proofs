import CebotarevDensity.NumberFieldEulerProduct
import ErdosProblems.Erdos980.NaturalChebotarev.PrimeIdealTheorem.IdealCounting

/-!
# Elementary bounds for bounded ideals

This file packages the geometry-of-numbers bound on all nonzero integral ideals in the
form needed when prime ideals and prime powers are discarded from a weighted prime-ideal
sum.  The main counting function is deliberately unweighted and takes values in `ℕ`.
-/

namespace Erdos980.NaturalChebotarev.PrimeIdealTheorem

open Asymptotics Chebotarev Filter NumberField
open scoped BigOperators nonZeroDivisors

noncomputable section

variable (K : Type*) [Field K] [NumberField K]

/-- The number of nonzero integral ideals of `𝓞 K` whose absolute norm is at most `N`.

It is defined through the norm multiplicities which occur as the coefficients of the
Dedekind zeta function. -/
def allIdealCount (N : ℕ) : ℕ :=
  ∑ n ∈ Finset.Icc 1 N, idealNormMultiplicity K n

/-- The coefficient definition of `allIdealCount` is exactly the cardinality of the
bounded subtype of nonzero ideals. -/
theorem allIdealCount_eq_nonzeroIdeal_card (N : ℕ) :
    allIdealCount K N =
      Nat.card {I : NonzeroIdeal K // Ideal.absNorm I.1 ≤ N} := by
  exact Chebotarev.sum_idealNormMultiplicity_eq_card_norm_le K N

/-- The same count expressed using Mathlib's `nonZeroDivisors` subtype of ideals. -/
theorem allIdealCount_eq_nonZeroDivisor_card (N : ℕ) :
    allIdealCount K N =
      Nat.card {I : (Ideal (𝓞 K))⁰ // Ideal.absNorm I.1 ≤ N} := by
  rw [allIdealCount_eq_nonzeroIdeal_card K N,
    Chebotarev.card_nonzeroIdeal_norm_le_eq_card_nonZeroDivisor_norm_le K N]

@[simp]
theorem allIdealCount_zero : allIdealCount K 0 = 0 := by
  simp [allIdealCount]

/-- Enlarging the norm cutoff can only enlarge the all-ideal count. -/
theorem allIdealCount_mono : Monotone (allIdealCount K) := by
  intro M N hMN
  rw [allIdealCount_eq_nonzeroIdeal_card K M,
    allIdealCount_eq_nonzeroIdeal_card K N]
  have : Finite {I : NonzeroIdeal K // Ideal.absNorm I.1 ≤ N} := by
    have hfinite : {I : NonzeroIdeal K | Ideal.absNorm I.1 ≤ N}.Finite :=
      Set.Finite.preimage (f := fun I : NonzeroIdeal K ↦ I.1)
        (fun _ _ _ _ ↦ Subtype.ext)
        (Ideal.finite_setOfPred_absNorm_le (S := 𝓞 K) N)
    exact hfinite.to_subtype
  let f : {I : NonzeroIdeal K // Ideal.absNorm I.1 ≤ M} →
      {I : NonzeroIdeal K // Ideal.absNorm I.1 ≤ N} :=
    fun I ↦ ⟨I.1, I.2.trans hMN⟩
  exact Nat.card_le_card_of_injective f fun I J h ↦ by
    apply Subtype.ext
    exact congrArg (fun X : {I : NonzeroIdeal K // Ideal.absNorm I.1 ≤ N} ↦ X.1) h

/-- The all-ideal count is `O(N)`. -/
theorem allIdealCount_isBigO :
    (fun N : ℕ ↦ (allIdealCount K N : ℝ)) =O[atTop]
      (fun N : ℕ ↦ (N : ℝ)) := by
  simpa only [allIdealCount, Nat.cast_sum, Real.rpow_one] using
    (Chebotarev.sum_idealNormMultiplicity_isBigO K)

/-- An eventual explicit linear majorant for the all-ideal count.  The constant is chosen
nonnegative so it can be enlarged without changing the inequality. -/
theorem exists_eventually_allIdealCount_le_linear :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ N : ℕ in atTop, (allIdealCount K N : ℝ) ≤ C * (N : ℝ) := by
  obtain ⟨c, hc⟩ := Asymptotics.isBigO_iff.mp (allIdealCount_isBigO K)
  refine ⟨|c|, abs_nonneg c, hc.mono fun N hN ↦ ?_⟩
  rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _),
    Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)] at hN
  exact hN.trans (mul_le_mul_of_nonneg_right (le_abs_self c) (Nat.cast_nonneg N))

/-- A global linear majorant.  The finitely many values before the eventual bound begins
are absorbed by enlarging the constant to include the count at the threshold. -/
theorem exists_allIdealCount_le_linear :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ N : ℕ, (allIdealCount K N : ℝ) ≤ C * (N : ℝ) := by
  obtain ⟨C₀, hC₀, hC₀eventual⟩ := exists_eventually_allIdealCount_le_linear K
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp hC₀eventual
  refine ⟨max C₀ (allIdealCount K N₀ : ℝ),
    hC₀.trans (le_max_left _ _), fun N ↦ ?_⟩
  by_cases hNzero : N = 0
  · subst N
    simp
  by_cases hlarge : N₀ ≤ N
  · exact (hN₀ N hlarge).trans <|
      mul_le_mul_of_nonneg_right (le_max_left _ _) (Nat.cast_nonneg N)
  · have hsmall : N ≤ N₀ := Nat.le_of_lt (lt_of_not_ge hlarge)
    have hmono : allIdealCount K N ≤ allIdealCount K N₀ :=
      allIdealCount_mono K hsmall
    have hNone : (1 : ℝ) ≤ (N : ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr hNzero
    calc
      (allIdealCount K N : ℝ) ≤ (allIdealCount K N₀ : ℝ) := by exact_mod_cast hmono
      _ ≤ (allIdealCount K N₀ : ℝ) * (N : ℝ) := by
        calc
          (allIdealCount K N₀ : ℝ) = (allIdealCount K N₀ : ℝ) * 1 :=
            (mul_one _).symm
          _ ≤ (allIdealCount K N₀ : ℝ) * (N : ℝ) :=
            mul_le_mul_of_nonneg_left hNone (Nat.cast_nonneg _)
      _ ≤ max C₀ (allIdealCount K N₀ : ℝ) * (N : ℝ) :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) (Nat.cast_nonneg N)

/-- A natural-valued global constant version of `exists_allIdealCount_le_linear`. -/
theorem exists_allIdealCount_le_nat_mul :
    ∃ C : ℕ, ∀ N : ℕ, allIdealCount K N ≤ C * N := by
  obtain ⟨C, _hC, hbound⟩ := exists_allIdealCount_le_linear K
  refine ⟨⌈C⌉₊, fun N ↦ ?_⟩
  have hreal : (allIdealCount K N : ℝ) ≤ (⌈C⌉₊ : ℝ) * (N : ℝ) :=
    (hbound N).trans <|
      mul_le_mul_of_nonneg_right (Nat.le_ceil C) (Nat.cast_nonneg N)
  exact_mod_cast hreal

/-- Bounded nonzero prime ideals form a subcollection of all bounded nonzero ideals. -/
theorem card_primeIdeal_norm_le_le_allIdealCount (N : ℕ) :
    Nat.card {P : Ideal (𝓞 K) //
      P.IsPrime ∧ P ≠ ⊥ ∧ Ideal.absNorm P ≤ N} ≤ allIdealCount K N := by
  rw [allIdealCount_eq_nonZeroDivisor_card K N]
  have : Finite {I : (Ideal (𝓞 K))⁰ // Ideal.absNorm I.1 ≤ N} :=
    (Ideal.finite_setOfPred_absNorm_le₀ (S := 𝓞 K) N).to_subtype
  let f : {P : Ideal (𝓞 K) // P.IsPrime ∧ P ≠ ⊥ ∧ Ideal.absNorm P ≤ N} →
      {I : (Ideal (𝓞 K))⁰ // Ideal.absNorm I.1 ≤ N} :=
    fun P ↦ ⟨⟨P.1, mem_nonZeroDivisors_of_ne_zero P.2.2.1⟩, P.2.2.2⟩
  exact Nat.card_le_card_of_injective f fun P Q h ↦ by
    exact Subtype.ext (congrArg (fun I ↦ (I.1 : Ideal (𝓞 K))) h)

end

end Erdos980.NaturalChebotarev.PrimeIdealTheorem
