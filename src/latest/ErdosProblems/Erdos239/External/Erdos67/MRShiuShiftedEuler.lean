import ErdosProblems.Erdos239.External.Erdos67.MRShiuGlobalMean
import ErdosProblems.Erdos239.External.Erdos67.MRGlobalExpWeightedPrimeTail
import ErdosProblems.Erdos239.External.Erdos67.EulerQuantitative

/-!
# Scalarizing the shifted Shiu Euler exponent

This file is the finite scalar bridge from the generic global Shiu theorem
to the low/high split in source Lemma 2.4.  Low primes contribute their
ordinary reciprocal mass, shifted high primes contribute the uniformly
bounded exponential tail, and all higher prime powers contribute the fixed
quadratic Euler constant.
-/

open scoped BigOperators
open Finset

namespace Erdos67.MRShiu

noncomputable section

open Erdos67.PrimeEstimates Erdos67.EulerQuantitative

private theorem quadraticLocalTerm_le
    {p : ℕ} (hp : p.Prime) :
    1 / ((p : ℝ) * ((p : ℝ) - 1)) ≤
      2 * (p : ℝ) ^ (-2 : ℝ) := by
  have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  rw [Real.rpow_neg (by positivity), Real.rpow_two]
  have hden : (0 : ℝ) < (p : ℝ) * ((p : ℝ) - 1) := mul_pos hp0 hp1
  have hsq : (0 : ℝ) < (p : ℝ) ^ 2 := sq_pos_of_pos hp0
  change 1 / ((p : ℝ) * ((p : ℝ) - 1)) ≤ 2 / (p : ℝ) ^ 2
  rw [div_le_div_iff₀ hden hsq]
  nlinarith

/-- The entire higher-prime-power correction in the Shiu Euler exponent is
bounded by the repository's fixed quadratic Euler constant. -/
theorem sum_quadraticLocalTerm_le_primeQuadraticConstant (N : ℕ) :
    (∑ p ∈ (N + 1).primesBelow,
      1 / ((p : ℝ) * ((p : ℝ) - 1))) ≤ primeQuadraticConstant := by
  let e : {p // p ∈ (N + 1).primesBelow} → Nat.Primes :=
    fun p ↦ ⟨p, Nat.prime_of_mem_primesBelow p.property⟩
  have heinj : Function.Injective e := by
    intro p q hpq
    apply Subtype.ext
    exact congrArg (fun z : Nat.Primes ↦ (z : ℕ)) hpq
  let T : Finset Nat.Primes := Finset.univ.map ⟨e, heinj⟩
  let G : Nat.Primes → ℝ := fun p ↦ 2 * (p.1 : ℝ) ^ (-2 : ℝ)
  have hG : Summable G := by
    exact ((Real.summable_nat_rpow.mpr (by norm_num : (-2 : ℝ) < -1)).subtype
      Nat.Prime).mul_left 2
  have hsumEq :
      (∑ p ∈ (N + 1).primesBelow,
        2 * (p : ℝ) ^ (-2 : ℝ)) = ∑ p ∈ T, G p := by
    rw [Finset.sum_subtype (N + 1).primesBelow (fun _ ↦ Iff.rfl),
      Finset.sum_map]
    rfl
  calc
    (∑ p ∈ (N + 1).primesBelow,
        1 / ((p : ℝ) * ((p : ℝ) - 1))) ≤
        ∑ p ∈ (N + 1).primesBelow,
          2 * (p : ℝ) ^ (-2 : ℝ) := by
      apply Finset.sum_le_sum
      intro p hp
      exact quadraticLocalTerm_le (Nat.prime_of_mem_primesBelow hp)
    _ = ∑ p ∈ T, G p := hsumEq
    _ ≤ ∑' p : Nat.Primes, G p :=
      hG.sum_le_tsum T (fun _ _ ↦ by positivity)
    _ = primeQuadraticConstant := rfl

private theorem shiftedPrimeTerm_div_eq
    {y p : ℕ} (_hy : 2 ≤ y) (hp : p.Prime) :
    (p : ℝ) ^ (-(Real.log (y : ℝ))⁻¹) / (p : ℝ) =
      expWeightedPrimeTerm y p := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  rw [expWeightedPrimeTerm, show -(1 : ℝ) - (Real.log (y : ℝ))⁻¹ =
      (-(Real.log (y : ℝ))⁻¹) + (-1 : ℝ) by ring,
    Real.rpow_add hpR, Real.rpow_neg_one]
  rfl

/-- A low/high pointwise bound for the first prime coefficient scalarizes
to the reciprocal low-prime mass plus the global exponential tail. -/
theorem sum_primeTerm_le_low_add_expWeightedTail
    {h : ℕ → ℝ} {y N : ℕ} (hy : 2 ≤ y) (hyN : y ≤ N)
    (hprime : ∀ p : ℕ, p.Prime →
      h p ≤ if p ≤ y then 1 else
        (p : ℝ) ^ (-(Real.log (y : ℝ))⁻¹)) :
    (∑ p ∈ (N + 1).primesBelow, h p / (p : ℝ)) ≤
      primeReciprocals y + expWeightedPrimeTail y N := by
  let S := (N + 1).primesBelow
  have hpoint :
      (∑ p ∈ S, h p / (p : ℝ)) ≤
        ∑ p ∈ S, if p ≤ y then (p : ℝ)⁻¹ else
          expWeightedPrimeTerm y p := by
    apply Finset.sum_le_sum
    intro p hpS
    have hp := Nat.prime_of_mem_primesBelow hpS
    have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
    by_cases hpy : p ≤ y
    · simp only [hpy, if_true]
      calc
        h p / (p : ℝ) ≤ 1 / (p : ℝ) :=
          div_le_div_of_nonneg_right
            (by simpa [hpy] using hprime p hp) hpR.le
        _ = (p : ℝ)⁻¹ := one_div _
    · simp only [hpy, if_false]
      calc
        h p / (p : ℝ) ≤
            (p : ℝ) ^ (-(Real.log (y : ℝ))⁻¹) / (p : ℝ) :=
          div_le_div_of_nonneg_right (by simpa [hpy] using hprime p hp) hpR.le
        _ = expWeightedPrimeTerm y p := shiftedPrimeTerm_div_eq hy hp
  have hlowSet : S.filter (fun p ↦ p ≤ y) = Nat.primesLE y := by
    ext p
    simp only [S, Finset.mem_filter, Nat.mem_primesBelow, Nat.mem_primesLE]
    constructor
    · rintro ⟨⟨hpN, hp⟩, hpy⟩
      exact ⟨hpy, hp⟩
    · rintro ⟨hpy, hp⟩
      exact ⟨⟨by omega, hp⟩, hpy⟩
  have hhighSet : S.filter (fun p ↦ ¬ p ≤ y) = primesInInterval y N := by
    ext p
    simp only [S, Finset.mem_filter, Nat.mem_primesBelow, mem_primesInInterval]
    aesop
  calc
    (∑ p ∈ (N + 1).primesBelow, h p / (p : ℝ)) ≤
        ∑ p ∈ S, if p ≤ y then (p : ℝ)⁻¹ else
          expWeightedPrimeTerm y p := hpoint
    _ = (∑ p ∈ S.filter (fun p ↦ p ≤ y), (p : ℝ)⁻¹) +
          ∑ p ∈ S.filter (fun p ↦ ¬ p ≤ y),
            expWeightedPrimeTerm y p := by
      rw [← Finset.sum_filter_add_sum_filter_not S (fun p ↦ p ≤ y)
        (fun p ↦ if p ≤ y then (p : ℝ)⁻¹ else expWeightedPrimeTerm y p)]
      congr 1
      · apply Finset.sum_congr rfl
        intro p hp
        simp [(Finset.mem_filter.mp hp).2]
      · apply Finset.sum_congr rfl
        intro p hp
        simp [(Finset.mem_filter.mp hp).2]
    _ = primeReciprocals y + expWeightedPrimeTail y N := by
      rw [hlowSet, hhighSet]
      rfl

/-- Source-ready scalar bound for the full Shiu Euler exponent of a shifted
low/high multiplicative majorant. -/
theorem globalEulerExponent_le_shifted
    {h : ℕ → ℝ} {y N : ℕ} (hy : 2 ≤ y) (hyN : y ≤ N)
    (hprime : ∀ p : ℕ, p.Prime →
      h p ≤ if p ≤ y then 1 else
        (p : ℝ) ^ (-(Real.log (y : ℝ))⁻¹)) :
    globalEulerExponent h N ≤
      primeReciprocals y + (Real.log 2 + 2 * mertensBound) +
        primeQuadraticConstant := by
  have hfirst := sum_primeTerm_le_low_add_expWeightedTail hy hyN hprime
  have htail := expWeightedPrimeTail_le_log_two_add_global hy hyN
  have hquad := sum_quadraticLocalTerm_le_primeQuadraticConstant N
  unfold globalEulerExponent
  rw [Finset.sum_add_distrib]
  linarith

end

end Erdos67.MRShiu

#print axioms Erdos67.MRShiu.globalEulerExponent_le_shifted
