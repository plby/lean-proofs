import ErdosProblems.Erdos239.External.Erdos67.MRGranvilleSoundararajanVariation
import ErdosProblems.Erdos239.External.Erdos67.ArchimedeanPrimeExtension
import ErdosProblems.Erdos239.External.Erdos67.PrimeEstimates
import Mathlib.Analysis.PSeries

/-!
# The pretentious Euler exponent in the GS near-twist case

The Halberstam--Richert variation bound is useful for a function which is
close to `n ↦ n^(it)`.  This file applies it to the untwisted coefficient
`f(n) * conj (n^(it))`.  Cauchy--Schwarz bounds the linear prime discrepancy
in its Euler exponent by the square root of the pretentious distance times
the reciprocal-prime mass.  The prime-power tail is bounded absolutely.
-/

open scoped BigOperators ComplexConjugate
open Finset

namespace Erdos67

noncomputable section

/-- Remove an Archimedean twist from a multiplicative coefficient. -/
def archimedeanUntwist (f : ℕ → ℂ) (t : ℝ) (n : ℕ) : ℂ :=
  if n = 0 then 0 else f n * conj (archimedeanTwist t n)

theorem archimedeanUntwist_isMultiplicative
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f) (t : ℝ) :
    IsMultiplicativeOnPositiveNat (archimedeanUntwist f t) := by
  refine ⟨?_, ?_⟩
  · simp [archimedeanUntwist, hmul.1, archimedeanTwist]
  · intro m n hm hn hcop
    rw [archimedeanUntwist, archimedeanUntwist, archimedeanUntwist,
      if_neg (Nat.mul_ne_zero hm.ne' hn.ne'), if_neg hm.ne', if_neg hn.ne',
      hmul.2 m n hm hn hcop, archimedeanTwist_mul t hm hn, map_mul]
    ring

theorem norm_archimedeanUntwist_le_one
    {f : ℕ → ℂ} (hone : ∀ n : ℕ, ‖f n‖ ≤ 1) (t : ℝ) (n : ℕ) :
    ‖archimedeanUntwist f t n‖ ≤ 1 := by
  by_cases hn : n = 0
  · subst n
    simp [archimedeanUntwist]
  rw [archimedeanUntwist, if_neg hn, norm_mul, Complex.norm_conj,
    norm_archimedeanTwist (Nat.pos_of_ne_zero hn), mul_one]
  exact hone n

/-- The squared prime discrepancy of the untwisted coefficient is at most
twice the corresponding pretentious numerator. -/
theorem norm_archimedeanUntwist_sub_one_sq_le
    {f : ℕ → ℂ} (hone : ∀ n : ℕ, ‖f n‖ ≤ 1)
    {p : ℕ} (hp : p.Prime) (t : ℝ) :
    ‖archimedeanUntwist f t p - 1‖ ^ 2 ≤
      2 * (1 - (f p * conj (archimedeanTwist t p)).re) := by
  have hu : ‖archimedeanUntwist f t p‖ ≤ 1 :=
    norm_archimedeanUntwist_le_one hone t p
  have hsq : ‖archimedeanUntwist f t p‖ ^ 2 ≤ 1 := by
    nlinarith [norm_nonneg (archimedeanUntwist f t p)]
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_sub]
  simp only [Complex.normSq_eq_norm_sq, Complex.normSq_one,
    map_one, mul_one]
  change ‖archimedeanUntwist f t p‖ ^ 2 + 1 -
      2 * (archimedeanUntwist f t p).re ≤
    2 * (1 - (f p * conj (archimedeanTwist t p)).re)
  have hdef : archimedeanUntwist f t p =
      f p * conj (archimedeanTwist t p) := by
    simp [archimedeanUntwist, hp.ne_zero]
  rw [← hdef]
  linarith

private theorem primesUpTo_eq_primesLE (N : ℕ) :
    primesUpTo N = Nat.primesLE N := by
  ext p
  simp [Nat.mem_primesLE, and_comm]

/-- Weighted finite Cauchy--Schwarz in the exact prime notation used by the
pretentious distance. -/
theorem sq_sum_norm_archimedeanUntwist_sub_one_div_le
    {f : ℕ → ℂ} (hone : ∀ n : ℕ, ‖f n‖ ≤ 1)
    (t : ℝ) (N : ℕ) :
    (∑ p ∈ primesUpTo N,
        ‖archimedeanUntwist f t p - 1‖ / (p : ℝ)) ^ 2 ≤
      2 * pretentiousDistSq f (archimedeanTwist t) N *
        PrimeEstimates.primeReciprocals N := by
  let r : ℕ → ℝ := fun p => ‖archimedeanUntwist f t p - 1‖ / (p : ℝ)
  let a : ℕ → ℝ := fun p => ‖archimedeanUntwist f t p - 1‖ ^ 2 / (p : ℝ)
  let b : ℕ → ℝ := fun p => 1 / (p : ℝ)
  have hpPos (p : ℕ) (hp : p ∈ primesUpTo N) : (0 : ℝ) < p := by
    exact_mod_cast (mem_primesUpTo.mp hp).1.pos
  have hcs :
      (∑ p ∈ primesUpTo N, r p) ^ 2 ≤
        (∑ p ∈ primesUpTo N, a p) *
          ∑ p ∈ primesUpTo N, b p := by
    apply sum_sq_le_sum_mul_sum_of_sq_le_mul
    · intro p hp
      exact div_nonneg (sq_nonneg _) (le_of_lt (hpPos p hp))
    · intro p hp
      exact div_nonneg zero_le_one (le_of_lt (hpPos p hp))
    · intro p hp
      dsimp [r, a, b]
      field_simp [ne_of_gt (hpPos p hp)]
      simpa [sub_eq_add_neg, add_comm]
  have ha : (∑ p ∈ primesUpTo N, a p) ≤
      2 * pretentiousDistSq f (archimedeanTwist t) N := by
    unfold pretentiousDistSq
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro p hp
    have hp' := (mem_primesUpTo.mp hp).1
    dsimp [a, pretentiousTerm]
    have hpoint := norm_archimedeanUntwist_sub_one_sq_le hone hp' t
    have hp0 : (0 : ℝ) ≤ p := le_of_lt (hpPos p hp)
    calc
      ‖archimedeanUntwist f t p - 1‖ ^ 2 / (p : ℝ) ≤
          (2 * (1 - (f p * conj (archimedeanTwist t p)).re)) / (p : ℝ) :=
        div_le_div_of_nonneg_right hpoint hp0
      _ = 2 * ((1 - (f p * conj (archimedeanTwist t p)).re) / (p : ℝ)) := by
        ring
  have hb : (∑ p ∈ primesUpTo N, b p) =
      PrimeEstimates.primeReciprocals N := by
    rw [primesUpTo_eq_primesLE]
    simp [b, PrimeEstimates.primeReciprocals,
      Erdos784.Analytic.primeReciprocals, one_div]
  have hdist0 : 0 ≤ pretentiousDistSq f (archimedeanTwist t) N := by
    apply pretentiousDistSq_nonneg
    · intro p hp
      exact hone p
    · intro p hp
      exact (norm_archimedeanTwist hp.pos t).le
  have hprime0 : 0 ≤ PrimeEstimates.primeReciprocals N :=
    PrimeEstimates.primeReciprocals_nonneg N
  change (∑ p ∈ primesUpTo N, r p) ^ 2 ≤ _
  rw [hb] at hcs
  exact hcs.trans (mul_le_mul ha le_rfl hprime0 (by positivity))

/-- The summable prime-power tail in the GS Euler exponent is bounded by
an absolute constant.  The coarse constant `8` keeps the statement fully
elementary. -/
theorem sum_primePowerTail_le_eight (N : ℕ) :
    (∑ p ∈ (N + 1).primesBelow,
        2 / ((p : ℝ) * ((p : ℝ) - 1))) ≤ 8 := by
  have hsubset : (N + 1).primesBelow ⊆ Finset.Ioo 0 (N + 1) := by
    intro p hp
    have hp' := Nat.prime_of_mem_primesBelow hp
    simp only [Finset.mem_Ioo]
    exact ⟨hp'.pos, Nat.lt_of_mem_primesBelow hp⟩
  calc
    (∑ p ∈ (N + 1).primesBelow,
        2 / ((p : ℝ) * ((p : ℝ) - 1))) ≤
        ∑ p ∈ (N + 1).primesBelow, 4 * ((p ^ 2 : ℕ) : ℝ)⁻¹ := by
      apply Finset.sum_le_sum
      intro p hp
      have hp' := Nat.prime_of_mem_primesBelow hp
      have hp2R : (2 : ℝ) ≤ p := by exact_mod_cast hp'.two_le
      have hpPos : (0 : ℝ) < p := by positivity
      have hpmPos : (0 : ℝ) < (p : ℝ) - 1 := by linarith
      rw [Nat.cast_pow]
      rw [show ((p : ℝ) ^ 2)⁻¹ = 1 / ((p : ℝ) ^ 2) by simp [one_div]]
      rw [show 4 * (1 / (p : ℝ) ^ 2) = 4 / (p : ℝ) ^ 2 by ring]
      apply (div_le_div_iff₀ (mul_pos hpPos hpmPos)
        (by positivity : (0 : ℝ) < (p : ℝ) ^ 2)).2
      nlinarith
    _ ≤ ∑ p ∈ Finset.Ioo 0 (N + 1), 4 * ((p ^ 2 : ℕ) : ℝ)⁻¹ := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
      intro p hp _
      positivity
    _ = 4 * ∑ p ∈ Finset.Ioo 0 (N + 1), ((p ^ 2 : ℕ) : ℝ)⁻¹ := by
      rw [Finset.mul_sum]
    _ ≤ 4 * (2 / ((0 + 1 : ℕ) : ℝ)) := by
      gcongr
      simpa only [Nat.cast_pow, Nat.cast_zero, Nat.cast_add, Nat.cast_one] using
        (sum_Ioo_inv_sq_le (α := ℝ) 0 (N + 1))
    _ = 8 := by norm_num

/-- The complete GS Euler exponent of the untwisted coefficient: a
pretentious Cauchy--Schwarz term plus an absolute prime-power tail. -/
theorem gsEulerExponent_archimedeanUntwist_le
    {f : ℕ → ℂ} (hone : ∀ n : ℕ, ‖f n‖ ≤ 1)
    (t : ℝ) (N : ℕ) :
    gsEulerExponent (archimedeanUntwist f t) N ≤
      Real.sqrt (2 * pretentiousDistSq f (archimedeanTwist t) N *
        PrimeEstimates.primeReciprocals N) + 8 := by
  have hsquare := sq_sum_norm_archimedeanUntwist_sub_one_div_le hone t N
  have hsum0 : 0 ≤ ∑ p ∈ primesUpTo N,
      ‖archimedeanUntwist f t p - 1‖ / (p : ℝ) := by
    exact Finset.sum_nonneg fun p hp => div_nonneg (norm_nonneg _) (Nat.cast_nonneg _)
  have hsqrt : (∑ p ∈ primesUpTo N,
      ‖archimedeanUntwist f t p - 1‖ / (p : ℝ)) ≤
      Real.sqrt (2 * pretentiousDistSq f (archimedeanTwist t) N *
        PrimeEstimates.primeReciprocals N) := by
    have hdist0 : 0 ≤ pretentiousDistSq f (archimedeanTwist t) N := by
      apply pretentiousDistSq_nonneg
      · intro p hp
        exact hone p
      · intro p hp
        exact (norm_archimedeanTwist hp.pos t).le
    have hprime0 : 0 ≤ PrimeEstimates.primeReciprocals N :=
      PrimeEstimates.primeReciprocals_nonneg N
    exact (Real.le_sqrt hsum0
      (mul_nonneg (mul_nonneg (by positivity) hdist0) hprime0)).2 hsquare
  have hsets : (N + 1).primesBelow = primesUpTo N := by
    ext p
    simp [Nat.mem_primesBelow, mem_primesUpTo, and_comm]
  unfold gsEulerExponent
  rw [Finset.sum_add_distrib]
  rw [hsets]
  exact add_le_add hsqrt (by simpa [hsets] using sum_primePowerTail_le_eight N)

end

end Erdos67
