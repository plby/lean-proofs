/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos822.FilteredEnergyFromAverage

/-!
# A beta-sieve upper bound for one prime progression

Putting the same affine form in both slots of the checked two-form sieve
gives the one-dimensional prime-progression estimate needed in the
first-moment argument.  The determinant is zero, so its pair local density
is exactly the one-shift density; only the prime slope itself is deleted.
-/

namespace Erdos822

open scoped BigOperators

theorem pairShiftDensity_zero_eq_oneShiftDensity (p : ℕ) :
    Erdos851.pairShiftDensity 0 p = Erdos851.oneShiftDensity p := by
  simp [Erdos851.pairShiftDensity, Erdos851.oneShiftDensity]

theorem localEulerProduct_pairShift_zero_eq_oneShift
    (z y : ℕ) :
    Erdos851.localEulerProduct (Erdos851.pairShiftDensity 0) z y =
      Erdos851.localEulerProduct Erdos851.oneShiftDensity z y := by
  unfold Erdos851.localEulerProduct
  apply Finset.prod_congr rfl
  intro p hp
  rw [pairShiftDensity_zero_eq_oneShiftDensity]

/-- For a prime slope, the deleted-slope reciprocal mass contains at most
the one slope prime itself. -/
theorem slopeReciprocalMass_prime_self_le_inv
    {p z y : ℕ} (hp : p.Prime) :
    slopeReciprocalMass p p z y ≤ (1 : ℝ) / p := by
  classical
  unfold slopeReciprocalMass
  by_cases hpMem : p ∈ Erdos851.sievePrimes z y
  · rw [Finset.sum_eq_single p]
    · simp
    · intro q hq hqp
      have hqPrime := (Erdos851.mem_sievePrimes.mp hq).2.2
      have hnot : ¬ q ∣ p := by
        intro hdiv
        have : q = p :=
          ((hp.dvd_iff_eq hqPrime.ne_one).mp hdiv).symm
        exact hqp this
      simp [hnot]
    · intro hnot
      exact (hnot hpMem).elim
  · have hzero :
        ∀ q ∈ Erdos851.sievePrimes z y,
          (if q ∣ p ∨ q ∣ p then (1 : ℝ) / q else 0) = 0 := by
      intro q hq
      have hqPrime := (Erdos851.mem_sievePrimes.mp hq).2.2
      have hnot : ¬ q ∣ p := by
        intro hdiv
        have hqp : q = p :=
          ((hp.dvd_iff_eq hqPrime.ne_one).mp hdiv).symm
        exact hpMem (hqp ▸ hq)
      simp [hnot]
    have hsum :
        (∑ q ∈ Erdos851.sievePrimes z y,
          if q ∣ p ∨ q ∣ p then (1 : ℝ) / q else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro q hq
      exact hzero q hq
    rw [hsum]
    positivity

/-- The slope loss for a duplicated prime-slope affine form is bounded by
the fixed constant exp 3. -/
theorem slopePrimeLoss_prime_self_le_exp_three
    {p y : ℕ} (hp : p.Prime) :
    slopePrimeLoss 0 p p 2 y ≤ Real.exp 3 := by
  calc
    slopePrimeLoss 0 p p 2 y ≤
        Real.exp (6 * slopeReciprocalMass p p 2 y) :=
      slopePrimeLoss_le_exp_slopeReciprocalMass 0 p p 2 y (by norm_num)
    _ ≤ Real.exp 3 := by
      apply Real.exp_le_exp.mpr
      have hpR : (2 : ℝ) ≤ p := by
        exact_mod_cast hp.two_le
      have hmass := slopeReciprocalMass_prime_self_le_inv
        (z := 2) (y := y) hp
      have hinv : (1 : ℝ) / p ≤ 1 / 2 := by
        exact one_div_le_one_div_of_le (by norm_num) hpR
      nlinarith

/-- Concrete dimension-one upper bound for primes in one affine
progression, expressed through the duplicated two-affine candidate set. -/
theorem exists_duplicateAffinePrimeCandidates_upper_bound :
    ∃ A C : ℝ, 1 ≤ A ∧ 0 < C ∧
      ∀ p q X y S : ℕ,
        p.Prime → q.Prime → y < q →
        2 ≤ y → 101 ≤ S →
        Real.log A ≤ 4 * (S - 100 : ℕ) / 99 →
        let eta := (4 * A / 3) * (1 / 4 : ℝ) ^ (S - 100)
        ((twoAffinePrimeCandidates p q p q X y).card : ℝ) ≤
          (X : ℝ) *
            ((1 + eta) *
              (C * (Real.log (2 : ℝ) / Real.log (y : ℝ)) *
                Real.exp 3)) +
            ((y ^ S : ℕ) : ℝ) ^ 2 := by
  obtain ⟨A, hA, hpair⟩ :=
    exists_twoAffinePrimeCandidates_slopeAware_pair_bound
  obtain ⟨C, hC, hMertens⟩ :=
    exists_oneShift_localEulerProduct_upper
  refine ⟨A, C, hA, hC, ?_⟩
  intro p q X y S hp hq hyq hy hS hlog
  dsimp only
  have hbound := hpair p p q q X 2 y S hq hq hyq hyq
    (by norm_num) (by omega) (by omega) hS hlog
  dsimp only at hbound
  have hdet : affineDetNat p q p q = 0 := by
    unfold affineDetNat
    simp
  rw [hdet, localEulerProduct_pairShift_zero_eq_oneShift] at hbound
  have hV :
      Erdos851.localEulerProduct Erdos851.oneShiftDensity 2 y ≤
        C * (Real.log (2 : ℝ) / Real.log (y : ℝ)) :=
    hMertens 2 y (by norm_num) (by omega)
  have hL : slopePrimeLoss 0 p p 2 y ≤ Real.exp 3 :=
    slopePrimeLoss_prime_self_le_exp_three hp
  have hV0 :
      0 ≤ Erdos851.localEulerProduct Erdos851.oneShiftDensity 2 y :=
    Erdos851.oneShift_localEulerProduct_pos.le
  have hL0 : 0 ≤ slopePrimeLoss 0 p p 2 y := by
    unfold slopePrimeLoss
    apply Finset.prod_nonneg
    intro r hr
    by_cases hrp : r ∣ p
    · simp only [hrp, or_self, if_true]
      exact (inv_nonneg.mpr
        (Erdos851.pairShift_localFactor_pos
          (Erdos851.mem_sievePrimes.mp hr).2.2
          (Erdos851.mem_sievePrimes.mp hr).1).le)
    · simp [hrp]
  have hright0 :
      0 ≤ C * (Real.log (2 : ℝ) / Real.log (y : ℝ)) := by
    have hlog2 : 0 ≤ Real.log (2 : ℝ) := Real.log_nonneg (by norm_num)
    have hlogy : 0 < Real.log (y : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < y by omega))
    positivity
  have hprod :
      Erdos851.localEulerProduct Erdos851.oneShiftDensity 2 y *
          slopePrimeLoss 0 p p 2 y ≤
        C * (Real.log (2 : ℝ) / Real.log (y : ℝ)) *
          Real.exp 3 := by
    exact mul_le_mul hV hL hL0 hright0
  have heta :
      0 ≤ 1 + (4 * A / 3) * (1 / 4 : ℝ) ^ (S - 100) := by
    positivity
  have hscaled :=
    mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hprod heta)
      (Nat.cast_nonneg X)
  exact hbound.trans (by
    simpa [mul_assoc] using
      (add_le_add_right hscaled (((y ^ S : ℕ) : ℝ) ^ 2)))

end Erdos822
