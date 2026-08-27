/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTEulerMajorant
import ErdosProblems.Erdos4b.FGKMTRoughPowerTail
import ErdosProblems.Erdos4b.FGKMTRoughWeights

/-!
# Uniform moments of the rough harmonic correction

The pre-sieve removes all primes up to the square of the dimension.
Outside it, the denominator differs from the prime by at most twice the
dimension and is at least half the prime. These explicit hypotheses give
an absolute quarter moment at most `exp 12`, independently of the
dimension, denominator function, and pre-sieve modulus.
-/

namespace Erdos4b.FGKMT

noncomputable section

open ArithmeticFunction
open scoped BigOperators

theorem rough_quarterMoment_bound {f : ArithmeticFunction ℝ} (hf : f.IsMultiplicative)
    {k : ℕ} (hk : 0 < k)
    (hsmall : ∀ p : ℕ, p.Prime → p ≤ k ^ 2 → f p = 0 ∧ f (p ^ 2) = 0)
    (hprime : ∀ p : ℕ, p.Prime → |f p| ≤ 4 * (k : ℝ) / (p : ℝ) ^ 2)
    (hsquare : ∀ p : ℕ, p.Prime → |f (p ^ 2)| ≤ 2 / (p : ℝ) ^ 2)
    (hhigh : ∀ p : ℕ, p.Prime → ∀ j, 3 ≤ j → f (p ^ j) = 0) :
    Summable (quarterMomentTerm f) ∧ (∑' n, quarterMomentTerm f n) ≤ Real.exp 12 := by
  have hlocalBound : ∀ p : ℕ, p.Prime →
      (∑' j, quarterMomentTerm f (p ^ j)) ≤ 1 + roughQuarterMajorant k p := by
    intro p hp
    by_cases hkp : k ^ 2 < p
    · rw [roughQuarterMajorant, if_pos hkp]
      exact quarterMomentTerm_local_tsum_le hf hp (by positivity) (hprime p hp)
        (hsquare p hp) (hhigh p hp)
    · obtain ⟨hp0, hp20⟩ := hsmall p hp (by omega)
      rw [quarterMomentTerm_local_tsum_eq hf (hhigh p hp), hp0, hp20,
        roughQuarterMajorant, if_neg hkp]
      simp
  have hprod : ∀ N : ℕ, (∏ p ∈ N.primesBelow, ∑' j, quarterMomentTerm f (p ^ j)) ≤
      Real.exp 12 := by
    intro N
    calc
      _ ≤ ∏ p ∈ N.primesBelow, (1 + roughQuarterMajorant k p) := by
        apply Finset.prod_le_prod
        · intro p _
          exact tsum_nonneg (fun j => quarterMomentTerm_nonneg f (p ^ j))
        · intro p hp
          exact hlocalBound p (Nat.prime_of_mem_primesBelow hp)
      _ ≤ Real.exp (∑ p ∈ N.primesBelow, roughQuarterMajorant k p) :=
        Real.prod_one_add_le_exp_sum _ (roughQuarterMajorant_nonneg k)
      _ ≤ Real.exp 12 := Real.exp_le_exp.mpr (sum_roughQuarterMajorant_primesBelow_le hk N)
  exact summable_and_tsum_le_of_local_products (quarterMomentTerm f)
    (by simp [quarterMomentTerm]) (by simp [quarterMomentTerm, hf.map_one])
    (quarterMomentTerm_nonneg f) (quarterMomentTerm_mul hf)
    (fun {p} hp => quarterMomentTerm_local_summable f (hhigh p hp)) hprod

theorem roughHarmonicCorrection_quarterMoment_bound {k M : ℕ} (hk : 0 < k)
    (hM : ∀ p : ℕ, p.Prime → p ≤ k ^ 2 → p ∣ M) (g : ℕ → ℝ)
    (hg : ∀ p : ℕ, p.Prime → ¬p ∣ M → (p : ℝ) / 2 ≤ g p)
    (hclose : ∀ p : ℕ, p.Prime → ¬p ∣ M → |g p - p| ≤ 2 * (k : ℝ)) :
    Summable (quarterMomentTerm (roughHarmonicCorrection M g)) ∧
      (∑' n, quarterMomentTerm (roughHarmonicCorrection M g) n) ≤ Real.exp 12 := by
  apply rough_quarterMoment_bound (roughHarmonicCorrection_isMultiplicative M g) hk
  · intro p hp hpk
    rw [roughHarmonicCorrection_prime M g hp, roughHarmonicCorrection_prime_sq M g hp]
    simp only [if_pos (hM p hp hpk), and_self]
  · intro p hp
    rw [roughHarmonicCorrection_prime M g hp]
    by_cases hpM : p ∣ M
    · rw [if_pos hpM, abs_zero]
      positivity
    · rw [if_neg hpM]
      exact harmonicCorrection_prime_bound (Nat.cast_nonneg k) (by exact_mod_cast hp.pos)
        (hg p hp hpM) (hclose p hp hpM)
  · intro p hp
    rw [roughHarmonicCorrection_prime_sq M g hp]
    by_cases hpM : p ∣ M
    · rw [if_pos hpM, abs_zero]
      positivity
    · rw [if_neg hpM]
      exact harmonicCorrection_primeSquare_bound (by exact_mod_cast hp.pos) (hg p hp hpM)
  · intro p hp j hj
    exact roughHarmonicCorrection_prime_pow_ge_three M g hp hj

theorem roughHarmonicCorrection_moments {k M : ℕ} (hk : 0 < k)
    (hM : ∀ p : ℕ, p.Prime → p ≤ k ^ 2 → p ∣ M) (g : ℕ → ℝ)
    (hg : ∀ p : ℕ, p.Prime → ¬p ∣ M → (p : ℝ) / 2 ≤ g p)
    (hclose : ∀ p : ℕ, p.Prime → ¬p ∣ M → |g p - p| ≤ 2 * (k : ℝ)) :
    Summable (fun n => |roughHarmonicCorrection M g n|) ∧
      (∑' n, |roughHarmonicCorrection M g n|) ≤ Real.exp 12 ∧
      Summable (fun n => |roughHarmonicCorrection M g n| * Real.log n) ∧
      (∑' n, |roughHarmonicCorrection M g n| * Real.log n) ≤ 4 * Real.exp 12 := by
  obtain ⟨hs, hsum⟩ := roughHarmonicCorrection_quarterMoment_bound hk hM g hg hclose
  exact moments_of_quarterMoment_summable _ hs hsum

/-- Every denominator arising while the unpinned coordinates are summed
successively satisfies the same absolute quarter-moment bound. -/
theorem shiftedDenominator_quarterMoment_bound {k M s : ℕ} (hk : 2 ≤ k) (hs : s ≤ k)
    (hM : ∀ p : ℕ, p.Prime → p ≤ 2 * k ^ 2 → p ∣ M) :
    Summable (quarterMomentTerm (roughHarmonicCorrection M (fun p => (p : ℝ) - k + s))) ∧
      (∑' n, quarterMomentTerm (roughHarmonicCorrection M
        (fun p => (p : ℝ) - k + s)) n) ≤ Real.exp 12 := by
  have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hsR : (s : ℝ) ≤ k := by exact_mod_cast hs
  have hrough : ∀ p : ℕ, p.Prime → ¬p ∣ M → 2 * (k : ℝ) ^ 2 < p := by
    intro p hp hpM
    have hlt : 2 * k ^ 2 < p := by
      by_contra hnot
      exact hpM (hM p hp (by omega))
    exact_mod_cast hlt
  apply roughHarmonicCorrection_quarterMoment_bound (by omega : 0 < k)
    (fun p hp hpk => hM p hp (by omega))
  · intro p hp hpM
    have hhalf := (rough_real_bounds hkR (hrough p hp hpM)).2
    have hs0 : (0 : ℝ) ≤ s := Nat.cast_nonneg s
    linarith
  · intro p _ _
    rw [abs_of_nonpos (by linarith : (p : ℝ) - k + s - p ≤ 0)]
    have hs0 : (0 : ℝ) ≤ s := Nat.cast_nonneg s
    linarith

/-- The slightly smaller pinned denominator is covered without replacing
it by `p - k`. -/
theorem pinnedDenominator_quarterMoment_bound {k M : ℕ} (hk : 2 ≤ k)
    (hM : ∀ p : ℕ, p.Prime → p ≤ 2 * k ^ 2 → p ∣ M) :
    Summable (quarterMomentTerm
      (roughHarmonicCorrection M (fun p => pinnedLocalDenominator k p))) ∧
      (∑' n, quarterMomentTerm
        (roughHarmonicCorrection M (fun p => pinnedLocalDenominator k p)) n) ≤ Real.exp 12 := by
  have hbounds : ∀ p : ℕ, p.Prime → ¬p ∣ M →
      (p : ℝ) / 2 < pinnedLocalDenominator k p ∧
        |pinnedLocalDenominator k p - p| ≤ 2 * (k : ℝ) := by
    intro p hp hpM
    have hlt : 2 * k ^ 2 < p := by
      by_contra hnot
      exact hpM (hM p hp (by omega))
    exact pinnedLocalDenominator_bounds (by exact_mod_cast hk) (by exact_mod_cast hlt)
  exact roughHarmonicCorrection_quarterMoment_bound (by omega : 0 < k)
    (fun p hp hpk => hM p hp (by omega)) _
    (fun p hp hpM => (hbounds p hp hpM).1.le)
    (fun p hp hpM => (hbounds p hp hpM).2)

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.roughHarmonicCorrection_moments
#print axioms Erdos4b.FGKMT.pinnedDenominator_quarterMoment_bound
