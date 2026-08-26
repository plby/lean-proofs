/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.GeneralCollisionSupport
import BoundedGaps.Maynard.PrimeMertens

/-!
# Uniform prime-divisor logarithmic mass

The exceptional integers in the doubled sieve need not be squarefree.
Split their prime factors at an independent threshold: Mertens controls
the small primes, and the radical-divides-modulus bound controls the rest.
-/

namespace Erdos4b

noncomputable section

open scoped BigOperators

theorem roughPrimeLogDivisorMass_le_primeMertens_add
    {P T : ℕ} (hP : 0 < P) (hT : 0 < T) (w : ℕ) :
    roughPrimeLogDivisorMass P w ≤
      BoundedGaps.Maynard.primeLogHarmonicSum T + Real.log P / T := by
  classical
  let low := P.primeFactors.filter fun p ↦ p ≤ T
  let high := P.primeFactors.filter fun p ↦ ¬p ≤ T
  have hsplit := Finset.sum_filter_add_sum_filter_not P.primeFactors
    (fun p ↦ p ≤ T) (fun p ↦ Real.log p / (p : ℝ))
  have hlow : (∑ p ∈ low, Real.log p / (p : ℝ)) ≤
      BoundedGaps.Maynard.primeLogHarmonicSum T := by
    unfold BoundedGaps.Maynard.primeLogHarmonicSum
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro p hp
      have hpData := Finset.mem_filter.mp hp
      exact Nat.mem_primesLE.mpr
        ⟨hpData.2, Nat.prime_of_mem_primeFactors hpData.1⟩
    · intro p hp hpnot
      positivity
  have hhigh : (∑ p ∈ high, Real.log p / (p : ℝ)) ≤ Real.log P / T := by
    simpa only [high, not_le, roughPrimeLogDivisorMass] using
      roughPrimeLogDivisorMass_le_log_div hP hT
  calc
    roughPrimeLogDivisorMass P w ≤
        ∑ p ∈ P.primeFactors, Real.log p / (p : ℝ) := by
      unfold roughPrimeLogDivisorMass
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      intro p hp hpnot
      positivity
    _ = (∑ p ∈ low, Real.log p / (p : ℝ)) +
        ∑ p ∈ high, Real.log p / (p : ℝ) := hsplit.symm
    _ ≤ _ := add_le_add hlow hhigh

theorem exists_uniform_roughPrimeLogDivisorMass_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {P T : ℕ}, 0 < P → 0 < T → ∀ w : ℕ,
      roughPrimeLogDivisorMass P w ≤ Real.log T + C + Real.log P / T := by
  obtain ⟨C, hC⟩ := BoundedGaps.Maynard.exists_uniform_abs_primeLogHarmonicSum_sub_log
  refine ⟨max C 0, le_max_right _ _, fun {P T} hP hT w ↦ ?_⟩
  have hmertens := (abs_le.mp (hC T)).2
  have hbase := roughPrimeLogDivisorMass_le_primeMertens_add hP hT w
  have hmax : C ≤ max C 0 := le_max_left _ _
  linarith

/-- A fixed logarithmic envelope for the exceptional integer can be
inserted before making the cutoff choice. -/
theorem roughPrimeLogDivisorMass_le_of_log_bound
    {P T : ℕ} {C B L : ℝ} (hP : 0 < P) (hT : 0 < T)
    (hC : ∀ {P T : ℕ}, 0 < P → 0 < T → ∀ w : ℕ,
      roughPrimeLogDivisorMass P w ≤ Real.log T + C + Real.log P / T)
    (hlog : Real.log P ≤ B * L) (w : ℕ) :
    roughPrimeLogDivisorMass P w ≤ Real.log T + C + B * L / T := by
  exact (hC hP hT w).trans
    (add_le_add le_rfl (div_le_div_of_nonneg_right hlog (Nat.cast_nonneg T)))

/-- Taking the splitting point at the ceiling of the logarithmic size
parameter yields a logarithm-of-logarithm bound, with no squarefreeness
assumption on the exceptional integer. -/
theorem exists_uniform_roughPrimeLogDivisorMass_log_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {P : ℕ} {B L : ℝ},
      0 < P → 0 ≤ B → 1 ≤ L → Real.log P ≤ B * L → ∀ w : ℕ,
      roughPrimeLogDivisorMass P w ≤ Real.log (L + 1) + C + B := by
  obtain ⟨C, hC, hmass⟩ := exists_uniform_roughPrimeLogDivisorMass_bound
  refine ⟨C, hC, fun {P B L} hP hB hL hlog w ↦ ?_⟩
  let T := Nat.ceil L
  have hLT : L ≤ (T : ℝ) := Nat.le_ceil L
  have hT0 : 0 < T := by
    have : (0 : ℝ) < T := lt_of_lt_of_le (by linarith) hLT
    exact_mod_cast this
  have hT0R : (0 : ℝ) < T := by exact_mod_cast hT0
  have hTupper : (T : ℝ) ≤ L + 1 :=
    (Nat.ceil_lt_add_one (by linarith : 0 ≤ L)).le
  have hlogs : Real.log T ≤ Real.log (L + 1) :=
    Real.log_le_log hT0R hTupper
  have hquot : B * L / T ≤ B := by
    apply (div_le_iff₀ hT0R).mpr
    exact mul_le_mul_of_nonneg_left hLT hB
  have hbase := roughPrimeLogDivisorMass_le_of_log_bound hP hT0 hmass hlog w
  linarith

end

end Erdos4b
