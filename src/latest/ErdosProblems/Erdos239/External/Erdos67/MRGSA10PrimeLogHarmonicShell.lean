import ErdosProblems.Erdos239.External.Erdos67.MRGSA10PrimeGaussianNearRow

/-!
# Logarithmic prime mass on multiplicative shells

The uniform bounded-error prime-log Mertens estimate immediately controls the
logarithmically weighted prime mass of `(A,B]`.  This file packages that
subtraction argument, its factor-four specialization, and subset forms that
can be applied directly inside `gsA10PrimeWindow`.
-/

open scoped BigOperators

namespace Erdos67.MRHalaszBands

noncomputable section

open BoundedGaps.Maynard

/-- The logarithmically weighted prime mass of the natural interval `(A,B]`. -/
def gsA10PrimeLogHarmonicInterval (A B : ℕ) : ℝ :=
  ∑ p ∈ PrimeEstimates.primesInInterval A B, Real.log p / (p : ℝ)

/-- Splitting the prime prefix at `A` identifies the logarithmic mass of
`(A,B]` with the difference of two prime-log harmonic sums. -/
theorem gsA10PrimeLogHarmonicInterval_eq_sub {A B : ℕ} (hAB : A ≤ B) :
    gsA10PrimeLogHarmonicInterval A B =
      primeLogHarmonicSum B - primeLogHarmonicSum A := by
  classical
  have hsplit : Nat.primesLE B =
      Nat.primesLE A ∪ PrimeEstimates.primesInInterval A B := by
    ext p
    simp only [Nat.mem_primesLE, Finset.mem_union,
      PrimeEstimates.mem_primesInInterval]
    constructor
    · intro hp
      by_cases hpA : p ≤ A
      · exact Or.inl ⟨hpA, hp.2⟩
      · exact Or.inr ⟨by omega, hp.1, hp.2⟩
    · rintro (hp | hp)
      · exact ⟨hp.1.trans hAB, hp.2⟩
      · exact ⟨hp.2.1, hp.2.2⟩
  have hdisj : Disjoint (Nat.primesLE A)
      (PrimeEstimates.primesInInterval A B) := by
    apply Finset.disjoint_left.mpr
    intro p hpA hpI
    have hpAle := (Nat.mem_primesLE.mp hpA).1
    have hpAlt := (PrimeEstimates.mem_primesInInterval.mp hpI).1
    omega
  unfold gsA10PrimeLogHarmonicInterval primeLogHarmonicSum
  rw [hsplit, Finset.sum_union hdisj]
  ring

/-- The two-sided uniform Mertens estimate, subtracted at the endpoints of
`(A,B]`.  The positivity assumption on `A` is exactly what is needed to write
the main term as `log (B/A)`. -/
theorem gsA10PrimeLogHarmonicInterval_le_log_div_add_two_mertens
    {A B : ℕ} (hA : 0 < A) (hAB : A ≤ B) :
    gsA10PrimeLogHarmonicInterval A B ≤
      Real.log ((B : ℝ) / (A : ℝ)) + 2 * primeLogMertensConstant := by
  have hB : 0 < B := hA.trans_le hAB
  have hupperB := (abs_le.mp (primeLogMertensConstant_spec B)).2
  have hlowerA := (abs_le.mp (primeLogMertensConstant_spec A)).1
  rw [gsA10PrimeLogHarmonicInterval_eq_sub hAB]
  rw [Real.log_div (Nat.cast_ne_zero.mpr hB.ne')
    (Nat.cast_ne_zero.mpr hA.ne')]
  linarith

/-- A factor-four prime shell has uniformly bounded logarithmic prime mass. -/
theorem gsA10PrimeLogHarmonicInterval_le_log_four_add_two_mertens
    {A B : ℕ} (hA : 0 < A) (hAB : A ≤ B) (hB4A : B ≤ 4 * A) :
    gsA10PrimeLogHarmonicInterval A B ≤
      Real.log 4 + 2 * primeLogMertensConstant := by
  have hAreal : 0 < (A : ℝ) := by exact_mod_cast hA
  have hratio : (B : ℝ) / (A : ℝ) ≤ 4 := by
    rw [div_le_iff₀ hAreal]
    exact_mod_cast hB4A
  calc
    gsA10PrimeLogHarmonicInterval A B ≤
        Real.log ((B : ℝ) / (A : ℝ)) +
          2 * primeLogMertensConstant :=
      gsA10PrimeLogHarmonicInterval_le_log_div_add_two_mertens hA hAB
    _ ≤ Real.log 4 + 2 * primeLogMertensConstant := by
      have hlog := Real.log_le_log
        (div_pos (by exact_mod_cast hA.trans_le hAB) hAreal) hratio
      linarith

/-- Exact `(A,4A]` form of the uniform factor-four shell bound. -/
theorem gsA10PrimeLogHarmonicInterval_mul_four_le
    {A : ℕ} (hA : 0 < A) :
    gsA10PrimeLogHarmonicInterval A (4 * A) ≤
      Real.log 4 + 2 * primeLogMertensConstant := by
  exact gsA10PrimeLogHarmonicInterval_le_log_four_add_two_mertens
    hA (Nat.le_mul_of_pos_left A (by norm_num)) le_rfl

/-- The universal constant controlling every factor-four shell. -/
def gsA10PrimeLogHarmonicFactorFourConstant : ℝ :=
  Real.log 4 + 2 * primeLogMertensConstant

theorem gsA10PrimeLogHarmonicFactorFourConstant_nonneg :
    0 ≤ gsA10PrimeLogHarmonicFactorFourConstant := by
  unfold gsA10PrimeLogHarmonicFactorFourConstant
  exact add_nonneg (Real.log_nonneg (by norm_num))
    (mul_nonneg (by norm_num) Erdos67.primeLogMertensConstant_nonneg)

/-- Any finite subset of the primes in `(A,B]` inherits the same Mertens
bound.  This is the convenient abstract form for filtered prime supports. -/
theorem sum_primeLog_div_subset_interval_le_log_div_add_two_mertens
    {S : Finset ℕ} {A B : ℕ}
    (hA : 0 < A) (hAB : A ≤ B)
    (hS : S ⊆ PrimeEstimates.primesInInterval A B) :
    (∑ p ∈ S, Real.log p / (p : ℝ)) ≤
      Real.log ((B : ℝ) / (A : ℝ)) + 2 * primeLogMertensConstant := by
  calc
    (∑ p ∈ S, Real.log p / (p : ℝ)) ≤
        gsA10PrimeLogHarmonicInterval A B := by
      unfold gsA10PrimeLogHarmonicInterval
      apply Finset.sum_le_sum_of_subset_of_nonneg hS
      intro p hpI _
      have hp := (PrimeEstimates.mem_primesInInterval.mp hpI).2.2
      exact div_nonneg (Real.log_nonneg (by exact_mod_cast hp.one_le)) (by positivity)
    _ ≤ _ :=
      gsA10PrimeLogHarmonicInterval_le_log_div_add_two_mertens hA hAB

/-- Predicate-style version of the subset bound, avoiding a separate Finset
inclusion proof at call sites. -/
theorem sum_primeLog_div_of_mem_interval_le_log_div_add_two_mertens
    {S : Finset ℕ} {A B : ℕ}
    (hA : 0 < A) (hAB : A ≤ B)
    (hS : ∀ p ∈ S, A < p ∧ p ≤ B ∧ p.Prime) :
    (∑ p ∈ S, Real.log p / (p : ℝ)) ≤
      Real.log ((B : ℝ) / (A : ℝ)) + 2 * primeLogMertensConstant := by
  apply sum_primeLog_div_subset_interval_le_log_div_add_two_mertens hA hAB
  intro p hp
  exact PrimeEstimates.mem_primesInInterval.mpr (hS p hp)

/-- Factor-four specialization for an arbitrary finite subset of `(A,B]`. -/
theorem sum_primeLog_div_subset_interval_le_factorFourConstant
    {S : Finset ℕ} {A B : ℕ}
    (hA : 0 < A) (hAB : A ≤ B) (hB4A : B ≤ 4 * A)
    (hS : S ⊆ PrimeEstimates.primesInInterval A B) :
    (∑ p ∈ S, Real.log p / (p : ℝ)) ≤
      gsA10PrimeLogHarmonicFactorFourConstant := by
  have hmain :=
    sum_primeLog_div_subset_interval_le_log_div_add_two_mertens hA hAB hS
  unfold gsA10PrimeLogHarmonicFactorFourConstant
  have hAreal : 0 < (A : ℝ) := by exact_mod_cast hA
  have hratio : (B : ℝ) / (A : ℝ) ≤ 4 := by
    rw [div_le_iff₀ hAreal]
    exact_mod_cast hB4A
  have hlog := Real.log_le_log
    (div_pos (by exact_mod_cast hA.trans_le hAB) hAreal) hratio
  linarith

/-- A subset of `gsA10PrimeWindow` lying in `(A,B]` satisfies the same exact
shell estimate; primality is supplied by the ambient A.10 window. -/
theorem sum_primeLog_div_subset_gsA10PrimeWindow_le_log_div_add_two_mertens
    {S : Finset ℕ} {y X A B : ℕ}
    (hA : 0 < A) (hAB : A ≤ B)
    (hWindow : S ⊆ gsA10PrimeWindow y X)
    (hShell : ∀ p ∈ S, A < p ∧ p ≤ B) :
    (∑ p ∈ S, Real.log p / (p : ℝ)) ≤
      Real.log ((B : ℝ) / (A : ℝ)) + 2 * primeLogMertensConstant := by
  apply sum_primeLog_div_of_mem_interval_le_log_div_add_two_mertens hA hAB
  intro p hp
  exact ⟨(hShell p hp).1, (hShell p hp).2,
    (mem_gsA10PrimeWindow.mp (hWindow hp)).2.2⟩

/-- Ready-to-use exact-ratio bound for the `(A,B]` filter of the A.10 prime
window. -/
theorem sum_primeLog_div_gsA10PrimeWindow_filter_Ioc_le_log_div_add_two_mertens
    {y X A B : ℕ} (hA : 0 < A) (hAB : A ≤ B) :
    (∑ p ∈ (gsA10PrimeWindow y X).filter
        (fun p ↦ p ∈ Finset.Ioc A B), Real.log p / (p : ℝ)) ≤
      Real.log ((B : ℝ) / (A : ℝ)) + 2 * primeLogMertensConstant := by
  apply sum_primeLog_div_subset_gsA10PrimeWindow_le_log_div_add_two_mertens
    hA hAB
  · exact Finset.filter_subset _ _
  · intro p hp
    exact Finset.mem_Ioc.mp (Finset.mem_filter.mp hp).2

/-- Ready-to-use uniform factor-four bound for a filtered A.10 prime window. -/
theorem sum_primeLog_div_gsA10PrimeWindow_filter_Ioc_le_factorFourConstant
    {y X A B : ℕ} (hA : 0 < A) (hAB : A ≤ B) (hB4A : B ≤ 4 * A) :
    (∑ p ∈ (gsA10PrimeWindow y X).filter
        (fun p ↦ p ∈ Finset.Ioc A B), Real.log p / (p : ℝ)) ≤
      gsA10PrimeLogHarmonicFactorFourConstant := by
  have hmain :=
    sum_primeLog_div_gsA10PrimeWindow_filter_Ioc_le_log_div_add_two_mertens
      (y := y) (X := X) hA hAB
  unfold gsA10PrimeLogHarmonicFactorFourConstant
  have hAreal : 0 < (A : ℝ) := by exact_mod_cast hA
  have hratio : (B : ℝ) / (A : ℝ) ≤ 4 := by
    rw [div_le_iff₀ hAreal]
    exact_mod_cast hB4A
  have hlog := Real.log_le_log
    (div_pos (by exact_mod_cast hA.trans_le hAB) hAreal) hratio
  linarith

/-- Exact `(A,4A]` filtered-window wrapper. -/
theorem sum_primeLog_div_gsA10PrimeWindow_filter_Ioc_mul_four_le
    {y X A : ℕ} (hA : 0 < A) :
    (∑ p ∈ (gsA10PrimeWindow y X).filter
        (fun p ↦ p ∈ Finset.Ioc A (4 * A)), Real.log p / (p : ℝ)) ≤
      gsA10PrimeLogHarmonicFactorFourConstant := by
  exact sum_primeLog_div_gsA10PrimeWindow_filter_Ioc_le_factorFourConstant
    hA (Nat.le_mul_of_pos_left A (by norm_num)) le_rfl

end

end Erdos67.MRHalaszBands
