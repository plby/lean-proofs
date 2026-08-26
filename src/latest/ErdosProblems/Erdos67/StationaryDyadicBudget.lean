import ErdosProblems.Erdos67.StationaryPrimeResidues

/-!
# The global dyadic information budget

The conditional block entropies supply the actual potential in the telescoping
argument. Thus the bound is uniform in the number of prime bands, not merely
a bound for each band separately.
-/

open scoped BigOperators
open Finset MeasureTheory

namespace Erdos67.StationaryModel

open FiniteEntropy

def dyadicScale (m : ℕ) : ℕ := 2 ^ (m + 1)

theorem dyadicScale_pos (m : ℕ) : 0 < dyadicScale m := pow_pos (by norm_num) _

theorem dyadicScale_zero : dyadicScale 0 = 2 := rfl

theorem dyadicScale_succ (m : ℕ) : dyadicScale (m + 1) = dyadicScale m + dyadicScale m := by
  simp only [dyadicScale, pow_succ]
  omega

noncomputable def primeBlockInformation (Q : ProbabilityMeasure Configuration)
    (K L : ℕ) : ℝ :=
  conditionalMutualInfo (signResidueTripleLaw Q (signBlock (K * L))
    (continuous_signBlock _).measurable (bandModulus L) (belowModulus L))

theorem primeBlockInformation_nonneg (Q : ProbabilityMeasure Configuration) (K L : ℕ) :
    0 ≤ primeBlockInformation Q K L := conditionalMutualInfo_nonneg _

theorem primeBlockInformation_eq (Q : ProbabilityMeasure Configuration) (K L : ℕ) :
    primeBlockInformation Q K L = conditionedBlockEntropy Q (K * L) (belowModulus L) -
      conditionedBlockEntropy Q (K * L) (belowModulus (L + L)) :=
  prime_residue_information_eq Q (K * L) L

noncomputable def normalizedPrimeEntropy (Q : ProbabilityMeasure Configuration) (K L : ℕ) : ℝ :=
  conditionedBlockEntropy Q (K * L) (belowModulus L) / L

theorem normalizedPrimeEntropy_nonneg (Q : ProbabilityMeasure Configuration) (K L : ℕ) :
    0 ≤ normalizedPrimeEntropy Q K L :=
  div_nonneg (conditionedBlockEntropy_nonneg _ _ _) (Nat.cast_nonneg _)

theorem normalizedPrimeEntropy_le (Q : ProbabilityMeasure Configuration) (K L : ℕ)
    (hL : 0 < L) : normalizedPrimeEntropy Q K L ≤ (K : ℝ) * Real.log 2 := by
  apply (div_le_iff₀ (Nat.cast_pos.mpr hL)).2
  have hb := conditionedBlockEntropy_le Q (K * L) (belowModulus L)
  push_cast at hb
  nlinarith only [hb]

theorem normalizedPrimeEntropy_double_le (Q : ProbabilityMeasure Configuration)
    (hQ : Measure.map (shift 1) (Q : Measure Configuration) = (Q : Measure Configuration))
    (K L : ℕ) (hL : 0 < L) :
    normalizedPrimeEntropy Q K (L + L) ≤ normalizedPrimeEntropy Q K L -
      primeBlockInformation Q K L / L := by
  have hd := conditionedBlockEntropy_double_le Q hQ (K * L) (belowModulus (L + L))
  rw [← Nat.mul_add] at hd
  have hLr : 0 < (L : ℝ) := Nat.cast_pos.mpr hL
  rw [normalizedPrimeEntropy, normalizedPrimeEntropy, primeBlockInformation_eq]
  calc
    _ ≤ (2 * conditionedBlockEntropy Q (K * L) (belowModulus (L + L))) /
        ((L + L : ℕ) : ℝ) := div_le_div_of_nonneg_right hd (Nat.cast_nonneg _)
    _ = _ := by push_cast; field_simp; ring

theorem dyadic_prime_information_sum_le (Q : ProbabilityMeasure Configuration)
    (hQ : Measure.map (shift 1) (Q : Measure Configuration) = (Q : Measure Configuration))
    (K M : ℕ) :
    (∑ m ∈ range M, primeBlockInformation Q K (dyadicScale m) / dyadicScale m) ≤
      (K : ℝ) * Real.log 2 := by
  apply (StationaryEntropyBudget.sum_le_initial
    (fun m ↦ normalizedPrimeEntropy Q K (dyadicScale m))
    (fun m ↦ primeBlockInformation Q K (dyadicScale m) / dyadicScale m)
    (fun m ↦ normalizedPrimeEntropy_nonneg _ _ _) ?_ M).trans
      (normalizedPrimeEntropy_le Q K (dyadicScale 0) (dyadicScale_pos 0))
  intro m
  rw [dyadicScale_succ]
  exact normalizedPrimeEntropy_double_le Q hQ K _ (dyadicScale_pos m)

noncomputable def primeBandCorrelationError (Q : ProbabilityMeasure Configuration)
    (h L : ℕ) : ℝ :=
  ∑ p : PrimeBand L,
    (correlation Q (h : ℤ) - correlation Q (((bandModulus L p).val : ℤ) * (h : ℤ))) ^ 2

theorem primeBandCorrelationError_le (Q : ProbabilityMeasure Configuration)
    (hQ : Measure.map (shift 1) (Q : Measure Configuration) = (Q : Measure Configuration))
    (hCD : ∀ (d : ℕ+) (F : C((ℤ → Bool), ℝ)),
      (∫ ω, F ω.1 ∂(Q : Measure Configuration)) =
        (d.val : ℝ) * ∫ ω, conditionalDilationTest d F ω ∂(Q : Measure Configuration))
    (h L : ℕ) (hL : 0 < L) :
    primeBandCorrelationError Q h L ≤ 18 * primeBlockInformation Q (2 * h + 1) L := by
  apply correlation_errors_le_block_information Q hQ hCD L h hL
    (bandModulus L) (belowModulus L)
    (fun p ↦ p.property.2) ?_ (primeBand_below_coprime L)
  intro p
  have hp := p.val.isLt
  change p.val.val ≤ 2 * L
  omega

/-- Squared correlation errors have a uniformly bounded sum over all dyadic
prime bands with the natural reciprocal-scale weight. -/
theorem dyadic_correlation_error_sum_le (Q : ProbabilityMeasure Configuration)
    (hQ : Measure.map (shift 1) (Q : Measure Configuration) = (Q : Measure Configuration))
    (hCD : ∀ (d : ℕ+) (F : C((ℤ → Bool), ℝ)),
      (∫ ω, F ω.1 ∂(Q : Measure Configuration)) =
        (d.val : ℝ) * ∫ ω, conditionalDilationTest d F ω ∂(Q : Measure Configuration))
    (h M : ℕ) :
    (∑ m ∈ range M, primeBandCorrelationError Q h (dyadicScale m) / dyadicScale m) ≤
      18 * ((2 * h + 1 : ℕ) : ℝ) * Real.log 2 := by
  calc
    _ ≤ ∑ m ∈ range M,
        (18 * primeBlockInformation Q (2 * h + 1) (dyadicScale m)) / dyadicScale m := by
      apply sum_le_sum
      intro m _
      exact div_le_div_of_nonneg_right
        (primeBandCorrelationError_le Q hQ hCD h _ (dyadicScale_pos m)) (Nat.cast_nonneg _)
    _ = 18 * ∑ m ∈ range M,
        primeBlockInformation Q (2 * h + 1) (dyadicScale m) / dyadicScale m := by
      simp only [mul_div_assoc, mul_sum]
    _ ≤ 18 * (((2 * h + 1 : ℕ) : ℝ) * Real.log 2) :=
      mul_le_mul_of_nonneg_left (dyadic_prime_information_sum_le Q hQ (2 * h + 1) M) (by norm_num)
    _ = _ := by ring

end Erdos67.StationaryModel
