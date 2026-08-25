import ErdosProblems.Erdos67.MRGSA10HalfEndpointOrdinary

/-!
# Scalar ordinary-multiplicative A.10 half-endpoint bound

The fixed endpoint divisor triples are reindexed before estimation.  Once
divided by `X`, every distinguished pair is bounded by the product of its
two reciprocal masses; hence no divisor-count loss occurs.
-/

open scoped BigOperators
open Finset

namespace Erdos67.MRHalaszBands

noncomputable section

open BoundedGaps.Maynard

/-- Reciprocal prime mass used by the endpoint estimate. -/
def gsA10HalfEndpointPrimeMass (X : ℕ) : ℝ :=
  2 * (Real.log 4 + 4) * (Nat.log 2 X : ℝ)

/-- The explicit ordinary higher-prime-power reciprocal-mass envelope. -/
def gsA10HalfEndpointHPPMassBound (y X : ℕ) : ℝ :=
  12 * Real.log X / y * PrimeEstimates.primeReciprocals X

theorem gsA10HalfEndpointPrimeMass_nonneg (X : ℕ) :
    0 ≤ gsA10HalfEndpointPrimeMass X := by
  unfold gsA10HalfEndpointPrimeMass
  positivity

theorem gsA10HalfEndpointHPPMassBound_nonneg
    {y X : ℕ} (hy : 0 < y) (hX : 1 ≤ X) :
    0 ≤ gsA10HalfEndpointHPPMassBound y X := by
  unfold gsA10HalfEndpointHPPMassBound
  exact mul_nonneg
    (div_nonneg
      (mul_nonneg (by norm_num) (Real.log_nonneg (by exact_mod_cast hX)))
      (by exact_mod_cast hy.le))
    (PrimeEstimates.primeReciprocals_nonneg X)

/-- A fixed three-factor divisor coefficient is bounded, without a divisor
count, by `N` times the product of the reciprocal masses of its two
distinguished factors. -/
theorem sum_nested_two_weights_le_mul_reciprocalMass
    {N : ℕ} (hN : 0 < N) (B C : ℕ → ℝ)
    (hB : ∀ n, 0 ≤ B n) (hC : ∀ n, 0 ≤ C n) :
    (∑ uv ∈ N.divisorsAntidiagonal,
      ∑ ab ∈ uv.1.divisorsAntidiagonal, B ab.1 * C ab.2) ≤
      (N : ℝ) *
        (∑ a ∈ Finset.Icc 1 N, B a / (a : ℝ)) *
        (∑ b ∈ Finset.Icc 1 N, C b / (b : ℝ)) := by
  classical
  have hdivSubset : N.divisors ⊆ Finset.Icc 1 N := by
    intro q hq
    have hqdvd := (Nat.mem_divisors.mp hq).1
    exact Finset.mem_Icc.mpr
      ⟨Nat.pos_of_dvd_of_pos hqdvd hN, Nat.le_of_dvd hN hqdvd⟩
  have hanti :
      (∑ uv ∈ N.divisorsAntidiagonal,
        ∑ ab ∈ uv.1.divisorsAntidiagonal, B ab.1 * C ab.2) =
        ∑ q ∈ N.divisors,
          ∑ ab ∈ q.divisorsAntidiagonal, B ab.1 * C ab.2 := by
    rw [Nat.sum_divisorsAntidiagonal
      (fun q d ↦ ∑ ab ∈ q.divisorsAntidiagonal, B ab.1 * C ab.2)]
  rw [hanti]
  calc
    (∑ q ∈ N.divisors,
        ∑ ab ∈ q.divisorsAntidiagonal, B ab.1 * C ab.2) ≤
        ∑ q ∈ Finset.Icc 1 N,
          ∑ ab ∈ q.divisorsAntidiagonal, B ab.1 * C ab.2 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hdivSubset
      intro q hq hnot
      apply Finset.sum_nonneg
      intro ab hab
      exact mul_nonneg (hB ab.1) (hC ab.2)
    _ = ∑ a ∈ gsPositiveBelow (N + 1),
          ∑ b ∈ (gsPositiveBelow (N + 1)).filter
              (fun b ↦ a * b < N + 1), B a * C b := by
      have hset : Finset.Icc 1 N = gsPositiveBelow (N + 1) := by
        ext n
        simp [gsPositiveBelow]
      rw [hset]
      calc
        (∑ q ∈ gsPositiveBelow (N + 1),
          ∑ ab ∈ q.divisorsAntidiagonal, B ab.1 * C ab.2) =
            ∑ q ∈ gsPositiveBelow (N + 1),
              ∑ a ∈ q.divisors, B a * C (q / a) := by
          apply Finset.sum_congr rfl
          intro q hq
          exact Nat.sum_divisorsAntidiagonal (fun a b ↦ B a * C b)
        _ = _ := by
          rw [sum_divisors_reindex_real (N + 1)
            (fun q a ↦ B a * C (q / a))]
          apply Finset.sum_congr rfl
          intro a ha
          apply Finset.sum_congr rfl
          intro b hb
          have haPos : 0 < a := (Finset.mem_Ico.mp ha).1
          rw [Nat.mul_div_cancel_left b haPos]
    _ ≤ ∑ a ∈ gsPositiveBelow (N + 1),
          ∑ b ∈ (gsPositiveBelow (N + 1)).filter
              (fun b ↦ a * b < N + 1),
            (N : ℝ) * (B a / (a : ℝ)) * (C b / (b : ℝ)) := by
      apply Finset.sum_le_sum
      intro a ha
      apply Finset.sum_le_sum
      intro b hb
      have haPos : 0 < a := (Finset.mem_Ico.mp ha).1
      have hbPos : 0 < b :=
        (Finset.mem_Ico.mp (Finset.mem_filter.mp hb).1).1
      have hab : a * b ≤ N := by
        exact Nat.lt_succ_iff.mp (Finset.mem_filter.mp hb).2
      have habR : ((a * b : ℕ) : ℝ) ≤ N := by exact_mod_cast hab
      have hratio : 0 ≤ (B a / (a : ℝ)) * (C b / (b : ℝ)) :=
        mul_nonneg (div_nonneg (hB a) (Nat.cast_nonneg _))
          (div_nonneg (hC b) (Nat.cast_nonneg _))
      have hid : B a * C b =
          ((a * b : ℕ) : ℝ) *
            (B a / (a : ℝ)) * (C b / (b : ℝ)) := by
        push_cast
        field_simp
      rw [hid]
      simpa only [mul_assoc] using
        mul_le_mul_of_nonneg_right habR hratio
    _ ≤ ∑ a ∈ Finset.Icc 1 N,
          ∑ b ∈ Finset.Icc 1 N,
            (N : ℝ) * (B a / (a : ℝ)) * (C b / (b : ℝ)) := by
      have hset : gsPositiveBelow (N + 1) = Finset.Icc 1 N := by
        ext n
        simp [gsPositiveBelow]
      rw [hset]
      apply Finset.sum_le_sum
      intro a ha
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      intro b hb hnot
      exact mul_nonneg
        (mul_nonneg (Nat.cast_nonneg _)
          (div_nonneg (hB a) (Nat.cast_nonneg _)))
        (div_nonneg (hC b) (Nat.cast_nonneg _))
    _ = (N : ℝ) *
        (∑ a ∈ Finset.Icc 1 N, B a / (a : ℝ)) *
        (∑ b ∈ Finset.Icc 1 N, C b / (b : ℝ)) := by
      calc
        _ = ∑ a ∈ Finset.Icc 1 N,
            ((N : ℝ) * (B a / (a : ℝ))) *
              (∑ b ∈ Finset.Icc 1 N, C b / (b : ℝ)) := by
          apply Finset.sum_congr rfl
          intro a ha
          rw [Finset.mul_sum]
        _ = (∑ a ∈ Finset.Icc 1 N,
              (N : ℝ) * (B a / (a : ℝ))) *
            (∑ b ∈ Finset.Icc 1 N, C b / (b : ℝ)) := by
          rw [Finset.sum_mul]
        _ = _ := by
          rw [← Finset.mul_sum]

theorem sum_shiftedPrimeLambdaWindowWeight_zero_div_le
    {y X : ℕ} (hX : 2 ≤ X) :
    (∑ n ∈ Finset.Icc 1 X,
      gsA10ShiftedPrimeLambdaWindowWeight y X 0 n / (n : ℝ)) ≤
      gsA10HalfEndpointPrimeMass X := by
  calc
    _ ≤ ∑ n ∈ Finset.Icc 1 X,
        ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-(1 : ℝ)) := by
      apply Finset.sum_le_sum
      intro n hn
      have hnPos : 0 < n := (Finset.mem_Icc.mp hn).1
      have hpoint : gsA10ShiftedPrimeLambdaWindowWeight y X 0 n ≤
          ArithmeticFunction.vonMangoldt n := by
        unfold gsA10ShiftedPrimeLambdaWindowWeight
        split_ifs
        · simp
        · simp
        · exact ArithmeticFunction.vonMangoldt_nonneg
      rw [Real.rpow_neg_one]
      exact div_le_div_of_nonneg_right hpoint
        (by exact_mod_cast hnPos.le)
    _ ≤ gsA10HalfEndpointPrimeMass X := by
      simpa only [sub_self, Real.rpow_zero, mul_one,
        gsA10HalfEndpointPrimeMass] using
        (sum_vonMangoldt_mul_rpow_neg_le_one hX
          (show (0 : ℝ) ≤ 1 by norm_num) (le_refl 1))

/-- Explicit scalar bound for the ordinary higher-prime-power correction
at the Perron half-endpoint. -/
theorem gsA10OrdinaryHalfEndpointHPPError_le_mass
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    {y X : ℕ} (hX : 2 ≤ X) :
    gsA10OrdinaryHalfEndpointHPPError hmul y X 0 0 ≤
      (X : ℝ) *
        (2 * gsA10HalfEndpointPrimeMass X *
            gsA10HigherPrimePowerGeometricMass y X +
          (gsA10HigherPrimePowerGeometricMass y X) ^ 2) := by
  let P : ℕ → ℝ := gsA10ShiftedPrimeLambdaWindowWeight y X 0
  let H : ℕ → ℝ :=
    gsA10HigherPrimePowerLambdaWindowWeight hmul y X 0
  have hP0 : ∀ n, 0 ≤ P n := fun n ↦
    gsA10ShiftedPrimeLambdaWindowWeight_nonneg y X 0 n
  have hH0 : ∀ n, 0 ≤ H n := fun n ↦
    gsA10HigherPrimePowerLambdaWindowWeight_nonneg hmul y X 0 n
  have hPH := sum_nested_two_weights_le_mul_reciprocalMass
    (show 0 < X by omega) P H hP0 hH0
  have hHP := sum_nested_two_weights_le_mul_reciprocalMass
    (show 0 < X by omega) H P hH0 hP0
  have hHH := sum_nested_two_weights_le_mul_reciprocalMass
    (show 0 < X by omega) H H hH0 hH0
  have hPmass := sum_shiftedPrimeLambdaWindowWeight_zero_div_le
    (y := y) hX
  have hHmass := sum_gsA10HigherPrimePowerLambdaWindowWeight_div_le_mass
    hmul hbound (y := y) (X := X) (K := X) (rho := 0) (le_refl 0)
  let p : ℝ := ∑ n ∈ Finset.Icc 1 X, P n / (n : ℝ)
  let h : ℝ := ∑ n ∈ Finset.Icc 1 X, H n / (n : ℝ)
  have hp0 : 0 ≤ p := by
    dsimp only [p]
    exact Finset.sum_nonneg fun n hn ↦
      div_nonneg (hP0 n) (Nat.cast_nonneg _)
  have hh0 : 0 ≤ h := by
    dsimp only [h]
    exact Finset.sum_nonneg fun n hn ↦
      div_nonneg (hH0 n) (Nat.cast_nonneg _)
  have hPmass' : p ≤ gsA10HalfEndpointPrimeMass X := by
    simpa only [p, P] using hPmass
  have hHmass' : h ≤ gsA10HigherPrimePowerGeometricMass y X := by
    simpa only [h, H] using hHmass
  have hM0 : 0 ≤ gsA10HigherPrimePowerGeometricMass y X := by
    unfold gsA10HigherPrimePowerGeometricMass
    apply Finset.sum_nonneg
    intro p hp
    exact mul_nonneg
      (Real.log_nonneg (by
        have hpPrime := (mem_primesUpTo.mp (Finset.mem_filter.mp hp).1).1
        exact_mod_cast hpPrime.one_le))
      (Finset.sum_nonneg fun k hk ↦
        div_nonneg (sub_nonneg.mpr (one_le_pow₀ (by norm_num)))
          (pow_nonneg (Nat.cast_nonneg _) _))
  have hEq : gsA10OrdinaryHalfEndpointHPPError hmul y X 0 0 =
      (∑ uv ∈ X.divisorsAntidiagonal,
        ∑ ab ∈ uv.1.divisorsAntidiagonal, P ab.1 * H ab.2) +
      (∑ uv ∈ X.divisorsAntidiagonal,
        ∑ ab ∈ uv.1.divisorsAntidiagonal, H ab.1 * P ab.2) +
      (∑ uv ∈ X.divisorsAntidiagonal,
        ∑ ab ∈ uv.1.divisorsAntidiagonal, H ab.1 * H ab.2) := by
    unfold gsA10OrdinaryHalfEndpointHPPError
    simp only [zero_add, mul_zero, P, H]
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro uv huv
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  rw [hEq]
  calc
    _ ≤ ((X : ℝ) * p * h) + ((X : ℝ) * h * p) +
          ((X : ℝ) * h * h) := by
      exact add_le_add (add_le_add
        (by simpa only [p, h] using hPH)
        (by simpa only [p, h] using hHP))
        (by simpa only [p, h] using hHH)
    _ ≤ ((X : ℝ) * gsA10HalfEndpointPrimeMass X *
            gsA10HigherPrimePowerGeometricMass y X) +
          ((X : ℝ) * gsA10HigherPrimePowerGeometricMass y X *
            gsA10HalfEndpointPrimeMass X) +
          ((X : ℝ) * gsA10HigherPrimePowerGeometricMass y X *
            gsA10HigherPrimePowerGeometricMass y X) := by
      have hX0 : (0 : ℝ) ≤ X := Nat.cast_nonneg X
      exact add_le_add (add_le_add
        (mul_le_mul
          (mul_le_mul le_rfl hPmass' hp0 hX0)
          hHmass' hh0
          (mul_nonneg hX0 (gsA10HalfEndpointPrimeMass_nonneg X)))
        (mul_le_mul
          (mul_le_mul le_rfl hHmass' hh0 hX0)
          hPmass' hp0 (mul_nonneg hX0 hM0)))
        (mul_le_mul
          (mul_le_mul le_rfl hHmass' hh0 hX0)
          hHmass' hh0 (mul_nonneg hX0 hM0))
    _ = (X : ℝ) *
        (2 * gsA10HalfEndpointPrimeMass X *
            gsA10HigherPrimePowerGeometricMass y X +
          (gsA10HigherPrimePowerGeometricMass y X) ^ 2) := by ring

/-- Fully scalarized normalized half-jump.  The first term is the classical
prime--prime endpoint, while the remaining two terms are respectively the
prime/HPP cross contribution and the HPP square. -/
theorem norm_gsA10TwoBlockTailoredCoefficient_div_two_mul_le_mass
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    (P₁ P₂ : ℕ → Prop) [DecidablePred P₁] [DecidablePred P₂]
    {y X : ℕ}
    (hQ₂ : ∀ p, (¬ P₁ p ∧ P₂ p) → p ≤ y)
    (hQ₃ : ∀ p, (¬ P₁ p ∧ ¬ P₂ p) → p ≤ y)
    (hX : 2 ≤ X) {alpha beta : ℝ}
    (halpha : 0 ≤ alpha) (hbeta : 0 ≤ beta) :
    ‖gsA10TwoBlockTailoredCoefficient
        f hmul P₁ P₂ y X alpha beta X‖ / (2 * (X : ℝ)) ≤
      (Real.log (X : ℝ)) ^ 2 / (2 * (X : ℝ)) +
        gsA10HalfEndpointPrimeMass X *
          gsA10HigherPrimePowerGeometricMass y X +
        (gsA10HigherPrimePowerGeometricMass y X) ^ 2 / 2 := by
  have hXpos : 0 < X := by omega
  have hbase :=
    norm_gsA10TwoBlockTailoredCoefficient_div_two_mul_le_zeroHPP
      hmul hbound P₁ P₂ hQ₂ hQ₃ hXpos halpha hbeta
  have hhpp := gsA10OrdinaryHalfEndpointHPPError_le_mass
    hmul hbound (y := y) hX
  refine hbase.trans ?_
  have hden : (0 : ℝ) < 2 * X := by positivity
  calc
    ((Real.log (X : ℝ)) ^ 2 +
        gsA10OrdinaryHalfEndpointHPPError hmul y X 0 0) /
          (2 * (X : ℝ)) ≤
      ((Real.log (X : ℝ)) ^ 2 +
        (X : ℝ) *
          (2 * gsA10HalfEndpointPrimeMass X *
              gsA10HigherPrimePowerGeometricMass y X +
            (gsA10HigherPrimePowerGeometricMass y X) ^ 2)) /
          (2 * (X : ℝ)) := by
      exact div_le_div_of_nonneg_right (add_le_add le_rfl hhpp) hden.le
    _ = (Real.log (X : ℝ)) ^ 2 / (2 * (X : ℝ)) +
        gsA10HalfEndpointPrimeMass X *
          gsA10HigherPrimePowerGeometricMass y X +
        (gsA10HigherPrimePowerGeometricMass y X) ^ 2 / 2 := by
      field_simp
      ring

/-- Completely explicit ordinary-multiplicative endpoint bound, after
inserting the geometric higher-prime-power mass estimate. -/
theorem norm_gsA10TwoBlockTailoredCoefficient_div_two_mul_le_explicit
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    (P₁ P₂ : ℕ → Prop) [DecidablePred P₁] [DecidablePred P₂]
    {y X : ℕ}
    (hQ₂ : ∀ p, (¬ P₁ p ∧ P₂ p) → p ≤ y)
    (hQ₃ : ∀ p, (¬ P₁ p ∧ ¬ P₂ p) → p ≤ y)
    (hy : 3 ≤ y) (hX : 2 ≤ X) {alpha beta : ℝ}
    (halpha : 0 ≤ alpha) (hbeta : 0 ≤ beta) :
    ‖gsA10TwoBlockTailoredCoefficient
        f hmul P₁ P₂ y X alpha beta X‖ / (2 * (X : ℝ)) ≤
      (Real.log (X : ℝ)) ^ 2 / (2 * (X : ℝ)) +
        gsA10HalfEndpointPrimeMass X *
          gsA10HalfEndpointHPPMassBound y X +
        (gsA10HalfEndpointHPPMassBound y X) ^ 2 / 2 := by
  have hbase := norm_gsA10TwoBlockTailoredCoefficient_div_two_mul_le_mass
    hmul hbound P₁ P₂ hQ₂ hQ₃ hX halpha hbeta
  refine hbase.trans ?_
  have hM := gsA10HigherPrimePowerGeometricMass_le (X := X) hy
  have hM0 : 0 ≤ gsA10HigherPrimePowerGeometricMass y X := by
    unfold gsA10HigherPrimePowerGeometricMass
    apply Finset.sum_nonneg
    intro p hp
    exact mul_nonneg
      (Real.log_nonneg (by
        have hpPrime := (mem_primesUpTo.mp (Finset.mem_filter.mp hp).1).1
        exact_mod_cast hpPrime.one_le))
      (Finset.sum_nonneg fun k hk ↦
        div_nonneg (sub_nonneg.mpr (one_le_pow₀ (by norm_num)))
          (pow_nonneg (Nat.cast_nonneg _) _))
  have hQ0 : 0 ≤ gsA10HalfEndpointHPPMassBound y X :=
    gsA10HalfEndpointHPPMassBound_nonneg (by omega) (by omega)
  have hM' : gsA10HigherPrimePowerGeometricMass y X ≤
      gsA10HalfEndpointHPPMassBound y X := by
    simpa only [gsA10HalfEndpointHPPMassBound] using hM
  exact add_le_add (add_le_add le_rfl
    (mul_le_mul_of_nonneg_left hM'
      (gsA10HalfEndpointPrimeMass_nonneg X)))
    (div_le_div_of_nonneg_right
      ((sq_le_sq₀ hM0 hQ0).2 hM') (by norm_num))

end


#print axioms Erdos67.MRHalaszBands.sum_nested_two_weights_le_mul_reciprocalMass
#print axioms Erdos67.MRHalaszBands.gsA10OrdinaryHalfEndpointHPPError_le_mass
#print axioms Erdos67.MRHalaszBands.norm_gsA10TwoBlockTailoredCoefficient_div_two_mul_le_mass
#print axioms Erdos67.MRHalaszBands.norm_gsA10TwoBlockTailoredCoefficient_div_two_mul_le_explicit

end Erdos67.MRHalaszBands
