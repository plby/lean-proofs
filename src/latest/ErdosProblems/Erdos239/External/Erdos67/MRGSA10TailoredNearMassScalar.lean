import ErdosProblems.Erdos239.External.Erdos67.MRGSA10TailoredNearMass

/-!
# Scalarization of the tailored A.10 near mass

The constant part of the hyperbola is summed one distinguished variable
at a time.  The reciprocal part separates into the square of the weighted
Chebyshev mass.
-/

open scoped BigOperators
open Finset

namespace Erdos67.MRHalaszBands

noncomputable section

open BoundedGaps.Maynard

def gsA10NearChebyshevConstant : ℝ := 12 * (Real.log 4 + 4)

def gsA10NearReciprocalMass (X : ℕ) : ℝ :=
  2 * (Real.log 4 + 4) * (Nat.log 2 (2 * X) : ℝ)

theorem gsA10NearChebyshevConstant_nonneg :
    0 ≤ gsA10NearChebyshevConstant := by
  dsimp only [gsA10NearChebyshevConstant]
  positivity

theorem gsA10_harmonic_cast_nonneg (n : ℕ) :
    0 ≤ (harmonic n : ℝ) := by
  simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv,
    Rat.cast_natCast]
  exact Finset.sum_nonneg fun k hk ↦ by positivity

theorem sum_vonMangoldt_le_nearChebyshevConstant_mul (K : ℕ) :
    (∑ n ∈ Finset.Icc 1 K, ArithmeticFunction.vonMangoldt n) ≤
      gsA10NearChebyshevConstant * K := by
  by_cases hK : 2 ≤ K
  · have h := sum_vonMangoldt_mul_rpow_neg_le hK
      (alpha := 0) (by norm_num) (by norm_num)
    simpa only [neg_zero, Real.rpow_zero, mul_one, sub_zero,
      Real.rpow_one, gsA10NearChebyshevConstant] using h
  · have hKle : K ≤ 1 := by omega
    have hset : Finset.Icc 1 K ⊆ {1} := by
      intro n hn
      simp only [Finset.mem_Icc, Finset.mem_singleton] at hn ⊢
      omega
    have hzero : (∑ n ∈ Finset.Icc 1 K,
        ArithmeticFunction.vonMangoldt n) = 0 := by
      apply Finset.sum_eq_zero
      intro n hn
      have hn1 : n = 1 := by
        simpa only [Finset.mem_singleton] using hset hn
      subst n
      exact ArithmeticFunction.vonMangoldt_apply_one
    rw [hzero]
    exact mul_nonneg gsA10NearChebyshevConstant_nonneg (by positivity)

theorem sum_vonMangoldt_div_le_nearReciprocalMass
    {X : ℕ} (hX : 0 < X) :
    (∑ n ∈ Finset.Icc 1 (2 * X),
      ArithmeticFunction.vonMangoldt n * (n : ℝ)⁻¹) ≤
        gsA10NearReciprocalMass X := by
  have h := sum_vonMangoldt_mul_rpow_neg_le_one
    (K := 2 * X) (alpha := 1) (by omega) (by norm_num) (by norm_num)
  simpa only [Real.rpow_neg_one, sub_self, Real.rpow_zero, mul_one,
    gsA10NearReciprocalMass] using h

/-- The unweighted von-Mangoldt hyperbola is `O(X log X)`. -/
theorem sum_vonMangoldt_hyperbola_le
    {X : ℕ} (hX : 0 < X) :
    (∑ a ∈ gsPositiveBelow (2 * X + 1),
      ∑ b ∈ (gsPositiveBelow (2 * X + 1)).filter
          (fun b ↦ a * b < 2 * X + 1),
        ArithmeticFunction.vonMangoldt a *
          ArithmeticFunction.vonMangoldt b) ≤
      gsA10NearChebyshevConstant * (2 * X : ℕ) *
        gsA10NearReciprocalMass X := by
  have hset : gsPositiveBelow (2 * X + 1) = Finset.Icc 1 (2 * X) := by
    ext n
    simp [gsPositiveBelow]
  rw [hset]
  calc
    (∑ a ∈ Finset.Icc 1 (2 * X),
      ∑ b ∈ (gsPositiveBelow (2 * X + 1)).filter
          (fun b ↦ a * b < 2 * X + 1),
        ArithmeticFunction.vonMangoldt a *
          ArithmeticFunction.vonMangoldt b) ≤
      ∑ a ∈ Finset.Icc 1 (2 * X),
        ArithmeticFunction.vonMangoldt a *
          (gsA10NearChebyshevConstant * ((2 * X / a : ℕ) : ℝ)) := by
      apply Finset.sum_le_sum
      intro a ha
      rw [← Finset.mul_sum]
      apply mul_le_mul_of_nonneg_left
      · calc
          (∑ b ∈ (gsPositiveBelow (2 * X + 1)).filter
              (fun b ↦ a * b < 2 * X + 1),
              ArithmeticFunction.vonMangoldt b) ≤
            ∑ b ∈ Finset.Icc 1 (2 * X / a),
              ArithmeticFunction.vonMangoldt b := by
                apply Finset.sum_le_sum_of_subset_of_nonneg
                · intro b hb
                  have hbData := Finset.mem_filter.mp hb
                  have hbIco : 1 ≤ b ∧ b < 2 * X + 1 := by
                    simpa [gsPositiveBelow] using hbData.1
                  have haPos : 0 < a := (Finset.mem_Icc.mp ha).1
                  apply Finset.mem_Icc.mpr
                  refine ⟨hbIco.1, ?_⟩
                  rw [Nat.le_div_iff_mul_le haPos]
                  simpa only [mul_comm] using (by omega : a * b ≤ 2 * X)
                · intro b hb hnot
                  exact ArithmeticFunction.vonMangoldt_nonneg
          _ ≤ gsA10NearChebyshevConstant * (2 * X / a : ℕ) :=
            sum_vonMangoldt_le_nearChebyshevConstant_mul _
      · exact ArithmeticFunction.vonMangoldt_nonneg
    _ ≤ ∑ a ∈ Finset.Icc 1 (2 * X),
        (gsA10NearChebyshevConstant * (2 * X : ℕ)) *
          (ArithmeticFunction.vonMangoldt a * (a : ℝ)⁻¹) := by
      apply Finset.sum_le_sum
      intro a ha
      have haPos : 0 < a := (Finset.mem_Icc.mp ha).1
      have hdiv : ((2 * X / a : ℕ) : ℝ) ≤ (2 * X : ℝ) / a := by
        simpa only [Nat.cast_mul, Nat.cast_ofNat] using
          (Nat.cast_div_le (α := ℝ) (m := 2 * X) (n := a))
      calc
        ArithmeticFunction.vonMangoldt a *
            (gsA10NearChebyshevConstant * ((2 * X / a : ℕ) : ℝ)) ≤
          ArithmeticFunction.vonMangoldt a *
            (gsA10NearChebyshevConstant * ((2 * X : ℝ) / a)) := by
              exact mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_left hdiv
                  gsA10NearChebyshevConstant_nonneg)
                ArithmeticFunction.vonMangoldt_nonneg
        _ = (gsA10NearChebyshevConstant * (2 * X : ℕ)) *
            (ArithmeticFunction.vonMangoldt a * (a : ℝ)⁻¹) := by
              rw [div_eq_mul_inv]
              push_cast
              ring
    _ = (gsA10NearChebyshevConstant * (2 * X : ℕ)) *
        (∑ a ∈ Finset.Icc 1 (2 * X),
          ArithmeticFunction.vonMangoldt a * (a : ℝ)⁻¹) := by
      rw [Finset.mul_sum]
    _ ≤ gsA10NearChebyshevConstant * (2 * X : ℕ) *
        gsA10NearReciprocalMass X := by
      exact mul_le_mul_of_nonneg_left
        (sum_vonMangoldt_div_le_nearReciprocalMass hX)
        (mul_nonneg gsA10NearChebyshevConstant_nonneg (by positivity))

/-- The reciprocal hyperbola separates into two one-variable masses. -/
theorem sum_vonMangoldt_hyperbola_reciprocal_le
    {X : ℕ} (hX : 0 < X) :
    (∑ a ∈ gsPositiveBelow (2 * X + 1),
      ∑ b ∈ (gsPositiveBelow (2 * X + 1)).filter
          (fun b ↦ a * b < 2 * X + 1),
        ArithmeticFunction.vonMangoldt a *
          ArithmeticFunction.vonMangoldt b * ((a * b : ℕ) : ℝ)⁻¹) ≤
      (gsA10NearReciprocalMass X) ^ 2 := by
  have hset : gsPositiveBelow (2 * X + 1) = Finset.Icc 1 (2 * X) := by
    ext n
    simp [gsPositiveBelow]
  rw [hset]
  calc
    (∑ a ∈ Finset.Icc 1 (2 * X),
      ∑ b ∈ (gsPositiveBelow (2 * X + 1)).filter
          (fun b ↦ a * b < 2 * X + 1),
        ArithmeticFunction.vonMangoldt a *
          ArithmeticFunction.vonMangoldt b * ((a * b : ℕ) : ℝ)⁻¹) ≤
      ∑ a ∈ Finset.Icc 1 (2 * X),
        ∑ b ∈ Finset.Icc 1 (2 * X),
          (ArithmeticFunction.vonMangoldt a * (a : ℝ)⁻¹) *
            (ArithmeticFunction.vonMangoldt b * (b : ℝ)⁻¹) := by
      apply Finset.sum_le_sum
      intro a ha
      calc
        (∑ b ∈ (gsPositiveBelow (2 * X + 1)).filter
            (fun b ↦ a * b < 2 * X + 1),
          ArithmeticFunction.vonMangoldt a *
            ArithmeticFunction.vonMangoldt b * ((a * b : ℕ) : ℝ)⁻¹) =
          ∑ b ∈ (gsPositiveBelow (2 * X + 1)).filter
            (fun b ↦ a * b < 2 * X + 1),
            (ArithmeticFunction.vonMangoldt a * (a : ℝ)⁻¹) *
              (ArithmeticFunction.vonMangoldt b * (b : ℝ)⁻¹) := by
                apply Finset.sum_congr rfl
                intro b hb
                push_cast
                rw [mul_inv]
                ring
        _ ≤ ∑ b ∈ Finset.Icc 1 (2 * X),
            (ArithmeticFunction.vonMangoldt a * (a : ℝ)⁻¹) *
              (ArithmeticFunction.vonMangoldt b * (b : ℝ)⁻¹) := by
                apply Finset.sum_le_sum_of_subset_of_nonneg
                · intro b hb
                  have hbData := Finset.mem_filter.mp hb
                  have hbIco : 1 ≤ b ∧ b < 2 * X + 1 := by
                    simpa [gsPositiveBelow] using hbData.1
                  exact Finset.mem_Icc.mpr ⟨hbIco.1, by omega⟩
                · intro b hb hnot
                  positivity
    _ = (∑ a ∈ Finset.Icc 1 (2 * X),
          ArithmeticFunction.vonMangoldt a * (a : ℝ)⁻¹) ^ 2 := by
      simp_rw [← Finset.mul_sum]
      rw [← Finset.sum_mul]
      ring
    _ ≤ (gsA10NearReciprocalMass X) ^ 2 := by
      have hmass := sum_vonMangoldt_div_le_nearReciprocalMass hX
      have hleft0 : 0 ≤ (∑ a ∈ Finset.Icc 1 (2 * X),
          ArithmeticFunction.vonMangoldt a * (a : ℝ)⁻¹) := by positivity
      have hright0 : 0 ≤ gsA10NearReciprocalMass X := by
        dsimp only [gsA10NearReciprocalMass]
        positivity
      nlinarith

/-- Fully scalar pointwise near-mass envelope. -/
theorem dirichletPerronNearMass_gsA10TwoBlockTailoredCoefficient_le_scalar
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hcomp : IsCompletelyMultiplicativeOnPositive f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    (P₁ P₂ : ℕ → Prop) [DecidablePred P₁] [DecidablePred P₂]
    {y X : ℕ}
    (hQ₂ : ∀ p, (¬ P₁ p ∧ P₂ p) → p ≤ y)
    (hQ₃ : ∀ p, (¬ P₁ p ∧ ¬ P₂ p) → p ≤ y)
    (hX : 0 < X) {T : ℝ} (hT : 0 < T)
    {alpha beta : ℝ} (halpha : 0 ≤ alpha) (hbeta : 0 ≤ beta) :
    dirichletPerronNearMass
        (gsA10TwoBlockTailoredCoefficient
          f hmul P₁ P₂ y X alpha beta) X T ≤
      2 * (gsA10NearChebyshevConstant * (2 * X : ℕ) *
        gsA10NearReciprocalMass X) +
      (4 * (X : ℝ) / T) * (harmonic (2 * X) : ℝ) *
        (gsA10NearReciprocalMass X) ^ 2 := by
  have hbase :=
    dirichletPerronNearMass_gsA10TwoBlockTailoredCoefficient_le_vonMangoldt
      hmul hcomp hbound P₁ P₂ hQ₂ hQ₃ hX hT halpha hbeta
  refine hbase.trans ?_
  let S := gsPositiveBelow (2 * X + 1)
  let R : ℝ := (4 * (X : ℝ) / T) * (harmonic (2 * X) : ℝ)
  have hsplit :
      (∑ a ∈ S, ∑ b ∈ S.filter (fun b ↦ a * b < 2 * X + 1),
        ArithmeticFunction.vonMangoldt a * ArithmeticFunction.vonMangoldt b *
          (2 + (4 * (X : ℝ) / T) * ((a * b : ℕ) : ℝ)⁻¹ *
            (harmonic (2 * X) : ℝ))) =
      2 * (∑ a ∈ S, ∑ b ∈ S.filter (fun b ↦ a * b < 2 * X + 1),
        ArithmeticFunction.vonMangoldt a * ArithmeticFunction.vonMangoldt b) +
      R * (∑ a ∈ S, ∑ b ∈ S.filter (fun b ↦ a * b < 2 * X + 1),
        ArithmeticFunction.vonMangoldt a * ArithmeticFunction.vonMangoldt b *
          ((a * b : ℕ) : ℝ)⁻¹) := by
    dsimp only [R]
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro a ha
    apply Finset.sum_congr rfl
    intro b hb
    ring
  dsimp only [S] at hsplit
  rw [hsplit]
  exact add_le_add
    (mul_le_mul_of_nonneg_left (sum_vonMangoldt_hyperbola_le hX) (by norm_num))
    (mul_le_mul_of_nonneg_left
      (sum_vonMangoldt_hyperbola_reciprocal_le hX) (by
        dsimp only [R]
        exact mul_nonneg
          (div_nonneg (by positivity) hT.le)
          (gsA10_harmonic_cast_nonneg (2 * X))))

end

end Erdos67.MRHalaszBands

#print axioms
  Erdos67.MRHalaszBands.dirichletPerronNearMass_gsA10TwoBlockTailoredCoefficient_le_scalar
