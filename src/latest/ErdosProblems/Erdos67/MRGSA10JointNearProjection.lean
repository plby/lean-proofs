import ErdosProblems.Erdos67.MRGSA10JointTailoredAverage
import ErdosProblems.Erdos67.MRRestrictedPerronErrorBound

/-!
# Joint A.10 near-mass and half-endpoint projection error

The coefficientwise joint rectangle estimate is commuted through the finite
Perron near kernel.  Thus the arithmetic near mass is reduced to the scalar
coefficient-one kernel mass, with no separate loss for each Mangoldt pair.
-/

open scoped BigOperators
open Finset MeasureTheory Set

namespace Erdos67.MRHalaszBands

noncomputable section

open BoundedGaps.Maynard

private theorem doubleIntervalIntegral_finsetSum_jointNear
    {ι : Type*} {s : Finset ι} {eta : ℝ} {F : ι → ℝ → ℝ → ℝ}
    (hF : ∀ i ∈ s, Continuous (Function.uncurry (F i))) :
    (∫ alpha : ℝ in 0..eta,
      ∫ beta : ℝ in 0..eta, ∑ i ∈ s, F i alpha beta) =
      ∑ i ∈ s, ∫ alpha : ℝ in 0..eta,
        ∫ beta : ℝ in 0..eta, F i alpha beta := by
  have hinner (i : ι) (hi : i ∈ s) : Continuous (fun alpha : ℝ ↦
      ∫ beta : ℝ in 0..eta, F i alpha beta) := by
    apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    exact hF i hi
  have hinnerSum : ∀ alpha : ℝ,
      (∫ beta : ℝ in 0..eta, ∑ i ∈ s, F i alpha beta) =
        ∑ i ∈ s, ∫ beta : ℝ in 0..eta, F i alpha beta := by
    intro alpha
    apply intervalIntegral.integral_finsetSum
    intro i hi
    exact ((hF i hi).comp
      (continuous_const.prodMk continuous_id)).intervalIntegrable 0 eta
  simp_rw [hinnerSum]
  apply intervalIntegral.integral_finsetSum
  intro i hi
  exact (hinner i hi).intervalIntegrable 0 eta

private theorem dirichletPerronNearMass_eq_sum_range_jointNear
    (a : ℕ → ℂ) (X : ℕ) (T : ℝ) :
    dirichletPerronNearMass a X T =
      ∑ n ∈ Finset.range (2 * X),
        ‖a n‖ * dirichletPerronNearError X T n := by
  unfold dirichletPerronNearMass
  rw [tsum_eq_sum (s := Finset.range (2 * X))]
  intro n hn
  have hnLower : 2 * X ≤ n := by simpa using hn
  have hnLowerR : (2 : ℝ) * X ≤ n := by exact_mod_cast hnLower
  rw [dirichletPerronNearError, if_neg]
  · simp
  · intro h
    exact (not_lt_of_ge hnLowerR) h.2.2.1

/-- The double rectangle average of the actual near mass is at most half
the scalar coefficient-one near mass. -/
theorem doubleIntervalIntegral_dirichletPerronNearMass_tailored_le_half_scalar
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hcomp : IsCompletelyMultiplicativeOnPositive f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    (P₁ P₂ : ℕ → Prop) [DecidablePred P₁] [DecidablePred P₂]
    (y : ℕ) {X : ℕ} (hX : 0 < X)
    (hQ₂ : ∀ p, (¬ P₁ p ∧ P₂ p) → p ≤ y)
    (hQ₃ : ∀ p, (¬ P₁ p ∧ ¬ P₂ p) → p ≤ y)
    {T eta : ℝ} (hT : 0 < T) (heta : 0 ≤ eta) :
    (∫ alpha : ℝ in 0..eta,
      ∫ beta : ℝ in 0..eta,
        dirichletPerronNearMass
          (gsA10TwoBlockTailoredCoefficient
            f hmul P₁ P₂ y X alpha beta) X T) ≤
      2 * (X : ℝ) * (harmonic X : ℝ) / T := by
  have hnear (alpha beta : ℝ) :
      dirichletPerronNearMass
          (gsA10TwoBlockTailoredCoefficient
            f hmul P₁ P₂ y X alpha beta) X T =
        ∑ n ∈ Finset.range (2 * X),
          ‖gsA10TwoBlockTailoredCoefficient
              f hmul P₁ P₂ y X alpha beta n‖ *
            dirichletPerronNearError X T n :=
    dirichletPerronNearMass_eq_sum_range_jointNear _ X T
  simp_rw [hnear]
  rw [doubleIntervalIntegral_finsetSum_jointNear]
  · calc
      (∑ n ∈ Finset.range (2 * X),
        ∫ alpha : ℝ in 0..eta,
          ∫ beta : ℝ in 0..eta,
            ‖gsA10TwoBlockTailoredCoefficient
                f hmul P₁ P₂ y X alpha beta n‖ *
              dirichletPerronNearError X T n) ≤
          ∑ n ∈ Finset.range (2 * X),
            (1 / 2 : ℝ) * dirichletPerronNearError X T n := by
        apply Finset.sum_le_sum
        intro n hn
        by_cases hn0 : n = 0
        · subst n
          simp
        simp_rw [intervalIntegral.integral_mul_const]
        apply mul_le_mul_of_nonneg_right
          (doubleIntervalIntegral_norm_gsA10TwoBlockTailoredCoefficient_le_half
            hmul hcomp hbound P₁ P₂ y X hQ₂ hQ₃
              (Nat.pos_of_ne_zero hn0) heta)
          (Erdos67.MRPerronNearProgression.dirichletPerronNearError_nonneg
            X hT n)
      _ = (1 / 2 : ℝ) *
          (∑ n ∈ Finset.range (2 * X),
            dirichletPerronNearError X T n) := by
        rw [Finset.mul_sum]
      _ ≤ (1 / 2 : ℝ) *
          (4 * (X : ℝ) * (harmonic X : ℝ) / T) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        have hone :=
          Erdos67.MRRestrictedPerronErrorBound.dirichletPerronNearMass_one_bounded_le_harmonic
          (a := fun _ ↦ (1 : ℂ)) (fun _ _ ↦ by norm_num) hX hT
        rw [dirichletPerronNearMass_eq_sum_range_jointNear] at hone
        simpa only [norm_one, one_mul] using hone
      _ = 2 * (X : ℝ) * (harmonic X : ℝ) / T := by ring
  · intro n hn
    exact (continuous_uncurry_norm_gsA10TwoBlockTailoredCoefficient
      hmul P₁ P₂ y X n).mul continuous_const

/-- The same joint average bounds the half-endpoint contribution by `1/4`. -/
theorem doubleIntervalIntegral_half_norm_tailored_endpoint_le_quarter
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hcomp : IsCompletelyMultiplicativeOnPositive f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    (P₁ P₂ : ℕ → Prop) [DecidablePred P₁] [DecidablePred P₂]
    (y : ℕ) {X : ℕ} (hX : 0 < X)
    (hQ₂ : ∀ p, (¬ P₁ p ∧ P₂ p) → p ≤ y)
    (hQ₃ : ∀ p, (¬ P₁ p ∧ ¬ P₂ p) → p ≤ y)
    {eta : ℝ} (heta : 0 ≤ eta) :
    (∫ alpha : ℝ in 0..eta,
      ∫ beta : ℝ in 0..eta,
        (1 / 2 : ℝ) *
          ‖gsA10TwoBlockTailoredCoefficient
            f hmul P₁ P₂ y X alpha beta X‖) ≤ 1 / 4 := by
  simp_rw [intervalIntegral.integral_const_mul]
  have h := doubleIntervalIntegral_norm_gsA10TwoBlockTailoredCoefficient_le_half
    hmul hcomp hbound P₁ P₂ y X hQ₂ hQ₃ hX heta
  nlinarith

/-- Combined local projection remainder in the exact form appearing in the
moving-Perron mass-envelope theorem. -/
theorem doubleIntervalIntegral_tailored_near_add_half_endpoint_le
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hcomp : IsCompletelyMultiplicativeOnPositive f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    (P₁ P₂ : ℕ → Prop) [DecidablePred P₁] [DecidablePred P₂]
    (y : ℕ) {X : ℕ} (hX : 0 < X)
    (hQ₂ : ∀ p, (¬ P₁ p ∧ P₂ p) → p ≤ y)
    (hQ₃ : ∀ p, (¬ P₁ p ∧ ¬ P₂ p) → p ≤ y)
    {T eta : ℝ} (hT : 0 < T) (heta : 0 ≤ eta) :
    (∫ alpha : ℝ in 0..eta,
      ∫ beta : ℝ in 0..eta,
        (dirichletPerronNearMass
          (gsA10TwoBlockTailoredCoefficient
            f hmul P₁ P₂ y X alpha beta) X T +
          (1 / 2 : ℝ) *
            ‖gsA10TwoBlockTailoredCoefficient
              f hmul P₁ P₂ y X alpha beta X‖)) ≤
      2 * (X : ℝ) * (harmonic X : ℝ) / T + 1 / 4 := by
  have hnear :=
    doubleIntervalIntegral_dirichletPerronNearMass_tailored_le_half_scalar
      hmul hcomp hbound P₁ P₂ y hX hQ₂ hQ₃ hT heta
  have hend := doubleIntervalIntegral_half_norm_tailored_endpoint_le_quarter
    hmul hcomp hbound P₁ P₂ y hX hQ₂ hQ₃ heta
  have hnearCont : Continuous (Function.uncurry fun alpha beta : ℝ ↦
      dirichletPerronNearMass
        (gsA10TwoBlockTailoredCoefficient
          f hmul P₁ P₂ y X alpha beta) X T) := by
    simp_rw [dirichletPerronNearMass_eq_sum_range_jointNear]
    apply continuous_finset_sum
    intro n hn
    exact (continuous_uncurry_norm_gsA10TwoBlockTailoredCoefficient
      hmul P₁ P₂ y X n).mul continuous_const
  have hendCont : Continuous (Function.uncurry fun alpha beta : ℝ ↦
      (1 / 2 : ℝ) *
        ‖gsA10TwoBlockTailoredCoefficient
          f hmul P₁ P₂ y X alpha beta X‖) :=
    continuous_const.mul
      (continuous_uncurry_norm_gsA10TwoBlockTailoredCoefficient
        hmul P₁ P₂ y X X)
  have hinner (alpha : ℝ) :
      (∫ beta : ℝ in 0..eta,
        (dirichletPerronNearMass
          (gsA10TwoBlockTailoredCoefficient
            f hmul P₁ P₂ y X alpha beta) X T +
          (1 / 2 : ℝ) *
            ‖gsA10TwoBlockTailoredCoefficient
              f hmul P₁ P₂ y X alpha beta X‖)) =
        (∫ beta : ℝ in 0..eta,
          dirichletPerronNearMass
            (gsA10TwoBlockTailoredCoefficient
              f hmul P₁ P₂ y X alpha beta) X T) +
        ∫ beta : ℝ in 0..eta,
          (1 / 2 : ℝ) *
            ‖gsA10TwoBlockTailoredCoefficient
              f hmul P₁ P₂ y X alpha beta X‖ := by
    apply intervalIntegral.integral_add
    · exact (hnearCont.comp
        (continuous_const.prodMk continuous_id)).intervalIntegrable 0 eta
    · exact (hendCont.comp
        (continuous_const.prodMk continuous_id)).intervalIntegrable 0 eta
  simp_rw [hinner]
  rw [intervalIntegral.integral_add
    ((intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      hnearCont 0 eta).intervalIntegrable 0 eta)
    ((intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      hendCont 0 eta).intervalIntegrable 0 eta)]
  linarith

/-- Normalized form consumed by the moving-Perron projection: the source
factor is `2 / (eta * X)`. -/
theorem two_div_eta_mul_X_mul_doubleIntervalIntegral_tailored_near_add_half_le
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hcomp : IsCompletelyMultiplicativeOnPositive f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    (P₁ P₂ : ℕ → Prop) [DecidablePred P₁] [DecidablePred P₂]
    (y : ℕ) {X : ℕ} (hX : 0 < X)
    (hQ₂ : ∀ p, (¬ P₁ p ∧ P₂ p) → p ≤ y)
    (hQ₃ : ∀ p, (¬ P₁ p ∧ ¬ P₂ p) → p ≤ y)
    {T eta : ℝ} (hT : 0 < T) (heta : 0 < eta) :
    (2 / (eta * (X : ℝ))) *
      (∫ alpha : ℝ in 0..eta,
        ∫ beta : ℝ in 0..eta,
          (dirichletPerronNearMass
            (gsA10TwoBlockTailoredCoefficient
              f hmul P₁ P₂ y X alpha beta) X T +
            (1 / 2 : ℝ) *
              ‖gsA10TwoBlockTailoredCoefficient
                f hmul P₁ P₂ y X alpha beta X‖)) ≤
      4 * (harmonic X : ℝ) / (eta * T) +
        1 / (2 * eta * (X : ℝ)) := by
  have h := doubleIntervalIntegral_tailored_near_add_half_endpoint_le
    hmul hcomp hbound P₁ P₂ y hX hQ₂ hQ₃ hT heta.le
  have hfac : 0 ≤ 2 / (eta * (X : ℝ)) := by positivity
  refine (mul_le_mul_of_nonneg_left h hfac).trans_eq ?_
  field_simp
  <;> ring

/-- Source specialization `T = log(X)^2`, `eta = 1/log y`.  The exact
remaining scalar is `4 H_X log y / log(X)^2 + log y/(2X)`. -/
theorem source_doubleIntervalIntegral_tailored_near_add_half_le
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hcomp : IsCompletelyMultiplicativeOnPositive f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    (P₁ P₂ : ℕ → Prop) [DecidablePred P₁] [DecidablePred P₂]
    {y X : ℕ} (hy : 2 ≤ y) (hX : 2 ≤ X)
    (hQ₂ : ∀ p, (¬ P₁ p ∧ P₂ p) → p ≤ y)
    (hQ₃ : ∀ p, (¬ P₁ p ∧ ¬ P₂ p) → p ≤ y) :
    (2 / ((Real.log (y : ℝ))⁻¹ * (X : ℝ))) *
      (∫ alpha : ℝ in 0..(Real.log (y : ℝ))⁻¹,
        ∫ beta : ℝ in 0..(Real.log (y : ℝ))⁻¹,
          (dirichletPerronNearMass
            (gsA10TwoBlockTailoredCoefficient
              f hmul P₁ P₂ y X alpha beta) X
                ((Real.log (X : ℝ)) ^ 2) +
            (1 / 2 : ℝ) *
              ‖gsA10TwoBlockTailoredCoefficient
                f hmul P₁ P₂ y X alpha beta X‖)) ≤
      4 * (harmonic X : ℝ) * Real.log (y : ℝ) /
          (Real.log (X : ℝ)) ^ 2 +
        Real.log (y : ℝ) / (2 * (X : ℝ)) := by
  have hlogy : 0 < Real.log (y : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  have hlogX : 0 < Real.log (X : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < X by omega))
  have h :=
    two_div_eta_mul_X_mul_doubleIntervalIntegral_tailored_near_add_half_le
      hmul hcomp hbound P₁ P₂ y (X := X) (by omega) hQ₂ hQ₃
        (sq_pos_of_pos hlogX) (inv_pos.mpr hlogy)
  convert h using 1 <;> field_simp

end

end Erdos67.MRHalaszBands
