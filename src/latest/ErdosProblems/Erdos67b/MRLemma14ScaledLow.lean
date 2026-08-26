import ErdosProblems.Erdos67b.MRLemma14UniversalLow
import ErdosProblems.Erdos67b.MRLemma14ContinuousCentralEnergy

/-!
# Scale-explicit central Perron energy

The quadratic source moments cancel all inverse powers of the short
length. The remaining bound is an absolute constant times the spatial
scale and the actual vertical energy, with no vertical-length loss.
-/

open Finset MeasureTheory Set

namespace Erdos67b

noncomputable section

/-- A convenient bound for a nonnegative quadratic moment. -/
theorem lemma14_quadratic_moment_le_cube {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) :
    (∫ u in a..b, u ^ 2) ≤ b ^ 3 := by
  calc
    (∫ u in a..b, u ^ 2) ≤ ∫ _u in a..b, b ^ 2 := by
      apply intervalIntegral.integral_mono_on hab
      · exact (by fun_prop : Continuous (fun u : ℝ ↦ u ^ 2)).intervalIntegrable _ _
      · exact continuous_const.intervalIntegrable _ _
      · intro u hu
        exact pow_le_pow_left₀ (ha.trans hu.1) hu.2 2
    _ = (b - a) * b ^ 2 := by simp
    _ ≤ b ^ 3 := by nlinarith [mul_nonneg ha (sq_nonneg b)]

theorem lemma14_left_source_low_moment_le
    {X H : ℝ} (hX : 0 < X) (hH : 0 < H) :
    (∫ u in H / (2 * X)..3 * H / X, u ^ 2) ≤ 27 * H ^ 3 / X ^ 3 := by
  have hCD : H / (2 * X) ≤ 3 * H / X := by
    have hratio : 0 ≤ H / X := by positivity
    have heq : H / (2 * X) = (H / X) / 2 := by ring
    rw [heq, show 3 * H / X = 3 * (H / X) by ring]
    linarith
  calc
    _ ≤ (3 * H / X) ^ 3 := lemma14_quadratic_moment_le_cube (by positivity) hCD
    _ = _ := by ring

theorem lemma14_right_source_low_moment_le
    {X H : ℝ} (hX : 0 < X) (hH : 0 < H) :
    (∫ u in 0..2 * H / (X + H), u ^ 2) ≤ 8 * H ^ 3 / X ^ 3 := by
  have hD0 : 0 ≤ 2 * H / (X + H) := by positivity
  have hDX : 2 * H / (X + H) ≤ 2 * H / X :=
    div_le_div_of_nonneg_left (by positivity) hX (by linarith)
  calc
    _ ≤ (2 * H / (X + H)) ^ 3 := lemma14_quadratic_moment_le_cube (le_refl 0) hD0
    _ ≤ (2 * H / X) ^ 3 := pow_le_pow_left₀ hD0 hDX 3
    _ = _ := by ring

/-- Absolute constant for the central spatial energy. -/
def lemma14UniversalScaledLowConstant : ℝ :=
  2160 * Complex.normSq ((((2 * Real.pi : ℝ) : ℂ))⁻¹) *
    (lemma14UniversalFourierCauchyConstant * Real.pi)

theorem lemma14UniversalScaledLowConstant_nonneg :
    0 ≤ lemma14UniversalScaledLowConstant := by
  unfold lemma14UniversalScaledLowConstant
  exact mul_nonneg
    (mul_nonneg (by norm_num) (Complex.normSq_nonneg _))
    (mul_nonneg lemma14UniversalFourierCauchyConstant_nonneg Real.pi_pos.le)

/-- The short-length powers cancel against the quadratic source moments. -/
theorem lemma14UniversalPerronSegmentLowCoefficient_le
    {X H : ℝ} (hX : 0 < X) (hH : 0 < H) (hHX : H ≤ X) :
    lemma14UniversalPerronSegmentLowCoefficient X (2 * X) H ≤
      lemma14UniversalScaledLowConstant * X := by
  let K : ℝ := lemma14UniversalFourierCauchyConstant * Real.pi
  let IL : ℝ := ∫ u in H / (2 * X)..3 * H / X, u ^ 2
  let IR : ℝ := ∫ u in 0..2 * H / (X + H), u ^ 2
  have hK : 0 ≤ K :=
    mul_nonneg lemma14UniversalFourierCauchyConstant_nonneg Real.pi_pos.le
  have hIR : 0 ≤ IR := by
    exact intervalIntegral.integral_nonneg (by positivity) (fun u hu ↦ sq_nonneg _)
  have hILb : IL ≤ 27 * H ^ 3 / X ^ 3 := lemma14_left_source_low_moment_le hX hH
  have hIRb : IR ≤ 8 * H ^ 3 / X ^ 3 := lemma14_right_source_low_moment_le hX hH
  have hfacL : 0 ≤ (2 * X) ^ 4 / H ^ 3 := by positivity
  have hleft :
      ((2 * X) / H ^ 3) * ((2 * X) ^ 3 * K * IL) ≤ 432 * K * X := by
    calc
      _ = K * (((2 * X) ^ 4 / H ^ 3) * IL) := by ring
      _ ≤ K * (((2 * X) ^ 4 / H ^ 3) * (27 * H ^ 3 / X ^ 3)) := by gcongr
      _ = 432 * K * X := by field_simp [hX.ne', hH.ne']; ring
  have hpowR : (2 * X + H) ^ 4 ≤ (3 * X) ^ 4 :=
    pow_le_pow_left₀ (by positivity) (by linarith) 4
  have hfacR : (2 * X + H) ^ 4 / H ^ 3 ≤ 81 * X ^ 4 / H ^ 3 := by
    have hdiv := div_le_div_of_nonneg_right hpowR (pow_nonneg hH.le 3)
    simpa only [show (3 * X) ^ 4 = 81 * X ^ 4 by ring] using hdiv
  have hright :
      ((2 * X + H) / H ^ 3) * ((2 * X + H) ^ 3 * K * IR) ≤ 648 * K * X := by
    calc
      _ = K * (((2 * X + H) ^ 4 / H ^ 3) * IR) := by ring
      _ ≤ K * ((81 * X ^ 4 / H ^ 3) * IR) := by gcongr
      _ ≤ K * ((81 * X ^ 4 / H ^ 3) * (8 * H ^ 3 / X ^ 3)) := by gcongr
      _ = 648 * K * X := by field_simp [hX.ne', hH.ne']; ring
  unfold lemma14UniversalPerronSegmentLowCoefficient lemma14UniversalScaledLowConstant
  change 2 * Complex.normSq ((((2 * Real.pi : ℝ) : ℂ))⁻¹) *
    ((((2 * X) / H ^ 3) * ((2 * X) ^ 3 * K * IL)) +
      (((2 * X + H) / H ^ 3) * ((2 * X + H) ^ 3 * K * IR))) ≤ _
  calc
    _ ≤ 2 * Complex.normSq ((((2 * Real.pi : ℝ) : ℂ))⁻¹) *
        (432 * K * X + 648 * K * X) :=
      mul_le_mul_of_nonneg_left (add_le_add hleft hright)
        (mul_nonneg (by norm_num) (Complex.normSq_nonneg _))
    _ = _ := by dsimp only [K]; ring

/-- Sharp central energy on a dyadic spatial interval, on any finite band. -/
theorem integral_normSq_perronKernelSegmentOn_le_scaled_low
    (F : ℝ → ℂ) (hF : Continuous F)
    {X H A B : ℝ} (hX : 0 < X) (hH : 0 < H) (hHX : H ≤ X) (hAB : A ≤ B) :
    (∫ x in X..2 * X, Complex.normSq (perronKernelSegmentOn F x H A B)) ≤
      lemma14UniversalScaledLowConstant * X * ∫ t in A..B, Complex.normSq (F t) := by
  have hE : 0 ≤ ∫ t in A..B, Complex.normSq (F t) :=
    intervalIntegral.integral_nonneg hAB (fun t ht ↦ Complex.normSq_nonneg _)
  exact (integral_normSq_perronKernelSegmentOn_le_low_universal
    F hF hX (by linarith) (by linarith) hH hAB).trans
      (mul_le_mul_of_nonneg_right
        (lemma14UniversalPerronSegmentLowCoefficient_le hX hH hHX) hE)

/-- The sharp bound on the exact shifted unit-cell window. -/
theorem integral_normSq_perronKernelSegmentOn_le_shifted_scaled_low
    (F : ℝ → ℂ) (hF : Continuous F)
    {X H : ℕ} (hH : 0 < H) (hHX : H ≤ X) {A B : ℝ} (hAB : A ≤ B) :
    (∫ x in ((X : ℝ) + 1)..(((2 * X : ℕ) : ℝ) + 1),
        Complex.normSq (perronKernelSegmentOn F x H A B)) ≤
      lemma14UniversalScaledLowConstant * ((X : ℝ) + 1) *
        ∫ t in A..B, Complex.normSq (F t) := by
  have hP : 0 < (X : ℝ) + 1 := by positivity
  have hHR : (0 : ℝ) < H := by exact_mod_cast hH
  have hHP : (H : ℝ) ≤ (X : ℝ) + 1 := by
    exact_mod_cast (hHX.trans (Nat.le_add_right X 1))
  have hPQ : (X : ℝ) + 1 ≤ ((2 * X : ℕ) : ℝ) + 1 := by
    norm_num only [Nat.cast_mul, Nat.cast_ofNat]
    have hX0 := Nat.cast_nonneg (α := ℝ) X
    linarith
  have hQtwo : (((2 * X : ℕ) : ℝ) + 1) ≤ 2 * ((X : ℝ) + 1) := by
    norm_num only [Nat.cast_mul, Nat.cast_ofNat]
    linarith
  have hcont : IntervalIntegrable
      (fun x ↦ Complex.normSq (perronKernelSegmentOn F x H A B)) volume
      ((X : ℝ) + 1) (2 * ((X : ℝ) + 1)) := by
    apply ContinuousOn.intervalIntegrable_of_Icc (by linarith)
    exact Complex.continuous_normSq.comp_continuousOn
      ((continuousOn_perronKernelSegmentOn F hF hP hHR A B).mono
        Set.Icc_subset_Ici_self)
  exact (intervalIntegral.integral_mono_interval (le_refl _) hPQ hQtwo
    (Filter.Eventually.of_forall fun x ↦ Complex.normSq_nonneg _) hcont).trans
      (integral_normSq_perronKernelSegmentOn_le_scaled_low F hF hP hHR hHP hAB)

/-- The actual discrete short-interval input with no central height loss. -/
theorem normalized_uncenteredShortIntervalMeanSquare_le_scaled_low_add_weightedHigh
    (S : Finset ℕ) (f : ℕ → ℂ) (Y : ℕ)
    {X H : ℕ} (hH : 0 < H) (hHX : H ≤ X) {T Efar : ℝ}
    (hT : 0 < T) (hEfar : 0 ≤ Efar)
    (hfar : ∀ U : ℝ, T ≤ U →
      (∫ t in -U..-T, lemma14SafeReciprocalSqWeight T t *
          Complex.normSq (dyadicVerticalDirichletPolynomial S f Y t)) +
        ∫ t in T..U, lemma14SafeReciprocalSqWeight T t *
          Complex.normSq (dyadicVerticalDirichletPolynomial S f Y t) ≤ Efar) :
    uncenteredShortIntervalMeanSquare (dyadicRestrictedCoefficient S f Y) X H /
        (H : ℝ) ^ 2 ≤
      2 * lemma14UniversalScaledLowConstant * ((X : ℝ) + 1) *
        (∫ t in -T..T, Complex.normSq (dyadicVerticalDirichletPolynomial S f Y t)) +
      4 * (lemma14UniversalScaledHighConstant * ((X : ℝ) + 1) ^ 3 /
        (H : ℝ) ^ 2) * Efar := by
  have hbase := normalized_uncenteredShortIntervalMeanSquare_le_central_add_weightedHigh
    S f Y (X := X) hH hT hEfar hfar
  have hcentral := integral_normSq_perronKernelSegmentOn_le_shifted_scaled_low
    (dyadicVerticalDirichletPolynomial S f Y)
    (continuous_dyadicVerticalDirichletPolynomial S f Y)
    (X := X) hH hHX (show -T ≤ T by linarith)
  have hhigh := mul_le_mul_of_nonneg_right
    (lemma14UniversalPerronSegmentSafeWeightedCoefficient_shifted_le hH hHX) hEfar
  nlinarith

end

end Erdos67b
