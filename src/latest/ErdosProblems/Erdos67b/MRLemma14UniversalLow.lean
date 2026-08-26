import ErdosProblems.Erdos67b.MRLemma14ContinuousHigh

/-!
# Universal low-frequency Perron energy

The proved spatial Fourier estimate and the quadratic source-multiplier
bound give a constant independent of the vertical band length.
The source averages and the actual Perron segment are unchanged.
-/

open Finset MeasureTheory Set

namespace Erdos67b

noncomputable section

theorem intervalIntegral_intervalIntegral_normSq_realSafeSmoothed_le_low_universal
    (F : ℝ → ℂ) (hF : Continuous F)
    {P Q C D : ℝ} (hP : 0 < P) (hPQ : P ≤ Q) (hQ3P : Q ≤ 3 * P)
    (hC : 0 ≤ C) (hCD : C ≤ D)
    {A B : ℝ} (hAB : A ≤ B) :
    (∫ x in P..Q, ∫ u in C..D,
        Complex.normSq
          (lemma14RealSafeSmoothedMellinSegment F u A B x)) ≤
      Q ^ 3 * (lemma14UniversalFourierCauchyConstant * Real.pi) *
        (∫ u in C..D, u ^ 2) *
        ∫ t in A..B,
          Complex.normSq (F t) := by
  let K : ℝ := Q ^ 3 *
    (lemma14UniversalFourierCauchyConstant * Real.pi)
  let E : ℝ := ∫ t in A..B,
    Complex.normSq (F t)
  have hK : 0 ≤ K := by
    dsimp only [K]
    exact mul_nonneg (pow_nonneg (hP.trans_le hPQ).le 3)
      (mul_nonneg lemma14UniversalFourierCauchyConstant_nonneg Real.pi_pos.le)
  have hmono :
      (∫ u in C..D, ∫ t in A..B,
          Complex.normSq (F t * safePerronRatioIncrement u t)) ≤
        ∫ u in C..D, u ^ 2 * E := by
    apply intervalIntegral.integral_mono_on hCD
    · exact (continuous_safePerronMultiplierEnergy F hF A B).intervalIntegrable _ _
    · exact (by fun_prop : Continuous
        (fun u : ℝ ↦ u ^ 2 * E)).intervalIntegrable _ _
    · intro u hu
      exact integral_normSq_mul_safePerronRatioIncrement_le_self
        F hF (hC.trans hu.1) hAB
  have hbase :=
    intervalIntegral_intervalIntegral_normSq_realSafeSmoothed_le_universal
      F hF hP hPQ hQ3P hCD hAB
  calc
    (∫ x in P..Q, ∫ u in C..D,
        Complex.normSq
          (lemma14RealSafeSmoothedMellinSegment F u A B x)) ≤
      K * ∫ u in C..D, ∫ t in A..B,
        Complex.normSq (F t * safePerronRatioIncrement u t) := by
          simpa only [K, mul_assoc] using hbase
    _ ≤ K * ∫ u in C..D, u ^ 2 * E :=
      mul_le_mul_of_nonneg_left hmono hK
    _ = K * (∫ u in C..D, u ^ 2) * E := by
      rw [intervalIntegral.integral_mul_const]
      ring
    _ = _ := by rfl

theorem integral_normSq_lemma14RealSourceSmoothedLeftOn_le_low_universal
    (F : ℝ → ℂ) (hF : Continuous F)
    {P Q h : ℝ} (hP : 0 < P) (hPQ : P ≤ Q) (hQ3P : Q ≤ 3 * P)
    (hh : 0 < h) {A B : ℝ} (hAB : A ≤ B) :
    (∫ x in P..Q,
        Complex.normSq (lemma14RealSourceSmoothedLeftOn F x h A B)) ≤
      (Q / h ^ 3) *
        (Q ^ 3 * (lemma14UniversalFourierCauchyConstant * Real.pi) *
          (∫ u in h / Q..3 * h / P, u ^ 2) *
          ∫ t in A..B,
            Complex.normSq (F t)) := by
  have hQ : 0 < Q := hP.trans_le hPQ
  have hCD : h / Q ≤ 3 * h / P := by
    have h1 : h / Q ≤ h / P :=
      div_le_div_of_nonneg_left hh.le hP hPQ
    have h2 : h / P ≤ 3 * h / P := by
      have hp : 0 < h / P := by positivity
      rw [show 3 * h / P = 3 * (h / P) by ring]
      linarith
    exact h1.trans h2
  have hrect :=
    integral_normSq_lemma14RealSourceSmoothedLeftOn_le_rectangle
      F hF hP hPQ hh A B
  have hsmooth :=
    intervalIntegral_intervalIntegral_normSq_realSafeSmoothed_le_low_universal
      F hF hP hPQ hQ3P (by positivity : 0 ≤ h / Q) hCD hAB
  calc
    (∫ x in P..Q,
        Complex.normSq (lemma14RealSourceSmoothedLeftOn F x h A B)) ≤
      (Q / h ^ 3) *
        ∫ x in P..Q, ∫ u in h / Q..3 * h / P,
          Complex.normSq
            (lemma14RealSafeSmoothedMellinSegment F u A B x) := hrect
    _ ≤ (Q / h ^ 3) *
        (Q ^ 3 * (lemma14UniversalFourierCauchyConstant * Real.pi) *
          (∫ u in h / Q..3 * h / P, u ^ 2) *
          ∫ t in A..B,
            Complex.normSq (F t)) :=
      mul_le_mul_of_nonneg_left hsmooth
        (div_nonneg hQ.le (pow_nonneg hh.le 3))

theorem integral_normSq_lemma14RealSourceSmoothedRightOn_le_low_universal
    (F : ℝ → ℂ) (hF : Continuous F)
    {P Q h : ℝ} (hP : 0 < P) (hPQ : P ≤ Q) (hQ3P : Q ≤ 3 * P)
    (hh : 0 < h) {A B : ℝ} (hAB : A ≤ B) :
    (∫ x in P..Q,
        Complex.normSq (lemma14RealSourceSmoothedRightOn F x h A B)) ≤
      ((Q + h) / h ^ 3) *
        ((Q + h) ^ 3 *
          (lemma14UniversalFourierCauchyConstant * Real.pi) *
          (∫ u in 0..2 * h / (P + h), u ^ 2) *
          ∫ t in A..B,
            Complex.normSq (F t)) := by
  have hPh : 0 < P + h := add_pos hP hh
  have hshift : P + h ≤ Q + h := by linarith
  have hshift3 : Q + h ≤ 3 * (P + h) := by linarith
  have hD : 0 ≤ 2 * h / (P + h) := by positivity
  have hrect :=
    integral_normSq_lemma14RealSourceSmoothedRightOn_le_rectangle
      F hF hP hPQ hh A B
  have hsmooth :=
    intervalIntegral_intervalIntegral_normSq_realSafeSmoothed_le_low_universal
      F hF hPh hshift hshift3 (le_refl 0) hD hAB
  calc
    (∫ x in P..Q,
        Complex.normSq (lemma14RealSourceSmoothedRightOn F x h A B)) ≤
      ((Q + h) / h ^ 3) *
        ∫ z in (P + h)..(Q + h), ∫ u in 0..2 * h / (P + h),
          Complex.normSq
            (lemma14RealSafeSmoothedMellinSegment F u A B z) := hrect
    _ ≤ ((Q + h) / h ^ 3) *
        ((Q + h) ^ 3 *
          (lemma14UniversalFourierCauchyConstant * Real.pi) *
          (∫ u in 0..2 * h / (P + h), u ^ 2) *
          ∫ t in A..B,
            Complex.normSq (F t)) :=
      mul_le_mul_of_nonneg_left hsmooth
        (div_nonneg (add_pos (hP.trans_le hPQ) hh).le
          (pow_nonneg hh.le 3))

/-- The universal quadratic-moment coefficient for a finite Perron segment. -/
def lemma14UniversalPerronSegmentLowCoefficient (P Q h : ℝ) : ℝ :=
  2 * Complex.normSq ((((2 * Real.pi : ℝ) : ℂ))⁻¹) *
    ((Q / h ^ 3) *
      (Q ^ 3 * (lemma14UniversalFourierCauchyConstant * Real.pi) *
        (∫ u in h / Q..3 * h / P, u ^ 2)) +
      ((Q + h) / h ^ 3) *
      ((Q + h) ^ 3 * (lemma14UniversalFourierCauchyConstant * Real.pi) *
        (∫ u in 0..2 * h / (P + h), u ^ 2)))

theorem integral_normSq_perronKernelSegmentOn_le_low_universal
    (F : ℝ → ℂ) (hF : Continuous F)
    {P Q h : ℝ} (hP : 0 < P) (hPQ : P ≤ Q) (hQ3P : Q ≤ 3 * P)
    (hh : 0 < h) {A B : ℝ} (hAB : A ≤ B) :
    (∫ x in P..Q,
        Complex.normSq (perronKernelSegmentOn F x h A B)) ≤
      lemma14UniversalPerronSegmentLowCoefficient P Q h *
        ∫ t in A..B,
          Complex.normSq (F t) := by
  let E : ℝ := ∫ t in A..B,
    Complex.normSq (F t)
  let EL : ℝ := (Q / h ^ 3) *
    (Q ^ 3 * (lemma14UniversalFourierCauchyConstant * Real.pi) *
      (∫ u in h / Q..3 * h / P, u ^ 2) * E)
  let ER : ℝ := ((Q + h) / h ^ 3) *
    ((Q + h) ^ 3 * (lemma14UniversalFourierCauchyConstant * Real.pi) *
      (∫ u in 0..2 * h / (P + h), u ^ 2) * E)
  have hL : (∫ x in P..Q,
      Complex.normSq (lemma14RealSourceSmoothedLeftOn F x h A B)) ≤ EL := by
    exact integral_normSq_lemma14RealSourceSmoothedLeftOn_le_low_universal
      F hF hP hPQ hQ3P hh hAB
  have hR : (∫ x in P..Q,
      Complex.normSq (lemma14RealSourceSmoothedRightOn F x h A B)) ≤ ER := by
    exact integral_normSq_lemma14RealSourceSmoothedRightOn_le_low_universal
      F hF hP hPQ hQ3P hh hAB
  have hbase := integral_normSq_perronKernelSegmentOn_le_of_sourceBounds
    F hF hP hPQ hh A B EL ER hL hR
  calc
    (∫ x in P..Q,
        Complex.normSq (perronKernelSegmentOn F x h A B)) ≤
      2 * Complex.normSq ((((2 * Real.pi : ℝ) : ℂ))⁻¹) *
        (EL + ER) := hbase
    _ = lemma14UniversalPerronSegmentLowCoefficient P Q h * E := by
      unfold lemma14UniversalPerronSegmentLowCoefficient
      dsimp only [EL, ER]
      ring
    _ = _ := by rfl

end

end Erdos67b
