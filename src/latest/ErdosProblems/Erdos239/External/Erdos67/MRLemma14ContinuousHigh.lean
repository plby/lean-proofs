import ErdosProblems.Erdos239.External.Erdos67.MRLemma14ContinuousSchur
import ErdosProblems.Erdos239.External.Erdos67.MRRealEndpointMeanSquare

/-!
# Continuous-endpoint high-frequency estimate for Lemma 14

This file joins the source-correct continuous Schur estimate to the Mellin
monomial that occurs in Perron's formula.  The logarithmic change of
variables costs only the expected cubic spatial scale and, crucially, no
term depending on the length of the vertical band.
-/

open scoped ComplexConjugate FourierTransform SchwartzMap
open MeasureTheory

namespace Erdos67

noncomputable section

/-- A finite Mellin segment on the line `Re s = 1`. -/
def lemma14MellinSegment
    (g : ℝ → ℂ) (A B x : ℝ) : ℂ :=
  ∫ t in A..B, g t *
    (x : ℂ) ^ ((1 : ℂ) + (t : ℂ) * Complex.I)

/-- On the positive half-line, the Mellin segment is the logarithmic
analysis transform evaluated at `-log x`, with its exact factor `x`.
-/
theorem lemma14MellinSegment_eq_logSpatialTransform
    (g : ℝ → ℂ) {x : ℝ} (hx : 0 < x) (A B : ℝ) :
    lemma14MellinSegment g A B x =
      (x : ℂ) * lemma14LogSpatialTransform g A B (-Real.log x) := by
  unfold lemma14MellinSegment lemma14LogSpatialTransform
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro t ht
  change g t *
      (x : ℂ) ^ ((1 : ℂ) + (t : ℂ) * Complex.I) =
    (x : ℂ) * (g t * realExponentialPhase (-t * -Real.log x))
  rw [ofReal_cpow_one_add_mul_I_eq_phase hx]
  have hphase : realExponentialPhase (t * Real.log x) =
      realExponentialPhase (-t * -Real.log x) := by
    congr 1
    ring
  rw [hphase]
  ring

/-- Continuity of a finite Mellin segment on the positive half-line. -/
theorem continuousOn_lemma14MellinSegment
    (g : ℝ → ℂ) (hg : Continuous g) (A B : ℝ) :
    ContinuousOn (lemma14MellinSegment g A B) (Set.Ioi 0) := by
  let H : ℝ → ℂ := lemma14LogSpatialTransform g A B
  have hH : Continuous H := continuous_lemma14LogSpatialTransform g hg A B
  have halt : ContinuousOn
      (fun x : ℝ ↦ (x : ℂ) * H (-Real.log x)) (Set.Ioi 0) := by
    intro x hx
    change ContinuousWithinAt
      (Complex.ofReal * (H ∘ (-Real.log))) (Set.Ioi 0) x
    exact (Complex.continuous_ofReal.continuousAt.mul
      (hH.continuousAt.comp ((Real.continuousAt_log hx.ne').neg))).continuousWithinAt
  apply halt.congr
  intro x hx
  exact lemma14MellinSegment_eq_logSpatialTransform g hx A B

/-- Exact logarithmic substitution for the square of a finite Mellin
segment. -/
theorem integral_normSq_lemma14MellinSegment_eq_log
    (g : ℝ → ℂ) (hg : Continuous g) {P Q : ℝ}
    (hP : 0 < P) (hPQ : P ≤ Q) (A B : ℝ) :
    (∫ x in P..Q, Complex.normSq (lemma14MellinSegment g A B x)) =
      ∫ y in (-Real.log Q)..(-Real.log P),
        Real.exp (-3 * y) *
          Complex.normSq (lemma14LogSpatialTransform g A B y) := by
  have hQ : 0 < Q := hP.trans_le hPQ
  let e : ℝ → ℝ := fun x ↦
    Complex.normSq (lemma14MellinSegment g A B x)
  have he : ContinuousOn e (Set.Ioi 0) := by
    change ContinuousOn
      (Complex.normSq ∘ lemma14MellinSegment g A B) (Set.Ioi 0)
    exact Complex.continuous_normSq.comp_continuousOn
      (continuousOn_lemma14MellinSegment g hg A B)
  have himage : (fun y : ℝ ↦ Real.exp (-y)) ''
      Set.uIcc (-Real.log Q) (-Real.log P) ⊆ Set.Ioi (0 : ℝ) := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact Real.exp_pos _
  have hsub := intervalIntegral.integral_comp_mul_deriv'
    (a := -Real.log Q) (b := -Real.log P)
    (f := fun y : ℝ ↦ Real.exp (-y))
    (f' := fun y : ℝ ↦ -Real.exp (-y))
    (g := e)
    (fun y hy ↦ by
      change HasDerivAt (Real.exp ∘ fun z : ℝ ↦ -z) (-Real.exp (-y)) y
      simpa only [mul_neg, mul_one] using
        (Real.hasDerivAt_exp (-y)).comp y (hasDerivAt_neg y))
    (by fun_prop)
    (he.mono himage)
  have hendQ : Real.exp (-(-Real.log Q)) = Q := by
    simp [Real.exp_log hQ]
  have hendP : Real.exp (-(-Real.log P)) = P := by
    simp [Real.exp_log hP]
  rw [hendQ, hendP] at hsub
  have hrewrite :
      (fun y : ℝ ↦
          e (Real.exp (-y)) * (-Real.exp (-y))) =
        fun y ↦ -(Real.exp (-3 * y) *
          Complex.normSq (lemma14LogSpatialTransform g A B y)) := by
    funext y
    have hexp : 0 < Real.exp (-y) := Real.exp_pos _
    rw [show e (Real.exp (-y)) =
        Complex.normSq
          ((Real.exp (-y) : ℂ) *
            lemma14LogSpatialTransform g A B y) by
      dsimp only [e]
      rw [lemma14MellinSegment_eq_logSpatialTransform g hexp A B]
      congr 2
      rw [Real.log_exp]
      ring]
    rw [Complex.normSq_mul]
    have hsq : Complex.normSq (Real.exp (-y) : ℂ) = Real.exp (-2 * y) := by
      rw [Complex.normSq_ofReal]
      simp only [sq, ← Real.exp_add]
      congr 1
      ring
    rw [hsq]
    calc
      Real.exp (-2 * y) *
            Complex.normSq (lemma14LogSpatialTransform g A B y) *
          -Real.exp (-y) =
        -((Real.exp (-2 * y) * Real.exp (-y)) *
          Complex.normSq (lemma14LogSpatialTransform g A B y)) := by ring
      _ = -(Real.exp (-3 * y) *
          Complex.normSq (lemma14LogSpatialTransform g A B y)) := by
        rw [← Real.exp_add]
        congr 3
        ring
  change (∫ y in (-Real.log Q)..(-Real.log P),
      e (Real.exp (-y)) * (-Real.exp (-y))) =
    ∫ x in Q..P, e x at hsub
  rw [hrewrite, intervalIntegral.integral_neg] at hsub
  change (∫ x in P..Q, e x) = _
  calc
    (∫ x in P..Q, e x) = -(∫ x in Q..P, e x) := by
      rw [intervalIntegral.integral_symm]
    _ = -(-(∫ y in (-Real.log Q)..(-Real.log P),
        Real.exp (-3 * y) *
          Complex.normSq (lemma14LogSpatialTransform g A B y))) := by rw [← hsub]
    _ = _ := neg_neg _

/-- Source-form continuous-endpoint mean-square estimate.  Its constant is
independent of `B-A`; all dependence on the vertical segment is through the
original `L²` energy. -/
theorem integral_normSq_lemma14MellinSegment_le
    (g : ℝ → ℂ) (hg : Continuous g)
    {P Q : ℝ} (hP : 0 < P) (hPQ : P ≤ Q)
    (delta L R : ℝ) (hdelta : 0 < delta)
    (hleft : L + 2 * delta ≤ -Real.log Q)
    (hright : -Real.log P ≤ R - 2 * delta)
    {A B : ℝ} (hAB : A ≤ B) :
    (∫ x in P..Q, Complex.normSq (lemma14MellinSegment g A B x)) ≤
      Q ^ 3 *
        (lemma14FourierCauchyConstant
            (lemma14PositiveLogCutoff delta L R hdelta) * Real.pi *
          ∫ t in A..B, Complex.normSq (g t)) := by
  have hQ : 0 < Q := hP.trans_le hPQ
  have hlog : -Real.log Q ≤ -Real.log P := by
    exact neg_le_neg (Real.strictMonoOn_log.monotoneOn hP hQ hPQ)
  have hLR : L + 2 * delta ≤ R - 2 * delta :=
    hleft.trans (hlog.trans hright)
  have htransform := intervalIntegral_normSq_logSpatialTransform_le
    g hg delta L R hdelta hLR hAB
  have henlarge :
      (∫ y in (-Real.log Q)..(-Real.log P),
          Complex.normSq (lemma14LogSpatialTransform g A B y)) ≤
        ∫ y in (L + 2 * delta)..(R - 2 * delta),
          Complex.normSq (lemma14LogSpatialTransform g A B y) := by
    exact intervalIntegral.integral_mono_interval hleft hlog hright
      (MeasureTheory.ae_of_all _ (fun y ↦ Complex.normSq_nonneg _))
      ((Complex.continuous_normSq.comp
        (continuous_lemma14LogSpatialTransform g hg A B)).intervalIntegrable _ _)
  rw [integral_normSq_lemma14MellinSegment_eq_log g hg hP hPQ A B]
  have hweight (y : ℝ) (hy : y ∈ Set.Icc (-Real.log Q) (-Real.log P)) :
      Real.exp (-3 * y) ≤ Q ^ 3 := by
    have hyQ : -Real.log Q ≤ y := hy.1
    have hmono : -3 * y ≤ 3 * Real.log Q := by linarith
    calc
      Real.exp (-3 * y) ≤ Real.exp (3 * Real.log Q) := Real.exp_le_exp.mpr hmono
      _ = Q ^ 3 := by
        rw [show 3 * Real.log Q =
          Real.log Q + Real.log Q + Real.log Q by ring,
          Real.exp_add, Real.exp_add, Real.exp_log hQ]
        ring
  calc
    (∫ y in (-Real.log Q)..(-Real.log P),
        Real.exp (-3 * y) *
          Complex.normSq (lemma14LogSpatialTransform g A B y)) ≤
      ∫ y in (-Real.log Q)..(-Real.log P),
        Q ^ 3 * Complex.normSq (lemma14LogSpatialTransform g A B y) := by
      apply intervalIntegral.integral_mono_on hlog
      · exact ((by
          exact (Real.continuous_exp.comp (by fun_prop)).mul
            (Complex.continuous_normSq.comp
              (continuous_lemma14LogSpatialTransform g hg A B))) :
          Continuous (fun y : ℝ ↦ Real.exp (-3 * y) *
            Complex.normSq (lemma14LogSpatialTransform g A B y))).intervalIntegrable _ _
      · exact ((continuous_const.mul
          (Complex.continuous_normSq.comp
            (continuous_lemma14LogSpatialTransform g hg A B))) :
          Continuous (fun y : ℝ ↦ Q ^ 3 * Complex.normSq
            (lemma14LogSpatialTransform g A B y))).intervalIntegrable _ _
      · intro y hy
        exact mul_le_mul_of_nonneg_right (hweight y hy)
          (Complex.normSq_nonneg _)
    _ = Q ^ 3 * (∫ y in (-Real.log Q)..(-Real.log P),
          Complex.normSq (lemma14LogSpatialTransform g A B y)) := by
      rw [intervalIntegral.integral_const_mul]
    _ ≤ Q ^ 3 * (∫ y in (L + 2 * delta)..(R - 2 * delta),
          Complex.normSq (lemma14LogSpatialTransform g A B y)) :=
      mul_le_mul_of_nonneg_left henlarge (by positivity)
    _ ≤ Q ^ 3 *
        (lemma14FourierCauchyConstant
            (lemma14PositiveLogCutoff delta L R hdelta) * Real.pi *
          ∫ t in A..B, Complex.normSq (g t)) :=
      mul_le_mul_of_nonneg_left htransform (by positivity)

/-! ## A universal logarithmic cutoff -/

/-- One fixed cutoff whose plateau contains `[-log 3,0]`. -/
def lemma14UniversalLogCutoff : 𝓢(ℝ, ℂ) :=
  lemma14PositiveLogCutoff 1 (-Real.log 3 - 2) 2 (by norm_num)

/-- The resulting absolute Fourier--Schur constant.  This definition has
no spatial-scale parameter. -/
def lemma14UniversalFourierCauchyConstant : ℝ :=
  lemma14FourierCauchyConstant lemma14UniversalLogCutoff

theorem lemma14UniversalFourierCauchyConstant_nonneg :
    0 ≤ lemma14UniversalFourierCauchyConstant :=
  lemma14FourierCauchyConstant_nonneg lemma14UniversalLogCutoff

/-- Modulation of the vertical coefficient corresponding to translation
of the logarithmic spatial variable. -/
def lemma14VerticalModulation (g : ℝ → ℂ) (a t : ℝ) : ℂ :=
  g t * realExponentialPhase (t * a)

theorem continuous_lemma14VerticalModulation
    (g : ℝ → ℂ) (hg : Continuous g) (a : ℝ) :
    Continuous (lemma14VerticalModulation g a) := by
  unfold lemma14VerticalModulation
  exact hg.mul (continuous_realExponentialPhase.comp (by fun_prop))

theorem normSq_lemma14VerticalModulation
    (g : ℝ → ℂ) (a t : ℝ) :
    Complex.normSq (lemma14VerticalModulation g a t) =
      Complex.normSq (g t) := by
  unfold lemma14VerticalModulation
  rw [Complex.normSq_mul]
  have hphase : Complex.normSq (realExponentialPhase (t * a)) = 1 := by
    rw [Complex.normSq_eq_norm_sq, norm_realExponentialPhase]
    norm_num
  rw [hphase, mul_one]

/-- Translating logarithmic space is exactly vertical modulation. -/
theorem lemma14LogSpatialTransform_verticalModulation
    (g : ℝ → ℂ) (a y A B : ℝ) :
    lemma14LogSpatialTransform (lemma14VerticalModulation g a) A B (y + a) =
      lemma14LogSpatialTransform g A B y := by
  unfold lemma14LogSpatialTransform lemma14VerticalModulation
  apply intervalIntegral.integral_congr
  intro t ht
  change g t * realExponentialPhase (t * a) *
      realExponentialPhase (-t * (y + a)) =
    g t * realExponentialPhase (-t * y)
  rw [mul_assoc]
  apply congrArg (g t * ·)
  unfold realExponentialPhase
  rw [← Complex.exp_add]
  congr 2
  push_cast
  ring

/-- The fixed cutoff controls every logarithmic interval coming from a
spatial interval `[P,Q]` of multiplicative width at most three. -/
theorem intervalIntegral_normSq_logSpatialTransform_le_universal
    (g : ℝ → ℂ) (hg : Continuous g)
    {P Q : ℝ} (hP : 0 < P) (hPQ : P ≤ Q) (hQ3P : Q ≤ 3 * P)
    {A B : ℝ} (hAB : A ≤ B) :
    (∫ y in (-Real.log Q)..(-Real.log P),
        Complex.normSq (lemma14LogSpatialTransform g A B y)) ≤
      lemma14UniversalFourierCauchyConstant * Real.pi *
        ∫ t in A..B, Complex.normSq (g t) := by
  let a : ℝ := Real.log P
  let g' : ℝ → ℂ := lemma14VerticalModulation g a
  have hg' : Continuous g' := continuous_lemma14VerticalModulation g hg a
  have hQ : 0 < Q := hP.trans_le hPQ
  have hlog : -Real.log Q ≤ -Real.log P :=
    neg_le_neg (Real.log_le_log hP hPQ)
  have hlower : -Real.log 3 ≤ -Real.log Q + a := by
    have hlogmul : Real.log Q ≤ Real.log 3 + Real.log P := by
      calc
        Real.log Q ≤ Real.log (3 * P) := Real.log_le_log hQ hQ3P
        _ = Real.log 3 + Real.log P := Real.log_mul (by norm_num) hP.ne'
    dsimp only [a]
    linarith
  have hupper : -Real.log P + a = 0 := by
    dsimp only [a]
    ring
  have hplateau : -Real.log 3 ≤ 0 := by
    exact neg_nonpos.mpr (Real.log_nonneg (by norm_num))
  have hfixed := intervalIntegral_normSq_logSpatialTransform_le
    g' hg' 1 (-Real.log 3 - 2) 2 (by norm_num) (by
      norm_num
      exact Real.log_nonneg (by norm_num)) hAB
  have hshift :
      (∫ y in (-Real.log Q)..(-Real.log P),
          Complex.normSq (lemma14LogSpatialTransform g A B y)) =
        ∫ z in (-Real.log Q + a)..(-Real.log P + a),
          Complex.normSq (lemma14LogSpatialTransform g' A B z) := by
    rw [← intervalIntegral.integral_comp_add_right
      (fun z ↦ Complex.normSq (lemma14LogSpatialTransform g' A B z)) a]
    apply intervalIntegral.integral_congr
    intro y hy
    exact congrArg Complex.normSq
      (lemma14LogSpatialTransform_verticalModulation g a y A B).symm
  rw [hshift]
  have henlarge :
      (∫ z in (-Real.log Q + a)..(-Real.log P + a),
          Complex.normSq (lemma14LogSpatialTransform g' A B z)) ≤
        ∫ z in (-Real.log 3)..0,
          Complex.normSq (lemma14LogSpatialTransform g' A B z) := by
    rw [hupper]
    exact intervalIntegral.integral_mono_interval hlower
      (by linarith [hlog, hupper]) (le_refl 0)
      (MeasureTheory.ae_of_all _ (fun z ↦ Complex.normSq_nonneg _))
      ((Complex.continuous_normSq.comp
        (continuous_lemma14LogSpatialTransform g' hg' A B)).intervalIntegrable _ _)
  calc
    (∫ z in (-Real.log Q + a)..(-Real.log P + a),
        Complex.normSq (lemma14LogSpatialTransform g' A B z)) ≤
      ∫ z in (-Real.log 3)..0,
        Complex.normSq (lemma14LogSpatialTransform g' A B z) := henlarge
    _ ≤ lemma14FourierCauchyConstant
          (lemma14PositiveLogCutoff 1 (-Real.log 3 - 2) 2 (by norm_num)) *
        Real.pi * ∫ t in A..B, Complex.normSq (g' t) := by
      convert hfixed using 1 <;> ring
    _ = lemma14UniversalFourierCauchyConstant * Real.pi *
        ∫ t in A..B, Complex.normSq (g t) := by
      unfold lemma14UniversalFourierCauchyConstant lemma14UniversalLogCutoff
      apply congrArg
        (lemma14FourierCauchyConstant
            (lemma14PositiveLogCutoff 1 (-Real.log 3 - 2) 2 (by norm_num)) *
          Real.pi * ·)
      apply intervalIntegral.integral_congr
      intro t ht
      exact normSq_lemma14VerticalModulation g a t

/-- Universal-cutoff Mellin mean-square estimate on multiplicative-width
three spatial intervals. -/
theorem integral_normSq_lemma14MellinSegment_le_universal
    (g : ℝ → ℂ) (hg : Continuous g)
    {P Q : ℝ} (hP : 0 < P) (hPQ : P ≤ Q) (hQ3P : Q ≤ 3 * P)
    {A B : ℝ} (hAB : A ≤ B) :
    (∫ x in P..Q, Complex.normSq (lemma14MellinSegment g A B x)) ≤
      Q ^ 3 *
        (lemma14UniversalFourierCauchyConstant * Real.pi *
          ∫ t in A..B, Complex.normSq (g t)) := by
  have hQ : 0 < Q := hP.trans_le hPQ
  have hlog : -Real.log Q ≤ -Real.log P :=
    neg_le_neg (Real.log_le_log hP hPQ)
  have htransform :=
    intervalIntegral_normSq_logSpatialTransform_le_universal
      g hg hP hPQ hQ3P hAB
  rw [integral_normSq_lemma14MellinSegment_eq_log g hg hP hPQ A B]
  have hweight (y : ℝ) (hy : y ∈ Set.Icc (-Real.log Q) (-Real.log P)) :
      Real.exp (-3 * y) ≤ Q ^ 3 := by
    have hmono : -3 * y ≤ 3 * Real.log Q := by linarith [hy.1]
    calc
      Real.exp (-3 * y) ≤ Real.exp (3 * Real.log Q) :=
        Real.exp_le_exp.mpr hmono
      _ = Q ^ 3 := by
        rw [show 3 * Real.log Q =
          Real.log Q + Real.log Q + Real.log Q by ring,
          Real.exp_add, Real.exp_add, Real.exp_log hQ]
        ring
  calc
    (∫ y in (-Real.log Q)..(-Real.log P),
        Real.exp (-3 * y) *
          Complex.normSq (lemma14LogSpatialTransform g A B y)) ≤
      ∫ y in (-Real.log Q)..(-Real.log P),
        Q ^ 3 * Complex.normSq (lemma14LogSpatialTransform g A B y) := by
      apply intervalIntegral.integral_mono_on hlog
      · exact ((Real.continuous_exp.comp (by fun_prop)).mul
          (Complex.continuous_normSq.comp
            (continuous_lemma14LogSpatialTransform g hg A B))).intervalIntegrable _ _
      · exact (continuous_const.mul
          (Complex.continuous_normSq.comp
            (continuous_lemma14LogSpatialTransform g hg A B))).intervalIntegrable _ _
      · intro y hy
        exact mul_le_mul_of_nonneg_right (hweight y hy)
          (Complex.normSq_nonneg _)
    _ = Q ^ 3 * (∫ y in (-Real.log Q)..(-Real.log P),
          Complex.normSq (lemma14LogSpatialTransform g A B y)) := by
      rw [intervalIntegral.integral_const_mul]
    _ ≤ Q ^ 3 *
        (lemma14UniversalFourierCauchyConstant * Real.pi *
          ∫ t in A..B, Complex.normSq (g t)) :=
      mul_le_mul_of_nonneg_left htransform (pow_nonneg hQ.le 3)

/-! ## Specialization to the source smoothing multiplier -/

/-- Continuous-endpoint form of the source's fixed-`u` smoothed Mellin
transform. -/
def lemma14RealSafeSmoothedMellinSegment
    (F : ℝ → ℂ) (u A B x : ℝ) : ℂ :=
  lemma14MellinSegment
    (fun t ↦ F t * safePerronRatioIncrement u t) A B x

theorem continuous_safePerronRatioIncrement_right (u : ℝ) :
    Continuous (safePerronRatioIncrement u) := by
  have hp : Continuous (fun t : ℝ ↦ (u, t)) :=
    continuous_const.prodMk continuous_id
  exact continuous_uncurry_safePerronRatioIncrement.comp hp

theorem continuous_lemma14RealSafeSmoothedMellinSegment_coefficient
    (F : ℝ → ℂ) (hF : Continuous F) (u : ℝ) :
    Continuous (fun t ↦ F t * safePerronRatioIncrement u t) :=
  hF.mul (continuous_safePerronRatioIncrement_right u)

/-- The continuous Schur estimate applied to the exact source multiplier.
This is the endpoint consumed by the moving-endpoint `u` average. -/
theorem integral_normSq_lemma14RealSafeSmoothedMellinSegment_le
    (F : ℝ → ℂ) (hF : Continuous F) (u : ℝ)
    {P Q : ℝ} (hP : 0 < P) (hPQ : P ≤ Q)
    (delta L R : ℝ) (hdelta : 0 < delta)
    (hleft : L + 2 * delta ≤ -Real.log Q)
    (hright : -Real.log P ≤ R - 2 * delta)
    {A B : ℝ} (hAB : A ≤ B) :
    (∫ x in P..Q,
        Complex.normSq
          (lemma14RealSafeSmoothedMellinSegment F u A B x)) ≤
      Q ^ 3 *
        (lemma14FourierCauchyConstant
            (lemma14PositiveLogCutoff delta L R hdelta) * Real.pi *
          ∫ t in A..B,
            Complex.normSq (F t * safePerronRatioIncrement u t)) := by
  exact integral_normSq_lemma14MellinSegment_le
    (fun t ↦ F t * safePerronRatioIncrement u t)
    (continuous_lemma14RealSafeSmoothedMellinSegment_coefficient F hF u)
    hP hPQ delta L R hdelta hleft hright hAB

theorem integral_normSq_lemma14RealSafeSmoothedMellinSegment_le_universal
    (F : ℝ → ℂ) (hF : Continuous F) (u : ℝ)
    {P Q : ℝ} (hP : 0 < P) (hPQ : P ≤ Q) (hQ3P : Q ≤ 3 * P)
    {A B : ℝ} (hAB : A ≤ B) :
    (∫ x in P..Q,
        Complex.normSq
          (lemma14RealSafeSmoothedMellinSegment F u A B x)) ≤
      Q ^ 3 *
        (lemma14UniversalFourierCauchyConstant * Real.pi *
          ∫ t in A..B,
            Complex.normSq (F t * safePerronRatioIncrement u t)) := by
  exact integral_normSq_lemma14MellinSegment_le_universal
    (fun t ↦ F t * safePerronRatioIncrement u t)
    (continuous_lemma14RealSafeSmoothedMellinSegment_coefficient F hF u)
    hP hPQ hQ3P hAB

/-- Low-frequency `u²` bound for the safe smoothing multiplier, including
the endpoint `u=0`. -/
theorem integral_normSq_mul_safePerronRatioIncrement_le_self
    (F : ℝ → ℂ) (hF : Continuous F) {u A B : ℝ}
    (hu : 0 ≤ u) (hAB : A ≤ B) :
    (∫ t in A..B,
        Complex.normSq (F t * safePerronRatioIncrement u t)) ≤
      u ^ 2 * ∫ t in A..B, Complex.normSq (F t) := by
  rcases hu.eq_or_lt with rfl | hu
  · simp [safePerronRatioIncrement, perronRatioIncrement]
  · simpa only [safePerronRatioIncrement_eq_of_nonneg hu.le] using
      integral_normSq_mul_perronRatioIncrement_le_self F hF hu hAB

/-- Reciprocal-frequency bound for the safe smoothing multiplier, including
the endpoint `u=0`. -/
theorem integral_normSq_mul_safePerronRatioIncrement_le_div
    (F : ℝ → ℂ) (hF : Continuous F) {u A B T : ℝ}
    (hu : 0 ≤ u) (hAB : A ≤ B) (hT : 0 < T)
    (haway : ∀ t ∈ Set.Icc A B, T ≤ |t|) :
    (∫ t in A..B,
        Complex.normSq (F t * safePerronRatioIncrement u t)) ≤
      ((2 + u) / T) ^ 2 * ∫ t in A..B, Complex.normSq (F t) := by
  rcases hu.eq_or_lt with rfl | hu
  · simp [safePerronRatioIncrement, perronRatioIncrement]
    exact mul_nonneg (sq_nonneg _) (intervalIntegral.integral_nonneg_of_forall
      hAB (fun t ↦ Complex.normSq_nonneg _))
  · simpa only [safePerronRatioIncrement_eq_of_nonneg hu.le] using
      integral_normSq_mul_perronRatioIncrement_le_div
        F hF hu hAB hT haway

/-- Pointwise reciprocal-frequency form of the source multiplier estimate.
Unlike the coarser lower-height bound above, this keeps the integrable
`1/|t|²` weight and is therefore uniform as the outer Perron height tends
to infinity. -/
theorem integral_normSq_mul_safePerronRatioIncrement_le_weighted
    (F : ℝ → ℂ) (hF : Continuous F) {u A B : ℝ}
    (hu : 0 ≤ u) (hAB : A ≤ B)
    (haway : ∀ t ∈ Set.Icc A B, t ≠ 0) :
    (∫ t in A..B,
        Complex.normSq (F t * safePerronRatioIncrement u t)) ≤
      ∫ t in A..B,
        ((2 + u) / |t|) ^ 2 * Complex.normSq (F t) := by
  have hleft : Continuous (fun t ↦
      Complex.normSq (F t * safePerronRatioIncrement u t)) := by
    exact Complex.continuous_normSq.comp
      (hF.mul (continuous_safePerronRatioIncrement_right u))
  have habsNe : ∀ t ∈ Set.Icc A B, |t| ≠ 0 := by
    intro t ht hzero
    exact haway t ht (abs_eq_zero.mp hzero)
  have hratio : ContinuousOn (fun t : ℝ ↦ (2 + u) / |t|)
      (Set.Icc A B) :=
    continuousOn_const.div continuous_abs.continuousOn habsNe
  have hrightIcc : ContinuousOn (fun t : ℝ ↦
      ((2 + u) / |t|) ^ 2 * Complex.normSq (F t)) (Set.Icc A B) :=
    hratio.pow 2 |>.mul
      (Complex.continuous_normSq.comp hF).continuousOn
  have hright : ContinuousOn (fun t : ℝ ↦
      ((2 + u) / |t|) ^ 2 * Complex.normSq (F t)) (Set.uIcc A B) := by
    rw [Set.uIcc_of_le hAB]
    exact hrightIcc
  have hleftInt : IntervalIntegrable (fun t ↦
      Complex.normSq (F t * safePerronRatioIncrement u t)) volume A B :=
    hleft.intervalIntegrable A B
  have hrightInt : IntervalIntegrable (fun t : ℝ ↦
      ((2 + u) / |t|) ^ 2 * Complex.normSq (F t)) volume A B :=
    hright.intervalIntegrable
  apply intervalIntegral.integral_mono_on hAB
    hleftInt hrightInt
  intro t ht
  have htne : t ≠ 0 := haway t ht
  have habs : 0 < |t| := abs_pos.mpr htne
  have hnum : 0 ≤ 2 + u := by linarith
  have hratioNonneg : 0 ≤ (2 + u) / |t| := div_nonneg hnum habs.le
  rcases hu.eq_or_lt with rfl | hu
  · simp [safePerronRatioIncrement, perronRatioIncrement]
    exact mul_nonneg (sq_nonneg _) (Complex.normSq_nonneg _)
  · rw [safePerronRatioIncrement_eq_of_nonneg hu.le,
      Complex.normSq_mul]
    have hnorm := norm_perronRatioIncrement_le_div_abs hu htne
    have hsquare : Complex.normSq (perronRatioIncrement u t) ≤
        ((2 + u) / |t|) ^ 2 := by
      rw [Complex.normSq_eq_norm_sq]
      exact sq_le_sq₀ (norm_nonneg _) hratioNonneg |>.2 hnorm
    nlinarith [Complex.normSq_nonneg (F t)]

/-- A globally continuous reciprocal-square cutoff.  On a band where
`T ≤ |t|` it is exactly `|t|⁻²`, while its denominator remains positive
at the origin. -/
def lemma14SafeReciprocalSqWeight (T t : ℝ) : ℝ :=
  (max |t| T)⁻¹ ^ 2

theorem continuous_lemma14SafeReciprocalSqWeight
    {T : ℝ} (hT : 0 < T) :
    Continuous (lemma14SafeReciprocalSqWeight T) := by
  unfold lemma14SafeReciprocalSqWeight
  apply Continuous.pow
  apply Continuous.inv₀
  · exact continuous_abs.max continuous_const
  · intro t hzero
    have hle : T ≤ max |t| T := le_max_right _ _
    linarith

/-- A one-bounded vertical polynomial has uniformly summable positive
reciprocal-square tail energy. -/
theorem intervalIntegral_safeReciprocalSqWeight_mul_normSq_le_inv
    (F : ℝ → ℂ) (hF : Continuous F) (hnorm : ∀ t, ‖F t‖ ≤ 1)
    {T U : ℝ} (hT : 0 < T) (hTU : T ≤ U) :
    (∫ t in T..U,
        lemma14SafeReciprocalSqWeight T t * Complex.normSq (F t)) ≤ T⁻¹ := by
  have hleft : Continuous (fun t ↦
      lemma14SafeReciprocalSqWeight T t * Complex.normSq (F t)) :=
    (continuous_lemma14SafeReciprocalSqWeight hT).mul
      (Complex.continuous_normSq.comp hF)
  have hright : ContinuousOn (fun t : ℝ ↦ t⁻¹ ^ 2) (Set.uIcc T U) := by
    rw [Set.uIcc_of_le hTU]
    apply ContinuousOn.pow
    apply ContinuousOn.inv₀ continuousOn_id
    intro t ht hzero
    simp only [id_eq] at hzero
    subst t
    linarith [ht.1]
  have hmono :
      (∫ t in T..U,
          lemma14SafeReciprocalSqWeight T t * Complex.normSq (F t)) ≤
        ∫ t in T..U, t⁻¹ ^ 2 := by
    apply intervalIntegral.integral_mono_on hTU
      (hleft.intervalIntegrable T U) hright.intervalIntegrable
    intro t ht
    have htpos : 0 < t := hT.trans_le ht.1
    have habs : |t| = t := abs_of_pos htpos
    have hmax : max |t| T = |t| := max_eq_left (by simpa [habs] using ht.1)
    have hsq : Complex.normSq (F t) ≤ 1 := by
      rw [Complex.normSq_eq_norm_sq]
      nlinarith [norm_nonneg (F t), hnorm t]
    unfold lemma14SafeReciprocalSqWeight
    rw [hmax, habs]
    simpa using mul_le_mul_of_nonneg_left hsq (sq_nonneg t⁻¹)
  have hz := integral_zpow (a := T) (b := U) (n := (-2 : ℤ)) (by
    right
    constructor
    · norm_num
    · rw [Set.uIcc_of_le hTU]
      intro hz
      linarith [hz.1])
  have heval : (∫ t in T..U, t⁻¹ ^ 2) = T⁻¹ - U⁻¹ := by
    calc
      _ = ∫ t in T..U, t ^ (-2 : ℤ) := by
        apply intervalIntegral.integral_congr
        intro t ht
        simp [zpow_neg]
      _ = _ := by
        rw [hz]
        norm_num [zpow_neg]
        ring
  calc
    _ ≤ ∫ t in T..U, t⁻¹ ^ 2 := hmono
    _ = T⁻¹ - U⁻¹ := heval
    _ ≤ T⁻¹ := sub_le_self _ (inv_nonneg.mpr (hT.trans_le hTU).le)

/-- The analogous one-bounded negative reciprocal-square tail estimate. -/
theorem intervalIntegral_safeReciprocalSqWeight_mul_normSq_neg_le_inv
    (F : ℝ → ℂ) (hF : Continuous F) (hnorm : ∀ t, ‖F t‖ ≤ 1)
    {T U : ℝ} (hT : 0 < T) (hTU : T ≤ U) :
    (∫ t in -U..-T,
        lemma14SafeReciprocalSqWeight T t * Complex.normSq (F t)) ≤ T⁻¹ := by
  have horder : -U ≤ -T := neg_le_neg hTU
  have hleft : Continuous (fun t ↦
      lemma14SafeReciprocalSqWeight T t * Complex.normSq (F t)) :=
    (continuous_lemma14SafeReciprocalSqWeight hT).mul
      (Complex.continuous_normSq.comp hF)
  have hright : ContinuousOn (fun t : ℝ ↦ t⁻¹ ^ 2) (Set.uIcc (-U) (-T)) := by
    rw [Set.uIcc_of_le horder]
    apply ContinuousOn.pow
    apply ContinuousOn.inv₀ continuousOn_id
    intro t ht hzero
    simp only [id_eq] at hzero
    subst t
    linarith [ht.2]
  have hmono :
      (∫ t in -U..-T,
          lemma14SafeReciprocalSqWeight T t * Complex.normSq (F t)) ≤
        ∫ t in -U..-T, t⁻¹ ^ 2 := by
    apply intervalIntegral.integral_mono_on horder
      (hleft.intervalIntegrable (-U) (-T)) hright.intervalIntegrable
    intro t ht
    have htneg : t < 0 := lt_of_le_of_lt ht.2 (neg_lt_zero.mpr hT)
    have habs : |t| = -t := abs_of_neg htneg
    have hTabs : T ≤ |t| := by rw [habs]; linarith [ht.2]
    have hmax : max |t| T = |t| := max_eq_left hTabs
    have hsq : Complex.normSq (F t) ≤ 1 := by
      rw [Complex.normSq_eq_norm_sq]
      nlinarith [norm_nonneg (F t), hnorm t]
    have hweight : lemma14SafeReciprocalSqWeight T t = t⁻¹ ^ 2 := by
      unfold lemma14SafeReciprocalSqWeight
      rw [hmax, habs]
      field_simp [htneg.ne]
    rw [hweight]
    simpa using mul_le_mul_of_nonneg_left hsq (sq_nonneg t⁻¹)
  have hz := integral_zpow (a := -U) (b := -T) (n := (-2 : ℤ)) (by
    right
    constructor
    · norm_num
    · rw [Set.uIcc_of_le horder]
      intro hz
      linarith [hz.2])
  have heval : (∫ t in -U..-T, t⁻¹ ^ 2) = T⁻¹ - U⁻¹ := by
    calc
      _ = ∫ t in -U..-T, t ^ (-2 : ℤ) := by
        apply intervalIntegral.integral_congr
        intro t ht
        simp [zpow_neg]
      _ = _ := by
        rw [hz]
        norm_num [zpow_neg]
        ring
  calc
    _ ≤ ∫ t in -U..-T, t⁻¹ ^ 2 := hmono
    _ = T⁻¹ - U⁻¹ := heval
    _ ≤ T⁻¹ := sub_le_self _ (inv_nonneg.mpr (hT.trans_le hTU).le)

/-- On a positive dyadic shell the safe reciprocal-square energy is the
ordinary vertical energy times at most `V⁻²`. -/
theorem intervalIntegral_safeReciprocalSqWeight_mul_normSq_posShell_le
    (F : ℝ → ℂ) (hF : Continuous F)
    {T V : ℝ} (hT : 0 < T) (hV : 0 < V) (hTV : T ≤ V) :
    (∫ t in V..2 * V,
        lemma14SafeReciprocalSqWeight T t * Complex.normSq (F t)) ≤
      V⁻¹ ^ 2 * ∫ t in V..2 * V, Complex.normSq (F t) := by
  have hV2 : V ≤ 2 * V := by linarith
  have hleft : Continuous (fun t ↦
      lemma14SafeReciprocalSqWeight T t * Complex.normSq (F t)) :=
    (continuous_lemma14SafeReciprocalSqWeight hT).mul
      (Complex.continuous_normSq.comp hF)
  have hright : Continuous (fun t ↦
      V⁻¹ ^ 2 * Complex.normSq (F t)) := by fun_prop
  calc
    (∫ t in V..2 * V,
        lemma14SafeReciprocalSqWeight T t * Complex.normSq (F t)) ≤
      ∫ t in V..2 * V,
        V⁻¹ ^ 2 * Complex.normSq (F t) := by
      apply intervalIntegral.integral_mono_on hV2
        (hleft.intervalIntegrable _ _) (hright.intervalIntegrable _ _)
      intro t ht
      have htpos : 0 < t := hV.trans_le ht.1
      have habs : |t| = t := abs_of_pos htpos
      have hmax : max |t| T = |t| := max_eq_left (by
        rw [habs]
        exact hTV.trans ht.1)
      have hinv : t⁻¹ ≤ V⁻¹ := inv_anti₀ hV ht.1
      have hsq : t⁻¹ ^ 2 ≤ V⁻¹ ^ 2 :=
        (sq_le_sq₀ (inv_nonneg.mpr htpos.le) (inv_nonneg.mpr hV.le)).2 hinv
      unfold lemma14SafeReciprocalSqWeight
      rw [hmax, habs]
      exact mul_le_mul_of_nonneg_right hsq (Complex.normSq_nonneg _)
    _ = V⁻¹ ^ 2 * ∫ t in V..2 * V, Complex.normSq (F t) := by
      rw [intervalIntegral.integral_const_mul]

/-- Negative-shell counterpart of the reciprocal-square comparison. -/
theorem intervalIntegral_safeReciprocalSqWeight_mul_normSq_negShell_le
    (F : ℝ → ℂ) (hF : Continuous F)
    {T V : ℝ} (hT : 0 < T) (hV : 0 < V) (hTV : T ≤ V) :
    (∫ t in -2 * V..-V,
        lemma14SafeReciprocalSqWeight T t * Complex.normSq (F t)) ≤
      V⁻¹ ^ 2 * ∫ t in -2 * V..-V, Complex.normSq (F t) := by
  have horder : -2 * V ≤ -V := by linarith
  have hleft : Continuous (fun t ↦
      lemma14SafeReciprocalSqWeight T t * Complex.normSq (F t)) :=
    (continuous_lemma14SafeReciprocalSqWeight hT).mul
      (Complex.continuous_normSq.comp hF)
  have hright : Continuous (fun t ↦
      V⁻¹ ^ 2 * Complex.normSq (F t)) := by fun_prop
  calc
    (∫ t in -2 * V..-V,
        lemma14SafeReciprocalSqWeight T t * Complex.normSq (F t)) ≤
      ∫ t in -2 * V..-V,
        V⁻¹ ^ 2 * Complex.normSq (F t) := by
      apply intervalIntegral.integral_mono_on horder
        (hleft.intervalIntegrable _ _) (hright.intervalIntegrable _ _)
      intro t ht
      have htneg : t < 0 := lt_of_le_of_lt ht.2 (neg_lt_zero.mpr hV)
      have habs : |t| = -t := abs_of_neg htneg
      have hVabs : V ≤ |t| := by rw [habs]; linarith [ht.2]
      have hmax : max |t| T = |t| := max_eq_left (hTV.trans hVabs)
      have hinv : |t|⁻¹ ≤ V⁻¹ := inv_anti₀ hV hVabs
      have hsq : |t|⁻¹ ^ 2 ≤ V⁻¹ ^ 2 :=
        (sq_le_sq₀ (inv_nonneg.mpr (abs_nonneg t))
          (inv_nonneg.mpr hV.le)).2 hinv
      unfold lemma14SafeReciprocalSqWeight
      rw [hmax]
      exact mul_le_mul_of_nonneg_right hsq (Complex.normSq_nonneg _)
    _ = V⁻¹ ^ 2 * ∫ t in -2 * V..-V, Complex.normSq (F t) := by
      rw [intervalIntegral.integral_const_mul]

/-- Outer-height-uniform multiplier estimate.  The full dependence on the
vertical variable is retained in the safe reciprocal-square energy. -/
theorem integral_normSq_mul_safePerronRatioIncrement_le_safeWeighted
    (F : ℝ → ℂ) (hF : Continuous F) {u A B T : ℝ}
    (hu : 0 ≤ u) (hAB : A ≤ B) (hT : 0 < T)
    (haway : ∀ t ∈ Set.Icc A B, T ≤ |t|) :
    (∫ t in A..B,
        Complex.normSq (F t * safePerronRatioIncrement u t)) ≤
      (2 + u) ^ 2 * ∫ t in A..B,
        lemma14SafeReciprocalSqWeight T t * Complex.normSq (F t) := by
  have hne : ∀ t ∈ Set.Icc A B, t ≠ 0 := by
    intro t ht hzero
    subst t
    simpa using (hT.trans_le (haway 0 ht))
  have hbase :=
    integral_normSq_mul_safePerronRatioIncrement_le_weighted
      F hF hu hAB hne
  calc
    (∫ t in A..B,
        Complex.normSq (F t * safePerronRatioIncrement u t)) ≤
      ∫ t in A..B,
        ((2 + u) / |t|) ^ 2 * Complex.normSq (F t) := hbase
    _ = (2 + u) ^ 2 * ∫ t in A..B,
        lemma14SafeReciprocalSqWeight T t * Complex.normSq (F t) := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro t ht
      rw [Set.uIcc_of_le hAB] at ht
      have htne := hne t ht
      have hmax : max |t| T = |t| := max_eq_left (haway t ht)
      change ((2 + u) / |t|) ^ 2 * Complex.normSq (F t) =
        (2 + u) ^ 2 *
          (lemma14SafeReciprocalSqWeight T t * Complex.normSq (F t))
      unfold lemma14SafeReciprocalSqWeight
      rw [hmax]
      field_simp [abs_ne_zero.mpr htne]

/-! ## A globally continuous spatial extension for Fubini -/

/-- Clamp the real Mellin base away from zero.  On `[P,∞)` it is exactly
the original base, while globally it permits joint-continuity arguments. -/
def lemma14PositiveClamp (P x : ℝ) : ℝ := max x (P / 2)

theorem lemma14PositiveClamp_pos {P : ℝ} (hP : 0 < P) (x : ℝ) :
    0 < lemma14PositiveClamp P x := by
  unfold lemma14PositiveClamp
  exact (by positivity : 0 < P / 2) |>.trans_le (le_max_right _ _)

theorem lemma14PositiveClamp_eq {P x : ℝ} (hP : 0 < P) (hPx : P ≤ x) :
    lemma14PositiveClamp P x = x := by
  unfold lemma14PositiveClamp
  rw [max_eq_left]
  linarith

/-- Globally continuous extension of the real fixed-`u` smoothed Mellin
segment. -/
def lemma14ClampedSafeSmoothedMellinSegment
    (P : ℝ) (F : ℝ → ℂ) (u A B x : ℝ) : ℂ :=
  ∫ t in A..B, F t *
      (lemma14PositiveClamp P x : ℂ) ^
        ((1 : ℂ) + (t : ℂ) * Complex.I) *
      safePerronRatioIncrement u t

theorem lemma14ClampedSafeSmoothedMellinSegment_eq
    (P : ℝ) (hP : 0 < P) (F : ℝ → ℂ) (u A B : ℝ)
    {x : ℝ} (hPx : P ≤ x) :
    lemma14ClampedSafeSmoothedMellinSegment P F u A B x =
      lemma14RealSafeSmoothedMellinSegment F u A B x := by
  unfold lemma14ClampedSafeSmoothedMellinSegment
    lemma14RealSafeSmoothedMellinSegment lemma14MellinSegment
  rw [lemma14PositiveClamp_eq hP hPx]
  apply intervalIntegral.integral_congr
  intro t ht
  ring

/-- Joint continuity in the spatial endpoint and smoothing parameter. -/
theorem continuous_uncurry_lemma14ClampedSafeSmoothedMellinSegment
    {P : ℝ} (hP : 0 < P) (F : ℝ → ℂ) (hF : Continuous F)
    (A B : ℝ) :
    Continuous (Function.uncurry
      (fun x u ↦ lemma14ClampedSafeSmoothedMellinSegment P F u A B x)) := by
  unfold lemma14ClampedSafeSmoothedMellinSegment Function.uncurry
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
  have hbase : Continuous (fun p : (ℝ × ℝ) × ℝ ↦
      (lemma14PositiveClamp P p.1.1 : ℂ)) := by
    unfold lemma14PositiveClamp
    fun_prop
  have hexp : Continuous (fun p : (ℝ × ℝ) × ℝ ↦
      (1 : ℂ) + (p.2 : ℂ) * Complex.I) := by fun_prop
  have hpow : Continuous (fun p : (ℝ × ℝ) × ℝ ↦
      (lemma14PositiveClamp P p.1.1 : ℂ) ^
        ((1 : ℂ) + (p.2 : ℂ) * Complex.I)) := by
    apply hbase.cpow hexp
    intro p
    rw [Complex.ofReal_mem_slitPlane]
    exact lemma14PositiveClamp_pos hP _
  have hratio : Continuous (fun p : (ℝ × ℝ) × ℝ ↦
      safePerronRatioIncrement p.1.2 p.2) :=
    continuous_uncurry_safePerronRatioIncrement.comp
      ((continuous_snd.comp continuous_fst).prodMk continuous_snd)
  exact ((hF.comp continuous_snd).mul hpow).mul hratio

theorem continuous_uncurry_normSq_lemma14ClampedSafeSmoothedMellinSegment
    {P : ℝ} (hP : 0 < P) (F : ℝ → ℂ) (hF : Continuous F)
    (A B : ℝ) :
    Continuous (Function.uncurry (fun x u ↦
      Complex.normSq
        (lemma14ClampedSafeSmoothedMellinSegment P F u A B x))) := by
  exact Complex.continuous_normSq.comp
    (continuous_uncurry_lemma14ClampedSafeSmoothedMellinSegment
      hP F hF A B)

/-- Fubini on a spatial/smoothing rectangle for the genuine (unclamped)
source transform.  The clamp is used only inside the proof to provide a
globally continuous extension. -/
theorem intervalIntegral_intervalIntegral_normSq_realSafeSmoothed_eq_swap
    (F : ℝ → ℂ) (hF : Continuous F)
    {P Q C D : ℝ} (hP : 0 < P) (hPQ : P ≤ Q) (hCD : C ≤ D)
    (A B : ℝ) :
    (∫ x in P..Q, ∫ u in C..D,
        Complex.normSq
          (lemma14RealSafeSmoothedMellinSegment F u A B x)) =
      ∫ u in C..D, ∫ x in P..Q,
        Complex.normSq
          (lemma14RealSafeSmoothedMellinSegment F u A B x) := by
  let q : ℝ → ℝ → ℝ := fun x u ↦
    Complex.normSq
      (lemma14ClampedSafeSmoothedMellinSegment P F u A B x)
  have hq : Continuous (Function.uncurry q) :=
    continuous_uncurry_normSq_lemma14ClampedSafeSmoothedMellinSegment
      hP F hF A B
  have hrect : IntegrableOn (Function.uncurry q)
      (Set.uIoc P Q ×ˢ Set.uIoc C D) :=
    (hq.continuousOn.integrableOn_compact
      (isCompact_uIcc.prod isCompact_uIcc)).mono_set
        (Set.prod_mono Set.uIoc_subset_uIcc Set.uIoc_subset_uIcc)
  have hswap :
      (∫ x in P..Q, ∫ u in C..D, q x u) =
        ∫ u in C..D, ∫ x in P..Q, q x u :=
    MeasureTheory.intervalIntegral_intervalIntegral_swap hrect
  have heq (x : ℝ) (hx : x ∈ Set.uIcc P Q) (u : ℝ) :
      q x u = Complex.normSq
        (lemma14RealSafeSmoothedMellinSegment F u A B x) := by
    rw [Set.uIcc_of_le hPQ] at hx
    dsimp only [q]
    rw [lemma14ClampedSafeSmoothedMellinSegment_eq P hP F u A B hx.1]
  calc
    (∫ x in P..Q, ∫ u in C..D,
        Complex.normSq
          (lemma14RealSafeSmoothedMellinSegment F u A B x)) =
      ∫ x in P..Q, ∫ u in C..D, q x u := by
        apply intervalIntegral.integral_congr
        intro x hx
        apply intervalIntegral.integral_congr
        intro u hu
        exact (heq x hx u).symm
    _ = ∫ u in C..D, ∫ x in P..Q, q x u := hswap
    _ = ∫ u in C..D, ∫ x in P..Q,
        Complex.normSq
          (lemma14RealSafeSmoothedMellinSegment F u A B x) := by
        apply intervalIntegral.integral_congr
        intro u hu
        apply intervalIntegral.integral_congr
        intro x hx
        exact heq x hx u

/-- Rectangle-integrated source smoothing estimate.  The right side has
the exact multiplier energy and a constant independent of both vertical
band length and the smoothing parameter. -/
theorem intervalIntegral_intervalIntegral_normSq_realSafeSmoothed_le
    (F : ℝ → ℂ) (hF : Continuous F)
    {P Q C D : ℝ} (hP : 0 < P) (hPQ : P ≤ Q) (hCD : C ≤ D)
    (delta L R : ℝ) (hdelta : 0 < delta)
    (hleft : L + 2 * delta ≤ -Real.log Q)
    (hright : -Real.log P ≤ R - 2 * delta)
    {A B : ℝ} (hAB : A ≤ B) :
    (∫ x in P..Q, ∫ u in C..D,
        Complex.normSq
          (lemma14RealSafeSmoothedMellinSegment F u A B x)) ≤
      Q ^ 3 *
        (lemma14FourierCauchyConstant
            (lemma14PositiveLogCutoff delta L R hdelta) * Real.pi) *
        ∫ u in C..D, ∫ t in A..B,
          Complex.normSq (F t * safePerronRatioIncrement u t) := by
  let K : ℝ := Q ^ 3 *
    (lemma14FourierCauchyConstant
      (lemma14PositiveLogCutoff delta L R hdelta) * Real.pi)
  have hK : 0 ≤ K := by
    dsimp only [K]
    have hQ : 0 < Q := hP.trans_le hPQ
    exact mul_nonneg (pow_nonneg hQ.le 3)
      (mul_nonneg
        (lemma14FourierCauchyConstant_nonneg
          (lemma14PositiveLogCutoff delta L R hdelta)) Real.pi_pos.le)
  have hinnerCont : Continuous (fun u ↦ ∫ x in P..Q,
      Complex.normSq
        (lemma14ClampedSafeSmoothedMellinSegment P F u A B x)) := by
    apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    have hjoint : Continuous (Function.uncurry (fun x u ↦
        Complex.normSq
          (lemma14ClampedSafeSmoothedMellinSegment P F u A B x))) :=
      continuous_uncurry_normSq_lemma14ClampedSafeSmoothedMellinSegment
        hP F hF A B
    let G : ℝ × ℝ → ℝ := fun p ↦ Complex.normSq
      (lemma14ClampedSafeSmoothedMellinSegment P F p.1 A B p.2)
    have hGeq : G =
        Function.uncurry (fun x u ↦ Complex.normSq
          (lemma14ClampedSafeSmoothedMellinSegment P F u A B x)) ∘
          Prod.swap := by
      funext p
      rfl
    rw [show Function.uncurry (fun u x ↦ Complex.normSq
        (lemma14ClampedSafeSmoothedMellinSegment P F u A B x)) = G by rfl,
      hGeq]
    exact hjoint.comp continuous_swap
  have henergyCont : Continuous (fun u ↦ ∫ t in A..B,
      Complex.normSq (F t * safePerronRatioIncrement u t)) := by
    apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    exact Complex.continuous_normSq.comp
      ((hF.comp continuous_snd).mul
        continuous_uncurry_safePerronRatioIncrement)
  have hpoint (u : ℝ) (hu : u ∈ Set.Icc C D) :
      (∫ x in P..Q,
          Complex.normSq
            (lemma14RealSafeSmoothedMellinSegment F u A B x)) ≤
        K * ∫ t in A..B,
          Complex.normSq (F t * safePerronRatioIncrement u t) := by
    simpa only [K, mul_assoc] using
      integral_normSq_lemma14RealSafeSmoothedMellinSegment_le
        F hF u hP hPQ delta L R hdelta hleft hright hAB
  rw [intervalIntegral_intervalIntegral_normSq_realSafeSmoothed_eq_swap
    F hF hP hPQ hCD A B]
  calc
    (∫ u in C..D, ∫ x in P..Q,
        Complex.normSq
          (lemma14RealSafeSmoothedMellinSegment F u A B x)) ≤
      ∫ u in C..D, K * ∫ t in A..B,
        Complex.normSq (F t * safePerronRatioIncrement u t) := by
        apply intervalIntegral.integral_mono_on hCD
        · have heq : (fun u ↦ ∫ x in P..Q,
              Complex.normSq
                (lemma14RealSafeSmoothedMellinSegment F u A B x)) =
            fun u ↦ ∫ x in P..Q,
              Complex.normSq
                (lemma14ClampedSafeSmoothedMellinSegment P F u A B x) := by
              funext u
              apply intervalIntegral.integral_congr
              intro x hx
              rw [Set.uIcc_of_le hPQ] at hx
              exact congrArg Complex.normSq
                (lemma14ClampedSafeSmoothedMellinSegment_eq
                  P hP F u A B hx.1).symm
          rw [heq]
          exact hinnerCont.intervalIntegrable C D
        · exact (henergyCont.const_mul K).intervalIntegrable C D
        · exact hpoint
    _ = K * ∫ u in C..D, ∫ t in A..B,
        Complex.normSq (F t * safePerronRatioIncrement u t) := by
      rw [intervalIntegral.integral_const_mul]
    _ = _ := by rfl

theorem intervalIntegral_intervalIntegral_normSq_realSafeSmoothed_le_universal
    (F : ℝ → ℂ) (hF : Continuous F)
    {P Q C D : ℝ} (hP : 0 < P) (hPQ : P ≤ Q) (hQ3P : Q ≤ 3 * P)
    (hCD : C ≤ D) {A B : ℝ} (hAB : A ≤ B) :
    (∫ x in P..Q, ∫ u in C..D,
        Complex.normSq
          (lemma14RealSafeSmoothedMellinSegment F u A B x)) ≤
      Q ^ 3 * (lemma14UniversalFourierCauchyConstant * Real.pi) *
        ∫ u in C..D, ∫ t in A..B,
          Complex.normSq (F t * safePerronRatioIncrement u t) := by
  let K : ℝ := Q ^ 3 *
    (lemma14UniversalFourierCauchyConstant * Real.pi)
  have hinnerCont : Continuous (fun u ↦ ∫ x in P..Q,
      Complex.normSq
        (lemma14ClampedSafeSmoothedMellinSegment P F u A B x)) := by
    apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    have hjoint : Continuous (Function.uncurry (fun x u ↦
        Complex.normSq
          (lemma14ClampedSafeSmoothedMellinSegment P F u A B x))) :=
      continuous_uncurry_normSq_lemma14ClampedSafeSmoothedMellinSegment
        hP F hF A B
    let G : ℝ × ℝ → ℝ := fun p ↦ Complex.normSq
      (lemma14ClampedSafeSmoothedMellinSegment P F p.1 A B p.2)
    have hGeq : G =
        Function.uncurry (fun x u ↦ Complex.normSq
          (lemma14ClampedSafeSmoothedMellinSegment P F u A B x)) ∘
          Prod.swap := by
      funext p
      rfl
    rw [show Function.uncurry (fun u x ↦ Complex.normSq
        (lemma14ClampedSafeSmoothedMellinSegment P F u A B x)) = G by rfl,
      hGeq]
    exact hjoint.comp continuous_swap
  have henergyCont : Continuous (fun u ↦ ∫ t in A..B,
      Complex.normSq (F t * safePerronRatioIncrement u t)) := by
    apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    exact Complex.continuous_normSq.comp
      ((hF.comp continuous_snd).mul
        continuous_uncurry_safePerronRatioIncrement)
  have hpoint (u : ℝ) (hu : u ∈ Set.Icc C D) :
      (∫ x in P..Q,
          Complex.normSq
            (lemma14RealSafeSmoothedMellinSegment F u A B x)) ≤
        K * ∫ t in A..B,
          Complex.normSq (F t * safePerronRatioIncrement u t) := by
    simpa only [K, mul_assoc] using
      integral_normSq_lemma14RealSafeSmoothedMellinSegment_le_universal
        F hF u hP hPQ hQ3P hAB
  rw [intervalIntegral_intervalIntegral_normSq_realSafeSmoothed_eq_swap
    F hF hP hPQ hCD A B]
  calc
    (∫ u in C..D, ∫ x in P..Q,
        Complex.normSq
          (lemma14RealSafeSmoothedMellinSegment F u A B x)) ≤
      ∫ u in C..D, K * ∫ t in A..B,
        Complex.normSq (F t * safePerronRatioIncrement u t) := by
      apply intervalIntegral.integral_mono_on hCD
      · have heq : (fun u ↦ ∫ x in P..Q,
            Complex.normSq
              (lemma14RealSafeSmoothedMellinSegment F u A B x)) =
          fun u ↦ ∫ x in P..Q,
            Complex.normSq
              (lemma14ClampedSafeSmoothedMellinSegment P F u A B x) := by
            funext u
            apply intervalIntegral.integral_congr
            intro x hx
            rw [Set.uIcc_of_le hPQ] at hx
            exact congrArg Complex.normSq
              (lemma14ClampedSafeSmoothedMellinSegment_eq
                P hP F u A B hx.1).symm
        rw [heq]
        exact hinnerCont.intervalIntegrable C D
      · exact (henergyCont.const_mul K).intervalIntegrable C D
      · exact hpoint
    _ = K * ∫ u in C..D, ∫ t in A..B,
        Complex.normSq (F t * safePerronRatioIncrement u t) := by
      rw [intervalIntegral.integral_const_mul]
    _ = _ := by rfl

theorem continuous_safePerronMultiplierEnergy
    (F : ℝ → ℂ) (hF : Continuous F) (A B : ℝ) :
    Continuous (fun u ↦ ∫ t in A..B,
      Complex.normSq (F t * safePerronRatioIncrement u t)) := by
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
  exact Complex.continuous_normSq.comp
    ((hF.comp continuous_snd).mul
      continuous_uncurry_safePerronRatioIncrement)

/-- Low-frequency rectangle form: the source smoothing multiplier contributes
exactly the integral of `u²`. -/
theorem intervalIntegral_intervalIntegral_normSq_realSafeSmoothed_le_low
    (F : ℝ → ℂ) (hF : Continuous F)
    {P Q C D : ℝ} (hP : 0 < P) (hPQ : P ≤ Q)
    (hC : 0 ≤ C) (hCD : C ≤ D)
    (delta L R : ℝ) (hdelta : 0 < delta)
    (hleft : L + 2 * delta ≤ -Real.log Q)
    (hright : -Real.log P ≤ R - 2 * delta)
    {A B : ℝ} (hAB : A ≤ B) :
    (∫ x in P..Q, ∫ u in C..D,
        Complex.normSq
          (lemma14RealSafeSmoothedMellinSegment F u A B x)) ≤
      Q ^ 3 *
        (lemma14FourierCauchyConstant
            (lemma14PositiveLogCutoff delta L R hdelta) * Real.pi) *
        (∫ u in C..D, u ^ 2) *
        ∫ t in A..B, Complex.normSq (F t) := by
  let K : ℝ := Q ^ 3 *
    (lemma14FourierCauchyConstant
      (lemma14PositiveLogCutoff delta L R hdelta) * Real.pi)
  let E : ℝ := ∫ t in A..B, Complex.normSq (F t)
  have hK : 0 ≤ K := by
    dsimp only [K]
    exact mul_nonneg (pow_nonneg (hP.trans_le hPQ).le 3)
      (mul_nonneg
        (lemma14FourierCauchyConstant_nonneg
          (lemma14PositiveLogCutoff delta L R hdelta)) Real.pi_pos.le)
  have hmono :
      (∫ u in C..D, ∫ t in A..B,
          Complex.normSq (F t * safePerronRatioIncrement u t)) ≤
        ∫ u in C..D, u ^ 2 * E := by
    apply intervalIntegral.integral_mono_on hCD
    · exact (continuous_safePerronMultiplierEnergy F hF A B).intervalIntegrable _ _
    · exact (by fun_prop : Continuous (fun u : ℝ ↦ u ^ 2 * E)).intervalIntegrable _ _
    · intro u hu
      exact integral_normSq_mul_safePerronRatioIncrement_le_self
        F hF (hC.trans hu.1) hAB
  have hbase := intervalIntegral_intervalIntegral_normSq_realSafeSmoothed_le
    F hF hP hPQ hCD delta L R hdelta hleft hright hAB
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

/-- High-frequency rectangle form: away from zero the source multiplier
contributes the reciprocal-frequency factor `((2+u)/T)²`. -/
theorem intervalIntegral_intervalIntegral_normSq_realSafeSmoothed_le_high
    (F : ℝ → ℂ) (hF : Continuous F)
    {P Q C D : ℝ} (hP : 0 < P) (hPQ : P ≤ Q)
    (hC : 0 ≤ C) (hCD : C ≤ D)
    (delta L R : ℝ) (hdelta : 0 < delta)
    (hleft : L + 2 * delta ≤ -Real.log Q)
    (hright : -Real.log P ≤ R - 2 * delta)
    {A B T : ℝ} (hAB : A ≤ B) (hT : 0 < T)
    (haway : ∀ t ∈ Set.Icc A B, T ≤ |t|) :
    (∫ x in P..Q, ∫ u in C..D,
        Complex.normSq
          (lemma14RealSafeSmoothedMellinSegment F u A B x)) ≤
      Q ^ 3 *
        (lemma14FourierCauchyConstant
            (lemma14PositiveLogCutoff delta L R hdelta) * Real.pi) *
        (∫ u in C..D, ((2 + u) / T) ^ 2) *
        ∫ t in A..B, Complex.normSq (F t) := by
  let K : ℝ := Q ^ 3 *
    (lemma14FourierCauchyConstant
      (lemma14PositiveLogCutoff delta L R hdelta) * Real.pi)
  let E : ℝ := ∫ t in A..B, Complex.normSq (F t)
  have hK : 0 ≤ K := by
    dsimp only [K]
    exact mul_nonneg (pow_nonneg (hP.trans_le hPQ).le 3)
      (mul_nonneg
        (lemma14FourierCauchyConstant_nonneg
          (lemma14PositiveLogCutoff delta L R hdelta)) Real.pi_pos.le)
  have hmono :
      (∫ u in C..D, ∫ t in A..B,
          Complex.normSq (F t * safePerronRatioIncrement u t)) ≤
        ∫ u in C..D, ((2 + u) / T) ^ 2 * E := by
    apply intervalIntegral.integral_mono_on hCD
    · exact (continuous_safePerronMultiplierEnergy F hF A B).intervalIntegrable _ _
    · exact (by fun_prop : Continuous
        (fun u : ℝ ↦ ((2 + u) / T) ^ 2 * E)).intervalIntegrable _ _
    · intro u hu
      exact integral_normSq_mul_safePerronRatioIncrement_le_div
        F hF (hC.trans hu.1) hAB hT haway
  have hbase := intervalIntegral_intervalIntegral_normSq_realSafeSmoothed_le
    F hF hP hPQ hCD delta L R hdelta hleft hright hAB
  calc
    (∫ x in P..Q, ∫ u in C..D,
        Complex.normSq
          (lemma14RealSafeSmoothedMellinSegment F u A B x)) ≤
      K * ∫ u in C..D, ∫ t in A..B,
        Complex.normSq (F t * safePerronRatioIncrement u t) := by
          simpa only [K, mul_assoc] using hbase
    _ ≤ K * ∫ u in C..D, ((2 + u) / T) ^ 2 * E :=
      mul_le_mul_of_nonneg_left hmono hK
    _ = K * (∫ u in C..D, ((2 + u) / T) ^ 2) * E := by
      rw [intervalIntegral.integral_mul_const]
      ring
    _ = _ := by rfl

/-- Reciprocal-square weighted rectangle estimate.  Its constant is
independent of the outer vertical endpoints `A,B`; all tail dependence is
inside the integrable weight `lemma14SafeReciprocalSqWeight T`. -/
theorem intervalIntegral_intervalIntegral_normSq_realSafeSmoothed_le_safeWeighted
    (F : ℝ → ℂ) (hF : Continuous F)
    {P Q C D : ℝ} (hP : 0 < P) (hPQ : P ≤ Q)
    (hC : 0 ≤ C) (hCD : C ≤ D)
    (delta L R : ℝ) (hdelta : 0 < delta)
    (hleft : L + 2 * delta ≤ -Real.log Q)
    (hright : -Real.log P ≤ R - 2 * delta)
    {A B T : ℝ} (hAB : A ≤ B) (hT : 0 < T)
    (haway : ∀ t ∈ Set.Icc A B, T ≤ |t|) :
    (∫ x in P..Q, ∫ u in C..D,
        Complex.normSq
          (lemma14RealSafeSmoothedMellinSegment F u A B x)) ≤
      Q ^ 3 *
        (lemma14FourierCauchyConstant
            (lemma14PositiveLogCutoff delta L R hdelta) * Real.pi) *
        (∫ u in C..D, (2 + u) ^ 2) *
        ∫ t in A..B,
          lemma14SafeReciprocalSqWeight T t * Complex.normSq (F t) := by
  let K : ℝ := Q ^ 3 *
    (lemma14FourierCauchyConstant
      (lemma14PositiveLogCutoff delta L R hdelta) * Real.pi)
  let E : ℝ := ∫ t in A..B,
    lemma14SafeReciprocalSqWeight T t * Complex.normSq (F t)
  have hK : 0 ≤ K := by
    dsimp only [K]
    exact mul_nonneg (pow_nonneg (hP.trans_le hPQ).le 3)
      (mul_nonneg
        (lemma14FourierCauchyConstant_nonneg
          (lemma14PositiveLogCutoff delta L R hdelta)) Real.pi_pos.le)
  have hmono :
      (∫ u in C..D, ∫ t in A..B,
          Complex.normSq (F t * safePerronRatioIncrement u t)) ≤
        ∫ u in C..D, (2 + u) ^ 2 * E := by
    apply intervalIntegral.integral_mono_on hCD
    · exact (continuous_safePerronMultiplierEnergy F hF A B).intervalIntegrable _ _
    · exact (by fun_prop : Continuous
        (fun u : ℝ ↦ (2 + u) ^ 2 * E)).intervalIntegrable _ _
    · intro u hu
      exact integral_normSq_mul_safePerronRatioIncrement_le_safeWeighted
        F hF (hC.trans hu.1) hAB hT haway
  have hbase := intervalIntegral_intervalIntegral_normSq_realSafeSmoothed_le
    F hF hP hPQ hCD delta L R hdelta hleft hright hAB
  calc
    (∫ x in P..Q, ∫ u in C..D,
        Complex.normSq
          (lemma14RealSafeSmoothedMellinSegment F u A B x)) ≤
      K * ∫ u in C..D, ∫ t in A..B,
        Complex.normSq (F t * safePerronRatioIncrement u t) := by
          simpa only [K, mul_assoc] using hbase
    _ ≤ K * ∫ u in C..D, (2 + u) ^ 2 * E :=
      mul_le_mul_of_nonneg_left hmono hK
    _ = K * (∫ u in C..D, (2 + u) ^ 2) * E := by
      rw [intervalIntegral.integral_mul_const]
      ring
    _ = _ := by rfl

theorem intervalIntegral_intervalIntegral_normSq_realSafeSmoothed_le_safeWeighted_universal
    (F : ℝ → ℂ) (hF : Continuous F)
    {P Q C D : ℝ} (hP : 0 < P) (hPQ : P ≤ Q) (hQ3P : Q ≤ 3 * P)
    (hC : 0 ≤ C) (hCD : C ≤ D)
    {A B T : ℝ} (hAB : A ≤ B) (hT : 0 < T)
    (haway : ∀ t ∈ Set.Icc A B, T ≤ |t|) :
    (∫ x in P..Q, ∫ u in C..D,
        Complex.normSq
          (lemma14RealSafeSmoothedMellinSegment F u A B x)) ≤
      Q ^ 3 * (lemma14UniversalFourierCauchyConstant * Real.pi) *
        (∫ u in C..D, (2 + u) ^ 2) *
        ∫ t in A..B,
          lemma14SafeReciprocalSqWeight T t * Complex.normSq (F t) := by
  let K : ℝ := Q ^ 3 *
    (lemma14UniversalFourierCauchyConstant * Real.pi)
  let E : ℝ := ∫ t in A..B,
    lemma14SafeReciprocalSqWeight T t * Complex.normSq (F t)
  have hK : 0 ≤ K := by
    dsimp only [K]
    exact mul_nonneg (pow_nonneg (hP.trans_le hPQ).le 3)
      (mul_nonneg lemma14UniversalFourierCauchyConstant_nonneg Real.pi_pos.le)
  have hmono :
      (∫ u in C..D, ∫ t in A..B,
          Complex.normSq (F t * safePerronRatioIncrement u t)) ≤
        ∫ u in C..D, (2 + u) ^ 2 * E := by
    apply intervalIntegral.integral_mono_on hCD
    · exact (continuous_safePerronMultiplierEnergy F hF A B).intervalIntegrable _ _
    · exact (by fun_prop : Continuous
        (fun u : ℝ ↦ (2 + u) ^ 2 * E)).intervalIntegrable _ _
    · intro u hu
      exact integral_normSq_mul_safePerronRatioIncrement_le_safeWeighted
        F hF (hC.trans hu.1) hAB hT haway
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
    _ ≤ K * ∫ u in C..D, (2 + u) ^ 2 * E :=
      mul_le_mul_of_nonneg_left hmono hK
    _ = K * (∫ u in C..D, (2 + u) ^ 2) * E := by
      rw [intervalIntegral.integral_mul_const]
      ring
    _ = _ := by rfl

/-! ## The left moving-endpoint source average -/

/-- The base-`x` moving-endpoint source term, now with a real spatial
endpoint. -/
def lemma14RealSourceSmoothedLeftOn
    (F : ℝ → ℂ) (x h A B : ℝ) : ℂ :=
  (h : ℂ)⁻¹ * ((2 * h : ℝ) : ℂ)⁻¹ * (x : ℂ) *
    ∫ u in h / x..3 * h / x,
      lemma14RealSafeSmoothedMellinSegment F u A B x

/-- Fixed-interval continuous extension obtained from `u=(h/x)v`. -/
def lemma14RealSourceSmoothedLeftExtension
    (P : ℝ) (F : ℝ → ℂ) (h A B x : ℝ) : ℂ :=
  ((2 * h : ℝ) : ℂ)⁻¹ *
    ∫ v in 1..3,
      lemma14ClampedSafeSmoothedMellinSegment P F
        (v * h / lemma14PositiveClamp P x) A B x

theorem lemma14RealSourceSmoothedLeftExtension_eq
    (F : ℝ → ℂ) {P x h : ℝ} (hP : 0 < P) (hPx : P ≤ x)
    (hh : 0 < h) (A B : ℝ) :
    lemma14RealSourceSmoothedLeftExtension P F h A B x =
      lemma14RealSourceSmoothedLeftOn F x h A B := by
  have hx : 0 < x := hP.trans_le hPx
  let M : ℝ → ℂ := fun u ↦
    lemma14RealSafeSmoothedMellinSegment F u A B x
  let c : ℝ := h / x
  have hc : c ≠ 0 := by dsimp only [c]; positivity
  have hcv := intervalIntegral.smul_integral_comp_mul_left
    (f := M) (a := 1) (b := 3) c
  have hleft : c * 1 = h / x := by simp [c]
  have hright : c * 3 = 3 * h / x := by dsimp only [c]; ring
  rw [hleft, hright] at hcv
  unfold lemma14RealSourceSmoothedLeftExtension
    lemma14RealSourceSmoothedLeftOn
  simp only [lemma14PositiveClamp_eq hP hPx]
  have hM (v : ℝ) :
      lemma14ClampedSafeSmoothedMellinSegment P F
          (v * h / x) A B x = M (c * v) := by
    dsimp only [M, c]
    rw [lemma14ClampedSafeSmoothedMellinSegment_eq P hP F
      (v * h / x) A B hPx]
    congr 2
    ring
  have hint : (∫ v in 1..3,
      lemma14ClampedSafeSmoothedMellinSegment P F
        (v * h / x) A B x) = ∫ v in 1..3, M (c * v) := by
    apply intervalIntegral.integral_congr
    intro v hv
    exact hM v
  rw [hint]
  simp only [Complex.real_smul] at hcv
  rw [← hcv]
  have hhC : (h : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hh.ne'
  have hxC : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  dsimp only [c]
  push_cast
  field_simp

theorem continuous_lemma14RealSourceSmoothedLeftExtension
    {P : ℝ} (hP : 0 < P) (F : ℝ → ℂ) (hF : Continuous F)
    (h A B : ℝ) :
    Continuous (lemma14RealSourceSmoothedLeftExtension P F h A B) := by
  have hclamp : Continuous (lemma14PositiveClamp P) := by
    unfold lemma14PositiveClamp
    fun_prop
  have hclamp_ne : ∀ x, lemma14PositiveClamp P x ≠ 0 :=
    fun x ↦ (lemma14PositiveClamp_pos hP x).ne'
  have hu : Continuous (fun p : ℝ × ℝ ↦
      p.2 * h / lemma14PositiveClamp P p.1) := by
    exact (continuous_snd.mul continuous_const).div
      (hclamp.comp continuous_fst) (fun p ↦ hclamp_ne p.1)
  have hp : Continuous (fun p : ℝ × ℝ ↦
      (p.1, p.2 * h / lemma14PositiveClamp P p.1)) :=
    continuous_fst.prodMk hu
  have hjoint :=
    continuous_uncurry_lemma14ClampedSafeSmoothedMellinSegment
      hP F hF A B
  unfold lemma14RealSourceSmoothedLeftExtension
  apply Continuous.const_mul
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
  exact hjoint.comp hp

theorem continuousOn_lemma14RealSourceSmoothedLeftOn
    {P : ℝ} (hP : 0 < P) (F : ℝ → ℂ) (hF : Continuous F)
    {h : ℝ} (hh : 0 < h) (A B : ℝ) :
    ContinuousOn (lemma14RealSourceSmoothedLeftOn F · h A B)
      (Set.Ici P) := by
  apply (continuous_lemma14RealSourceSmoothedLeftExtension
    hP F hF h A B).continuousOn.congr
  intro x hx
  exact (lemma14RealSourceSmoothedLeftExtension_eq F hP hx hh A B).symm

/-- Pointwise Cauchy--Schwarz and enlargement to a single common `u`
interval for the real left source term. -/
theorem normSq_lemma14RealSourceSmoothedLeftOn_le_common
    (F : ℝ → ℂ) (hF : Continuous F)
    {P Q x h : ℝ} (hP : 0 < P) (hPQ : P ≤ Q)
    (hx : x ∈ Set.Icc P Q) (hh : 0 < h) (A B : ℝ) :
    Complex.normSq (lemma14RealSourceSmoothedLeftOn F x h A B) ≤
      (Q / h ^ 3) *
        ∫ u in h / Q..3 * h / P,
          Complex.normSq
            (lemma14RealSafeSmoothedMellinSegment F u A B x) := by
  have hx0 : 0 < x := hP.trans_le hx.1
  have hlocal : h / x ≤ 3 * h / x := by
    have hp : 0 < h / x := by positivity
    rw [show 3 * h / x = 3 * (h / x) by ring]
    linarith
  have hleft : h / Q ≤ h / x :=
    div_le_div_of_nonneg_left hh.le hx0 hx.2
  have hright : 3 * h / x ≤ 3 * h / P :=
    div_le_div_of_nonneg_left (by positivity) hP hx.1
  have hM : Continuous (fun u ↦
      lemma14RealSafeSmoothedMellinSegment F u A B x) := by
    have hjoint : Continuous (Function.uncurry (fun x u ↦
        lemma14ClampedSafeSmoothedMellinSegment P F u A B x)) :=
      continuous_uncurry_lemma14ClampedSafeSmoothedMellinSegment
        hP F hF A B
    have hp : Continuous (fun u : ℝ ↦ (x, u)) :=
      continuous_const.prodMk continuous_id
    have hclamp : Continuous (fun u ↦
        lemma14ClampedSafeSmoothedMellinSegment P F u A B x) := by
      change Continuous
        (Function.uncurry (fun x u ↦
          lemma14ClampedSafeSmoothedMellinSegment P F u A B x) ∘
            fun u ↦ (x, u))
      exact hjoint.comp hp
    apply hclamp.congr
    intro u
    exact lemma14ClampedSafeSmoothedMellinSegment_eq
      P hP F u A B hx.1
  have hcs := normSq_intervalIntegral_le_length_mul_integral_normSq
    hM hlocal
  have henlarge :
      (∫ u in h / x..3 * h / x,
          Complex.normSq
            (lemma14RealSafeSmoothedMellinSegment F u A B x)) ≤
        ∫ u in h / Q..3 * h / P,
          Complex.normSq
            (lemma14RealSafeSmoothedMellinSegment F u A B x) :=
    intervalIntegral.integral_mono_interval hleft hlocal hright
      (MeasureTheory.ae_of_all _ (fun u ↦ Complex.normSq_nonneg _))
      ((Complex.continuous_normSq.comp hM).intervalIntegrable _ _)
  have hI0 : 0 ≤ ∫ u in h / x..3 * h / x,
      Complex.normSq
        (lemma14RealSafeSmoothedMellinSegment F u A B x) :=
    intervalIntegral.integral_nonneg_of_forall hlocal
      (fun u ↦ Complex.normSq_nonneg _)
  have hIcommon0 : 0 ≤ ∫ u in h / Q..3 * h / P,
      Complex.normSq
        (lemma14RealSafeSmoothedMellinSegment F u A B x) :=
    hI0.trans henlarge
  have hlen : 3 * h / x - h / x = 2 * h / x := by ring
  have hcoef :
      Complex.normSq
          ((h : ℂ)⁻¹ * ((2 * h : ℝ) : ℂ)⁻¹ * (x : ℂ)) *
        (2 * h / x) ≤ Q / h ^ 3 := by
    simp only [Complex.normSq_mul, Complex.normSq_inv,
      Complex.normSq_ofReal]
    field_simp [hh.ne', hx0.ne']
    nlinarith [hx.2]
  unfold lemma14RealSourceSmoothedLeftOn
  rw [Complex.normSq_mul]
  calc
    Complex.normSq
          ((h : ℂ)⁻¹ * ((2 * h : ℝ) : ℂ)⁻¹ * (x : ℂ)) *
        Complex.normSq (∫ u in h / x..3 * h / x,
          lemma14RealSafeSmoothedMellinSegment F u A B x) ≤
      Complex.normSq
          ((h : ℂ)⁻¹ * ((2 * h : ℝ) : ℂ)⁻¹ * (x : ℂ)) *
        ((2 * h / x) * ∫ u in h / x..3 * h / x,
          Complex.normSq
            (lemma14RealSafeSmoothedMellinSegment F u A B x)) := by
        apply mul_le_mul_of_nonneg_left
        simpa only [hlen] using hcs
        exact Complex.normSq_nonneg _
    _ = (Complex.normSq
          ((h : ℂ)⁻¹ * ((2 * h : ℝ) : ℂ)⁻¹ * (x : ℂ)) *
        (2 * h / x)) * ∫ u in h / x..3 * h / x,
          Complex.normSq
            (lemma14RealSafeSmoothedMellinSegment F u A B x) := by ring
    _ ≤ (Q / h ^ 3) * ∫ u in h / x..3 * h / x,
          Complex.normSq
            (lemma14RealSafeSmoothedMellinSegment F u A B x) :=
      mul_le_mul_of_nonneg_right hcoef hI0
    _ ≤ (Q / h ^ 3) * ∫ u in h / Q..3 * h / P,
          Complex.normSq
            (lemma14RealSafeSmoothedMellinSegment F u A B x) :=
      mul_le_mul_of_nonneg_left henlarge
        (div_nonneg (hP.trans_le hPQ).le (pow_nonneg hh.le 3))

/-- Integrated left source term, reduced to the common smoothing rectangle.
This is the Cauchy/enlargement step immediately preceding the continuous
Schur estimate. -/
theorem integral_normSq_lemma14RealSourceSmoothedLeftOn_le_rectangle
    (F : ℝ → ℂ) (hF : Continuous F)
    {P Q h : ℝ} (hP : 0 < P) (hPQ : P ≤ Q) (hh : 0 < h)
    (A B : ℝ) :
    (∫ x in P..Q,
        Complex.normSq (lemma14RealSourceSmoothedLeftOn F x h A B)) ≤
      (Q / h ^ 3) *
        ∫ x in P..Q, ∫ u in h / Q..3 * h / P,
          Complex.normSq
            (lemma14RealSafeSmoothedMellinSegment F u A B x) := by
  let C : ℝ := h / Q
  let D : ℝ := 3 * h / P
  have hleftCont : Continuous (fun x ↦ Complex.normSq
      (lemma14RealSourceSmoothedLeftExtension P F h A B x)) :=
    Complex.continuous_normSq.comp
      (continuous_lemma14RealSourceSmoothedLeftExtension hP F hF h A B)
  have hleftInt : IntervalIntegrable (fun x ↦ Complex.normSq
      (lemma14RealSourceSmoothedLeftOn F x h A B)) volume P Q := by
    apply ContinuousOn.intervalIntegrable_of_Icc hPQ
    apply hleftCont.continuousOn.congr
    intro x hx
    exact congrArg Complex.normSq
      (lemma14RealSourceSmoothedLeftExtension_eq F hP hx.1 hh A B).symm
  have hjoint : Continuous (Function.uncurry (fun x u ↦
      Complex.normSq
        (lemma14ClampedSafeSmoothedMellinSegment P F u A B x))) :=
    continuous_uncurry_normSq_lemma14ClampedSafeSmoothedMellinSegment
      hP F hF A B
  have hcommonExt : Continuous (fun x ↦ ∫ u in C..D,
      Complex.normSq
        (lemma14ClampedSafeSmoothedMellinSegment P F u A B x)) := by
    apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    exact hjoint
  have hcommonInt : IntervalIntegrable (fun x ↦
      (Q / h ^ 3) * ∫ u in C..D,
        Complex.normSq
          (lemma14RealSafeSmoothedMellinSegment F u A B x)) volume P Q := by
    apply ContinuousOn.intervalIntegrable_of_Icc hPQ
    apply (continuous_const.mul hcommonExt).continuousOn.congr
    intro x hx
    apply congrArg ((Q / h ^ 3) * ·)
    apply intervalIntegral.integral_congr
    intro u hu
    exact congrArg Complex.normSq
      (lemma14ClampedSafeSmoothedMellinSegment_eq
        P hP F u A B hx.1).symm
  calc
    (∫ x in P..Q,
        Complex.normSq (lemma14RealSourceSmoothedLeftOn F x h A B)) ≤
      ∫ x in P..Q, (Q / h ^ 3) * ∫ u in C..D,
        Complex.normSq
          (lemma14RealSafeSmoothedMellinSegment F u A B x) := by
        apply intervalIntegral.integral_mono_on hPQ hleftInt hcommonInt
        intro x hx
        simpa only [C, D] using
          normSq_lemma14RealSourceSmoothedLeftOn_le_common
            F hF hP hPQ hx hh A B
    _ = (Q / h ^ 3) * ∫ x in P..Q, ∫ u in C..D,
        Complex.normSq
          (lemma14RealSafeSmoothedMellinSegment F u A B x) := by
      rw [intervalIntegral.integral_const_mul]
    _ = _ := by rfl

/-- Complete low-frequency estimate for the left moving-endpoint source
piece.  The factor `Q/h³` from Cauchy is canceled by the cubic `u`-moment
on an interval of scale `h/P`. -/
theorem integral_normSq_lemma14RealSourceSmoothedLeftOn_le_low
    (F : ℝ → ℂ) (hF : Continuous F)
    {P Q h : ℝ} (hP : 0 < P) (hPQ : P ≤ Q) (hh : 0 < h)
    (delta L R : ℝ) (hdelta : 0 < delta)
    (hleft : L + 2 * delta ≤ -Real.log Q)
    (hright : -Real.log P ≤ R - 2 * delta)
    {A B : ℝ} (hAB : A ≤ B) :
    (∫ x in P..Q,
        Complex.normSq (lemma14RealSourceSmoothedLeftOn F x h A B)) ≤
      (Q / h ^ 3) *
        (Q ^ 3 *
          (lemma14FourierCauchyConstant
              (lemma14PositiveLogCutoff delta L R hdelta) * Real.pi) *
          (∫ u in h / Q..3 * h / P, u ^ 2) *
          ∫ t in A..B, Complex.normSq (F t)) := by
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
    intervalIntegral_intervalIntegral_normSq_realSafeSmoothed_le_low
      F hF hP hPQ (by positivity : 0 ≤ h / Q) hCD
      delta L R hdelta hleft hright hAB
  calc
    (∫ x in P..Q,
        Complex.normSq (lemma14RealSourceSmoothedLeftOn F x h A B)) ≤
      (Q / h ^ 3) *
        ∫ x in P..Q, ∫ u in h / Q..3 * h / P,
          Complex.normSq
            (lemma14RealSafeSmoothedMellinSegment F u A B x) := hrect
    _ ≤ (Q / h ^ 3) *
        (Q ^ 3 *
          (lemma14FourierCauchyConstant
              (lemma14PositiveLogCutoff delta L R hdelta) * Real.pi) *
          (∫ u in h / Q..3 * h / P, u ^ 2) *
          ∫ t in A..B, Complex.normSq (F t)) :=
      mul_le_mul_of_nonneg_left hsmooth
        (div_nonneg hQ.le (pow_nonneg hh.le 3))

/-- Complete reciprocal-frequency estimate for the left moving-endpoint
source piece. -/
theorem integral_normSq_lemma14RealSourceSmoothedLeftOn_le_high
    (F : ℝ → ℂ) (hF : Continuous F)
    {P Q h : ℝ} (hP : 0 < P) (hPQ : P ≤ Q) (hh : 0 < h)
    (delta L R : ℝ) (hdelta : 0 < delta)
    (hleft : L + 2 * delta ≤ -Real.log Q)
    (hright : -Real.log P ≤ R - 2 * delta)
    {A B T : ℝ} (hAB : A ≤ B) (hT : 0 < T)
    (haway : ∀ t ∈ Set.Icc A B, T ≤ |t|) :
    (∫ x in P..Q,
        Complex.normSq (lemma14RealSourceSmoothedLeftOn F x h A B)) ≤
      (Q / h ^ 3) *
        (Q ^ 3 *
          (lemma14FourierCauchyConstant
              (lemma14PositiveLogCutoff delta L R hdelta) * Real.pi) *
          (∫ u in h / Q..3 * h / P, ((2 + u) / T) ^ 2) *
          ∫ t in A..B, Complex.normSq (F t)) := by
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
    intervalIntegral_intervalIntegral_normSq_realSafeSmoothed_le_high
      F hF hP hPQ (by positivity : 0 ≤ h / Q) hCD
      delta L R hdelta hleft hright hAB hT haway
  calc
    (∫ x in P..Q,
        Complex.normSq (lemma14RealSourceSmoothedLeftOn F x h A B)) ≤
      (Q / h ^ 3) *
        ∫ x in P..Q, ∫ u in h / Q..3 * h / P,
          Complex.normSq
            (lemma14RealSafeSmoothedMellinSegment F u A B x) := hrect
    _ ≤ (Q / h ^ 3) *
        (Q ^ 3 *
          (lemma14FourierCauchyConstant
              (lemma14PositiveLogCutoff delta L R hdelta) * Real.pi) *
          (∫ u in h / Q..3 * h / P, ((2 + u) / T) ^ 2) *
          ∫ t in A..B, Complex.normSq (F t)) :=
      mul_le_mul_of_nonneg_left hsmooth
        (div_nonneg hQ.le (pow_nonneg hh.le 3))

/-- Outer-height-uniform reciprocal-square estimate for the left source
piece. -/
theorem integral_normSq_lemma14RealSourceSmoothedLeftOn_le_safeWeighted
    (F : ℝ → ℂ) (hF : Continuous F)
    {P Q h : ℝ} (hP : 0 < P) (hPQ : P ≤ Q) (hh : 0 < h)
    (delta L R : ℝ) (hdelta : 0 < delta)
    (hleft : L + 2 * delta ≤ -Real.log Q)
    (hright : -Real.log P ≤ R - 2 * delta)
    {A B T : ℝ} (hAB : A ≤ B) (hT : 0 < T)
    (haway : ∀ t ∈ Set.Icc A B, T ≤ |t|) :
    (∫ x in P..Q,
        Complex.normSq (lemma14RealSourceSmoothedLeftOn F x h A B)) ≤
      (Q / h ^ 3) *
        (Q ^ 3 *
          (lemma14FourierCauchyConstant
              (lemma14PositiveLogCutoff delta L R hdelta) * Real.pi) *
          (∫ u in h / Q..3 * h / P, (2 + u) ^ 2) *
          ∫ t in A..B,
            lemma14SafeReciprocalSqWeight T t * Complex.normSq (F t)) := by
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
    intervalIntegral_intervalIntegral_normSq_realSafeSmoothed_le_safeWeighted
      F hF hP hPQ (by positivity : 0 ≤ h / Q) hCD
      delta L R hdelta hleft hright hAB hT haway
  calc
    (∫ x in P..Q,
        Complex.normSq (lemma14RealSourceSmoothedLeftOn F x h A B)) ≤
      (Q / h ^ 3) *
        ∫ x in P..Q, ∫ u in h / Q..3 * h / P,
          Complex.normSq
            (lemma14RealSafeSmoothedMellinSegment F u A B x) := hrect
    _ ≤ (Q / h ^ 3) *
        (Q ^ 3 *
          (lemma14FourierCauchyConstant
              (lemma14PositiveLogCutoff delta L R hdelta) * Real.pi) *
          (∫ u in h / Q..3 * h / P, (2 + u) ^ 2) *
          ∫ t in A..B,
            lemma14SafeReciprocalSqWeight T t * Complex.normSq (F t)) :=
      mul_le_mul_of_nonneg_left hsmooth
        (div_nonneg hQ.le (pow_nonneg hh.le 3))

theorem integral_normSq_lemma14RealSourceSmoothedLeftOn_le_safeWeighted_universal
    (F : ℝ → ℂ) (hF : Continuous F)
    {P Q h : ℝ} (hP : 0 < P) (hPQ : P ≤ Q) (hQ3P : Q ≤ 3 * P)
    (hh : 0 < h) {A B T : ℝ} (hAB : A ≤ B) (hT : 0 < T)
    (haway : ∀ t ∈ Set.Icc A B, T ≤ |t|) :
    (∫ x in P..Q,
        Complex.normSq (lemma14RealSourceSmoothedLeftOn F x h A B)) ≤
      (Q / h ^ 3) *
        (Q ^ 3 * (lemma14UniversalFourierCauchyConstant * Real.pi) *
          (∫ u in h / Q..3 * h / P, (2 + u) ^ 2) *
          ∫ t in A..B,
            lemma14SafeReciprocalSqWeight T t * Complex.normSq (F t)) := by
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
    intervalIntegral_intervalIntegral_normSq_realSafeSmoothed_le_safeWeighted_universal
      F hF hP hPQ hQ3P (by positivity : 0 ≤ h / Q) hCD hAB hT haway
  calc
    (∫ x in P..Q,
        Complex.normSq (lemma14RealSourceSmoothedLeftOn F x h A B)) ≤
      (Q / h ^ 3) *
        ∫ x in P..Q, ∫ u in h / Q..3 * h / P,
          Complex.normSq
            (lemma14RealSafeSmoothedMellinSegment F u A B x) := hrect
    _ ≤ (Q / h ^ 3) *
        (Q ^ 3 * (lemma14UniversalFourierCauchyConstant * Real.pi) *
          (∫ u in h / Q..3 * h / P, (2 + u) ^ 2) *
          ∫ t in A..B,
            lemma14SafeReciprocalSqWeight T t * Complex.normSq (F t)) :=
      mul_le_mul_of_nonneg_left hsmooth
        (div_nonneg hQ.le (pow_nonneg hh.le 3))

/-! ## The shifted right moving-endpoint source average -/

def lemma14RealSourceSmoothedRightOn
    (F : ℝ → ℂ) (x h A B : ℝ) : ℂ :=
  (h : ℂ)⁻¹ * ((2 * h : ℝ) : ℂ)⁻¹ * ((x + h : ℝ) : ℂ) *
    ∫ u in 0..2 * h / (x + h),
      lemma14RealSafeSmoothedMellinSegment F u A B (x + h)

def lemma14RealSourceSmoothedRightExtension
    (P : ℝ) (F : ℝ → ℂ) (h A B x : ℝ) : ℂ :=
  ((2 * h : ℝ) : ℂ)⁻¹ *
    ∫ v in 0..2,
      lemma14ClampedSafeSmoothedMellinSegment (P + h) F
        (v * h / lemma14PositiveClamp (P + h) (x + h)) A B (x + h)

theorem lemma14RealSourceSmoothedRightExtension_eq
    (F : ℝ → ℂ) {P x h : ℝ} (hP : 0 < P) (hPx : P ≤ x)
    (hh : 0 < h) (A B : ℝ) :
    lemma14RealSourceSmoothedRightExtension P F h A B x =
      lemma14RealSourceSmoothedRightOn F x h A B := by
  have hPh : 0 < P + h := add_pos hP hh
  have hxh : 0 < x + h := add_pos (hP.trans_le hPx) hh
  have hbound : P + h ≤ x + h := by linarith
  let M : ℝ → ℂ := fun u ↦
    lemma14RealSafeSmoothedMellinSegment F u A B (x + h)
  let c : ℝ := h / (x + h)
  have hcv := intervalIntegral.smul_integral_comp_mul_left
    (f := M) (a := 0) (b := 2) c
  have hleft : c * 0 = 0 := by ring
  have hright : c * 2 = 2 * h / (x + h) := by dsimp only [c]; ring
  rw [hleft, hright] at hcv
  unfold lemma14RealSourceSmoothedRightExtension
    lemma14RealSourceSmoothedRightOn
  simp only [lemma14PositiveClamp_eq hPh hbound]
  have hint : (∫ v in 0..2,
      lemma14ClampedSafeSmoothedMellinSegment (P + h) F
        (v * h / (x + h)) A B (x + h)) =
      ∫ v in 0..2, M (c * v) := by
    apply intervalIntegral.integral_congr
    intro v hv
    change lemma14ClampedSafeSmoothedMellinSegment (P + h) F
        (v * h / (x + h)) A B (x + h) = M (c * v)
    rw [lemma14ClampedSafeSmoothedMellinSegment_eq
      (P + h) hPh F (v * h / (x + h)) A B hbound]
    congr 2
    dsimp only [c]
    ring
  rw [hint]
  simp only [Complex.real_smul] at hcv
  rw [← hcv]
  have hxhC : ((x + h : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr hxh.ne'
  have hsumC : (x : ℂ) + (h : ℂ) ≠ 0 := by
    simpa only [Complex.ofReal_add] using hxhC
  dsimp only [c]
  push_cast
  field_simp [hh.ne', hxh.ne', hxhC, hsumC]

theorem continuous_lemma14RealSourceSmoothedRightExtension
    {P h : ℝ} (hP : 0 < P) (hh : 0 < h)
    (F : ℝ → ℂ) (hF : Continuous F) (A B : ℝ) :
    Continuous (lemma14RealSourceSmoothedRightExtension P F h A B) := by
  have hPh : 0 < P + h := add_pos hP hh
  have hclamp : Continuous (lemma14PositiveClamp (P + h)) := by
    unfold lemma14PositiveClamp
    fun_prop
  have hclamp_ne : ∀ x, lemma14PositiveClamp (P + h) x ≠ 0 :=
    fun x ↦ (lemma14PositiveClamp_pos hPh x).ne'
  have hspace : Continuous (fun p : ℝ × ℝ ↦ p.1 + h) := by fun_prop
  have hu : Continuous (fun p : ℝ × ℝ ↦
      p.2 * h / lemma14PositiveClamp (P + h) (p.1 + h)) := by
    exact (continuous_snd.mul continuous_const).div
      (hclamp.comp hspace) (fun p ↦ hclamp_ne (p.1 + h))
  have hp : Continuous (fun p : ℝ × ℝ ↦
      (p.1 + h,
        p.2 * h / lemma14PositiveClamp (P + h) (p.1 + h))) :=
    hspace.prodMk hu
  have hjoint : Continuous (Function.uncurry (fun z u ↦
      lemma14ClampedSafeSmoothedMellinSegment (P + h) F u A B z)) :=
    continuous_uncurry_lemma14ClampedSafeSmoothedMellinSegment
      hPh F hF A B
  unfold lemma14RealSourceSmoothedRightExtension
  apply Continuous.const_mul
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
  let G : ℝ × ℝ → ℂ := fun p ↦
    lemma14ClampedSafeSmoothedMellinSegment (P + h) F
      (p.2 * h / lemma14PositiveClamp (P + h) (p.1 + h)) A B (p.1 + h)
  change Continuous G
  have hGeq : G = Function.uncurry (fun z u ↦
      lemma14ClampedSafeSmoothedMellinSegment (P + h) F u A B z) ∘
        (fun p ↦ (p.1 + h,
          p.2 * h / lemma14PositiveClamp (P + h) (p.1 + h))) := by
    funext p
    rfl
  rw [hGeq]
  exact hjoint.comp hp

theorem continuousOn_lemma14RealSourceSmoothedRightOn
    {P h : ℝ} (hP : 0 < P) (hh : 0 < h)
    (F : ℝ → ℂ) (hF : Continuous F) (A B : ℝ) :
    ContinuousOn (lemma14RealSourceSmoothedRightOn F · h A B)
      (Set.Ici P) := by
  apply (continuous_lemma14RealSourceSmoothedRightExtension
    hP hh F hF A B).continuousOn.congr
  intro x hx
  exact (lemma14RealSourceSmoothedRightExtension_eq
    F hP hx hh A B).symm

theorem normSq_lemma14RealSourceSmoothedRightOn_le_common
    (F : ℝ → ℂ) (hF : Continuous F)
    {P Q x h : ℝ} (hP : 0 < P) (hPQ : P ≤ Q)
    (hx : x ∈ Set.Icc P Q) (hh : 0 < h) (A B : ℝ) :
    Complex.normSq (lemma14RealSourceSmoothedRightOn F x h A B) ≤
      ((Q + h) / h ^ 3) *
        ∫ u in 0..2 * h / (P + h),
          Complex.normSq
            (lemma14RealSafeSmoothedMellinSegment F u A B (x + h)) := by
  have hPh : 0 < P + h := add_pos hP hh
  have hxh : 0 < x + h := add_pos (hP.trans_le hx.1) hh
  have hQh : 0 < Q + h := add_pos (hP.trans_le hPQ) hh
  have hlocal : 0 ≤ 2 * h / (x + h) := by positivity
  have hright : 2 * h / (x + h) ≤ 2 * h / (P + h) :=
    div_le_div_of_nonneg_left (by positivity) hPh (by linarith [hx.1])
  have hM : Continuous (fun u ↦
      lemma14RealSafeSmoothedMellinSegment F u A B (x + h)) := by
    have hjoint : Continuous (Function.uncurry (fun z u ↦
        lemma14ClampedSafeSmoothedMellinSegment (P + h) F u A B z)) :=
      continuous_uncurry_lemma14ClampedSafeSmoothedMellinSegment
        hPh F hF A B
    have hp : Continuous (fun u : ℝ ↦ (x + h, u)) := by fun_prop
    have hclamp : Continuous (fun u ↦
        lemma14ClampedSafeSmoothedMellinSegment (P + h) F u A B (x + h)) := by
      change Continuous (Function.uncurry (fun z u ↦
        lemma14ClampedSafeSmoothedMellinSegment (P + h) F u A B z) ∘
          fun u ↦ (x + h, u))
      exact hjoint.comp hp
    apply hclamp.congr
    intro u
    exact lemma14ClampedSafeSmoothedMellinSegment_eq
      (P + h) hPh F u A B (by linarith [hx.1])
  have hcs := normSq_intervalIntegral_le_length_mul_integral_normSq
    hM hlocal
  have henlarge :
      (∫ u in 0..2 * h / (x + h),
          Complex.normSq
            (lemma14RealSafeSmoothedMellinSegment F u A B (x + h))) ≤
        ∫ u in 0..2 * h / (P + h),
          Complex.normSq
            (lemma14RealSafeSmoothedMellinSegment F u A B (x + h)) :=
    intervalIntegral.integral_mono_interval (le_refl 0) hlocal hright
      (MeasureTheory.ae_of_all _ (fun u ↦ Complex.normSq_nonneg _))
      ((Complex.continuous_normSq.comp hM).intervalIntegrable _ _)
  have hI0 : 0 ≤ ∫ u in 0..2 * h / (x + h),
      Complex.normSq
        (lemma14RealSafeSmoothedMellinSegment F u A B (x + h)) :=
    intervalIntegral.integral_nonneg_of_forall hlocal
      (fun u ↦ Complex.normSq_nonneg _)
  have hcoef :
      Complex.normSq
          ((h : ℂ)⁻¹ * ((2 * h : ℝ) : ℂ)⁻¹ * ((x + h : ℝ) : ℂ)) *
        (2 * h / (x + h)) ≤ (Q + h) / h ^ 3 := by
    simp only [Complex.normSq_mul, Complex.normSq_inv,
      Complex.normSq_ofReal]
    field_simp [hh.ne', hxh.ne']
    nlinarith [hx.2]
  unfold lemma14RealSourceSmoothedRightOn
  rw [Complex.normSq_mul]
  calc
    Complex.normSq
          ((h : ℂ)⁻¹ * ((2 * h : ℝ) : ℂ)⁻¹ * ((x + h : ℝ) : ℂ)) *
        Complex.normSq (∫ u in 0..2 * h / (x + h),
          lemma14RealSafeSmoothedMellinSegment F u A B (x + h)) ≤
      Complex.normSq
          ((h : ℂ)⁻¹ * ((2 * h : ℝ) : ℂ)⁻¹ * ((x + h : ℝ) : ℂ)) *
        ((2 * h / (x + h)) * ∫ u in 0..2 * h / (x + h),
          Complex.normSq
            (lemma14RealSafeSmoothedMellinSegment F u A B (x + h))) := by
        apply mul_le_mul_of_nonneg_left
        simpa only [sub_zero] using hcs
        exact Complex.normSq_nonneg _
    _ = (Complex.normSq
          ((h : ℂ)⁻¹ * ((2 * h : ℝ) : ℂ)⁻¹ * ((x + h : ℝ) : ℂ)) *
        (2 * h / (x + h))) * ∫ u in 0..2 * h / (x + h),
          Complex.normSq
            (lemma14RealSafeSmoothedMellinSegment F u A B (x + h)) := by ring
    _ ≤ ((Q + h) / h ^ 3) * ∫ u in 0..2 * h / (x + h),
          Complex.normSq
            (lemma14RealSafeSmoothedMellinSegment F u A B (x + h)) :=
      mul_le_mul_of_nonneg_right hcoef hI0
    _ ≤ ((Q + h) / h ^ 3) * ∫ u in 0..2 * h / (P + h),
          Complex.normSq
            (lemma14RealSafeSmoothedMellinSegment F u A B (x + h)) :=
      mul_le_mul_of_nonneg_left henlarge
        (div_nonneg hQh.le (pow_nonneg hh.le 3))

theorem integral_normSq_lemma14RealSourceSmoothedRightOn_le_rectangle
    (F : ℝ → ℂ) (hF : Continuous F)
    {P Q h : ℝ} (hP : 0 < P) (hPQ : P ≤ Q) (hh : 0 < h)
    (A B : ℝ) :
    (∫ x in P..Q,
        Complex.normSq (lemma14RealSourceSmoothedRightOn F x h A B)) ≤
      ((Q + h) / h ^ 3) *
        ∫ z in (P + h)..(Q + h), ∫ u in 0..2 * h / (P + h),
          Complex.normSq
            (lemma14RealSafeSmoothedMellinSegment F u A B z) := by
  let D : ℝ := 2 * h / (P + h)
  have hPh : 0 < P + h := add_pos hP hh
  have hleftCont : Continuous (fun x ↦ Complex.normSq
      (lemma14RealSourceSmoothedRightExtension P F h A B x)) :=
    Complex.continuous_normSq.comp
      (continuous_lemma14RealSourceSmoothedRightExtension hP hh F hF A B)
  have hleftInt : IntervalIntegrable (fun x ↦ Complex.normSq
      (lemma14RealSourceSmoothedRightOn F x h A B)) volume P Q := by
    apply ContinuousOn.intervalIntegrable_of_Icc hPQ
    apply hleftCont.continuousOn.congr
    intro x hx
    exact congrArg Complex.normSq
      (lemma14RealSourceSmoothedRightExtension_eq F hP hx.1 hh A B).symm
  have hjoint : Continuous (Function.uncurry (fun z u ↦
      Complex.normSq
        (lemma14ClampedSafeSmoothedMellinSegment (P + h) F u A B z))) :=
    continuous_uncurry_normSq_lemma14ClampedSafeSmoothedMellinSegment
      hPh F hF A B
  have hp : Continuous (fun p : ℝ × ℝ ↦ (p.1 + h, p.2)) := by fun_prop
  have hshiftJoint : Continuous (Function.uncurry (fun x u ↦
      Complex.normSq
        (lemma14ClampedSafeSmoothedMellinSegment (P + h) F u A B (x + h)))) := by
    let G : ℝ × ℝ → ℝ := fun p ↦ Complex.normSq
      (lemma14ClampedSafeSmoothedMellinSegment (P + h) F p.2 A B (p.1 + h))
    change Continuous G
    have hGeq : G = Function.uncurry (fun z u ↦
        Complex.normSq
          (lemma14ClampedSafeSmoothedMellinSegment (P + h) F u A B z)) ∘
            fun p ↦ (p.1 + h, p.2) := by
      funext p
      rfl
    rw [hGeq]
    exact hjoint.comp hp
  have hcommonExt : Continuous (fun x ↦ ∫ u in 0..D,
      Complex.normSq
        (lemma14ClampedSafeSmoothedMellinSegment
          (P + h) F u A B (x + h))) := by
    apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    exact hshiftJoint
  have hcommonInt : IntervalIntegrable (fun x ↦
      ((Q + h) / h ^ 3) * ∫ u in 0..D,
        Complex.normSq
          (lemma14RealSafeSmoothedMellinSegment F u A B (x + h))) volume P Q := by
    apply ContinuousOn.intervalIntegrable_of_Icc hPQ
    apply (continuous_const.mul hcommonExt).continuousOn.congr
    intro x hx
    apply congrArg (((Q + h) / h ^ 3) * ·)
    apply intervalIntegral.integral_congr
    intro u hu
    exact congrArg Complex.normSq
      (lemma14ClampedSafeSmoothedMellinSegment_eq
        (P + h) hPh F u A B (by linarith [hx.1])).symm
  calc
    (∫ x in P..Q,
        Complex.normSq (lemma14RealSourceSmoothedRightOn F x h A B)) ≤
      ∫ x in P..Q, ((Q + h) / h ^ 3) * ∫ u in 0..D,
        Complex.normSq
          (lemma14RealSafeSmoothedMellinSegment F u A B (x + h)) := by
        apply intervalIntegral.integral_mono_on hPQ hleftInt hcommonInt
        intro x hx
        simpa only [D] using
          normSq_lemma14RealSourceSmoothedRightOn_le_common
            F hF hP hPQ hx hh A B
    _ = ((Q + h) / h ^ 3) * ∫ x in P..Q, ∫ u in 0..D,
        Complex.normSq
          (lemma14RealSafeSmoothedMellinSegment F u A B (x + h)) := by
      rw [intervalIntegral.integral_const_mul]
    _ = ((Q + h) / h ^ 3) * ∫ z in (P + h)..(Q + h), ∫ u in 0..D,
        Complex.normSq
          (lemma14RealSafeSmoothedMellinSegment F u A B z) := by
      apply congrArg (((Q + h) / h ^ 3) * ·)
      exact intervalIntegral.integral_comp_add_right
        (f := fun z ↦ ∫ u in 0..D,
          Complex.normSq
            (lemma14RealSafeSmoothedMellinSegment F u A B z)) h
    _ = _ := by rfl

theorem integral_normSq_lemma14RealSourceSmoothedRightOn_le_low
    (F : ℝ → ℂ) (hF : Continuous F)
    {P Q h : ℝ} (hP : 0 < P) (hPQ : P ≤ Q) (hh : 0 < h)
    (delta L R : ℝ) (hdelta : 0 < delta)
    (hleft : L + 2 * delta ≤ -Real.log (Q + h))
    (hright : -Real.log (P + h) ≤ R - 2 * delta)
    {A B : ℝ} (hAB : A ≤ B) :
    (∫ x in P..Q,
        Complex.normSq (lemma14RealSourceSmoothedRightOn F x h A B)) ≤
      ((Q + h) / h ^ 3) *
        ((Q + h) ^ 3 *
          (lemma14FourierCauchyConstant
              (lemma14PositiveLogCutoff delta L R hdelta) * Real.pi) *
          (∫ u in 0..2 * h / (P + h), u ^ 2) *
          ∫ t in A..B, Complex.normSq (F t)) := by
  have hPh : 0 < P + h := add_pos hP hh
  have hshift : P + h ≤ Q + h := by linarith
  have hD : 0 ≤ 2 * h / (P + h) := by positivity
  have hrect :=
    integral_normSq_lemma14RealSourceSmoothedRightOn_le_rectangle
      F hF hP hPQ hh A B
  have hsmooth :=
    intervalIntegral_intervalIntegral_normSq_realSafeSmoothed_le_low
      F hF hPh hshift (le_refl 0) hD
      delta L R hdelta hleft hright hAB
  calc
    (∫ x in P..Q,
        Complex.normSq (lemma14RealSourceSmoothedRightOn F x h A B)) ≤
      ((Q + h) / h ^ 3) *
        ∫ z in (P + h)..(Q + h), ∫ u in 0..2 * h / (P + h),
          Complex.normSq
            (lemma14RealSafeSmoothedMellinSegment F u A B z) := hrect
    _ ≤ ((Q + h) / h ^ 3) *
        ((Q + h) ^ 3 *
          (lemma14FourierCauchyConstant
              (lemma14PositiveLogCutoff delta L R hdelta) * Real.pi) *
          (∫ u in 0..2 * h / (P + h), u ^ 2) *
          ∫ t in A..B, Complex.normSq (F t)) :=
      mul_le_mul_of_nonneg_left hsmooth
        (div_nonneg (add_pos (hP.trans_le hPQ) hh).le
          (pow_nonneg hh.le 3))

theorem integral_normSq_lemma14RealSourceSmoothedRightOn_le_high
    (F : ℝ → ℂ) (hF : Continuous F)
    {P Q h : ℝ} (hP : 0 < P) (hPQ : P ≤ Q) (hh : 0 < h)
    (delta L R : ℝ) (hdelta : 0 < delta)
    (hleft : L + 2 * delta ≤ -Real.log (Q + h))
    (hright : -Real.log (P + h) ≤ R - 2 * delta)
    {A B T : ℝ} (hAB : A ≤ B) (hT : 0 < T)
    (haway : ∀ t ∈ Set.Icc A B, T ≤ |t|) :
    (∫ x in P..Q,
        Complex.normSq (lemma14RealSourceSmoothedRightOn F x h A B)) ≤
      ((Q + h) / h ^ 3) *
        ((Q + h) ^ 3 *
          (lemma14FourierCauchyConstant
              (lemma14PositiveLogCutoff delta L R hdelta) * Real.pi) *
          (∫ u in 0..2 * h / (P + h), ((2 + u) / T) ^ 2) *
          ∫ t in A..B, Complex.normSq (F t)) := by
  have hPh : 0 < P + h := add_pos hP hh
  have hshift : P + h ≤ Q + h := by linarith
  have hD : 0 ≤ 2 * h / (P + h) := by positivity
  have hrect :=
    integral_normSq_lemma14RealSourceSmoothedRightOn_le_rectangle
      F hF hP hPQ hh A B
  have hsmooth :=
    intervalIntegral_intervalIntegral_normSq_realSafeSmoothed_le_high
      F hF hPh hshift (le_refl 0) hD
      delta L R hdelta hleft hright hAB hT haway
  calc
    (∫ x in P..Q,
        Complex.normSq (lemma14RealSourceSmoothedRightOn F x h A B)) ≤
      ((Q + h) / h ^ 3) *
        ∫ z in (P + h)..(Q + h), ∫ u in 0..2 * h / (P + h),
          Complex.normSq
            (lemma14RealSafeSmoothedMellinSegment F u A B z) := hrect
    _ ≤ ((Q + h) / h ^ 3) *
        ((Q + h) ^ 3 *
          (lemma14FourierCauchyConstant
              (lemma14PositiveLogCutoff delta L R hdelta) * Real.pi) *
          (∫ u in 0..2 * h / (P + h), ((2 + u) / T) ^ 2) *
          ∫ t in A..B, Complex.normSq (F t)) :=
      mul_le_mul_of_nonneg_left hsmooth
        (div_nonneg (add_pos (hP.trans_le hPQ) hh).le
          (pow_nonneg hh.le 3))

/-- Outer-height-uniform reciprocal-square estimate for the shifted right
source piece. -/
theorem integral_normSq_lemma14RealSourceSmoothedRightOn_le_safeWeighted
    (F : ℝ → ℂ) (hF : Continuous F)
    {P Q h : ℝ} (hP : 0 < P) (hPQ : P ≤ Q) (hh : 0 < h)
    (delta L R : ℝ) (hdelta : 0 < delta)
    (hleft : L + 2 * delta ≤ -Real.log (Q + h))
    (hright : -Real.log (P + h) ≤ R - 2 * delta)
    {A B T : ℝ} (hAB : A ≤ B) (hT : 0 < T)
    (haway : ∀ t ∈ Set.Icc A B, T ≤ |t|) :
    (∫ x in P..Q,
        Complex.normSq (lemma14RealSourceSmoothedRightOn F x h A B)) ≤
      ((Q + h) / h ^ 3) *
        ((Q + h) ^ 3 *
          (lemma14FourierCauchyConstant
              (lemma14PositiveLogCutoff delta L R hdelta) * Real.pi) *
          (∫ u in 0..2 * h / (P + h), (2 + u) ^ 2) *
          ∫ t in A..B,
            lemma14SafeReciprocalSqWeight T t * Complex.normSq (F t)) := by
  have hPh : 0 < P + h := add_pos hP hh
  have hshift : P + h ≤ Q + h := by linarith
  have hD : 0 ≤ 2 * h / (P + h) := by positivity
  have hrect :=
    integral_normSq_lemma14RealSourceSmoothedRightOn_le_rectangle
      F hF hP hPQ hh A B
  have hsmooth :=
    intervalIntegral_intervalIntegral_normSq_realSafeSmoothed_le_safeWeighted
      F hF hPh hshift (le_refl 0) hD
      delta L R hdelta hleft hright hAB hT haway
  calc
    (∫ x in P..Q,
        Complex.normSq (lemma14RealSourceSmoothedRightOn F x h A B)) ≤
      ((Q + h) / h ^ 3) *
        ∫ z in (P + h)..(Q + h), ∫ u in 0..2 * h / (P + h),
          Complex.normSq
            (lemma14RealSafeSmoothedMellinSegment F u A B z) := hrect
    _ ≤ ((Q + h) / h ^ 3) *
        ((Q + h) ^ 3 *
          (lemma14FourierCauchyConstant
              (lemma14PositiveLogCutoff delta L R hdelta) * Real.pi) *
          (∫ u in 0..2 * h / (P + h), (2 + u) ^ 2) *
          ∫ t in A..B,
            lemma14SafeReciprocalSqWeight T t * Complex.normSq (F t)) :=
      mul_le_mul_of_nonneg_left hsmooth
        (div_nonneg (add_pos (hP.trans_le hPQ) hh).le
          (pow_nonneg hh.le 3))

theorem integral_normSq_lemma14RealSourceSmoothedRightOn_le_safeWeighted_universal
    (F : ℝ → ℂ) (hF : Continuous F)
    {P Q h : ℝ} (hP : 0 < P) (hPQ : P ≤ Q) (hQ3P : Q ≤ 3 * P)
    (hh : 0 < h) {A B T : ℝ} (hAB : A ≤ B) (hT : 0 < T)
    (haway : ∀ t ∈ Set.Icc A B, T ≤ |t|) :
    (∫ x in P..Q,
        Complex.normSq (lemma14RealSourceSmoothedRightOn F x h A B)) ≤
      ((Q + h) / h ^ 3) *
        ((Q + h) ^ 3 *
          (lemma14UniversalFourierCauchyConstant * Real.pi) *
          (∫ u in 0..2 * h / (P + h), (2 + u) ^ 2) *
          ∫ t in A..B,
            lemma14SafeReciprocalSqWeight T t * Complex.normSq (F t)) := by
  have hPh : 0 < P + h := add_pos hP hh
  have hshift : P + h ≤ Q + h := by linarith
  have hshift3 : Q + h ≤ 3 * (P + h) := by linarith
  have hD : 0 ≤ 2 * h / (P + h) := by positivity
  have hrect :=
    integral_normSq_lemma14RealSourceSmoothedRightOn_le_rectangle
      F hF hP hPQ hh A B
  have hsmooth :=
    intervalIntegral_intervalIntegral_normSq_realSafeSmoothed_le_safeWeighted_universal
      F hF hPh hshift hshift3 (le_refl 0) hD hAB hT haway
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
          (∫ u in 0..2 * h / (P + h), (2 + u) ^ 2) *
          ∫ t in A..B,
            lemma14SafeReciprocalSqWeight T t * Complex.normSq (F t)) :=
      mul_le_mul_of_nonneg_left hsmooth
        (div_nonneg (add_pos (hP.trans_le hPQ) hh).le
          (pow_nonneg hh.le 3))

/-! ## Recombination into the finite Perron segment -/

/-- Fubini for the real fixed-base source smoothing transform. -/
theorem intervalIntegral_realSafeSmoothedMellinSegment_eq_swap
    (F : ℝ → ℂ) (hF : Continuous F) {x C D : ℝ}
    (hx : 0 < x) (hC : 0 ≤ C) (hCD : C ≤ D) (A B : ℝ) :
    (∫ u in C..D,
        lemma14RealSafeSmoothedMellinSegment F u A B x) =
      ∫ t in A..B, F t *
        (x : ℂ) ^ ((1 : ℂ) + (t : ℂ) * Complex.I) *
          ∫ u in C..D, perronRatioIncrement u t := by
  have hxC : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  letI : NeZero (x : ℂ) := ⟨hxC⟩
  let H : ℝ → ℝ → ℂ := fun t u ↦ F t *
    (x : ℂ) ^ ((1 : ℂ) + (t : ℂ) * Complex.I) *
      safePerronRatioIncrement u t
  have hpow : Continuous (fun p : ℝ × ℝ ↦
      (x : ℂ) ^ ((1 : ℂ) + (p.1 : ℂ) * Complex.I)) :=
    (continuous_const_cpow (x : ℂ)).comp (by fun_prop)
  have hH : Continuous (Function.uncurry H) := by
    exact ((hF.comp continuous_fst).mul hpow).mul
      (continuous_uncurry_safePerronRatioIncrement.comp continuous_swap)
  have hrect : IntegrableOn (Function.uncurry H)
      (Set.uIoc A B ×ˢ Set.uIoc C D) :=
    (hH.continuousOn.integrableOn_compact
      (isCompact_uIcc.prod isCompact_uIcc)).mono_set
        (Set.prod_mono Set.uIoc_subset_uIcc Set.uIoc_subset_uIcc)
  have hswap :
      (∫ t in A..B, ∫ u in C..D, H t u) =
        ∫ u in C..D, ∫ t in A..B, H t u :=
    MeasureTheory.intervalIntegral_intervalIntegral_swap hrect
  calc
    (∫ u in C..D,
        lemma14RealSafeSmoothedMellinSegment F u A B x) =
      ∫ u in C..D, ∫ t in A..B, H t u := by
        apply intervalIntegral.integral_congr
        intro u hu
        unfold lemma14RealSafeSmoothedMellinSegment lemma14MellinSegment
        apply intervalIntegral.integral_congr
        intro t ht
        dsimp only [H]
        ring
    _ = ∫ t in A..B, ∫ u in C..D, H t u := hswap.symm
    _ = ∫ t in A..B, F t *
        (x : ℂ) ^ ((1 : ℂ) + (t : ℂ) * Complex.I) *
          ∫ u in C..D, perronRatioIncrement u t := by
      apply intervalIntegral.integral_congr
      intro t ht
      change (∫ u in C..D, H t u) =
        F t * (x : ℂ) ^ ((1 : ℂ) + (t : ℂ) * Complex.I) *
          ∫ u in C..D, perronRatioIncrement u t
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro u hu
      rw [Set.uIcc_of_le hCD] at hu
      dsimp only [H]
      rw [safePerronRatioIncrement_eq_of_nonneg (hC.trans hu.1)]

/-- Exact real-endpoint source smoothing identity for one finite Perron
segment. -/
theorem perronKernelSegmentOn_eq_realSourceSmoothed
    (F : ℝ → ℂ) (hF : Continuous F) {x h : ℝ}
    (hx : 0 < x) (hh : 0 < h) (A B : ℝ) :
    perronKernelSegmentOn F x h A B =
      (((2 * Real.pi : ℝ) : ℂ)⁻¹ *
        (lemma14RealSourceSmoothedLeftOn F x h A B -
          lemma14RealSourceSmoothedRightOn F x h A B)) := by
  have hxh : 0 < x + h := add_pos hx hh
  have hleftOrder : h / x ≤ 3 * h / x := by
    have hp : 0 < h / x := by positivity
    rw [show 3 * h / x = 3 * (h / x) by ring]
    linarith
  have hleftSwap := intervalIntegral_realSafeSmoothedMellinSegment_eq_swap
    F hF hx (by positivity : 0 ≤ h / x) hleftOrder A B
  have hrightSwap := intervalIntegral_realSafeSmoothedMellinSegment_eq_swap
    F hF hxh (le_refl 0) (by positivity : 0 ≤ 2 * h / (x + h)) A B
  letI : NeZero (x : ℂ) := ⟨Complex.ofReal_ne_zero.mpr hx.ne'⟩
  letI : NeZero ((x + h : ℝ) : ℂ) :=
    ⟨Complex.ofReal_ne_zero.mpr hxh.ne'⟩
  let L : ℝ → ℂ := fun t ↦ F t *
    (x : ℂ) ^ ((1 : ℂ) + (t : ℂ) * Complex.I) *
      ∫ u in h / x..3 * h / x, perronRatioIncrement u t
  let R : ℝ → ℂ := fun t ↦ F t *
    ((x + h : ℝ) : ℂ) ^ ((1 : ℂ) + (t : ℂ) * Complex.I) *
      ∫ u in 0..2 * h / (x + h), perronRatioIncrement u t
  have hL : Continuous L := by
    dsimp only [L]
    exact (hF.mul ((continuous_const_cpow (x : ℂ)).comp (by fun_prop))).mul
      (continuous_intervalIntegral_perronRatioIncrement
        (a := h / x) (b := 3 * h / x) (by positivity) hleftOrder)
  have hR : Continuous R := by
    dsimp only [R]
    exact (hF.mul ((continuous_const_cpow ((x + h : ℝ) : ℂ)).comp
      (by fun_prop))).mul
        (continuous_intervalIntegral_perronRatioIncrement
          (a := 0) (b := 2 * h / (x + h)) (le_refl 0) (by positivity))
  unfold perronKernelSegmentOn lemma14RealSourceSmoothedLeftOn
    lemma14RealSourceSmoothedRightOn
  rw [hleftSwap, hrightSwap]
  apply congrArg ((((2 * Real.pi : ℝ) : ℂ)⁻¹) * ·)
  calc
    (∫ t in A..B, F t * perronIncrementKernel x h t) =
      ∫ t in A..B,
        (h : ℂ)⁻¹ * ((2 * h : ℝ) : ℂ)⁻¹ *
          ((x : ℂ) * L t - ((x + h : ℝ) : ℂ) * R t) := by
        apply intervalIntegral.integral_congr
        intro t ht
        change F t * perronIncrementKernel x h t =
          (h : ℂ)⁻¹ * ((2 * h : ℝ) : ℂ)⁻¹ *
            ((x : ℂ) * L t - ((x + h : ℝ) : ℂ) * R t)
        rw [perronIncrementKernel_eq_sourceSmoothed_real hx hh t]
        rw [intervalIntegral.integral_const_mul,
          intervalIntegral.integral_const_mul]
        dsimp only [L, R]
        ring
    _ = (h : ℂ)⁻¹ * ((2 * h : ℝ) : ℂ)⁻¹ * (x : ℂ) *
          (∫ t in A..B, L t) -
        (h : ℂ)⁻¹ * ((2 * h : ℝ) : ℂ)⁻¹ * ((x + h : ℝ) : ℂ) *
          (∫ t in A..B, R t) := by
      rw [intervalIntegral.integral_const_mul,
        intervalIntegral.integral_sub
          ((hL.const_mul (x : ℂ)).intervalIntegrable A B)
          ((hR.const_mul ((x + h : ℝ) : ℂ)).intervalIntegrable A B),
        intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const_mul]
      ring
    _ = _ := by rfl

theorem continuousOn_perronKernelSegmentOn
    (F : ℝ → ℂ) (hF : Continuous F)
    {P h : ℝ} (hP : 0 < P) (hh : 0 < h) (A B : ℝ) :
    ContinuousOn (fun x ↦ perronKernelSegmentOn F x h A B)
      (Set.Ici P) := by
  let c : ℂ := (((2 * Real.pi : ℝ) : ℂ))⁻¹
  let L : ℝ → ℂ := fun x ↦ lemma14RealSourceSmoothedLeftOn F x h A B
  let R : ℝ → ℂ := fun x ↦ lemma14RealSourceSmoothedRightOn F x h A B
  have hLc : ContinuousOn L (Set.Ici P) :=
    continuousOn_lemma14RealSourceSmoothedLeftOn hP F hF hh A B
  have hRc : ContinuousOn R (Set.Ici P) :=
    continuousOn_lemma14RealSourceSmoothedRightOn hP hh F hF A B
  apply (continuousOn_const.mul (hLc.sub hRc)).congr
  intro x hx
  change perronKernelSegmentOn F x h A B = c * (L x - R x)
  exact perronKernelSegmentOn_eq_realSourceSmoothed
    F hF (hP.trans_le hx) hh A B

/-- Combine any integrated bounds for the two real source pieces into an
integrated bound for the finite Perron segment. -/
theorem integral_normSq_perronKernelSegmentOn_le_of_sourceBounds
    (F : ℝ → ℂ) (hF : Continuous F)
    {P Q h : ℝ} (hP : 0 < P) (hPQ : P ≤ Q) (hh : 0 < h)
    (A B Eleft Eright : ℝ)
    (hleft : (∫ x in P..Q,
      Complex.normSq (lemma14RealSourceSmoothedLeftOn F x h A B)) ≤ Eleft)
    (hright : (∫ x in P..Q,
      Complex.normSq (lemma14RealSourceSmoothedRightOn F x h A B)) ≤ Eright) :
    (∫ x in P..Q,
        Complex.normSq (perronKernelSegmentOn F x h A B)) ≤
      2 * Complex.normSq ((((2 * Real.pi : ℝ) : ℂ))⁻¹) *
        (Eleft + Eright) := by
  let c : ℂ := (((2 * Real.pi : ℝ) : ℂ))⁻¹
  let L : ℝ → ℂ := fun x ↦ lemma14RealSourceSmoothedLeftOn F x h A B
  let R : ℝ → ℂ := fun x ↦ lemma14RealSourceSmoothedRightOn F x h A B
  have hLc : ContinuousOn L (Set.Ici P) :=
    continuousOn_lemma14RealSourceSmoothedLeftOn hP F hF hh A B
  have hRc : ContinuousOn R (Set.Ici P) :=
    continuousOn_lemma14RealSourceSmoothedRightOn hP hh F hF A B
  have hbaseCont : ContinuousOn (fun x ↦ c * (L x - R x)) (Set.Ici P) :=
    continuousOn_const.mul (hLc.sub hRc)
  have hsegCont : ContinuousOn
      (fun x ↦ Complex.normSq (perronKernelSegmentOn F x h A B))
      (Set.uIcc P Q) := by
    apply (Complex.continuous_normSq.comp_continuousOn
      (hbaseCont.mono (by
        rw [Set.uIcc_of_le hPQ]
        exact Set.Icc_subset_Ici_self))).congr
    intro x hx
    rw [Set.uIcc_of_le hPQ] at hx
    exact congrArg Complex.normSq
      (perronKernelSegmentOn_eq_realSourceSmoothed
        F hF (hP.trans_le hx.1) hh A B)
  have hmajorCont : ContinuousOn (fun x ↦
      2 * Complex.normSq c *
        (Complex.normSq (L x) + Complex.normSq (R x)))
      (Set.uIcc P Q) := by
    exact continuousOn_const.mul
      ((Complex.continuous_normSq.comp_continuousOn
          (hLc.mono (by
            rw [Set.uIcc_of_le hPQ]
            exact Set.Icc_subset_Ici_self))).add
        (Complex.continuous_normSq.comp_continuousOn
          (hRc.mono (by
            rw [Set.uIcc_of_le hPQ]
            exact Set.Icc_subset_Ici_self))))
  have hpoint (x : ℝ) (hx : x ∈ Set.Icc P Q) :
      Complex.normSq (perronKernelSegmentOn F x h A B) ≤
        2 * Complex.normSq c *
          (Complex.normSq (L x) + Complex.normSq (R x)) := by
    rw [perronKernelSegmentOn_eq_realSourceSmoothed
      F hF (hP.trans_le hx.1) hh A B]
    change Complex.normSq (c * (L x - R x)) ≤ _
    rw [Complex.normSq_mul]
    have hs := normSq_sub_le_two_mul_add (L x) (R x)
    nlinarith [Complex.normSq_nonneg c]
  calc
    (∫ x in P..Q,
        Complex.normSq (perronKernelSegmentOn F x h A B)) ≤
      ∫ x in P..Q, 2 * Complex.normSq c *
        (Complex.normSq (L x) + Complex.normSq (R x)) := by
          exact intervalIntegral.integral_mono_on hPQ
            hsegCont.intervalIntegrable hmajorCont.intervalIntegrable hpoint
    _ = 2 * Complex.normSq c *
        ((∫ x in P..Q, Complex.normSq (L x)) +
          ∫ x in P..Q, Complex.normSq (R x)) := by
      rw [intervalIntegral.integral_const_mul]
      congr 1
      simpa only [Function.comp_apply] using
        intervalIntegral.integral_add
          ((Complex.continuous_normSq.comp_continuousOn
            (hLc.mono (by
              rw [Set.uIcc_of_le hPQ]
              exact Set.Icc_subset_Ici_self))).intervalIntegrable)
          ((Complex.continuous_normSq.comp_continuousOn
            (hRc.mono (by
              rw [Set.uIcc_of_le hPQ]
              exact Set.Icc_subset_Ici_self))).intervalIntegrable)
    _ ≤ 2 * Complex.normSq c * (Eleft + Eright) := by
      apply mul_le_mul_of_nonneg_left (add_le_add hleft hright)
      exact mul_nonneg (by norm_num) (Complex.normSq_nonneg c)
    _ = _ := by rfl

/-! ## Explicit source-weighted Perron segment bounds -/

/-- The low-frequency source envelope for one normalized short average. -/
def lemma14PerronSegmentLowEnvelope
    (F : ℝ → ℂ) (P Q h delta L R A B : ℝ) (hdelta : 0 < delta) : ℝ :=
  2 * Complex.normSq ((((2 * Real.pi : ℝ) : ℂ))⁻¹) *
    ((Q / h ^ 3) *
      (Q ^ 3 *
        (lemma14FourierCauchyConstant
            (lemma14PositiveLogCutoff delta L R hdelta) * Real.pi) *
        (∫ u in h / Q..3 * h / P, u ^ 2) *
        ∫ t in A..B, Complex.normSq (F t)) +
      ((Q + h) / h ^ 3) *
      ((Q + h) ^ 3 *
        (lemma14FourierCauchyConstant
            (lemma14PositiveLogCutoff delta L R hdelta) * Real.pi) *
        (∫ u in 0..2 * h / (P + h), u ^ 2) *
        ∫ t in A..B, Complex.normSq (F t)))

/-- The reciprocal-frequency source envelope for one normalized short
average on a band separated from the origin by `T`. -/
def lemma14PerronSegmentHighEnvelope
    (F : ℝ → ℂ) (P Q h delta L R A B T : ℝ) (hdelta : 0 < delta) : ℝ :=
  2 * Complex.normSq ((((2 * Real.pi : ℝ) : ℂ))⁻¹) *
    ((Q / h ^ 3) *
      (Q ^ 3 *
        (lemma14FourierCauchyConstant
            (lemma14PositiveLogCutoff delta L R hdelta) * Real.pi) *
        (∫ u in h / Q..3 * h / P, ((2 + u) / T) ^ 2) *
        ∫ t in A..B, Complex.normSq (F t)) +
      ((Q + h) / h ^ 3) *
      ((Q + h) ^ 3 *
        (lemma14FourierCauchyConstant
            (lemma14PositiveLogCutoff delta L R hdelta) * Real.pi) *
        (∫ u in 0..2 * h / (P + h), ((2 + u) / T) ^ 2) *
        ∫ t in A..B, Complex.normSq (F t)))

/-- The outer-height-uniform reciprocal-square source envelope. -/
def lemma14PerronSegmentSafeWeightedEnvelope
    (F : ℝ → ℂ) (P Q h delta L R A B T : ℝ) (hdelta : 0 < delta) : ℝ :=
  2 * Complex.normSq ((((2 * Real.pi : ℝ) : ℂ))⁻¹) *
    ((Q / h ^ 3) *
      (Q ^ 3 *
        (lemma14FourierCauchyConstant
            (lemma14PositiveLogCutoff delta L R hdelta) * Real.pi) *
        (∫ u in h / Q..3 * h / P, (2 + u) ^ 2) *
        ∫ t in A..B,
          lemma14SafeReciprocalSqWeight T t * Complex.normSq (F t)) +
      ((Q + h) / h ^ 3) *
      ((Q + h) ^ 3 *
        (lemma14FourierCauchyConstant
            (lemma14PositiveLogCutoff delta L R hdelta) * Real.pi) *
        (∫ u in 0..2 * h / (P + h), (2 + u) ^ 2) *
        ∫ t in A..B,
          lemma14SafeReciprocalSqWeight T t * Complex.normSq (F t)))

/-- The analytic coefficient multiplying the reciprocal-square vertical
energy in the safe weighted Perron estimate. -/
def lemma14PerronSegmentSafeWeightedCoefficient
    (P Q h delta L R : ℝ) (hdelta : 0 < delta) : ℝ :=
  2 * Complex.normSq ((((2 * Real.pi : ℝ) : ℂ))⁻¹) *
    ((Q / h ^ 3) *
      (Q ^ 3 *
        (lemma14FourierCauchyConstant
            (lemma14PositiveLogCutoff delta L R hdelta) * Real.pi) *
        (∫ u in h / Q..3 * h / P, (2 + u) ^ 2)) +
      ((Q + h) / h ^ 3) *
      ((Q + h) ^ 3 *
        (lemma14FourierCauchyConstant
            (lemma14PositiveLogCutoff delta L R hdelta) * Real.pi) *
        (∫ u in 0..2 * h / (P + h), (2 + u) ^ 2)))

/-- Scale-free version of the source coefficient, using the one fixed
universal logarithmic cutoff. -/
def lemma14UniversalPerronSegmentSafeWeightedCoefficient
    (P Q h : ℝ) : ℝ :=
  2 * Complex.normSq ((((2 * Real.pi : ℝ) : ℂ))⁻¹) *
    ((Q / h ^ 3) *
      (Q ^ 3 * (lemma14UniversalFourierCauchyConstant * Real.pi) *
        (∫ u in h / Q..3 * h / P, (2 + u) ^ 2)) +
      ((Q + h) / h ^ 3) *
      ((Q + h) ^ 3 *
        (lemma14UniversalFourierCauchyConstant * Real.pi) *
        (∫ u in 0..2 * h / (P + h), (2 + u) ^ 2)))

theorem lemma14UniversalPerronSegmentSafeWeightedCoefficient_nonneg
    {P Q h : ℝ} (hP : 0 < P) (hPQ : P ≤ Q) (hh : 0 < h) :
    0 ≤ lemma14UniversalPerronSegmentSafeWeightedCoefficient P Q h := by
  have hQ : 0 < Q := hP.trans_le hPQ
  have hCD : h / Q ≤ 3 * h / P := by
    have h1 : h / Q ≤ h / P :=
      div_le_div_of_nonneg_left hh.le hP hPQ
    have h2 : h / P ≤ 3 * h / P := by
      have hp : 0 < h / P := by positivity
      rw [show 3 * h / P = 3 * (h / P) by ring]
      linarith
    exact h1.trans h2
  have hD : 0 ≤ 2 * h / (P + h) := by positivity
  have hleftMoment : 0 ≤ ∫ u in h / Q..3 * h / P, (2 + u) ^ 2 :=
    intervalIntegral.integral_nonneg hCD (fun u hu ↦ sq_nonneg _)
  have hrightMoment : 0 ≤ ∫ u in 0..2 * h / (P + h), (2 + u) ^ 2 :=
    intervalIntegral.integral_nonneg hD (fun u hu ↦ sq_nonneg _)
  have hcut : 0 ≤ lemma14UniversalFourierCauchyConstant * Real.pi :=
    mul_nonneg lemma14UniversalFourierCauchyConstant_nonneg Real.pi_pos.le
  have hleftTerm : 0 ≤ (Q / h ^ 3) *
      (Q ^ 3 * (lemma14UniversalFourierCauchyConstant * Real.pi) *
        (∫ u in h / Q..3 * h / P, (2 + u) ^ 2)) := by
    apply mul_nonneg (div_nonneg hQ.le (pow_nonneg hh.le 3))
    exact mul_nonneg (mul_nonneg (pow_nonneg hQ.le 3) hcut) hleftMoment
  have hrightTerm : 0 ≤ ((Q + h) / h ^ 3) *
      ((Q + h) ^ 3 *
        (lemma14UniversalFourierCauchyConstant * Real.pi) *
        (∫ u in 0..2 * h / (P + h), (2 + u) ^ 2)) := by
    have hQh : 0 < Q + h := add_pos hQ hh
    apply mul_nonneg (div_nonneg hQh.le (pow_nonneg hh.le 3))
    exact mul_nonneg (mul_nonneg (pow_nonneg hQh.le 3) hcut) hrightMoment
  unfold lemma14UniversalPerronSegmentSafeWeightedCoefficient
  exact mul_nonneg
    (mul_nonneg (by norm_num) (Complex.normSq_nonneg _))
    (add_nonneg hleftTerm hrightTerm)

theorem lemma14_left_source_moment_le
    {X H : ℝ} (hX : 0 < X) (hH : 0 < H) (hHX : H ≤ X) :
    (∫ u in H / (2 * X)..3 * H / X, (2 + u) ^ 2) ≤ 75 * H / X := by
  have hC : 0 ≤ H / (2 * X) := by positivity
  have hD : 3 * H / X ≤ 3 := by
    apply (div_le_iff₀ hX).2
    nlinarith
  have heq : H / (2 * X) = (H / X) / 2 := by ring
  have hCD : H / (2 * X) ≤ 3 * H / X := by
    rw [heq]
    calc
      H / X / 2 = (1 / 2 : ℝ) * (H / X) := by ring
      _ ≤ 3 * (H / X) := by gcongr <;> norm_num
      _ = 3 * H / X := by ring
  calc
    (∫ u in H / (2 * X)..3 * H / X, (2 + u) ^ 2) ≤
      ∫ _u in H / (2 * X)..3 * H / X, (25 : ℝ) := by
      apply intervalIntegral.integral_mono_on hCD
      · exact (by fun_prop : Continuous
          (fun u : ℝ ↦ (2 + u) ^ 2)).intervalIntegrable _ _
      · exact continuous_const.intervalIntegrable _ _
      · intro u hu
        have hu0 : 0 ≤ u := hC.trans hu.1
        have hu5 : 2 + u ≤ 5 := by linarith [hu.2, hD]
        nlinarith [sq_nonneg (2 + u)]
    _ = 25 * (3 * H / X - H / (2 * X)) := by simp; ring
    _ ≤ 75 * H / X := by
      rw [heq]
      calc
        25 * (3 * H / X - H / X / 2) =
            (125 / 2 : ℝ) * (H / X) := by ring
        _ ≤ 75 * (H / X) := by gcongr <;> norm_num
        _ = 75 * H / X := by ring

theorem lemma14_right_source_moment_le
    {X H : ℝ} (hX : 0 < X) (hH : 0 < H) :
    (∫ u in 0..2 * H / (X + H), (2 + u) ^ 2) ≤ 32 * H / X := by
  have hD0 : 0 ≤ 2 * H / (X + H) := by positivity
  have hD2 : 2 * H / (X + H) ≤ 2 := by
    apply (div_le_iff₀ (add_pos hX hH)).2
    nlinarith
  have hDX : 2 * H / (X + H) ≤ 2 * H / X := by
    apply div_le_div_of_nonneg_left (by positivity) hX
    linarith
  calc
    (∫ u in 0..2 * H / (X + H), (2 + u) ^ 2) ≤
      ∫ _u in 0..2 * H / (X + H), (16 : ℝ) := by
      apply intervalIntegral.integral_mono_on hD0
      · exact (by fun_prop : Continuous
          (fun u : ℝ ↦ (2 + u) ^ 2)).intervalIntegrable _ _
      · exact continuous_const.intervalIntegrable _ _
      · intro u hu
        have hu0 : 0 ≤ u := hu.1
        have hu4 : 2 + u ≤ 4 := by linarith [hu.2, hD2]
        nlinarith [sq_nonneg (2 + u)]
    _ = 16 * (2 * H / (X + H)) := by simp; ring
    _ ≤ 16 * (2 * H / X) :=
      mul_le_mul_of_nonneg_left hDX (by norm_num)
    _ = 32 * H / X := by ring

/-- Absolute scale-free constant in the scalarized source coefficient. -/
def lemma14UniversalScaledHighConstant : ℝ :=
  7584 * Complex.normSq ((((2 * Real.pi : ℝ) : ℂ))⁻¹) *
    (lemma14UniversalFourierCauchyConstant * Real.pi)

theorem lemma14UniversalScaledHighConstant_nonneg :
    0 ≤ lemma14UniversalScaledHighConstant := by
  unfold lemma14UniversalScaledHighConstant
  exact mul_nonneg
    (mul_nonneg (by norm_num) (Complex.normSq_nonneg _))
    (mul_nonneg lemma14UniversalFourierCauchyConstant_nonneg Real.pi_pos.le)

/-- Explicit polynomial bound for the universal source coefficient on
`[X,2X]`, valid uniformly for every `0 < H ≤ X`. -/
theorem lemma14UniversalPerronSegmentSafeWeightedCoefficient_le
    {X H : ℝ} (hX : 0 < X) (hH : 0 < H) (hHX : H ≤ X) :
    lemma14UniversalPerronSegmentSafeWeightedCoefficient X (2 * X) H ≤
      lemma14UniversalScaledHighConstant * X ^ 3 / H ^ 2 := by
  let K : ℝ := lemma14UniversalFourierCauchyConstant * Real.pi
  let IL : ℝ := ∫ u in H / (2 * X)..3 * H / X, (2 + u) ^ 2
  let IR : ℝ := ∫ u in 0..2 * H / (X + H), (2 + u) ^ 2
  have hK : 0 ≤ K :=
    mul_nonneg lemma14UniversalFourierCauchyConstant_nonneg Real.pi_pos.le
  have hIL : 0 ≤ IL := by
    dsimp only [IL]
    apply intervalIntegral.integral_nonneg
    · have heq : H / (2 * X) = (H / X) / 2 := by ring
      rw [heq]
      calc
        H / X / 2 = (1 / 2 : ℝ) * (H / X) := by ring
        _ ≤ 3 * (H / X) := by gcongr <;> norm_num
        _ = 3 * H / X := by ring
    · intro u hu
      exact sq_nonneg _
  have hIR : 0 ≤ IR := by
    dsimp only [IR]
    exact intervalIntegral.integral_nonneg (by positivity)
      (fun u hu ↦ sq_nonneg _)
  have hILb : IL ≤ 75 * H / X :=
    lemma14_left_source_moment_le hX hH hHX
  have hIRb : IR ≤ 32 * H / X :=
    lemma14_right_source_moment_le hX hH
  have hfacL : 0 ≤ (2 * X) ^ 4 / H ^ 3 := by positivity
  have hleft :
      ((2 * X) / H ^ 3) * ((2 * X) ^ 3 * K * IL) ≤
        1200 * K * X ^ 3 / H ^ 2 := by
    calc
      _ = K * (((2 * X) ^ 4 / H ^ 3) * IL) := by ring
      _ ≤ K * (((2 * X) ^ 4 / H ^ 3) * (75 * H / X)) := by
        gcongr
      _ = 1200 * K * X ^ 3 / H ^ 2 := by
        field_simp [hX.ne', hH.ne']
        ring
  have hbaseR : 0 ≤ 2 * X + H := by positivity
  have hleR : 2 * X + H ≤ 3 * X := by linarith
  have hpowR : (2 * X + H) ^ 4 ≤ (3 * X) ^ 4 :=
    pow_le_pow_left₀ hbaseR hleR 4
  have hfacR : (2 * X + H) ^ 4 / H ^ 3 ≤ 81 * X ^ 4 / H ^ 3 := by
    have hdiv := div_le_div_of_nonneg_right hpowR (pow_nonneg hH.le 3)
    simpa only [show (3 * X) ^ 4 = 81 * X ^ 4 by ring] using hdiv
  have hright :
      ((2 * X + H) / H ^ 3) * ((2 * X + H) ^ 3 * K * IR) ≤
        2592 * K * X ^ 3 / H ^ 2 := by
    calc
      _ = K * (((2 * X + H) ^ 4 / H ^ 3) * IR) := by ring
      _ ≤ K * ((81 * X ^ 4 / H ^ 3) * IR) := by gcongr
      _ ≤ K * ((81 * X ^ 4 / H ^ 3) * (32 * H / X)) := by gcongr
      _ = 2592 * K * X ^ 3 / H ^ 2 := by
        field_simp [hX.ne', hH.ne']
        ring
  unfold lemma14UniversalPerronSegmentSafeWeightedCoefficient
    lemma14UniversalScaledHighConstant
  change 2 * Complex.normSq ((((2 * Real.pi : ℝ) : ℂ))⁻¹) *
    ((((2 * X) / H ^ 3) * ((2 * X) ^ 3 * K * IL)) +
      (((2 * X + H) / H ^ 3) * ((2 * X + H) ^ 3 * K * IR))) ≤ _
  calc
    _ ≤ 2 * Complex.normSq ((((2 * Real.pi : ℝ) : ℂ))⁻¹) *
      ((1200 * K * X ^ 3 / H ^ 2) +
        (2592 * K * X ^ 3 / H ^ 2)) := by
      apply mul_le_mul_of_nonneg_left (add_le_add hleft hright)
      exact mul_nonneg (by norm_num) (Complex.normSq_nonneg _)
    _ = 7584 * Complex.normSq ((((2 * Real.pi : ℝ) : ℂ))⁻¹) *
        K * X ^ 3 / H ^ 2 := by ring
    _ = _ := by rfl

theorem lemma14PerronSegmentSafeWeightedEnvelope_eq
    (F : ℝ → ℂ) (P Q h delta L R A B T : ℝ) (hdelta : 0 < delta) :
    lemma14PerronSegmentSafeWeightedEnvelope
        F P Q h delta L R A B T hdelta =
      lemma14PerronSegmentSafeWeightedCoefficient
          P Q h delta L R hdelta *
        ∫ t in A..B,
          lemma14SafeReciprocalSqWeight T t * Complex.normSq (F t) := by
  unfold lemma14PerronSegmentSafeWeightedEnvelope
    lemma14PerronSegmentSafeWeightedCoefficient
  ring

theorem lemma14PerronSegmentSafeWeightedCoefficient_nonneg
    {P Q h delta L R : ℝ} (hP : 0 < P) (hPQ : P ≤ Q)
    (hh : 0 < h) (hdelta : 0 < delta) :
    0 ≤ lemma14PerronSegmentSafeWeightedCoefficient
      P Q h delta L R hdelta := by
  have hQ : 0 < Q := hP.trans_le hPQ
  have hPh : 0 < P + h := add_pos hP hh
  have hCD : h / Q ≤ 3 * h / P := by
    have h1 : h / Q ≤ h / P :=
      div_le_div_of_nonneg_left hh.le hP hPQ
    have h2 : h / P ≤ 3 * h / P := by
      have hp : 0 < h / P := by positivity
      rw [show 3 * h / P = 3 * (h / P) by ring]
      linarith
    exact h1.trans h2
  have hD : 0 ≤ 2 * h / (P + h) := by positivity
  have hleftMoment : 0 ≤ ∫ u in h / Q..3 * h / P, (2 + u) ^ 2 :=
    intervalIntegral.integral_nonneg hCD (fun u hu ↦ sq_nonneg _)
  have hrightMoment : 0 ≤ ∫ u in 0..2 * h / (P + h), (2 + u) ^ 2 :=
    intervalIntegral.integral_nonneg hD (fun u hu ↦ sq_nonneg _)
  have hcut : 0 ≤ lemma14FourierCauchyConstant
      (lemma14PositiveLogCutoff delta L R hdelta) * Real.pi :=
    mul_nonneg
      (lemma14FourierCauchyConstant_nonneg
        (lemma14PositiveLogCutoff delta L R hdelta)) Real.pi_pos.le
  have hleftTerm : 0 ≤ (Q / h ^ 3) *
      (Q ^ 3 *
        (lemma14FourierCauchyConstant
            (lemma14PositiveLogCutoff delta L R hdelta) * Real.pi) *
        (∫ u in h / Q..3 * h / P, (2 + u) ^ 2)) := by
    apply mul_nonneg (div_nonneg hQ.le (pow_nonneg hh.le 3))
    exact mul_nonneg (mul_nonneg (pow_nonneg hQ.le 3) hcut) hleftMoment
  have hrightTerm : 0 ≤ ((Q + h) / h ^ 3) *
      ((Q + h) ^ 3 *
        (lemma14FourierCauchyConstant
            (lemma14PositiveLogCutoff delta L R hdelta) * Real.pi) *
        (∫ u in 0..2 * h / (P + h), (2 + u) ^ 2)) := by
    have hQh : 0 < Q + h := add_pos hQ hh
    apply mul_nonneg (div_nonneg hQh.le (pow_nonneg hh.le 3))
    exact mul_nonneg (mul_nonneg (pow_nonneg hQh.le 3) hcut) hrightMoment
  unfold lemma14PerronSegmentSafeWeightedCoefficient
  exact mul_nonneg
    (mul_nonneg (by norm_num) (Complex.normSq_nonneg _))
    (add_nonneg hleftTerm hrightTerm)

/-- Concrete low-frequency continuous-endpoint estimate for the actual
finite Perron segment.  This is the cancellation-friendly source bound:
the only small multiplier moment is the quadratic `u`-moment. -/
theorem integral_normSq_perronKernelSegmentOn_le_low
    (F : ℝ → ℂ) (hF : Continuous F)
    {P Q h : ℝ} (hP : 0 < P) (hPQ : P ≤ Q) (hh : 0 < h)
    (delta L R : ℝ) (hdelta : 0 < delta)
    (hleft : L + 2 * delta ≤ -Real.log (Q + h))
    (hright : -Real.log P ≤ R - 2 * delta)
    {A B : ℝ} (hAB : A ≤ B) :
    (∫ x in P..Q,
        Complex.normSq (perronKernelSegmentOn F x h A B)) ≤
      lemma14PerronSegmentLowEnvelope F P Q h delta L R A B hdelta := by
  have hleftQ : L + 2 * delta ≤ -Real.log Q := by
    have hQ : 0 < Q := hP.trans_le hPQ
    have hQh : Q ≤ Q + h := by linarith
    exact hleft.trans (neg_le_neg (Real.log_le_log hQ hQh))
  have hrightPh : -Real.log (P + h) ≤ R - 2 * delta := by
    have hPh : 0 < P + h := add_pos hP hh
    have hPPh : P ≤ P + h := by linarith
    exact (neg_le_neg (Real.log_le_log hP hPPh)).trans hright
  apply integral_normSq_perronKernelSegmentOn_le_of_sourceBounds
      F hF hP hPQ hh A B
  · exact integral_normSq_lemma14RealSourceSmoothedLeftOn_le_low
      F hF hP hPQ hh delta L R hdelta hleftQ hright hAB
  · exact integral_normSq_lemma14RealSourceSmoothedRightOn_le_low
      F hF hP hPQ hh delta L R hdelta hleft hrightPh hAB

/-- Concrete reciprocal-frequency continuous-endpoint estimate for the
actual finite Perron segment.  Its band dependence is exactly a vertical
energy multiplied by the squared reciprocal-frequency moment. -/
theorem integral_normSq_perronKernelSegmentOn_le_high
    (F : ℝ → ℂ) (hF : Continuous F)
    {P Q h : ℝ} (hP : 0 < P) (hPQ : P ≤ Q) (hh : 0 < h)
    (delta L R : ℝ) (hdelta : 0 < delta)
    (hleft : L + 2 * delta ≤ -Real.log (Q + h))
    (hright : -Real.log P ≤ R - 2 * delta)
    {A B T : ℝ} (hAB : A ≤ B) (hT : 0 < T)
    (haway : ∀ t ∈ Set.Icc A B, T ≤ |t|) :
    (∫ x in P..Q,
        Complex.normSq (perronKernelSegmentOn F x h A B)) ≤
      lemma14PerronSegmentHighEnvelope F P Q h delta L R A B T hdelta := by
  have hleftQ : L + 2 * delta ≤ -Real.log Q := by
    have hQ : 0 < Q := hP.trans_le hPQ
    have hQh : Q ≤ Q + h := by linarith
    exact hleft.trans (neg_le_neg (Real.log_le_log hQ hQh))
  have hrightPh : -Real.log (P + h) ≤ R - 2 * delta := by
    have hPh : 0 < P + h := add_pos hP hh
    have hPPh : P ≤ P + h := by linarith
    exact (neg_le_neg (Real.log_le_log hP hPPh)).trans hright
  apply integral_normSq_perronKernelSegmentOn_le_of_sourceBounds
      F hF hP hPQ hh A B
  · exact integral_normSq_lemma14RealSourceSmoothedLeftOn_le_high
      F hF hP hPQ hh delta L R hdelta hleftQ hright hAB hT haway
  · exact integral_normSq_lemma14RealSourceSmoothedRightOn_le_high
      F hF hP hPQ hh delta L R hdelta hleft hrightPh hAB hT haway

/-- Final outer-height-uniform continuous source estimate for an actual
Perron segment.  Increasing `A,B` changes only the reciprocal-square
vertical energy, never the analytic constant. -/
theorem integral_normSq_perronKernelSegmentOn_le_safeWeighted
    (F : ℝ → ℂ) (hF : Continuous F)
    {P Q h : ℝ} (hP : 0 < P) (hPQ : P ≤ Q) (hh : 0 < h)
    (delta L R : ℝ) (hdelta : 0 < delta)
    (hleft : L + 2 * delta ≤ -Real.log (Q + h))
    (hright : -Real.log P ≤ R - 2 * delta)
    {A B T : ℝ} (hAB : A ≤ B) (hT : 0 < T)
    (haway : ∀ t ∈ Set.Icc A B, T ≤ |t|) :
    (∫ x in P..Q,
        Complex.normSq (perronKernelSegmentOn F x h A B)) ≤
      lemma14PerronSegmentSafeWeightedEnvelope
        F P Q h delta L R A B T hdelta := by
  have hleftQ : L + 2 * delta ≤ -Real.log Q := by
    have hQ : 0 < Q := hP.trans_le hPQ
    have hQh : Q ≤ Q + h := by linarith
    exact hleft.trans (neg_le_neg (Real.log_le_log hQ hQh))
  have hrightPh : -Real.log (P + h) ≤ R - 2 * delta := by
    have hPh : 0 < P + h := add_pos hP hh
    have hPPh : P ≤ P + h := by linarith
    exact (neg_le_neg (Real.log_le_log hP hPPh)).trans hright
  apply integral_normSq_perronKernelSegmentOn_le_of_sourceBounds
      F hF hP hPQ hh A B
  · exact
      integral_normSq_lemma14RealSourceSmoothedLeftOn_le_safeWeighted
        F hF hP hPQ hh delta L R hdelta hleftQ hright hAB hT haway
  · exact
      integral_normSq_lemma14RealSourceSmoothedRightOn_le_safeWeighted
        F hF hP hPQ hh delta L R hdelta hleft hrightPh hAB hT haway

theorem integral_normSq_perronKernelSegmentOn_le_safeWeighted_universal
    (F : ℝ → ℂ) (hF : Continuous F)
    {P Q h : ℝ} (hP : 0 < P) (hPQ : P ≤ Q) (hQ3P : Q ≤ 3 * P)
    (hh : 0 < h) {A B T : ℝ} (hAB : A ≤ B) (hT : 0 < T)
    (haway : ∀ t ∈ Set.Icc A B, T ≤ |t|) :
    (∫ x in P..Q,
        Complex.normSq (perronKernelSegmentOn F x h A B)) ≤
      lemma14UniversalPerronSegmentSafeWeightedCoefficient P Q h *
        ∫ t in A..B,
          lemma14SafeReciprocalSqWeight T t * Complex.normSq (F t) := by
  let E : ℝ := ∫ t in A..B,
    lemma14SafeReciprocalSqWeight T t * Complex.normSq (F t)
  let EL : ℝ := (Q / h ^ 3) *
    (Q ^ 3 * (lemma14UniversalFourierCauchyConstant * Real.pi) *
      (∫ u in h / Q..3 * h / P, (2 + u) ^ 2) * E)
  let ER : ℝ := ((Q + h) / h ^ 3) *
    ((Q + h) ^ 3 * (lemma14UniversalFourierCauchyConstant * Real.pi) *
      (∫ u in 0..2 * h / (P + h), (2 + u) ^ 2) * E)
  have hL : (∫ x in P..Q,
      Complex.normSq (lemma14RealSourceSmoothedLeftOn F x h A B)) ≤ EL := by
    exact integral_normSq_lemma14RealSourceSmoothedLeftOn_le_safeWeighted_universal
      F hF hP hPQ hQ3P hh hAB hT haway
  have hR : (∫ x in P..Q,
      Complex.normSq (lemma14RealSourceSmoothedRightOn F x h A B)) ≤ ER := by
    exact integral_normSq_lemma14RealSourceSmoothedRightOn_le_safeWeighted_universal
      F hF hP hPQ hQ3P hh hAB hT haway
  have hbase := integral_normSq_perronKernelSegmentOn_le_of_sourceBounds
    F hF hP hPQ hh A B EL ER hL hR
  calc
    (∫ x in P..Q,
        Complex.normSq (perronKernelSegmentOn F x h A B)) ≤
      2 * Complex.normSq ((((2 * Real.pi : ℝ) : ℂ))⁻¹) *
        (EL + ER) := hbase
    _ = lemma14UniversalPerronSegmentSafeWeightedCoefficient P Q h * E := by
      unfold lemma14UniversalPerronSegmentSafeWeightedCoefficient
      dsimp only [EL, ER]
      ring
    _ = _ := by rfl

theorem intervalIntegral_normSq_add_le_two_add
    (f g : ℝ → ℂ) {P Q : ℝ} (hPQ : P ≤ Q)
    (hf : ContinuousOn f (Set.uIcc P Q))
    (hg : ContinuousOn g (Set.uIcc P Q)) :
    (∫ x in P..Q, Complex.normSq (f x + g x)) ≤
      2 * ((∫ x in P..Q, Complex.normSq (f x)) +
        ∫ x in P..Q, Complex.normSq (g x)) := by
  have hsumc : ContinuousOn (fun x ↦
      Complex.normSq (f x + g x)) (Set.uIcc P Q) :=
    Complex.continuous_normSq.comp_continuousOn (hf.add hg)
  have hmajorc : ContinuousOn (fun x ↦
      2 * (Complex.normSq (f x) + Complex.normSq (g x)))
      (Set.uIcc P Q) :=
    continuousOn_const.mul
      ((Complex.continuous_normSq.comp_continuousOn hf).add
        (Complex.continuous_normSq.comp_continuousOn hg))
  calc
    (∫ x in P..Q, Complex.normSq (f x + g x)) ≤
      ∫ x in P..Q,
        2 * (Complex.normSq (f x) + Complex.normSq (g x)) := by
      apply intervalIntegral.integral_mono_on hPQ
        hsumc.intervalIntegrable hmajorc.intervalIntegrable
      intro x hx
      have h := normSq_sub_le_two_mul_add (f x) (-g x)
      simpa only [sub_neg_eq_add, Complex.normSq_neg] using h
    _ = 2 * ((∫ x in P..Q, Complex.normSq (f x)) +
        ∫ x in P..Q, Complex.normSq (g x)) := by
      rw [intervalIntegral.integral_const_mul]
      congr 1
      simpa only [Function.comp_apply] using
        intervalIntegral.integral_add
          (Complex.continuous_normSq.comp_continuousOn hf).intervalIntegrable
          (Complex.continuous_normSq.comp_continuousOn hg).intervalIntegrable

/-- The positive and negative high-frequency parts of a symmetric finite
Perron integral. -/
def lemma14SymmetricPerronHighSegmentOn
    (F : ℝ → ℂ) (x h T U : ℝ) : ℂ :=
  perronKernelSegmentOn F x h (-U) (-T) +
    perronKernelSegmentOn F x h T U

/-- Uniform finite-outer-height high-frequency estimate in the exact form
needed before taking the full Perron limit.  Both tails retain their
reciprocal-square vertical energies. -/
theorem integral_normSq_lemma14SymmetricPerronHighSegmentOn_le_safeWeighted
    (F : ℝ → ℂ) (hF : Continuous F)
    {P Q h T U : ℝ} (hP : 0 < P) (hPQ : P ≤ Q) (hh : 0 < h)
    (hT : 0 < T) (hTU : T ≤ U)
    (delta L R : ℝ) (hdelta : 0 < delta)
    (hleft : L + 2 * delta ≤ -Real.log (Q + h))
    (hright : -Real.log P ≤ R - 2 * delta) :
    (∫ x in P..Q,
        Complex.normSq
          (lemma14SymmetricPerronHighSegmentOn F x h T U)) ≤
      2 *
        (lemma14PerronSegmentSafeWeightedEnvelope
            F P Q h delta L R (-U) (-T) T hdelta +
          lemma14PerronSegmentSafeWeightedEnvelope
            F P Q h delta L R T U T hdelta) := by
  have hnegAway : ∀ t ∈ Set.Icc (-U) (-T), T ≤ |t| := by
    intro t ht
    rw [abs_of_nonpos (ht.2.trans (neg_nonpos.mpr hT.le))]
    linarith [ht.2]
  have hposAway : ∀ t ∈ Set.Icc T U, T ≤ |t| := by
    intro t ht
    rw [abs_of_nonneg (hT.le.trans ht.1)]
    exact ht.1
  have hneg := integral_normSq_perronKernelSegmentOn_le_safeWeighted
    F hF hP hPQ hh delta L R hdelta hleft hright
      (neg_le_neg hTU) hT hnegAway
  have hpos := integral_normSq_perronKernelSegmentOn_le_safeWeighted
    F hF hP hPQ hh delta L R hdelta hleft hright
      hTU hT hposAway
  let N : ℝ → ℂ := fun x ↦ perronKernelSegmentOn F x h (-U) (-T)
  let S : ℝ → ℂ := fun x ↦ perronKernelSegmentOn F x h T U
  have hNc : ContinuousOn N (Set.uIcc P Q) :=
    (continuousOn_perronKernelSegmentOn F hF hP hh (-U) (-T)).mono
      (by rw [Set.uIcc_of_le hPQ]; exact Set.Icc_subset_Ici_self)
  have hSc : ContinuousOn S (Set.uIcc P Q) :=
    (continuousOn_perronKernelSegmentOn F hF hP hh T U).mono
      (by rw [Set.uIcc_of_le hPQ]; exact Set.Icc_subset_Ici_self)
  have hsumc : ContinuousOn (fun x ↦
      Complex.normSq (N x + S x)) (Set.uIcc P Q) :=
    Complex.continuous_normSq.comp_continuousOn (hNc.add hSc)
  have hmajorc : ContinuousOn (fun x ↦
      2 * (Complex.normSq (N x) + Complex.normSq (S x)))
      (Set.uIcc P Q) :=
    continuousOn_const.mul
      ((Complex.continuous_normSq.comp_continuousOn hNc).add
        (Complex.continuous_normSq.comp_continuousOn hSc))
  have hpoint (x : ℝ) (hx : x ∈ Set.Icc P Q) :
      Complex.normSq (N x + S x) ≤
        2 * (Complex.normSq (N x) + Complex.normSq (S x)) := by
    have h := normSq_sub_le_two_mul_add (N x) (-S x)
    simpa only [sub_neg_eq_add, Complex.normSq_neg] using h
  unfold lemma14SymmetricPerronHighSegmentOn
  change (∫ x in P..Q, Complex.normSq (N x + S x)) ≤ _
  calc
    (∫ x in P..Q, Complex.normSq (N x + S x)) ≤
      ∫ x in P..Q,
        2 * (Complex.normSq (N x) + Complex.normSq (S x)) := by
      exact intervalIntegral.integral_mono_on hPQ
        hsumc.intervalIntegrable hmajorc.intervalIntegrable hpoint
    _ = 2 * ((∫ x in P..Q, Complex.normSq (N x)) +
        ∫ x in P..Q, Complex.normSq (S x)) := by
      rw [intervalIntegral.integral_const_mul]
      congr 1
      simpa only [Function.comp_apply] using
        intervalIntegral.integral_add
          (Complex.continuous_normSq.comp_continuousOn hNc).intervalIntegrable
          (Complex.continuous_normSq.comp_continuousOn hSc).intervalIntegrable
    _ ≤ 2 *
        (lemma14PerronSegmentSafeWeightedEnvelope
            F P Q h delta L R (-U) (-T) T hdelta +
          lemma14PerronSegmentSafeWeightedEnvelope
            F P Q h delta L R T U T hdelta) := by
      exact mul_le_mul_of_nonneg_left (add_le_add hneg hpos) (by norm_num)

/-- Universal-cutoff version of the symmetric high-frequency estimate.
The analytic coefficient is independent of the location of the logarithmic
window; all dependence on the vertical band remains in the weighted energies. -/
theorem integral_normSq_lemma14SymmetricPerronHighSegmentOn_le_safeWeighted_universal
    (F : ℝ → ℂ) (hF : Continuous F)
    {P Q h T U : ℝ} (hP : 0 < P) (hPQ : P ≤ Q) (hQ3P : Q ≤ 3 * P)
    (hh : 0 < h) (hT : 0 < T) (hTU : T ≤ U) :
    (∫ x in P..Q,
        Complex.normSq
          (lemma14SymmetricPerronHighSegmentOn F x h T U)) ≤
      2 * lemma14UniversalPerronSegmentSafeWeightedCoefficient P Q h *
        ((∫ t in -U..-T,
            lemma14SafeReciprocalSqWeight T t * Complex.normSq (F t)) +
          ∫ t in T..U,
            lemma14SafeReciprocalSqWeight T t * Complex.normSq (F t)) := by
  have hnegAway : ∀ t ∈ Set.Icc (-U) (-T), T ≤ |t| := by
    intro t ht
    rw [abs_of_nonpos (ht.2.trans (neg_nonpos.mpr hT.le))]
    linarith [ht.2]
  have hposAway : ∀ t ∈ Set.Icc T U, T ≤ |t| := by
    intro t ht
    rw [abs_of_nonneg (hT.le.trans ht.1)]
    exact ht.1
  have hneg := integral_normSq_perronKernelSegmentOn_le_safeWeighted_universal
    F hF hP hPQ hQ3P hh (neg_le_neg hTU) hT hnegAway
  have hpos := integral_normSq_perronKernelSegmentOn_le_safeWeighted_universal
    F hF hP hPQ hQ3P hh hTU hT hposAway
  let N : ℝ → ℂ := fun x ↦ perronKernelSegmentOn F x h (-U) (-T)
  let S : ℝ → ℂ := fun x ↦ perronKernelSegmentOn F x h T U
  have hNc : ContinuousOn N (Set.uIcc P Q) :=
    (continuousOn_perronKernelSegmentOn F hF hP hh (-U) (-T)).mono
      (by rw [Set.uIcc_of_le hPQ]; exact Set.Icc_subset_Ici_self)
  have hSc : ContinuousOn S (Set.uIcc P Q) :=
    (continuousOn_perronKernelSegmentOn F hF hP hh T U).mono
      (by rw [Set.uIcc_of_le hPQ]; exact Set.Icc_subset_Ici_self)
  have hcombine := intervalIntegral_normSq_add_le_two_add N S hPQ hNc hSc
  unfold lemma14SymmetricPerronHighSegmentOn
  change (∫ x in P..Q, Complex.normSq (N x + S x)) ≤ _
  calc
    (∫ x in P..Q, Complex.normSq (N x + S x)) ≤
        2 * ((∫ x in P..Q, Complex.normSq (N x)) +
          ∫ x in P..Q, Complex.normSq (S x)) := hcombine
    _ ≤ 2 *
        (lemma14UniversalPerronSegmentSafeWeightedCoefficient P Q h *
            (∫ t in -U..-T,
              lemma14SafeReciprocalSqWeight T t * Complex.normSq (F t)) +
          lemma14UniversalPerronSegmentSafeWeightedCoefficient P Q h *
            ∫ t in T..U,
              lemma14SafeReciprocalSqWeight T t * Complex.normSq (F t)) := by
      exact mul_le_mul_of_nonneg_left (add_le_add hneg hpos) (by norm_num)
    _ = 2 * lemma14UniversalPerronSegmentSafeWeightedCoefficient P Q h *
        ((∫ t in -U..-T,
            lemma14SafeReciprocalSqWeight T t * Complex.normSq (F t)) +
          ∫ t in T..U,
            lemma14SafeReciprocalSqWeight T t * Complex.normSq (F t)) := by
      ring

/-- Scale-explicit specialization of the symmetric source estimate to
`[X,2X]`.  This is the sharp weighted endpoint used by the scheduled
Lemma-14 join: a dyadic shell at height `V` gains its full `V⁻²` weight. -/
theorem integral_normSq_lemma14SymmetricPerronHighSegmentOn_le_scaled
    (F : ℝ → ℂ) (hF : Continuous F)
    {X H T U : ℝ} (hX : 0 < X) (hH : 0 < H) (hHX : H ≤ X)
    (hT : 0 < T) (hTU : T ≤ U) :
    (∫ x in X..2 * X,
        Complex.normSq
          (lemma14SymmetricPerronHighSegmentOn F x H T U)) ≤
      2 * (lemma14UniversalScaledHighConstant * X ^ 3 / H ^ 2) *
        ((∫ t in -U..-T,
            lemma14SafeReciprocalSqWeight T t * Complex.normSq (F t)) +
          ∫ t in T..U,
            lemma14SafeReciprocalSqWeight T t * Complex.normSq (F t)) := by
  let Eneg : ℝ := ∫ t in -U..-T,
    lemma14SafeReciprocalSqWeight T t * Complex.normSq (F t)
  let Epos : ℝ := ∫ t in T..U,
    lemma14SafeReciprocalSqWeight T t * Complex.normSq (F t)
  have hQ3P : 2 * X ≤ 3 * X := by linarith
  have hbase :=
    integral_normSq_lemma14SymmetricPerronHighSegmentOn_le_safeWeighted_universal
      F hF hX (by linarith) hQ3P hH hT hTU
  have hcoeff :=
    lemma14UniversalPerronSegmentSafeWeightedCoefficient_le hX hH hHX
  have hEc : Continuous (fun t ↦
      lemma14SafeReciprocalSqWeight T t * Complex.normSq (F t)) :=
    (continuous_lemma14SafeReciprocalSqWeight hT).mul
      (Complex.continuous_normSq.comp hF)
  have hEneg : 0 ≤ Eneg := by
    dsimp only [Eneg]
    apply intervalIntegral.integral_nonneg (neg_le_neg hTU)
    intro t ht
    exact mul_nonneg (sq_nonneg _) (Complex.normSq_nonneg _)
  have hEpos : 0 ≤ Epos := by
    dsimp only [Epos]
    apply intervalIntegral.integral_nonneg hTU
    intro t ht
    exact mul_nonneg (sq_nonneg _) (Complex.normSq_nonneg _)
  calc
    (∫ x in X..2 * X,
        Complex.normSq
          (lemma14SymmetricPerronHighSegmentOn F x H T U)) ≤
      2 * lemma14UniversalPerronSegmentSafeWeightedCoefficient X (2 * X) H *
        (Eneg + Epos) := by simpa only [Eneg, Epos] using hbase
    _ ≤ 2 * (lemma14UniversalScaledHighConstant * X ^ 3 / H ^ 2) *
        (Eneg + Epos) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hcoeff (by norm_num))
        (add_nonneg hEneg hEpos)
    _ = _ := by rfl

/-- Outer-height-independent scalar consequence of the scale-explicit
weighted estimate.  The entire high tail costs exactly one factor `T⁻¹`. -/
theorem integral_normSq_lemma14SymmetricPerronHighSegmentOn_le_scaled_inv
    (F : ℝ → ℂ) (hF : Continuous F) (hnorm : ∀ t, ‖F t‖ ≤ 1)
    {X H T U : ℝ} (hX : 0 < X) (hH : 0 < H) (hHX : H ≤ X)
    (hT : 0 < T) (hTU : T ≤ U) :
    (∫ x in X..2 * X,
        Complex.normSq
          (lemma14SymmetricPerronHighSegmentOn F x H T U)) ≤
      4 * lemma14UniversalScaledHighConstant * X ^ 3 / H ^ 2 * T⁻¹ := by
  let Eneg : ℝ := ∫ t in -U..-T,
    lemma14SafeReciprocalSqWeight T t * Complex.normSq (F t)
  let Epos : ℝ := ∫ t in T..U,
    lemma14SafeReciprocalSqWeight T t * Complex.normSq (F t)
  have hbase :=
    integral_normSq_lemma14SymmetricPerronHighSegmentOn_le_scaled
      F hF hX hH hHX hT hTU
  have hEneg : Eneg ≤ T⁻¹ := by
    exact intervalIntegral_safeReciprocalSqWeight_mul_normSq_neg_le_inv
      F hF hnorm hT hTU
  have hEpos : Epos ≤ T⁻¹ := by
    exact intervalIntegral_safeReciprocalSqWeight_mul_normSq_le_inv
      F hF hnorm hT hTU
  have hscale : 0 ≤
      2 * (lemma14UniversalScaledHighConstant * X ^ 3 / H ^ 2) := by
    exact mul_nonneg (by norm_num)
      (div_nonneg
        (mul_nonneg lemma14UniversalScaledHighConstant_nonneg
          (pow_nonneg hX.le 3))
        (pow_nonneg hH.le 2))
  calc
    (∫ x in X..2 * X,
        Complex.normSq
          (lemma14SymmetricPerronHighSegmentOn F x H T U)) ≤
      2 * (lemma14UniversalScaledHighConstant * X ^ 3 / H ^ 2) *
        (Eneg + Epos) := by simpa only [Eneg, Epos] using hbase
    _ ≤ 2 * (lemma14UniversalScaledHighConstant * X ^ 3 / H ^ 2) *
        (T⁻¹ + T⁻¹) := by
      exact mul_le_mul_of_nonneg_left (add_le_add hEneg hEpos) hscale
    _ = 4 * lemma14UniversalScaledHighConstant * X ^ 3 / H ^ 2 * T⁻¹ := by
      ring

/-- Dyadic one-bounded specialization of the scalarized universal source
estimate, ready for the corrected Perron limiting argument. -/
theorem integral_normSq_dyadicSymmetricPerronHighSegmentOn_le_scaled_inv
    (S : Finset ℕ) {f : ℕ → ℂ}
    (hf : ∀ n, 0 < n → ‖f n‖ ≤ 1) (Y : ℕ)
    {X H T U : ℝ} (hX : 0 < X) (hH : 0 < H) (hHX : H ≤ X)
    (hT : 0 < T) (hTU : T ≤ U) :
    (∫ x in X..2 * X,
        Complex.normSq
          (lemma14SymmetricPerronHighSegmentOn
            (dyadicVerticalDirichletPolynomial S f Y) x H T U)) ≤
      4 * lemma14UniversalScaledHighConstant * X ^ 3 / H ^ 2 * T⁻¹ := by
  exact integral_normSq_lemma14SymmetricPerronHighSegmentOn_le_scaled_inv
    (dyadicVerticalDirichletPolynomial S f Y)
    (continuous_dyadicVerticalDirichletPolynomial S f Y)
    (norm_dyadicVerticalDirichletPolynomial_le_one S hf Y)
    hX hH hHX hT hTU

/-- Completely outer-height-independent version for a one-bounded
vertical polynomial.  This is the finite-`U` estimate that can be passed
unchanged to the corrected Perron limit. -/
theorem integral_normSq_lemma14SymmetricPerronHighSegmentOn_le_inv
    (F : ℝ → ℂ) (hF : Continuous F) (hnorm : ∀ t, ‖F t‖ ≤ 1)
    {P Q h T U : ℝ} (hP : 0 < P) (hPQ : P ≤ Q) (hh : 0 < h)
    (hT : 0 < T) (hTU : T ≤ U)
    (delta L R : ℝ) (hdelta : 0 < delta)
    (hleft : L + 2 * delta ≤ -Real.log (Q + h))
    (hright : -Real.log P ≤ R - 2 * delta) :
    (∫ x in P..Q,
        Complex.normSq
          (lemma14SymmetricPerronHighSegmentOn F x h T U)) ≤
      4 * lemma14PerronSegmentSafeWeightedCoefficient
          P Q h delta L R hdelta * T⁻¹ := by
  let C : ℝ := lemma14PerronSegmentSafeWeightedCoefficient
    P Q h delta L R hdelta
  let Eneg : ℝ := ∫ t in -U..-T,
    lemma14SafeReciprocalSqWeight T t * Complex.normSq (F t)
  let Epos : ℝ := ∫ t in T..U,
    lemma14SafeReciprocalSqWeight T t * Complex.normSq (F t)
  have hC : 0 ≤ C :=
    lemma14PerronSegmentSafeWeightedCoefficient_nonneg
      hP hPQ hh hdelta
  have hEneg : Eneg ≤ T⁻¹ := by
    exact intervalIntegral_safeReciprocalSqWeight_mul_normSq_neg_le_inv
      F hF hnorm hT hTU
  have hEpos : Epos ≤ T⁻¹ := by
    exact intervalIntegral_safeReciprocalSqWeight_mul_normSq_le_inv
      F hF hnorm hT hTU
  have hbase :=
    integral_normSq_lemma14SymmetricPerronHighSegmentOn_le_safeWeighted
      F hF hP hPQ hh hT hTU delta L R hdelta hleft hright
  have hrewriteNeg :
      lemma14PerronSegmentSafeWeightedEnvelope
          F P Q h delta L R (-U) (-T) T hdelta = C * Eneg := by
    exact lemma14PerronSegmentSafeWeightedEnvelope_eq
      F P Q h delta L R (-U) (-T) T hdelta
  have hrewritePos :
      lemma14PerronSegmentSafeWeightedEnvelope
          F P Q h delta L R T U T hdelta = C * Epos := by
    exact lemma14PerronSegmentSafeWeightedEnvelope_eq
      F P Q h delta L R T U T hdelta
  calc
    (∫ x in P..Q,
        Complex.normSq
          (lemma14SymmetricPerronHighSegmentOn F x h T U)) ≤
      2 * (C * Eneg + C * Epos) := by
        simpa only [hrewriteNeg, hrewritePos] using hbase
    _ ≤ 2 * (C * T⁻¹ + C * T⁻¹) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact add_le_add
        (mul_le_mul_of_nonneg_left hEneg hC)
        (mul_le_mul_of_nonneg_left hEpos hC)
    _ = 4 * lemma14PerronSegmentSafeWeightedCoefficient
          P Q h delta L R hdelta * T⁻¹ := by
      dsimp only [C]
      ring

/-- Dyadic one-bounded specialization of the uniform high-frequency
estimate. -/
theorem integral_normSq_dyadicSymmetricPerronHighSegmentOn_le_inv
    (S : Finset ℕ) {f : ℕ → ℂ}
    (hf : ∀ n, 0 < n → ‖f n‖ ≤ 1) (Y : ℕ)
    {P Q h T U : ℝ} (hP : 0 < P) (hPQ : P ≤ Q) (hh : 0 < h)
    (hT : 0 < T) (hTU : T ≤ U)
    (delta L R : ℝ) (hdelta : 0 < delta)
    (hleft : L + 2 * delta ≤ -Real.log (Q + h))
    (hright : -Real.log P ≤ R - 2 * delta) :
    (∫ x in P..Q,
        Complex.normSq
          (lemma14SymmetricPerronHighSegmentOn
            (dyadicVerticalDirichletPolynomial S f Y) x h T U)) ≤
      4 * lemma14PerronSegmentSafeWeightedCoefficient
          P Q h delta L R hdelta * T⁻¹ := by
  exact integral_normSq_lemma14SymmetricPerronHighSegmentOn_le_inv
    (dyadicVerticalDirichletPolynomial S f Y)
    (continuous_dyadicVerticalDirichletPolynomial S f Y)
    (norm_dyadicVerticalDirichletPolynomial_le_one S hf Y)
    hP hPQ hh hT hTU delta L R hdelta hleft hright

end

end Erdos67
