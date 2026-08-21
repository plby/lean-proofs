import ErdosProblems.Erdos88.GaussianRemainderMoments

/-!
# Lower interval bounds for one Gaussian quadratic coordinate

This file formalizes the change-of-variables lower bound from KSSS Lemma 5.8.
The first public endpoint treats the branch with nonnegative quadratic
coefficient and retains an explicit positive constant for later convolution.
-/

open MeasureTheory ProbabilityTheory Set

namespace Erdos88.GaussianQuadratic

private lemma gaussianPDFReal_standard_lower_of_nonneg_le
    {T x : ℝ} (hT : 0 ≤ T) (hx : x ∈ Set.Icc 0 T) :
    gaussianPDFReal 0 1 T ≤ gaussianPDFReal 0 1 x := by
  have hsq : x ^ 2 ≤ T ^ 2 := by nlinarith [hx.1, hx.2]
  unfold gaussianPDFReal
  norm_num only [NNReal.coe_one, mul_one, sub_zero]
  gcongr

private lemma gaussianPDFReal_standard_lower_of_abs_le
    {T x : ℝ} (hT : 0 ≤ T) (hx : |x| ≤ T) :
    gaussianPDFReal 0 1 T ≤ gaussianPDFReal 0 1 x := by
  have hsq : x ^ 2 ≤ T ^ 2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg x) hT).mpr hx
  unfold gaussianPDFReal
  norm_num only [NNReal.coe_one, mul_one, sub_zero]
  gcongr

/-- Interval form of the nonnegative-quadratic branch of KSSS Lemma 5.8.
The explicit constant is deliberately retained for later convolution. -/
theorem map_centeredCoordinatePolynomial_measureReal_Icc_ge_of_nonneg
    {a lam A u eps : ℝ}
    (ha : 0 ≤ a) (hlam : 0 ≤ lam) (hA : 0 ≤ A)
    (hsigma : 0 < coordinateSigma a lam)
    (heps : 0 ≤ eps) (hepsSigma : eps ≤ coordinateSigma a lam)
    (hu : 0 ≤ u) (huA : u ≤ A * coordinateSigma a lam) :
    eps / ((2 * A + 7) * coordinateSigma a lam) *
        gaussianPDFReal 0 1 (A + 3) ≤
      (standardGaussian.map (centeredCoordinatePolynomial a lam)).real
        (Set.Icc u (u + eps)) := by
  by_cases hepsZero : eps = 0
  · subst eps
    simp only [zero_div, zero_mul]
    exact measureReal_nonneg
  have hepsPos : 0 < eps := lt_of_le_of_ne heps (Ne.symm hepsZero)
  let p := centeredCoordinatePolynomial a lam
  let sigma := coordinateSigma a lam
  let T := A + 3
  have hT : 0 ≤ T := by dsimp only [T]; linarith
  have hTpos : 0 < T := by dsimp only [T]; linarith
  have hsigmaSq : sigma ^ 2 = a ^ 2 + 2 * lam ^ 2 := by
    dsimp only [sigma, coordinateSigma, coordinateVariance]
    rw [Real.sq_sqrt]
    positivity
  have hsigmaUpper : sigma ≤ a + 2 * lam := by
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
    change sigma ^ 2 ≤ (a + 2 * lam) ^ 2
    rw [hsigmaSq]
    nlinarith [sq_nonneg (a + lam)]
  have hp0 : p 0 ≤ u := by
    dsimp only [p, centeredCoordinatePolynomial]
    nlinarith
  have hpT : u + eps ≤ p T := by
    have hpoly : (A + 1) * (a + 2 * lam) ≤ p T := by
      dsimp only [p, T, centeredCoordinatePolynomial]
      nlinarith [sq_nonneg A]
    have hscale : (A + 1) * sigma ≤ (A + 1) * (a + 2 * lam) :=
      mul_le_mul_of_nonneg_left hsigmaUpper (by linarith)
    have hut : u + eps ≤ (A + 1) * sigma := by
      dsimp only [sigma] at huA hepsSigma ⊢
      nlinarith
    exact hut.trans (hscale.trans hpoly)
  have hpcont : Continuous p := by
    dsimp only [p]
    exact continuous_centeredCoordinatePolynomial a lam
  have huMem : u ∈ Set.Icc (p 0) (p T) :=
    ⟨hp0, by linarith [hpT, heps]⟩
  obtain ⟨s, hsI, hsval⟩ :=
    intermediate_value_Icc hT hpcont.continuousOn huMem
  have huepsMem : u + eps ∈ Set.Icc (p 0) (p T) :=
    ⟨by linarith [hp0, heps], hpT⟩
  obtain ⟨t, htI, htval⟩ :=
    intermediate_value_Icc hT hpcont.continuousOn huepsMem
  have hmono : MonotoneOn p (Set.Icc 0 T) := by
    intro x hx y hy hxy
    rw [← sub_nonneg]
    have hsub := centeredCoordinatePolynomial_sub a lam x y
    change centeredCoordinatePolynomial a lam y -
        centeredCoordinatePolynomial a lam x ≥ 0
    rw [hsub]
    have hfac : 0 ≤ a + lam * (x + y) := by
      have : 0 ≤ x + y := by linarith [hx.1, hy.1]
      positivity
    nlinarith
  have hst : s ≤ t := by
    by_contra hnot
    have hle := hmono htI hsI (le_of_not_ge hnot)
    rw [hsval, htval] at hle
    linarith
  have hintervalSubset : Set.Icc s t ⊆ p ⁻¹' Set.Icc u (u + eps) := by
    intro x hx
    change p x ∈ Set.Icc u (u + eps)
    constructor
    · rw [← hsval]
      exact hmono hsI ⟨hsI.1.trans hx.1, hx.2.trans htI.2⟩ hx.1
    · rw [← htval]
      exact hmono ⟨hsI.1.trans hx.1, hx.2.trans htI.2⟩ htI hx.2
  have hlen : eps / ((2 * A + 7) * sigma) ≤ t - s := by
    have hdiff : eps = (t - s) * (a + lam * (s + t)) := by
      rw [show eps = p t - p s by rw [hsval, htval]; ring]
      exact centeredCoordinatePolynomial_sub a lam s t
    have hderivUpper : a + lam * (s + t) ≤ (2 * A + 7) * sigma := by
      have haSigma : a ≤ sigma := by
        simpa only [abs_of_nonneg ha] using abs_linear_le_coordinateSigma a lam
      have hlamSigma : lam ≤ sigma := by
        have hsqrt := sqrt_two_mul_abs_quadratic_le_coordinateSigma a lam
        have hsqrtOne : 1 ≤ Real.sqrt 2 := (Real.one_le_sqrt).2 (by norm_num)
        rw [abs_of_nonneg hlam] at hsqrt
        nlinarith [mul_le_mul_of_nonneg_right hsqrtOne hlam]
      have hstT : s + t ≤ 2 * T := by linarith [hsI.2, htI.2]
      have hlamst : lam * (s + t) ≤ lam * (2 * T) :=
        mul_le_mul_of_nonneg_left hstT hlam
      have h2T : 0 ≤ 2 * T := by positivity
      have hlamT : lam * (2 * T) ≤ sigma * (2 * T) :=
        mul_le_mul_of_nonneg_right hlamSigma h2T
      calc
        a + lam * (s + t) ≤ a + lam * (2 * T) := by
          simpa only [add_comm] using add_le_add_left hlamst a
        _ ≤ sigma + sigma * (2 * T) := add_le_add haSigma hlamT
        _ = (2 * A + 7) * sigma := by dsimp only [T]; ring
    have hcoefPos : 0 < (2 * A + 7) * sigma := by
      dsimp only [sigma]
      positivity
    apply (div_le_iff₀ hcoefPos).2
    have hlen0 : 0 ≤ t - s := sub_nonneg.mpr hst
    have hmul := mul_le_mul_of_nonneg_left hderivUpper hlen0
    nlinarith [hdiff, hmul]
  have hpdf : ∀ x ∈ Set.Icc s t,
      gaussianPDFReal 0 1 T ≤ gaussianPDFReal 0 1 x := by
    intro x hx
    exact gaussianPDFReal_standard_lower_of_nonneg_le hT
      ⟨hsI.1.trans hx.1, hx.2.trans htI.2⟩
  have hmeasureIcc : standardGaussian.real (Set.Icc s t) =
      ∫ x : ℝ in Set.Icc s t, gaussianPDFReal 0 1 x := by
    rw [measureReal_def]
    change (gaussianReal 0 1 (Set.Icc s t)).toReal = _
    have hone : (1 : NNReal) ≠ 0 := one_ne_zero
    rw [gaussianReal_apply_eq_integral 0 hone (Set.Icc s t)]
    rw [ENNReal.toReal_ofReal]
    exact setIntegral_nonneg measurableSet_Icc
      (fun x _ ↦ gaussianPDFReal_nonneg 0 1 x)
  have hmassIcc :
      (t - s) * gaussianPDFReal 0 1 T ≤ standardGaussian.real (Set.Icc s t) := by
    rw [hmeasureIcc]
    calc
      (t - s) * gaussianPDFReal 0 1 T =
          ∫ _x : ℝ in Set.Icc s t, gaussianPDFReal 0 1 T := by
        rw [setIntegral_const, smul_eq_mul, measureReal_def, Real.volume_Icc,
          ENNReal.toReal_ofReal (sub_nonneg.mpr hst)]
      _ ≤ ∫ x : ℝ in Set.Icc s t, gaussianPDFReal 0 1 x := by
        apply setIntegral_mono_on
        · exact integrableOn_const (μ := volume) (s := Set.Icc s t)
            (C := gaussianPDFReal 0 1 T)
            (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
        · exact (integrable_gaussianPDFReal 0 1).integrableOn
        · exact measurableSet_Icc
        · exact hpdf
  have hpreimageMass : standardGaussian.real (Set.Icc s t) ≤
      standardGaussian.real (p ⁻¹' Set.Icc u (u + eps)) :=
    measureReal_mono hintervalSubset
  have htarget :
      standardGaussian.real (p ⁻¹' Set.Icc u (u + eps)) =
        (standardGaussian.map p).real (Set.Icc u (u + eps)) := by
    rw [map_measureReal_apply hpcont.measurable measurableSet_Icc]
  rw [← htarget]
  calc
    eps / ((2 * A + 7) * coordinateSigma a lam) *
        gaussianPDFReal 0 1 (A + 3) =
        eps / ((2 * A + 7) * sigma) * gaussianPDFReal 0 1 T := rfl
    _ ≤ (t - s) * gaussianPDFReal 0 1 T :=
      mul_le_mul_of_nonneg_right hlen (gaussianPDFReal_nonneg 0 1 T)
    _ ≤ standardGaussian.real (Set.Icc s t) := hmassIcc
    _ ≤ standardGaussian.real (p ⁻¹' Set.Icc u (u + eps)) := hpreimageMass

lemma map_centeredCoordinatePolynomial_abs_linear (a lam : ℝ) :
    standardGaussian.map (centeredCoordinatePolynomial a lam) =
      standardGaussian.map (centeredCoordinatePolynomial |a| lam) := by
  by_cases ha : 0 ≤ a
  · rw [abs_of_nonneg ha]
  · have haNeg : a < 0 := lt_of_not_ge ha
    rw [abs_of_neg haNeg]
    have hfun : centeredCoordinatePolynomial (-a) lam =
        centeredCoordinatePolynomial a lam ∘ fun x : ℝ ↦ -x := by
      funext x
      simp only [Function.comp_apply, centeredCoordinatePolynomial]
      ring
    rw [hfun, ← Measure.map_map
      (continuous_centeredCoordinatePolynomial a lam).measurable measurable_neg]
    simpa only [neg_zero] using (congrArg
      (fun mu : Measure ℝ ↦ mu.map (centeredCoordinatePolynomial a lam))
      (gaussianReal_map_neg (μ := (0 : ℝ)) (v := (1 : NNReal)))).symm

lemma coordinateSigma_abs_linear (a lam : ℝ) :
    coordinateSigma |a| lam = coordinateSigma a lam := by
  unfold coordinateSigma coordinateVariance
  rw [sq_abs]

/-- The full nonnegative-quadratic branch of KSSS Lemma 5.8, with no sign
restriction on the linear coefficient. -/
theorem map_centeredCoordinatePolynomial_measureReal_Icc_ge_of_quadratic_nonneg
    {a lam A u eps : ℝ}
    (hlam : 0 ≤ lam) (hA : 0 ≤ A)
    (hsigma : 0 < coordinateSigma a lam)
    (heps : 0 ≤ eps) (hepsSigma : eps ≤ coordinateSigma a lam)
    (hu : 0 ≤ u) (huA : u ≤ A * coordinateSigma a lam) :
    eps / ((2 * A + 7) * coordinateSigma a lam) *
        gaussianPDFReal 0 1 (A + 3) ≤
      (standardGaussian.map (centeredCoordinatePolynomial a lam)).real
        (Set.Icc u (u + eps)) := by
  have h := map_centeredCoordinatePolynomial_measureReal_Icc_ge_of_nonneg
    (a := |a|) (lam := lam) (A := A) (u := u) (eps := eps)
    (abs_nonneg a) hlam hA
    (by simpa only [coordinateSigma_abs_linear] using hsigma)
    heps (by simpa only [coordinateSigma_abs_linear] using hepsSigma)
    hu (by simpa only [coordinateSigma_abs_linear] using huA)
  rw [coordinateSigma_abs_linear] at h
  rw [← map_centeredCoordinatePolynomial_abs_linear a lam] at h
  exact h

/-- The linearly dominated branch of KSSS Lemma 5.8.  The quadratic
coefficient may have either sign.  The explicit dominance hypothesis keeps
the polynomial monotone on the symmetric interval used in the proof. -/
theorem map_centeredCoordinatePolynomial_measureReal_Icc_ge_of_linear_dominates
    {a lam A u eps : ℝ}
    (hA : 0 ≤ A)
    (hsigma : 0 < coordinateSigma a lam)
    (hdom : 8 * (4 * (A + 1) + 1) * |lam| ≤ |a|)
    (heps : 0 ≤ eps) (hepsSigma : eps ≤ coordinateSigma a lam)
    (hu : 0 ≤ u) (huA : u ≤ A * coordinateSigma a lam) :
    eps / (2 * coordinateSigma a lam) *
        gaussianPDFReal 0 1 (4 * (A + 1) + 1) ≤
      (standardGaussian.map (centeredCoordinatePolynomial a lam)).real
        (Set.Icc u (u + eps)) := by
  rw [map_centeredCoordinatePolynomial_abs_linear a lam]
  rw [← coordinateSigma_abs_linear a lam] at hsigma hepsSigma huA ⊢
  let aa := |a|
  let p := centeredCoordinatePolynomial aa lam
  let sigma := coordinateSigma aa lam
  let T := 4 * (A + 1) + 1
  have haa : 0 ≤ aa := abs_nonneg a
  have hT : 0 ≤ T := by dsimp only [T]; linarith
  have hTone : 1 ≤ T := by dsimp only [T]; linarith
  have hTpos : 0 < T := lt_of_lt_of_le (by norm_num) hTone
  have hdom' : 8 * T * |lam| ≤ aa := by
    simpa only [aa, T] using hdom
  have haaPos : 0 < aa := by
    by_contra hnot
    have haaZero : aa = 0 := le_antisymm (le_of_not_gt hnot) haa
    have hprodNonneg : 0 ≤ 8 * T * |lam| := by positivity
    have hprodZero : T * |lam| = 0 := by nlinarith [hdom']
    have hlamAbs : |lam| = 0 :=
      (mul_eq_zero.mp hprodZero).resolve_left hTpos.ne'
    have hlamZero : lam = 0 := abs_eq_zero.mp hlamAbs
    have haaZero' : |a| = 0 := by simpa only [aa] using haaZero
    rw [haaZero', hlamZero] at hsigma
    norm_num [coordinateSigma, coordinateVariance] at hsigma
  have hsigmaSq : sigma ^ 2 = aa ^ 2 + 2 * lam ^ 2 := by
    dsimp only [sigma, coordinateSigma, coordinateVariance]
    rw [Real.sq_sqrt]
    positivity
  have hsigmaUpper : sigma ≤ aa + 2 * |lam| := by
    apply (sq_le_sq₀ (coordinateSigma_nonneg _ _) (by positivity)).mp
    rw [hsigmaSq]
    nlinarith [mul_nonneg haa (abs_nonneg lam), sq_nonneg |lam|, sq_abs lam]
  have htwoLam : 2 * |lam| ≤ aa / 4 := by
    have hscale : 2 * |lam| ≤ 2 * T * |lam| := by
      have hnonneg : 0 ≤ (2 : ℝ) * |lam| :=
        mul_nonneg (by norm_num) (abs_nonneg lam)
      have h := mul_le_mul_of_nonneg_left hTone hnonneg
      simpa only [one_mul, mul_one, mul_assoc, mul_comm, mul_left_comm] using h
    nlinarith [hdom']
  have hsigmaUpper' : sigma ≤ (5 / 4 : ℝ) * aa := by
    linarith
  have hquadT : |lam| * T ^ 2 ≤ aa * T / 8 := by
    have hmul := mul_le_mul_of_nonneg_right hdom' hT
    nlinarith
  have hTquad : 0 ≤ T ^ 2 - 1 := by nlinarith
  have htermUpper : lam * (T ^ 2 - 1) ≤ |lam| * T ^ 2 := by
    calc
      lam * (T ^ 2 - 1) ≤ |lam| * (T ^ 2 - 1) :=
        mul_le_mul_of_nonneg_right (le_abs_self lam) hTquad
      _ ≤ |lam| * T ^ 2 := by
        exact mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg lam)
  have htermLower : -|lam| * T ^ 2 ≤ lam * (T ^ 2 - 1) := by
    calc
      -|lam| * T ^ 2 ≤ -|lam| * (T ^ 2 - 1) := by
        nlinarith [abs_nonneg lam]
      _ ≤ lam * (T ^ 2 - 1) :=
        mul_le_mul_of_nonneg_right (neg_abs_le lam) hTquad
  have hpNeg : p (-T) ≤ 0 := by
    dsimp only [p, centeredCoordinatePolynomial]
    have hnegTerm : lam * ((-T) ^ 2 - 1) ≤ |lam| * T ^ 2 := by
      simpa only [neg_sq] using htermUpper
    nlinarith [hquadT]
  have hpPos : (A + 1) * sigma ≤ p T := by
    have hscale := mul_le_mul_of_nonneg_left hsigmaUpper'
      (by linarith : 0 ≤ A + 1)
    dsimp only [p, centeredCoordinatePolynomial]
    dsimp only [T] at hscale hquadT htermLower ⊢
    nlinarith [mul_nonneg haa (by linarith : 0 ≤ A + 1)]
  by_cases hepsZero : eps = 0
  · subst eps
    simp only [zero_div, zero_mul]
    exact measureReal_nonneg
  have hepsPos : 0 < eps := lt_of_le_of_ne heps (Ne.symm hepsZero)
  have hpcont : Continuous p := by
    dsimp only [p]
    exact continuous_centeredCoordinatePolynomial aa lam
  have hut : u + eps ≤ (A + 1) * sigma := by
    dsimp only [sigma] at huA hepsSigma ⊢
    nlinarith
  have huMem : u ∈ Set.Icc (p (-T)) (p T) :=
    ⟨hpNeg.trans hu, by linarith [hpPos, hut, heps]⟩
  obtain ⟨s, hsI, hsval⟩ :=
    intermediate_value_Icc (by linarith : -T ≤ T) hpcont.continuousOn huMem
  have huepsMem : u + eps ∈ Set.Icc (p (-T)) (p T) :=
    ⟨by linarith [hpNeg, hu, heps], hut.trans hpPos⟩
  obtain ⟨t, htI, htval⟩ :=
    intermediate_value_Icc (by linarith : -T ≤ T) hpcont.continuousOn huepsMem
  have hfactorNonneg : ∀ x ∈ Set.Icc (-T) T, ∀ y ∈ Set.Icc (-T) T,
      0 ≤ aa + lam * (x + y) := by
    intro x hx y hy
    have hsumAbs : |x + y| ≤ 2 * T := by
      rw [abs_le]
      constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]
    have hprodLower : -2 * T * |lam| ≤ lam * (x + y) := by
      calc
        -2 * T * |lam| = -(|lam| * (2 * T)) := by ring
        _ ≤ -(|lam| * |x + y|) := by
          exact neg_le_neg (mul_le_mul_of_nonneg_left hsumAbs (abs_nonneg lam))
        _ = -|lam * (x + y)| := by rw [abs_mul]
        _ ≤ lam * (x + y) := neg_abs_le _
    have hquarter : 2 * T * |lam| ≤ aa / 4 := by nlinarith [hdom']
    nlinarith
  have hmono : MonotoneOn p (Set.Icc (-T) T) := by
    intro x hx y hy hxy
    rw [← sub_nonneg]
    change centeredCoordinatePolynomial aa lam y -
        centeredCoordinatePolynomial aa lam x ≥ 0
    rw [centeredCoordinatePolynomial_sub]
    exact mul_nonneg (sub_nonneg.mpr hxy) (hfactorNonneg x hx y hy)
  have hst : s ≤ t := by
    by_contra hnot
    have hle := hmono htI hsI (le_of_not_ge hnot)
    rw [hsval, htval] at hle
    linarith
  have hintervalSubset : Set.Icc s t ⊆ p ⁻¹' Set.Icc u (u + eps) := by
    intro y hy
    change p y ∈ Set.Icc u (u + eps)
    constructor
    · rw [← hsval]
      exact hmono hsI ⟨hsI.1.trans hy.1, hy.2.trans htI.2⟩ hy.1
    · rw [← htval]
      exact hmono ⟨hsI.1.trans hy.1, hy.2.trans htI.2⟩ htI hy.2
  have hfactorUpper : aa + lam * (s + t) ≤ 2 * sigma := by
    have hsumAbs : |s + t| ≤ 2 * T := by
      rw [abs_le]
      constructor <;> linarith [hsI.1, hsI.2, htI.1, htI.2]
    have hprodUpper : lam * (s + t) ≤ 2 * T * |lam| := by
      calc
        lam * (s + t) ≤ |lam * (s + t)| := le_abs_self _
        _ = |lam| * |s + t| := abs_mul _ _
        _ ≤ |lam| * (2 * T) :=
          mul_le_mul_of_nonneg_left hsumAbs (abs_nonneg lam)
        _ = 2 * T * |lam| := by ring
    have hquarter : 2 * T * |lam| ≤ aa / 4 := by nlinarith [hdom']
    have haaSigma : aa ≤ sigma := by
      simpa only [aa, abs_abs, sigma] using abs_linear_le_coordinateSigma aa lam
    nlinarith
  have hdiff : eps = (t - s) * (aa + lam * (s + t)) := by
    rw [show eps = p t - p s by rw [hsval, htval]; ring]
    exact centeredCoordinatePolynomial_sub aa lam s t
  have hlen : eps / (2 * sigma) ≤ t - s := by
    have hcoefPos : 0 < 2 * sigma := by positivity
    apply (div_le_iff₀ hcoefPos).2
    have hlen0 : 0 ≤ t - s := sub_nonneg.mpr hst
    have hmul := mul_le_mul_of_nonneg_left hfactorUpper hlen0
    rw [hdiff]
    simpa only [mul_assoc, mul_comm, mul_left_comm] using hmul
  have hpdf : ∀ y ∈ Set.Icc s t,
      gaussianPDFReal 0 1 T ≤ gaussianPDFReal 0 1 y := by
    intro y hy
    apply gaussianPDFReal_standard_lower_of_abs_le hT
    rw [abs_le]
    exact ⟨hsI.1.trans hy.1, hy.2.trans htI.2⟩
  have hmeasureIcc : standardGaussian.real (Set.Icc s t) =
      ∫ y : ℝ in Set.Icc s t, gaussianPDFReal 0 1 y := by
    rw [measureReal_def]
    change (gaussianReal 0 1 (Set.Icc s t)).toReal = _
    have hone : (1 : NNReal) ≠ 0 := one_ne_zero
    rw [gaussianReal_apply_eq_integral 0 hone (Set.Icc s t)]
    rw [ENNReal.toReal_ofReal]
    exact setIntegral_nonneg measurableSet_Icc
      (fun y _ ↦ gaussianPDFReal_nonneg 0 1 y)
  have hmassIcc :
      (t - s) * gaussianPDFReal 0 1 T ≤ standardGaussian.real (Set.Icc s t) := by
    rw [hmeasureIcc]
    calc
      (t - s) * gaussianPDFReal 0 1 T =
          ∫ _y : ℝ in Set.Icc s t, gaussianPDFReal 0 1 T := by
        rw [setIntegral_const, smul_eq_mul, measureReal_def, Real.volume_Icc,
          ENNReal.toReal_ofReal (sub_nonneg.mpr hst)]
      _ ≤ ∫ y : ℝ in Set.Icc s t, gaussianPDFReal 0 1 y := by
        apply setIntegral_mono_on
        · exact integrableOn_const (μ := volume) (s := Set.Icc s t)
            (C := gaussianPDFReal 0 1 T)
            (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
        · exact (integrable_gaussianPDFReal 0 1).integrableOn
        · exact measurableSet_Icc
        · exact hpdf
  have hpreimageMass : standardGaussian.real (Set.Icc s t) ≤
      standardGaussian.real (p ⁻¹' Set.Icc u (u + eps)) :=
    measureReal_mono hintervalSubset
  have htarget : standardGaussian.real (p ⁻¹' Set.Icc u (u + eps)) =
      (standardGaussian.map p).real (Set.Icc u (u + eps)) := by
    rw [map_measureReal_apply hpcont.measurable measurableSet_Icc]
  rw [← htarget]
  calc
    eps / (2 * coordinateSigma aa lam) *
        gaussianPDFReal 0 1 (4 * (A + 1) + 1) =
        eps / (2 * sigma) * gaussianPDFReal 0 1 T := rfl
    _ ≤ (t - s) * gaussianPDFReal 0 1 T :=
      mul_le_mul_of_nonneg_right hlen (gaussianPDFReal_nonneg 0 1 T)
    _ ≤ standardGaussian.real (Set.Icc s t) := hmassIcc
    _ ≤ standardGaussian.real (p ⁻¹' Set.Icc u (u + eps)) := hpreimageMass

end Erdos88.GaussianQuadratic
