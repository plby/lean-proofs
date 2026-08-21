import ErdosProblems.Erdos88.GaussianLocalCLT
import ErdosProblems.Erdos88.Esseen

open scoped BigOperators FourierTransform RealInnerProductSpace
open MeasureTheory ProbabilityTheory Real Complex

namespace Erdos88.GaussianQuadratic

noncomputable def gaussianApproxKernel (c x u : ℝ) : ℝ :=
  c / √(2 * π) * Real.exp (-(c ^ 2 * (x - u) ^ 2) / 2)

lemma gaussianApproxKernel_eq_gaussianPDFReal
    (c x u : ℝ) (hc : 0 < c) :
    gaussianApproxKernel c x u =
      gaussianPDFReal x (NNReal.mk (c⁻¹ ^ 2) (sq_nonneg (c⁻¹))) u := by
  unfold gaussianApproxKernel gaussianPDFReal
  simp only [NNReal.coe_mk]
  rw [Real.sqrt_mul (by positivity : 0 ≤ 2 * π)]
  rw [Real.sqrt_sq_eq_abs, abs_inv, abs_of_pos hc]
  field_simp [hc.ne', Real.pi_ne_zero]
  ring

lemma gaussianApproxKernel_integrable (c x : ℝ) (hc : 0 < c) :
    Integrable (gaussianApproxKernel c x) := by
  rw [funext fun u ↦ gaussianApproxKernel_eq_gaussianPDFReal c x u hc]
  exact integrable_gaussianPDFReal _ _

lemma integral_gaussianApproxKernel (c x : ℝ) (hc : 0 < c) :
    ∫ u : ℝ, gaussianApproxKernel c x u = 1 := by
  rw [funext fun u ↦ gaussianApproxKernel_eq_gaussianPDFReal c x u hc]
  exact integral_gaussianPDFReal_eq_one x (by
    intro h
    have hv := congrArg (fun v : NNReal ↦ (v : ℝ)) h
    simp only [NNReal.coe_mk, NNReal.coe_zero] at hv
    exact (pow_ne_zero 2 (inv_ne_zero hc.ne')) hv)

noncomputable def gaussianSmoothedDensity
    (mu : Measure ℝ) (c u : ℝ) : ℝ :=
  ∫ x : ℝ, gaussianApproxKernel c x u ∂mu

lemma gaussianApproxKernel_nonneg (c x u : ℝ) (hc : 0 < c) :
    0 ≤ gaussianApproxKernel c x u := by
  unfold gaussianApproxKernel
  positivity

lemma gaussianApproxKernel_joint_integrable
    (mu : Measure ℝ) [IsFiniteMeasure mu] (c : ℝ) (hc : 0 < c) :
    Integrable (Function.uncurry (fun x u : ℝ ↦ gaussianApproxKernel c x u))
      (mu.prod volume) := by
  apply (integrable_prod_iff (Continuous.aestronglyMeasurable (by
    dsimp only [Function.uncurry_apply_pair, gaussianApproxKernel]
    fun_prop))).2
  constructor
  · exact Filter.Eventually.of_forall fun x ↦ gaussianApproxKernel_integrable c x hc
  · have hconst : Integrable (fun _ : ℝ ↦ (1 : ℝ)) mu := integrable_const _
    convert hconst using 1
    funext x
    change (∫ y : ℝ, ‖gaussianApproxKernel c x y‖) = 1
    rw [show (fun u : ℝ ↦ ‖gaussianApproxKernel c x u‖) =
        gaussianApproxKernel c x by
      funext u
      rw [Real.norm_eq_abs, abs_of_nonneg (gaussianApproxKernel_nonneg c x u hc)]]
    exact integral_gaussianApproxKernel c x hc

lemma gaussianSmoothedDensity_integrable
    (mu : Measure ℝ) [IsFiniteMeasure mu] (c : ℝ) (hc : 0 < c) :
    Integrable (gaussianSmoothedDensity mu c) := by
  have hswap := (gaussianApproxKernel_joint_integrable mu c hc).swap.integral_prod_left
  change Integrable (fun u : ℝ ↦ ∫ x : ℝ, gaussianApproxKernel c x u ∂mu) at hswap
  exact hswap

lemma gaussianSmoothedDensity_nonneg
    (mu : Measure ℝ) (c u : ℝ) (hc : 0 < c) :
    0 ≤ gaussianSmoothedDensity mu c u := by
  apply integral_nonneg
  exact fun x ↦ gaussianApproxKernel_nonneg c x u hc

lemma integral_gaussianSmoothedDensity
    (mu : Measure ℝ) [IsFiniteMeasure mu] (c : ℝ) (hc : 0 < c) :
    ∫ u : ℝ, gaussianSmoothedDensity mu c u = mu.real Set.univ := by
  unfold gaussianSmoothedDensity
  rw [← integral_integral_swap (gaussianApproxKernel_joint_integrable mu c hc)]
  simp_rw [integral_gaussianApproxKernel c _ hc]
  simp

lemma gaussianSmoothedDensity_eq_dampedInverse
    (mu : Measure ℝ) [IsFiniteMeasure mu] (c u : ℝ) (hc : 0 < c) :
    ((gaussianSmoothedDensity mu c u : ℝ) : ℂ) =
      (((2 * π : ℝ) : ℂ))⁻¹ *
        (∫ t : ℝ, charFun mu t *
          cexp (-(((t * u : ℝ) : ℂ) * I)) *
          cexp (((-(t ^ 2 / (2 * c ^ 2)) : ℝ) : ℂ))) := by
  rw [gaussianSmoothedDensity]
  rw [gaussianDampedCharFun_inverse_eq_kernelIntegral mu c u hc]
  rw [integral_complex_ofReal]
  rfl

lemma tendsto_gaussianSmoothedDensity
    (mu : Measure ℝ) [IsFiniteMeasure mu]
    (hchar : Integrable (charFun mu)) (u : ℝ) :
    Filter.Tendsto
      (fun n : ℕ ↦ gaussianSmoothedDensity mu ((n : ℝ) + 1) u)
      Filter.atTop
      (nhds (inverseFourierDensityCandidate (charFun mu) u)) := by
  let F : ℕ → ℝ → ℂ := fun n t ↦
    charFun mu t * cexp (-(((t * u : ℝ) : ℂ) * I)) *
      cexp (((-(t ^ 2 / (2 * ((n : ℝ) + 1) ^ 2)) : ℝ) : ℂ))
  let f : ℝ → ℂ := fun t ↦
    charFun mu t * cexp (-(((t * u : ℝ) : ℂ) * I))
  have hFmeas (n : ℕ) : AEStronglyMeasurable (F n) := by
    apply AEStronglyMeasurable.mul
    · exact hchar.aestronglyMeasurable.mul (by fun_prop)
    · apply Continuous.aestronglyMeasurable
      fun_prop
  have hbound (n : ℕ) : ∀ᵐ t : ℝ, ‖F n t‖ ≤ ‖charFun mu t‖ :=
    Filter.Eventually.of_forall fun t ↦ by
      dsimp only [F]
      rw [norm_mul, norm_mul, Complex.norm_exp, Complex.norm_exp]
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.I_re,
        Complex.ofReal_im, Complex.I_im, mul_zero, sub_zero,
        neg_re, neg_zero, Real.exp_zero, mul_one]
      have hnpos : -(t ^ 2 / (2 * ((n : ℝ) + 1) ^ 2)) ≤ 0 := by
        exact neg_nonpos.mpr (div_nonneg (sq_nonneg t) (by positivity))
      calc
        ‖charFun mu t‖ * Real.exp (-(t ^ 2 / (2 * ((n : ℝ) + 1) ^ 2))) ≤
            ‖charFun mu t‖ * 1 := by
          gcongr
          exact Real.exp_le_one_iff.mpr hnpos
        _ = ‖charFun mu t‖ := mul_one _
  have hlim : ∀ᵐ t : ℝ,
      Filter.Tendsto (fun n ↦ F n t) Filter.atTop (nhds (f t)) :=
    Filter.Eventually.of_forall fun t ↦ by
      have hdampR := tendsto_gaussianDamping t
      have hdampC := Complex.continuous_ofReal.continuousAt.tendsto.comp hdampR
      have hdamp : Filter.Tendsto
          (fun n : ℕ ↦
            cexp (((-(t ^ 2 / (2 * ((n : ℝ) + 1) ^ 2)) : ℝ) : ℂ)))
          Filter.atTop (nhds 1) := by
        change Filter.Tendsto
          (fun n : ℕ ↦
            ((Real.exp (-(t ^ 2 / (2 * ((n : ℝ) + 1) ^ 2))) : ℝ) : ℂ))
          Filter.atTop (nhds ((1 : ℝ) : ℂ)) at hdampC
        simpa only [Complex.ofReal_exp, Complex.ofReal_one] using hdampC
      have hconst : Filter.Tendsto
          (fun _ : ℕ ↦ charFun mu t * cexp (-(((t * u : ℝ) : ℂ) * I)))
          Filter.atTop
          (nhds (charFun mu t * cexp (-(((t * u : ℝ) : ℂ) * I)))) :=
        tendsto_const_nhds
      simpa only [F, f, mul_one] using hconst.mul hdamp
  have hint : Filter.Tendsto (fun n ↦ ∫ t : ℝ, F n t)
      Filter.atTop (nhds (∫ t : ℝ, f t)) :=
    tendsto_integral_of_dominated_convergence
      (fun t ↦ ‖charFun mu t‖) hFmeas hchar.norm hbound hlim
  have hz : Filter.Tendsto
      (fun n ↦ (((2 * π : ℝ) : ℂ))⁻¹ * ∫ t : ℝ, F n t)
      Filter.atTop
      (nhds ((((2 * π : ℝ) : ℂ))⁻¹ * ∫ t : ℝ, f t)) :=
    tendsto_const_nhds.mul hint
  have hre : Filter.Tendsto
      (fun n ↦ ((((2 * π : ℝ) : ℂ))⁻¹ * ∫ t : ℝ, F n t).re)
      Filter.atTop
      (nhds (inverseFourierDensityCandidate (charFun mu) u)) := by
    have h := Complex.continuous_re.continuousAt.tendsto.comp hz
    change Filter.Tendsto
      (fun n ↦ ((((2 * π : ℝ) : ℂ))⁻¹ * ∫ t : ℝ, F n t).re)
      Filter.atTop
      (nhds (((((2 * π : ℝ) : ℂ))⁻¹ * ∫ t : ℝ, f t).re)) at h
    simpa only [inverseFourierDensityCandidate, f] using h
  apply hre.congr'
  exact Filter.Eventually.of_forall fun n ↦ by
    have hnpos : 0 < (n : ℝ) + 1 := by positivity
    have hrel := congrArg Complex.re
      (gaussianSmoothedDensity_eq_dampedInverse mu ((n : ℝ) + 1) u hnpos)
    dsimp only [F]
    simpa only [Complex.ofReal_re] using hrel.symm

theorem inverseFourierDensityCandidate_charFun_integrable
    (mu : Measure ℝ) [IsFiniteMeasure mu]
    (hchar : Integrable (charFun mu)) :
    Integrable (inverseFourierDensityCandidate (charFun mu)) := by
  let G : ℕ → ℝ → ℝ := fun n u ↦
    gaussianSmoothedDensity mu ((n : ℝ) + 1) u
  have hGlim : ∀ᵐ u : ℝ,
      Filter.Tendsto (fun n ↦ G n u) Filter.atTop
        (nhds (inverseFourierDensityCandidate (charFun mu) u)) :=
    Filter.Eventually.of_forall fun u ↦ tendsto_gaussianSmoothedDensity mu hchar u
  have hGint (n : ℕ) : Integrable (G n) := by
    exact gaussianSmoothedDensity_integrable mu ((n : ℝ) + 1) (by positivity)
  apply integrable_of_tendsto hGlim (fun n ↦ (hGint n).aestronglyMeasurable)
  have hlin (n : ℕ) :
      ∫⁻ u : ℝ, ‖G n u‖ₑ = ENNReal.ofReal (mu.real Set.univ) := by
    rw [← ofReal_integral_norm_eq_lintegral_enorm (hGint n)]
    have hnonneg : ∀ u, 0 ≤ G n u := fun u ↦
      gaussianSmoothedDensity_nonneg mu ((n : ℝ) + 1) u (by positivity)
    rw [show (fun u : ℝ ↦ ‖G n u‖) = G n by
      funext u
      rw [Real.norm_eq_abs, abs_of_nonneg (hnonneg u)]]
    rw [integral_gaussianSmoothedDensity mu ((n : ℝ) + 1) (by positivity)]
  simp_rw [hlin]
  simp

lemma inverseFourierDensityCandidate_coe_eq_fourier
    {phi : ℝ → ℂ}
    (hInv : HasInverseFourierDensity (inverseFourierDensityCandidate phi) phi)
    (u : ℝ) :
    ((inverseFourierDensityCandidate phi u : ℝ) : ℂ) =
      (((2 * π : ℝ) : ℂ))⁻¹ * 𝓕 phi (u / (2 * π)) := by
  rw [hInv u, Real.fourier_real_eq_integral_exp_smul]
  congr 1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun t ↦ by
    change phi t * Complex.exp (-(((t * u : ℝ) : ℂ) * Complex.I)) =
      Complex.exp (((-2 * π * t * (u / (2 * π)) : ℝ) : ℂ) * Complex.I) • phi t
    rw [smul_eq_mul, mul_comm]
    congr 1
    congr 1
    push_cast
    field_simp [Real.pi_ne_zero]

lemma fourier_eq_scaled_inverseFourierDensityCandidate
    {phi : ℝ → ℂ}
    (hInv : HasInverseFourierDensity (inverseFourierDensityCandidate phi) phi)
    (w : ℝ) :
    𝓕 phi w =
      (((2 * π : ℝ) : ℂ)) *
        ((inverseFourierDensityCandidate phi (2 * π * w) : ℝ) : ℂ) := by
  have h := inverseFourierDensityCandidate_coe_eq_fourier hInv (2 * π * w)
  rw [show 2 * π * w / (2 * π) = w by field_simp [Real.pi_ne_zero]] at h
  rw [h]
  field_simp [Real.pi_ne_zero]

lemma fourier_integrable_of_inverseFourierDensityCandidate_integrable
    {phi : ℝ → ℂ}
    (hInv : HasInverseFourierDensity (inverseFourierDensityCandidate phi) phi)
    (hp : Integrable (inverseFourierDensityCandidate phi)) :
    Integrable (𝓕 phi) := by
  have hpC : Integrable (fun x : ℝ ↦
      ((inverseFourierDensityCandidate phi x : ℝ) : ℂ)) := hp.ofReal
  have hscale := hpC.comp_mul_left' (R := 2 * π)
    (mul_ne_zero (by norm_num) Real.pi_ne_zero)
  have hmul := hscale.const_mul (((2 * π : ℝ) : ℂ))
  apply hmul.congr
  exact Filter.Eventually.of_forall fun w ↦ by
    exact (fourier_eq_scaled_inverseFourierDensityCandidate hInv w).symm

theorem measure_eq_withDensity_inverseFourierDensityCandidate
    (mu : Measure ℝ) [IsFiniteMeasure mu]
    (hchar : Integrable (charFun mu)) :
    mu = volume.withDensity (fun x ↦
      ENNReal.ofReal (inverseFourierDensityCandidate (charFun mu) x)) := by
  let p : ℝ → ℝ := inverseFourierDensityCandidate (charFun mu)
  have hInv : HasInverseFourierDensity p (charFun mu) := by
    apply inverseFourierDensityCandidate_hasInverse
    intro t
    exact charFun_neg (μ := mu) (t := t)
  have hp : Integrable p := inverseFourierDensityCandidate_charFun_integrable mu hchar
  have hpnonneg : ∀ x, 0 ≤ p x :=
    inverseFourierDensityCandidate_charFun_nonneg mu hchar
  have hpcontinuous : Continuous p :=
    continuous_inverseFourierDensityCandidate hchar
  let nu : Measure ℝ := volume.withDensity (fun x ↦ ENNReal.ofReal (p x))
  letI : IsFiniteMeasure nu := by
    dsimp only [nu]
    exact isFiniteMeasure_withDensity_ofReal hp.hasFiniteIntegral
  apply Measure.ext_of_charFun
  change charFun mu = charFun nu
  funext t
  rw [charFun_apply_real, charFun_apply_real]
  rw [show (∫ x : ℝ, cexp ((t : ℂ) * (x : ℂ) * I) ∂nu) =
      ∫ x : ℝ, (p x : ℂ) * cexp ((t : ℂ) * (x : ℂ) * I) by
    dsimp only [nu]
    rw [integral_withDensity_eq_integral_toReal_smul]
    · apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x ↦ by
        change (ENNReal.ofReal (p x)).toReal •
          cexp ((t : ℂ) * (x : ℂ) * I) =
            (p x : ℂ) * cexp ((t : ℂ) * (x : ℂ) * I)
        rw [ENNReal.toReal_ofReal (hpnonneg x), Complex.real_smul]
    · exact ENNReal.measurable_ofReal.comp hpcontinuous.measurable
    · exact Filter.Eventually.of_forall fun x ↦ ENNReal.ofReal_lt_top]
  have hFourier : Integrable (𝓕 (charFun mu)) :=
    fourier_integrable_of_inverseFourierDensityCandidate_integrable hInv hp
  have hInversion : 𝓕⁻ (𝓕 (charFun mu)) t = charFun mu t :=
    hchar.fourierInv_fourier_eq hFourier (continuous_charFun.continuousAt)
  rw [← charFun_apply_real]
  rw [← hInversion, fourierInv_eq]
  symm
  have hscale := Measure.integral_comp_mul_left
    (fun x : ℝ ↦ cexp ((t : ℂ) * (x : ℂ) * I) * (p x : ℂ)) (2 * π)
  have h2pi : 0 < 2 * π := by positivity
  rw [abs_of_pos (inv_pos.mpr h2pi)] at hscale
  calc
    ∫ x : ℝ, (p x : ℂ) * cexp ((t : ℂ) * (x : ℂ) * I) =
        (2 * π : ℂ) * ∫ w : ℝ,
          cexp ((t : ℂ) * ((2 * π * w : ℝ) : ℂ) * I) * (p (2 * π * w) : ℂ) := by
      rw [show (fun x : ℝ ↦ (p x : ℂ) * cexp ((t : ℂ) * (x : ℂ) * I)) =
          fun x : ℝ ↦ cexp ((t : ℂ) * (x : ℂ) * I) * (p x : ℂ) by
        funext x
        ring]
      rw [hscale]
      rw [real_smul]
      push_cast
      field_simp [Real.pi_ne_zero]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x ↦ by
        congr 2
        ring
    _ = _ := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun w ↦ by
        change (2 * π : ℂ) *
            (cexp ((t : ℂ) * ((2 * π * w : ℝ) : ℂ) * I) *
              (p (2 * π * w) : ℂ)) =
          Real.fourierChar ⟪w, t⟫ • 𝓕 (charFun mu) w
        rw [fourier_eq_scaled_inverseFourierDensityCandidate hInv w]
        dsimp only [p]
        rw [Circle.smul_def, Real.fourierChar_apply]
        have hphase :
            cexp ((t : ℂ) * ((2 * π * w : ℝ) : ℂ) * I) =
              cexp (((2 * π * ⟪w, t⟫ : ℝ) : ℂ) * I) := by
          congr 1
          simp only [RCLike.inner_apply, conj_trivial]
          push_cast
          ring
        rw [hphase]
        push_cast
        ring

theorem hasContinuousDensity_inverseFourierDensityCandidate
    (mu : Measure ℝ) [IsFiniteMeasure mu]
    (hchar : Integrable (charFun mu)) :
    Esseen.HasContinuousDensity mu
      (inverseFourierDensityCandidate (charFun mu)) := by
  let p : ℝ → ℝ := inverseFourierDensityCandidate (charFun mu)
  have hp : Integrable p := inverseFourierDensityCandidate_charFun_integrable mu hchar
  have hpnonneg : ∀ x, 0 ≤ p x :=
    inverseFourierDensityCandidate_charFun_nonneg mu hchar
  have hpcontinuous : Continuous p :=
    continuous_inverseFourierDensityCandidate hchar
  refine ⟨hpcontinuous, hpnonneg, ?_⟩
  intro eps x heps
  rw [Esseen.smallBall]
  have hle : x - eps ≤ x + eps := by linarith
  calc
    mu.real (Set.Icc (x - eps) (x + eps)) =
        (volume.withDensity fun y ↦ ENNReal.ofReal (p y)).real
          (Set.Icc (x - eps) (x + eps)) := by
      rw [measure_eq_withDensity_inverseFourierDensityCandidate mu hchar]
    (volume.withDensity fun y ↦ ENNReal.ofReal (p y)).real
        (Set.Icc (x - eps) (x + eps)) =
        ∫ y in Set.Icc (x - eps) (x + eps), p y := by
      rw [measureReal_def, withDensity_apply _ measurableSet_Icc]
      rw [← ofReal_integral_eq_lintegral_ofReal hp.integrableOn
        (Filter.Eventually.of_forall hpnonneg)]
      rw [ENNReal.toReal_ofReal]
      exact integral_nonneg hpnonneg
    _ = ∫ y in Set.Ioc (x - eps) (x + eps), p y :=
      integral_Icc_eq_integral_Ioc
    _ = ∫ y in (x - eps)..(x + eps), p y := by
      rw [intervalIntegral.integral_of_le hle]

/-! ## The no-influential-coordinate Gaussian small-ball branch -/

/-- A convenient absolute integral bound for the universal Hölder envelope.
The exact value is smaller; `2π` gives the normalized density bound `1`. -/
lemma holderEnvelope_integral_le_two_pi :
    (∫ t : ℝ, holderEnvelope t) ≤ 2 * Real.pi := by
  have hmajor : ∀ t : ℝ,
      holderEnvelope t ≤ 2 * (1 + t ^ 2)⁻¹ := by
    intro t
    unfold holderEnvelope
    have hleft : 0 < 1 + t ^ 2 / 2 := by positivity
    have hright : 0 < 1 + t ^ 2 := by positivity
    field_simp [ne_of_gt hleft, ne_of_gt hright]
    nlinarith [sq_nonneg t]
  have hmajorInt : Integrable (fun t : ℝ ↦ 2 * (1 + t ^ 2)⁻¹) :=
    integrable_inv_one_add_sq.const_mul 2
  calc
    (∫ t : ℝ, holderEnvelope t) ≤
        ∫ t : ℝ, 2 * (1 + t ^ 2)⁻¹ := by
      apply integral_mono holderEnvelope_integrable hmajorInt hmajor
    _ = 2 * Real.pi := by
      rw [integral_const_mul, integral_univ_inv_one_add_sq]

/-- In the no-influential-coordinate branch of KSSS Lemma 5.5, the exact
centered characteristic product is globally integrable. -/
theorem diagonalCenteredCharProduct_integrable_of_small_coordinates
    {ι : Type*} [Fintype ι]
    (a lam : ι → ℝ) (hsum : totalVariance a lam = 1)
    (hsmall : ∀ i, coordinateVariance (a i) (lam i) ≤ 1 / 4) :
    Integrable (diagonalCenteredCharProduct a lam) := by
  apply holderEnvelope_integrable.mono
  · exact (continuous_diagonalCenteredCharProduct a lam).aestronglyMeasurable
  · filter_upwards [] with t
    rw [norm_diagonalCenteredCharProduct, Real.norm_eq_abs,
      abs_of_nonneg (holderEnvelope_nonneg t)]
    exact diagonalCharModulus_le_holderEnvelope a lam hsum hsmall t

/-- The inverse-Fourier density in the no-influential-coordinate branch is
bounded by one.  This is the first complete case of the uniform Gaussian
small-ball theorem (KSSS Theorem 1.6). -/
lemma abs_inverseFourierDensityCandidate_le_one_of_small_coordinates
    {ι : Type*} [Fintype ι]
    (a lam : ι → ℝ) (hsum : totalVariance a lam = 1)
    (hsmall : ∀ i, coordinateVariance (a i) (lam i) ≤ 1 / 4)
    (u : ℝ) :
    |inverseFourierDensityCandidate (diagonalCenteredCharProduct a lam) u| ≤ 1 := by
  let phi := diagonalCenteredCharProduct a lam
  let p := inverseFourierDensityCandidate phi
  have hchar : Integrable phi :=
    diagonalCenteredCharProduct_integrable_of_small_coordinates
      a lam hsum hsmall
  have hInv : HasInverseFourierDensity p phi :=
    inverseFourierDensityCandidate_hasInverse
      (diagonalCenteredCharProduct_neg a lam)
  have hphase (t : ℝ) :
      ‖phi t * cexp (-(((t * u : ℝ) : ℂ) * I))‖ = ‖phi t‖ := by
    rw [norm_mul, Complex.norm_exp]
    simp
  have hnormInt : (∫ t : ℝ, ‖phi t‖) ≤ 2 * Real.pi := by
    calc
      (∫ t : ℝ, ‖phi t‖) ≤ ∫ t : ℝ, holderEnvelope t := by
        apply integral_mono hchar.norm holderEnvelope_integrable
        intro t
        dsimp only [phi]
        rw [norm_diagonalCenteredCharProduct]
        exact diagonalCharModulus_le_holderEnvelope a lam hsum hsmall t
      _ ≤ 2 * Real.pi := holderEnvelope_integral_le_two_pi
  rw [← Real.norm_eq_abs, ← Complex.norm_real, hInv u, norm_mul, norm_inv,
    Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (mul_pos (by norm_num) Real.pi_pos)]
  calc
    (2 * Real.pi)⁻¹ *
        ‖∫ t : ℝ, phi t * cexp (-(((t * u : ℝ) : ℂ) * I))‖ ≤
        (2 * Real.pi)⁻¹ *
          ∫ t : ℝ, ‖phi t * cexp (-(((t * u : ℝ) : ℂ) * I))‖ := by
      gcongr
      exact norm_integral_le_integral_norm _
    _ = (2 * Real.pi)⁻¹ * ∫ t : ℝ, ‖phi t‖ := by
      congr 1
      apply integral_congr_ae
      exact Filter.Eventually.of_forall hphase
    _ ≤ (2 * Real.pi)⁻¹ * (2 * Real.pi) := by gcongr
    _ = 1 := by field_simp [Real.pi_ne_zero]

/-- Normalized uniform small-ball estimate for a diagonal Gaussian quadratic
form with no influential coordinate. -/
theorem smallBall_diagonalCenteredLaw_le_two_mul_of_small_coordinates
    {ι : Type*} [Fintype ι]
    (a lam : ι → ℝ) (hsum : totalVariance a lam = 1)
    (hsmall : ∀ i, coordinateVariance (a i) (lam i) ≤ 1 / 4)
    {eps : ℝ} (heps : 0 ≤ eps) (x : ℝ) :
    Esseen.smallBall (diagonalCenteredLaw a lam) eps x ≤ 2 * eps := by
  letI : IsProbabilityMeasure (diagonalCenteredLaw a lam) :=
    diagonalCenteredLaw_isProbabilityMeasure a lam
  let phi := diagonalCenteredCharProduct a lam
  let p := inverseFourierDensityCandidate (charFun (diagonalCenteredLaw a lam))
  have hchar : Integrable phi :=
    diagonalCenteredCharProduct_integrable_of_small_coordinates
      a lam hsum hsmall
  have hlawChar : Integrable (charFun (diagonalCenteredLaw a lam)) := by
    rw [charFun_diagonalCenteredLaw]
    exact hchar
  have hdens : Esseen.HasContinuousDensity
      (diagonalCenteredLaw a lam) p := by
    exact hasContinuousDensity_inverseFourierDensityCandidate
      (diagonalCenteredLaw a lam) hlawChar
  rw [hdens.smallBall_eq_integral eps x heps]
  calc
    (∫ y in (x - eps)..(x + eps), p y) ≤
        ∫ _y in (x - eps)..(x + eps), (1 : ℝ) := by
      apply intervalIntegral.integral_mono_on (by linarith)
        (hdens.continuous.intervalIntegrable _ _) intervalIntegrable_const
      intro y hy
      exact (le_abs_self (p y)).trans (by
        dsimp only [p]
        rw [charFun_diagonalCenteredLaw]
        exact abs_inverseFourierDensityCandidate_le_one_of_small_coordinates
          a lam hsum hsmall y)
    _ = 2 * eps := by
      rw [intervalIntegral.integral_const]
      simp only [smul_eq_mul]
      ring

/-- Under four disjoint positive-mass spectral blocks, the centered diagonal
quadratic Gaussian law has the continuous inverse-Fourier density used in
Claim 12.1. -/
theorem hasContinuousDensity_diagonal_of_four_le_spectralBlocks
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (a lam : ι → ℝ) (B : κ → Finset ι)
    (hcard : 4 ≤ Fintype.card κ)
    (hdisj : Set.PairwiseDisjoint
      (↑(Finset.univ : Finset κ) : Set κ) B)
    {s : ℝ} (hs : 0 < s)
    (hblock : ∀ j, s ≤ ∑ i ∈ B j, (lam i) ^ 2) :
    Esseen.HasContinuousDensity
      (diagonalCenteredLaw a lam)
      (inverseFourierDensityCandidate
        (diagonalCenteredCharProduct a lam)) := by
  letI : IsProbabilityMeasure (diagonalCenteredLaw a lam) :=
    diagonalCenteredLaw_isProbabilityMeasure a lam
  have hdiag : Integrable (diagonalCenteredCharProduct a lam) :=
    diagonalCenteredCharProduct_integrable_of_four_le_spectralBlocks
      a lam B hcard hdisj hs hblock
  have hlaw : Integrable (charFun (diagonalCenteredLaw a lam)) := by
    rw [charFun_diagonalCenteredLaw a lam]
    exact hdiag
  have h := hasContinuousDensity_inverseFourierDensityCandidate
    (diagonalCenteredLaw a lam) hlaw
  simpa only [charFun_diagonalCenteredLaw] using h

/-- The probability-theoretic form of the Gaussian comparison in Claim 12.1:
the centered diagonal law has an actual continuous density, and that density
obeys the explicit Petrov/spectral-block comparison with the standard normal
density. -/
theorem exists_continuousDensity_diagonal_comparison_of_four_le_spectralBlocks
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (a lam : ι → ℝ) (B : κ → Finset ι)
    (hcard : 4 ≤ Fintype.card κ)
    (hdisj : Set.PairwiseDisjoint
      (↑(Finset.univ : Finset κ) : Set κ) B)
    {s : ℝ}
    (hsum : totalVariance a lam = 1)
    (hs : 0 < s)
    (hblock : ∀ j, s ≤ ∑ i ∈ B j, (lam i) ^ 2) :
    ∃ p : ℝ → ℝ,
      Esseen.HasContinuousDensity (diagonalCenteredLaw a lam) p ∧
        ∀ u : ℝ,
          |p u - standardNormalDensity u| ≤
            (2 * π)⁻¹ *
              (1280 / lyapunovGamma a lam +
                16 / (s * lyapunovGamma a lam)) := by
  refine ⟨inverseFourierDensityCandidate
      (diagonalCenteredCharProduct a lam), ?_, ?_⟩
  · exact hasContinuousDensity_diagonal_of_four_le_spectralBlocks
      a lam B hcard hdisj hs hblock
  · exact inverseFourierDensityCandidate_comparison_of_four_le_spectralBlocks
      a lam B hcard hdisj hsum hs hblock

lemma integral_fourSpectralEnvelope {s : ℝ} (hs : 0 < s) :
    (∫ t : ℝ, fourSpectralEnvelope s t) = Real.pi / (2 * Real.sqrt s) := by
  let R : ℝ := (2 * Real.sqrt s)⁻¹
  let g : ℝ → ℝ := fun x ↦ (1 + x ^ 2)⁻¹
  have hR : 0 < R := by dsimp only [R]; positivity
  have hfun : fourSpectralEnvelope s = fun t ↦ g (t / R) := by
    funext t
    unfold fourSpectralEnvelope
    dsimp only [g, R]
    field_simp [(Real.sqrt_pos.2 hs).ne']
    rw [Real.sq_sqrt hs.le]
    ring
  rw [hfun, Measure.integral_comp_div g R, abs_of_pos hR]
  dsimp only [g, R]
  rw [integral_univ_inv_one_add_sq]
  rw [smul_eq_mul]
  field_simp [(Real.sqrt_pos.2 hs).ne']

lemma abs_inverseFourierDensityCandidate_le_of_four_le_spectralBlocks
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (a lam : ι → ℝ) (B : κ → Finset ι)
    (hcard : 4 ≤ Fintype.card κ)
    (hdisj : Set.PairwiseDisjoint
      (↑(Finset.univ : Finset κ) : Set κ) B)
    {s : ℝ} (hs : 0 < s)
    (hblock : ∀ j, s ≤ ∑ i ∈ B j, (lam i) ^ 2)
    (u : ℝ) :
    |inverseFourierDensityCandidate (diagonalCenteredCharProduct a lam) u| ≤
      1 / (4 * Real.sqrt s) := by
  let phi := diagonalCenteredCharProduct a lam
  let p := inverseFourierDensityCandidate phi
  have hchar : Integrable phi :=
    diagonalCenteredCharProduct_integrable_of_four_le_spectralBlocks
      a lam B hcard hdisj hs hblock
  have hInv : HasInverseFourierDensity p phi :=
    inverseFourierDensityCandidate_hasInverse
      (diagonalCenteredCharProduct_neg a lam)
  have hphase (t : ℝ) :
      ‖phi t * Complex.exp (-(((t * u : ℝ) : ℂ) * Complex.I))‖ =
        ‖phi t‖ := by
    rw [norm_mul, Complex.norm_exp]
    simp
  have hnormInt : (∫ t : ℝ, ‖phi t‖) ≤
      Real.pi / (2 * Real.sqrt s) := by
    calc
      (∫ t : ℝ, ‖phi t‖) ≤ ∫ t : ℝ, fourSpectralEnvelope s t := by
        apply integral_mono hchar.norm (fourSpectralEnvelope_integrable hs)
        intro t
        dsimp only [phi]
        rw [norm_diagonalCenteredCharProduct]
        exact diagonalCharModulus_le_fourSpectralEnvelope_of_four_le_card
          a lam B hcard hdisj hs.le hblock t
      _ = Real.pi / (2 * Real.sqrt s) := integral_fourSpectralEnvelope hs
  rw [← Real.norm_eq_abs, ← Complex.norm_real, hInv u, norm_mul, norm_inv,
    Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (mul_pos (by norm_num) Real.pi_pos)]
  calc
    (2 * Real.pi)⁻¹ *
        ‖∫ t : ℝ, phi t * Complex.exp
          (-(((t * u : ℝ) : ℂ) * Complex.I))‖ ≤
        (2 * Real.pi)⁻¹ *
          ∫ t : ℝ, ‖phi t * Complex.exp
            (-(((t * u : ℝ) : ℂ) * Complex.I))‖ := by
      gcongr
      exact norm_integral_le_integral_norm _
    _ = (2 * Real.pi)⁻¹ * ∫ t : ℝ, ‖phi t‖ := by
      congr 1
      apply integral_congr_ae
      exact Filter.Eventually.of_forall hphase
    _ ≤ (2 * Real.pi)⁻¹ *
        (Real.pi / (2 * Real.sqrt s)) := by gcongr
    _ = 1 / (4 * Real.sqrt s) := by
      field_simp [Real.pi_ne_zero, (Real.sqrt_pos.2 hs).ne']
      norm_num

theorem smallBall_diagonalCenteredLaw_le_of_four_le_spectralBlocks
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (a lam : ι → ℝ) (B : κ → Finset ι)
    (hcard : 4 ≤ Fintype.card κ)
    (hdisj : Set.PairwiseDisjoint
      (↑(Finset.univ : Finset κ) : Set κ) B)
    {s : ℝ} (hs : 0 < s)
    (hblock : ∀ j, s ≤ ∑ i ∈ B j, (lam i) ^ 2)
    {eps : ℝ} (heps : 0 ≤ eps) (x : ℝ) :
    Erdos88.Esseen.smallBall (diagonalCenteredLaw a lam) eps x ≤
      eps / (2 * Real.sqrt s) := by
  letI : IsProbabilityMeasure (diagonalCenteredLaw a lam) :=
    diagonalCenteredLaw_isProbabilityMeasure a lam
  let phi := diagonalCenteredCharProduct a lam
  let p := inverseFourierDensityCandidate (charFun (diagonalCenteredLaw a lam))
  have hchar : Integrable phi :=
    diagonalCenteredCharProduct_integrable_of_four_le_spectralBlocks
      a lam B hcard hdisj hs hblock
  have hlawChar : Integrable (charFun (diagonalCenteredLaw a lam)) := by
    rw [charFun_diagonalCenteredLaw]
    exact hchar
  have hdens : Erdos88.Esseen.HasContinuousDensity
      (diagonalCenteredLaw a lam) p :=
    hasContinuousDensity_inverseFourierDensityCandidate
      (diagonalCenteredLaw a lam) hlawChar
  rw [hdens.smallBall_eq_integral eps x heps]
  calc
    (∫ y in (x - eps)..(x + eps), p y) ≤
        ∫ _y in (x - eps)..(x + eps),
          (1 / (4 * Real.sqrt s) : ℝ) := by
      apply intervalIntegral.integral_mono_on (by linarith)
        (hdens.continuous.intervalIntegrable _ _) intervalIntegrable_const
      intro y hy
      exact (le_abs_self (p y)).trans (by
        dsimp only [p]
        rw [charFun_diagonalCenteredLaw]
        exact abs_inverseFourierDensityCandidate_le_of_four_le_spectralBlocks
          a lam B hcard hdisj hs hblock y)
    _ = eps / (2 * Real.sqrt s) := by
      rw [intervalIntegral.integral_const]
      simp only [smul_eq_mul]
      field_simp [(Real.sqrt_pos.2 hs).ne']
      ring

end Erdos88.GaussianQuadratic
