import ErdosProblems.Erdos587.Analytic

/-!
# Gaussian regularization for the Fresnel transform

The reciprocity argument uses an exact quadratic Fourier identity, not an
asymptotic stationary-phase estimate. This module proves the exact transform
by Gaussian regularization and establishes uniform rapid-decay bounds for
its transformed Schwartz weights.
-/

open Filter MeasureTheory
open scoped FourierTransform RealInnerProductSpace Topology SchwartzMap

namespace Erdos587

/-- Inverse Fourier transform of a complex Gaussian with a linear term. -/
lemma inverse_fourier_complex_gaussian {b : ℂ} (hb : 0 < b.re) (t : ℂ) (ξ : ℝ) :
    𝓕⁻ (fun x : ℝ => Complex.exp (-b * (x : ℂ) ^ 2 + Complex.I * t * x)) ξ =
      (Real.pi / b) ^ (1 / 2 : ℂ) *
        Complex.exp (-(t + 2 * Real.pi * (ξ : ℂ)) ^ 2 / (4 * b)) := by
  rw [Real.fourierInv_eq']
  calc
    (∫ x : ℝ, Complex.exp ((↑(2 * Real.pi * ⟪x, ξ⟫) : ℂ) * Complex.I) •
        Complex.exp (-b * (x : ℂ) ^ 2 + Complex.I * t * x)) =
      ∫ x : ℝ, Complex.exp (Complex.I * (t + 2 * Real.pi * (ξ : ℂ)) * x) *
        Complex.exp (-b * (x : ℂ) ^ 2) := by
      apply integral_congr_ae
      filter_upwards [] with x
      rw [smul_eq_mul, ← Complex.exp_add, ← Complex.exp_add]
      congr 1
      change (↑(2 * Real.pi * (ξ * x)) : ℂ) * Complex.I +
          (-b * (x : ℂ) ^ 2 + Complex.I * t * x) = _
      push_cast
      ring
    _ = (Real.pi / b) ^ (1 / 2 : ℂ) *
        Complex.exp (-(t + 2 * Real.pi * (ξ : ℂ)) ^ 2 / (4 * b)) :=
      fourierIntegral_gaussian hb _

/-- The bilinear inverse-Fourier interchange, in the scalar real-line form
used for the regularized quadratic kernel. -/
lemma integral_inverse_fourier_mul {f g : ℝ → ℂ}
    (hf : Integrable f) (hg : Integrable g) :
    (∫ x : ℝ, 𝓕⁻ f x * g x) = ∫ ξ : ℝ, f ξ * 𝓕⁻ g ξ := by
  have hflip : (-innerₗ ℝ).flip = -innerₗ ℝ := by
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro y
    change -⟪y, x⟫ = -⟪x, y⟫
    rw [real_inner_comm]
  have h := VectorFourier.integral_fourierIntegral_smul_eq_flip
    (L := -innerₗ ℝ) Real.continuous_fourierChar continuous_inner.neg hf hg
  rw [hflip] at h
  exact h

/-- Exact regularized Fresnel identity. The later undamped identity follows
by taking the real part of `b` to zero through positive values. -/
theorem regularized_fresnel_identity {f : ℝ → ℂ}
    (hf : Integrable f) (hhat : Integrable (𝓕 f)) (hcont : Continuous f)
    {b : ℂ} (hb : 0 < b.re) (t : ℂ) :
    (∫ x : ℝ, f x * Complex.exp (-b * (x : ℂ) ^ 2 + Complex.I * t * x)) =
      (Real.pi / b) ^ (1 / 2 : ℂ) *
        ∫ ξ : ℝ, 𝓕 f ξ * Complex.exp (-(t + 2 * Real.pi * (ξ : ℂ)) ^ 2 / (4 * b)) := by
  have hg : Integrable (fun x : ℝ => Complex.exp (-b * (x : ℂ) ^ 2 + Complex.I * t * x)) := by
    simpa only [add_zero] using integrable_cexp_quadratic hb (Complex.I * t) 0
  calc
    (∫ x : ℝ, f x * Complex.exp (-b * (x : ℂ) ^ 2 + Complex.I * t * x)) =
        ∫ ξ : ℝ, 𝓕 f ξ *
          𝓕⁻ (fun x : ℝ => Complex.exp (-b * (x : ℂ) ^ 2 + Complex.I * t * x)) ξ := by
      have h := integral_inverse_fourier_mul hhat hg
      rw [hcont.fourierInv_fourier_eq hf hhat] at h
      exact h
    _ = (Real.pi / b) ^ (1 / 2 : ℂ) *
        ∫ ξ : ℝ, 𝓕 f ξ * Complex.exp (-(t + 2 * Real.pi * (ξ : ℂ)) ^ 2 / (4 * b)) := by
      simp_rw [inverse_fourier_complex_gaussian hb t]
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with ξ
      ring

/-- Gaussian damping never increases the modulus of the quadratic kernel. -/
lemma norm_damped_quadratic_kernel_le_one {b : ℂ} (hb : 0 ≤ b.re) (t x : ℝ) :
    ‖Complex.exp (-b * (x : ℂ) ^ 2 + Complex.I * t * x)‖ ≤ 1 := by
  rw [Complex.norm_exp, Real.exp_le_one_iff]
  have hre : (-b * (x : ℂ) ^ 2 + Complex.I * t * x).re = -b.re * x ^ 2 := by
    simp [Complex.mul_re, Complex.mul_im, pow_two]
  rw [hre]
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hb) (sq_nonneg x)

/-- The dual Gaussian multiplier has modulus at most one as well. -/
lemma norm_dual_gaussian_kernel_le_one {b : ℂ} (hb : 0 ≤ b.re) (y : ℝ) :
    ‖Complex.exp (-(y : ℂ) ^ 2 / (4 * b))‖ ≤ 1 := by
  rw [Complex.norm_exp, Real.exp_le_one_iff]
  have hinv : 0 ≤ ((4 * b)⁻¹).re := by
    rw [Complex.inv_re]
    apply div_nonneg _ (Complex.normSq_nonneg _)
    simpa using (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hb)
  have hre : (-(y : ℂ) ^ 2 / (4 * b)).re = -y ^ 2 * ((4 * b)⁻¹).re := by
    simp [div_eq_mul_inv, ← Complex.ofReal_pow, Complex.mul_re]
  rw [hre]
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg y)) hinv

/-- Removing the damping on the original side of the Fresnel identity. -/
lemma tendsto_damped_quadratic_integral {f : ℝ → ℂ} (hf : Integrable f)
    {b : ℂ} (hb : b.re = 0) (t : ℝ) :
    Tendsto (fun ε : ℝ => ∫ x : ℝ,
      f x * Complex.exp (-(b + ε) * (x : ℂ) ^ 2 + Complex.I * t * x))
      (𝓝[>] 0) (𝓝 (∫ x : ℝ, f x * Complex.exp (-b * (x : ℂ) ^ 2 + Complex.I * t * x))) := by
  apply tendsto_integral_filter_of_dominated_convergence (fun x => ‖f x‖)
  · apply Eventually.of_forall
    intro ε
    apply hf.aestronglyMeasurable.mul
    have hcont : Continuous (fun x : ℝ =>
        Complex.exp (-(b + ε) * (x : ℂ) ^ 2 + Complex.I * t * x)) := by fun_prop
    exact hcont.aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    filter_upwards [] with x
    rw [norm_mul]
    have hbε : 0 ≤ (b + (ε : ℂ)).re := by
      simpa [hb] using (show (0 : ℝ) ≤ ε from le_of_lt hε)
    exact (mul_le_mul_of_nonneg_left (norm_damped_quadratic_kernel_le_one hbε t x)
      (norm_nonneg _)).trans_eq (mul_one _)
  · exact hf.norm
  · filter_upwards [] with x
    have hcont : Continuous (fun ε : ℝ =>
        f x * Complex.exp (-(b + ε) * (x : ℂ) ^ 2 + Complex.I * t * x)) := by fun_prop
    have hlim := (hcont.continuousAt (x := (0 : ℝ))).tendsto.mono_left
      (show 𝓝[>] (0 : ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds)
    simpa only [Complex.ofReal_zero, add_zero] using hlim

/-- Removing the damping on the dual side; the Fourier weight is merely
required to be integrable. -/
lemma tendsto_dual_gaussian_integral {g : ℝ → ℂ} (hg : Integrable g)
    {b : ℂ} (hb : b.re = 0) (hb0 : b ≠ 0) (t : ℝ) :
    Tendsto (fun ε : ℝ => ∫ ξ : ℝ, g ξ *
      Complex.exp (-((t : ℂ) + 2 * Real.pi * (ξ : ℂ)) ^ 2 / (4 * (b + ε))))
      (𝓝[>] 0) (𝓝 (∫ ξ : ℝ, g ξ *
        Complex.exp (-((t : ℂ) + 2 * Real.pi * (ξ : ℂ)) ^ 2 / (4 * b)))) := by
  apply tendsto_integral_filter_of_dominated_convergence (fun ξ => ‖g ξ‖)
  · apply Eventually.of_forall
    intro ε
    apply hg.aestronglyMeasurable.mul
    have hcont : Continuous (fun ξ : ℝ =>
        Complex.exp (-((t : ℂ) + 2 * Real.pi * (ξ : ℂ)) ^ 2 / (4 * (b + ε)))) := by fun_prop
    exact hcont.aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    filter_upwards [] with ξ
    have hbε : 0 ≤ (b + (ε : ℂ)).re := by
      simpa [hb] using (show (0 : ℝ) ≤ ε from le_of_lt hε)
    have hnorm :
        ‖Complex.exp (-((t : ℂ) + 2 * Real.pi * (ξ : ℂ)) ^ 2 / (4 * (b + ε)))‖ ≤ 1 := by
      simpa only [Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_ofNat] using
        norm_dual_gaussian_kernel_le_one hbε (t + 2 * Real.pi * ξ)
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_left hnorm (norm_nonneg _)).trans_eq (mul_one _)
  · exact hg.norm
  · filter_upwards [] with ξ
    have hε : Tendsto (fun ε : ℝ => (ε : ℂ)) (𝓝[>] 0) (𝓝 (0 : ℂ)) :=
      Complex.continuous_ofReal.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    have hden : Tendsto (fun ε : ℝ => (4 : ℂ) * (b + ε)) (𝓝[>] 0) (𝓝 (4 * b)) := by
      simpa only [add_zero] using tendsto_const_nhds.mul (tendsto_const_nhds.add hε)
    have hquot : Tendsto (fun ε : ℝ =>
        -((t : ℂ) + 2 * Real.pi * (ξ : ℂ)) ^ 2 / (4 * (b + ε))) (𝓝[>] 0)
        (𝓝 (-((t : ℂ) + 2 * Real.pi * (ξ : ℂ)) ^ 2 / (4 * b))) :=
      tendsto_const_nhds.div hden (mul_ne_zero (by norm_num) hb0)
    exact tendsto_const_nhds.mul (Complex.continuous_exp.continuousAt.tendsto.comp hquot)

/-- The undamped Fresnel identity on the imaginary axis. Keeping the
prefactor as a complex square root makes its branch explicit. -/
theorem fresnel_identity {f : ℝ → ℂ}
    (hf : Integrable f) (hhat : Integrable (𝓕 f)) (hcont : Continuous f)
    {b : ℂ} (hb : b.re = 0) (hb0 : b ≠ 0) (t : ℝ) :
    (∫ x : ℝ, f x * Complex.exp (-b * (x : ℂ) ^ 2 + Complex.I * t * x)) =
      (Real.pi / b) ^ (1 / 2 : ℂ) *
        ∫ ξ : ℝ, 𝓕 f ξ * Complex.exp (-((t : ℂ) + 2 * Real.pi * (ξ : ℂ)) ^ 2 / (4 * b)) := by
  have hε : Tendsto (fun ε : ℝ => (ε : ℂ)) (𝓝[>] 0) (𝓝 (0 : ℂ)) :=
    Complex.continuous_ofReal.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hbε : Tendsto (fun ε : ℝ => b + (ε : ℂ)) (𝓝[>] 0) (𝓝 b) := by
    simpa only [add_zero] using tendsto_const_nhds.add hε
  have hre : 0 ≤ ((Real.pi : ℂ) / b).re := by simp [Complex.div_re, hb]
  have hpow : ContinuousAt (fun z : ℂ => z ^ (1 / 2 : ℂ)) ((Real.pi : ℂ) / b) :=
    Complex.continuousAt_cpow_const_of_re_pos (Or.inl hre) (by norm_num)
  have hpref := hpow.tendsto.comp (tendsto_const_nhds.div hbε hb0)
  have hright := hpref.mul (tendsto_dual_gaussian_integral hhat hb hb0 t)
  apply tendsto_nhds_unique (tendsto_damped_quadratic_integral hf hb t)
  apply hright.congr'
  filter_upwards [self_mem_nhdsWithin] with ε hεpos
  exact (regularized_fresnel_identity hf hhat hcont
    (by simpa [hb] using hεpos : 0 < (b + (ε : ℂ)).re) (t : ℂ)).symm

/-- The transformed weight in the completed-square Fresnel identity. -/
noncomputable def fresnelProfile (f : ℝ → ℂ) (A s : ℝ) : ℂ :=
  ∫ ξ : ℝ, 𝓕 f ξ * phase (s * ξ - ξ ^ 2 / (4 * A))

/-- A normalization of the square-root factor that isolates its dependence
on the quadratic scale. -/
noncomputable def fresnelPrefactor (A : ℝ) : ℂ :=
  (Complex.I / (2 * (A : ℂ))) ^ (1 / 2 : ℂ)

/-- Exact completed-square Fresnel identity in the `e(x) = exp(2πix)`
convention used by the reciprocal Gauss sums. -/
theorem fresnel_identity_phase {f : ℝ → ℂ}
    (hf : Integrable f) (hhat : Integrable (𝓕 f)) (hcont : Continuous f)
    {A : ℝ} (hA : 0 < A) (k : ℝ) :
    (∫ x : ℝ, f x * phase (A * x ^ 2 - k * x)) =
      fresnelPrefactor A * phase (-(k ^ 2) / (4 * A)) * fresnelProfile f A (k / (2 * A)) := by
  let b : ℂ := -(2 * Real.pi * (A : ℂ) * Complex.I)
  have hb : b.re = 0 := by simp [b, Complex.mul_re, Complex.mul_im]
  have hA0 : (A : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hA.ne'
  have hpi0 : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hb0 : b ≠ 0 := by
    dsimp [b]
    exact neg_ne_zero.mpr (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hpi0) hA0)
      Complex.I_ne_zero)
  have hphase (x : ℝ) : Complex.exp (-b * (x : ℂ) ^ 2 + Complex.I * (-2 * Real.pi * k : ℝ) * x) =
      phase (A * x ^ 2 - k * x) := by
    simp only [phase, Real.fourierChar_apply]
    congr 1
    dsimp [b]
    push_cast
    ring
  have hpref : ((Real.pi : ℂ) / b) ^ (1 / 2 : ℂ) = fresnelPrefactor A := by
    unfold fresnelPrefactor
    congr 1
    dsimp [b]
    field_simp
    simp only [Complex.I_sq]
  have hdual (ξ : ℝ) :
      Complex.exp (-((-2 * Real.pi * k : ℝ) + 2 * Real.pi * (ξ : ℂ)) ^ 2 / (4 * b)) =
        phase (-(k ^ 2) / (4 * A)) * phase (k / (2 * A) * ξ - ξ ^ 2 / (4 * A)) := by
    rw [← phase_add]
    simp only [phase, Real.fourierChar_apply]
    congr 1
    dsimp [b]
    push_cast
    field_simp
    ring_nf
    simp only [Complex.I_sq]
    ring
  have h := fresnel_identity hf hhat hcont hb hb0 (-2 * Real.pi * k)
  simp_rw [hphase, hpref, hdual] at h
  rw [fresnelProfile]
  rw [h]
  rw [mul_assoc]
  congr 1
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with ξ
  ring

/-- Exact modulus of the Fresnel prefactor. -/
lemma norm_fresnelPrefactor {A : ℝ} (hA : 0 < A) :
    ‖fresnelPrefactor A‖ = 1 / Real.sqrt (2 * A) := by
  unfold fresnelPrefactor
  rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num, Complex.norm_cpow_real]
  have hn : ‖Complex.I / (2 * (A : ℂ))‖ = 1 / (2 * A) := by
    rw [norm_div, norm_mul, Complex.norm_I]
    simp [Complex.norm_real, abs_of_pos hA]
  rw [hn, ← Real.sqrt_eq_rpow, Real.sqrt_div (by norm_num), Real.sqrt_one]

/-- The zero-order bound for the transformed weight is uniform in both
the scale and the evaluation point. -/
lemma norm_fresnelProfile_le (f : ℝ → ℂ) (A s : ℝ) :
    ‖fresnelProfile f A s‖ ≤ ∫ ξ : ℝ, ‖𝓕 f ξ‖ := by
  calc
    ‖fresnelProfile f A s‖ ≤
        ∫ ξ : ℝ, ‖𝓕 f ξ * phase (s * ξ - ξ ^ 2 / (4 * A))‖ :=
      norm_integral_le_integral_norm _
    _ = ∫ ξ : ℝ, ‖𝓕 f ξ‖ := by simp_rw [norm_mul, norm_phase, mul_one]

/-- The exact transform also supplies the square-root cancellation scale
with no asymptotic error term. -/
theorem norm_quadratic_integral_le_fourier_l1 {f : ℝ → ℂ}
    (hf : Integrable f) (hhat : Integrable (𝓕 f)) (hcont : Continuous f)
    {A : ℝ} (hA : 0 < A) (k : ℝ) :
    ‖∫ x : ℝ, f x * phase (A * x ^ 2 - k * x)‖ ≤
      (∫ ξ : ℝ, ‖𝓕 f ξ‖) / Real.sqrt (2 * A) := by
  rw [fresnel_identity_phase hf hhat hcont hA k, norm_mul, norm_mul,
    norm_fresnelPrefactor hA, norm_phase, mul_one]
  calc
    1 / Real.sqrt (2 * A) * ‖fresnelProfile f A (k / (2 * A))‖ ≤
        1 / Real.sqrt (2 * A) * (∫ ξ : ℝ, ‖𝓕 f ξ‖) :=
      mul_le_mul_of_nonneg_left (norm_fresnelProfile_le _ _ _) (by positivity)
    _ = (∫ ξ : ℝ, ‖𝓕 f ξ‖) / Real.sqrt (2 * A) := by ring

/-- Iterated real derivatives of a complex exponential with constant slope. -/
lemma iteratedDeriv_real_cexp_mul (c : ℂ) (n : ℕ) :
    iteratedDeriv n (fun x : ℝ => Complex.exp (c * x)) =
      fun x : ℝ => c ^ n * Complex.exp (c * x) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext x
    have hd : HasDerivAt (fun x : ℝ => Complex.exp (c * x))
        (Complex.exp (c * x) * c) x := by
      simpa using (Complex.ofRealCLM.hasDerivAt.const_mul c).cexp
    calc
      deriv (fun x : ℝ => c ^ n * Complex.exp (c * x)) x =
          c ^ n * (Complex.exp (c * x) * c) := (hd.const_mul (c ^ n)).deriv
      _ = c ^ (n + 1) * Complex.exp (c * x) := by rw [pow_succ]; ring

/-- The imaginary exponential has uniformly bounded derivatives of every
order, so composing it with polynomial phases gives temperate growth. -/
lemma hasTemperateGrowth_imaginary_exp :
    (fun x : ℝ => Complex.exp (Complex.I * x)).HasTemperateGrowth := by
  refine ⟨(contDiff_const.mul Complex.ofRealCLM.contDiff).cexp, ?_⟩
  intro n
  refine ⟨0, 1, ?_⟩
  intro x
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_real_cexp_mul]
  simp [norm_pow, Complex.norm_exp, Complex.mul_re]

/-- A smooth temperate real phase gives a temperate unit-modulus
multiplier. This applies also to polynomial phases with extra parameters. -/
lemma hasTemperateGrowth_phase_comp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : E → ℝ} (hg : g.HasTemperateGrowth) :
    (fun x => phase (g x)).HasTemperateGrowth := by
  have hscaled : (fun x => 2 * Real.pi * g x).HasTemperateGrowth := by fun_prop
  have heq : (fun x => phase (g x)) =
      (fun y : ℝ => Complex.exp (Complex.I * y)) ∘ (fun x => 2 * Real.pi * g x) := by
    funext x
    simp only [Function.comp_apply, phase, Real.fourierChar_apply]
    congr 1
    push_cast
    ring
  rw [heq]
  exact hasTemperateGrowth_imaginary_exp.comp hscaled

lemma hasTemperateGrowth_quadratic_chirp (u : ℝ) :
    (fun x : ℝ => phase (u * x ^ 2)).HasTemperateGrowth :=
  hasTemperateGrowth_phase_comp (by fun_prop)

lemma hasTemperateGrowth_parameterized_quadratic_chirp :
    (fun p : ℝ × ℝ => phase (p.1 * p.2 ^ 2)).HasTemperateGrowth := by
  have hf : (fun p : ℝ × ℝ => p.1).HasTemperateGrowth :=
    (ContinuousLinearMap.fst ℝ ℝ ℝ).hasTemperateGrowth
  have hs : (fun p : ℝ × ℝ => p.2).HasTemperateGrowth :=
    (ContinuousLinearMap.snd ℝ ℝ ℝ).hasTemperateGrowth
  exact hasTemperateGrowth_phase_comp (hf.mul (hs.pow 2))

/-- On a bounded parameter interval, every fixed collection of derivatives
of the quadratic multiplier has a common polynomial growth bound. -/
theorem exists_uniform_quadratic_chirp_derivative_bound (N : ℕ) :
    ∃ (k : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ u : ℝ, |u| ≤ 1 → ∀ n ≤ N, ∀ x : ℝ,
      ‖iteratedFDeriv ℝ n (fun x : ℝ => phase (u * x ^ 2)) x‖ ≤ C * (1 + |x|) ^ k := by
  let G : ℝ × ℝ → ℂ := fun p => phase (p.1 * p.2 ^ 2)
  have hG : G.HasTemperateGrowth := hasTemperateGrowth_parameterized_quadratic_chirp
  obtain ⟨k, C, hC, hgrowth⟩ := hG.norm_iteratedFDeriv_le_uniform N
  refine ⟨k, C * 2 ^ k, by positivity, ?_⟩
  intro u hu n hn x
  let J : ℝ →L[ℝ] ℝ × ℝ := ContinuousLinearMap.inr ℝ ℝ ℝ
  let H : ℝ × ℝ → ℂ := fun p => G ((u, 0) + p)
  have hH : ContDiff ℝ (↑(⊤ : ℕ∞)) H := hG.1.comp (contDiff_const.add contDiff_id)
  have heq : (fun x : ℝ => phase (u * x ^ 2)) = H ∘ J := by
    funext x
    simp [H, G, J]
  have hderiv : ‖iteratedFDeriv ℝ n (fun x : ℝ => phase (u * x ^ 2)) x‖ ≤
      ‖iteratedFDeriv ℝ n G (u, x)‖ := by
    rw [heq, J.iteratedFDeriv_comp_right hH x (by exact_mod_cast le_top)]
    have hshift : iteratedFDeriv ℝ n H (J x) = iteratedFDeriv ℝ n G (u, x) := by
      simpa only [H, J, ContinuousLinearMap.inr_apply, Prod.mk_add_mk, add_zero, zero_add] using
        iteratedFDeriv_comp_add_left n (u, 0) (J x) (f := G)
    rw [hshift]
    simpa [J, ContinuousLinearMap.norm_inr] using
      (iteratedFDeriv ℝ n G (u, x)).norm_compContinuousLinearMap_le (fun _ => J)
  have hpair : 1 + ‖(u, x)‖ ≤ 2 * (1 + |x|) := by
    rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs]
    have hm : max |u| |x| ≤ 1 + |x| := by
      apply max_le
      · linarith [abs_nonneg x]
      · linarith
    linarith [abs_nonneg x]
  calc
    ‖iteratedFDeriv ℝ n (fun x : ℝ => phase (u * x ^ 2)) x‖ ≤
        ‖iteratedFDeriv ℝ n G (u, x)‖ := hderiv
    _ ≤ C * (1 + ‖(u, x)‖) ^ k := hgrowth n hn (u, x)
    _ ≤ C * (2 * (1 + |x|)) ^ k :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hpair _) hC
    _ = C * 2 ^ k * (1 + |x|) ^ k := by rw [mul_pow]; ring

/-- Multiplication by a quadratic phase, as an operation on Schwartz functions. -/
noncomputable def quadraticChirpMul (u : ℝ) (f : 𝓢(ℝ, ℂ)) : 𝓢(ℝ, ℂ) :=
  SchwartzMap.smulLeftCLM ℂ (fun x : ℝ => phase (u * x ^ 2)) f

lemma quadraticChirpMul_apply (u : ℝ) (f : 𝓢(ℝ, ℂ)) (x : ℝ) :
    quadraticChirpMul u f x = phase (u * x ^ 2) * f x := by
  simp only [quadraticChirpMul, SchwartzMap.smulLeftCLM_apply_apply
    (hasTemperateGrowth_quadratic_chirp u), smul_eq_mul]

/-- Every Schwartz seminorm of a bounded family of quadratic multipliers
applied to a fixed Schwartz function has a common bound. -/
theorem exists_uniform_quadraticChirpMul_seminorm_bound (f : 𝓢(ℝ, ℂ)) (k n : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ u : ℝ, |u| ≤ 1 →
      SchwartzMap.seminorm ℝ k n (quadraticChirpMul u f) ≤ M := by
  obtain ⟨l, C, hC, hgrowth⟩ := exists_uniform_quadratic_chirp_derivative_bound n
  let P : Seminorm ℝ 𝓢(ℝ, ℂ) :=
    (Finset.Iic (l + k, n)).sup (fun p => SchwartzMap.seminorm ℝ p.1 p.2)
  let M : ℝ := 2 ^ (l + k) * P f
  let B := ContinuousLinearMap.mul ℝ ℂ
  have hM : 0 ≤ M := mul_nonneg (by positivity) (apply_nonneg _ _)
  refine ⟨‖B‖ * ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * (C * M), by positivity, ?_⟩
  intro u hu
  apply SchwartzMap.seminorm_le_bound ℝ k n _ (by positivity)
  intro x
  have hcoef : (quadraticChirpMul u f : ℝ → ℂ) =
      fun x : ℝ => B (phase (u * x ^ 2)) (f x) := by
    funext x
    exact quadraticChirpMul_apply u f x
  rw [hcoef]
  have hprod := B.norm_iteratedFDeriv_le_of_bilinear
    (hasTemperateGrowth_quadratic_chirp u).1 (f.smooth ⊤) x
    (n := n) (by exact_mod_cast le_top)
  have hterm : ∀ i ∈ Finset.range (n + 1),
      ‖x‖ ^ k * (‖iteratedFDeriv ℝ i (fun x : ℝ => phase (u * x ^ 2)) x‖ *
        ‖iteratedFDeriv ℝ (n - i) f x‖) ≤ C * M := by
    intro i hi
    have hin : i ≤ n := by simpa using Finset.mem_range.mp hi
    have hg := hgrowth u hu i hin x
    have hf := SchwartzMap.one_add_le_sup_seminorm_apply
      (𝕜 := ℝ) (m := (l + k, n)) (k := l + k) (n := n - i) le_rfl (Nat.sub_le _ _) f x
    have hf' : (1 + ‖x‖) ^ (l + k) * ‖iteratedFDeriv ℝ (n - i) f x‖ ≤ M := hf
    have hx : ‖x‖ ^ k ≤ (1 + ‖x‖) ^ k :=
      pow_le_pow_left₀ (norm_nonneg _) (by linarith) k
    have hg' : ‖iteratedFDeriv ℝ i (fun x : ℝ => phase (u * x ^ 2)) x‖ ≤
        C * (1 + ‖x‖) ^ l := by simpa only [Real.norm_eq_abs] using hg
    calc
      ‖x‖ ^ k * (‖iteratedFDeriv ℝ i (fun x : ℝ => phase (u * x ^ 2)) x‖ *
          ‖iteratedFDeriv ℝ (n - i) f x‖) ≤
          (1 + ‖x‖) ^ k * ((C * (1 + ‖x‖) ^ l) * ‖iteratedFDeriv ℝ (n - i) f x‖) := by
        gcongr
      _ = C * ((1 + ‖x‖) ^ (l + k) * ‖iteratedFDeriv ℝ (n - i) f x‖) := by
        rw [pow_add]
        ring
      _ ≤ C * M := mul_le_mul_of_nonneg_left hf' hC
  calc
    ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (fun x : ℝ => B (phase (u * x ^ 2)) (f x)) x‖ ≤
        ‖x‖ ^ k * (‖B‖ * ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
          ‖iteratedFDeriv ℝ i (fun x : ℝ => phase (u * x ^ 2)) x‖ *
            ‖iteratedFDeriv ℝ (n - i) f x‖) :=
      mul_le_mul_of_nonneg_left hprod (by positivity)
    _ = ‖B‖ * ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
        (‖x‖ ^ k * (‖iteratedFDeriv ℝ i (fun x : ℝ => phase (u * x ^ 2)) x‖ *
          ‖iteratedFDeriv ℝ (n - i) f x‖)) := by
      rw [mul_left_comm]
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ ≤ ‖B‖ * ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * (C * M) := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg B)
      exact Finset.sum_le_sum (fun i hi =>
        mul_le_mul_of_nonneg_left (hterm i hi) (Nat.cast_nonneg _))

/-- Continuous linear operations on Schwartz space preserve the uniform
seminorm bounds of the bounded quadratic-multiplier family. -/
theorem exists_uniform_linear_quadraticChirpMul_seminorm_bound
    (f : 𝓢(ℝ, ℂ)) (T : 𝓢(ℝ, ℂ) →L[ℝ] 𝓢(ℝ, ℂ)) (k n : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ u : ℝ, |u| ≤ 1 →
      SchwartzMap.seminorm ℝ k n (T (quadraticChirpMul u f)) ≤ M := by
  let S : Set 𝓢(ℝ, ℂ) := (fun u : ℝ => quadraticChirpMul u f) '' {u : ℝ | |u| ≤ 1}
  have hS : Bornology.IsVonNBounded ℝ S := by
    apply (schwartz_withSeminorms ℝ ℝ ℂ).isVonNBounded_iff_seminorm_bounded.mpr
    rintro ⟨k', n'⟩
    obtain ⟨M, hM, hbound⟩ := exists_uniform_quadraticChirpMul_seminorm_bound f k' n'
    refine ⟨M + 1, by linarith, ?_⟩
    intro g hg
    obtain ⟨u, hu, rfl⟩ := hg
    exact (hbound u hu).trans_lt (by linarith)
  have hTS := hS.image T
  obtain ⟨M, hM, hbound⟩ :=
    (schwartz_withSeminorms ℝ ℝ ℂ).isVonNBounded_iff_seminorm_bounded.mp hTS (k, n)
  refine ⟨M, hM.le, ?_⟩
  intro u hu
  exact (hbound _ ⟨quadraticChirpMul u f, ⟨u, hu, rfl⟩, rfl⟩).le

/-- The Fresnel profile is an inverse Fourier transform of the Fourier
weight multiplied by a bounded-parameter quadratic phase. -/
lemma fresnelProfile_eq_inverse_fourier (f : 𝓢(ℝ, ℂ)) (A s : ℝ) :
    fresnelProfile f A s = 𝓕⁻ (quadraticChirpMul (-1 / (4 * A)) (𝓕 f)) s := by
  rw [SchwartzMap.fourierInv_coe, Real.fourierInv_eq, fresnelProfile]
  apply integral_congr_ae
  filter_upwards [] with ξ
  rw [quadraticChirpMul_apply]
  change 𝓕 (f : ℝ → ℂ) ξ * phase (s * ξ - ξ ^ 2 / (4 * A)) =
    phase (s * ξ) * (phase ((-1 / (4 * A)) * ξ ^ 2) * 𝓕 (f : ℝ → ℂ) ξ)
  have heq : phase (s * ξ - ξ ^ 2 / (4 * A)) =
      phase (s * ξ) * phase ((-1 / (4 * A)) * ξ ^ 2) := by
    rw [← phase_add]
    congr 1
    ring
  rw [heq]
  ring

/-- All rapid-decay and derivative bounds for the Fresnel profile are
uniform for `A ≥ 1`. This is the uniform Schwartz estimate required when
truncating and partially summing the reciprocal Fourier series. -/
theorem exists_uniform_fresnelProfile_derivative_bound (f : 𝓢(ℝ, ℂ)) (k n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ A : ℝ, 1 ≤ A → ∀ s : ℝ,
      (1 + |s|) ^ k * ‖iteratedDeriv n (fresnelProfile f A) s‖ ≤ C := by
  let T : 𝓢(ℝ, ℂ) →L[ℝ] 𝓢(ℝ, ℂ) := FourierTransform.fourierInvCLM ℝ 𝓢(ℝ, ℂ)
  obtain ⟨M₀, hM₀, hbound₀⟩ := exists_uniform_linear_quadraticChirpMul_seminorm_bound (𝓕 f) T 0 n
  obtain ⟨Mₖ, hMₖ, hboundₖ⟩ := exists_uniform_linear_quadraticChirpMul_seminorm_bound (𝓕 f) T k n
  refine ⟨2 ^ k * (M₀ + Mₖ), by positivity, ?_⟩
  intro A hA s
  have hu : |-1 / (4 * A)| ≤ 1 := by
    rw [abs_div, abs_neg, abs_one, abs_of_pos (by linarith : 0 < 4 * A)]
    exact (div_le_one₀ (by linarith : 0 < 4 * A)).mpr (by linarith)
  let g : 𝓢(ℝ, ℂ) := T (quadraticChirpMul (-1 / (4 * A)) (𝓕 f))
  have hcoef : fresnelProfile f A = (g : ℝ → ℂ) := by
    funext s
    exact fresnelProfile_eq_inverse_fourier f A s
  rw [hcoef]
  have hzero : ‖iteratedDeriv n (g : ℝ → ℂ) s‖ ≤ M₀ := by
    have h := SchwartzMap.le_seminorm' ℝ 0 n g s
    simp only [pow_zero, one_mul] at h
    exact h.trans (hbound₀ _ hu)
  have hpow : |s| ^ k * ‖iteratedDeriv n (g : ℝ → ℂ) s‖ ≤ Mₖ :=
    (SchwartzMap.le_seminorm' ℝ k n g s).trans (hboundₖ _ hu)
  by_cases hs : |s| ≤ 1
  · calc
      (1 + |s|) ^ k * ‖iteratedDeriv n (g : ℝ → ℂ) s‖ ≤
          2 ^ k * ‖iteratedDeriv n (g : ℝ → ℂ) s‖ := by
        gcongr
        linarith
      _ ≤ 2 ^ k * M₀ := mul_le_mul_of_nonneg_left hzero (by positivity)
      _ ≤ 2 ^ k * (M₀ + Mₖ) :=
        mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hMₖ) (by positivity)
  · have hs' : 1 ≤ |s| := (lt_of_not_ge hs).le
    calc
      (1 + |s|) ^ k * ‖iteratedDeriv n (g : ℝ → ℂ) s‖ ≤
          (2 * |s|) ^ k * ‖iteratedDeriv n (g : ℝ → ℂ) s‖ := by
        gcongr
        linarith
      _ = 2 ^ k * (|s| ^ k * ‖iteratedDeriv n (g : ℝ → ℂ) s‖) := by rw [mul_pow]; ring
      _ ≤ 2 ^ k * Mₖ := mul_le_mul_of_nonneg_left hpow (by positivity)
      _ ≤ 2 ^ k * (M₀ + Mₖ) := mul_le_mul_of_nonneg_left (le_add_of_nonneg_left hM₀) (by positivity)

end Erdos587
