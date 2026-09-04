import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import ErdosProblems.Erdos1002.FourierSeries
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.NumberTheory.ZetaValues

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# The principal-value transform in Lemma 2.1

The symmetric truncations and the Abel-damped auxiliary kernels are defined
explicitly in this file.  No distributional interpretation of `PV (1/x)` is
used.
-/

open Filter MeasureTheory Set
open scoped ComplexConjugate ENNReal Real Topology

namespace Erdos1002

noncomputable section

/-- The complex exponential `e(t) = exp(2πit)` in the paper's convention. -/
def paperExp (t : ℝ) : ℂ :=
  Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ))

/-- The quotient `V(Nx)/x`, with the irrelevant value at zero fixed to zero. -/
def transformKernel (N : ℕ) (x : ℝ) : ℝ :=
  if x = 0 then 0 else bernoulliMark ((N : ℝ) * x) / x

/-- Symmetric finite truncation of the real-line transform. -/
def principalValueTruncation (N : ℕ) (s R : ℝ) : ℂ :=
  ∫ x in -R..R, (transformKernel N x : ℂ) * paperExp (-s * x)

/-- A fully explicit assertion that symmetric truncations have principal value `z`. -/
def HasSymmetricPrincipalValue (N : ℕ) (s : ℝ) (z : ℂ) : Prop :=
  Tendsto (principalValueTruncation N s) atTop (nhds z)

/-- Exponentially damped one-sided sine kernel used to prove the Dirichlet limit. -/
def dampedSineIntegral (ε a : ℝ) : ℝ :=
  ∫ x in Ioi (0 : ℝ), Real.exp (-ε * x) * (Real.sin (a * x) / x)

private theorem integral_exp_neg_mul_cos_Ioi (ε t : ℝ) (hε : 0 < ε) :
    ∫ x in Ioi (0 : ℝ), Real.exp (-ε * x) * Real.cos (t * x) =
      ε / (ε ^ 2 + t ^ 2) := by
  let z : ℂ := (-ε : ℂ) + (t : ℂ) * Complex.I
  have hz : z.re < 0 := by
    dsimp [z]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.I_re, mul_zero, Complex.ofReal_im, Complex.I_im,
    mul_one, sub_self, add_zero, Left.neg_neg_iff]
    exact hε
  have hzint := integrableOn_exp_mul_complex_Ioi hz 0
  have hformula := integral_exp_mul_complex_Ioi hz 0
  have hpoint : ∀ x : ℝ,
      (Complex.exp (z * (x : ℂ))).re = Real.exp (-ε * x) * Real.cos (t * x) := by
    intro x
    rw [Complex.exp_re]
    dsimp [z]
    simp
  calc
    (∫ x in Ioi (0 : ℝ), Real.exp (-ε * x) * Real.cos (t * x)) =
        ∫ x in Ioi (0 : ℝ), (Complex.exp (z * (x : ℂ))).re := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      exact (hpoint x).symm
    _ = (∫ x in Ioi (0 : ℝ), Complex.exp (z * (x : ℂ))).re :=
      integral_re hzint
    _ = (-Complex.exp (z * (0 : ℂ)) / z).re := congrArg Complex.re hformula
    _ = ε / (ε ^ 2 + t ^ 2) := by
      dsimp [z]
      simp only [Complex.neg_re, Complex.ofReal_re, Complex.add_re, Complex.mul_re,
        Complex.I_re, Complex.I_im, Complex.ofReal_im, mul_zero, zero_mul, sub_zero,
        Complex.neg_im, Complex.add_im, Complex.mul_im, mul_one, add_zero,
        Complex.div_re, Complex.normSq_apply, mul_neg, mul_zero,
        Complex.exp_zero, Complex.one_re, Complex.one_im, neg_zero]
      ring_nf

private theorem integral_cos_mul (a x : ℝ) (hx : x ≠ 0) :
    ∫ t in (0 : ℝ)..a, Real.cos (t * x) = Real.sin (a * x) / x := by
  rw [intervalIntegral.integral_comp_mul_right Real.cos hx]
  rw [integral_cos]
  simp only [zero_mul, Real.sin_zero, sub_zero, smul_eq_mul]
  rw [inv_mul_eq_div]

private theorem integral_eps_div_sq (ε a : ℝ) (hε : 0 < ε) :
    ∫ t in (0 : ℝ)..a, ε / (ε ^ 2 + t ^ 2) = Real.arctan (a / ε) := by
  have hε0 : ε ≠ 0 := hε.ne'
  have hderiv : ∀ t : ℝ,
      HasDerivAt (fun u : ℝ => Real.arctan (u / ε)) (ε / (ε ^ 2 + t ^ 2)) t := by
    intro t
    convert! (Real.hasDerivAt_arctan (t / ε)).comp t ((hasDerivAt_id t).div_const ε) using 1
    field_simp [hε0]
  calc
    (∫ t in (0 : ℝ)..a, ε / (ε ^ 2 + t ^ 2)) =
        Real.arctan (a / ε) - Real.arctan (0 / ε) := by
      apply intervalIntegral.integral_eq_sub_of_hasDerivAt
      · intro t ht
        exact hderiv t
      · apply Continuous.intervalIntegrable
        exact continuous_const.div₀ (continuous_const.add (continuous_id.pow 2)) fun t => by
          have : 0 < ε ^ 2 := sq_pos_of_pos hε
          positivity
    _ = Real.arctan (a / ε) := by simp

private theorem dampedSineIntegral_eq_arctan_of_nonneg (ε a : ℝ)
    (hε : 0 < ε) (ha : 0 ≤ a) :
    dampedSineIntegral ε a = Real.arctan (a / ε) := by
  let F : ℝ → ℝ → ℝ := fun t x => Real.exp (-ε * x) * Real.cos (t * x)
  have ht : Integrable (fun _t : ℝ => (1 : ℝ))
      (volume.restrict (uIoc (0 : ℝ) a)) := by
    rw [uIoc_of_le ha]
    exact integrableOn_const measure_Ioc_lt_top.ne
  have hx : Integrable (fun x : ℝ => Real.exp (-ε * x))
      (volume.restrict (Ioi (0 : ℝ))) := by
    simpa only [neg_mul] using! integrableOn_exp_mul_Ioi (a := -ε) (neg_lt_zero.mpr hε) 0
  have hF : Integrable (Function.uncurry F)
      ((volume.restrict (uIoc (0 : ℝ) a)).prod (volume.restrict (Ioi (0 : ℝ)))) := by
    apply (ht.mul_prod hx).mono'
    · exact (by
        dsimp [F, Function.uncurry]
        fun_prop : AEStronglyMeasurable (Function.uncurry F)
          ((volume.restrict (uIoc (0 : ℝ) a)).prod (volume.restrict (Ioi (0 : ℝ)))))
    · filter_upwards with z
      dsimp [F, Function.uncurry]
      rw [abs_mul, abs_of_pos (Real.exp_pos _), one_mul]
      exact mul_le_of_le_one_right (Real.exp_pos _).le (Real.abs_cos_le_one _)
  calc
    dampedSineIntegral ε a =
        ∫ x in Ioi (0 : ℝ), Real.exp (-ε * x) *
          (∫ t in (0 : ℝ)..a, Real.cos (t * x)) := by
      unfold dampedSineIntegral
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hxmem
      change Real.exp (-ε * x) * (Real.sin (a * x) / x) =
        Real.exp (-ε * x) * (∫ t in (0 : ℝ)..a, Real.cos (t * x))
      rw [integral_cos_mul a x (ne_of_gt hxmem)]
    _ = ∫ x in Ioi (0 : ℝ), ∫ t in (0 : ℝ)..a, F t x := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hxmem
      change Real.exp (-ε * x) * (∫ t in (0 : ℝ)..a, Real.cos (t * x)) =
        ∫ t in (0 : ℝ)..a, Real.exp (-ε * x) * Real.cos (t * x)
      rw [intervalIntegral.integral_const_mul]
    _ = ∫ t in (0 : ℝ)..a,
          ∫ x in Ioi (0 : ℝ), Real.exp (-ε * x) * Real.cos (t * x) := by
      exact (intervalIntegral_integral_swap hF).symm
    _ = ∫ t in (0 : ℝ)..a, ε / (ε ^ 2 + t ^ 2) := by
      apply intervalIntegral.integral_congr
      intro t htmem
      exact integral_exp_neg_mul_cos_Ioi ε t hε
    _ = Real.arctan (a / ε) := integral_eps_div_sq ε a hε

theorem dampedSineIntegral_neg (ε a : ℝ) :
    dampedSineIntegral ε (-a) = -dampedSineIntegral ε a := by
  unfold dampedSineIntegral
  simp only [neg_mul, Real.sin_neg, neg_div, mul_neg]
  exact integral_neg _

/-- The elementary Abel-damped sine integral, proved by Fubini and the Laplace transform of cosine. -/
theorem dampedSineIntegral_eq_arctan (ε a : ℝ) (hε : 0 < ε) :
    dampedSineIntegral ε a = Real.arctan (a / ε) := by
  rcases le_total 0 a with ha | ha
  · exact dampedSineIntegral_eq_arctan_of_nonneg ε a hε ha
  · have hna : 0 ≤ -a := neg_nonneg.mpr ha
    calc
      dampedSineIntegral ε a = -dampedSineIntegral ε (-a) := by
        rw [dampedSineIntegral_neg]
        simp
      _ = -Real.arctan ((-a) / ε) := by
        rw [dampedSineIntegral_eq_arctan_of_nonneg ε (-a) hε hna]
      _ = Real.arctan (a / ε) := by
        rw [show (-a) / ε = -(a / ε) by ring, Real.arctan_neg]
        simp

/-- The signed endpoint of the Dirichlet integral.  It is written without a
`sign` convention so that the value at zero is completely explicit. -/
def dirichletSineLimit (a : ℝ) : ℝ :=
  if 0 < a then Real.pi / 2 else if a < 0 then -(Real.pi / 2) else 0

/-- Abel's regularization of the Dirichlet sine integral tends to its exact
signed half-π value. -/
theorem tendsto_dampedSineIntegral_nhdsGT_zero (a : ℝ) :
    Tendsto (fun ε : ℝ => dampedSineIntegral ε a) (𝓝[>] 0)
      (nhds (dirichletSineLimit a)) := by
  have heq : (fun ε : ℝ => dampedSineIntegral ε a) =ᶠ[𝓝[>] 0]
      fun ε => Real.arctan (a / ε) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact dampedSineIntegral_eq_arctan ε a hε
  rcases lt_trichotomy a 0 with ha | rfl | ha
  · have hratio : Tendsto (fun ε : ℝ => a / ε) (𝓝[>] 0) atBot := by
      simpa only [div_eq_inv_mul, mul_comm] using!
        tendsto_inv_nhdsGT_zero.atTop_mul_neg ha tendsto_const_nhds
    have harctan : Tendsto (fun ε : ℝ => Real.arctan (a / ε)) (𝓝[>] 0)
        (nhds (-(Real.pi / 2))) :=
      (tendsto_nhds_of_tendsto_nhdsWithin Real.tendsto_arctan_atBot).comp hratio
    simpa [dirichletSineLimit, ha, not_lt.mpr ha.le] using! harctan.congr' heq.symm
  · have hzero : Tendsto (fun ε : ℝ => Real.arctan ((0 : ℝ) / ε)) (𝓝[>] 0)
        (nhds 0) := by
      simp only [zero_div, Real.arctan_zero]
      exact (tendsto_const_nhds :
        Tendsto (fun _ε : ℝ => (0 : ℝ)) (𝓝[>] 0) (nhds 0))
    simpa [dirichletSineLimit] using! hzero.congr' heq.symm
  · have hratio : Tendsto (fun ε : ℝ => a / ε) (𝓝[>] 0) atTop := by
      simpa only [div_eq_inv_mul, mul_comm] using!
        tendsto_inv_nhdsGT_zero.atTop_mul_pos ha tendsto_const_nhds
    have harctan : Tendsto (fun ε : ℝ => Real.arctan (a / ε)) (𝓝[>] 0)
        (nhds (Real.pi / 2)) :=
      (tendsto_nhds_of_tendsto_nhdsWithin Real.tendsto_arctan_atTop).comp hratio
    simpa [dirichletSineLimit, ha, not_lt.mpr ha.le] using! harctan.congr' heq.symm

/-- Euler's formula in the normalization used by the paper. -/
theorem paperExp_eq_cos_add_sin_mul_I (t : ℝ) :
    paperExp t =
      (Real.cos (2 * Real.pi * t) : ℂ) + (Real.sin (2 * Real.pi * t) : ℂ) * Complex.I := by
  unfold paperExp
  rw [show 2 * (Real.pi : ℂ) * Complex.I * (t : ℂ) =
      ((2 * Real.pi * t : ℝ) : ℂ) * Complex.I by push_cast; ring]
  simpa only [Complex.ofReal_cos, Complex.ofReal_sin] using!
    (Complex.exp_mul_I ((2 * Real.pi * t : ℝ) : ℂ))

/-- The Abel-damped symmetric pairing of `e(-ax)/x` on the two half-lines. -/
def dampedSymmetricExponentialIntegral (ε a : ℝ) : ℂ :=
  ∫ x in Ioi (0 : ℝ),
    (Real.exp (-ε * x) : ℂ) *
      ((paperExp (-a * x) - paperExp (a * x)) / (x : ℂ))

/-- Pairing the two half-lines turns the exponential kernel into exactly
`-2i` times the corresponding sine kernel. -/
theorem dampedSymmetricExponentialIntegral_eq (ε a : ℝ) :
    dampedSymmetricExponentialIntegral ε a =
      (-2 * Complex.I) * (dampedSineIntegral ε (2 * Real.pi * a) : ℂ) := by
  let f : ℝ → ℝ := fun x =>
    Real.exp (-ε * x) * (Real.sin ((2 * Real.pi * a) * x) / x)
  calc
    dampedSymmetricExponentialIntegral ε a =
        ∫ x in Ioi (0 : ℝ), (-2 * Complex.I) * (f x : ℂ) := by
      unfold dampedSymmetricExponentialIntegral
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      change (Real.exp (-ε * x) : ℂ) *
          ((paperExp (-a * x) - paperExp (a * x)) / (x : ℂ)) =
        (-2 * Complex.I) * (f x : ℂ)
      have harg : 2 * Real.pi * (-a * x) = -(2 * Real.pi * a * x) := by ring
      have hdiff : paperExp (-a * x) - paperExp (a * x) =
          (-2 * Complex.I) * (Real.sin (2 * Real.pi * a * x) : ℂ) := by
        rw [paperExp_eq_cos_add_sin_mul_I, paperExp_eq_cos_add_sin_mul_I, harg,
          Real.cos_neg, Real.sin_neg]
        push_cast
        ring_nf
      rw [hdiff]
      have hx0 : x ≠ 0 := ne_of_gt hx
      dsimp [f]
      push_cast
      have hxc : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx0
      apply (mul_right_cancel₀ hxc)
      simp
      ring
    _ = (-2 * Complex.I) * ∫ x in Ioi (0 : ℝ), (f x : ℂ) := by
      rw [integral_const_mul]
    _ = (-2 * Complex.I) * (∫ x in Ioi (0 : ℝ), f x : ℝ) := by
      congr 1
      exact integral_ofReal
    _ = (-2 * Complex.I) * (dampedSineIntegral ε (2 * Real.pi * a) : ℂ) := by rfl

/-- The exact signed value of the symmetric transform of `e(-ax)/x`. -/
def signedExponentialPV (a : ℝ) : ℂ :=
  if 0 < a then -Complex.I * Real.pi
  else if a < 0 then Complex.I * Real.pi
  else 0

private theorem signedExponentialPV_eq_dirichlet (a : ℝ) :
    signedExponentialPV a =
      (-2 * Complex.I) * (dirichletSineLimit (2 * Real.pi * a) : ℂ) := by
  rcases lt_trichotomy a 0 with ha | rfl | ha
  · have hpa : 2 * Real.pi * a < 0 := mul_neg_of_pos_of_neg (mul_pos two_pos Real.pi_pos) ha
    unfold signedExponentialPV dirichletSineLimit
    rw [if_neg (not_lt.mpr ha.le), if_pos ha, if_neg (not_lt.mpr hpa.le), if_pos hpa]
    push_cast
    ring
  · simp [signedExponentialPV, dirichletSineLimit]
  · have hpa : 0 < 2 * Real.pi * a := mul_pos (mul_pos two_pos Real.pi_pos) ha
    unfold signedExponentialPV dirichletSineLimit
    rw [if_pos ha, if_pos hpa]
    push_cast
    ring

/-- The exponential damping limit
`PV ∫ e(-ax) / x dx = -iπ sign(a)`, including the zero-frequency value.
It follows from the Fubini computation above, rather than from a
distributional Fourier-transform rule. -/
theorem tendsto_dampedSymmetricExponentialIntegral_nhdsGT_zero (a : ℝ) :
    Tendsto (fun ε : ℝ => dampedSymmetricExponentialIntegral ε a) (𝓝[>] 0)
      (nhds (signedExponentialPV a)) := by
  have hsine := tendsto_dampedSineIntegral_nhdsGT_zero (2 * Real.pi * a)
  have hcast : Tendsto
      (fun ε : ℝ => (dampedSineIntegral ε (2 * Real.pi * a) : ℂ)) (𝓝[>] 0)
      (nhds (dirichletSineLimit (2 * Real.pi * a) : ℂ)) :=
    (Complex.continuous_ofReal.tendsto _).comp hsine
  have hmul : Tendsto
      (fun ε : ℝ => (-2 * Complex.I) *
        (dampedSineIntegral ε (2 * Real.pi * a) : ℂ)) (𝓝[>] 0)
      (nhds ((-2 * Complex.I) * (dirichletSineLimit (2 * Real.pi * a) : ℂ))) :=
    tendsto_const_nhds.mul hcast
  rw [signedExponentialPV_eq_dirichlet]
  apply hmul.congr'
  filter_upwards with ε
  exact (dampedSymmetricExponentialIntegral_eq ε a).symm

/-! ## From Abel damping to genuine symmetric truncation -/

private theorem integral_inv_sq (A B : ℝ) (hA : 0 < A) (hAB : A ≤ B) :
    ∫ x in A..B, 1 / x ^ 2 = 1 / A - 1 / B := by
  have hderiv : ∀ x ∈ uIcc A B,
      HasDerivAt (fun y : ℝ => -(y⁻¹)) (1 / x ^ 2) x := by
    intro x hx
    rw [uIcc_of_le hAB] at hx
    convert! (hasDerivAt_inv (ne_of_gt (hA.trans_le hx.1))).neg using 1
    ring
  have hint : IntervalIntegrable (fun x : ℝ => 1 / x ^ 2) volume A B := by
    apply ContinuousOn.intervalIntegrable
    exact continuousOn_const.div (continuousOn_id.pow 2) (fun x hx => by
      rw [uIcc_of_le hAB] at hx
      exact pow_ne_zero 2 (ne_of_gt (hA.trans_le hx.1)))
  calc
    (∫ x in A..B, 1 / x ^ 2) = -(B⁻¹) - (-(A⁻¹)) :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
    _ = 1 / A - 1 / B := by ring

private theorem sine_tail_formula (a A B : ℝ) (ha : a ≠ 0) (hA : 0 < A) (hAB : A ≤ B) :
    ∫ x in A..B, Real.sin (a * x) / x =
      B⁻¹ * (-(a⁻¹) * Real.cos (a * B)) -
        A⁻¹ * (-(a⁻¹) * Real.cos (a * A)) -
        ∫ x in A..B, (-(x ^ 2)⁻¹) * (-(a⁻¹) * Real.cos (a * x)) := by
  let u : ℝ → ℝ := fun x => x⁻¹
  let u' : ℝ → ℝ := fun x => -(x ^ 2)⁻¹
  let v : ℝ → ℝ := fun x => -(a⁻¹) * Real.cos (a * x)
  let v' : ℝ → ℝ := fun x => Real.sin (a * x)
  have hu : ∀ x ∈ uIcc A B, HasDerivAt u (u' x) x := by
    intro x hx
    rw [uIcc_of_le hAB] at hx
    exact hasDerivAt_inv (ne_of_gt (hA.trans_le hx.1))
  have hv : ∀ x ∈ uIcc A B, HasDerivAt v (v' x) x := by
    intro x hx
    dsimp [v, v']
    convert! (((hasDerivAt_id x).const_mul a).cos.const_mul (-(a⁻¹))) using 1
    simp only [id_eq]
    field_simp [ha]
  have hu' : IntervalIntegrable u' volume A B := by
    apply ContinuousOn.intervalIntegrable
    exact ((continuousOn_id.pow 2).inv₀ (fun x hx => by
      rw [uIcc_of_le hAB] at hx
      exact pow_ne_zero 2 (ne_of_gt (hA.trans_le hx.1)))).neg
  have hv' : IntervalIntegrable v' volume A B := by
    exact (Real.continuous_sin.comp (continuous_const.mul continuous_id)).intervalIntegrable A B
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hv hu' hv'
  dsimp [u, u', v, v'] at hparts ⊢
  simpa only [inv_mul_eq_div] using! hparts

private theorem sine_tail_bound (a A B : ℝ) (ha : a ≠ 0) (hA : 0 < A) (hAB : A ≤ B) :
    |∫ x in A..B, Real.sin (a * x) / x| ≤ 3 * (|a|⁻¹ * A⁻¹) := by
  have hB : 0 < B := hA.trans_le hAB
  have haabs : 0 < |a| := abs_pos.mpr ha
  have hBinv : B⁻¹ ≤ A⁻¹ := (inv_le_inv₀ hB hA).2 hAB
  have htermB :
      |B⁻¹ * (-(a⁻¹) * Real.cos (a * B))| ≤ |a|⁻¹ * A⁻¹ := by
    rw [abs_mul, abs_of_pos (inv_pos.mpr hB), abs_mul, abs_neg, abs_inv]
    calc
      B⁻¹ * (|a|⁻¹ * |Real.cos (a * B)|) ≤ B⁻¹ * (|a|⁻¹ * 1) := by
        gcongr
        exact Real.abs_cos_le_one _
      _ ≤ A⁻¹ * (|a|⁻¹ * 1) := by gcongr
      _ = |a|⁻¹ * A⁻¹ := by ring
  have htermA :
      |A⁻¹ * (-(a⁻¹) * Real.cos (a * A))| ≤ |a|⁻¹ * A⁻¹ := by
    rw [abs_mul, abs_of_pos (inv_pos.mpr hA), abs_mul, abs_neg, abs_inv]
    calc
      A⁻¹ * (|a|⁻¹ * |Real.cos (a * A)|) ≤ A⁻¹ * (|a|⁻¹ * 1) := by
        gcongr
        exact Real.abs_cos_le_one _
      _ = |a|⁻¹ * A⁻¹ := by ring
  let q : ℝ → ℝ := fun x => (-(x ^ 2)⁻¹) * (-(a⁻¹) * Real.cos (a * x))
  let g : ℝ → ℝ := fun x => |a|⁻¹ * (1 / x ^ 2)
  have hg : IntervalIntegrable g volume A B := by
    apply ContinuousOn.intervalIntegrable
    exact continuousOn_const.mul (continuousOn_const.div (continuousOn_id.pow 2)
      (fun x hx => by
        rw [uIcc_of_le hAB] at hx
        exact pow_ne_zero 2 (ne_of_gt (hA.trans_le hx.1))))
  have hqg : ∀ x ∈ Ioc A B, ‖q x‖ ≤ g x := by
    intro x hx
    have hxpos : 0 < x := hA.trans hx.1
    dsimp [q, g]
    rw [abs_mul, abs_neg, abs_inv, abs_mul, abs_neg, abs_inv,
      abs_of_pos (sq_pos_of_pos hxpos)]
    calc
      (x ^ 2)⁻¹ * (|a|⁻¹ * |Real.cos (a * x)|) ≤
          (x ^ 2)⁻¹ * (|a|⁻¹ * 1) := by
        gcongr
        exact Real.abs_cos_le_one _
      _ = |a|⁻¹ * (1 / x ^ 2) := by ring
  have hcorr0 : |∫ x in A..B, q x| ≤ ∫ x in A..B, g x := by
    simpa only [Real.norm_eq_abs] using! intervalIntegral.norm_integral_le_of_norm_le hAB
      (Eventually.of_forall fun x hx => hqg x hx) hg
  have hgval : (∫ x in A..B, g x) = |a|⁻¹ * (1 / A - 1 / B) := by
    dsimp [g]
    rw [intervalIntegral.integral_const_mul, integral_inv_sq A B hA hAB]
  have hcorr : |∫ x in A..B, q x| ≤ |a|⁻¹ * A⁻¹ := by
    calc
      |∫ x in A..B, q x| ≤ ∫ x in A..B, g x := hcorr0
      _ = |a|⁻¹ * (1 / A - 1 / B) := hgval
      _ ≤ |a|⁻¹ * A⁻¹ := by
        have : 0 ≤ B⁻¹ := (inv_pos.mpr hB).le
        rw [one_div, one_div]
        nlinarith [inv_pos.mpr haabs]
  rw [sine_tail_formula a A B ha hA hAB]
  change |B⁻¹ * (-(a⁻¹) * Real.cos (a * B)) -
      A⁻¹ * (-(a⁻¹) * Real.cos (a * A)) - ∫ x in A..B, q x| ≤ _
  calc
    |B⁻¹ * (-(a⁻¹) * Real.cos (a * B)) -
        A⁻¹ * (-(a⁻¹) * Real.cos (a * A)) - ∫ x in A..B, q x| ≤
      |B⁻¹ * (-(a⁻¹) * Real.cos (a * B))| +
        |A⁻¹ * (-(a⁻¹) * Real.cos (a * A))| + |∫ x in A..B, q x| := by
      calc
        |_ - ∫ x in A..B, q x| ≤
            |B⁻¹ * (-(a⁻¹) * Real.cos (a * B)) -
              A⁻¹ * (-(a⁻¹) * Real.cos (a * A))| + |∫ x in A..B, q x| := abs_sub _ _
        _ ≤ (|B⁻¹ * (-(a⁻¹) * Real.cos (a * B))| +
              |A⁻¹ * (-(a⁻¹) * Real.cos (a * A))|) + |∫ x in A..B, q x| := by
            gcongr
            exact abs_sub _ _
    _ ≤ 3 * (|a|⁻¹ * A⁻¹) := by linarith

def sineKernel (a x : ℝ) : ℝ := a * Real.sinc (a * x)

private theorem sineKernel_eq (a : ℝ) {x : ℝ} (hx : x ≠ 0) :
    sineKernel a x = Real.sin (a * x) / x := by
  by_cases ha : a = 0
  · simp [sineKernel, ha]
  · rw [sineKernel, Real.sinc_of_ne_zero (mul_ne_zero ha hx)]
    field_simp [ha, hx]

private theorem continuous_sineKernel (a : ℝ) : Continuous (sineKernel a) := by
  exact continuous_const.mul (Real.continuous_sinc.comp (continuous_const.mul continuous_id))

private theorem sineKernel_tail_bound (a A B : ℝ) (ha : a ≠ 0) (hA : 0 < A) (hAB : A ≤ B) :
    |∫ x in A..B, sineKernel a x| ≤ 3 * (|a|⁻¹ * A⁻¹) := by
  have heq : (∫ x in A..B, sineKernel a x) =
      ∫ x in A..B, Real.sin (a * x) / x := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le hAB] at hx
    exact sineKernel_eq a (ne_of_gt (hA.trans_le hx.1))
  rw [heq]
  exact sine_tail_bound a A B ha hA hAB

private theorem damped_sineKernel_tail_bound (ε a A : ℝ)
    (hε : 0 < ε) (ha : a ≠ 0) (hA : 0 < A) :
    |∫ x in Ioi A, Real.exp (-ε * x) * sineKernel a x| ≤
      3 * (|a|⁻¹ * A⁻¹) := by
  let f : ℝ → ℝ := sineKernel a
  let G : ℝ → ℝ := fun x => ∫ t in A..x, f t
  let u : ℝ → ℝ := fun x => Real.exp (-ε * x)
  let u' : ℝ → ℝ := fun x => -ε * Real.exp (-ε * x)
  let C : ℝ := 3 * (|a|⁻¹ * A⁻¹)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hfcont : Continuous f := continuous_sineKernel a
  have hGderiv : ∀ x : ℝ, HasDerivAt G (f x) x := by
    intro x
    exact intervalIntegral.integral_hasDerivAt_right
      (hfcont.intervalIntegrable A x) (hfcont.stronglyMeasurableAtFilter volume (𝓝 x))
      hfcont.continuousAt
  have hGcont : Continuous G := continuous_iff_continuousAt.mpr fun x => (hGderiv x).continuousAt
  have hGbound : ∀ x ∈ Ici A, |G x| ≤ C := by
    intro x hx
    change A ≤ x at hx
    rcases hx.eq_or_lt with rfl | hxlt
    · simpa [G] using! hC
    · exact sineKernel_tail_bound a A x ha hA hxlt.le
  have huDeriv : ∀ x : ℝ, HasDerivAt u (u' x) x := by
    intro x
    dsimp [u, u']
    convert! (((hasDerivAt_id x).const_mul (-ε)).exp) using 1
    simp only [id_eq]
    ring
  have hexp : IntegrableOn (fun x : ℝ => Real.exp (-ε * x)) (Ioi A) := by
    simpa only [neg_mul] using! integrableOn_exp_mul_Ioi (neg_lt_zero.mpr hε) A
  have huf : IntegrableOn (u * f) (Ioi A) := by
    apply (hexp.const_mul |a|).mono'
    · exact Continuous.aestronglyMeasurable
        ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul hfcont)
    · filter_upwards with x
      dsimp [u, f, sineKernel]
      change |Real.exp (-ε * x) * (a * Real.sinc (a * x))| ≤
        |a| * Real.exp (-ε * x)
      rw [abs_mul, abs_of_pos (Real.exp_pos _), abs_mul]
      calc
        Real.exp (-ε * x) * (|a| * |Real.sinc (a * x)|) ≤
            Real.exp (-ε * x) * (|a| * 1) := by
          gcongr
          exact Real.abs_sinc_le_one _
        _ = |a| * Real.exp (-ε * x) := by ring
  have huG : IntegrableOn (u' * G) (Ioi A) := by
    apply (hexp.const_mul (ε * C)).mono'
    · exact Continuous.aestronglyMeasurable ((continuous_const.mul
        (Real.continuous_exp.comp (continuous_const.mul continuous_id))).mul hGcont)
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      have hCx := hGbound x (mem_Ici.mpr (le_of_lt hx))
      dsimp [u', u, G, C] at hCx ⊢
      simp only [abs_mul, abs_neg, abs_of_pos hε, abs_of_pos (Real.exp_pos _)]
      calc
        ε * Real.exp (-ε * x) * |∫ t in A..x, f t| ≤
            ε * Real.exp (-ε * x) * (3 * (|a|⁻¹ * A⁻¹)) :=
          mul_le_mul_of_nonneg_left hCx (mul_nonneg hε.le (Real.exp_pos _).le)
        _ = ε * (3 * (|a|⁻¹ * A⁻¹)) * Real.exp (-ε * x) := by ring
  have hzeroA : Tendsto (u * G) (𝓝[>] A) (nhds 0) := by
    have hG0 : Tendsto G (𝓝[>] A) (nhds 0) := by
      have := (hGderiv A).continuousAt.tendsto
      simpa [G] using! this.mono_left inf_le_left
    have huA : Tendsto u (𝓝[>] A) (nhds (u A)) :=
      (Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousAt.tendsto.mono_left
        inf_le_left
    simpa only [Pi.mul_apply, mul_zero] using! huA.mul hG0
  have hzeroTop : Tendsto (u * G) atTop (nhds 0) := by
    have hu0 : Tendsto u atTop (nhds 0) := by
      exact Real.tendsto_exp_atBot.comp
        ((tendsto_const_mul_atBot_of_neg (neg_lt_zero.mpr hε)).2 tendsto_id)
    have hGbdd : IsBoundedUnder (· ≤ ·) atTop ((‖·‖) ∘ G) := by
      apply isBoundedUnder_of_eventually_le (a := C)
      filter_upwards [Ici_mem_atTop A] with x hx
      simpa only [Function.comp_apply, Real.norm_eq_abs] using! hGbound x hx
    simpa only [Pi.mul_apply] using! hu0.zero_mul_isBoundedUnder_le hGbdd
  have hparts := MeasureTheory.integral_Ioi_mul_deriv_eq_deriv_mul
    (a := A) (u := u) (v := G) (u' := u') (v' := f)
    (fun x hx => huDeriv x) (fun x hx => hGderiv x) huf huG hzeroA hzeroTop
  have hidentity :
      (∫ x in Ioi A, u x * f x) = ε * ∫ x in Ioi A, u x * G x := by
    rw [hparts]
    have hint : (∫ x in Ioi A, u' x * G x) =
        ∫ x in Ioi A, (-ε) * (u x * G x) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      dsimp [u', u]
      ring
    rw [hint, integral_const_mul]
    ring
  have huGnorm :
      |∫ x in Ioi A, u x * G x| ≤ C * ∫ x in Ioi A, Real.exp (-ε * x) := by
    have hInt : IntegrableOn (u * G) (Ioi A) := by
      apply (hexp.const_mul C).mono'
      · exact Continuous.aestronglyMeasurable
          ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul hGcont)
      · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
        have hCx := hGbound x (mem_Ici.mpr (le_of_lt hx))
        dsimp [u, G] at hCx ⊢
        rw [abs_mul, abs_of_pos (Real.exp_pos _)]
        calc
          Real.exp (-ε * x) * |∫ t in A..x, f t| ≤ Real.exp (-ε * x) * C :=
            mul_le_mul_of_nonneg_left hCx (Real.exp_pos _).le
          _ = C * Real.exp (-ε * x) := mul_comm _ _
    calc
      |∫ x in Ioi A, u x * G x| ≤ ∫ x in Ioi A, |u x * G x| := by
        simpa only [Real.norm_eq_abs] using!
          (norm_integral_le_integral_norm (μ := volume.restrict (Ioi A)) (u * G))
      _ ≤ ∫ x in Ioi A, C * Real.exp (-ε * x) := by
        apply setIntegral_mono_on hInt.abs (hexp.const_mul C) measurableSet_Ioi
        intro x hx
        have hCx := hGbound x (mem_Ici.mpr (le_of_lt hx))
        dsimp [u, G]
        rw [abs_mul, abs_of_pos (Real.exp_pos _)]
        nlinarith [Real.exp_pos (-ε * x)]
      _ = C * ∫ x in Ioi A, Real.exp (-ε * x) := integral_const_mul C _
  rw [hidentity, abs_mul, abs_of_pos hε]
  calc
    ε * |∫ x in Ioi A, u x * G x| ≤
        ε * (C * ∫ x in Ioi A, Real.exp (-ε * x)) :=
      mul_le_mul_of_nonneg_left huGnorm hε.le
    _ = C * Real.exp (-ε * A) := by
      rw [show (∫ x in Ioi A, Real.exp (-ε * x)) = Real.exp (-ε * A) / ε by
        have hval := integral_exp_mul_Ioi (neg_lt_zero.mpr hε) A
        simp only [neg_mul] at hval ⊢
        rw [hval]
        field_simp [hε.ne']]
      field_simp [hε.ne']
    _ ≤ C := by
      have hexple : Real.exp (-ε * A) ≤ 1 := by
        rw [← Real.exp_zero]
        exact Real.exp_le_exp.mpr (by nlinarith)
      exact mul_le_of_le_one_right hC hexple
    _ = 3 * (|a|⁻¹ * A⁻¹) := rfl

/-- A continuous representative of the finite Dirichlet integral. -/
def sineIntegralTruncation (a R : ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..R, sineKernel a x

@[simp]
theorem sineIntegralTruncation_one (R : ℝ) :
    sineIntegralTruncation 1 R =
      ∫ x in (0 : ℝ)..R, Real.sinc x := by
  unfold sineIntegralTruncation sineKernel
  simp

@[simp]
theorem dirichletSineLimit_one :
    dirichletSineLimit 1 = Real.pi / 2 := by
  simp [dirichletSineLimit]

private theorem tendsto_finite_damped_sineKernel (a A : ℝ) (hA : 0 < A) :
    Tendsto (fun ε : ℝ =>
      ∫ x in (0 : ℝ)..A, Real.exp (-ε * x) * sineKernel a x) (𝓝[>] 0)
      (nhds (sineIntegralTruncation a A)) := by
  let F : ℝ → ℝ → ℝ := fun ε x => Real.exp (-ε * x) * sineKernel a x
  have hcont : ContinuousWithinAt (fun ε : ℝ => ∫ x in (0 : ℝ)..A, F ε x)
      (Ioi 0) 0 := by
    apply intervalIntegral.continuousWithinAt_of_dominated_interval
        (bound := fun _x : ℝ => |a|)
    · filter_upwards with ε
      exact Continuous.aestronglyMeasurable
        ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul
          (continuous_sineKernel a))
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      filter_upwards with x hx
      rw [uIoc_of_le hA.le] at hx
      dsimp [F, sineKernel]
      rw [abs_mul, abs_of_pos (Real.exp_pos _), abs_mul]
      have hexple : Real.exp (-ε * x) ≤ 1 := by
        rw [← Real.exp_zero]
        exact Real.exp_le_exp.mpr
          (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hε.le) hx.1.le)
      calc
        Real.exp (-ε * x) * (|a| * |Real.sinc (a * x)|) ≤
            Real.exp (-ε * x) * (|a| * 1) := by
          gcongr
          exact Real.abs_sinc_le_one _
        _ ≤ 1 * (|a| * 1) :=
          mul_le_mul_of_nonneg_right hexple (mul_nonneg (abs_nonneg a) zero_le_one)
        _ = |a| := by ring
    · exact intervalIntegrable_const
    · filter_upwards with x hx
      exact ((Real.continuous_exp.comp (continuous_id.neg.mul continuous_const)).mul
        continuous_const).continuousAt.continuousWithinAt
  change Tendsto (fun ε : ℝ => ∫ x in (0 : ℝ)..A, F ε x) (𝓝[>] 0)
    (nhds (∫ x in (0 : ℝ)..A, F 0 x)) at hcont
  simpa [F, sineIntegralTruncation] using! hcont

private theorem dampedSineIntegral_split (ε a A : ℝ) (hε : 0 < ε) (hA : 0 < A) :
    dampedSineIntegral ε a =
      (∫ x in (0 : ℝ)..A, Real.exp (-ε * x) * sineKernel a x) +
      ∫ x in Ioi A, Real.exp (-ε * x) * sineKernel a x := by
  let h : ℝ → ℝ := fun x => Real.exp (-ε * x) * sineKernel a x
  have hexp : IntegrableOn (fun x : ℝ => Real.exp (-ε * x)) (Ioi (0 : ℝ)) := by
    simpa only [neg_mul] using! integrableOn_exp_mul_Ioi (neg_lt_zero.mpr hε) 0
  have hh : IntegrableOn h (Ioi (0 : ℝ)) := by
    apply (hexp.const_mul |a|).mono'
    · exact Continuous.aestronglyMeasurable
        ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul
          (continuous_sineKernel a))
    · filter_upwards with x
      dsimp [h, sineKernel]
      change |Real.exp (-ε * x) * (a * Real.sinc (a * x))| ≤
        |a| * Real.exp (-ε * x)
      rw [abs_mul, abs_of_pos (Real.exp_pos _), abs_mul]
      calc
        Real.exp (-ε * x) * (|a| * |Real.sinc (a * x)|) ≤
            Real.exp (-ε * x) * (|a| * 1) := by
          gcongr
          exact Real.abs_sinc_le_one _
        _ = |a| * Real.exp (-ε * x) := by ring
  calc
    dampedSineIntegral ε a = ∫ x in Ioi (0 : ℝ), h x := by
      unfold dampedSineIntegral
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      dsimp [h]
      rw [sineKernel_eq a (ne_of_gt hx)]
    _ = (∫ x in Ioc (0 : ℝ) A, h x) + ∫ x in Ioi A, h x := by
      rw [← setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi,
        Ioc_union_Ioi_eq_Ioi hA.le]
      · exact hh.mono_set Ioc_subset_Ioi_self
      · exact hh.mono_set (Ioi_subset_Ioi hA.le)
    _ = (∫ x in (0 : ℝ)..A, Real.exp (-ε * x) * sineKernel a x) +
        ∫ x in Ioi A, Real.exp (-ε * x) * sineKernel a x := by
      rw [intervalIntegral.integral_of_le hA.le]

private theorem sineIntegralTruncation_center_error (a A : ℝ) (ha : a ≠ 0) (hA : 0 < A) :
    |dirichletSineLimit a - sineIntegralTruncation a A| ≤
      3 * (|a|⁻¹ * A⁻¹) := by
  let E : ℝ → ℝ := fun ε =>
    ∫ x in (0 : ℝ)..A, Real.exp (-ε * x) * sineKernel a x
  have hlim : Tendsto (fun ε : ℝ => |dampedSineIntegral ε a - E ε|) (𝓝[>] 0)
      (nhds |dirichletSineLimit a - sineIntegralTruncation a A|) :=
    (tendsto_dampedSineIntegral_nhdsGT_zero a).sub
      (tendsto_finite_damped_sineKernel a A hA) |>.abs
  apply le_of_tendsto hlim
  filter_upwards [self_mem_nhdsWithin] with ε hε
  rw [dampedSineIntegral_split ε a A hε hA]
  change |((E ε + ∫ x in Ioi A, Real.exp (-ε * x) * sineKernel a x) - E ε)| ≤ _
  rw [add_sub_cancel_left]
  exact damped_sineKernel_tail_bound ε a A hε ha hA

/-- Public quantitative form of the Dirichlet sine-integral tail estimate.
It is exported for the Fourier coefficient bound in the nearest-cell window
argument. -/
theorem abs_dirichletSineLimit_sub_sineIntegralTruncation_le
    (a A : ℝ) (ha : a ≠ 0) (hA : 0 < A) :
    |dirichletSineLimit a - sineIntegralTruncation a A| ≤
      3 * (|a|⁻¹ * A⁻¹) :=
  sineIntegralTruncation_center_error a A ha hA

private theorem sineIntegralTruncation_sub_bound (a A R : ℝ)
    (ha : a ≠ 0) (hA : 0 < A) (hAR : A ≤ R) :
    |sineIntegralTruncation a R - sineIntegralTruncation a A| ≤
      3 * (|a|⁻¹ * A⁻¹) := by
  have hcont := continuous_sineKernel a
  have h0A : IntervalIntegrable (sineKernel a) volume (0 : ℝ) A :=
    hcont.intervalIntegrable 0 A
  have hARint : IntervalIntegrable (sineKernel a) volume A R :=
    hcont.intervalIntegrable A R
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    h0A hARint
  have hdiff : sineIntegralTruncation a R - sineIntegralTruncation a A =
      ∫ x in A..R, sineKernel a x := by
    unfold sineIntegralTruncation
    rw [← hadd]
    ring
  rw [hdiff]
  exact sineKernel_tail_bound a A R ha hA hAR

/-- The ordinary (undamped) Dirichlet integral, obtained from the proved Abel
limit using uniform oscillatory-tail estimates. -/
theorem tendsto_sineIntegralTruncation_atTop (a : ℝ) :
    Tendsto (sineIntegralTruncation a) atTop (nhds (dirichletSineLimit a)) := by
  by_cases ha : a = 0
  · subst a
    have hz : sineIntegralTruncation 0 = fun _R : ℝ => 0 := by
      funext R
      simp [sineIntegralTruncation, sineKernel]
    rw [hz]
    simp [dirichletSineLimit]
  rw [Metric.tendsto_atTop]
  intro η hη
  have hsmall : Tendsto (fun A : ℝ => 6 * (|a|⁻¹ * A⁻¹)) atTop (nhds 0) := by
    have hconst6 : Tendsto (fun _A : ℝ => (6 : ℝ)) atTop (nhds 6) := tendsto_const_nhds
    have hconsta : Tendsto (fun _A : ℝ => |a|⁻¹) atTop (nhds |a|⁻¹) := tendsto_const_nhds
    simpa only [mul_zero] using! hconst6.mul (hconsta.mul tendsto_inv_atTop_zero)
  have hevent : ∀ᶠ A : ℝ in atTop, 0 < A ∧ 6 * (|a|⁻¹ * A⁻¹) < η := by
    filter_upwards [Ioi_mem_atTop (0 : ℝ), hsmall.eventually (Iio_mem_nhds hη)] with A hA hbound
    exact ⟨hA, hbound⟩
  rcases hevent.exists with ⟨A, hA, hbound⟩
  refine ⟨A, fun R hAR => ?_⟩
  rw [Real.dist_eq]
  calc
    |sineIntegralTruncation a R - dirichletSineLimit a| =
        |(sineIntegralTruncation a R - sineIntegralTruncation a A) +
          (sineIntegralTruncation a A - dirichletSineLimit a)| := by congr 1; ring
    _ ≤ |sineIntegralTruncation a R - sineIntegralTruncation a A| +
        |sineIntegralTruncation a A - dirichletSineLimit a| := abs_add_le _ _
    _ ≤ 3 * (|a|⁻¹ * A⁻¹) + 3 * (|a|⁻¹ * A⁻¹) := by
      apply add_le_add (sineIntegralTruncation_sub_bound a A R ha hA hAR)
      simpa only [abs_sub_comm] using! sineIntegralTruncation_center_error a A ha hA
    _ = 6 * (|a|⁻¹ * A⁻¹) := by ring
    _ < η := hbound

/-- Finite symmetric pairing of the exponential kernel. -/
def symmetricExponentialTruncation (a R : ℝ) : ℂ :=
  ∫ x in (0 : ℝ)..R, (paperExp (-a * x) - paperExp (a * x)) / (x : ℂ)

theorem symmetricExponentialTruncation_eq (a R : ℝ) :
    symmetricExponentialTruncation a R =
      (-2 * Complex.I) * (sineIntegralTruncation (2 * Real.pi * a) R : ℂ) := by
  let f : ℝ → ℝ := sineKernel (2 * Real.pi * a)
  calc
    symmetricExponentialTruncation a R =
        ∫ x in (0 : ℝ)..R, (-2 * Complex.I) * (f x : ℂ) := by
      unfold symmetricExponentialTruncation
      apply intervalIntegral.integral_congr_ae
      filter_upwards [(volume : Measure ℝ).ae_ne 0] with x hx0 hxmem
      have harg : 2 * Real.pi * (-a * x) = -(2 * Real.pi * a * x) := by ring
      have hdiff : paperExp (-a * x) - paperExp (a * x) =
          (-2 * Complex.I) * (Real.sin (2 * Real.pi * a * x) : ℂ) := by
        rw [paperExp_eq_cos_add_sin_mul_I, paperExp_eq_cos_add_sin_mul_I, harg,
          Real.cos_neg, Real.sin_neg]
        push_cast
        ring_nf
      rw [hdiff]
      dsimp [f]
      rw [sineKernel_eq (2 * Real.pi * a) hx0]
      push_cast
      have hxc : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx0
      apply (mul_right_cancel₀ hxc)
      simp
      ring
    _ = (-2 * Complex.I) * ∫ x in (0 : ℝ)..R, (f x : ℂ) := by
      rw [intervalIntegral.integral_const_mul]
    _ = (-2 * Complex.I) * (∫ x in (0 : ℝ)..R, f x : ℝ) := by
      congr 1
      exact intervalIntegral.integral_ofReal
    _ = (-2 * Complex.I) * (sineIntegralTruncation (2 * Real.pi * a) R : ℂ) := by rfl

/-- The genuine symmetric-truncation exponential identity. -/
theorem tendsto_symmetricExponentialTruncation_atTop (a : ℝ) :
    Tendsto (symmetricExponentialTruncation a) atTop (nhds (signedExponentialPV a)) := by
  have hsine := tendsto_sineIntegralTruncation_atTop (2 * Real.pi * a)
  have hcast : Tendsto
      (fun R : ℝ => (sineIntegralTruncation (2 * Real.pi * a) R : ℂ)) atTop
      (nhds (dirichletSineLimit (2 * Real.pi * a) : ℂ)) :=
    (Complex.continuous_ofReal.tendsto _).comp hsine
  have hmul : Tendsto
      (fun R : ℝ => (-2 * Complex.I) *
        (sineIntegralTruncation (2 * Real.pi * a) R : ℂ)) atTop
      (nhds ((-2 * Complex.I) * (dirichletSineLimit (2 * Real.pi * a) : ℂ))) :=
    (tendsto_const_nhds : Tendsto (fun _R : ℝ => (-2 * Complex.I)) atTop
      (nhds (-2 * Complex.I))).mul hcast
  rw [signedExponentialPV_eq_dirichlet]
  apply hmul.congr'
  filter_upwards with R
  exact (symmetricExponentialTruncation_eq a R).symm

/-! ## The absolutely convergent cosine expansion of `V` -/

private theorem cosine_square_sum_on_cell (z : ℝ) (hz : z ∈ Icc (0 : ℝ) 1) :
    HasSum (fun n : ℕ => 1 / (n : ℝ) ^ 2 * Real.cos (2 * Real.pi * n * z))
      (Real.pi ^ 2 * (z ^ 2 - z + 1 / 6)) := by
  have h := hasSum_one_div_nat_pow_mul_cos (k := 1) one_ne_zero hz
  convert! h using 1
  norm_num
  rw [Polynomial.aeval_def, ← Polynomial.eval_map]
  change Real.pi ^ 2 * (z ^ 2 - z + 1 / 6) =
    (2 * Real.pi) ^ 2 / 2 / 2 * bernoulliFun 2 z
  rw [bernoulliFun_two]
  ring

private theorem cosine_difference_sum_on_cell (z : ℝ) (hz : z ∈ Icc (0 : ℝ) 1) :
    HasSum (fun n : ℕ => (1 - Real.cos (2 * Real.pi * n * z)) /
      (2 * Real.pi ^ 2 * (n : ℝ) ^ 2)) (z * (1 - z) / 2) := by
  have h0 : HasSum (fun n : ℕ => 1 / (n : ℝ) ^ 2 * Real.cos (2 * Real.pi * n * 0))
      (Real.pi ^ 2 * ((0 : ℝ) ^ 2 - 0 + 1 / 6)) := by
    exact cosine_square_sum_on_cell 0 (by norm_num)
  have hzsum := cosine_square_sum_on_cell z hz
  have hmul := (h0.sub hzsum).mul_left (1 / (2 * Real.pi ^ 2))
  convert! hmul using 1
  · ext n
    by_cases hn : n = 0
    · subst n
      simp
    · field_simp [Real.pi_ne_zero, hn]
      simp
  · field_simp [Real.pi_ne_zero]
    ring

private theorem cos_mul_eq_cos_mul_fract (n : ℕ) (y : ℝ) :
    Real.cos (2 * Real.pi * n * y) = Real.cos (2 * Real.pi * n * Int.fract y) := by
  conv_lhs => rw [← Int.floor_add_fract y]
  rw [show 2 * Real.pi * (n : ℝ) * ((⌊y⌋ : ℝ) + Int.fract y) =
      2 * Real.pi * (n : ℝ) * Int.fract y + (((n : ℤ) * ⌊y⌋ : ℤ) : ℝ) *
        (2 * Real.pi) by push_cast; ring]
  exact Real.cos_add_int_mul_two_pi _ _

/-- The pointwise, absolutely convergent cosine expansion
`V(y) = Σₙ (1 - cos(2πny)) / (2π²n²)`.  The `n = 0` term is zero. -/
theorem hasSum_bernoulliMark_cosine (y : ℝ) :
    HasSum (fun n : ℕ => (1 - Real.cos (2 * Real.pi * n * y)) /
      (2 * Real.pi ^ 2 * (n : ℝ) ^ 2)) (bernoulliMark y) := by
  have hz : Int.fract y ∈ Icc (0 : ℝ) 1 :=
    ⟨Int.fract_nonneg y, (Int.fract_lt_one y).le⟩
  have h := cosine_difference_sum_on_cell (Int.fract y) hz
  have hfun :
      (fun n : ℕ => (1 - Real.cos (2 * Real.pi * n * Int.fract y)) /
        (2 * Real.pi ^ 2 * (n : ℝ) ^ 2)) =
      (fun n : ℕ => (1 - Real.cos (2 * Real.pi * n * y)) /
        (2 * Real.pi ^ 2 * (n : ℝ) ^ 2)) := by
    funext n
    rw [cos_mul_eq_cos_mul_fract n y]
  change HasSum _ (Int.fract y * (1 - Int.fract y) / 2)
  rw [← hfun]
  exact h

/-! ## Pairing the Bernoulli transform on the positive half-axis -/

/-- The periodic Bernoulli mark is even.  The proof includes the integral
points, where the usual formula `fract (-x) = 1 - fract x` has an exceptional
case. -/
theorem bernoulliMark_neg (x : ℝ) : bernoulliMark (-x) = bernoulliMark x := by
  by_cases hx : Int.fract x = 0
  · have hnx : Int.fract (-x) = 0 := Int.fract_neg_eq_zero.mpr hx
    simp [bernoulliMark, hx, hnx]
  · rw [bernoulliMark, bernoulliMark, Int.fract_neg hx]
    ring

/-- The continuous extension at zero of
`(e(-sx)-e(sx))/x`. -/
private def pairedKernel (s x : ℝ) : ℂ :=
  (-2 * Complex.I) * (sineKernel (2 * Real.pi * s) x : ℂ)

private theorem continuous_pairedKernel (s : ℝ) : Continuous (pairedKernel s) := by
  exact continuous_const.mul
    (Complex.continuous_ofReal.comp (continuous_sineKernel (2 * Real.pi * s)))

private theorem pairedKernel_eq (s : ℝ) {x : ℝ} (hx : x ≠ 0) :
    pairedKernel s x = (paperExp (-s * x) - paperExp (s * x)) / (x : ℂ) := by
  have harg : 2 * Real.pi * (-s * x) = -(2 * Real.pi * s * x) := by ring
  have hdiff : paperExp (-s * x) - paperExp (s * x) =
      (-2 * Complex.I) * (Real.sin (2 * Real.pi * s * x) : ℂ) := by
    rw [paperExp_eq_cos_add_sin_mul_I, paperExp_eq_cos_add_sin_mul_I, harg,
      Real.cos_neg, Real.sin_neg]
    push_cast
    ring_nf
  rw [pairedKernel, sineKernel_eq (2 * Real.pi * s) hx, hdiff]
  push_cast
  rw [div_eq_mul_inv]
  ring

/-- The positive-half-axis form of the paired Bernoulli transform. -/
def bernoulliPairedTruncation (N : ℕ) (s R : ℝ) : ℂ :=
  ∫ x in (0 : ℝ)..R, (bernoulliMark ((N : ℝ) * x) : ℂ) * pairedKernel s x

theorem transformKernel_neg (N : ℕ) {x : ℝ} (hx : x ≠ 0) :
    transformKernel N (-x) = -transformKernel N x := by
  rw [transformKernel, transformKernel, if_neg (neg_ne_zero.mpr hx), if_neg hx]
  rw [show (N : ℝ) * -x = -((N : ℝ) * x) by ring, bernoulliMark_neg]
  ring

/-- The totalized transform kernel is odd, including its chosen value at
the origin. -/
theorem transformKernel_odd (N : ℕ) : Function.Odd (transformKernel N) := by
  intro x
  by_cases hx : x = 0
  · subst x
    simp [transformKernel]
  · exact transformKernel_neg N hx

private theorem bernoulliMark_le_div_two_of_nonneg (y : ℝ) (hy : 0 ≤ y) :
    bernoulliMark y ≤ y / 2 := by
  have hfloor : (0 : ℝ) ≤ (⌊y⌋ : ℤ) := by exact_mod_cast Int.floor_nonneg.mpr hy
  have hfract_le : Int.fract y ≤ y := by
    rw [Int.fract]
    linarith
  have hfract0 := Int.fract_nonneg y
  have hfract1 := (Int.fract_lt_one y).le
  dsimp [bernoulliMark]
  nlinarith

private theorem bernoulliMark_le_abs_div_two (y : ℝ) :
    bernoulliMark y ≤ |y| / 2 := by
  rcases le_total 0 y with hy | hy
  · rw [abs_of_nonneg hy]
    exact bernoulliMark_le_div_two_of_nonneg y hy
  · have hny : 0 ≤ -y := neg_nonneg.mpr hy
    rw [← bernoulliMark_neg y, ← abs_neg y, abs_of_nonneg hny]
    exact bernoulliMark_le_div_two_of_nonneg (-y) hny

private theorem transformKernel_measurable (N : ℕ) : Measurable (transformKernel N) := by
  unfold transformKernel
  exact Measurable.ite (by simpa only [Set.setOf_eq_eq_singleton] using!
      (measurableSet_singleton (0 : ℝ))) measurable_const
    ((bernoulliMark_measurable.comp (measurable_const.mul measurable_id)).div measurable_id)

private theorem continuous_paperExp : Continuous paperExp := by
  unfold paperExp
  fun_prop

private theorem norm_paperExp (t : ℝ) : ‖paperExp t‖ = 1 := by
  rw [paperExp, Complex.norm_exp]
  simp

private theorem norm_transformKernel_le (N : ℕ) (x : ℝ) :
    ‖transformKernel N x‖ ≤ (N : ℝ) / 2 := by
  by_cases hx : x = 0
  · simp [transformKernel, hx, div_nonneg]
  · rw [transformKernel, if_neg hx, Real.norm_eq_abs, abs_div]
    rw [abs_of_nonneg (bernoulliMark_nonneg _)]
    have hxabs : 0 < |x| := abs_pos.mpr hx
    apply (div_le_iff₀ hxabs).2
    calc
      bernoulliMark ((N : ℝ) * x) ≤ |(N : ℝ) * x| / 2 :=
        bernoulliMark_le_abs_div_two _
      _ = ((N : ℝ) / 2) * |x| := by
        rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg N)]
        ring

private theorem principalValueIntegrand_intervalIntegrable (N : ℕ) (s a b : ℝ) :
    IntervalIntegrable
      (fun x => (transformKernel N x : ℂ) * paperExp (-s * x)) volume a b := by
  apply (intervalIntegrable_const (c := ((N : ℝ) / 2))).mono_fun
  · exact ((transformKernel_measurable N).complex_ofReal.mul
      (continuous_paperExp.comp (continuous_const.mul continuous_id)).measurable).aestronglyMeasurable
  · filter_upwards with x
    rw [norm_mul, Complex.norm_real, norm_paperExp, mul_one]
    have hN : 0 ≤ (N : ℝ) / 2 := div_nonneg (Nat.cast_nonneg N) (by norm_num)
    change |transformKernel N x| ≤ |(N : ℝ) / 2|
    rw [abs_of_nonneg hN]
    simpa only [Real.norm_eq_abs] using! norm_transformKernel_le N x

/-- Splitting at zero and reflecting the negative half-axis produces the
continuous paired kernel.  Oriented interval integrals make the identity
valid for every real truncation parameter. -/
theorem principalValueTruncation_eq_paired (N : ℕ) (s R : ℝ) :
    principalValueTruncation N s R = bernoulliPairedTruncation N s R := by
  let f : ℝ → ℂ := fun x => (transformKernel N x : ℂ) * paperExp (-s * x)
  have hf : IntervalIntegrable f volume (-R) 0 ∧ IntervalIntegrable f volume 0 R :=
    ⟨principalValueIntegrand_intervalIntegrable N s (-R) 0,
      principalValueIntegrand_intervalIntegrable N s 0 R⟩
  have hadd := intervalIntegral.integral_add_adjacent_intervals hf.1 hf.2
  unfold principalValueTruncation
  change (∫ x in -R..R, f x) = _
  rw [← hadd]
  have hreflect : (∫ x in -R..0, f x) = ∫ x in 0..R, f (-x) := by
    have h := (intervalIntegral.integral_comp_neg (f := f) (a := 0) (b := R)).symm
    simp only [neg_zero] at h
    exact h
  have hfneg : IntervalIntegrable (fun x => f (-x)) volume 0 R := by
    apply (intervalIntegrable_const (c := ((N : ℝ) / 2))).mono_fun
    · exact (((transformKernel_measurable N).comp measurable_neg).complex_ofReal.mul
        (continuous_paperExp.comp
          (continuous_const.mul continuous_neg)).measurable).aestronglyMeasurable
    · filter_upwards with x
      dsimp [f]
      rw [norm_mul, Complex.norm_real, norm_paperExp, mul_one]
      have hN : 0 ≤ (N : ℝ) / 2 := div_nonneg (Nat.cast_nonneg N) (by norm_num)
      change |transformKernel N (-x)| ≤ |(N : ℝ) / 2|
      rw [abs_of_nonneg hN]
      simpa only [Real.norm_eq_abs] using! norm_transformKernel_le N (-x)
  rw [hreflect]
  unfold bernoulliPairedTruncation
  rw [← intervalIntegral.integral_add hfneg hf.2]
  apply intervalIntegral.integral_congr_ae
  filter_upwards [(volume : Measure ℝ).ae_ne 0] with x hx hxmem
  dsimp [f]
  rw [transformKernel_neg N hx]
  change ((-(transformKernel N x) : ℝ) : ℂ) * paperExp (-s * -x) +
      (transformKernel N x : ℂ) * paperExp (-s * x) =
    (bernoulliMark ((N : ℝ) * x) : ℂ) * pairedKernel s x
  rw [transformKernel, if_neg hx, pairedKernel_eq s hx]
  push_cast
  field_simp [hx]
  ring_nf

/-! ## Termwise integration of the absolutely convergent cosine series -/

def bernoulliCosineTerm (k : ℕ) (y : ℝ) : ℝ :=
  (1 - Real.cos (2 * Real.pi * k * y)) /
    (2 * Real.pi ^ 2 * (k : ℝ) ^ 2)

/-- The contribution of the `k`-th cosine mode to the paired truncation. -/
def bernoulliModeTruncation (N : ℕ) (s : ℝ) (k : ℕ) (R : ℝ) : ℂ :=
  ∫ x in (0 : ℝ)..R,
    (bernoulliCosineTerm k ((N : ℝ) * x) : ℂ) * pairedKernel s x

private def bernoulliModeBound (s : ℝ) (k : ℕ) : ℝ :=
  (2 * (2 * |2 * Real.pi * s|) / (2 * Real.pi ^ 2)) *
    (1 / (k : ℝ) ^ 2)

private theorem norm_pairedKernel_le (s x : ℝ) :
    ‖pairedKernel s x‖ ≤ 2 * |2 * Real.pi * s| := by
  rw [pairedKernel, norm_mul, Complex.norm_real]
  have htwo : ‖(-2 : ℂ) * Complex.I‖ = 2 := by norm_num
  rw [htwo]
  dsimp [sineKernel]
  rw [abs_mul]
  calc
    2 * (|2 * Real.pi * s| * |Real.sinc (2 * Real.pi * s * x)|) ≤
        2 * (|2 * Real.pi * s| * 1) := by
      gcongr
      exact Real.abs_sinc_le_one _
    _ = 2 * |2 * Real.pi * s| := by ring

private theorem norm_bernoulliMode_integrand_le (N k : ℕ) (s x : ℝ) :
    ‖(bernoulliCosineTerm k ((N : ℝ) * x) : ℂ) * pairedKernel s x‖ ≤
      bernoulliModeBound s k := by
  by_cases hk : k = 0
  · subst k
    simp [bernoulliCosineTerm, bernoulliModeBound]
  · have hkpos : 0 < (k : ℝ) ^ 2 := sq_pos_of_ne_zero (Nat.cast_ne_zero.mpr hk)
    have hden : 0 < 2 * Real.pi ^ 2 * (k : ℝ) ^ 2 := by positivity
    have hcos :
        |1 - Real.cos (2 * Real.pi * k * ((N : ℝ) * x))| ≤ 2 := by
      rw [abs_le]
      constructor
      · linarith [Real.cos_le_one (2 * Real.pi * k * ((N : ℝ) * x))]
      · linarith [Real.neg_one_le_cos (2 * Real.pi * k * ((N : ℝ) * x))]
    rw [norm_mul, Complex.norm_real]
    have hcoef :
        |bernoulliCosineTerm k ((N : ℝ) * x)| ≤
          2 / (2 * Real.pi ^ 2 * (k : ℝ) ^ 2) := by
      rw [bernoulliCosineTerm, abs_div, abs_of_pos hden]
      exact div_le_div_of_nonneg_right hcos hden.le
    calc
      |bernoulliCosineTerm k ((N : ℝ) * x)| * ‖pairedKernel s x‖ ≤
          (2 / (2 * Real.pi ^ 2 * (k : ℝ) ^ 2)) *
            (2 * |2 * Real.pi * s|) :=
        mul_le_mul hcoef (norm_pairedKernel_le s x) (norm_nonneg _) (by positivity)
      _ = bernoulliModeBound s k := by
        unfold bernoulliModeBound
        field_simp [Real.pi_ne_zero, hk]

private theorem summable_bernoulliModeBound (s : ℝ) :
    Summable (bernoulliModeBound s) := by
  unfold bernoulliModeBound
  exact (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < (2 : ℕ))).mul_left _

/-- The pointwise cosine expansion of `V` may be integrated term by term on
every finite interval.  The displayed `k⁻²` majorant is independent of the
truncation parameter and will also justify passage to the principal-value
limit below. -/
theorem hasSum_bernoulliModeTruncation (N : ℕ) (s R : ℝ) :
    HasSum (fun k : ℕ => bernoulliModeTruncation N s k R)
      (bernoulliPairedTruncation N s R) := by
  unfold bernoulliModeTruncation bernoulliPairedTruncation
  apply intervalIntegral.hasSum_integral_of_dominated_convergence
      (fun k _x => bernoulliModeBound s k)
  · intro k
    exact Continuous.aestronglyMeasurable (by
      apply Continuous.mul
      · exact Complex.continuous_ofReal.comp (by
          unfold bernoulliCosineTerm
          fun_prop)
      · exact continuous_pairedKernel s)
  · intro k
    filter_upwards with x hx
    exact norm_bernoulliMode_integrand_le N k s x
  · filter_upwards with x hx
    exact summable_bernoulliModeBound s
  · change IntervalIntegrable (fun _x : ℝ => ∑' k : ℕ, bernoulliModeBound s k)
      volume 0 R
    exact intervalIntegrable_const
  · filter_upwards with x hx
    have hreal := hasSum_bernoulliMark_cosine ((N : ℝ) * x)
    change HasSum (fun k : ℕ => bernoulliCosineTerm k ((N : ℝ) * x))
      (bernoulliMark ((N : ℝ) * x)) at hreal
    exact (Complex.hasSum_ofReal.mpr hreal).mul_right (pairedKernel s x)

/-! ## Exact evaluation of one cosine mode -/

private theorem paperExp_mul (u v : ℝ) :
    paperExp u * paperExp v = paperExp (u + v) := by
  unfold paperExp
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

private theorem cosine_eq_paperExp_average (t : ℝ) :
    (Real.cos (2 * Real.pi * t) : ℂ) =
      (paperExp t + paperExp (-t)) / 2 := by
  rw [paperExp_eq_cos_add_sin_mul_I, paperExp_eq_cos_add_sin_mul_I]
  have harg : 2 * Real.pi * -t = -(2 * Real.pi * t) := by ring
  rw [harg, Real.cos_neg, Real.sin_neg]
  push_cast
  ring

def bernoulliModeClosedForm (N : ℕ) (s : ℝ) (k : ℕ) (R : ℝ) : ℂ :=
  ((1 / (2 * Real.pi ^ 2 * (k : ℝ) ^ 2) : ℝ) : ℂ) *
    (symmetricExponentialTruncation s R -
      (1 / 2 : ℂ) * symmetricExponentialTruncation (s - (k : ℝ) * N) R -
      (1 / 2 : ℂ) * symmetricExponentialTruncation (s + (k : ℝ) * N) R)

private theorem bernoulliMode_integrand_eq (N k : ℕ) (s : ℝ) {x : ℝ}
    (hx : x ≠ 0) :
    (bernoulliCosineTerm k ((N : ℝ) * x) : ℂ) * pairedKernel s x =
      ((1 / (2 * Real.pi ^ 2 * (k : ℝ) ^ 2) : ℝ) : ℂ) *
        (pairedKernel s x - (1 / 2 : ℂ) * pairedKernel (s - (k : ℝ) * N) x -
          (1 / 2 : ℂ) * pairedKernel (s + (k : ℝ) * N) x) := by
  rw [pairedKernel, pairedKernel, pairedKernel,
    sineKernel_eq (2 * Real.pi * s) hx,
    sineKernel_eq (2 * Real.pi * (s - (k : ℝ) * N)) hx,
    sineKernel_eq (2 * Real.pi * (s + (k : ℝ) * N)) hx]
  have hcos : 2 * Real.pi * (k : ℝ) * ((N : ℝ) * x) =
      2 * Real.pi * ((k : ℝ) * N) * x := by ring
  have hminus : 2 * Real.pi * (s - (k : ℝ) * N) * x =
      2 * Real.pi * s * x - 2 * Real.pi * ((k : ℝ) * N) * x := by ring
  have hplus : 2 * Real.pi * (s + (k : ℝ) * N) * x =
      2 * Real.pi * s * x + 2 * Real.pi * ((k : ℝ) * N) * x := by ring
  unfold bernoulliCosineTerm
  rw [hcos, hminus, hplus, Real.sin_sub, Real.sin_add]
  push_cast
  ring

private theorem intervalIntegral_pairedKernel (a R : ℝ) :
    (∫ x in (0 : ℝ)..R, pairedKernel a x) = symmetricExponentialTruncation a R := by
  rw [symmetricExponentialTruncation_eq]
  unfold pairedKernel sineIntegralTruncation
  rw [intervalIntegral.integral_const_mul]
  congr 1
  exact intervalIntegral.integral_ofReal

/-- Exact finite-truncation formula for one cosine mode.  This identity is
proved before taking any limit, so no hidden interchange of a principal value
and a Fourier series occurs. -/
theorem bernoulliModeTruncation_eq_closedForm (N k : ℕ) (s R : ℝ) :
    bernoulliModeTruncation N s k R = bernoulliModeClosedForm N s k R := by
  unfold bernoulliModeTruncation bernoulliModeClosedForm
  have hcont (a : ℝ) : IntervalIntegrable (pairedKernel a) volume 0 R :=
    (continuous_pairedKernel a).intervalIntegrable 0 R
  calc
    (∫ x in (0 : ℝ)..R,
        (bernoulliCosineTerm k ((N : ℝ) * x) : ℂ) * pairedKernel s x) =
      ∫ x in (0 : ℝ)..R,
        ((1 / (2 * Real.pi ^ 2 * (k : ℝ) ^ 2) : ℝ) : ℂ) *
          (pairedKernel s x - (1 / 2 : ℂ) * pairedKernel (s - (k : ℝ) * N) x -
            (1 / 2 : ℂ) * pairedKernel (s + (k : ℝ) * N) x) := by
        apply intervalIntegral.integral_congr_ae
        filter_upwards [(volume : Measure ℝ).ae_ne 0] with x hx hxmem
        exact bernoulliMode_integrand_eq N k s hx
    _ = ((1 / (2 * Real.pi ^ 2 * (k : ℝ) ^ 2) : ℝ) : ℂ) *
        (∫ x in (0 : ℝ)..R,
          (pairedKernel s x - (1 / 2 : ℂ) * pairedKernel (s - (k : ℝ) * N) x -
            (1 / 2 : ℂ) * pairedKernel (s + (k : ℝ) * N) x)) := by
      rw [intervalIntegral.integral_const_mul]
    _ = ((1 / (2 * Real.pi ^ 2 * (k : ℝ) ^ 2) : ℝ) : ℂ) *
        ((∫ x in (0 : ℝ)..R, pairedKernel s x) -
          (1 / 2 : ℂ) * (∫ x in (0 : ℝ)..R, pairedKernel (s - (k : ℝ) * N) x) -
          (1 / 2 : ℂ) * (∫ x in (0 : ℝ)..R, pairedKernel (s + (k : ℝ) * N) x)) := by
      congr 1
      rw [intervalIntegral.integral_sub
          ((hcont s).sub ((hcont (s - (k : ℝ) * N)).const_mul (1 / 2)))
          ((hcont (s + (k : ℝ) * N)).const_mul (1 / 2)),
        intervalIntegral.integral_sub (hcont s)
          ((hcont (s - (k : ℝ) * N)).const_mul (1 / 2)),
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
    _ = ((1 / (2 * Real.pi ^ 2 * (k : ℝ) ^ 2) : ℝ) : ℂ) *
        (symmetricExponentialTruncation s R -
          (1 / 2 : ℂ) * symmetricExponentialTruncation (s - (k : ℝ) * N) R -
          (1 / 2 : ℂ) * symmetricExponentialTruncation (s + (k : ℝ) * N) R) := by
      rw [intervalIntegral_pairedKernel, intervalIntegral_pairedKernel,
        intervalIntegral_pairedKernel]

/-! ## A summable majorant uniform in the truncation radius -/

private theorem abs_sineKernel_le (a x : ℝ) : |sineKernel a x| ≤ |a| := by
  unfold sineKernel
  rw [abs_mul]
  calc
    |a| * |Real.sinc (a * x)| ≤ |a| * 1 := by
      gcongr
      exact Real.abs_sinc_le_one _
    _ = |a| := mul_one _

private theorem abs_sineIntegralTruncation_le_mul (a R : ℝ) (hR : 0 ≤ R) :
    |sineIntegralTruncation a R| ≤ |a| * R := by
  unfold sineIntegralTruncation
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (f := sineKernel a) (a := (0 : ℝ)) (b := R) (C := |a|)
    (fun x hx => by simpa only [Real.norm_eq_abs] using! abs_sineKernel_le a x)
  simpa only [Real.norm_eq_abs, sub_zero, abs_of_nonneg hR] using! h

private theorem abs_sineIntegralTruncation_le_four (a R : ℝ) (hR : 0 ≤ R) :
    |sineIntegralTruncation a R| ≤ 4 := by
  by_cases ha : a = 0
  · subst a
    simp [sineIntegralTruncation, sineKernel]
  let A : ℝ := |a|⁻¹
  have haabs : 0 < |a| := abs_pos.mpr ha
  have hA : 0 < A := inv_pos.mpr haabs
  rcases le_total R A with hRA | hAR
  · calc
      |sineIntegralTruncation a R| ≤ |a| * R :=
        abs_sineIntegralTruncation_le_mul a R hR
      _ ≤ |a| * A := mul_le_mul_of_nonneg_left hRA (abs_nonneg a)
      _ = 1 := by
        dsimp [A]
        exact mul_inv_cancel₀ (ne_of_gt haabs)
      _ ≤ 4 := by norm_num
  · calc
      |sineIntegralTruncation a R| ≤
          |sineIntegralTruncation a R - sineIntegralTruncation a A| +
            |sineIntegralTruncation a A| := by
        calc
          |sineIntegralTruncation a R| =
              |(sineIntegralTruncation a R - sineIntegralTruncation a A) +
                sineIntegralTruncation a A| := by congr 1; ring
          _ ≤ |sineIntegralTruncation a R - sineIntegralTruncation a A| +
              |sineIntegralTruncation a A| := abs_add_le _ _
      _ ≤ 3 * (|a|⁻¹ * A⁻¹) + |a| * A :=
        add_le_add (sineIntegralTruncation_sub_bound a A R ha hA hAR)
          (abs_sineIntegralTruncation_le_mul a A hA.le)
      _ = 4 := by
        dsimp [A]
        field_simp [ne_of_gt haabs]
        norm_num

private theorem norm_symmetricExponentialTruncation_le_eight (a R : ℝ) (hR : 0 ≤ R) :
    ‖symmetricExponentialTruncation a R‖ ≤ 8 := by
  rw [symmetricExponentialTruncation_eq, norm_mul, Complex.norm_real]
  have htwo : ‖(-2 : ℂ) * Complex.I‖ = 2 := by norm_num
  rw [htwo, Real.norm_eq_abs]
  nlinarith [abs_sineIntegralTruncation_le_four (2 * Real.pi * a) R hR]

private def principalValueModeBound (k : ℕ) : ℝ :=
  (16 / (2 * Real.pi ^ 2)) * (1 / (k : ℝ) ^ 2)

private theorem summable_principalValueModeBound : Summable principalValueModeBound := by
  unfold principalValueModeBound
  exact (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < (2 : ℕ))).mul_left _

private theorem norm_bernoulliModeTruncation_le (N k : ℕ) (s R : ℝ) (hR : 0 ≤ R) :
    ‖bernoulliModeTruncation N s k R‖ ≤ principalValueModeBound k := by
  by_cases hk : k = 0
  · subst k
    simp [bernoulliModeTruncation, bernoulliCosineTerm, principalValueModeBound]
  rw [bernoulliModeTruncation_eq_closedForm]
  unfold bernoulliModeClosedForm
  rw [norm_mul, Complex.norm_real]
  have hden : 0 < 2 * Real.pi ^ 2 * (k : ℝ) ^ 2 := by
    have hkcast : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hk
    positivity
  have hcoef : |1 / (2 * Real.pi ^ 2 * (k : ℝ) ^ 2)| =
      1 / (2 * Real.pi ^ 2 * (k : ℝ) ^ 2) := abs_of_pos (one_div_pos.mpr hden)
  rw [Real.norm_eq_abs, hcoef]
  have hbracket :
      ‖symmetricExponentialTruncation s R -
          (1 / 2 : ℂ) * symmetricExponentialTruncation (s - (k : ℝ) * N) R -
          (1 / 2 : ℂ) * symmetricExponentialTruncation (s + (k : ℝ) * N) R‖ ≤ 16 := by
    calc
      ‖symmetricExponentialTruncation s R -
          (1 / 2 : ℂ) * symmetricExponentialTruncation (s - (k : ℝ) * N) R -
          (1 / 2 : ℂ) * symmetricExponentialTruncation (s + (k : ℝ) * N) R‖ ≤
        ‖symmetricExponentialTruncation s R‖ +
          ‖(1 / 2 : ℂ) * symmetricExponentialTruncation (s - (k : ℝ) * N) R‖ +
          ‖(1 / 2 : ℂ) * symmetricExponentialTruncation (s + (k : ℝ) * N) R‖ := by
        calc
          ‖_ - (1 / 2 : ℂ) * symmetricExponentialTruncation (s + (k : ℝ) * N) R‖ ≤
              ‖symmetricExponentialTruncation s R -
                (1 / 2 : ℂ) * symmetricExponentialTruncation (s - (k : ℝ) * N) R‖ +
                ‖(1 / 2 : ℂ) * symmetricExponentialTruncation (s + (k : ℝ) * N) R‖ :=
            norm_sub_le _ _
          _ ≤ (‖symmetricExponentialTruncation s R‖ +
                ‖(1 / 2 : ℂ) * symmetricExponentialTruncation (s - (k : ℝ) * N) R‖) +
                ‖(1 / 2 : ℂ) * symmetricExponentialTruncation (s + (k : ℝ) * N) R‖ := by
            gcongr
            exact norm_sub_le _ _
      _ ≤ 8 + (1 / 2) * 8 + (1 / 2) * 8 := by
        rw [norm_mul, norm_mul]
        norm_num
        nlinarith [norm_symmetricExponentialTruncation_le_eight s R hR,
          norm_symmetricExponentialTruncation_le_eight (s - (k : ℝ) * N) R hR,
          norm_symmetricExponentialTruncation_le_eight (s + (k : ℝ) * N) R hR]
      _ = 16 := by norm_num
  calc
    (1 / (2 * Real.pi ^ 2 * (k : ℝ) ^ 2)) * ‖_‖ ≤
        (1 / (2 * Real.pi ^ 2 * (k : ℝ) ^ 2)) * 16 :=
      mul_le_mul_of_nonneg_left hbracket (one_div_nonneg.mpr hden.le)
    _ = principalValueModeBound k := by
      unfold principalValueModeBound
      field_simp [Real.pi_ne_zero, hk]

def bernoulliModePrincipalValue (N : ℕ) (s : ℝ) (k : ℕ) : ℂ :=
  ((1 / (2 * Real.pi ^ 2 * (k : ℝ) ^ 2) : ℝ) : ℂ) *
    (signedExponentialPV s - (1 / 2 : ℂ) * signedExponentialPV (s - (k : ℝ) * N) -
      (1 / 2 : ℂ) * signedExponentialPV (s + (k : ℝ) * N))

private theorem tendsto_bernoulliModeTruncation_atTop (N k : ℕ) (s : ℝ) :
    Tendsto (bernoulliModeTruncation N s k) atTop
      (nhds (bernoulliModePrincipalValue N s k)) := by
  have hs := tendsto_symmetricExponentialTruncation_atTop s
  have hm := tendsto_symmetricExponentialTruncation_atTop (s - (k : ℝ) * N)
  have hp := tendsto_symmetricExponentialTruncation_atTop (s + (k : ℝ) * N)
  have hhalf : Tendsto (fun _R : ℝ => (1 / 2 : ℂ)) atTop (nhds (1 / 2 : ℂ)) :=
    tendsto_const_nhds
  have hcomb : Tendsto
      (fun R => symmetricExponentialTruncation s R -
        (1 / 2 : ℂ) * symmetricExponentialTruncation (s - (k : ℝ) * N) R -
        (1 / 2 : ℂ) * symmetricExponentialTruncation (s + (k : ℝ) * N) R)
      atTop
      (nhds (signedExponentialPV s -
        (1 / 2 : ℂ) * signedExponentialPV (s - (k : ℝ) * N) -
        (1 / 2 : ℂ) * signedExponentialPV (s + (k : ℝ) * N))) :=
    (hs.sub (hhalf.mul hm)).sub (hhalf.mul hp)
  have hcoef : Tendsto
      (fun _R : ℝ => ((1 / (2 * Real.pi ^ 2 * (k : ℝ) ^ 2) : ℝ) : ℂ)) atTop
      (nhds ((1 / (2 * Real.pi ^ 2 * (k : ℝ) ^ 2) : ℝ) : ℂ)) :=
    tendsto_const_nhds
  have hmul := hcoef.mul hcomb
  unfold bernoulliModePrincipalValue
  apply hmul.congr'
  filter_upwards with R
  rw [bernoulliModeTruncation_eq_closedForm]
  rfl

/-- Before simplifying the signs, the Bernoulli principal value is the
absolutely convergent sum of the exact one-mode principal values. -/
theorem tendsto_bernoulliPairedTruncation_atTop (N : ℕ) (s : ℝ) :
    Tendsto (bernoulliPairedTruncation N s) atTop
      (nhds (∑' k : ℕ, bernoulliModePrincipalValue N s k)) := by
  have ht := tendsto_tsum_of_dominated_convergence summable_principalValueModeBound
    (fun k => tendsto_bernoulliModeTruncation_atTop N k s)
    (by
      filter_upwards [Ici_mem_atTop (0 : ℝ)] with R hR k
      exact norm_bernoulliModeTruncation_le N k s R hR)
  apply ht.congr'
  filter_upwards with R
  exact (hasSum_bernoulliModeTruncation N s R).tsum_eq

/-! ## The half-weighted reciprocal-square tail -/

/-- The summand in the paper's tail formula.  Frequencies strictly beyond
the threshold have full weight, a frequency exactly on the threshold has
weight `1/2`, and all earlier frequencies have weight zero. -/
def halfWeightedTailTerm (N : ℕ) (s : ℝ) (k : ℕ) : ℝ :=
  if s < (k : ℝ) * N then 1 / (k : ℝ) ^ 2
  else if s = (k : ℝ) * N then 1 / (2 * (k : ℝ) ^ 2)
  else 0

/-- The exact half-weighted tail appearing in Lemma 2.1. -/
def halfWeightedTail (N : ℕ) (s : ℝ) : ℝ :=
  ∑' k : ℕ, halfWeightedTailTerm N s k

theorem summable_halfWeightedTailTerm (N : ℕ) (s : ℝ) :
    Summable (halfWeightedTailTerm N s) := by
  apply (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < (2 : ℕ))).of_nonneg_of_le
  · intro k
    unfold halfWeightedTailTerm
    split_ifs <;> positivity
  · intro k
    unfold halfWeightedTailTerm
    split_ifs
    · exact le_rfl
    · have hk2 : 0 ≤ (k : ℝ) ^ 2 := sq_nonneg _
      by_cases hk : k = 0
      · subst k
        simp
      · have hk2pos : 0 < (k : ℝ) ^ 2 := sq_pos_of_ne_zero (Nat.cast_ne_zero.mpr hk)
        exact one_div_le_one_div_of_le hk2pos (by nlinarith)
    · positivity

theorem bernoulliModePrincipalValue_eq_tailTerm (N k : ℕ) (s : ℝ)
    (hN : 0 < N) (hs : 0 < s) :
    bernoulliModePrincipalValue N s k =
      (-(Complex.I / (2 * Real.pi))) * (halfWeightedTailTerm N s k : ℂ) := by
  by_cases hk : k = 0
  · subst k
    simp [bernoulliModePrincipalValue, halfWeightedTailTerm, signedExponentialPV,
      hs.ne', hs]
  have hkNat : 0 < k := Nat.pos_of_ne_zero hk
  have hkN : 0 < (k : ℝ) * N := mul_pos (Nat.cast_pos.mpr hkNat) (Nat.cast_pos.mpr hN)
  have hplus : 0 < s + (k : ℝ) * N := add_pos hs hkN
  rcases lt_trichotomy s ((k : ℝ) * N) with hlt | heq | hgt
  · have hminus : s - (k : ℝ) * N < 0 := sub_neg.mpr hlt
    rw [bernoulliModePrincipalValue, halfWeightedTailTerm, if_pos hlt]
    unfold signedExponentialPV
    rw [if_pos hs, if_neg (not_lt.mpr hminus.le), if_pos hminus, if_pos hplus]
    push_cast
    field_simp [Real.pi_ne_zero, hk]
    ring_nf
  · have hminus : s - (k : ℝ) * N = 0 := sub_eq_zero.mpr heq
    rw [bernoulliModePrincipalValue, halfWeightedTailTerm, if_neg (not_lt.mpr heq.ge),
      if_pos heq, hminus]
    unfold signedExponentialPV
    rw [if_pos hs, if_neg (lt_irrefl 0), if_neg (lt_irrefl 0), if_pos hplus]
    push_cast
    field_simp [Real.pi_ne_zero, hk]
    ring_nf
  · have hminus : 0 < s - (k : ℝ) * N := sub_pos.mpr hgt
    have hne : s ≠ (k : ℝ) * N := ne_of_gt hgt
    rw [bernoulliModePrincipalValue, halfWeightedTailTerm,
      if_neg (not_lt.mpr hgt.le), if_neg hne]
    unfold signedExponentialPV
    rw [if_pos hs, if_pos hminus, if_pos hplus]
    push_cast
    ring

theorem summable_bernoulliModePrincipalValue (N : ℕ) (s : ℝ)
    (hN : 0 < N) (hs : 0 < s) :
    Summable (bernoulliModePrincipalValue N s) := by
  have htail : Summable fun k : ℕ ↦
      (halfWeightedTailTerm N s k : ℂ) :=
    Complex.summable_ofReal.mpr (summable_halfWeightedTailTerm N s)
  have hscaled := htail.mul_left (-(Complex.I / (2 * Real.pi)))
  exact hscaled.congr fun k ↦
    (bernoulliModePrincipalValue_eq_tailTerm N k s hN hs).symm

theorem tsum_bernoulliModePrincipalValue_eq_tail (N : ℕ) (s : ℝ)
    (hN : 0 < N) (hs : 0 < s) :
    (∑' k : ℕ, bernoulliModePrincipalValue N s k) =
      (-(Complex.I / (2 * Real.pi))) * (halfWeightedTail N s : ℂ) := by
  calc
    (∑' k : ℕ, bernoulliModePrincipalValue N s k) =
        ∑' k : ℕ, (-(Complex.I / (2 * Real.pi))) *
          (halfWeightedTailTerm N s k : ℂ) := by
      apply tsum_congr
      intro k
      exact bernoulliModePrincipalValue_eq_tailTerm N k s hN hs
    _ = (-(Complex.I / (2 * Real.pi))) *
        ∑' k : ℕ, (halfWeightedTailTerm N s k : ℂ) := tsum_mul_left
    _ = (-(Complex.I / (2 * Real.pi))) * (halfWeightedTail N s : ℂ) := by
      rw [halfWeightedTail, Complex.ofReal_tsum]

/-- Lemma 2.1, as an ordinary symmetric principal value.  The conclusion is
the exact reciprocal-square tail, including half weight when `s = kN`.
Every limiting operation used in the proof is represented above by a finite
truncation, dominated-convergence theorem, or Tannery theorem. -/
theorem principalValueTransform_eq_halfWeightedTail (N : ℕ) (s : ℝ)
    (hN : 0 < N) (hs : 0 < s) :
    HasSymmetricPrincipalValue N s
      ((-(Complex.I / (2 * Real.pi))) * (halfWeightedTail N s : ℂ)) := by
  unfold HasSymmetricPrincipalValue
  rw [← tsum_bernoulliModePrincipalValue_eq_tail N s hN hs]
  have hlim := tendsto_bernoulliPairedTruncation_atTop N s
  apply hlim.congr'
  filter_upwards with R
  exact (principalValueTruncation_eq_paired N s R).symm

/-- At zero frequency the paired kernel vanishes identically.  This records
the zero-frequency oddness separately from the positive-frequency tail
formula. -/
theorem principalValueTransform_zero_frequency (N : ℕ) :
    HasSymmetricPrincipalValue N 0 0 := by
  unfold HasSymmetricPrincipalValue
  have hzero : principalValueTruncation N 0 = fun _R : ℝ => 0 := by
    funext R
    rw [principalValueTruncation_eq_paired]
    simp [bernoulliPairedTruncation, pairedKernel, sineKernel]
  rw [hzero]
  exact tendsto_const_nhds

end

end Erdos1002
