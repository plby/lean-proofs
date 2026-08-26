import ErdosProblems.Erdos67b.MRLemma14TwoLengthHighAssembly
import ErdosProblems.Erdos67b.MRFiniteHalaszSmoothing

/-!
# The continuous Schur estimate in source Lemma 14

The discrete logarithmic large-sieve estimate has an interval-length term
which cannot be summed over arbitrarily high dyadic shells.  The source
proof instead expands the square before integrating in the spatial
variable.  The Fourier transform of the smooth spatial cutoff is bounded
by a constant multiple of the Cauchy kernel
`(1 + (t₁ - t₂)^2)⁻¹`.  This file isolates the exact Schur estimate which
turns that double integral into vertical `L²` energy, uniformly in the
length of the vertical interval.
-/

open scoped ComplexConjugate FourierTransform SchwartzMap
open MeasureTheory

namespace Erdos67b

noncomputable section

open MRFiniteHalaszSmoothing

/-- The Cauchy kernel which occurs after two integrations by parts in the
smooth spatial Fourier transform. -/
def lemma14CauchyKernel (s t : ℝ) : ℝ :=
  (1 + (s - t) ^ 2)⁻¹

theorem lemma14CauchyKernel_nonneg (s t : ℝ) :
    0 ≤ lemma14CauchyKernel s t := by
  unfold lemma14CauchyKernel
  positivity

theorem continuous_lemma14CauchyKernel :
    Continuous (Function.uncurry lemma14CauchyKernel) := by
  unfold lemma14CauchyKernel Function.uncurry
  apply Continuous.inv₀
  · fun_prop
  · intro p
    positivity

/-- Every row of the Cauchy kernel has interval mass at most `π`. -/
theorem intervalIntegral_lemma14CauchyKernel_le_pi
    {A B : ℝ} (hAB : A ≤ B) (s : ℝ) :
    (∫ t in A..B, lemma14CauchyKernel s t) ≤ Real.pi := by
  unfold lemma14CauchyKernel
  change (∫ t in A..B, (fun u : ℝ ↦ (1 + u ^ 2)⁻¹) (s - t)) ≤ _
  have hcv := intervalIntegral.integral_comp_sub_left
    (f := fun u : ℝ ↦ (1 + u ^ 2)⁻¹) (a := A) (b := B) s
  rw [hcv]
  rw [integral_inv_one_add_sq]
  linarith [Real.arctan_lt_pi_div_two (s - A),
    Real.neg_pi_div_two_lt_arctan (s - B)]

/-- Continuous Schur's test for the Cauchy kernel on an arbitrary finite
vertical interval.  Crucially, the constant is independent of `B-A`.
This is the analytic core which removes the divergent diagonal term in a
dyadic use of discrete logarithmic Plancherel. -/
theorem intervalIntegral_intervalIntegral_norm_mul_cauchyKernel_le
    (g : ℝ → ℂ) (hg : Continuous g) {A B : ℝ} (hAB : A ≤ B) :
    (∫ s in A..B, ∫ t in A..B,
        ‖g s‖ * ‖g t‖ * lemma14CauchyKernel s t) ≤
      Real.pi * ∫ t in A..B, Complex.normSq (g t) := by
  let K : ℝ → ℝ → ℝ := fun s t ↦ lemma14CauchyKernel s t
  let e : ℝ → ℝ := fun t ↦ Complex.normSq (g t)
  have hK : Continuous (Function.uncurry K) := by
    simpa only [K] using continuous_lemma14CauchyKernel
  have he : Continuous e := by
    dsimp [e]
    fun_prop
  have hnorm : Continuous (fun t ↦ ‖g t‖) := hg.norm
  have hprod : Continuous (Function.uncurry (fun s t : ℝ ↦
      ‖g s‖ * ‖g t‖ * K s t)) := by
    fun_prop
  have hdiag₁ : Continuous (Function.uncurry (fun s t : ℝ ↦
      e s * K s t)) := by
    fun_prop
  have hdiag₂ : Continuous (Function.uncurry (fun s t : ℝ ↦
      e t * K s t)) := by
    fun_prop
  have hcompact : IsCompact (Set.uIcc A B ×ˢ Set.uIcc A B) :=
    (isCompact_uIcc.prod isCompact_uIcc)
  have hprodInt : IntegrableOn
      (Function.uncurry (fun s t : ℝ ↦ ‖g s‖ * ‖g t‖ * K s t))
      (Set.uIoc A B ×ˢ Set.uIoc A B) :=
    (hprod.continuousOn.integrableOn_compact hcompact).mono_set
      (Set.prod_mono Set.uIoc_subset_uIcc Set.uIoc_subset_uIcc)
  have hdiag₁Int : IntegrableOn
      (Function.uncurry (fun s t : ℝ ↦ e s * K s t))
      (Set.uIoc A B ×ˢ Set.uIoc A B) :=
    (hdiag₁.continuousOn.integrableOn_compact hcompact).mono_set
      (Set.prod_mono Set.uIoc_subset_uIcc Set.uIoc_subset_uIcc)
  have hdiag₂Int : IntegrableOn
      (Function.uncurry (fun s t : ℝ ↦ e t * K s t))
      (Set.uIoc A B ×ˢ Set.uIoc A B) :=
    (hdiag₂.continuousOn.integrableOn_compact hcompact).mono_set
      (Set.prod_mono Set.uIoc_subset_uIcc Set.uIoc_subset_uIcc)
  have hyoung (s t : ℝ) :
      ‖g s‖ * ‖g t‖ * K s t ≤
        (1 / 2 : ℝ) * (e s * K s t + e t * K s t) := by
    have hk := lemma14CauchyKernel_nonneg s t
    have hs := norm_nonneg (g s)
    have ht := norm_nonneg (g t)
    have hab : 2 * ‖g s‖ * ‖g t‖ ≤ ‖g s‖ ^ 2 + ‖g t‖ ^ 2 := by
      nlinarith [sq_nonneg (‖g s‖ - ‖g t‖)]
    dsimp [K, e]
    rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
    nlinarith
  have hmain :
      (∫ s in A..B, ∫ t in A..B,
          ‖g s‖ * ‖g t‖ * K s t) ≤
        ∫ s in A..B, ∫ t in A..B,
          (1 / 2 : ℝ) * (e s * K s t + e t * K s t) := by
    apply intervalIntegral.integral_mono_on hAB
    · have hc : Continuous (fun s ↦ ∫ t in A..B,
          ‖g s‖ * ‖g t‖ * K s t) := by
        apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
        fun_prop
      exact hc.intervalIntegrable A B
    · have hc : Continuous (fun s ↦ ∫ t in A..B,
          (1 / 2 : ℝ) * (e s * K s t + e t * K s t)) := by
        apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
        fun_prop
      exact hc.intervalIntegrable A B
    · intro s hs
      apply intervalIntegral.integral_mono_on hAB
      · have hc : Continuous (fun t ↦ ‖g s‖ * ‖g t‖ * K s t) := by
          fun_prop
        exact hc.intervalIntegrable A B
      · have hc : Continuous (fun t ↦
            (1 / 2 : ℝ) * (e s * K s t + e t * K s t)) := by fun_prop
        exact hc.intervalIntegrable A B
      · intro t ht
        exact hyoung s t
  have hrow₁ :
      (∫ s in A..B, ∫ t in A..B, e s * K s t) ≤
        Real.pi * ∫ s in A..B, e s := by
    have hpoint (s : ℝ) (hs : s ∈ Set.Icc A B) :
        (∫ t in A..B, e s * K s t) ≤ Real.pi * e s := by
      rw [intervalIntegral.integral_const_mul]
      have hle := mul_le_mul_of_nonneg_left
        (intervalIntegral_lemma14CauchyKernel_le_pi hAB s) (show 0 ≤ e s by
          dsimp [e]
          exact Complex.normSq_nonneg _)
      simpa only [K, e, mul_comm] using hle
    calc
      (∫ s in A..B, ∫ t in A..B, e s * K s t) ≤
          ∫ s in A..B, Real.pi * e s :=
        intervalIntegral.integral_mono_on hAB
          (by
        have hc : Continuous (fun s ↦ ∫ t in A..B, e s * K s t) := by
          apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
          fun_prop
        exact hc.intervalIntegrable A B)
          ((continuous_const.mul he).intervalIntegrable A B) hpoint
      _ = Real.pi * ∫ s in A..B, e s := by
        rw [intervalIntegral.integral_const_mul]
  have hswap :
      (∫ s in A..B, ∫ t in A..B, e t * K s t) =
        ∫ t in A..B, ∫ s in A..B, e t * K s t := by
    exact intervalIntegral_intervalIntegral_swap hdiag₂Int
  have hrow₂ :
      (∫ s in A..B, ∫ t in A..B, e t * K s t) ≤
        Real.pi * ∫ t in A..B, e t := by
    calc
      (∫ s in A..B, ∫ t in A..B, e t * K s t) =
          ∫ t in A..B, ∫ s in A..B, e t * K s t := hswap
      _ ≤ Real.pi * ∫ t in A..B, e t := by
        calc
          (∫ t in A..B, ∫ s in A..B, e t * K s t) ≤
              ∫ t in A..B, Real.pi * e t := by
            apply intervalIntegral.integral_mono_on hAB
            · have hc : Continuous (fun t ↦ ∫ s in A..B, e t * K s t) := by
                apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
                fun_prop
              exact hc.intervalIntegrable A B
            · exact (continuous_const.mul he).intervalIntegrable A B
            · intro t ht
              rw [intervalIntegral.integral_const_mul]
              have hkrow : (∫ s in A..B, K s t) ≤ Real.pi := by
                have hsymm : (fun s ↦ K s t) =
                    fun s ↦ lemma14CauchyKernel t s := by
                  funext s
                  unfold K lemma14CauchyKernel
                  congr 2
                  ring
                rw [hsymm]
                exact intervalIntegral_lemma14CauchyKernel_le_pi hAB t
              have hle := mul_le_mul_of_nonneg_left hkrow (show 0 ≤ e t by
                dsimp [e]
                exact Complex.normSq_nonneg _)
              simpa only [mul_comm] using hle
          _ = Real.pi * ∫ t in A..B, e t := by
            rw [intervalIntegral.integral_const_mul]
  calc
    (∫ s in A..B, ∫ t in A..B,
        ‖g s‖ * ‖g t‖ * lemma14CauchyKernel s t) =
        ∫ s in A..B, ∫ t in A..B,
          ‖g s‖ * ‖g t‖ * K s t := by rfl
    _ ≤ ∫ s in A..B, ∫ t in A..B,
          (1 / 2 : ℝ) * (e s * K s t + e t * K s t) := hmain
    _ = (1 / 2 : ℝ) *
        ((∫ s in A..B, ∫ t in A..B, e s * K s t) +
          ∫ s in A..B, ∫ t in A..B, e t * K s t) := by
      have hinner (s : ℝ) :
          (∫ t in A..B,
              (1 / 2 : ℝ) * (e s * K s t + e t * K s t)) =
            (1 / 2 : ℝ) *
              ((∫ t in A..B, e s * K s t) +
                ∫ t in A..B, e t * K s t) := by
        rw [intervalIntegral.integral_const_mul,
          intervalIntegral.integral_add
            ((by fun_prop : Continuous (fun t ↦ e s * K s t)).intervalIntegrable A B)
            ((by fun_prop : Continuous (fun t ↦ e t * K s t)).intervalIntegrable A B)]
      rw [show (fun s ↦ ∫ t in A..B,
          (1 / 2 : ℝ) * (e s * K s t + e t * K s t)) =
          fun s ↦ (1 / 2 : ℝ) *
            ((∫ t in A..B, e s * K s t) +
              ∫ t in A..B, e t * K s t) by
            funext s
            exact hinner s]
      rw [intervalIntegral.integral_const_mul]
      have hc₁ : Continuous (fun s ↦ ∫ t in A..B, e s * K s t) := by
        apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
        fun_prop
      have hc₂ : Continuous (fun s ↦ ∫ t in A..B, e t * K s t) := by
        apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
        fun_prop
      rw [intervalIntegral.integral_add
        (hc₁.intervalIntegrable A B) (hc₂.intervalIntegrable A B)]
    _ ≤ (1 / 2 : ℝ) *
        (Real.pi * (∫ s in A..B, e s) +
          Real.pi * (∫ t in A..B, e t)) := by
      gcongr
    _ = Real.pi * ∫ t in A..B, Complex.normSq (g t) := by
      dsimp [e]
      ring

/-- Kernel form of the source double-integral argument.  Once the spatial
Fourier transform of the cutoff is bounded by `C` times the Cauchy kernel,
the entire bilinear expression is controlled by `C * π` times the vertical
energy.  This statement is uniform in the endpoints `A,B`. -/
theorem norm_intervalIntegral_intervalIntegral_mul_kernel_le
    (g : ℝ → ℂ) (hg : Continuous g)
    (J : ℝ → ℝ → ℂ)
    (hJ : Continuous (Function.uncurry J))
    {A B C : ℝ} (hAB : A ≤ B) (hC : 0 ≤ C)
    (hkernel : ∀ s ∈ Set.Icc A B, ∀ t ∈ Set.Icc A B,
      ‖J s t‖ ≤ C * lemma14CauchyKernel s t) :
    ‖∫ s in A..B, ∫ t in A..B,
        g s * conj (g t) * J s t‖ ≤
      C * Real.pi * ∫ t in A..B, Complex.normSq (g t) := by
  let q : ℝ → ℝ → ℂ := fun s t ↦ g s * conj (g t) * J s t
  let m : ℝ → ℝ → ℝ := fun s t ↦
    ‖g s‖ * ‖g t‖ * lemma14CauchyKernel s t
  have hq : Continuous (Function.uncurry q) := by
    dsimp [q]
    fun_prop
  have hm : Continuous (Function.uncurry m) := by
    dsimp [m]
    exact ((hg.norm.comp continuous_fst).mul (hg.norm.comp continuous_snd)).mul
      continuous_lemma14CauchyKernel
  have hinner (s : ℝ) (hs : s ∈ Set.Icc A B) :
      ‖∫ t in A..B, q s t‖ ≤ C * ∫ t in A..B, m s t := by
    calc
      ‖∫ t in A..B, q s t‖ ≤ ∫ t in A..B, ‖q s t‖ :=
        intervalIntegral.norm_integral_le_integral_norm hAB
      _ ≤ ∫ t in A..B, C * m s t := by
        apply intervalIntegral.integral_mono_on hAB
        · exact (by fun_prop : Continuous (fun t ↦ ‖q s t‖)).intervalIntegrable A B
        · exact (by fun_prop : Continuous (fun t ↦ C * m s t)).intervalIntegrable A B
        · intro t ht
          have hj := hkernel s hs t ht
          dsimp [q, m]
          simp only [norm_mul, RCLike.norm_conj]
          have hfac : 0 ≤ ‖g s‖ * ‖g t‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
          calc
            ‖g s‖ * ‖g t‖ * ‖J s t‖ ≤
                ‖g s‖ * ‖g t‖ *
                  (C * lemma14CauchyKernel s t) :=
              mul_le_mul_of_nonneg_left hj hfac
            _ = C * (‖g s‖ * ‖g t‖ * lemma14CauchyKernel s t) := by ring
      _ = C * ∫ t in A..B, m s t := by
        rw [intervalIntegral.integral_const_mul]
  calc
    ‖∫ s in A..B, ∫ t in A..B,
        g s * conj (g t) * J s t‖ =
        ‖∫ s in A..B, ∫ t in A..B, q s t‖ := by rfl
    _ ≤ ∫ s in A..B, ‖∫ t in A..B, q s t‖ :=
      intervalIntegral.norm_integral_le_integral_norm hAB
    _ ≤ ∫ s in A..B, C * ∫ t in A..B, m s t := by
      apply intervalIntegral.integral_mono_on hAB
      · have hc : Continuous (fun s ↦ ‖∫ t in A..B, q s t‖) := by
          apply Continuous.norm
          apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
          exact hq
        exact hc.intervalIntegrable A B
      · have hc : Continuous (fun s ↦ C * ∫ t in A..B, m s t) := by
          apply continuous_const.mul
          apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
          exact hm
        exact hc.intervalIntegrable A B
      · exact hinner
    _ = C * (∫ s in A..B, ∫ t in A..B, m s t) := by
      rw [intervalIntegral.integral_const_mul]
    _ ≤ C * (Real.pi * ∫ t in A..B, Complex.normSq (g t)) := by
      apply mul_le_mul_of_nonneg_left _ hC
      exact intervalIntegral_intervalIntegral_norm_mul_cauchyKernel_le
        g hg hAB
    _ = C * Real.pi * ∫ t in A..B, Complex.normSq (g t) := by ring

/-! ## A concrete smooth spatial Fourier kernel -/

/-- Explicit constant controlling a smooth spatial Fourier kernel by the
Cauchy kernel.  It uses only the order-zero and order-two Schwartz
seminorms of the Fourier transform. -/
def lemma14FourierCauchyConstant (ψ : 𝓢(ℝ, ℂ)) : ℝ :=
  SchwartzMap.seminorm ℂ 0 0 (𝓕 ψ) +
    (2 * Real.pi) ^ 2 * SchwartzMap.seminorm ℂ 2 0 (𝓕 ψ)

theorem lemma14FourierCauchyConstant_nonneg (ψ : 𝓢(ℝ, ℂ)) :
    0 ≤ lemma14FourierCauchyConstant ψ := by
  unfold lemma14FourierCauchyConstant
  exact add_nonneg (apply_nonneg _ _)
    (mul_nonneg (sq_nonneg _) (apply_nonneg _ _))

/-- The Fourier kernel at the logarithmic frequency difference occurring
after expanding the spatial square.  Mathlib's Fourier convention has the
factor `2π`, hence the rescaling below. -/
def lemma14SmoothSpatialKernel (ψ : 𝓢(ℝ, ℂ)) (s t : ℝ) : ℂ :=
  (𝓕 ψ) ((s - t) / (2 * Real.pi))

theorem continuous_lemma14SmoothSpatialKernel (ψ : 𝓢(ℝ, ℂ)) :
    Continuous (Function.uncurry (lemma14SmoothSpatialKernel ψ)) := by
  unfold lemma14SmoothSpatialKernel Function.uncurry
  exact (𝓕 ψ).continuous.comp (by fun_prop)

/-- Integral representation of the smooth spatial kernel, in the same
phase convention as the logarithmic Perron polynomial. -/
theorem lemma14SmoothSpatialKernel_eq_integral
    (ψ : 𝓢(ℝ, ℂ)) (s t : ℝ) :
    lemma14SmoothSpatialKernel ψ s t =
      ∫ y : ℝ, realExponentialPhase (-(s - t) * y) * ψ y := by
  unfold lemma14SmoothSpatialKernel
  rw [SchwartzMap.fourier_coe, Real.fourier_eq']
  apply integral_congr_ae
  filter_upwards with y
  simp only [RCLike.inner_apply, conj_trivial, smul_eq_mul]
  unfold realExponentialPhase
  congr 2
  push_cast
  have hπ : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  field_simp [hπ]

/-- Logarithmic spatial analysis transform on a finite vertical band. -/
def lemma14LogSpatialTransform
    (g : ℝ → ℂ) (A B y : ℝ) : ℂ :=
  ∫ t in A..B, g t * realExponentialPhase (-t * y)

theorem continuous_lemma14LogSpatialTransform
    (g : ℝ → ℂ) (hg : Continuous g) (A B : ℝ) :
    Continuous (lemma14LogSpatialTransform g A B) := by
  unfold lemma14LogSpatialTransform
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
  exact (hg.comp continuous_snd).mul
    (continuous_realExponentialPhase.comp
      (continuous_snd.neg.mul continuous_fst))

/-- Pointwise expansion of the spatial square into its two vertical
frequencies.  The phase is exactly the one appearing in the Fourier
representation of `lemma14SmoothSpatialKernel`. -/
theorem ofReal_normSq_lemma14LogSpatialTransform_eq_doubleIntegral
    (g : ℝ → ℂ) (hg : Continuous g) {A B y : ℝ} :
    (Complex.normSq (lemma14LogSpatialTransform g A B y) : ℂ) =
      ∫ s in A..B, ∫ t in A..B,
        g s * conj (g t) * realExponentialPhase (-(s - t) * y) := by
  let a : ℝ → ℂ := fun t ↦ g t * realExponentialPhase (-t * y)
  have ha : Continuous a := by
    dsimp [a]
    exact hg.mul (continuous_realExponentialPhase.comp (by fun_prop))
  have hconj : Continuous (fun t ↦ conj (a t)) := by fun_prop
  have hmul :
      lemma14LogSpatialTransform g A B y *
          conj (lemma14LogSpatialTransform g A B y) =
        ∫ s in A..B, ∫ t in A..B, a s * conj (a t) := by
    unfold lemma14LogSpatialTransform
    rw [← intervalIntegral.intervalIntegral_conj]
    rw [← intervalIntegral.integral_mul_const]
    apply intervalIntegral.integral_congr
    intro s hs
    change a s * (∫ t in A..B, conj (a t)) = _
    rw [← intervalIntegral.integral_const_mul]
  rw [Complex.normSq_eq_conj_mul_self]
  rw [show
    conj (lemma14LogSpatialTransform g A B y) *
        lemma14LogSpatialTransform g A B y =
      lemma14LogSpatialTransform g A B y *
        conj (lemma14LogSpatialTransform g A B y) by ring, hmul]
  apply intervalIntegral.integral_congr
  intro s hs
  apply intervalIntegral.integral_congr
  intro t ht
  dsimp [a]
  rw [map_mul, conj_realExponentialPhase]
  rw [show
    g s * realExponentialPhase (-s * y) *
        (conj (g t) * realExponentialPhase (-(-t * y))) =
      g s * conj (g t) *
        (realExponentialPhase (-s * y) *
          realExponentialPhase (-(-t * y))) by ring]
  rw [realExponentialPhase_mul]
  congr 2
  ring

/-- Exact Fubini identity which turns the smoothly weighted spatial square
into the vertical double integral with Fourier kernel.  This is the source
Lemma-14 square-expansion step; all three integrals are genuinely
integrable because the vertical band is finite and `ψ` is Schwartz. -/
theorem integral_schwartz_mul_normSq_logSpatialTransform_eq_doubleIntegral
    (g : ℝ → ℂ) (hg : Continuous g) (ψ : 𝓢(ℝ, ℂ))
    {A B : ℝ} (hAB : A ≤ B) :
    (∫ y : ℝ, ψ y *
        (Complex.normSq (lemma14LogSpatialTransform g A B y) : ℂ)) =
      ∫ s in A..B, ∫ t in A..B,
        g s * conj (g t) * lemma14SmoothSpatialKernel ψ s t := by
  let μI : Measure ℝ := volume.restrict (Set.Ioc A B)
  let R : (ℝ × ℝ) → ℝ → ℂ := fun z y ↦
    g z.1 * conj (g z.2) *
      realExponentialPhase (-(z.1 - z.2) * y) * ψ y
  have hgI : Integrable g μI := by
    dsimp [μI]
    exact (hg.intervalIntegrable A B).1
  have hgcI : Integrable (fun t ↦ conj (g t)) μI := by
    apply hgI.norm.mono'
    · fun_prop
    · filter_upwards with t
      simp only [RCLike.norm_conj]
      exact le_rfl
  have hpair : Integrable
      (fun z : ℝ × ℝ ↦ g z.1 * conj (g z.2)) (μI.prod μI) :=
    hgI.mul_prod hgcI
  have hbase : Integrable
      (fun p : (ℝ × ℝ) × ℝ ↦
        (g p.1.1 * conj (g p.1.2)) * ψ p.2)
      ((μI.prod μI).prod volume) := hpair.mul_prod ψ.integrable
  have hRcont : Continuous (Function.uncurry R) := by
    dsimp [R, Function.uncurry]
    fun_prop
  have hRint : Integrable (Function.uncurry R)
      ((μI.prod μI).prod volume) := by
    apply hbase.norm.mono' hRcont.aestronglyMeasurable
    filter_upwards with p
    dsimp [R, Function.uncurry]
    simp only [norm_mul, RCLike.norm_conj, norm_realExponentialPhase, mul_one]
    exact le_rfl
  have hRst (y : ℝ) : Integrable (fun z : ℝ × ℝ ↦ R z y)
      (μI.prod μI) := by
    have hdom : Integrable
        (fun z : ℝ × ℝ ↦ (g z.1 * conj (g z.2)) * ψ y)
        (μI.prod μI) := hpair.mul_const (ψ y)
    apply hdom.norm.mono'
    · exact (hRcont.comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable
    · filter_upwards with z
      dsimp [R]
      simp only [norm_mul, RCLike.norm_conj, norm_realExponentialPhase, mul_one]
      exact le_rfl
  have hswap :
      (∫ y : ℝ, (∫ s, (∫ t, R (s, t) y ∂μI) ∂μI)) =
        ∫ s, (∫ t, (∫ y : ℝ, R (s, t) y) ∂μI) ∂μI := by
    calc
      (∫ y : ℝ, (∫ s, (∫ t, R (s, t) y ∂μI) ∂μI)) =
          ∫ y : ℝ, (∫ z : ℝ × ℝ, R z y ∂(μI.prod μI)) := by
        apply integral_congr_ae
        filter_upwards with y
        exact (integral_prod _ (hRst y)).symm
      _ = ∫ z : ℝ × ℝ, (∫ y : ℝ, R z y) ∂(μI.prod μI) :=
        (integral_integral_swap hRint).symm
      _ = ∫ s, (∫ t, (∫ y : ℝ, R (s, t) y) ∂μI) ∂μI := by
        exact integral_prod (fun z : ℝ × ℝ ↦ ∫ y : ℝ, R z y)
          hRint.integral_prod_left
  have hleftPoint (y : ℝ) :
      ψ y * (Complex.normSq (lemma14LogSpatialTransform g A B y) : ℂ) =
        ∫ s, (∫ t, R (s, t) y ∂μI) ∂μI := by
    rw [ofReal_normSq_lemma14LogSpatialTransform_eq_doubleIntegral g hg]
    simp_rw [intervalIntegral.integral_of_le hAB]
    dsimp [μI]
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with s
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with t
    dsimp [R]
    ring
  have hrightPoint (s t : ℝ) :
      g s * conj (g t) * lemma14SmoothSpatialKernel ψ s t =
        ∫ y : ℝ, R (s, t) y := by
    rw [lemma14SmoothSpatialKernel_eq_integral]
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with y
    dsimp [R]
    ring
  have hrightEq :
      (∫ s in A..B, ∫ t in A..B,
        g s * conj (g t) * lemma14SmoothSpatialKernel ψ s t) =
        ∫ s, (∫ t, (∫ y : ℝ, R (s, t) y) ∂μI) ∂μI := by
    have hinner (s : ℝ) :
        (∫ t in A..B,
            g s * conj (g t) * lemma14SmoothSpatialKernel ψ s t) =
          ∫ t, (∫ y : ℝ, R (s, t) y) ∂μI := by
      rw [intervalIntegral.integral_of_le hAB]
      dsimp [μI]
      apply integral_congr_ae
      filter_upwards with t
      exact hrightPoint s t
    calc
      (∫ s in A..B, ∫ t in A..B,
          g s * conj (g t) * lemma14SmoothSpatialKernel ψ s t) =
          ∫ s in A..B, (∫ t, (∫ y : ℝ, R (s, t) y) ∂μI) := by
        apply intervalIntegral.integral_congr
        intro s hs
        exact hinner s
      _ = ∫ s, (∫ t, (∫ y : ℝ, R (s, t) y) ∂μI) ∂μI := by
        rw [intervalIntegral.integral_of_le hAB]
  calc
    (∫ y : ℝ, ψ y *
        (Complex.normSq (lemma14LogSpatialTransform g A B y) : ℂ)) =
        ∫ y : ℝ, (∫ s, (∫ t, R (s, t) y ∂μI) ∂μI) := by
      apply integral_congr_ae
      filter_upwards with y
      exact hleftPoint y
    _ = ∫ s, (∫ t, (∫ y : ℝ, R (s, t) y) ∂μI) ∂μI := hswap
    _ = ∫ s in A..B, ∫ t in A..B,
        g s * conj (g t) * lemma14SmoothSpatialKernel ψ s t := hrightEq.symm

/-- The concrete Fourier transform of every Schwartz spatial cutoff has
the required Cauchy decay, with a fully specified seminorm constant. -/
theorem norm_lemma14SmoothSpatialKernel_le
    (ψ : 𝓢(ℝ, ℂ)) (s t : ℝ) :
    ‖lemma14SmoothSpatialKernel ψ s t‖ ≤
      lemma14FourierCauchyConstant ψ * lemma14CauchyKernel s t := by
  let ξ : ℝ := (s - t) / (2 * Real.pi)
  let M₀ : ℝ := SchwartzMap.seminorm ℂ 0 0 (𝓕 ψ)
  let M₂ : ℝ := SchwartzMap.seminorm ℂ 2 0 (𝓕 ψ)
  have hπ : 0 < 2 * Real.pi := by positivity
  have h₀ : ‖(𝓕 ψ) ξ‖ ≤ M₀ := by
    dsimp [M₀]
    exact SchwartzMap.norm_le_seminorm ℂ (𝓕 ψ) ξ
  have h₂ : |ξ| ^ 2 * ‖(𝓕 ψ) ξ‖ ≤ M₂ := by
    dsimp [M₂]
    simpa only [Real.norm_eq_abs] using
      (SchwartzMap.norm_pow_mul_le_seminorm ℂ (𝓕 ψ) 2 ξ)
  have hscaled : (s - t) ^ 2 * ‖(𝓕 ψ) ξ‖ ≤
      (2 * Real.pi) ^ 2 * M₂ := by
    have hξ : |ξ| ^ 2 = (s - t) ^ 2 / (2 * Real.pi) ^ 2 := by
      dsimp [ξ]
      rw [abs_div, abs_of_pos hπ]
      rw [div_pow, sq_abs]
    rw [hξ] at h₂
    calc
      (s - t) ^ 2 * ‖(𝓕 ψ) ξ‖ =
          (2 * Real.pi) ^ 2 *
            (((s - t) ^ 2 / (2 * Real.pi) ^ 2) * ‖(𝓕 ψ) ξ‖) := by
        field_simp [hπ.ne']
      _ ≤ (2 * Real.pi) ^ 2 * M₂ :=
        mul_le_mul_of_nonneg_left h₂ (sq_nonneg _)
  have hsum :
      (1 + (s - t) ^ 2) * ‖(𝓕 ψ) ξ‖ ≤
        M₀ + (2 * Real.pi) ^ 2 * M₂ := by
    nlinarith
  have hden : 0 < 1 + (s - t) ^ 2 := by positivity
  unfold lemma14SmoothSpatialKernel lemma14FourierCauchyConstant
    lemma14CauchyKernel
  change ‖(𝓕 ψ) ξ‖ ≤ (M₀ + (2 * Real.pi) ^ 2 * M₂) *
    (1 + (s - t) ^ 2)⁻¹
  rw [← div_eq_mul_inv]
  exact (le_div_iff₀ hden).2 (by simpa only [mul_comm] using hsum)

/-- Fully concrete continuous-Schur endpoint for a Schwartz spatial
cutoff.  This is the source high-frequency double-integral estimate before
the remaining exact identification with the moving-endpoint square. -/
theorem norm_intervalIntegral_intervalIntegral_mul_smoothSpatialKernel_le
    (g : ℝ → ℂ) (hg : Continuous g) (ψ : 𝓢(ℝ, ℂ))
    {A B : ℝ} (hAB : A ≤ B) :
    ‖∫ s in A..B, ∫ t in A..B,
        g s * conj (g t) * lemma14SmoothSpatialKernel ψ s t‖ ≤
      lemma14FourierCauchyConstant ψ * Real.pi *
        ∫ t in A..B, Complex.normSq (g t) := by
  exact norm_intervalIntegral_intervalIntegral_mul_kernel_le
    g hg (lemma14SmoothSpatialKernel ψ)
      (continuous_lemma14SmoothSpatialKernel ψ) hAB
      (lemma14FourierCauchyConstant_nonneg ψ)
      (fun s hs t ht ↦ norm_lemma14SmoothSpatialKernel_le ψ s t)

/-- Source-form continuous spatial mean-square estimate.  The left side is
the smoothly weighted square of the logarithmic analysis transform, while
the right side is the original vertical `L²` energy with a constant
independent of the band length. -/
theorem norm_integral_schwartz_mul_normSq_logSpatialTransform_le
    (g : ℝ → ℂ) (hg : Continuous g) (ψ : 𝓢(ℝ, ℂ))
    {A B : ℝ} (hAB : A ≤ B) :
    ‖∫ y : ℝ, ψ y *
        (Complex.normSq (lemma14LogSpatialTransform g A B y) : ℂ)‖ ≤
      lemma14FourierCauchyConstant ψ * Real.pi *
        ∫ t in A..B, Complex.normSq (g t) := by
  rw [integral_schwartz_mul_normSq_logSpatialTransform_eq_doubleIntegral
    g hg ψ hAB]
  exact norm_intervalIntegral_intervalIntegral_mul_smoothSpatialKernel_le
    g hg ψ hAB

/-! ## A nonnegative compact logarithmic cutoff -/

/-- Pointwise squared modulus of the repository's compact logarithmic
trapezoid window. -/
def lemma14PositiveLogCutoffFun
    (delta L R : ℝ) (hdelta : 0 < delta) (y : ℝ) : ℂ :=
  conj (logTrapezoidWindow delta L R hdelta y) *
    logTrapezoidWindow delta L R hdelta y

/-- The positive cutoff packaged as a Schwartz function. -/
def lemma14PositiveLogCutoff
    (delta L R : ℝ) (hdelta : 0 < delta) : 𝓢(ℝ, ℂ) := by
  let w : ℝ → ℂ := logTrapezoidWindow delta L R hdelta
  have hs : HasCompactSupport (fun y ↦ conj (w y) * w y) :=
    (hasCompactSupport_logTrapezoidWindow delta L R hdelta).mul_left
  have hw := contDiff_logTrapezoidWindow delta L R hdelta
  have hc := Complex.conjCLE.contDiff.comp hw
  exact hs.toSchwartzMap (by
    simpa only [Function.comp_apply, Complex.conjCLE_apply, w] using hc.mul hw)

@[simp] theorem lemma14PositiveLogCutoff_apply
    (delta L R : ℝ) (hdelta : 0 < delta) (y : ℝ) :
    lemma14PositiveLogCutoff delta L R hdelta y =
      lemma14PositiveLogCutoffFun delta L R hdelta y := by
  unfold lemma14PositiveLogCutoff
  rfl

theorem lemma14PositiveLogCutoff_apply_eq_normSq
    (delta L R : ℝ) (hdelta : 0 < delta) (y : ℝ) :
    lemma14PositiveLogCutoff delta L R hdelta y =
      (Complex.normSq (logTrapezoidWindow delta L R hdelta y) : ℂ) := by
  rw [lemma14PositiveLogCutoff_apply]
  exact_mod_cast Complex.normSq_eq_conj_mul_self.symm

theorem lemma14PositiveLogCutoff_re_nonneg
    (delta L R : ℝ) (hdelta : 0 < delta) (y : ℝ) :
    0 ≤ (lemma14PositiveLogCutoff delta L R hdelta y).re := by
  rw [lemma14PositiveLogCutoff_apply_eq_normSq]
  simp only [Complex.ofReal_re]
  exact Complex.normSq_nonneg _

theorem lemma14PositiveLogCutoff_im_eq_zero
    (delta L R : ℝ) (hdelta : 0 < delta) (y : ℝ) :
    (lemma14PositiveLogCutoff delta L R hdelta y).im = 0 := by
  rw [lemma14PositiveLogCutoff_apply_eq_normSq]
  exact Complex.ofReal_im _

theorem lemma14PositiveLogCutoff_norm_le_one
    (delta L R : ℝ) (hdelta : 0 < delta) (y : ℝ) :
    ‖lemma14PositiveLogCutoff delta L R hdelta y‖ ≤ 1 := by
  rw [lemma14PositiveLogCutoff_apply_eq_normSq, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (Complex.normSq_nonneg _),
    Complex.normSq_eq_norm_sq]
  nlinarith [norm_logTrapezoidWindow_le_one delta L R hdelta y,
    norm_nonneg (logTrapezoidWindow delta L R hdelta y)]

/-- On the full interior plateau the positive cutoff is exactly one. -/
theorem lemma14PositiveLogCutoff_eq_one_of_mem_interior
    (delta L R : ℝ) (hdelta : 0 < delta) {y : ℝ}
    (hy : y ∈ Set.Icc (L + 2 * delta) (R - 2 * delta)) :
    lemma14PositiveLogCutoff delta L R hdelta y = 1 := by
  rw [lemma14PositiveLogCutoff_apply]
  unfold lemma14PositiveLogCutoffFun
  rw [logTrapezoidWindow_eq_one_of_mem_interior delta L R hdelta hy]
  simp

/-- The positive cutoff retains the same compact support interval. -/
theorem lemma14PositiveLogCutoff_eq_zero_of_not_mem
    (delta L R : ℝ) (hdelta : 0 < delta) {y : ℝ}
    (hy : y ∉ Set.Icc L R) :
    lemma14PositiveLogCutoff delta L R hdelta y = 0 := by
  rw [lemma14PositiveLogCutoff_apply]
  unfold lemma14PositiveLogCutoffFun
  rw [logTrapezoidWindow_eq_zero_of_not_mem delta L R hdelta hy]
  simp

theorem hasCompactSupport_lemma14PositiveLogCutoff
    (delta L R : ℝ) (hdelta : 0 < delta) :
    HasCompactSupport (lemma14PositiveLogCutoff delta L R hdelta) := by
  let w : ℝ → ℂ := logTrapezoidWindow delta L R hdelta
  have hs : HasCompactSupport (fun y ↦ conj (w y) * w y) :=
    (hasCompactSupport_logTrapezoidWindow delta L R hdelta).mul_left
  apply hs.mono
  intro y hy
  rw [Function.mem_support] at hy ⊢
  simpa only [lemma14PositiveLogCutoff_apply, lemma14PositiveLogCutoffFun, w]
    using hy

/-- A nonnegative continuous energy on the interior plateau is controlled by
the norm of its full-line integral against the positive Schwartz cutoff.
This is the compact-support localization needed before applying the
continuous Schur estimate. -/
theorem intervalIntegral_le_norm_integral_positiveLogCutoff
    (e : ℝ → ℝ) (he : Continuous e) (he0 : ∀ y, 0 ≤ e y)
    (delta L R : ℝ) (hdelta : 0 < delta)
    (hLR : L + 2 * delta ≤ R - 2 * delta) :
    (∫ y in (L + 2 * delta)..(R - 2 * delta), e y) ≤
      ‖∫ y : ℝ, lemma14PositiveLogCutoff delta L R hdelta y * (e y : ℂ)‖ := by
  let ψ : ℝ → ℂ := lemma14PositiveLogCutoff delta L R hdelta
  let q : ℝ → ℝ := fun y ↦ (ψ y).re * e y
  let z : ℝ → ℂ := fun y ↦ ψ y * (e y : ℂ)
  have hψ : Continuous ψ :=
    (lemma14PositiveLogCutoff delta L R hdelta).continuous
  have hq : Continuous q := by
    dsimp only [q]
    fun_prop
  have hz : Continuous z := by
    dsimp only [z]
    fun_prop
  have hψc : HasCompactSupport ψ :=
    hasCompactSupport_lemma14PositiveLogCutoff delta L R hdelta
  have hzc : HasCompactSupport z := by
    exact hψc.mul_right
  have hzi : Integrable z := hz.integrable_of_hasCompactSupport hzc
  have hqc : HasCompactSupport q := by
    have hψre : HasCompactSupport (fun y ↦ (ψ y).re) := by
      change HasCompactSupport (Complex.re ∘ ψ)
      exact hψc.comp_left Complex.zero_re
    exact hψre.mul_right
  have hplateau :
      (∫ y in (L + 2 * delta)..(R - 2 * delta), e y) =
        ∫ y in (L + 2 * delta)..(R - 2 * delta), q y := by
    apply intervalIntegral.integral_congr
    intro y hy
    rw [Set.uIcc_of_le hLR] at hy
    have hψone : ψ y = 1 :=
      lemma14PositiveLogCutoff_eq_one_of_mem_interior delta L R hdelta hy
    simp only [q, hψone, Complex.one_re, one_mul]
  have hq0 : ∀ y, 0 ≤ q y := by
    intro y
    exact mul_nonneg
      (lemma14PositiveLogCutoff_re_nonneg delta L R hdelta y) (he0 y)
  have hsupport : Function.support q ⊆ Set.Ioc (L - 1) (R + 1) := by
    intro y hy
    have hyI : y ∈ Set.Icc L R := by
      by_contra hyn
      have hψzero :=
        lemma14PositiveLogCutoff_eq_zero_of_not_mem delta L R hdelta hyn
      have hψzero' : ψ y = 0 := hψzero
      exact hy (by simp only [q, hψzero', Complex.zero_re, zero_mul])
    exact ⟨by linarith [hyI.1], by linarith [hyI.2]⟩
  have hq_global :
      (∫ y in (L - 1)..(R + 1), q y) = ∫ y : ℝ, q y :=
    intervalIntegral.integral_eq_integral_of_support_subset hsupport
  have hre : (∫ y : ℝ, q y) = (∫ y : ℝ, z y).re := by
    calc
      (∫ y : ℝ, q y) = ∫ y : ℝ, (z y).re := by
        apply integral_congr_ae
        filter_upwards [] with y
        have hψim := lemma14PositiveLogCutoff_im_eq_zero delta L R hdelta y
        simp only [q, z, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
          mul_zero, sub_zero]
      _ = (∫ y : ℝ, z y).re := integral_re hzi
  calc
    (∫ y in (L + 2 * delta)..(R - 2 * delta), e y) =
        ∫ y in (L + 2 * delta)..(R - 2 * delta), q y := hplateau
    _ ≤ ∫ y in (L - 1)..(R + 1), q y := by
      apply intervalIntegral.integral_mono_interval
      · linarith
      · exact hLR
      · linarith
      · filter_upwards [] with y
        exact hq0 y
      · exact hq.intervalIntegrable _ _
    _ = ∫ y : ℝ, q y := hq_global
    _ = (∫ y : ℝ, z y).re := hre
    _ ≤ ‖∫ y : ℝ, z y‖ := Complex.re_le_norm _
    _ = ‖∫ y : ℝ,
        lemma14PositiveLogCutoff delta L R hdelta y * (e y : ℂ)‖ := by
      rfl

/-- Interior spatial energy of a finite logarithmic transform, localized by
the positive cutoff and then bounded with a constant independent of the
vertical band length. -/
theorem intervalIntegral_normSq_logSpatialTransform_le
    (g : ℝ → ℂ) (hg : Continuous g)
    (delta L R : ℝ) (hdelta : 0 < delta)
    (hLR : L + 2 * delta ≤ R - 2 * delta)
    {A B : ℝ} (hAB : A ≤ B) :
    (∫ y in (L + 2 * delta)..(R - 2 * delta),
        Complex.normSq (lemma14LogSpatialTransform g A B y)) ≤
      lemma14FourierCauchyConstant
          (lemma14PositiveLogCutoff delta L R hdelta) * Real.pi *
        ∫ t in A..B, Complex.normSq (g t) := by
  calc
    (∫ y in (L + 2 * delta)..(R - 2 * delta),
        Complex.normSq (lemma14LogSpatialTransform g A B y)) ≤
      ‖∫ y : ℝ, lemma14PositiveLogCutoff delta L R hdelta y *
        (Complex.normSq (lemma14LogSpatialTransform g A B y) : ℂ)‖ := by
      exact intervalIntegral_le_norm_integral_positiveLogCutoff
        (fun y ↦ Complex.normSq (lemma14LogSpatialTransform g A B y))
        (Complex.continuous_normSq.comp
          (continuous_lemma14LogSpatialTransform g hg A B))
        (fun y ↦ Complex.normSq_nonneg _) delta L R hdelta hLR
    _ ≤ lemma14FourierCauchyConstant
          (lemma14PositiveLogCutoff delta L R hdelta) * Real.pi *
        ∫ t in A..B, Complex.normSq (g t) :=
      norm_integral_schwartz_mul_normSq_logSpatialTransform_le
        g hg (lemma14PositiveLogCutoff delta L R hdelta) hAB

end

end Erdos67b
