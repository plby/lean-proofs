import ErdosProblems.Erdos67.MRTMajorArc
import Mathlib.NumberTheory.MulChar.Lemmas
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import BoundedGaps.BombieriVinogradov.Analytic.CosecantHilbert

/-!
# The Matomäki--Radziwiłł mean-square proof

This file begins the unconditional proof of
`MRComplexNonpretentiousMeanSquareInput`.  The first step is the exact finite autocorrelation
expansion of the uncentered short-interval second moment, together with the twist-distance
identity which transfers the global MRT hypothesis to every bounded-conductor Dirichlet
twist.  Keeping these identities explicit isolates the finite layer from the remaining
Dirichlet-polynomial estimates.
-/

open scoped BigOperators ComplexConjugate Topology
open Finset
open Filter

namespace Erdos67

noncomputable section

/-! ## Finite logarithmic Dirichlet polynomials -/

/-- The pure logarithmic phase `exp(i t log n)`.  This exponential presentation is convenient
for interval integration and agrees with the usual `n^{it}` on positive integers. -/
def logarithmicPhase (n : ℕ) (t : ℝ) : ℂ :=
  Complex.exp (((t * Real.log n : ℝ) : ℂ) * Complex.I)

@[simp]
theorem norm_logarithmicPhase (n : ℕ) (t : ℝ) :
    ‖logarithmicPhase n t‖ = 1 := by
  exact Complex.norm_exp_ofReal_mul_I _

/-- A finite Dirichlet polynomial written using logarithmic phases. -/
def logarithmicDirichletPolynomial (S : Finset ℕ) (a : ℕ → ℂ) (t : ℝ) : ℂ :=
  ∑ n ∈ S, a n * logarithmicPhase n t

/-- The product of two logarithmic phases is the exponential at the difference frequency. -/
theorem conj_logarithmicPhase_mul_logarithmicPhase (m n : ℕ) (t : ℝ) :
    conj (logarithmicPhase m t) * logarithmicPhase n t =
      Complex.exp (((t * (Real.log n - Real.log m) : ℝ) : ℂ) * Complex.I) := by
  rw [logarithmicPhase, logarithmicPhase, ← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

/-- Pointwise square expansion of a finite logarithmic Dirichlet polynomial. -/
theorem conj_logarithmicDirichletPolynomial_mul_self
    (S : Finset ℕ) (a : ℕ → ℂ) (t : ℝ) :
    conj (logarithmicDirichletPolynomial S a t) *
        logarithmicDirichletPolynomial S a t =
      ∑ m ∈ S, ∑ n ∈ S,
        conj (a m) * a n *
          Complex.exp (((t * (Real.log n - Real.log m) : ℝ) : ℂ) * Complex.I) := by
  unfold logarithmicDirichletPolynomial
  rw [map_sum]
  simp only [map_mul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro m hm
  apply Finset.sum_congr rfl
  intro n hn
  rw [show conj (a m) * conj (logarithmicPhase m t) *
      (a n * logarithmicPhase n t) =
      conj (a m) * a n *
        (conj (logarithmicPhase m t) * logarithmicPhase n t) by ring]
  rw [conj_logarithmicPhase_mul_logarithmicPhase]

/-- Exact interval-integral expansion of the square of a finite Dirichlet polynomial.  This
is the first identity in the continuous Matomäki--Radziwiłł mean-value argument; no limiting
or convergence interchange is involved because the support is finite. -/
theorem logarithmicDirichletPolynomial_intervalIntegral_expansion
    (S : Finset ℕ) (a : ℕ → ℂ) (T : ℝ) :
    (∫ t in -T..T,
        conj (logarithmicDirichletPolynomial S a t) *
          logarithmicDirichletPolynomial S a t) =
      ∑ m ∈ S, ∑ n ∈ S,
        conj (a m) * a n *
          (∫ t in -T..T,
            Complex.exp (((t * (Real.log n - Real.log m) : ℝ) : ℂ) * Complex.I)) := by
  simp_rw [conj_logarithmicDirichletPolynomial_mul_self]
  rw [intervalIntegral.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro m hm
    rw [intervalIntegral.integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro n hn
      rw [intervalIntegral.integral_const_mul]
    · intro n hn
      apply Continuous.intervalIntegrable
      fun_prop
  · intro m hm
    apply Continuous.intervalIntegrable
    fun_prop

/-- The continuous Dirichlet kernel at logarithmic frequency `u`. -/
def logarithmicDirichletKernel (T u : ℝ) : ℂ :=
  ∫ t in -T..T,
    Complex.exp (((t * u : ℝ) : ℂ) * Complex.I)

@[simp]
theorem logarithmicDirichletKernel_zero (T : ℝ) :
    logarithmicDirichletKernel T 0 = 2 * T := by
  unfold logarithmicDirichletKernel
  simp
  ring

/-- Exact endpoint formula for the off-diagonal continuous Dirichlet kernel. -/
theorem logarithmicDirichletKernel_eq_exp_sub_div
    (T u : ℝ) (hu : u ≠ 0) :
    logarithmicDirichletKernel T u =
      (Complex.exp (((u : ℂ) * Complex.I) * T) -
        Complex.exp (((u : ℂ) * Complex.I) * (-T))) /
          ((u : ℂ) * Complex.I) := by
  unfold logarithmicDirichletKernel
  rw [show (fun t : ℝ ↦
      Complex.exp (((t * u : ℝ) : ℂ) * Complex.I)) =
      fun t : ℝ ↦ Complex.exp (((u : ℂ) * Complex.I) * t) by
        funext t
        congr 1
        push_cast
        ring]
  have hc : (u : ℂ) * Complex.I ≠ 0 :=
    mul_ne_zero (by exact_mod_cast hu) Complex.I_ne_zero
  convert (integral_exp_mul_complex (a := -T) (b := T) (c := (u : ℂ) * Complex.I) hc)
    using 1 <;> (push_cast; ring_nf)

/-- Sine-kernel evaluation of the off-diagonal continuous Dirichlet kernel. -/
theorem logarithmicDirichletKernel_eq_sin_div
    (T u : ℝ) (hu : u ≠ 0) :
    logarithmicDirichletKernel T u =
      ((2 * Real.sin (u * T) / u : ℝ) : ℂ) := by
  rw [logarithmicDirichletKernel_eq_exp_sub_div T u hu]
  rw [show ((u : ℂ) * Complex.I) * (T : ℂ) =
      (((u * T : ℝ) : ℂ) * Complex.I) by
        push_cast
        ring]
  rw [show ((u : ℂ) * Complex.I) * (-(T : ℂ)) =
      (((-(u * T) : ℝ) : ℂ) * Complex.I) by
        push_cast
        ring]
  simp only [Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg,
    ← Complex.ofReal_cos, ← Complex.ofReal_sin, Complex.ofReal_neg]
  push_cast
  field_simp [hu]
  ring

/-- The elementary off-diagonal kernel bound used before the Hilbert-inequality step. -/
theorem norm_logarithmicDirichletKernel_le
    (T u : ℝ) (hu : u ≠ 0) :
    ‖logarithmicDirichletKernel T u‖ ≤ 2 / |u| := by
  rw [logarithmicDirichletKernel_eq_exp_sub_div T u hu, norm_div]
  have hplus :
      ‖Complex.exp (((u : ℂ) * Complex.I) * T)‖ = 1 := by
    rw [show ((u : ℂ) * Complex.I) * (T : ℂ) =
      (((u * T : ℝ) : ℂ) * Complex.I) by
        push_cast
        ring]
    exact Complex.norm_exp_ofReal_mul_I _
  have hminus :
      ‖Complex.exp (((u : ℂ) * Complex.I) * (-T))‖ = 1 := by
    rw [show ((u : ℂ) * Complex.I) * (-(T : ℂ)) =
      (((u * (-T) : ℝ) : ℂ) * Complex.I) by
        push_cast
        ring]
    exact Complex.norm_exp_ofReal_mul_I _
  have hden : ‖(u : ℂ) * Complex.I‖ = |u| := by
    rw [norm_mul, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs]
  rw [hden]
  calc
    ‖Complex.exp (((u : ℂ) * Complex.I) * T) -
        Complex.exp (((u : ℂ) * Complex.I) * (-T))‖ / |u| ≤
        (‖Complex.exp (((u : ℂ) * Complex.I) * T)‖ +
          ‖Complex.exp (((u : ℂ) * Complex.I) * (-T))‖) / |u| := by
      exact div_le_div_of_nonneg_right (norm_sub_le _ _) (abs_nonneg u)
    _ = 2 / |u| := by rw [hplus, hminus]; norm_num

/-- A finite real-frequency family may be rescaled into the unit circle without losing its
separation, provided every rescaled difference lies in the centered half-period.  Applying the
coefficient-one cosecant Hilbert inequality then gives this exact finite bound.  Passing this
estimate to the small-scale limit is the standard route to the ordinary Hilbert inequality. -/
theorem norm_rescaled_cosecantBilinearForm_le
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (freq : ι → ℝ) (u : ι → ℂ) {ε δ : ℝ}
    (hε : 0 < ε) (hδ : 0 < δ)
    (hsep : ∀ r s, r ≠ s → δ ≤ |freq r - freq s|)
    (hhalf : ∀ r s, r ≠ s → |ε * (freq r - freq s)| ≤ (1 : ℝ) / 2) :
    ‖BoundedGaps.Maynard.cosecantBilinearForm (fun r ↦ ε * freq r) u‖ ≤
      (ε * δ)⁻¹ * ∑ r, ‖u r‖ ^ 2 := by
  apply BoundedGaps.Maynard.norm_cosecantBilinearForm_le
    (fun r ↦ ε * freq r) (mul_pos hε hδ)
  intro r s hrs
  have hdist :
      dist ((ε * freq r : ℝ) : UnitAddCircle) ((ε * freq s : ℝ) : UnitAddCircle) =
        |ε * (freq r - freq s)| := by
    rw [dist_eq_norm]
    calc
      ‖((ε * freq r : ℝ) : UnitAddCircle) - ((ε * freq s : ℝ) : UnitAddCircle)‖ =
          ‖((ε * (freq r - freq s) : ℝ) : UnitAddCircle)‖ := by
            change ‖QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℝ)) (ε * freq r) -
                QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℝ)) (ε * freq s)‖ =
              ‖QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℝ))
                (ε * (freq r - freq s))‖
            rw [← map_sub]
            congr 2
            ring
      _ = |ε * (freq r - freq s)| :=
        (AddCircle.norm_coe_eq_abs_iff (p := 1) one_ne_zero).2 (by
          simpa using hhalf r s hrs)
  rw [hdist, abs_mul, abs_of_pos hε]
  exact mul_le_mul_of_nonneg_left (hsep r s hrs) hε.le

/-- The removable-singularity regularization of the rescaled cosecant kernel.  At scale zero
it is the ordinary Hilbert kernel `d⁻¹`. -/
def regularizedReciprocalKernel (d scale : ℝ) : ℝ :=
  (d * Real.sinc (Real.pi * scale * d))⁻¹

@[simp]
theorem regularizedReciprocalKernel_zero (d : ℝ) :
    regularizedReciprocalKernel d 0 = d⁻¹ := by
  simp [regularizedReciprocalKernel, Real.sinc_zero]

/-- The regularized kernel is continuous at scale zero when `d` is nonzero. -/
theorem continuousAt_regularizedReciprocalKernel {d : ℝ} (hd : d ≠ 0) :
    ContinuousAt (regularizedReciprocalKernel d) 0 := by
  unfold regularizedReciprocalKernel
  apply ContinuousAt.inv₀
  · fun_prop
  · simpa [Real.sinc_zero] using hd

/-- Away from scale zero, the regularized kernel is exactly the rescaled cosecant kernel. -/
theorem regularizedReciprocalKernel_eq_cosecant
    {d scale : ℝ} (hd : d ≠ 0) (hscale : scale ≠ 0) :
    regularizedReciprocalKernel d scale =
      Real.pi * scale * (Real.sin (Real.pi * scale * d))⁻¹ := by
  unfold regularizedReciprocalKernel
  have hz : Real.pi * scale * d ≠ 0 :=
    mul_ne_zero (mul_ne_zero Real.pi_ne_zero hscale) hd
  rw [Real.sinc_of_ne_zero hz]
  by_cases hsin : Real.sin (Real.pi * scale * d) = 0
  · simp [hsin]
  · field_simp [hd, hscale, hsin, Real.pi_ne_zero]

/-- The ordinary coefficient-one Hilbert bilinear form on a finite frequency family. -/
def realHilbertBilinearForm
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (freq : ι → ℝ) (u : ι → ℂ) : ℂ :=
  ∑ r, ∑ s ∈ Finset.univ.erase r,
    u r * conj (u s) * ((((freq r - freq s)⁻¹ : ℝ)) : ℂ)

/-- The continuous-at-zero regularization used to obtain the real Hilbert kernel from the
cosecant kernel. -/
def regularizedHilbertBilinearForm
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (freq : ι → ℝ) (u : ι → ℂ) (scale : ℝ) : ℂ :=
  ∑ r, ∑ s ∈ Finset.univ.erase r,
    u r * conj (u s) *
      (regularizedReciprocalKernel (freq r - freq s) scale : ℂ)

@[simp]
theorem regularizedHilbertBilinearForm_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (freq : ι → ℝ) (u : ι → ℂ) :
    regularizedHilbertBilinearForm freq u 0 = realHilbertBilinearForm freq u := by
  simp [regularizedHilbertBilinearForm, realHilbertBilinearForm]

/-- At nonzero scale the regularized form is exactly `π * scale` times the cosecant form. -/
theorem regularizedHilbertBilinearForm_eq_cosecant
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {freq : ι → ℝ} (hfreq : Function.Injective freq) (u : ι → ℂ)
    {scale : ℝ} (hscale : scale ≠ 0) :
    regularizedHilbertBilinearForm freq u scale =
      ((Real.pi * scale : ℝ) : ℂ) *
        BoundedGaps.Maynard.cosecantBilinearForm (fun r ↦ scale * freq r) u := by
  unfold regularizedHilbertBilinearForm BoundedGaps.Maynard.cosecantBilinearForm
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s hs
  have hrs : r ≠ s := Ne.symm (Finset.ne_of_mem_erase hs)
  rw [regularizedReciprocalKernel_eq_cosecant
    (sub_ne_zero.mpr (hfreq.ne hrs)) hscale]
  push_cast
  simp only [RCLike.star_def]
  ring_nf

/-- The finite regularized Hilbert form is continuous at scale zero. -/
theorem continuousAt_regularizedHilbertBilinearForm
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {freq : ι → ℝ} (hfreq : Function.Injective freq) (u : ι → ℂ) :
    ContinuousAt (regularizedHilbertBilinearForm freq u) 0 := by
  unfold regularizedHilbertBilinearForm
  apply tendsto_finsetSum
  intro r hr
  apply tendsto_finsetSum
  intro s hs
  apply ContinuousAt.mul continuousAt_const
  exact RCLike.continuous_ofReal.continuousAt.comp'
    (continuousAt_regularizedReciprocalKernel
      (sub_ne_zero.mpr (hfreq.ne (Ne.symm (Finset.ne_of_mem_erase hs)))))

/-- The ordinary coefficient-one Hilbert inequality follows from the cosecant inequality along
any positive scale sequence tending to zero and remaining inside the centered half-period. -/
theorem norm_realHilbertBilinearForm_le_of_scales
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {freq : ι → ℝ} (hfreq : Function.Injective freq) (u : ι → ℂ)
    {δ : ℝ} (hδ : 0 < δ)
    (hsep : ∀ r s, r ≠ s → δ ≤ |freq r - freq s|)
    (scale : ℕ → ℝ) (hscale : ∀ k, 0 < scale k)
    (hscale0 : Tendsto scale atTop (𝓝 0))
    (hhalf : ∀ k r s, r ≠ s →
      |scale k * (freq r - freq s)| ≤ (1 : ℝ) / 2) :
    ‖realHilbertBilinearForm freq u‖ ≤
      Real.pi * δ⁻¹ * ∑ r, ‖u r‖ ^ 2 := by
  have hbound : ∀ k : ℕ,
      ‖regularizedHilbertBilinearForm freq u (scale k)‖ ≤
        Real.pi * δ⁻¹ * ∑ r, ‖u r‖ ^ 2 := by
    intro k
    have hcsc := norm_rescaled_cosecantBilinearForm_le freq u
      (hscale k) hδ hsep (hhalf k)
    rw [regularizedHilbertBilinearForm_eq_cosecant hfreq u (hscale k).ne', norm_mul]
    have hpiscale : ‖(((Real.pi * scale k : ℝ) : ℂ))‖ =
        Real.pi * scale k := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (mul_pos Real.pi_pos (hscale k))]
    rw [hpiscale]
    calc
      Real.pi * scale k *
          ‖BoundedGaps.Maynard.cosecantBilinearForm
            (fun r ↦ scale k * freq r) u‖ ≤
          Real.pi * scale k *
            ((scale k * δ)⁻¹ * ∑ r, ‖u r‖ ^ 2) := by
        exact mul_le_mul_of_nonneg_left hcsc
          (mul_nonneg Real.pi_pos.le (hscale k).le)
      _ = Real.pi * δ⁻¹ * ∑ r, ‖u r‖ ^ 2 := by
        field_simp [(hscale k).ne', hδ.ne']
  have hlim : Tendsto
      (fun k ↦ ‖regularizedHilbertBilinearForm freq u (scale k)‖)
      atTop (𝓝 ‖realHilbertBilinearForm freq u‖) := by
    have hform := (continuousAt_regularizedHilbertBilinearForm hfreq u).tendsto.comp hscale0
    have hnorm := hform.norm
    simpa using hnorm
  exact le_of_tendsto' hlim hbound

/-- Total absolute frequency spread, used only to choose a uniformly valid rescaling. -/
def frequencyDifferenceMass
    {ι : Type*} [Fintype ι] (freq : ι → ℝ) : ℝ :=
  ∑ r, ∑ s, |freq r - freq s|

theorem abs_frequency_sub_le_frequencyDifferenceMass
    {ι : Type*} [Fintype ι] (freq : ι → ℝ) (r s : ι) :
    |freq r - freq s| ≤ frequencyDifferenceMass freq := by
  unfold frequencyDifferenceMass
  calc
    |freq r - freq s| ≤ ∑ s, |freq r - freq s| :=
      Finset.single_le_sum (f := fun s ↦ |freq r - freq s|)
        (fun _ _ ↦ abs_nonneg _) (Finset.mem_univ s)
    _ ≤ ∑ r, ∑ s, |freq r - freq s| :=
      Finset.single_le_sum (f := fun r ↦ ∑ s, |freq r - freq s|)
        (fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ abs_nonneg _) (Finset.mem_univ r)

/-- Montgomery--Vaughan's ordinary coefficient-one Hilbert inequality, derived by finite
rescaling from the available cosecant theorem. -/
theorem norm_realHilbertBilinearForm_le
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (freq : ι → ℝ) (u : ι → ℂ) {δ : ℝ} (hδ : 0 < δ)
    (hsep : ∀ r s, r ≠ s → δ ≤ |freq r - freq s|) :
    ‖realHilbertBilinearForm freq u‖ ≤
      Real.pi * δ⁻¹ * ∑ r, ‖u r‖ ^ 2 := by
  have hfreq : Function.Injective freq := by
    intro r s hrs
    by_contra hne
    have h := hsep r s hne
    rw [hrs, sub_self, abs_zero] at h
    linarith
  let mass : ℝ := frequencyDifferenceMass freq
  have hmass : 0 ≤ mass := by
    dsimp [mass, frequencyDifferenceMass]
    exact Finset.sum_nonneg fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ abs_nonneg _
  let C : ℝ := 2 * (mass + 1)
  have hC : 0 < C := by dsimp [C]; positivity
  let scale : ℕ → ℝ := fun k ↦ (((k : ℝ) + 1) * C)⁻¹
  have hscale : ∀ k, 0 < scale k := by
    intro k
    dsimp [scale]
    positivity
  have hscale0 : Tendsto scale atTop (𝓝 0) := by
    have htop : Tendsto (fun k : ℕ ↦ (k : ℝ) + 1) atTop atTop :=
      tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
    have hinv : Tendsto (fun k : ℕ ↦ ((k : ℝ) + 1)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp htop
    have hmul := hinv.mul_const C⁻¹
    simpa only [scale, mul_inv_rev, zero_mul, mul_comm] using hmul
  apply norm_realHilbertBilinearForm_le_of_scales hfreq u hδ hsep scale hscale hscale0
  intro k r s hrs
  rw [abs_mul, abs_of_pos (hscale k)]
  calc
    scale k * |freq r - freq s| ≤ scale k * mass := by
      gcongr
      exact abs_frequency_sub_le_frequencyDifferenceMass freq r s
    _ ≤ (1 : ℝ) / 2 := by
      dsimp [scale]
      rw [inv_mul_eq_div]
      apply (div_le_iff₀ (mul_pos (by positivity : 0 < (k : ℝ) + 1) hC)).2
      dsimp [C]
      have hk : 0 ≤ (k : ℝ) := by positivity
      have hm1 : 0 ≤ mass + 1 := by positivity
      nlinarith [mul_nonneg hk hm1]

/-! ## The continuous Dirichlet-polynomial mean-value bound -/

/-- A pure imaginary exponential at a real argument. -/
def realExponentialPhase (x : ℝ) : ℂ :=
  Complex.exp ((x : ℂ) * Complex.I)

@[fun_prop]
theorem continuous_realExponentialPhase : Continuous realExponentialPhase := by
  unfold realExponentialPhase
  fun_prop

@[simp]
theorem norm_realExponentialPhase (x : ℝ) : ‖realExponentialPhase x‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I x

theorem conj_realExponentialPhase (x : ℝ) :
    conj (realExponentialPhase x) = realExponentialPhase (-x) := by
  unfold realExponentialPhase
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

theorem realExponentialPhase_mul (x y : ℝ) :
    realExponentialPhase x * realExponentialPhase y =
      realExponentialPhase (x + y) := by
  unfold realExponentialPhase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The two boundary coefficient families whose Hilbert forms produce the sine kernel. -/
def negativeBoundaryCoeff
    {ι : Type*} (freq : ι → ℝ) (a : ι → ℂ) (T : ℝ) (r : ι) : ℂ :=
  conj (a r) * realExponentialPhase (-T * freq r)

def positiveBoundaryCoeff
    {ι : Type*} (freq : ι → ℝ) (a : ι → ℂ) (T : ℝ) (r : ι) : ℂ :=
  conj (a r) * realExponentialPhase (T * freq r)

@[simp]
theorem norm_negativeBoundaryCoeff
    {ι : Type*} (freq : ι → ℝ) (a : ι → ℂ) (T : ℝ) (r : ι) :
    ‖negativeBoundaryCoeff freq a T r‖ = ‖a r‖ := by
  simp [negativeBoundaryCoeff, norm_realExponentialPhase]

@[simp]
theorem norm_positiveBoundaryCoeff
    {ι : Type*} (freq : ι → ℝ) (a : ι → ℂ) (T : ℝ) (r : ι) :
    ‖positiveBoundaryCoeff freq a T r‖ = ‖a r‖ := by
  simp [positiveBoundaryCoeff, norm_realExponentialPhase]

theorem negativeBoundaryCoeff_mul_conj
    {ι : Type*} (freq : ι → ℝ) (a : ι → ℂ) (T : ℝ) (r s : ι) :
    negativeBoundaryCoeff freq a T r * conj (negativeBoundaryCoeff freq a T s) =
      conj (a r) * a s * realExponentialPhase (T * (freq s - freq r)) := by
  unfold negativeBoundaryCoeff
  rw [map_mul, starRingEnd_self_apply, conj_realExponentialPhase]
  rw [show conj (a r) * realExponentialPhase (-T * freq r) *
      (a s * realExponentialPhase (-(-T * freq s))) =
      conj (a r) * a s *
        (realExponentialPhase (-T * freq r) *
          realExponentialPhase (-(-T * freq s))) by ring]
  rw [realExponentialPhase_mul]
  congr 2
  ring

theorem positiveBoundaryCoeff_mul_conj
    {ι : Type*} (freq : ι → ℝ) (a : ι → ℂ) (T : ℝ) (r s : ι) :
    positiveBoundaryCoeff freq a T r * conj (positiveBoundaryCoeff freq a T s) =
      conj (a r) * a s * realExponentialPhase (-T * (freq s - freq r)) := by
  unfold positiveBoundaryCoeff
  rw [map_mul, starRingEnd_self_apply, conj_realExponentialPhase]
  rw [show conj (a r) * realExponentialPhase (T * freq r) *
      (a s * realExponentialPhase (-(T * freq s))) =
      conj (a r) * a s *
        (realExponentialPhase (T * freq r) *
          realExponentialPhase (-(T * freq s))) by ring]
  rw [realExponentialPhase_mul]
  congr 2
  ring

/-- One off-diagonal sine-kernel term is the difference of the two boundary Hilbert terms. -/
theorem mul_logarithmicDirichletKernel_eq_boundaryTerms
    {ι : Type*} {freq : ι → ℝ} (a : ι → ℂ) (T : ℝ)
    {r s : ι} (hrs : freq r ≠ freq s) :
    conj (a r) * a s *
        logarithmicDirichletKernel T (freq s - freq r) =
      Complex.I *
        (negativeBoundaryCoeff freq a T r *
              conj (negativeBoundaryCoeff freq a T s) *
              ((((freq r - freq s)⁻¹ : ℝ)) : ℂ) -
          positiveBoundaryCoeff freq a T r *
              conj (positiveBoundaryCoeff freq a T s) *
              ((((freq r - freq s)⁻¹ : ℝ)) : ℂ)) := by
  rw [negativeBoundaryCoeff_mul_conj, positiveBoundaryCoeff_mul_conj]
  have hd : freq s - freq r ≠ 0 := sub_ne_zero.mpr hrs.symm
  rw [logarithmicDirichletKernel_eq_exp_sub_div T (freq s - freq r) hd]
  unfold realExponentialPhase
  rw [show ((((freq s - freq r : ℝ) : ℂ) * Complex.I) * (T : ℂ)) =
      (((T * (freq s - freq r) : ℝ) : ℂ) * Complex.I) by
        push_cast
        ring]
  rw [show ((((freq s - freq r : ℝ) : ℂ) * Complex.I) * (-(T : ℂ))) =
      (((-T * (freq s - freq r) : ℝ) : ℂ) * Complex.I) by
        push_cast
        ring]
  push_cast
  have hd' : (freq r : ℂ) - freq s ≠ 0 := by
    exact sub_ne_zero.mpr (by exact_mod_cast hrs)
  have hdC : (freq s : ℂ) - freq r ≠ 0 := by
    exact sub_ne_zero.mpr (by exact_mod_cast hrs.symm)
  field_simp [hd, hd', hdC, Complex.I_ne_zero]
  rw [Complex.I_sq]
  ring

/-- The full off-diagonal kernel sum is the difference of two Hilbert bilinear forms. -/
def logarithmicKernelOffDiagonal
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (freq : ι → ℝ) (a : ι → ℂ) (T : ℝ) : ℂ :=
  ∑ r, ∑ s ∈ Finset.univ.erase r,
    conj (a r) * a s * logarithmicDirichletKernel T (freq s - freq r)

theorem logarithmicKernelOffDiagonal_eq_boundaryHilbert
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {freq : ι → ℝ} (hfreq : Function.Injective freq) (a : ι → ℂ) (T : ℝ) :
    logarithmicKernelOffDiagonal freq a T =
      Complex.I *
        (realHilbertBilinearForm freq (negativeBoundaryCoeff freq a T) -
          realHilbertBilinearForm freq (positiveBoundaryCoeff freq a T)) := by
  unfold logarithmicKernelOffDiagonal realHilbertBilinearForm
  rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s hs
  exact mul_logarithmicDirichletKernel_eq_boundaryTerms a T
    (hfreq.ne (Ne.symm (Finset.ne_of_mem_erase hs)))

/-- Hilbert's inequality controls the complete off-diagonal sine-kernel contribution. -/
theorem norm_logarithmicKernelOffDiagonal_le
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (freq : ι → ℝ) (a : ι → ℂ) (T : ℝ) {δ : ℝ} (hδ : 0 < δ)
    (hsep : ∀ r s, r ≠ s → δ ≤ |freq r - freq s|) :
    ‖logarithmicKernelOffDiagonal freq a T‖ ≤
      2 * Real.pi * δ⁻¹ * ∑ r, ‖a r‖ ^ 2 := by
  have hfreq : Function.Injective freq := by
    intro r s hrs
    by_contra hne
    have h := hsep r s hne
    rw [hrs, sub_self, abs_zero] at h
    linarith
  rw [logarithmicKernelOffDiagonal_eq_boundaryHilbert hfreq]
  rw [norm_mul, Complex.norm_I, one_mul]
  have hneg := norm_realHilbertBilinearForm_le freq
    (negativeBoundaryCoeff freq a T) hδ hsep
  have hpos := norm_realHilbertBilinearForm_le freq
    (positiveBoundaryCoeff freq a T) hδ hsep
  simp only [norm_negativeBoundaryCoeff] at hneg
  simp only [norm_positiveBoundaryCoeff] at hpos
  calc
    ‖realHilbertBilinearForm freq (negativeBoundaryCoeff freq a T) -
        realHilbertBilinearForm freq (positiveBoundaryCoeff freq a T)‖ ≤
        ‖realHilbertBilinearForm freq (negativeBoundaryCoeff freq a T)‖ +
          ‖realHilbertBilinearForm freq (positiveBoundaryCoeff freq a T)‖ :=
      norm_sub_le _ _
    _ ≤ (Real.pi * δ⁻¹ * ∑ r, ‖a r‖ ^ 2) +
          (Real.pi * δ⁻¹ * ∑ r, ‖a r‖ ^ 2) := add_le_add hneg hpos
    _ = 2 * Real.pi * δ⁻¹ * ∑ r, ‖a r‖ ^ 2 := by ring

/-- A finite exponential polynomial with arbitrary real frequencies. -/
def finiteFrequencyPolynomial
    {ι : Type*} [Fintype ι] (freq : ι → ℝ) (a : ι → ℂ) (t : ℝ) : ℂ :=
  ∑ r, a r * realExponentialPhase (t * freq r)

theorem conj_realExponentialPhase_mul_realExponentialPhase (x y : ℝ) :
    conj (realExponentialPhase x) * realExponentialPhase y =
      realExponentialPhase (y - x) := by
  rw [conj_realExponentialPhase, realExponentialPhase_mul]
  congr 1
  ring

theorem conj_finiteFrequencyPolynomial_mul_self
    {ι : Type*} [Fintype ι] (freq : ι → ℝ) (a : ι → ℂ) (t : ℝ) :
    conj (finiteFrequencyPolynomial freq a t) * finiteFrequencyPolynomial freq a t =
      ∑ r, ∑ s, conj (a r) * a s *
        realExponentialPhase (t * (freq s - freq r)) := by
  unfold finiteFrequencyPolynomial
  rw [map_sum]
  simp only [map_mul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r hr
  apply Finset.sum_congr rfl
  intro s hs
  rw [show conj (a r) * conj (realExponentialPhase (t * freq r)) *
      (a s * realExponentialPhase (t * freq s)) =
      conj (a r) * a s *
        (conj (realExponentialPhase (t * freq r)) *
          realExponentialPhase (t * freq s)) by ring]
  rw [conj_realExponentialPhase_mul_realExponentialPhase]
  congr 2
  ring

/-- Exact square-integral expansion for a finite real-frequency polynomial. -/
theorem finiteFrequencyPolynomial_intervalIntegral_kernel
    {ι : Type*} [Fintype ι]
    (freq : ι → ℝ) (a : ι → ℂ) (T : ℝ) :
    (∫ t in -T..T,
        conj (finiteFrequencyPolynomial freq a t) *
          finiteFrequencyPolynomial freq a t) =
      ∑ r, ∑ s, conj (a r) * a s *
        logarithmicDirichletKernel T (freq s - freq r) := by
  simp_rw [conj_finiteFrequencyPolynomial_mul_self]
  rw [intervalIntegral.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro r hr
    rw [intervalIntegral.integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro s hs
      rw [intervalIntegral.integral_const_mul]
      rfl
    · intro s hs
      apply Continuous.intervalIntegrable
      fun_prop
  · intro r hr
    apply Continuous.intervalIntegrable
    fun_prop

/-- Split a full Fintype double sum into its diagonal and row-wise erasures. -/
theorem sum_univ_pair_eq_diag_add_erase
    {ι M : Type*} [Fintype ι] [DecidableEq ι] [AddCommMonoid M]
    (F : ι → ι → M) :
    (∑ r, ∑ s, F r s) =
      (∑ r, F r r) + ∑ r, ∑ s ∈ Finset.univ.erase r, F r s := by
  calc
    (∑ r, ∑ s, F r s) =
        ∑ r, (F r r + ∑ s ∈ Finset.univ.erase r, F r s) := by
      apply Finset.sum_congr rfl
      intro r hr
      rw [add_comm, Finset.sum_erase_add _ _ (Finset.mem_univ r)]
    _ = (∑ r, F r r) + ∑ r, ∑ s ∈ Finset.univ.erase r, F r s := by
      rw [Finset.sum_add_distrib]

/-- Exact diagonal/off-diagonal decomposition of the continuous mean square. -/
theorem finiteFrequencyPolynomial_intervalIntegral_diag_offDiag
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (freq : ι → ℝ) (a : ι → ℂ) (T : ℝ) :
    (∫ t in -T..T,
        conj (finiteFrequencyPolynomial freq a t) *
          finiteFrequencyPolynomial freq a t) =
      (∑ r, ((2 * T : ℝ) : ℂ) * Complex.normSq (a r)) +
        logarithmicKernelOffDiagonal freq a T := by
  rw [finiteFrequencyPolynomial_intervalIntegral_kernel]
  rw [sum_univ_pair_eq_diag_add_erase]
  congr 1
  · apply Finset.sum_congr rfl
    intro r hr
    simp only [sub_self, logarithmicDirichletKernel_zero]
    rw [Complex.normSq_eq_conj_mul_self]
    push_cast
    ring

/-- The finite continuous Dirichlet-polynomial mean-square theorem. -/
theorem norm_finiteFrequencyPolynomial_intervalIntegral_le
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (freq : ι → ℝ) (a : ι → ℂ) {T δ : ℝ} (hT : 0 ≤ T) (hδ : 0 < δ)
    (hsep : ∀ r s, r ≠ s → δ ≤ |freq r - freq s|) :
    ‖∫ t in -T..T,
        conj (finiteFrequencyPolynomial freq a t) *
          finiteFrequencyPolynomial freq a t‖ ≤
      (2 * T + 2 * Real.pi * δ⁻¹) * ∑ r, ‖a r‖ ^ 2 := by
  rw [finiteFrequencyPolynomial_intervalIntegral_diag_offDiag]
  have hdiag :
      ‖∑ r, ((2 * T : ℝ) : ℂ) * Complex.normSq (a r)‖ ≤
        2 * T * ∑ r, ‖a r‖ ^ 2 := by
    calc
      ‖∑ r, ((2 * T : ℝ) : ℂ) * Complex.normSq (a r)‖ ≤
          ∑ r, ‖((2 * T : ℝ) : ℂ) * Complex.normSq (a r)‖ := norm_sum_le _ _
      _ = ∑ r, 2 * T * ‖a r‖ ^ 2 := by
        apply Finset.sum_congr rfl
        intro r hr
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (mul_nonneg (by norm_num) hT), Complex.norm_real,
          Real.norm_eq_abs, abs_of_nonneg (Complex.normSq_nonneg _),
          Complex.normSq_eq_norm_sq]
      _ = 2 * T * ∑ r, ‖a r‖ ^ 2 := by rw [Finset.mul_sum]
  have hoff := norm_logarithmicKernelOffDiagonal_le freq a T hδ hsep
  calc
    ‖(∑ r, ((2 * T : ℝ) : ℂ) * Complex.normSq (a r)) +
        logarithmicKernelOffDiagonal freq a T‖ ≤
        ‖∑ r, ((2 * T : ℝ) : ℂ) * Complex.normSq (a r)‖ +
          ‖logarithmicKernelOffDiagonal freq a T‖ := norm_add_le _ _
    _ ≤ 2 * T * ∑ r, ‖a r‖ ^ 2 +
          2 * Real.pi * δ⁻¹ * ∑ r, ‖a r‖ ^ 2 := add_le_add hdiag hoff
    _ = (2 * T + 2 * Real.pi * δ⁻¹) * ∑ r, ‖a r‖ ^ 2 := by ring

/-- Logarithms of distinct positive integers at most `N` are `1/N`-separated. -/
theorem inv_nat_le_abs_log_sub_log
    {m n N : ℕ} (hm : 0 < m) (hn : 0 < n) (hmN : m ≤ N) (hnN : n ≤ N)
    (hmn : m ≠ n) :
    (N : ℝ)⁻¹ ≤ |Real.log m - Real.log n| := by
  have hN : 0 < N := hn.trans_le hnN
  rcases lt_or_gt_of_ne hmn with hmnlt | hnmlt
  · have hmR : (0 : ℝ) < m := by exact_mod_cast hm
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have hNR : (0 : ℝ) < N := by exact_mod_cast hN
    have hfrac : (N : ℝ)⁻¹ ≤ 1 - (m : ℝ) / n := by
      have hgap : (m : ℝ) + 1 ≤ n := by exact_mod_cast (Nat.succ_le_iff.mpr hmnlt)
      have hnNR : (n : ℝ) ≤ N := by exact_mod_cast hnN
      rw [show 1 - (m : ℝ) / n = (n - m) / n by field_simp]
      rw [inv_eq_one_div]
      apply (div_le_div_iff₀ hNR hnR).2
      calc
        (1 : ℝ) * n = n := one_mul _
        _ ≤ N := hnNR
        _ = 1 * N := (one_mul _).symm
        _ ≤ (n - m) * N := by
          gcongr
          linarith
    have hlog := Real.one_sub_inv_le_log_of_pos (div_pos hnR hmR)
    rw [inv_div] at hlog
    have hmono : Real.log m ≤ Real.log n := Real.log_le_log hmR (by exact_mod_cast hmnlt.le)
    rw [abs_of_nonpos (sub_nonpos.mpr hmono)]
    calc
      (N : ℝ)⁻¹ ≤ 1 - (m : ℝ) / n := hfrac
      _ ≤ Real.log ((n : ℝ) / m) := hlog
      _ = Real.log n - Real.log m := Real.log_div hnR.ne' hmR.ne'
      _ = -(Real.log m - Real.log n) := by ring
  · have hmR : (0 : ℝ) < m := by exact_mod_cast hm
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have hNR : (0 : ℝ) < N := by exact_mod_cast hN
    have hfrac : (N : ℝ)⁻¹ ≤ 1 - (n : ℝ) / m := by
      have hgap : (n : ℝ) + 1 ≤ m := by exact_mod_cast (Nat.succ_le_iff.mpr hnmlt)
      have hmNR : (m : ℝ) ≤ N := by exact_mod_cast hmN
      rw [show 1 - (n : ℝ) / m = (m - n) / m by field_simp]
      rw [inv_eq_one_div]
      apply (div_le_div_iff₀ hNR hmR).2
      calc
        (1 : ℝ) * m = m := one_mul _
        _ ≤ N := hmNR
        _ = 1 * N := (one_mul _).symm
        _ ≤ (m - n) * N := by
          gcongr
          linarith
    have hlog := Real.one_sub_inv_le_log_of_pos (div_pos hmR hnR)
    rw [inv_div] at hlog
    have hmono : Real.log n ≤ Real.log m := Real.log_le_log hnR (by exact_mod_cast hnmlt.le)
    rw [abs_of_nonneg (sub_nonneg.mpr hmono)]
    calc
      (N : ℝ)⁻¹ ≤ 1 - (n : ℝ) / m := hfrac
      _ ≤ Real.log ((m : ℝ) / n) := hlog
      _ = Real.log m - Real.log n := Real.log_div hmR.ne' hnR.ne'

/-- The continuous mean-square theorem at the logarithmic frequencies of the positive
integers up to `N`.  The elementary spacing bound above makes the error term explicit:
it is `2πN` times the coefficient square mass. -/
theorem norm_finiteLogPolynomial_intervalIntegral_le
    {N : ℕ} (hN : 0 < N)
    (a : Fin N → ℂ) {T : ℝ} (hT : 0 ≤ T) :
    ‖∫ t in -T..T,
        conj (finiteFrequencyPolynomial (fun n => Real.log (n.1 + 1)) a t) *
          finiteFrequencyPolynomial (fun n => Real.log (n.1 + 1)) a t‖ ≤
      (2 * T + 2 * Real.pi * (N : ℝ)) * ∑ n, ‖a n‖ ^ 2 := by
  have hdelta : (0 : ℝ) < (N : ℝ)⁻¹ := inv_pos.mpr (by exact_mod_cast hN)
  have hsep : ∀ r s : Fin N, r ≠ s →
      (N : ℝ)⁻¹ ≤ |Real.log (r.1 + 1) - Real.log (s.1 + 1)| := by
    intro r s hrs
    have hrsval : r.1 + 1 ≠ s.1 + 1 := by
      intro h
      apply hrs
      apply Fin.ext
      omega
    simpa only [Nat.cast_add, Nat.cast_one] using
      (inv_nat_le_abs_log_sub_log (m := r.1 + 1) (n := s.1 + 1) (N := N)
        (Nat.zero_lt_succ _) (Nat.zero_lt_succ _)
        (Nat.succ_le_iff.mpr r.2) (Nat.succ_le_iff.mpr s.2) hrsval)
  simpa only [inv_inv] using
    (norm_finiteFrequencyPolynomial_intervalIntegral_le
      (fun n : Fin N => Real.log (n.1 + 1)) a hT hdelta hsep)

/-- Kernel form of the exact interval-integral expansion. -/
theorem logarithmicDirichletPolynomial_intervalIntegral_kernel
    (S : Finset ℕ) (a : ℕ → ℂ) (T : ℝ) :
    (∫ t in -T..T,
        conj (logarithmicDirichletPolynomial S a t) *
          logarithmicDirichletPolynomial S a t) =
      ∑ m ∈ S, ∑ n ∈ S,
        conj (a m) * a n *
          logarithmicDirichletKernel T (Real.log n - Real.log m) := by
  simpa only [logarithmicDirichletKernel] using
    logarithmicDirichletPolynomial_intervalIntegral_expansion S a T

/-- On positive integers, the `cpow` monomial used by `finiteDirichletPolynomial` is the
negative-parameter logarithmic phase. -/
theorem cpow_neg_I_mul_eq_logarithmicPhase_neg
    {n : ℕ} (hn : 0 < n) (t : ℝ) :
    (n : ℂ) ^ (-(Complex.I * (t : ℂ))) = logarithmicPhase n (-t) := by
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast (Nat.ne_of_gt hn))]
  unfold logarithmicPhase
  rw [← Complex.natCast_log]
  congr 1
  push_cast
  ring

/-- The local `finiteDirichletPolynomial` is exactly the logarithmic presentation, after
reversing the real frequency. -/
theorem finiteDirichletPolynomial_eq_logarithmic
    {S : Finset ℕ} (hS : ∀ n ∈ S, 0 < n) (a : ℕ → ℂ) (t : ℝ) :
    finiteDirichletPolynomial S a t =
      logarithmicDirichletPolynomial S a (-t) := by
  unfold finiteDirichletPolynomial logarithmicDirichletPolynomial
  apply Finset.sum_congr rfl
  intro n hn
  rw [cpow_neg_I_mul_eq_logarithmicPhase_neg (hS n hn)]

/-- Split a finite double sum into its diagonal and off-diagonal pairs. -/
theorem sum_pair_eq_sum_diag_add_sum_offDiag
    {α M : Type*} [DecidableEq α] [AddCommMonoid M]
    (S : Finset α) (F : α → α → M) :
    (∑ m ∈ S, ∑ n ∈ S, F m n) =
      (∑ m ∈ S, F m m) + ∑ p ∈ S.offDiag, F p.1 p.2 := by
  rw [← Finset.sum_product']
  rw [← Finset.diag_union_offDiag]
  rw [Finset.sum_union (Finset.disjoint_diag_offDiag S)]
  simp [Finset.diag]

/-- Exact diagonal/off-diagonal form of the Dirichlet-polynomial mean square. -/
theorem logarithmicDirichletPolynomial_intervalIntegral_diag_offDiag
    (S : Finset ℕ) (a : ℕ → ℂ) (T : ℝ) :
    (∫ t in -T..T,
        conj (logarithmicDirichletPolynomial S a t) *
          logarithmicDirichletPolynomial S a t) =
      (∑ m ∈ S, ((2 * T : ℝ) : ℂ) * Complex.normSq (a m)) +
        ∑ p ∈ S.offDiag,
          conj (a p.1) * a p.2 *
            logarithmicDirichletKernel T (Real.log p.2 - Real.log p.1) := by
  rw [logarithmicDirichletPolynomial_intervalIntegral_kernel]
  rw [sum_pair_eq_sum_diag_add_sum_offDiag]
  congr 1
  apply Finset.sum_congr rfl
  intro m hm
  simp only [sub_self, logarithmicDirichletKernel_zero]
  rw [Complex.normSq_eq_conj_mul_self]
  push_cast
  ring

/-- Center a sequence by its reference mean on `(X,2X]`. -/
def centeredAtLongMean (f : ℕ → ℂ) (X m : ℕ) : ℂ :=
  f m - longIntervalMean f X

/-! ## Pretentious distance under Dirichlet twists -/

/-- Twisting `f` by `χ` and measuring its distance from `n^{it}` is exactly the same as
measuring `f` against the inverse-character twist `χ⁻¹(n)n^{it}`. -/
theorem pretentiousDistSq_dirichletTwist_archimedean
    {q : ℕ} (f : ℕ → ℂ) (χ : DirichletCharacter ℂ q) (t : ℝ) (X : ℕ) :
    pretentiousDistSq (fun n ↦ f n * χ n) (archimedeanTwist t) X =
      pretentiousDistSqToTwist f χ⁻¹ t X := by
  unfold pretentiousDistSqToTwist pretentiousDistSq
  apply Finset.sum_congr rfl
  intro p hp
  unfold pretentiousTerm dirichletArchimedeanTwist
  congr 2
  rw [map_mul]
  have hχ : conj (χ⁻¹ (p : ZMod q)) = χ (p : ZMod q) := by
    simpa only [RCLike.star_def, inv_inv] using
      (MulChar.star_apply' (χ := χ⁻¹) (a := (p : ZMod q)))
  rw [hχ]
  ring_nf

/-- The global MRT nonpretentiousness condition implies Archimedean nonpretentiousness for
every bounded-conductor Dirichlet twist. -/
theorem mrtNonpretentious_dirichletTwist_archimedean
    {q A X : ℕ} {f : ℕ → ℂ} (χ : DirichletCharacter ℂ q)
    (hq : 0 < q) (hqA : q ≤ A) (hA : 1 ≤ A)
    (h : MRTNonpretentious f A X) :
    MRArchimedeanNonpretentious (fun n ↦ f n * χ n) A X := by
  intro t ht
  rw [pretentiousDistSq_dirichletTwist_archimedean]
  apply h q hq hqA χ⁻¹ t
  calc
    |t| ≤ X := ht
    _ ≤ (A : ℝ) * X := by
      have hAR : (1 : ℝ) ≤ A := by exact_mod_cast hA
      have hX : (0 : ℝ) ≤ X := Nat.cast_nonneg X
      nlinarith

/-- The discrepancy from `H` times the long mean is exactly the short sum of the centered
sequence. -/
theorem shortIntervalDeviation_eq_sum_centered
    (f : ℕ → ℂ) (X n H : ℕ) :
    shortIntervalDeviation f X n H =
      ∑ j ∈ Finset.Icc 1 H, centeredAtLongMean f X (n + j) := by
  unfold shortIntervalDeviation centeredAtLongMean
  rw [Finset.sum_sub_distrib]
  congr 1
  rw [Finset.sum_const, nsmul_eq_mul]
  simp

/-- Exact expansion of the squared norm of a finite complex sum into its two-point
correlations. -/
theorem normSq_finset_sum_eq_sum_correlation
    {ι : Type*} (s : Finset ι) (F : ι → ℂ) :
    Complex.normSq (∑ i ∈ s, F i) =
      ∑ i ∈ s, ∑ j ∈ s, (conj (F i) * F j).re := by
  classical
  have hc : ((Complex.normSq (∑ i ∈ s, F i) : ℝ) : ℂ) =
      ∑ i ∈ s, ∑ j ∈ s, conj (F i) * F j := by
    rw [Complex.normSq_eq_conj_mul_self, map_sum]
    simp only [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
  have hr := congrArg Complex.re hc
  simpa only [Complex.ofReal_re, Complex.re_sum] using hr

/-- Exact finite autocorrelation formula for the Matomäki--Radziwiłł second moment. -/
theorem shortIntervalMeanSquare_eq_sum_correlations
    (f : ℕ → ℂ) (X H : ℕ) :
    shortIntervalMeanSquare f X H =
      ∑ j ∈ Finset.Icc 1 H, ∑ k ∈ Finset.Icc 1 H,
        ∑ n ∈ Finset.Ioc X (2 * X),
          (conj (centeredAtLongMean f X (n + j)) *
            centeredAtLongMean f X (n + k)).re := by
  classical
  unfold shortIntervalMeanSquare
  simp_rw [shortIntervalDeviation_eq_sum_centered,
    normSq_finset_sum_eq_sum_correlation]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_comm]

/-- Exact finite autocorrelation formula for the uncentered complex short-interval moment in
Appendix A of Matomäki--Radziwiłł--Tao. -/
theorem uncenteredShortIntervalMeanSquare_eq_sum_correlations
    (f : ℕ → ℂ) (X H : ℕ) :
    uncenteredShortIntervalMeanSquare f X H =
      ∑ j ∈ Finset.Icc 1 H, ∑ k ∈ Finset.Icc 1 H,
        ∑ n ∈ Finset.Ioc X (2 * X),
          (conj (f (n + j)) * f (n + k)).re := by
  classical
  unfold uncenteredShortIntervalMeanSquare
  simp_rw [normSq_finset_sum_eq_sum_correlation]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_comm]

/-- The diagonal correlations of a pointwise unit-disc sequence cost at most `H X`. -/
theorem diagonal_centered_correlation_le
    (f : ℕ → ℂ) (X H : ℕ)
    (hf : ∀ m : ℕ, 0 < m → ‖f m‖ ≤ 1) :
    (∑ j ∈ Finset.Icc 1 H,
      ∑ n ∈ Finset.Ioc X (2 * X),
        Complex.normSq (f (n + j))) ≤ H * X := by
  calc
    (∑ j ∈ Finset.Icc 1 H,
      ∑ n ∈ Finset.Ioc X (2 * X), Complex.normSq (f (n + j))) ≤
        ∑ _j ∈ Finset.Icc 1 H,
          ∑ _n ∈ Finset.Ioc X (2 * X), (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro j hj
      apply Finset.sum_le_sum
      intro n hn
      rw [Complex.normSq_eq_norm_sq]
      have hpos : 0 < n + j := by
        have hnpos : 0 < n := by
          have := (Finset.mem_Ioc.mp hn).1
          omega
        omega
      nlinarith [hf (n + j) hpos, norm_nonneg (f (n + j))]
    _ = H * X := by
      simp
      omega

/-- The remaining analytic task after the exact expansion: prove that the total off-diagonal
centered correlation is `o(H²X)`, uniformly over nonpretentious one-bounded multiplicative
functions.  This definition is only a name for the target expression; it introduces no
assumption. -/
def MRNonpretentiousOffDiagonalCorrelationConclusion : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ B : ℕ, 1 ≤ B ∧
      ∀ A H : ℕ, B ≤ A → B ≤ H →
        ∃ X₀ : ℕ, max A H ≤ X₀ ∧
          ∀ X : ℕ, X₀ ≤ X →
            ∀ f : ℕ → ℂ,
              IsMultiplicativeOnPositiveNat f →
              (∀ m : ℕ, 0 < m → ‖f m‖ ≤ 1) →
              MRArchimedeanNonpretentious f A X →
              uncenteredShortIntervalMeanSquare f X H ≤ ε ^ 2 * H ^ 2 * X

/-- The correlation conclusion is definitionally the corrected complex MR mean-square input. -/
theorem mrNonpretentiousOffDiagonalCorrelationConclusion_iff :
    MRNonpretentiousOffDiagonalCorrelationConclusion ↔
      MRComplexNonpretentiousMeanSquareInput := by
  rfl

end

end Erdos67
