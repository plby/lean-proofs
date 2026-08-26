import ErdosProblems.Erdos1002.DiscreteAbel
import ErdosProblems.Erdos1002.PrincipalValueTransform
import ErdosProblems.Erdos1002.GevreyCutoff
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Topology.Order.Compact

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Uniform near-resonant multipliers

This file isolates the analytic and finite-summation assertions used in the
near-resonant square-function argument.  The cutoff is built from one fixed
smooth compactly-supported bump and its dilates.  Thus every constant below
is attached to a fixed profile, while all dependence on the shrinking inner
scale is explicit.
-/

open Filter MeasureTheory Set
open scoped BigOperators ComplexConjugate FourierTransform ENNReal

namespace Erdos1002

noncomputable section

/-! ## Finite vector-valued Abel summation -/

/-- Coordinatewise multiplication on a finite vector of Fourier modes. -/
def coordinateMul {ι : Type*} (x y : ι → ℂ) : ι → ℂ :=
  fun i => x i * y i

/-- Vector partial sum on a closed natural interval. -/
def vectorIntervalPartialSum {ι : Type*}
    (u : ℕ → ι → ℂ) (a b : ℕ) : ι → ℂ :=
  ∑ n ∈ Finset.Icc a b, u n

/-- Exact finite vector-valued Abel summation.  The terminal term and every
variation term are present; equality is coordinatewise and no convergence
claim is used. -/
theorem vectorDiscreteAbel_identity {ι : Type*}
    (u w : ℕ → ι → ℂ) {a b : ℕ} (hab : a ≤ b) :
    (∑ n ∈ Finset.Icc a b, coordinateMul (u n) (w n)) =
      coordinateMul (vectorIntervalPartialSum u a b) (w b) +
        ∑ n ∈ Finset.Ico a b,
          coordinateMul (vectorIntervalPartialSum u a n) (w n - w (n + 1)) := by
  funext i
  simpa only [coordinateMul, vectorIntervalPartialSum, Finset.sum_apply,
    Pi.add_apply, Pi.sub_apply] using!
    discreteAbel_identity (fun n => u n i) (fun n => w n i) hab

/-- The norm estimate following from the exact vector Abel identity.  This
is stated for a finite set of coordinates, so the Pi norm is the required
uniform norm over the dyadic block. -/
theorem norm_vector_sum_coordinateMul_le
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (u w : ℕ → ι → ℂ) {a b : ℕ} (hab : a ≤ b) (M : ℝ)
    (hM : ∀ n ∈ Finset.Icc a b, ‖vectorIntervalPartialSum u a n‖ ≤ M) :
    ‖∑ n ∈ Finset.Icc a b, coordinateMul (u n) (w n)‖ ≤
      M * (‖w b‖ + ∑ n ∈ Finset.Ico a b, ‖w n - w (n + 1)‖) := by
  rw [vectorDiscreteAbel_identity u w hab]
  calc
    ‖coordinateMul (vectorIntervalPartialSum u a b) (w b) +
        ∑ n ∈ Finset.Ico a b,
          coordinateMul (vectorIntervalPartialSum u a n) (w n - w (n + 1))‖ ≤
      ‖coordinateMul (vectorIntervalPartialSum u a b) (w b)‖ +
        ‖∑ n ∈ Finset.Ico a b,
          coordinateMul (vectorIntervalPartialSum u a n) (w n - w (n + 1))‖ :=
      norm_add_le _ _
    _ ≤ ‖vectorIntervalPartialSum u a b‖ * ‖w b‖ +
        ∑ n ∈ Finset.Ico a b,
          ‖vectorIntervalPartialSum u a n‖ * ‖w n - w (n + 1)‖ := by
      gcongr
      · exact norm_mul_le _ _
      · refine (norm_sum_le _ _).trans ?_
        gcongr with n hn
        exact norm_mul_le _ _
    _ ≤ M * ‖w b‖ +
        ∑ n ∈ Finset.Ico a b, M * ‖w n - w (n + 1)‖ := by
      gcongr with n hn
      · exact hM b (Finset.mem_Icc.mpr ⟨hab, le_rfl⟩)
      · exact hM n (Finset.mem_Icc.mpr
          ⟨(Finset.mem_Ico.mp hn).1, (Finset.mem_Ico.mp hn).2.le⟩)
    _ = M * (‖w b‖ + ∑ n ∈ Finset.Ico a b, ‖w n - w (n + 1)‖) := by
      rw [mul_add, Finset.mul_sum]

/-! ## Exact Fourier-side leakage -/

/-- Fourier coefficient modulation by the integer carrier `m`. -/
def modulateCoefficients (m : ℤ) (c : ℤ → ℂ) (n : ℤ) : ℂ :=
  c (n - m)

/-- Coordinate projection onto an integer frequency set. -/
noncomputable def projectCoefficients (A : Set ℤ) (c : ℤ → ℂ) (n : ℤ) : ℂ := by
  classical
  exact if n ∈ A then c n else 0

/-- Squared `L²` energy of a coefficient sequence, valued in `ℝ≥0∞` so
that no summability assumption is hidden. -/
def coefficientEnergy (c : ℤ → ℂ) : ENNReal :=
  ∑' n : ℤ, ENNReal.ofReal (‖c n‖ ^ 2)

/-- Energy leaking out of `A` after modulation by the carrier `m`, written
in the original (unshifted) Fourier coordinate. -/
noncomputable def fourierLeakageEnergy
    (A : Set ℤ) (m : ℤ) (c : ℤ → ℂ) : ENNReal := by
  classical
  exact ∑' k : ℤ, if m + k ∉ A then ENNReal.ofReal (‖c k‖ ^ 2) else 0

/-- Fourier-side energy of the formal `j`-th derivative.  The factor
`2π` is included exactly, so the eventual leakage constant is
`(2πD)^{-j}` rather than an unspecified multiple. -/
def fourierDerivativeEnergy (j : ℕ) (c : ℤ → ℂ) : ENNReal :=
  ∑' k : ℤ, ENNReal.ofReal
    ((2 * Real.pi * |(k : ℝ)|) ^ (2 * j) * ‖c k‖ ^ 2)

/-- Modulation followed by complementary projection has exactly the
leakage energy above.  This is the coefficient-level form of the first
equality in the paper's Fourier leakage display. -/
theorem coefficientEnergy_modulate_sub_projection
    (A : Set ℤ) (m : ℤ) (c : ℤ → ℂ) :
    coefficientEnergy (fun n =>
      modulateCoefficients m c n -
        projectCoefficients A (modulateCoefficients m c) n) =
      fourierLeakageEnergy A m c := by
  classical
  unfold coefficientEnergy fourierLeakageEnergy
  let q : ℤ → ENNReal := fun n =>
    if n ∉ A then ENNReal.ofReal (‖c (n - m)‖ ^ 2) else 0
  calc
    (∑' n : ℤ, ENNReal.ofReal
        (‖modulateCoefficients m c n -
          projectCoefficients A (modulateCoefficients m c) n‖ ^ 2)) =
      ∑' n : ℤ, q n := by
        apply tsum_congr
        intro n
        by_cases hn : n ∈ A
        · simp [q, projectCoefficients, hn]
        · simp [q, projectCoefficients, modulateCoefficients, hn]
    _ = ∑' k : ℤ,
        if m + k ∉ A then ENNReal.ofReal (‖c k‖ ^ 2) else 0 := by
      rw [← (Equiv.addLeft m).tsum_eq q]
      apply tsum_congr
      intro k
      simp [q]

/-- Exact squared leakage inequality.  The separation assumption is
stated only for frequencies that actually leak.  No constants depend on
`j`: every occurrence is displayed in `(2πD)^(2j)`. -/
theorem fourierLeakageEnergy_scaled_le
    (A : Set ℤ) (m : ℤ) (c : ℤ → ℂ) (D : ℝ) (j : ℕ)
    (hD : 0 ≤ D)
    (hsep : ∀ k : ℤ, m + k ∉ A → D ≤ |(k : ℝ)|) :
    ENNReal.ofReal ((2 * Real.pi * D) ^ (2 * j)) *
        fourierLeakageEnergy A m c ≤
      fourierDerivativeEnergy j c := by
  classical
  unfold fourierLeakageEnergy fourierDerivativeEnergy
  rw [← ENNReal.tsum_mul_left]
  apply ENNReal.tsum_le_tsum
  intro k
  by_cases hk : m + k ∉ A
  · simp only [hk, not_false_eq_true, if_true]
    rw [← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have hbase : 2 * Real.pi * D ≤ 2 * Real.pi * |(k : ℝ)| := by
      exact mul_le_mul_of_nonneg_left (hsep k hk)
        (mul_nonneg (by norm_num) Real.pi_nonneg)
    have hpow :
        (2 * Real.pi * D) ^ (2 * j) ≤
          (2 * Real.pi * |(k : ℝ)|) ^ (2 * j) :=
      pow_le_pow_left₀ (by positivity) hbase (2 * j)
    exact mul_le_mul_of_nonneg_right hpow (sq_nonneg _)
  · simp [hk]

/-- Division form of the leakage estimate.  This is precisely the
squared version of the paper's `(2πD)^{-j}‖f^{(j)}‖₂` bound. -/
theorem fourierLeakageEnergy_le_inv_mul
    (A : Set ℤ) (m : ℤ) (c : ℤ → ℂ) (D : ℝ) (j : ℕ)
    (hD : 0 < D)
    (hsep : ∀ k : ℤ, m + k ∉ A → D ≤ |(k : ℝ)|) :
    fourierLeakageEnergy A m c ≤
      (ENNReal.ofReal ((2 * Real.pi * D) ^ (2 * j)))⁻¹ *
        fourierDerivativeEnergy j c := by
  apply (ENNReal.mul_le_iff_le_inv ?_ ENNReal.ofReal_ne_top).mp
  · exact fourierLeakageEnergy_scaled_le A m c D j hD.le hsep
  · intro hzero
    have hle := ENNReal.ofReal_eq_zero.mp hzero
    exact (not_le_of_gt
      (pow_pos (mul_pos (mul_pos (by norm_num) Real.pi_pos) hD) _)) hle

/-- Extended nonnegative `L²` size associated with coefficient energy. -/
def coefficientENNL2Norm (c : ℤ → ℂ) : ENNReal :=
  coefficientEnergy c ^ (1 / 2 : ℝ)

def fourierLeakageENNL2Norm
    (A : Set ℤ) (m : ℤ) (c : ℤ → ℂ) : ENNReal :=
  fourierLeakageEnergy A m c ^ (1 / 2 : ℝ)

def fourierDerivativeENNL2Norm (j : ℕ) (c : ℤ → ℂ) : ENNReal :=
  fourierDerivativeEnergy j c ^ (1 / 2 : ℝ)

private theorem ennreal_pow_two_mul_rpow_half (b : ENNReal) (j : ℕ) :
    (b ^ (2 * j)) ^ (1 / 2 : ℝ) = b ^ j := by
  calc
    (b ^ (2 * j)) ^ (1 / 2 : ℝ) =
        (b ^ ((2 * j : ℕ) : ℝ)) ^ (1 / 2 : ℝ) := by
      rw [ENNReal.rpow_natCast]
    _ = b ^ (((2 * j : ℕ) : ℝ) * (1 / 2 : ℝ)) := by
      rw [ENNReal.rpow_mul]
    _ = b ^ (j : ℝ) := by
      congr 1
      push_cast
      ring
    _ = b ^ j := ENNReal.rpow_natCast b j

/-- Norm form of the exact leakage inequality:
`(2πD)^j · leakage ≤ derivative`.  It is equivalent to the paper's
display after division, and makes the entire `j` dependence explicit. -/
theorem fourierLeakageENNL2Norm_scaled_le
    (A : Set ℤ) (m : ℤ) (c : ℤ → ℂ) (D : ℝ) (j : ℕ)
    (hD : 0 ≤ D)
    (hsep : ∀ k : ℤ, m + k ∉ A → D ≤ |(k : ℝ)|) :
    (ENNReal.ofReal (2 * Real.pi * D)) ^ j *
        fourierLeakageENNL2Norm A m c ≤
      fourierDerivativeENNL2Norm j c := by
  have hsquared := fourierLeakageEnergy_scaled_le A m c D j hD hsep
  have hsqrt := ENNReal.rpow_le_rpow hsquared (by norm_num : (0 : ℝ) ≤ 1 / 2)
  unfold fourierLeakageENNL2Norm fourierDerivativeENNL2Norm
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2)] at hsqrt
  have hbase : 0 ≤ 2 * Real.pi * D := by positivity
  rw [ENNReal.ofReal_pow hbase, ennreal_pow_two_mul_rpow_half] at hsqrt
  exact hsqrt

theorem fourierLeakageENNL2Norm_le_inv_mul
    (A : Set ℤ) (m : ℤ) (c : ℤ → ℂ) (D : ℝ) (j : ℕ)
    (hD : 0 < D)
    (hsep : ∀ k : ℤ, m + k ∉ A → D ≤ |(k : ℝ)|) :
    fourierLeakageENNL2Norm A m c ≤
      ((ENNReal.ofReal (2 * Real.pi * D)) ^ j)⁻¹ *
        fourierDerivativeENNL2Norm j c := by
  apply (ENNReal.mul_le_iff_le_inv ?_ ?_).mp
  · exact fourierLeakageENNL2Norm_scaled_le A m c D j hD.le hsep
  · intro hzero
    have hbasezero : ENNReal.ofReal (2 * Real.pi * D) = 0 :=
      eq_zero_of_pow_eq_zero hzero
    have hle := ENNReal.ofReal_eq_zero.mp hbasezero
    exact (not_le_of_gt (mul_pos (mul_pos (by norm_num) Real.pi_pos) hD)) hle
  · exact ENNReal.pow_ne_top ENNReal.ofReal_ne_top

/-! ## Bounded-overlap square summation -/

/-- Number of active carrier sets at one integer frequency. -/
noncomputable def frequencyOverlapCount
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (A : ι → Set ℤ) (n : ℤ) : ℕ := by
  classical
  exact (s.filter fun i => n ∈ A i).card

/-- Pointwise Cauchy--Schwarz for projected coefficient families.  The
only combinatorial input is the explicit overlap-cardinality bound. -/
theorem norm_sq_sum_projected_le_overlap
    {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (A : ι → Set ℤ) (c : ι → ℤ → ℂ) (B : ℕ)
    (hoverlap : ∀ n : ℤ, frequencyOverlapCount s A n ≤ B)
    (n : ℤ) :
    ‖∑ i ∈ s, projectCoefficients (A i) (c i) n‖ ^ 2 ≤
      B * ∑ i ∈ s, ‖c i n‖ ^ 2 := by
  classical
  let u := s.filter fun i => n ∈ A i
  have hsum :
      (∑ i ∈ s, projectCoefficients (A i) (c i) n) =
        ∑ i ∈ u, c i n := by
    simpa [u, projectCoefficients] using!
      (Finset.sum_filter (s := s) (fun i => n ∈ A i)
        (fun i => c i n)).symm
  rw [hsum]
  have hnorm : ‖∑ i ∈ u, c i n‖ ≤ ∑ i ∈ u, ‖c i n‖ :=
    norm_sum_le _ _
  calc
    ‖∑ i ∈ u, c i n‖ ^ 2 ≤ (∑ i ∈ u, ‖c i n‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hnorm 2
    _ ≤ u.card * ∑ i ∈ u, ‖c i n‖ ^ 2 :=
      sq_sum_le_card_mul_sum_sq
    _ ≤ B * ∑ i ∈ s, ‖c i n‖ ^ 2 := by
      have hcard : (u.card : ℝ) ≤ B := by
        have hc : u.card ≤ B := by
          simpa [u, frequencyOverlapCount] using! hoverlap n
        exact_mod_cast hc
      have hsumsub : (∑ i ∈ u, ‖c i n‖ ^ 2) ≤
          ∑ i ∈ s, ‖c i n‖ ^ 2 := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        intro i _hi _his
        positivity
      exact mul_le_mul hcard hsumsub (by positivity) (by positivity)

private theorem ennreal_tsum_finset_sum
    {ι : Type*} (s : Finset ι) (f : ι → ℤ → ENNReal) :
    (∑' n : ℤ, ∑ i ∈ s, f i n) =
      ∑ i ∈ s, ∑' n : ℤ, f i n := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      simp only [Finset.sum_insert hi]
      rw [ENNReal.tsum_add, ih]

/-- Frequency-by-frequency bounded overlap, summed exactly over all
integer frequencies.  This is the coefficient-level Plancherel estimate
`‖∑ Π_s F_s‖₂² ≤ B ∑ ‖F_s‖₂²`. -/
theorem coefficientEnergy_sum_projected_le_overlap
    {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (A : ι → Set ℤ) (c : ι → ℤ → ℂ) (B : ℕ)
    (hoverlap : ∀ n : ℤ, frequencyOverlapCount s A n ≤ B) :
    coefficientEnergy (fun n =>
      ∑ i ∈ s, projectCoefficients (A i) (c i) n) ≤
      B * ∑ i ∈ s, coefficientEnergy (c i) := by
  classical
  unfold coefficientEnergy
  calc
    (∑' n : ℤ, ENNReal.ofReal
        (‖∑ i ∈ s, projectCoefficients (A i) (c i) n‖ ^ 2)) ≤
      ∑' n : ℤ, (B : ENNReal) *
        ∑ i ∈ s, ENNReal.ofReal (‖c i n‖ ^ 2) := by
      apply ENNReal.tsum_le_tsum
      intro n
      have hpoint := norm_sq_sum_projected_le_overlap
        s A c B hoverlap n
      have h := ENNReal.ofReal_le_ofReal hpoint
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast,
        ENNReal.ofReal_sum_of_nonneg (fun _ _ => sq_nonneg _)] at h
      exact h
    _ = (B : ENNReal) *
        (∑' n : ℤ, ∑ i ∈ s, ENNReal.ofReal (‖c i n‖ ^ 2)) := by
      rw [ENNReal.tsum_mul_left]
    _ = (B : ENNReal) *
        ∑ i ∈ s, ∑' n : ℤ, ENNReal.ofReal (‖c i n‖ ^ 2) := by
      rw [ennreal_tsum_finset_sum]

/-! ## A fixed smooth profile and its dilates -/

/-- A legacy `ContDiffBump` with the same support geometry.  The actual
profile below is the explicit Gevrey bump, because derivatives whose order
grows with `N` require quantitative bounds unavailable from an abstract
`ContDiffBump`. -/
def nearBaseBump : ContDiffBump (0 : ℝ) :=
  ⟨1, 2, by norm_num, by norm_num⟩

/-- Complex-valued explicit Gevrey profile.  It equals one on `[-1,1]`,
vanishes outside `[-2,2]`, and has the derivative bounds proved in
`GevreyCutoff`. -/
def nearBaseProfile (x : ℝ) : ℂ :=
  (gevreyOuterCutoff 2 x : ℂ)

/-- Dilation by a positive length scale. -/
def scaledNearProfile (s : ℝ) (x : ℝ) : ℂ :=
  nearBaseProfile (x / s)

/-- Outer cutoff minus the shrinking inner cutoff.  The outer bump has
inner/outer radii `ε/2,ε`; the inner bump has radii `a,2a`. -/
def nearRho (a ε : ℝ) (x : ℝ) : ℂ :=
  scaledNearProfile (ε / 2) x - scaledNearProfile a x

/-- Fourier transform of the cutoff. -/
def nearRhoFourier (a ε : ℝ) (t : ℝ) : ℂ :=
  FourierTransform.fourier (nearRho a ε) t

theorem nearBaseProfile_contDiff :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) nearBaseProfile := by
  simpa only [nearBaseProfile] using!
    Complex.ofRealCLM.contDiff.comp
      (gevreyOuterCutoff_contDiff (m := (⊤ : ℕ∞)) 2)

theorem nearBaseProfile_hasCompactSupport : HasCompactSupport nearBaseProfile := by
  refine HasCompactSupport.of_support_subset_isCompact
    (K := Icc (-(2 : ℝ)) 2) isCompact_Icc ?_
  intro x hx
  apply support_gevreyOuterCutoff_subset (by norm_num : (0 : ℝ) < 2)
  intro hzero
  apply hx
  simp [nearBaseProfile, hzero]

theorem nearBaseProfile_integrable : Integrable nearBaseProfile :=
  nearBaseProfile_contDiff.continuous.integrable_of_hasCompactSupport
    nearBaseProfile_hasCompactSupport

theorem scaledNearProfile_integrable (s : ℝ) (hs : s ≠ 0) :
    Integrable (scaledNearProfile s) := by
  exact nearBaseProfile_integrable.comp_div hs

private theorem nearBaseProfile_iteratedDeriv_hasCompactSupport (m : ℕ) :
    HasCompactSupport ((deriv^[m]) nearBaseProfile) := by
  induction m with
  | zero => simpa using! nearBaseProfile_hasCompactSupport
  | succ m ih =>
      rw [Function.iterate_succ_apply']
      exact ih.deriv

theorem nearBaseProfile_iteratedDeriv_integrable (m : ℕ) :
    Integrable (iteratedDeriv m nearBaseProfile) volume := by
  rw [iteratedDeriv_eq_iterate]
  exact Continuous.integrable_of_hasCompactSupport (μ := volume)
    (nearBaseProfile_contDiff.iterate_deriv m).continuous
    (nearBaseProfile_iteratedDeriv_hasCompactSupport m)

/-- The elementary `L¹` Fourier bound, recorded with the exact profile
constant. -/
theorem norm_fourier_le_integral_norm
    (f : ℝ → ℂ) (t : ℝ) :
    ‖FourierTransform.fourier f t‖ ≤ ∫ x : ℝ, ‖f x‖ := by
  exact VectorFourier.norm_fourierIntegral_le_integral_norm
    Real.fourierChar volume (innerₗ ℝ) f t

private theorem fourier_sub_of_integrable
    (f g : ℝ → ℂ) (hf : Integrable f) (hg : Integrable g) (t : ℝ) :
    FourierTransform.fourier (fun x => f x - g x) t =
      FourierTransform.fourier f t - FourierTransform.fourier g t := by
  simp only [Real.fourier_eq]
  have hfi := (Real.fourierIntegral_convergent_iff t).2 hf
  have hgi := (Real.fourierIntegral_convergent_iff t).2 hg
  rw [← integral_sub hfi hgi]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with x
  exact smul_sub (Real.fourierChar (-inner ℝ x t)) (f x) (g x)

/-- Exact Fourier scaling for a positive dilation. -/
theorem fourier_scaledNearProfile (s t : ℝ) (hs : 0 < s) :
    FourierTransform.fourier (scaledNearProfile s) t =
      (s : ℂ) * FourierTransform.fourier nearBaseProfile (s * t) := by
  rw [Real.fourier_eq, Real.fourier_eq]
  let g : ℝ → ℂ := fun y =>
    (Real.fourierChar (-(y * (s * t))) : ℂ) * nearBaseProfile y
  have hchange := Measure.integral_comp_div g s
  rw [abs_of_pos hs, Complex.real_smul] at hchange
  calc
    (∫ v : ℝ, Real.fourierChar (-inner ℝ v t) • scaledNearProfile s v) =
        ∫ x : ℝ, g (x / s) := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards with x
      dsimp [g, scaledNearProfile]
      simp only [Circle.smul_def, smul_eq_mul, conj_trivial]
      have harg : -(t * x) = -((x / s) * (s * t)) := by
        field_simp [ne_of_gt hs]
      rw [harg]
    _ = (s : ℂ) * ∫ y : ℝ, g y := hchange
    _ = (s : ℂ) *
        ∫ v : ℝ, Real.fourierChar (-inner ℝ v (s * t)) • nearBaseProfile v := by
      congr 1
      apply MeasureTheory.integral_congr_ae
      filter_upwards with y
      dsimp [g]
      simp only [Circle.smul_def, smul_eq_mul, conj_trivial]
      have harg : -(y * (s * t)) = -((s * t) * y) := by ring
      rw [harg]

/-- The transform of `rho` is the difference of two fixed-profile
transforms at the two scales. -/
theorem nearRhoFourier_eq_scaled (a ε t : ℝ) (ha : 0 < a) (hε : 0 < ε) :
    nearRhoFourier a ε t =
      ((ε / 2 : ℝ) : ℂ) *
          FourierTransform.fourier nearBaseProfile ((ε / 2) * t) -
        (a : ℂ) * FourierTransform.fourier nearBaseProfile (a * t) := by
  unfold nearRhoFourier nearRho
  rw [fourier_sub_of_integrable
    (scaledNearProfile (ε / 2)) (scaledNearProfile a)
    (scaledNearProfile_integrable (ε / 2) (by positivity))
    (scaledNearProfile_integrable a (ne_of_gt ha))]
  rw [fourier_scaledNearProfile (ε / 2) t (by positivity),
    fourier_scaledNearProfile a t ha]

/-! ## A uniform integrable Fourier envelope -/

/-- The two fixed profile constants needed for quadratic Fourier decay. -/
def nearProfileL1 : ℝ :=
  ∫ x : ℝ, ‖nearBaseProfile x‖

def nearProfileD2L1 : ℝ :=
  ∫ x : ℝ, ‖iteratedDeriv 2 nearBaseProfile x‖

theorem nearProfileL1_nonneg : 0 ≤ nearProfileL1 := by
  unfold nearProfileL1
  exact integral_nonneg fun _ => norm_nonneg _

theorem nearProfileD2L1_nonneg : 0 ≤ nearProfileD2L1 := by
  unfold nearProfileD2L1
  exact integral_nonneg fun _ => norm_nonneg _

/-- Twice integrating the fixed profile by parts, expressed through the
library's exact Fourier-transform/iterated-derivative identity. -/
theorem nearBaseProfile_fourier_quadratic (t : ℝ) :
    (2 * Real.pi * |t|) ^ 2 *
        ‖FourierTransform.fourier nearBaseProfile t‖ ≤ nearProfileD2L1 := by
  have hfour := Real.fourier_iteratedDeriv
    (f := nearBaseProfile) (N := (⊤ : ℕ∞)) (n := 2)
    nearBaseProfile_contDiff
    (fun n _hn => nearBaseProfile_iteratedDeriv_integrable n)
    (by simp)
  have heq := congrFun hfour t
  have hnorm := norm_fourier_le_integral_norm
    (iteratedDeriv 2 nearBaseProfile) t
  rw [heq] at hnorm
  unfold nearProfileD2L1
  convert! hnorm using 1
  rw [norm_smul]
  simp only [norm_pow, norm_mul, Complex.norm_real, Complex.norm_I,
    mul_one, Real.norm_eq_abs, abs_of_nonneg Real.pi_nonneg]
  norm_num

/-- A single nonnegative constant dominating both the low-frequency and
twice-integrated-by-parts bounds of the fixed profile. -/
def nearProfileDecayConstant : ℝ :=
  max nearProfileL1 (nearProfileD2L1 / (2 * Real.pi) ^ 2)

theorem nearProfileDecayConstant_nonneg : 0 ≤ nearProfileDecayConstant := by
  exact nearProfileL1_nonneg.trans (le_max_left _ _)

theorem nearProfileL1_le_decayConstant :
    nearProfileL1 ≤ nearProfileDecayConstant :=
  le_max_left _ _

theorem nearProfileD2L1_div_le_decayConstant :
    nearProfileD2L1 / (2 * Real.pi) ^ 2 ≤ nearProfileDecayConstant :=
  le_max_right _ _

theorem nearBaseProfile_fourier_low (t : ℝ) :
    ‖FourierTransform.fourier nearBaseProfile t‖ ≤ nearProfileDecayConstant := by
  exact (norm_fourier_le_integral_norm nearBaseProfile t).trans
    nearProfileL1_le_decayConstant

theorem nearBaseProfile_fourier_high (t : ℝ) (ht : 1 ≤ |t|) :
    ‖FourierTransform.fourier nearBaseProfile t‖ ≤
      nearProfileDecayConstant / |t| ^ 2 := by
  have htpos : 0 < |t| := lt_of_lt_of_le zero_lt_one ht
  have hpipos : 0 < 2 * Real.pi := mul_pos (by norm_num) Real.pi_pos
  have hden : 0 < (2 * Real.pi * |t|) ^ 2 := sq_pos_of_pos (mul_pos hpipos htpos)
  have hfirst : ‖FourierTransform.fourier nearBaseProfile t‖ ≤
      nearProfileD2L1 / (2 * Real.pi * |t|) ^ 2 := by
    exact (le_div_iff₀ hden).2 (by
      simpa only [mul_comm] using! nearBaseProfile_fourier_quadratic t)
  calc
    ‖FourierTransform.fourier nearBaseProfile t‖ ≤
        nearProfileD2L1 / (2 * Real.pi * |t|) ^ 2 := hfirst
    _ = (nearProfileD2L1 / (2 * Real.pi) ^ 2) / |t| ^ 2 := by
      field_simp [ne_of_gt hpipos, ne_of_gt htpos]
    _ ≤ nearProfileDecayConstant / |t| ^ 2 := by
      exact div_le_div_of_nonneg_right nearProfileD2L1_div_le_decayConstant
        (sq_nonneg _)

/-- Fixed-profile decay in the convenient integrable `(1+|t|)^{-2}`
form.  The constant is completely independent of either cutoff scale. -/
theorem nearBaseProfile_fourier_envelope (t : ℝ) :
    ‖FourierTransform.fourier nearBaseProfile t‖ ≤
      4 * nearProfileDecayConstant / (1 + |t|) ^ 2 := by
  by_cases ht : |t| ≤ 1
  · refine (nearBaseProfile_fourier_low t).trans ?_
    have hden : 0 < (1 + |t|) ^ 2 := sq_pos_of_pos (by positivity)
    rw [le_div_iff₀ hden]
    have hsquare : (1 + |t|) ^ 2 ≤ 4 := by
      nlinarith [abs_nonneg t]
    simpa only [mul_comm] using!
      mul_le_mul_of_nonneg_left hsquare nearProfileDecayConstant_nonneg
  · have ht' : 1 ≤ |t| := le_of_lt (lt_of_not_ge ht)
    refine (nearBaseProfile_fourier_high t ht').trans ?_
    have htpos : 0 < |t| := lt_of_lt_of_le zero_lt_one ht'
    have hden₁ : 0 < |t| ^ 2 := sq_pos_of_pos htpos
    have hden₂ : 0 < (1 + |t|) ^ 2 := sq_pos_of_pos (by positivity)
    rw [div_le_div_iff₀ hden₁ hden₂]
    have hsquare : (1 + |t|) ^ 2 ≤ 4 * |t| ^ 2 := by
      nlinarith [abs_nonneg t]
    simpa only [mul_assoc, mul_comm, mul_left_comm] using!
      mul_le_mul_of_nonneg_left hsquare nearProfileDecayConstant_nonneg

/-- The explicit two-scale envelope corresponding to
`ε(1+ε|t|)^{-2}+a(1+a|t|)^{-2}`.  The harmless factor `1/2` in
the outer scale is forced by the chosen plateau radii. -/
def nearRhoEnvelope (a ε t : ℝ) : ℝ :=
  4 * nearProfileDecayConstant *
    ((ε / 2) / (1 + (ε / 2) * |t|) ^ 2 +
      a / (1 + a * |t|) ^ 2)

theorem nearRhoEnvelope_nonneg
    (a ε t : ℝ) (ha : 0 ≤ a) (hε : 0 ≤ ε) :
    0 ≤ nearRhoEnvelope a ε t := by
  unfold nearRhoEnvelope
  exact mul_nonneg
    (mul_nonneg (by norm_num) nearProfileDecayConstant_nonneg)
    (add_nonneg
      (div_nonneg (by positivity) (sq_nonneg _))
      (div_nonneg ha (sq_nonneg _)))

/-- Uniform Fourier envelope for the shrinking cutoff, with every scale
visible and no constant depending on `a`. -/
theorem norm_nearRhoFourier_le_envelope
    (a ε t : ℝ) (ha : 0 < a) (hε : 0 < ε) :
    ‖nearRhoFourier a ε t‖ ≤ nearRhoEnvelope a ε t := by
  rw [nearRhoFourier_eq_scaled a ε t ha hε]
  have hs : 0 < ε / 2 := by positivity
  have hout :
      ‖FourierTransform.fourier nearBaseProfile ((ε / 2) * t)‖ ≤
        4 * nearProfileDecayConstant /
          (1 + (ε / 2) * |t|) ^ 2 := by
    simpa only [abs_mul, abs_of_pos hs] using!
      nearBaseProfile_fourier_envelope ((ε / 2) * t)
  have hin :
      ‖FourierTransform.fourier nearBaseProfile (a * t)‖ ≤
        4 * nearProfileDecayConstant / (1 + a * |t|) ^ 2 := by
    simpa only [abs_mul, abs_of_pos ha] using!
      nearBaseProfile_fourier_envelope (a * t)
  calc
    ‖((ε / 2 : ℝ) : ℂ) *
          FourierTransform.fourier nearBaseProfile ((ε / 2) * t) -
        (a : ℂ) * FourierTransform.fourier nearBaseProfile (a * t)‖ ≤
      ‖((ε / 2 : ℝ) : ℂ) *
          FourierTransform.fourier nearBaseProfile ((ε / 2) * t)‖ +
        ‖(a : ℂ) * FourierTransform.fourier nearBaseProfile (a * t)‖ :=
      norm_sub_le _ _
    _ = (ε / 2) *
          ‖FourierTransform.fourier nearBaseProfile ((ε / 2) * t)‖ +
        a * ‖FourierTransform.fourier nearBaseProfile (a * t)‖ := by
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hs, abs_of_pos ha]
    _ ≤ (ε / 2) *
          (4 * nearProfileDecayConstant /
            (1 + (ε / 2) * |t|) ^ 2) +
        a * (4 * nearProfileDecayConstant / (1 + a * |t|) ^ 2) := by
      gcongr
    _ = nearRhoEnvelope a ε t := by
      unfold nearRhoEnvelope
      ring

/-- Each positive-scale summand of the envelope. -/
def scaleDecayEnvelope (s t : ℝ) : ℝ :=
  s / (1 + s * t) ^ 2

theorem scaleDecayEnvelope_mul_le
    (s t r : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) (hr : 1 ≤ r) :
    scaleDecayEnvelope s (r * t) ≤ scaleDecayEnvelope s t := by
  unfold scaleDecayEnvelope
  have hrt : t ≤ r * t := by
    simpa only [one_mul] using! mul_le_mul_of_nonneg_right hr ht
  have hlin : 1 + s * t ≤ 1 + s * (r * t) := by
    gcongr
  have hsmall : 0 < (1 + s * t) ^ 2 := sq_pos_of_pos (by positivity)
  apply div_le_div_of_nonneg_left hs hsmall
  exact pow_le_pow_left₀ (by positivity) hlin 2

/-- On the positive half-line, enlarging the frequency by a factor
`1 ≤ r` can only decrease the explicit envelope. -/
theorem nearRhoEnvelope_mul_le
    (a ε t r : ℝ) (ha : 0 ≤ a) (hε : 0 ≤ ε)
    (ht : 0 ≤ t) (hr : 1 ≤ r) :
    nearRhoEnvelope a ε (r * t) ≤ nearRhoEnvelope a ε t := by
  have hr0 : 0 ≤ r := zero_le_one.trans hr
  rw [nearRhoEnvelope, nearRhoEnvelope]
  rw [abs_of_nonneg (mul_nonneg hr0 ht), abs_of_nonneg ht]
  apply mul_le_mul_of_nonneg_left _
    (mul_nonneg (by norm_num) nearProfileDecayConstant_nonneg)
  exact add_le_add
    (scaleDecayEnvelope_mul_le (ε / 2) t r (by positivity) ht hr)
    (scaleDecayEnvelope_mul_le a t r ha ht hr)

/-- Primitive used to evaluate the envelope integral exactly. -/
def scaleDecayPrimitive (s t : ℝ) : ℝ :=
  -(1 / (1 + s * t))

theorem hasDerivAt_scaleDecayPrimitive
    (s t : ℝ) (hs : 0 < s) (ht : 0 ≤ t) :
    HasDerivAt (scaleDecayPrimitive s) (scaleDecayEnvelope s t) t := by
  have hlin : HasDerivAt (fun x : ℝ => 1 + s * x) s t := by
    convert! (hasDerivAt_const t 1).add ((hasDerivAt_id t).const_mul s) using 1
    ring
  have hpos : 0 < 1 + s * t := by positivity
  have hinv := hlin.inv (ne_of_gt hpos)
  have hneg := hinv.neg
  unfold scaleDecayPrimitive scaleDecayEnvelope
  simpa only [one_div, neg_div, neg_neg] using! hneg

theorem scaleDecayPrimitive_tendsto_atTop_zero
    (s : ℝ) (hs : 0 < s) :
    Tendsto (scaleDecayPrimitive s) atTop (nhds 0) := by
  have hlin : Tendsto (fun t : ℝ => 1 + s * t) atTop atTop :=
    tendsto_atTop_add_const_left atTop 1
      ((tendsto_const_mul_atTop_of_pos hs).2 tendsto_id)
  have hinv : Tendsto (fun t : ℝ => (1 + s * t)⁻¹) atTop (nhds 0) :=
    (tendsto_inv_atTop_zero : Tendsto (fun x : ℝ => x⁻¹) atTop (nhds 0)).comp hlin
  unfold scaleDecayPrimitive
  simp only [one_div]
  simpa only [neg_zero] using! hinv.neg

/-- The scale-normalized quadratic envelope is integrable on `(0,∞)`. -/
theorem scaleDecayEnvelope_integrableOn_Ioi (s : ℝ) (hs : 0 < s) :
    IntegrableOn (scaleDecayEnvelope s) (Ioi 0) := by
  apply integrableOn_Ioi_deriv_of_nonneg
    ((hasDerivAt_scaleDecayPrimitive s 0 hs le_rfl).continuousAt.continuousWithinAt)
    (fun x hx => hasDerivAt_scaleDecayPrimitive s x hs hx.le)
  · intro x hx
    unfold scaleDecayEnvelope
    positivity
  · exact scaleDecayPrimitive_tendsto_atTop_zero s hs

/-- Exact scale-independent mass of one envelope summand. -/
theorem integral_scaleDecayEnvelope_Ioi (s : ℝ) (hs : 0 < s) :
    ∫ t in Ioi (0 : ℝ), scaleDecayEnvelope s t = 1 := by
  have h := integral_Ioi_of_hasDerivAt_of_tendsto'
    (fun x hx => hasDerivAt_scaleDecayPrimitive s x hs hx)
    (scaleDecayEnvelope_integrableOn_Ioi s hs)
    (scaleDecayPrimitive_tendsto_atTop_zero s hs)
  simpa [scaleDecayPrimitive] using! h

theorem nearRhoEnvelope_eq_scaleDecay_of_nonneg
    (a ε t : ℝ) (ht : 0 ≤ t) :
    nearRhoEnvelope a ε t =
      4 * nearProfileDecayConstant *
        (scaleDecayEnvelope (ε / 2) t + scaleDecayEnvelope a t) := by
  unfold nearRhoEnvelope scaleDecayEnvelope
  rw [abs_of_nonneg ht]

/-- The two-scale envelope is integrable with a mass independent of `a`
and `ε`. -/
theorem nearRhoEnvelope_integrableOn_Ioi
    (a ε : ℝ) (ha : 0 < a) (hε : 0 < ε) :
    IntegrableOn (nearRhoEnvelope a ε) (Ioi 0) := by
  have hout := scaleDecayEnvelope_integrableOn_Ioi (ε / 2) (by positivity)
  have hin := scaleDecayEnvelope_integrableOn_Ioi a ha
  have hsum : Integrable
      (fun t => scaleDecayEnvelope (ε / 2) t + scaleDecayEnvelope a t)
      (volume.restrict (Ioi 0)) := hout.add hin
  have hmul := hsum.const_mul (4 * nearProfileDecayConstant)
  apply hmul.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact (nearRhoEnvelope_eq_scaleDecay_of_nonneg a ε t ht.le).symm

/-- Exact uniform mass of the explicit dyadic envelope. -/
theorem integral_nearRhoEnvelope_Ioi
    (a ε : ℝ) (ha : 0 < a) (hε : 0 < ε) :
    ∫ t in Ioi (0 : ℝ), nearRhoEnvelope a ε t =
      8 * nearProfileDecayConstant := by
  have hout := scaleDecayEnvelope_integrableOn_Ioi (ε / 2) (by positivity)
  have hin := scaleDecayEnvelope_integrableOn_Ioi a ha
  have heq : nearRhoEnvelope a ε =ᵐ[volume.restrict (Ioi 0)]
      fun t => 4 * nearProfileDecayConstant *
        (scaleDecayEnvelope (ε / 2) t + scaleDecayEnvelope a t) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact nearRhoEnvelope_eq_scaleDecay_of_nonneg a ε t ht.le
  rw [integral_congr_ae heq, integral_const_mul]
  rw [integral_add hout hin]
  rw [integral_scaleDecayEnvelope_Ioi (ε / 2) (by positivity),
    integral_scaleDecayEnvelope_Ioi a ha]
  ring

/-! ## The quotient multiplier and the derivative of `J_a` -/

theorem scaledNearProfile_eq_one
    (s x : ℝ) (hs : 0 < s) (hx : |x| ≤ s) :
    scaledNearProfile s x = 1 := by
  unfold scaledNearProfile nearBaseProfile
  have hscaled : |x / s| ≤ (2 : ℝ) / 2 := by
    rw [abs_div, abs_of_pos hs]
    norm_num
    exact (div_le_one hs).2 hx
  rw [gevreyOuterCutoff_eq_one_of_abs_le_half
    (by norm_num : (0 : ℝ) < 2) hscaled]
  norm_num

theorem nearBaseProfile_neg (x : ℝ) :
    nearBaseProfile (-x) = nearBaseProfile x := by
  unfold nearBaseProfile
  rw [gevreyOuterCutoff_even]

theorem scaledNearProfile_neg (s x : ℝ) :
    scaledNearProfile s (-x) = scaledNearProfile s x := by
  unfold scaledNearProfile
  have harg : (-x) / s = -(x / s) := by ring
  rw [harg, nearBaseProfile_neg]

theorem nearRho_neg (a ε x : ℝ) :
    nearRho a ε (-x) = nearRho a ε x := by
  unfold nearRho
  rw [scaledNearProfile_neg, scaledNearProfile_neg]

/-- The two profiles cancel throughout the deleted inner interval. -/
theorem nearRho_eq_zero_of_abs_le
    (a ε x : ℝ) (ha : 0 < a) (haε : a ≤ ε / 4) (hx : |x| ≤ a) :
    nearRho a ε x = 0 := by
  have hε : 0 < ε := by linarith
  have hout : |x| ≤ ε / 2 := by linarith
  rw [nearRho, scaledNearProfile_eq_one a x ha hx,
    scaledNearProfile_eq_one (ε / 2) x (by positivity) hout]
  ring

theorem nearRho_integrable
    (a ε : ℝ) (ha : 0 < a) (hε : 0 < ε) :
    Integrable (nearRho a ε) := by
  exact (scaledNearProfile_integrable (ε / 2) (by positivity)).sub
    (scaledNearProfile_integrable a (ne_of_gt ha))

/-- The paper's quotient cutoff `W_a=ρ/v`, totalized at the origin.  Since
complex division is already totalized, no separate arbitrary value is
needed. -/
def nearW (a ε : ℝ) (x : ℝ) : ℂ :=
  nearRho a ε x / (x : ℂ)

theorem nearW_neg (a ε x : ℝ) :
    nearW a ε (-x) = -nearW a ε x := by
  unfold nearW
  rw [nearRho_neg]
  push_cast
  rw [div_neg]

theorem nearW_aestronglyMeasurable
    (a ε : ℝ) (ha : 0 < a) (hε : 0 < ε) :
    AEStronglyMeasurable (nearW a ε) := by
  unfold nearW
  have hinv : AEStronglyMeasurable (fun x : ℝ => ((x : ℂ)⁻¹)) :=
    ((Complex.continuous_ofReal.comp continuous_id).measurable.inv).aestronglyMeasurable
  simpa only [div_eq_mul_inv] using!
    (nearRho_integrable a ε ha hε).aestronglyMeasurable.mul hinv

theorem norm_nearW_le
    (a ε x : ℝ) (ha : 0 < a) (haε : a ≤ ε / 4) :
    ‖nearW a ε x‖ ≤ a⁻¹ * ‖nearRho a ε x‖ := by
  by_cases hx : |x| ≤ a
  · unfold nearW
    rw [nearRho_eq_zero_of_abs_le a ε x ha haε hx]
    simp
  · have hax : a ≤ |x| := (lt_of_not_ge hx).le
    rw [nearW, norm_div, Complex.norm_real, Real.norm_eq_abs]
    calc
      ‖nearRho a ε x‖ / |x| ≤ ‖nearRho a ε x‖ / a :=
        div_le_div_of_nonneg_left (norm_nonneg _) ha hax
      _ = a⁻¹ * ‖nearRho a ε x‖ := by
        rw [inv_mul_eq_div, div_eq_mul_inv, mul_comm]

theorem nearW_integrable
    (a ε : ℝ) (ha : 0 < a) (hε : 0 < ε) (haε : a ≤ ε / 4) :
    Integrable (nearW a ε) := by
  have hdom : Integrable (fun x => a⁻¹ * ‖nearRho a ε x‖) :=
    (nearRho_integrable a ε ha hε).norm.const_mul a⁻¹
  exact hdom.mono' (nearW_aestronglyMeasurable a ε ha hε)
    (Eventually.of_forall fun x => norm_nearW_le a ε x ha haε)

theorem real_smul_nearW_eq_rho
    (a ε x : ℝ) (ha : 0 < a) (haε : a ≤ ε / 4) :
    x • nearW a ε x = nearRho a ε x := by
  by_cases hx : x = 0
  · subst x
    rw [nearRho_eq_zero_of_abs_le a ε 0 ha haε (by simpa using! ha.le)]
    simp
  · rw [Complex.real_smul]
    unfold nearW
    apply mul_div_cancel₀
    exact_mod_cast hx

theorem nearW_moment_integrable
    (a ε : ℝ) (ha : 0 < a) (hε : 0 < ε) (haε : a ≤ ε / 4) :
    Integrable (fun x : ℝ => x • nearW a ε x) := by
  exact (nearRho_integrable a ε ha hε).congr
    (Eventually.of_forall fun x => (real_smul_nearW_eq_rho a ε x ha haε).symm)

/-- The near-resonant Fourier multiplier denoted by `J_a` in the paper. -/
def nearJ (a ε : ℝ) (t : ℝ) : ℂ :=
  FourierTransform.fourier (nearW a ε) t

theorem integral_nearW_eq_zero (a ε : ℝ) :
    ∫ x : ℝ, nearW a ε x = 0 := by
  have h := MeasureTheory.integral_neg_eq_self (nearW a ε) volume
  have hneg : (fun x : ℝ => nearW a ε (-x)) =
      fun x : ℝ => -nearW a ε x := by
    funext x
    exact nearW_neg a ε x
  rw [hneg, MeasureTheory.integral_neg] at h
  exact neg_eq_self.mp h

theorem nearJ_zero (a ε : ℝ) : nearJ a ε 0 = 0 := by
  unfold nearJ
  rw [Real.fourier_eq]
  simpa using! integral_nearW_eq_zero a ε

theorem nearJ_neg (a ε t : ℝ) : nearJ a ε (-t) = -nearJ a ε t := by
  unfold nearJ
  simp only [Real.fourier_eq]
  calc
    (∫ x : ℝ,
        Real.fourierChar (-inner ℝ x (-t)) • nearW a ε x) =
      ∫ x : ℝ,
        Real.fourierChar (-inner ℝ (-x) (-t)) • nearW a ε (-x) := by
          symm
          exact MeasureTheory.integral_neg_eq_self
            (fun x : ℝ =>
              Real.fourierChar (-inner ℝ x (-t)) • nearW a ε x) volume
    _ = ∫ x : ℝ,
        -(Real.fourierChar (-inner ℝ x t) • nearW a ε x) := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards with x
      rw [nearW_neg]
      simp
    _ = -(∫ x : ℝ,
        Real.fourierChar (-inner ℝ x t) • nearW a ε x) :=
      MeasureTheory.integral_neg _

theorem norm_nearJ_neg (a ε t : ℝ) :
    ‖nearJ a ε (-t)‖ = ‖nearJ a ε t‖ := by
  rw [nearJ_neg, norm_neg]

private theorem fourier_const_mul
    (c : ℂ) (f : ℝ → ℂ) (t : ℝ) :
    FourierTransform.fourier (fun x => c * f x) t =
      c * FourierTransform.fourier f t := by
  simp only [Real.fourier_eq]
  rw [← MeasureTheory.integral_const_mul]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with x
  simp only [Circle.smul_def, smul_eq_mul]
  ring

/-- Exact derivative formula for `J_a`.  In particular, all dependence on
the shrinking scale occurs in the already-controlled transform of `ρ`. -/
theorem nearJ_hasDerivAt
    (a ε t : ℝ) (ha : 0 < a) (hε : 0 < ε) (haε : a ≤ ε / 4) :
    HasDerivAt (nearJ a ε)
      (-(2 * (Real.pi : ℂ) * Complex.I) * nearRhoFourier a ε t) t := by
  have hmoment := nearW_moment_integrable a ε ha hε haε
  have hd := Real.hasDerivAt_fourier
    (nearW_integrable a ε ha hε haε) hmoment t
  have hfun :
      (fun x : ℝ =>
        (-2 * (Real.pi : ℂ) * Complex.I * (x : ℂ)) • nearW a ε x) =
        (fun x : ℝ =>
          -(2 * (Real.pi : ℂ) * Complex.I) * nearRho a ε x) := by
    funext x
    have hxrho : (x : ℂ) * nearW a ε x = nearRho a ε x := by
      simpa only [Complex.real_smul] using!
        real_smul_nearW_eq_rho a ε x ha haε
    simp only [smul_eq_mul]
    calc
      (-2 * (Real.pi : ℂ) * Complex.I * (x : ℂ)) * nearW a ε x =
          -(2 * (Real.pi : ℂ) * Complex.I) *
            ((x : ℂ) * nearW a ε x) := by ring
      _ = -(2 * (Real.pi : ℂ) * Complex.I) * nearRho a ε x := by
        rw [hxrho]
  rw [hfun, fourier_const_mul] at hd
  exact hd

theorem nearJ_differentiableAt
    (a ε t : ℝ) (ha : 0 < a) (hε : 0 < ε) (haε : a ≤ ε / 4) :
    DifferentiableAt ℝ (nearJ a ε) t :=
  (nearJ_hasDerivAt a ε t ha hε haε).differentiableAt

theorem nearJ_deriv
    (a ε t : ℝ) (ha : 0 < a) (hε : 0 < ε) (haε : a ≤ ε / 4) :
    deriv (nearJ a ε) t =
      -(2 * (Real.pi : ℂ) * Complex.I) * nearRhoFourier a ε t :=
  (nearJ_hasDerivAt a ε t ha hε haε).deriv

theorem nearJ_deriv_continuous
    (a ε : ℝ) (ha : 0 < a) (hε : 0 < ε) (haε : a ≤ ε / 4) :
    Continuous (fun t => deriv (nearJ a ε) t) := by
  have hrho : Continuous (nearRhoFourier a ε) := by
    unfold nearRhoFourier
    exact VectorFourier.fourierIntegral_continuous
      Real.continuous_fourierChar continuous_inner
      (nearRho_integrable a ε ha hε)
  simp_rw [nearJ_deriv a ε _ ha hε haε]
  exact continuous_const.mul hrho

/-- A common integrable majorant for all dilates `r J'_a(rt)`,
`1 ≤ r ≤ 2`. -/
def nearJDerivativeDyadicEnvelope (a ε t : ℝ) : ℝ :=
  4 * Real.pi * nearRhoEnvelope a ε t

theorem nearJDerivativeDyadicEnvelope_nonneg
    (a ε t : ℝ) (ha : 0 ≤ a) (hε : 0 ≤ ε) :
    0 ≤ nearJDerivativeDyadicEnvelope a ε t := by
  unfold nearJDerivativeDyadicEnvelope
  exact mul_nonneg (mul_nonneg (by norm_num) Real.pi_nonneg)
    (nearRhoEnvelope_nonneg a ε t ha hε)

/-- Pointwise derivative estimate with a constant independent of the inner
scale `a`. -/
theorem norm_nearJ_deriv_le
    (a ε t : ℝ) (ha : 0 < a) (hε : 0 < ε) (haε : a ≤ ε / 4) :
    ‖deriv (nearJ a ε) t‖ ≤
      2 * Real.pi * nearRhoEnvelope a ε t := by
  rw [nearJ_deriv a ε t ha hε haε, norm_mul]
  have hc : ‖-(2 * (Real.pi : ℂ) * Complex.I)‖ = 2 * Real.pi := by
    simp only [norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      Complex.norm_I, mul_one, abs_of_nonneg Real.pi_nonneg]
    norm_num
  rw [hc]
  exact mul_le_mul_of_nonneg_left
    (norm_nearRhoFourier_le_envelope a ε t ha hε)
    (mul_nonneg (by norm_num) Real.pi_nonneg)

/-- The explicit envelope simultaneously bounds every member of the
dyadic dilation family. -/
theorem nearJ_deriv_dyadic_le_envelope
    (a ε t r : ℝ) (ha : 0 < a) (hε : 0 < ε) (haε : a ≤ ε / 4)
    (ht : 0 ≤ t) (hr₁ : 1 ≤ r) (hr₂ : r ≤ 2) :
    r * ‖deriv (nearJ a ε) (r * t)‖ ≤
      nearJDerivativeDyadicEnvelope a ε t := by
  have hr0 : 0 ≤ r := zero_le_one.trans hr₁
  have henvrt : nearRhoEnvelope a ε (r * t) ≤ nearRhoEnvelope a ε t :=
    nearRhoEnvelope_mul_le a ε t r ha.le hε.le ht hr₁
  have henv0 : 0 ≤ nearRhoEnvelope a ε t :=
    nearRhoEnvelope_nonneg a ε t ha.le hε.le
  calc
    r * ‖deriv (nearJ a ε) (r * t)‖ ≤
        r * (2 * Real.pi * nearRhoEnvelope a ε (r * t)) :=
      mul_le_mul_of_nonneg_left
        (norm_nearJ_deriv_le a ε (r * t) ha hε haε) hr0
    _ ≤ r * (2 * Real.pi * nearRhoEnvelope a ε t) := by
      gcongr
    _ ≤ 2 * (2 * Real.pi * nearRhoEnvelope a ε t) := by
      exact mul_le_mul_of_nonneg_right hr₂
        (mul_nonneg (mul_nonneg (by norm_num) Real.pi_nonneg) henv0)
    _ = nearJDerivativeDyadicEnvelope a ε t := by
      unfold nearJDerivativeDyadicEnvelope
      ring

theorem nearJDerivativeDyadicEnvelope_integrableOn_Ioi
    (a ε : ℝ) (ha : 0 < a) (hε : 0 < ε) :
    IntegrableOn (nearJDerivativeDyadicEnvelope a ε) (Ioi 0) := by
  exact (nearRhoEnvelope_integrableOn_Ioi a ε ha hε).const_mul
    (4 * Real.pi)

/-- The majorant has an exact mass independent of both scales. -/
theorem integral_nearJDerivativeDyadicEnvelope_Ioi
    (a ε : ℝ) (ha : 0 < a) (hε : 0 < ε) :
    ∫ t in Ioi (0 : ℝ), nearJDerivativeDyadicEnvelope a ε t =
      32 * Real.pi * nearProfileDecayConstant := by
  unfold nearJDerivativeDyadicEnvelope
  rw [MeasureTheory.integral_const_mul,
    integral_nearRhoEnvelope_Ioi a ε ha hε]
  ring

/-- The actual supremum occurring in the dyadic bounded-variation
argument.  It is a supremum over the compact dilation interval, rather
than an informal pointwise `sup`. -/
def nearJDerivativeDyadicSup (a ε t : ℝ) : ℝ :=
  sSup ((fun r : ℝ => r * ‖deriv (nearJ a ε) (r * t)‖) '' Icc 1 2)

theorem nearRhoFourier_continuous
    (a ε : ℝ) (ha : 0 < a) (hε : 0 < ε) :
    Continuous (nearRhoFourier a ε) := by
  unfold nearRhoFourier
  exact VectorFourier.fourierIntegral_continuous
    Real.continuous_fourierChar continuous_inner
    (nearRho_integrable a ε ha hε)

/-- Compact maximization preserves continuity here; this supplies the
measurability that is tacit in the paper's integral of a supremum. -/
theorem nearJDerivativeDyadicSup_continuous
    (a ε : ℝ) (ha : 0 < a) (hε : 0 < ε) (haε : a ≤ ε / 4) :
    Continuous (nearJDerivativeDyadicSup a ε) := by
  have hrho := nearRhoFourier_continuous a ε ha hε
  have hfamily : Continuous ↿(fun t r : ℝ =>
      r * ‖deriv (nearJ a ε) (r * t)‖) := by
    change Continuous (fun p : ℝ × ℝ =>
      p.2 * ‖deriv (nearJ a ε) (p.2 * p.1)‖)
    simp_rw [nearJ_deriv a ε _ ha hε haε]
    exact continuous_snd.mul
      ((continuous_const.mul (hrho.comp (continuous_snd.mul continuous_fst))).norm)
  exact isCompact_Icc.continuous_sSup hfamily

theorem nearJDerivativeDyadicSup_le_envelope
    (a ε t : ℝ) (ha : 0 < a) (hε : 0 < ε) (haε : a ≤ ε / 4)
    (ht : 0 ≤ t) :
    nearJDerivativeDyadicSup a ε t ≤
      nearJDerivativeDyadicEnvelope a ε t := by
  unfold nearJDerivativeDyadicSup
  apply csSup_le
  · refine ⟨‖deriv (nearJ a ε) t‖, ?_⟩
    refine ⟨1, by norm_num, ?_⟩
    simp
  · rintro y ⟨r, hr, rfl⟩
    exact nearJ_deriv_dyadic_le_envelope a ε t r ha hε haε ht hr.1 hr.2

theorem nearJDerivativeDyadicSup_nonneg
    (a ε t : ℝ) (ha : 0 < a) (hε : 0 < ε) (haε : a ≤ ε / 4)
    (ht : 0 ≤ t) :
    0 ≤ nearJDerivativeDyadicSup a ε t := by
  unfold nearJDerivativeDyadicSup
  have hbdd : BddAbove
      ((fun r : ℝ => r * ‖deriv (nearJ a ε) (r * t)‖) '' Icc 1 2) := by
    refine ⟨nearJDerivativeDyadicEnvelope a ε t, ?_⟩
    rintro y ⟨r, hr, rfl⟩
    exact nearJ_deriv_dyadic_le_envelope a ε t r ha hε haε ht hr.1 hr.2
  have hone : 0 ≤ (1 : ℝ) * ‖deriv (nearJ a ε) ((1 : ℝ) * t)‖ := by
    positivity
  exact hone.trans (le_csSup hbdd ⟨1, by norm_num, rfl⟩)

theorem nearJDerivativeDyadicSup_integrableOn_Ioi
    (a ε : ℝ) (ha : 0 < a) (hε : 0 < ε) (haε : a ≤ ε / 4) :
    IntegrableOn (nearJDerivativeDyadicSup a ε) (Ioi 0) := by
  have henv := nearJDerivativeDyadicEnvelope_integrableOn_Ioi a ε ha hε
  refine henv.mono'
    (nearJDerivativeDyadicSup_continuous a ε ha hε haε).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [Real.norm_eq_abs,
    abs_of_nonneg (nearJDerivativeDyadicSup_nonneg a ε t ha hε haε ht.le)]
  exact nearJDerivativeDyadicSup_le_envelope a ε t ha hε haε ht.le

/-- Fully quantified version of the uniform dyadic derivative estimate:
the integral of the genuine compact supremum is bounded independently of
the shrinking scale `a`. -/
theorem integral_nearJDerivativeDyadicSup_Ioi_le
    (a ε : ℝ) (ha : 0 < a) (hε : 0 < ε) (haε : a ≤ ε / 4) :
    ∫ t in Ioi (0 : ℝ), nearJDerivativeDyadicSup a ε t ≤
      32 * Real.pi * nearProfileDecayConstant := by
  calc
    ∫ t in Ioi (0 : ℝ), nearJDerivativeDyadicSup a ε t ≤
        ∫ t in Ioi (0 : ℝ), nearJDerivativeDyadicEnvelope a ε t := by
      apply MeasureTheory.integral_mono_ae
        (nearJDerivativeDyadicSup_integrableOn_Ioi a ε ha hε haε)
        (nearJDerivativeDyadicEnvelope_integrableOn_Ioi a ε ha hε)
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact nearJDerivativeDyadicSup_le_envelope a ε t ha hε haε ht.le
    _ = 32 * Real.pi * nearProfileDecayConstant :=
      integral_nearJDerivativeDyadicEnvelope_Ioi a ε ha hε

/-- Uniform zero-order multiplier bound on the positive half-line, obtained
from `J_a(0)=0` and the integrable derivative envelope. -/
theorem norm_nearJ_le_of_nonneg
    (a ε t : ℝ) (ha : 0 < a) (hε : 0 < ε) (haε : a ≤ ε / 4)
    (ht : 0 ≤ t) :
    ‖nearJ a ε t‖ ≤ 32 * Real.pi * nearProfileDecayConstant := by
  have hderiv := nearJ_deriv_continuous a ε ha hε haε
  have hftc :
      ∫ u : ℝ in (0 : ℝ)..t, deriv (nearJ a ε) u =
        nearJ a ε t - nearJ a ε 0 := by
    exact intervalIntegral.integral_deriv_eq_sub
      (fun u _hu => nearJ_differentiableAt a ε u ha hε haε)
      (hderiv.intervalIntegrable 0 t)
  rw [nearJ_zero, sub_zero] at hftc
  have hnormInt : IntervalIntegrable
      (fun u => ‖deriv (nearJ a ε) u‖) volume 0 t :=
    (hderiv.intervalIntegrable 0 t).norm
  have henvIoi := nearJDerivativeDyadicEnvelope_integrableOn_Ioi a ε ha hε
  have henvInt : IntervalIntegrable
      (nearJDerivativeDyadicEnvelope a ε) volume 0 t := by
    rw [intervalIntegrable_iff, uIoc_of_le ht]
    exact henvIoi.mono_set (fun _ hu => hu.1)
  calc
    ‖nearJ a ε t‖ = ‖∫ u : ℝ in (0 : ℝ)..t, deriv (nearJ a ε) u‖ := by
      rw [hftc]
    _ ≤ ∫ u : ℝ in (0 : ℝ)..t, ‖deriv (nearJ a ε) u‖ :=
      intervalIntegral.norm_integral_le_integral_norm ht
    _ ≤ ∫ u : ℝ in (0 : ℝ)..t,
        nearJDerivativeDyadicEnvelope a ε u := by
      apply intervalIntegral.integral_mono_on ht hnormInt henvInt
      intro u hu
      simpa using! nearJ_deriv_dyadic_le_envelope
        a ε u 1 ha hε haε hu.1 (by norm_num) (by norm_num)
    _ ≤ ∫ u in Ioi (0 : ℝ), nearJDerivativeDyadicEnvelope a ε u := by
      rw [intervalIntegral.integral_of_le ht]
      apply MeasureTheory.integral_mono_measure
        (Measure.restrict_mono_set volume (fun _ hu => hu.1))
        (Eventually.of_forall fun u =>
          nearJDerivativeDyadicEnvelope_nonneg a ε u ha.le hε.le)
        henvIoi
    _ = 32 * Real.pi * nearProfileDecayConstant :=
      integral_nearJDerivativeDyadicEnvelope_Ioi a ε ha hε

/-- Uniform zero-order bound for every real frequency, with no dependence
on the shrinking inner scale `a`. -/
theorem norm_nearJ_le
    (a ε t : ℝ) (ha : 0 < a) (hε : 0 < ε) (haε : a ≤ ε / 4) :
    ‖nearJ a ε t‖ ≤ 32 * Real.pi * nearProfileDecayConstant := by
  by_cases ht : 0 ≤ t
  · exact norm_nearJ_le_of_nonneg a ε t ha hε haε ht
  · have hmt : 0 ≤ -t := neg_nonneg.mpr (le_of_not_ge ht)
    have hsymm := norm_nearJ_neg a ε (-t)
    simp only [neg_neg] at hsymm
    rw [hsymm]
    exact norm_nearJ_le_of_nonneg a ε (-t) ha hε haε hmt

/-! ## The reciprocal-square change of variables in total variation -/

/-- One scale of the pullback of `s(1+st)⁻² dt` under `t=K/x²`.
The formula is totalized at zero, where it has the correct value zero. -/
def scaleReciprocalDecayEnvelope (K s x : ℝ) : ℝ :=
  2 * K * s * x / (x ^ 2 + K * s) ^ 2

/-- A primitive for the reciprocal-square envelope. -/
def scaleReciprocalDecayPrimitive (K s x : ℝ) : ℝ :=
  -(K * s / (x ^ 2 + K * s))

theorem scaleReciprocalDecayEnvelope_nonneg
    (K s x : ℝ) (hK : 0 ≤ K) (hs : 0 ≤ s) (hx : 0 ≤ x) :
    0 ≤ scaleReciprocalDecayEnvelope K s x := by
  unfold scaleReciprocalDecayEnvelope
  exact div_nonneg (by positivity) (sq_nonneg _)

theorem hasDerivAt_scaleReciprocalDecayPrimitive
    (K s x : ℝ) (hK : 0 < K) (hs : 0 < s) :
    HasDerivAt (scaleReciprocalDecayPrimitive K s)
      (scaleReciprocalDecayEnvelope K s x) x := by
  have hden : HasDerivAt (fun y : ℝ => y ^ 2 + K * s) (2 * x) x := by
    have hsq := (hasDerivAt_id x).mul (hasDerivAt_id x)
    convert! hsq.add_const (K * s) using 1
    · funext y
      simp [pow_two]
    · simp
      ring
  have hdenpos : 0 < x ^ 2 + K * s := by positivity
  have hinv := hden.inv (ne_of_gt hdenpos)
  have hmul := hinv.const_mul (-(K * s))
  unfold scaleReciprocalDecayPrimitive scaleReciprocalDecayEnvelope
  convert! hmul using 1
  · funext y
    simp only [div_eq_mul_inv, Pi.inv_apply]
    rw [add_comm (y ^ 2) (K * s)]
    ring
  · field_simp

theorem scaleReciprocalDecayPrimitive_tendsto_atTop_zero
    (K s : ℝ) (_hK : 0 < K) (_hs : 0 < s) :
    Tendsto (scaleReciprocalDecayPrimitive K s) atTop (nhds 0) := by
  have hpow : Tendsto (fun x : ℝ => x ^ 2) atTop atTop :=
    tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)
  have hden : Tendsto (fun x : ℝ => x ^ 2 + K * s) atTop atTop :=
    tendsto_atTop_add_const_right atTop (K * s) hpow
  have hquot : Tendsto (fun x : ℝ => K * s / (x ^ 2 + K * s))
      atTop (nhds 0) := tendsto_const_nhds.div_atTop hden
  unfold scaleReciprocalDecayPrimitive
  simpa only [neg_zero] using! hquot.neg

theorem scaleReciprocalDecayEnvelope_integrableOn_Ioi
    (K s : ℝ) (hK : 0 < K) (hs : 0 < s) :
    IntegrableOn (scaleReciprocalDecayEnvelope K s) (Ioi 0) := by
  apply integrableOn_Ioi_deriv_of_nonneg
    ((hasDerivAt_scaleReciprocalDecayPrimitive K s 0 hK hs).continuousAt.continuousWithinAt)
    (fun x _hx => hasDerivAt_scaleReciprocalDecayPrimitive K s x hK hs)
  · intro x hx
    exact scaleReciprocalDecayEnvelope_nonneg K s x hK.le hs.le hx.le
  · exact scaleReciprocalDecayPrimitive_tendsto_atTop_zero K s hK hs

/-- The reciprocal-square pullback also has exact mass one. -/
theorem integral_scaleReciprocalDecayEnvelope_Ioi
    (K s : ℝ) (hK : 0 < K) (hs : 0 < s) :
    ∫ x in Ioi (0 : ℝ), scaleReciprocalDecayEnvelope K s x = 1 := by
  have h := integral_Ioi_of_hasDerivAt_of_tendsto'
    (fun x _hx => hasDerivAt_scaleReciprocalDecayPrimitive K s x hK hs)
    (scaleReciprocalDecayEnvelope_integrableOn_Ioi K s hK hs)
    (scaleReciprocalDecayPrimitive_tendsto_atTop_zero K s hK hs)
  have hKs : K * s ≠ 0 := mul_ne_zero (ne_of_gt hK) (ne_of_gt hs)
  simpa [scaleReciprocalDecayPrimitive, hKs] using! h

/-- Explicit common majorant after the reciprocal-square substitution. -/
def nearJReciprocalSquareEnvelope (a ε K x : ℝ) : ℝ :=
  16 * Real.pi * nearProfileDecayConstant *
    (scaleReciprocalDecayEnvelope K (ε / 2) x +
      scaleReciprocalDecayEnvelope K a x)

theorem nearJReciprocalSquareEnvelope_nonneg
    (a ε K x : ℝ) (ha : 0 ≤ a) (hε : 0 ≤ ε)
    (hK : 0 ≤ K) (hx : 0 ≤ x) :
    0 ≤ nearJReciprocalSquareEnvelope a ε K x := by
  unfold nearJReciprocalSquareEnvelope
  exact mul_nonneg
    (mul_nonneg
      (mul_nonneg (by norm_num) Real.pi_nonneg)
      nearProfileDecayConstant_nonneg)
    (add_nonneg
      (scaleReciprocalDecayEnvelope_nonneg K (ε / 2) x hK (by positivity) hx)
      (scaleReciprocalDecayEnvelope_nonneg K a x hK ha hx))

theorem nearJReciprocalSquareEnvelope_integrableOn_Ioi
    (a ε K : ℝ) (ha : 0 < a) (hε : 0 < ε) (hK : 0 < K) :
    IntegrableOn (nearJReciprocalSquareEnvelope a ε K) (Ioi 0) := by
  have hout := scaleReciprocalDecayEnvelope_integrableOn_Ioi
    K (ε / 2) hK (by positivity)
  have hin := scaleReciprocalDecayEnvelope_integrableOn_Ioi K a hK ha
  exact (hout.add hin).const_mul
    (16 * Real.pi * nearProfileDecayConstant)

theorem integral_nearJReciprocalSquareEnvelope_Ioi
    (a ε K : ℝ) (ha : 0 < a) (hε : 0 < ε) (hK : 0 < K) :
    ∫ x in Ioi (0 : ℝ), nearJReciprocalSquareEnvelope a ε K x =
      32 * Real.pi * nearProfileDecayConstant := by
  unfold nearJReciprocalSquareEnvelope
  rw [MeasureTheory.integral_const_mul]
  rw [MeasureTheory.integral_add
    (scaleReciprocalDecayEnvelope_integrableOn_Ioi K (ε / 2) hK (by positivity))
    (scaleReciprocalDecayEnvelope_integrableOn_Ioi K a hK ha)]
  rw [integral_scaleReciprocalDecayEnvelope_Ioi K (ε / 2) hK (by positivity),
    integral_scaleReciprocalDecayEnvelope_Ioi K a hK ha]
  ring

theorem reciprocal_scaleDecayEnvelope_identity
    (K s x : ℝ) (hK : 0 < K) (hs : 0 < s) (hx : 0 < x) :
    (2 * K / x ^ 3) * scaleDecayEnvelope s (K / x ^ 2) =
      scaleReciprocalDecayEnvelope K s x := by
  have hx0 : x ≠ 0 := ne_of_gt hx
  have hden : 0 < 1 + s * (K / x ^ 2) := by positivity
  unfold scaleDecayEnvelope scaleReciprocalDecayEnvelope
  field_simp [hx0, ne_of_gt hden]

theorem reciprocal_nearJDerivativeEnvelope_identity
    (a ε K x : ℝ) (ha : 0 < a) (hε : 0 < ε)
    (hK : 0 < K) (hx : 0 < x) :
    (2 * K / x ^ 3) * nearJDerivativeDyadicEnvelope a ε (K / x ^ 2) =
      nearJReciprocalSquareEnvelope a ε K x := by
  have ht : 0 ≤ K / x ^ 2 := by positivity
  rw [nearJDerivativeDyadicEnvelope,
    nearRhoEnvelope_eq_scaleDecay_of_nonneg a ε (K / x ^ 2) ht]
  unfold nearJReciprocalSquareEnvelope
  calc
    (2 * K / x ^ 3) *
        (4 * Real.pi *
          (4 * nearProfileDecayConstant *
            (scaleDecayEnvelope (ε / 2) (K / x ^ 2) +
              scaleDecayEnvelope a (K / x ^ 2)))) =
      16 * Real.pi * nearProfileDecayConstant *
        ((2 * K / x ^ 3) * scaleDecayEnvelope (ε / 2) (K / x ^ 2) +
          (2 * K / x ^ 3) * scaleDecayEnvelope a (K / x ^ 2)) := by ring
    _ = 16 * Real.pi * nearProfileDecayConstant *
        (scaleReciprocalDecayEnvelope K (ε / 2) x +
          scaleReciprocalDecayEnvelope K a x) := by
      rw [reciprocal_scaleDecayEnvelope_identity K (ε / 2) x hK
          (by positivity) hx,
        reciprocal_scaleDecayEnvelope_identity K a x hK ha hx]

/-- The composed multiplier whose variation occurs in the Abel estimate. -/
def nearJReciprocalSquare (a ε n : ℝ) (x : ℝ) : ℂ :=
  nearJ a ε (n / x ^ 2)

theorem reciprocalSquareArgument_hasDerivAt
    (n x : ℝ) (hx : x ≠ 0) :
    HasDerivAt (fun y : ℝ => n / y ^ 2) (-2 * n / x ^ 3) x := by
  have hsq : HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x := by
    have hmul := (hasDerivAt_id x).mul (hasDerivAt_id x)
    convert! hmul using 1
    · funext y
      simp [pow_two]
    · simp
      ring
  have hquot := (hasDerivAt_const x n).div hsq (pow_ne_zero 2 hx)
  convert! hquot using 1
  field_simp [hx]
  ring

theorem nearJReciprocalSquare_hasDerivAt
    (a ε n x : ℝ) (ha : 0 < a) (hε : 0 < ε) (haε : a ≤ ε / 4)
    (hx : x ≠ 0) :
    HasDerivAt (nearJReciprocalSquare a ε n)
      ((-2 * n / x ^ 3) • deriv (nearJ a ε) (n / x ^ 2)) x := by
  have hout := (nearJ_differentiableAt a ε (n / x ^ 2) ha hε haε).hasDerivAt
  have hinner := reciprocalSquareArgument_hasDerivAt n x hx
  simpa only [nearJReciprocalSquare, Function.comp_def] using!
    hout.scomp x hinner

/-- Pointwise form of (3.10): every `n` in the dyadic block has its
reciprocal-square derivative bounded by one common integrable function. -/
theorem norm_nearJReciprocalSquare_deriv_le_envelope
    (a ε K n x : ℝ) (ha : 0 < a) (hε : 0 < ε) (haε : a ≤ ε / 4)
    (hK : 0 < K) (hn₁ : K ≤ n) (hn₂ : n ≤ 2 * K) (hx : 0 < x) :
    ‖deriv (nearJReciprocalSquare a ε n) x‖ ≤
      nearJReciprocalSquareEnvelope a ε K x := by
  have hn : 0 < n := hK.trans_le hn₁
  have hr₁ : 1 ≤ n / K := (le_div_iff₀ hK).2 (by simpa using! hn₁)
  have hr₂ : n / K ≤ 2 := (div_le_iff₀ hK).2 (by simpa using! hn₂)
  have ht : 0 ≤ K / x ^ 2 := by positivity
  have harg : (n / K) * (K / x ^ 2) = n / x ^ 2 := by
    field_simp [ne_of_gt hK, ne_of_gt hx]
  have hdy := nearJ_deriv_dyadic_le_envelope a ε (K / x ^ 2) (n / K)
    ha hε haε ht hr₁ hr₂
  rw [harg] at hdy
  have hcomp := nearJReciprocalSquare_hasDerivAt a ε n x ha hε haε (ne_of_gt hx)
  rw [hcomp.deriv, norm_smul, Real.norm_eq_abs]
  have hcoef : |-2 * n / x ^ 3| = 2 * n / x ^ 3 := by
    have hnonpos : -2 * n / x ^ 3 ≤ 0 := by
      apply div_nonpos_of_nonpos_of_nonneg
      · nlinarith
      · positivity
    rw [abs_of_nonpos hnonpos]
    ring
  rw [hcoef]
  calc
    (2 * n / x ^ 3) * ‖deriv (nearJ a ε) (n / x ^ 2)‖ =
        (2 * K / x ^ 3) *
          ((n / K) * ‖deriv (nearJ a ε) (n / x ^ 2)‖) := by
      field_simp [ne_of_gt hK, ne_of_gt hx]
    _ ≤ (2 * K / x ^ 3) *
        nearJDerivativeDyadicEnvelope a ε (K / x ^ 2) := by
      exact mul_le_mul_of_nonneg_left hdy (by positivity)
    _ = nearJReciprocalSquareEnvelope a ε K x :=
      reciprocal_nearJDerivativeEnvelope_identity a ε K x ha hε hK hx

/-- The natural-number dyadic block is nonempty (it contains its left
endpoint), including when `K=0`. -/
theorem natDyadicIcc_nonempty (K : ℕ) :
    (Finset.Icc K (2 * K)).Nonempty := by
  exact ⟨K, Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩⟩

/-- Genuine maximum over all integer frequencies in one dyadic block. -/
def nearJReciprocalSquareDyadicMax
    (a ε : ℝ) (K : ℕ) (x : ℝ) : ℝ :=
  (Finset.Icc K (2 * K)).sup' (natDyadicIcc_nonempty K)
    (fun n => ‖deriv (nearJReciprocalSquare a ε (n : ℝ)) x‖)

theorem nearJReciprocalSquareDyadicMax_continuousOn_Ioi
    (a ε : ℝ) (K : ℕ) (ha : 0 < a) (hε : 0 < ε)
    (haε : a ≤ ε / 4) :
    ContinuousOn (nearJReciprocalSquareDyadicMax a ε K) (Ioi 0) := by
  unfold nearJReciprocalSquareDyadicMax
  apply ContinuousOn.finset_sup'_apply (natDyadicIcc_nonempty K)
  intro n _hn
  have harg : ContinuousOn (fun x : ℝ => (n : ℝ) / x ^ 2) (Ioi 0) := by
    exact continuousOn_const.div (continuousOn_id.pow 2)
      (fun x hx => pow_ne_zero 2 (ne_of_gt hx))
  have hcoef : ContinuousOn (fun x : ℝ => -2 * (n : ℝ) / x ^ 3) (Ioi 0) := by
    exact continuousOn_const.div (continuousOn_id.pow 3)
      (fun x hx => pow_ne_zero 3 (ne_of_gt hx))
  have houter : ContinuousOn
      (fun x : ℝ => deriv (nearJ a ε) ((n : ℝ) / x ^ 2)) (Ioi 0) := by
    simpa only [Function.comp_def] using!
      (nearJ_deriv_continuous a ε ha hε haε).continuousOn.comp harg
        (fun _ _ => mem_univ _)
  have hexplicit : ContinuousOn
      (fun x : ℝ =>
        ‖(-2 * (n : ℝ) / x ^ 3) •
          deriv (nearJ a ε) ((n : ℝ) / x ^ 2)‖) (Ioi 0) :=
    (hcoef.smul houter).norm
  apply hexplicit.congr
  intro x hx
  change ‖deriv (nearJReciprocalSquare a ε (n : ℝ)) x‖ =
    ‖(-2 * (n : ℝ) / x ^ 3) •
      deriv (nearJ a ε) ((n : ℝ) / x ^ 2)‖
  rw [(nearJReciprocalSquare_hasDerivAt a ε (n : ℝ) x ha hε haε
    (ne_of_gt hx)).deriv]

theorem nearJReciprocalSquareDyadicMax_le_envelope
    (a ε : ℝ) (K : ℕ) (ha : 0 < a) (hε : 0 < ε)
    (haε : a ≤ ε / 4) (hK : 0 < K) {x : ℝ} (hx : 0 < x) :
    nearJReciprocalSquareDyadicMax a ε K x ≤
      nearJReciprocalSquareEnvelope a ε (K : ℝ) x := by
  unfold nearJReciprocalSquareDyadicMax
  apply Finset.sup'_le (natDyadicIcc_nonempty K)
  intro n hn
  have hbounds := Finset.mem_Icc.mp hn
  apply norm_nearJReciprocalSquare_deriv_le_envelope
    a ε (K : ℝ) (n : ℝ) x ha hε haε
  · exact_mod_cast hK
  · exact_mod_cast hbounds.1
  · norm_num at hbounds ⊢
    exact_mod_cast hbounds.2
  · exact hx

theorem nearJReciprocalSquareDyadicMax_nonneg
    (a ε : ℝ) (K : ℕ) (x : ℝ) :
    0 ≤ nearJReciprocalSquareDyadicMax a ε K x := by
  unfold nearJReciprocalSquareDyadicMax
  have hmem : K ∈ Finset.Icc K (2 * K) :=
    Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩
  exact (norm_nonneg (deriv (nearJReciprocalSquare a ε (K : ℝ)) x)).trans
    (Finset.le_sup' (s := Finset.Icc K (2 * K))
      (fun n : ℕ => ‖deriv (nearJReciprocalSquare a ε (n : ℝ)) x‖) hmem)

/-- Fully formal form of (3.10), with the supremum interpreted as the
actual maximum over all natural `K ≤ n ≤ 2K`. -/
theorem nearJReciprocalSquareDyadicMax_integrableOn_Ioi
    (a ε : ℝ) (K : ℕ) (ha : 0 < a) (hε : 0 < ε)
    (haε : a ≤ ε / 4) (hK : 0 < K) :
    IntegrableOn (nearJReciprocalSquareDyadicMax a ε K) (Ioi 0) := by
  have henv := nearJReciprocalSquareEnvelope_integrableOn_Ioi
    a ε (K : ℝ) ha hε (by exact_mod_cast hK)
  refine henv.mono'
    ((nearJReciprocalSquareDyadicMax_continuousOn_Ioi a ε K ha hε haε).aestronglyMeasurable
      measurableSet_Ioi) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  rw [Real.norm_eq_abs,
    abs_of_nonneg (nearJReciprocalSquareDyadicMax_nonneg a ε K x)]
  exact nearJReciprocalSquareDyadicMax_le_envelope
    a ε K ha hε haε hK hx

theorem integral_nearJReciprocalSquareDyadicMax_Ioi_le
    (a ε : ℝ) (K : ℕ) (ha : 0 < a) (hε : 0 < ε)
    (haε : a ≤ ε / 4) (hK : 0 < K) :
    ∫ x in Ioi (0 : ℝ), nearJReciprocalSquareDyadicMax a ε K x ≤
      32 * Real.pi * nearProfileDecayConstant := by
  calc
    ∫ x in Ioi (0 : ℝ), nearJReciprocalSquareDyadicMax a ε K x ≤
        ∫ x in Ioi (0 : ℝ),
          nearJReciprocalSquareEnvelope a ε (K : ℝ) x := by
      apply MeasureTheory.integral_mono_ae
        (nearJReciprocalSquareDyadicMax_integrableOn_Ioi
          a ε K ha hε haε hK)
        (nearJReciprocalSquareEnvelope_integrableOn_Ioi
          a ε (K : ℝ) ha hε (by exact_mod_cast hK))
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      exact nearJReciprocalSquareDyadicMax_le_envelope
        a ε K ha hε haε hK hx
    _ = 32 * Real.pi * nearProfileDecayConstant :=
      integral_nearJReciprocalSquareEnvelope_Ioi
        a ε (K : ℝ) ha hε (by exact_mod_cast hK)

end

end Erdos1002
