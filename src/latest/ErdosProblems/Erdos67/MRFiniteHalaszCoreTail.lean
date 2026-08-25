import ErdosProblems.Erdos67.MRFiniteHalaszProductSmoothing

/-!
# Core--tail estimate for the compact finite-Halasz smoothing kernel

This file supplies the analytic inequality used after the exact product
smoothing identity.  On a bounded frequency core it is the usual
`L∞ × L² × L²` estimate.  Outside the core all three factors are
bounded by their concrete absolute Dirichlet masses, while the integrable
Schwartz kernel supplies a tail tending to zero.
-/

open scoped BigOperators ComplexConjugate ENNReal
open Complex MeasureTheory Set

namespace Erdos67.MRHalaszBands

noncomputable section

open Erdos67.MRFiniteHalaszSmoothing

/-- Two-factor core--tail inequality, used for the unrestricted finite
dyadic polynomial before any typical-support restriction is imposed. -/
theorem norm_integral_mul_le_core_tail
    (f K : ℝ → ℂ) {R M Z : ℝ}
    (_hR : 0 ≤ R) (_hM : 0 ≤ M) (_hZ : 0 ≤ Z)
    (hf : Continuous f) (hKc : Continuous K) (hKi : Integrable K)
    (hfGlobal : ∀ x, ‖f x‖ ≤ Z)
    (hfCore : ∀ x, |x| ≤ R → ‖f x‖ ≤ M) :
    ‖∫ x : ℝ, f x * K x‖ ≤
      M * (∫ x in Set.Icc (-R) R, ‖K x‖) +
        Z * (∫ x in (Set.Icc (-R) R)ᶜ, ‖K x‖) := by
  let S : Set ℝ := Set.Icc (-R) R
  let F : ℝ → ℂ := fun x ↦ f x * K x
  have hS : MeasurableSet S := measurableSet_Icc
  have hmajor : Integrable (fun x : ℝ ↦ Z * ‖K x‖) := hKi.norm.const_mul Z
  have hF : Integrable F := by
    refine hmajor.mono' (hf.mul hKc).aestronglyMeasurable ?_
    filter_upwards with x
    dsimp only [F]
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hfGlobal x) (norm_nonneg _)
  have hcoreMajor : IntegrableOn (fun x : ℝ ↦ M * ‖K x‖) S :=
    (hKi.norm.const_mul M).integrableOn
  have hcore : ‖∫ x in S, F x‖ ≤ M * ∫ x in S, ‖K x‖ := by
    calc
      ‖∫ x in S, F x‖ ≤ ∫ x in S, M * ‖K x‖ := by
        apply norm_integral_le_of_norm_le hcoreMajor
        filter_upwards [ae_restrict_mem hS] with x hx
        dsimp only [F]
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right
          (hfCore x (abs_le.mpr ⟨hx.1, hx.2⟩)) (norm_nonneg _)
      _ = M * ∫ x in S, ‖K x‖ := by rw [integral_const_mul]
  have htail : ‖∫ x in Sᶜ, F x‖ ≤ Z * ∫ x in Sᶜ, ‖K x‖ := by
    calc
      ‖∫ x in Sᶜ, F x‖ ≤ ∫ x in Sᶜ, Z * ‖K x‖ := by
        apply norm_integral_le_of_norm_le hmajor.integrableOn
        filter_upwards with x
        dsimp only [F]
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right (hfGlobal x) (norm_nonneg _)
      _ = Z * ∫ x in Sᶜ, ‖K x‖ := by rw [integral_const_mul]
  have hsplit :
      (∫ x : ℝ, F x) = (∫ x in S, F x) + ∫ x in Sᶜ, F x :=
    (integral_add_compl hS hF).symm
  change ‖∫ x : ℝ, F x‖ ≤ _
  rw [hsplit]
  exact (norm_add_le _ _).trans (add_le_add hcore htail)

/-- A four-factor core--tail inequality.  It is formulated on the real
line because that is the frequency variable in the finite Halasz smoothing
identity.  Every quantity on the right is an explicit integral or scalar
bound; no asymptotic input is hidden in the statement. -/
theorem norm_integral_four_mul_le_core_tail
    (f g h K : ℝ → ℂ) {R M Q Z G H : ℝ}
    (_hR : 0 ≤ R) (hM : 0 ≤ M) (hQ : 0 ≤ Q)
    (hZ : 0 ≤ Z) (hG : 0 ≤ G) (_hH : 0 ≤ H)
    (hf : Continuous f) (hg : Continuous g) (hh : Continuous h)
    (hKc : Continuous K) (hKi : Integrable K)
    (hfGlobal : ∀ x, ‖f x‖ ≤ Z)
    (hgGlobal : ∀ x, ‖g x‖ ≤ G)
    (hhGlobal : ∀ x, ‖h x‖ ≤ H)
    (hfCore : ∀ x, |x| ≤ R → ‖f x‖ ≤ M)
    (hKCore : ∀ x, |x| ≤ R → ‖K x‖ ≤ Q) :
    ‖∫ x : ℝ, f x * g x * h x * K x‖ ≤
      M * Q *
          ((∫ x in Set.Icc (-R) R, ‖g x‖ ^ (2 : ℝ)) ^ ((1 : ℝ) / 2)) *
          ((∫ x in Set.Icc (-R) R, ‖h x‖ ^ (2 : ℝ)) ^ ((1 : ℝ) / 2)) +
        Z * G * H * ∫ x in (Set.Icc (-R) R)ᶜ, ‖K x‖ := by
  let S : Set ℝ := Set.Icc (-R) R
  let F : ℝ → ℂ := fun x ↦ f x * g x * h x * K x
  have hS : MeasurableSet S := measurableSet_Icc
  have hmajor : Integrable (fun x : ℝ ↦ Z * G * H * ‖K x‖) :=
    hKi.norm.const_mul _
  have hF : Integrable F := by
    refine hmajor.mono' ?_ ?_
    · exact (hf.mul hg |>.mul hh |>.mul hKc).aestronglyMeasurable
    · filter_upwards with x
      dsimp only [F]
      rw [norm_mul, norm_mul, norm_mul]
      have hfg : ‖f x‖ * ‖g x‖ ≤ Z * G :=
        mul_le_mul (hfGlobal x) (hgGlobal x) (norm_nonneg _) hZ
      have hfgh : ‖f x‖ * ‖g x‖ * ‖h x‖ ≤ Z * G * H :=
        mul_le_mul hfg (hhGlobal x) (norm_nonneg _) (mul_nonneg hZ hG)
      exact mul_le_mul_of_nonneg_right hfgh (norm_nonneg _)
  have hgLp : MemLp g (2 : ENNReal) (volume.restrict S) := by
    apply MemLp.of_bound (hg.aestronglyMeasurable.restrict) G
    filter_upwards with x
    exact hgGlobal x
  have hhLp : MemLp h (2 : ENNReal) (volume.restrict S) := by
    apply MemLp.of_bound (hh.aestronglyMeasurable.restrict) H
    filter_upwards with x
    exact hhGlobal x
  have hfKCore : ∀ᵐ x ∂(volume.restrict S), ‖f x * K x‖ ≤ M * Q := by
    apply ae_restrict_of_forall_mem hS
    intro x hx
    rw [norm_mul]
    apply mul_le_mul (hfCore x (abs_le.mpr ⟨hx.1, hx.2⟩))
      (hKCore x (abs_le.mpr ⟨hx.1, hx.2⟩)) (norm_nonneg _) hM
  have hcore := norm_integral_triple_le_Linfty_mul_L2_mul_L2
    (mu := volume.restrict S) (f := fun x ↦ f x * K x)
    (g := g) (k := h) (mul_nonneg hM hQ) hfKCore hgLp hhLp
  have hcore' :
      ‖∫ x in S, F x‖ ≤
        M * Q *
          ((∫ x in S, ‖g x‖ ^ (2 : ℝ)) ^ ((1 : ℝ) / 2)) *
          ((∫ x in S, ‖h x‖ ^ (2 : ℝ)) ^ ((1 : ℝ) / 2)) := by
    have hident : (∫ x in S, F x) =
        ∫ x in S, (f x * K x) * g x * h x := by
      apply integral_congr_ae
      filter_upwards with x
      dsimp only [F]
      ring
    rw [hident]
    simpa only [mul_assoc] using hcore
  have htailMajor : IntegrableOn
      (fun x : ℝ ↦ Z * G * H * ‖K x‖) Sᶜ := hmajor.integrableOn
  have htail :
      ‖∫ x in Sᶜ, F x‖ ≤ Z * G * H * ∫ x in Sᶜ, ‖K x‖ := by
    calc
      ‖∫ x in Sᶜ, F x‖ ≤
          ∫ x in Sᶜ, Z * G * H * ‖K x‖ := by
        apply norm_integral_le_of_norm_le htailMajor
        filter_upwards with x
        dsimp only [F]
        rw [norm_mul, norm_mul, norm_mul]
        have hfg : ‖f x‖ * ‖g x‖ ≤ Z * G :=
          mul_le_mul (hfGlobal x) (hgGlobal x) (norm_nonneg _) hZ
        have hfgh : ‖f x‖ * ‖g x‖ * ‖h x‖ ≤ Z * G * H :=
          mul_le_mul hfg (hhGlobal x) (norm_nonneg _) (mul_nonneg hZ hG)
        exact mul_le_mul_of_nonneg_right hfgh (norm_nonneg _)
      _ = Z * G * H * ∫ x in Sᶜ, ‖K x‖ := by
        rw [MeasureTheory.integral_const_mul]
  have hsplit :
      (∫ x : ℝ, F x) = (∫ x in S, F x) + ∫ x in Sᶜ, F x := by
    exact (integral_add_compl hS hF).symm
  change ‖∫ x : ℝ, F x‖ ≤ _
  rw [hsplit]
  exact (norm_add_le _ _).trans (add_le_add hcore' htail)

/-- If two nonnegative square energies have the same upper bound, the
product of their half-powers is bounded by that common upper bound. -/
theorem rpow_half_mul_rpow_half_le
    {E₂ E₃ E : ℝ} (hE₂ : 0 ≤ E₂) (hE₃ : 0 ≤ E₃) (hE : 0 ≤ E)
    (h₂ : E₂ ≤ E) (h₃ : E₃ ≤ E) :
    E₂ ^ ((1 : ℝ) / 2) * E₃ ^ ((1 : ℝ) / 2) ≤ E := by
  have h₂' : E₂ ^ ((1 : ℝ) / 2) ≤ E ^ ((1 : ℝ) / 2) :=
    Real.rpow_le_rpow hE₂ h₂ (by norm_num)
  have h₃' : E₃ ^ ((1 : ℝ) / 2) ≤ E ^ ((1 : ℝ) / 2) :=
    Real.rpow_le_rpow hE₃ h₃ (by norm_num)
  calc
    E₂ ^ ((1 : ℝ) / 2) * E₃ ^ ((1 : ℝ) / 2) ≤
        E ^ ((1 : ℝ) / 2) * E ^ ((1 : ℝ) / 2) :=
      mul_le_mul h₂' h₃' (Real.rpow_nonneg hE₃ _) (Real.rpow_nonneg hE _)
    _ = Real.sqrt E ^ 2 := by rw [Real.sqrt_eq_rpow]; ring
    _ = E := Real.sq_sqrt hE

/-! ## Concrete masses for the finite three-band product -/

/-- Absolute mass of an L-series on the real line `Re(s)=sigma`. -/
def finiteHalaszLSeriesAbsoluteMass (a : ℕ → ℂ) (sigma : ℝ) : ℝ :=
  ∑' n : ℕ, ‖LSeries.term a (sigma : ℂ) n‖

/-- Absolute mass of a positive finite band factor. -/
def finiteHalaszPositiveBandMass
    (f : ℕ → ℂ) (Q : ℕ → Prop) [DecidablePred Q]
    (N : ℕ) (sigma : ℝ) : ℝ :=
  ∑ n ∈ Finset.Ioc 1 N, ‖smoothedPrimeBandCoefficient f Q sigma n‖

/-- Square energy of one positive finite band on the smoothing core. -/
def finiteHalaszPositiveBandCoreEnergy
    (f : ℕ → ℂ) (Q : ℕ → Prop) [DecidablePred Q]
    (N : ℕ) (sigma t0 R : ℝ) : ℝ :=
  ∫ xi in Set.Icc (-R) R,
    ‖LSeries (positivePrefixTruncate (primeBandCoefficient f Q) N)
        ((sigma : ℂ) + Complex.I *
          ((t0 - 2 * Real.pi * xi : ℝ) : ℂ))‖ ^ (2 : ℝ)

/-- Uniform Fourier bound for the explicit compact smoothing kernel. -/
def logTrapezoidKernelUniformBound
    (delta A B : ℝ) (hdelta : 0 < delta) : ℝ :=
  ‖(logTrapezoidSchwartz delta A B hdelta).toLp 1‖

/-- Exact `L¹` tail of the explicit Schwartz kernel outside `[-R,R]`. -/
def logTrapezoidKernelTailMass
    (delta A B : ℝ) (hdelta : 0 < delta) (R : ℝ) : ℝ :=
  ∫ xi in (Set.Icc (-R) R)ᶜ,
    ‖logTrapezoidKernel delta A B hdelta xi‖

/-- Exact compact smoothing of an unrestricted absolutely convergent
L-series, with compact support turning the countable coefficient side into
the finite positive prefix `(0,N]`. -/
theorem integral_LSeries_mul_logTrapezoidKernel_eq_finitePrefix
    (a : ℕ → ℂ) {sigma : ℝ}
    (hsum : LSeriesSummable a (sigma : ℂ))
    {N : ℕ} (hN : 0 < N)
    (delta A B : ℝ) (hdelta : 0 < delta)
    (hB : B ≤ Real.log N) (t0 : ℝ) :
    (∫ xi : ℝ,
        LSeries a
            ((sigma : ℂ) + Complex.I *
              ((t0 - 2 * Real.pi * xi : ℝ) : ℂ)) *
          logTrapezoidKernel delta A B hdelta xi) =
      ∑ n ∈ Finset.Ioc 0 N,
        LSeries.term a (sigma : ℂ) n * logarithmicPhase n (-t0) *
          logTrapezoidWindow delta A B hdelta (Real.log n) := by
  classical
  rw [integral_LSeries_mul_logTrapezoidKernel a sigma hsum
    delta A B hdelta t0]
  rw [tsum_eq_sum (s := Finset.Ioc 0 N)]
  intro n hn
  by_cases hn0 : n = 0
  · subst n
    simp
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
  have hNn : N < n := by
    by_contra hnot
    exact hn (Finset.mem_Ioc.mpr ⟨hnpos, Nat.le_of_not_gt hnot⟩)
  have hlog : Real.log (N : ℝ) < Real.log (n : ℝ) :=
    Real.strictMonoOn_log
      (show (N : ℝ) ∈ Set.Ioi 0 by
        rw [Set.mem_Ioi]
        exact_mod_cast hN)
      (show (n : ℝ) ∈ Set.Ioi 0 by
        rw [Set.mem_Ioi]
        exact_mod_cast hnpos)
      (by exact_mod_cast hNn)
  have hnotmem : Real.log (n : ℝ) ∉ Set.Icc A B := by
    intro hmem
    linarith [hmem.2]
  rw [logTrapezoidWindow_eq_zero_of_not_mem delta A B hdelta hnotmem,
    mul_zero]

theorem finiteHalaszLSeriesAbsoluteMass_nonneg
    (a : ℕ → ℂ) (sigma : ℝ) :
    0 ≤ finiteHalaszLSeriesAbsoluteMass a sigma := by
  unfold finiteHalaszLSeriesAbsoluteMass
  exact tsum_nonneg fun _ ↦ norm_nonneg _

theorem finiteHalaszPositiveBandMass_nonneg
    (f : ℕ → ℂ) (Q : ℕ → Prop) [DecidablePred Q]
    (N : ℕ) (sigma : ℝ) :
    0 ≤ finiteHalaszPositiveBandMass f Q N sigma := by
  unfold finiteHalaszPositiveBandMass
  positivity

theorem finiteHalaszPositiveBandCoreEnergy_nonneg
    (f : ℕ → ℂ) (Q : ℕ → Prop) [DecidablePred Q]
    (N : ℕ) (sigma t0 R : ℝ) :
    0 ≤ finiteHalaszPositiveBandCoreEnergy f Q N sigma t0 R := by
  unfold finiteHalaszPositiveBandCoreEnergy
  exact integral_nonneg fun _ ↦ Real.rpow_nonneg (norm_nonneg _) _

theorem logTrapezoidKernelUniformBound_nonneg
    (delta A B : ℝ) (hdelta : 0 < delta) :
    0 ≤ logTrapezoidKernelUniformBound delta A B hdelta :=
  norm_nonneg _

theorem logTrapezoidKernelTailMass_nonneg
    (delta A B : ℝ) (hdelta : 0 < delta) (R : ℝ) :
    0 ≤ logTrapezoidKernelTailMass delta A B hdelta R := by
  unfold logTrapezoidKernelTailMass
  exact integral_nonneg fun _ ↦ norm_nonneg _

/-- The exact Schwartz-kernel tail is a genuine `o(1)` term along any
natural frequency cutoff tending to infinity. -/
theorem tendsto_logTrapezoidKernelTailMass_nat
    (delta A B : ℝ) (hdelta : 0 < delta) :
    Filter.Tendsto
      (fun R : ℕ ↦
        logTrapezoidKernelTailMass delta A B hdelta (R : ℝ))
      Filter.atTop (nhds 0) := by
  let k : ℝ → ℝ := fun xi ↦ ‖logTrapezoidKernel delta A B hdelta xi‖
  let S : ℕ → Set ℝ := fun R ↦ (Set.Icc (-(R : ℝ)) (R : ℝ))ᶜ
  have hk : Integrable k :=
    (integrable_logTrapezoidKernel delta A B hdelta).norm
  have hSmeas : ∀ R, MeasurableSet (S R) := fun R ↦ measurableSet_Icc.compl
  have hSanti : Antitone S := by
    intro R U hRU
    apply compl_subset_compl.mpr
    intro x hx
    have hcast : (R : ℝ) ≤ U := by exact_mod_cast hRU
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hinter : (⋂ R : ℕ, S R) = ∅ := by
    ext x
    simp only [Set.mem_iInter, Set.mem_empty_iff_false, iff_false]
    intro hx
    obtain ⟨R, hR⟩ := exists_nat_gt |x|
    have hRreal : |x| < (R : ℝ) := by exact_mod_cast hR
    have hxI : x ∈ Set.Icc (-(R : ℝ)) (R : ℝ) :=
      ⟨by linarith [neg_le_abs x], by linarith [le_abs_self x]⟩
    exact hx R hxI
  have ht := tendsto_setIntegral_of_antitone hSmeas hSanti
    (f := k) (μ := volume) ⟨0, hk.integrableOn⟩
  rw [hinter] at ht
  simpa [logTrapezoidKernelTailMass, k, S] using ht

theorem norm_logTrapezoidKernel_le_uniformBound
    (delta A B : ℝ) (hdelta : 0 < delta) (xi : ℝ) :
    ‖logTrapezoidKernel delta A B hdelta xi‖ ≤
      logTrapezoidKernelUniformBound delta A B hdelta := by
  exact SchwartzMap.norm_fourier_apply_le_toLp_one
    (logTrapezoidSchwartz delta A B hdelta) xi

/-- Absolute convergence gives a frequency-uniform bound by the concrete
absolute mass on the real line. -/
theorem norm_LSeries_le_finiteHalaszLSeriesAbsoluteMass
    (a : ℕ → ℂ) {sigma : ℝ}
    (hsum : LSeriesSummable a (sigma : ℂ)) (t : ℝ) :
    ‖LSeries a ((sigma : ℂ) + Complex.I * (t : ℂ))‖ ≤
      finiteHalaszLSeriesAbsoluteMass a sigma := by
  unfold LSeries finiteHalaszLSeriesAbsoluteMass
  have hsumt : LSeriesSummable a
      ((sigma : ℂ) + Complex.I * (t : ℂ)) := by
    exact LSeriesSummable.of_re_le_re (by simp) hsum
  calc
    ‖∑' n : ℕ,
        LSeries.term a ((sigma : ℂ) + Complex.I * (t : ℂ)) n‖ ≤
        ∑' n : ℕ,
          ‖LSeries.term a ((sigma : ℂ) + Complex.I * (t : ℂ)) n‖ :=
      norm_tsum_le_tsum_norm hsumt.norm
    _ = ∑' n : ℕ, ‖LSeries.term a (sigma : ℂ) n‖ := by
      apply tsum_congr
      intro n
      rw [LSeries.norm_term_eq, LSeries.norm_term_eq]
      simp

/-- A positive finite factor is bounded uniformly by its explicit finite
absolute mass. -/
theorem norm_LSeries_positivePrefixTruncate_le_bandMass
    (f : ℕ → ℂ) (Q : ℕ → Prop) [DecidablePred Q]
    (N : ℕ) (sigma t : ℝ) :
    ‖LSeries (positivePrefixTruncate (primeBandCoefficient f Q) N)
        ((sigma : ℂ) + Complex.I * (t : ℂ))‖ ≤
      finiteHalaszPositiveBandMass f Q N sigma := by
  rw [LSeries_positivePrefixTruncate_eq_logarithmic]
  unfold logarithmicDirichletPolynomial finiteHalaszPositiveBandMass
  refine (norm_sum_le _ _).trans ?_
  apply Finset.sum_le_sum
  intro n hn
  rw [norm_mul, norm_logarithmicPhase, mul_one]
  rfl

/-- A one-bounded L-series is continuous on the Halasz vertical line. -/
theorem continuous_LSeries_halaszPoint_of_oneBounded
    {a : ℕ → ℂ} (hbound : ∀ n, 0 < n → ‖a n‖ ≤ 1)
    {Y : ℕ} (hY : 1 < Y) :
    Continuous (fun t : ℝ ↦
      LSeries a (Erdos67.MRHalaszEuler.halaszPoint Y t)) := by
  let sigma := Erdos67.EulerResidue.taoExponent Y
  have hsigma : 1 < sigma :=
    Erdos67.EulerResidue.one_lt_taoExponent hY
  have hmid : 1 < (sigma + 1) / 2 := by linarith
  have hsum : LSeriesSummable a (((sigma + 1) / 2 : ℝ) : ℂ) :=
    LSeriesSummable_of_bounded_of_one_lt_re
      (fun n hn ↦ hbound n (Nat.pos_of_ne_zero hn)) (by simpa using hmid)
  have habs : LSeries.abscissaOfAbsConv a < (sigma : ℝ) := by
    calc
      LSeries.abscissaOfAbsConv a ≤ (((sigma + 1) / 2 : ℝ) : EReal) := by
        simpa using hsum.abscissaOfAbsConv_le
      _ < (sigma : ℝ) := by
        exact_mod_cast (by linarith : (sigma + 1) / 2 < sigma)
  have hline : Continuous
      (fun t : ℝ ↦ Erdos67.MRHalaszEuler.halaszPoint Y t) := by
    unfold Erdos67.MRHalaszEuler.halaszPoint
    fun_prop
  exact (LSeries_differentiableOn a).continuousOn.comp_continuous
    hline (fun t ↦ by
      simpa [sigma, Erdos67.MRHalaszEuler.halaszPoint_re] using habs)

/-- The smoothing-core energy of a positive finite band is controlled by
the existing finite mean-value/missing-prime-block estimate.  The factor
`(2π)⁻¹` is the exact Jacobian of `u = -t0 + 2π xi`; the enlarged symmetric
frequency range is `|t0| + 2πR`. -/
theorem finiteHalaszPositiveBandCoreEnergy_le_missingBlock
    (I : ℕ × ℕ) (Q : ℕ → Prop) [DecidablePred Q]
    (hdisj : ∀ p ∈ primesInBlock I, ¬ Q p)
    (f : ℕ → ℂ) (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    {N : ℕ} (hN : 0 < N)
    {sigma : ℝ} (hsigma : 1 ≤ sigma)
    {R : ℝ} (hR : 0 ≤ R) (t0 : ℝ) :
    finiteHalaszPositiveBandCoreEnergy f Q N sigma t0 R ≤
      (2 * Real.pi)⁻¹ *
        ((2 * (|t0| + 2 * Real.pi * R) + 2 * Real.pi * (N : ℝ)) *
          (((1 : ℝ)⁻¹) ^ 2 *
            ((missingPrimeBlockSet I N).card : ℝ))) := by
  let T : ℝ := |t0| + 2 * Real.pi * R
  let P : ℝ → ℝ := fun t ↦
    Complex.normSq (smoothedPrimeBandPolynomial f Q sigma 1 N t)
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have hpi : 0 < 2 * Real.pi := by positivity
  have hPcont : Continuous P := by
    unfold P smoothedPrimeBandPolynomial logarithmicDirichletPolynomial
      logarithmicPhase
    fun_prop
  have hPnonneg (t : ℝ) : 0 ≤ P t := Complex.normSq_nonneg _
  have hpoly (xi : ℝ) :
      ‖LSeries (positivePrefixTruncate (primeBandCoefficient f Q) N)
          ((sigma : ℂ) + Complex.I *
            ((t0 - 2 * Real.pi * xi : ℝ) : ℂ))‖ ^ (2 : ℝ) =
        P (2 * Real.pi * xi + (-t0)) := by
    rw [LSeries_positivePrefixTruncate_eq_logarithmic]
    rw [Real.rpow_two, ← Complex.normSq_eq_norm_sq]
    unfold P smoothedPrimeBandPolynomial smoothedPrimeBandCoefficient
    congr 2
    ring
  have hleft : -T ≤ 2 * Real.pi * (-R) + (-t0) := by
    dsimp [T]
    have ht : -|t0| ≤ -t0 := neg_abs_le_neg t0
    nlinarith
  have hright : 2 * Real.pi * R + (-t0) ≤ T := by
    dsimp [T]
    have ht : -t0 ≤ |t0| := neg_le_abs t0
    linarith
  have hmid :
      (∫ t in (2 * Real.pi * (-R) + (-t0))..
          (2 * Real.pi * R + (-t0)), P t) ≤
        ∫ t in -T..T, P t := by
    apply intervalIntegral.integral_mono_interval hleft (by nlinarith) hright
    · filter_upwards with t
      exact hPnonneg t
    · exact hPcont.intervalIntegrable _ _
  have hmean :=
    intervalIntegral_normSq_smoothedPrimeBandPolynomial_le_missingBlock
      I Q hdisj f hbound hsigma (L := 1) (U := N) (by norm_num)
      (by omega) hT
  have hmeanP :
      (∫ t in -T..T, P t) ≤
        (2 * T + 2 * Real.pi * (N : ℝ)) *
          (((1 : ℝ)⁻¹) ^ 2 *
            ((missingPrimeBlockSet I N).card : ℝ)) := by
    simpa only [P, Nat.cast_one] using hmean
  have hscaled :
      finiteHalaszPositiveBandCoreEnergy f Q N sigma t0 R =
        (2 * Real.pi)⁻¹ *
          ∫ t in (2 * Real.pi * (-R) + (-t0))..
            (2 * Real.pi * R + (-t0)), P t := by
    unfold finiteHalaszPositiveBandCoreEnergy
    rw [show (∫ xi in Set.Icc (-R) R,
        ‖LSeries (positivePrefixTruncate (primeBandCoefficient f Q) N)
            ((sigma : ℂ) + Complex.I *
              ((t0 - 2 * Real.pi * xi : ℝ) : ℂ))‖ ^ (2 : ℝ)) =
          ∫ xi in -R..R, P (2 * Real.pi * xi + (-t0)) by
      rw [intervalIntegral.integral_of_le (by linarith),
        setIntegral_congr_set MeasureTheory.Ioc_ae_eq_Icc]
      apply integral_congr_ae
      filter_upwards with xi
      exact hpoly xi]
    rw [intervalIntegral.integral_comp_mul_add P hpi.ne' (-t0)]
    rfl
  rw [hscaled]
  calc
    (2 * Real.pi)⁻¹ *
          (∫ t in (2 * Real.pi * (-R) + -t0)..
            (2 * Real.pi * R + -t0), P t) ≤
        (2 * Real.pi)⁻¹ * (∫ t in -T..T, P t) :=
      mul_le_mul_of_nonneg_left hmid (inv_nonneg.mpr hpi.le)
    _ ≤ (2 * Real.pi)⁻¹ *
        ((2 * T + 2 * Real.pi * (N : ℝ)) *
          (((1 : ℝ)⁻¹) ^ 2 *
            ((missingPrimeBlockSet I N).card : ℝ))) :=
      mul_le_mul_of_nonneg_left hmeanP (inv_nonneg.mpr hpi.le)
    _ = _ := by rfl

/-- Fully explicit beta-sieve/Mertens discharge of the finite core energy.
The first summand is the logarithmic density ratio and the second is the
finite sieve-level remainder. -/
theorem exists_finiteHalaszPositiveBandCoreEnergy_mertens_beta_bound :
    ∃ Cβ : ℝ, 1 ≤ Cβ ∧
      ∀ (I : ℕ × ℕ) (Q : ℕ → Prop) [DecidablePred Q]
        (f : ℕ → ℂ) (N S : ℕ) {sigma R t0 : ℝ},
        (∀ p ∈ primesInBlock I, ¬ Q p) →
        (∀ n, 0 < n → ‖f n‖ ≤ 1) →
        0 < N → 1 ≤ sigma → 0 ≤ R →
        3 ≤ I.1 → I.1 ≤ I.2 → 101 ≤ S →
        Real.log Cβ ≤ 2 * (S - 100 : ℕ) / 99 →
        finiteHalaszPositiveBandCoreEnergy f Q N sigma t0 R ≤
          (2 * Real.pi)⁻¹ *
            ((2 * (|t0| + 2 * Real.pi * R) + 2 * Real.pi * (N : ℝ)) *
              ((N : ℝ) *
                  ((1 + (4 * Cβ / 3) * (1 / 4 : ℝ) ^ (S - 100)) *
                    (Real.exp (2 * Erdos67.PrimeEstimates.mertensBound) *
                      (Real.log ((I.1 - 1 : ℕ) : ℝ) /
                        Real.log (I.2 : ℝ)))) +
                ((I.2 ^ S : ℕ) : ℝ) ^ 2)) := by
  obtain ⟨Cβ, hCβ, hbeta⟩ :=
    exists_card_missingPrimeBlockSet_mertens_beta_bound
  refine ⟨Cβ, hCβ, ?_⟩
  intro I Q _ f N S sigma R t0 hdisj hbound hN hsigma hR
    hlo hLU hS hlog
  have henergy := finiteHalaszPositiveBandCoreEnergy_le_missingBlock
    I Q hdisj f hbound hN hsigma hR t0
  have hcard := hbeta N I.1 I.2 S hlo hLU hS hlog
  have htime :
      0 ≤ 2 * (|t0| + 2 * Real.pi * R) + 2 * Real.pi * (N : ℝ) := by
    positivity
  have hpi : 0 ≤ (2 * Real.pi)⁻¹ := by positivity
  calc
    finiteHalaszPositiveBandCoreEnergy f Q N sigma t0 R ≤
        (2 * Real.pi)⁻¹ *
          ((2 * (|t0| + 2 * Real.pi * R) + 2 * Real.pi * (N : ℝ)) *
            (((1 : ℝ)⁻¹) ^ 2 *
              ((missingPrimeBlockSet I N).card : ℝ))) := henergy
    _ = (2 * Real.pi)⁻¹ *
          ((2 * (|t0| + 2 * Real.pi * R) + 2 * Real.pi * (N : ℝ)) *
            ((missingPrimeBlockSet I N).card : ℝ)) := by norm_num
    _ ≤ (2 * Real.pi)⁻¹ *
          ((2 * (|t0| + 2 * Real.pi * R) + 2 * Real.pi * (N : ℝ)) *
            ((N : ℝ) *
                ((1 + (4 * Cβ / 3) * (1 / 4 : ℝ) ^ (S - 100)) *
                  (Real.exp (2 * Erdos67.PrimeEstimates.mertensBound) *
                    (Real.log ((I.1 - 1 : ℕ) : ℝ) /
                      Real.log (I.2 : ℝ)))) +
              ((I.2 ^ S : ℕ) : ℝ) ^ 2)) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hcard htime) hpi

/-- The fixed-band Euler factor appearing in the direct finite-Halasz
core estimate. -/
def fixedFiniteHalaszEulerBound (C : ℝ) (A X Y : ℕ) : ℝ :=
  Real.exp
    (Real.log (riemannZeta (Erdos67.EulerResidue.taoExponent Y : ℂ)).re -
      Real.exp (-1) *
        ((A : ℝ) -
          2 * (Real.log ((X : ℝ) / (Y + 1 : ℝ)) + C) /
            Real.log (Y + 1 : ℝ)) +
      3 * Erdos67.EulerQuantitative.primeQuadraticConstant)

/-- The exact compactly windowed finite typical coefficient sum. -/
def finiteHalaszTypicalWindowSum
    (f : ℕ → ℂ) (P₁ P₂ : ℕ → Prop)
    [DecidablePred P₁] [DecidablePred P₂]
    (N : ℕ) (sigma : ℝ)
    (delta logA logB : ℝ) (hdelta : 0 < delta) (t0 : ℝ) : ℂ :=
  ∑ n ∈ Finset.Ioc 1 N,
    LSeries.term (finiteHalaszTypicalCoefficient f P₁ P₂) (sigma : ℂ) n *
      logarithmicPhase n (-t0) *
      logTrapezoidWindow delta logA logB hdelta (Real.log n)

/-- Common missing-block upper bound for either positive band core. -/
def finiteHalaszMissingBlockCoreBound
    (I : ℕ × ℕ) (N : ℕ) (t0 R : ℝ) : ℝ :=
  (2 * Real.pi)⁻¹ *
    ((2 * (|t0| + 2 * Real.pi * R) + 2 * Real.pi * (N : ℝ)) *
      (((1 : ℝ)⁻¹) ^ 2 * ((missingPrimeBlockSet I N).card : ℝ)))

theorem finiteHalaszMissingBlockCoreBound_nonneg
    (I : ℕ × ℕ) (N : ℕ) (t0 : ℝ) {R : ℝ} (hR : 0 ≤ R) :
    0 ≤ finiteHalaszMissingBlockCoreBound I N t0 R := by
  unfold finiteHalaszMissingBlockCoreBound
  positivity

/-- Direct unrestricted finite-Halasz endpoint for the compact window.
This is the form applied before the typical-set restriction is restored in
`L²`: the coefficient sum is finite, the near-frequency contribution has
the propagated nonpretentious Euler decay, and the only far-frequency term
is the exact Schwartz tail. -/
theorem exists_uniform_norm_finiteHalaszFullWindowSum_le_core_tail :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {f : ℕ → ℂ} {A X Y N : ℕ},
        IsMultiplicativeOnPositiveNat f →
        (∀ n, 0 < n → ‖f n‖ ≤ 1) →
        2 ≤ Y → Y < X → 0 < N →
        MRArchimedeanNonpretentious f A X →
        ∀ {R t0 : ℝ}, 0 ≤ R →
        |t0| + 2 * Real.pi * R ≤ X →
        ∀ (delta logA logB : ℝ) (hdelta : 0 < delta),
        logB ≤ Real.log N →
        ‖∑ n ∈ Finset.Ioc 0 N,
            LSeries.term f (Erdos67.EulerResidue.taoExponent Y : ℂ) n *
              logarithmicPhase n (-t0) *
              logTrapezoidWindow delta logA logB hdelta (Real.log n)‖ ≤
          fixedFiniteHalaszEulerBound C A X Y *
              (∫ xi in Set.Icc (-R) R,
                ‖logTrapezoidKernel delta logA logB hdelta xi‖) +
            finiteHalaszLSeriesAbsoluteMass f
                (Erdos67.EulerResidue.taoExponent Y) *
              logTrapezoidKernelTailMass delta logA logB hdelta R := by
  obtain ⟨C, hC, hEuler⟩ :=
    Erdos67.MRMultiplicativeEuler.exists_uniform_norm_LSeries_lower_halaszPoint_le
  refine ⟨C, hC, ?_⟩
  intro f A X Y N hmul hbound hY hYX hN hnonpret R t0 hR hfreq
    delta logA logB hdelta hlogB
  let sigma : ℝ := Erdos67.EulerResidue.taoExponent Y
  let F : ℝ → ℂ := fun xi ↦
    LSeries f ((sigma : ℂ) + Complex.I *
      ((t0 - 2 * Real.pi * xi : ℝ) : ℂ))
  let K : ℝ → ℂ := logTrapezoidKernel delta logA logB hdelta
  let M : ℝ := fixedFiniteHalaszEulerBound C A X Y
  let Z : ℝ := finiteHalaszLSeriesAbsoluteMass f sigma
  have hsigma : 1 < sigma := by
    dsimp [sigma]
    exact Erdos67.EulerResidue.one_lt_taoExponent (by omega)
  have hsum : LSeriesSummable f (sigma : ℂ) :=
    LSeriesSummable_of_bounded_of_one_lt_re
      (fun n hn ↦ hbound n (Nat.pos_of_ne_zero hn)) (by simpa using hsigma)
  have hF : Continuous F := by
    have hc := continuous_LSeries_halaszPoint_of_oneBounded hbound
      (show 1 < Y by omega)
    have hu : Continuous (fun xi : ℝ ↦ t0 - 2 * Real.pi * xi) := by fun_prop
    have hcomp := hc.comp hu
    simpa only [Function.comp_def, F, sigma,
      Erdos67.MRHalaszEuler.halaszPoint, mul_comm] using hcomp
  have hKc : Continuous K := by
    exact (FourierTransform.fourier
      (logTrapezoidSchwartz delta logA logB hdelta)).continuous
  have hKi : Integrable K :=
    integrable_logTrapezoidKernel delta logA logB hdelta
  have hM : 0 ≤ M := by dsimp [M, fixedFiniteHalaszEulerBound]; positivity
  have hZ : 0 ≤ Z := finiteHalaszLSeriesAbsoluteMass_nonneg _ _
  have hFGlobal (xi : ℝ) : ‖F xi‖ ≤ Z :=
    norm_LSeries_le_finiteHalaszLSeriesAbsoluteMass f hsum
      (t0 - 2 * Real.pi * xi)
  have hFCore (xi : ℝ) (hxi : |xi| ≤ R) : ‖F xi‖ ≤ M := by
    have hpi : 0 ≤ 2 * Real.pi := by positivity
    have hmulabs : |2 * Real.pi * xi| ≤ 2 * Real.pi * R := by
      rw [abs_mul, abs_of_nonneg hpi]
      exact mul_le_mul_of_nonneg_left hxi hpi
    have hu : |t0 - 2 * Real.pi * xi| ≤ X := by
      calc
        |t0 - 2 * Real.pi * xi| ≤ |t0| + |2 * Real.pi * xi| := abs_sub _ _
        _ ≤ |t0| + 2 * Real.pi * R := add_le_add le_rfl hmulabs
        _ ≤ X := hfreq
    have he := hEuler hmul hbound hY hYX hnonpret
      (t0 - 2 * Real.pi * xi) hu
    simpa only [F, sigma, M, fixedFiniteHalaszEulerBound,
      Erdos67.MRHalaszEuler.halaszPoint, mul_comm] using he
  have hcore := norm_integral_mul_le_core_tail F K hR hM hZ hF hKc hKi
    hFGlobal hFCore
  rw [← integral_LSeries_mul_logTrapezoidKernel_eq_finitePrefix
    f hsum hN delta logA logB hdelta hlogB t0]
  simpa only [F, K, M, Z, sigma, logTrapezoidKernelTailMass] using hcore

/-- Direct finite, fixed-band Halasz core--tail estimate.  The left side is
the exact compactly smoothed finite typical sum.  The first term on the
right has the propagated nonpretentious exponential, multiplied by the two
actual finite square energies.  The second is the exact Schwartz-kernel
tail multiplied by three explicit absolute masses.

There is no complete-L-series-to-finite-tail comparison: compact support
made the coefficient side finite before norms were taken. -/
theorem exists_uniform_norm_finiteHalaszTypicalWindowSum_le_core_tail :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {f : ℕ → ℂ} {A X Y N : ℕ}
        (P₁ P₂ : ℕ → Prop) [DecidablePred P₁] [DecidablePred P₂],
        IsMultiplicativeOnPositiveNat f →
        (∀ n, 0 < n → ‖f n‖ ≤ 1) →
        2 ≤ Y → Y < X → 0 < N →
        (∀ p, p.Prime → p ≤ Y → P₁ p) →
        MRArchimedeanNonpretentious f A X →
        ∀ {R t0 : ℝ}, 0 ≤ R →
        |t0| + 2 * Real.pi * R ≤ X →
        ∀ (delta logA logB : ℝ) (hdelta : 0 < delta),
        logB ≤ Real.log N →
        ‖∑ n ∈ Finset.Ioc 1 N,
            LSeries.term (finiteHalaszTypicalCoefficient f P₁ P₂)
                (Erdos67.EulerResidue.taoExponent Y : ℂ) n *
              logarithmicPhase n (-t0) *
              logTrapezoidWindow delta logA logB hdelta
                (Real.log n)‖ ≤
          fixedFiniteHalaszEulerBound C A X Y *
              logTrapezoidKernelUniformBound delta logA logB hdelta *
              (finiteHalaszPositiveBandCoreEnergy f
                (fun p ↦ ¬ P₁ p ∧ P₂ p) N
                (Erdos67.EulerResidue.taoExponent Y) t0 R) ^
                  ((1 : ℝ) / 2) *
              (finiteHalaszPositiveBandCoreEnergy f
                (fun p ↦ ¬ P₁ p ∧ ¬ P₂ p) N
                (Erdos67.EulerResidue.taoExponent Y) t0 R) ^
                  ((1 : ℝ) / 2) +
            finiteHalaszLSeriesAbsoluteMass
                (primeBandCoefficient f P₁)
                (Erdos67.EulerResidue.taoExponent Y) *
              finiteHalaszPositiveBandMass f
                (fun p ↦ ¬ P₁ p ∧ P₂ p) N
                (Erdos67.EulerResidue.taoExponent Y) *
              finiteHalaszPositiveBandMass f
                (fun p ↦ ¬ P₁ p ∧ ¬ P₂ p) N
                (Erdos67.EulerResidue.taoExponent Y) *
              logTrapezoidKernelTailMass delta logA logB
                hdelta R := by
  obtain ⟨C, hC, hEuler⟩ :=
    exists_uniform_norm_fixedBand_LSeries_lower_halaszPoint_le
  refine ⟨C, hC, ?_⟩
  intro f A X Y N P₁ P₂ _ _ hmul hbound hY hYX hN hP hnonpret
    R t0 hR hfreq delta logA logB hdelta hlogB
  let sigma : ℝ := Erdos67.EulerResidue.taoExponent Y
  let sAt : ℝ → ℂ := fun xi ↦
    (sigma : ℂ) + Complex.I * ((t0 - 2 * Real.pi * xi : ℝ) : ℂ)
  let F₁ : ℝ → ℂ := fun xi ↦ LSeries (primeBandCoefficient f P₁) (sAt xi)
  let F₂ : ℝ → ℂ := fun xi ↦
    LSeries
      (positivePrefixTruncate
        (primeBandCoefficient f (fun p ↦ ¬ P₁ p ∧ P₂ p)) N) (sAt xi)
  let F₃ : ℝ → ℂ := fun xi ↦
    LSeries
      (positivePrefixTruncate
        (primeBandCoefficient f (fun p ↦ ¬ P₁ p ∧ ¬ P₂ p)) N) (sAt xi)
  let K : ℝ → ℂ := logTrapezoidKernel delta logA logB hdelta
  let M : ℝ := fixedFiniteHalaszEulerBound C A X Y
  let Q : ℝ := logTrapezoidKernelUniformBound delta logA logB hdelta
  let Z : ℝ := finiteHalaszLSeriesAbsoluteMass
    (primeBandCoefficient f P₁) sigma
  let G : ℝ := finiteHalaszPositiveBandMass f
    (fun p ↦ ¬ P₁ p ∧ P₂ p) N sigma
  let H : ℝ := finiteHalaszPositiveBandMass f
    (fun p ↦ ¬ P₁ p ∧ ¬ P₂ p) N sigma
  have hsigma : 1 < sigma := by
    dsimp [sigma]
    exact Erdos67.EulerResidue.one_lt_taoExponent (by omega)
  have hsum₁ : LSeriesSummable (primeBandCoefficient f P₁) (sigma : ℂ) :=
    primeBandCoefficient_LSeriesSummable hbound P₁ (by simpa using hsigma)
  have hM : 0 ≤ M := by dsimp [M, fixedFiniteHalaszEulerBound]; positivity
  have hQ : 0 ≤ Q := by
    exact logTrapezoidKernelUniformBound_nonneg delta logA logB hdelta
  have hZ : 0 ≤ Z := finiteHalaszLSeriesAbsoluteMass_nonneg _ _
  have hG : 0 ≤ G := finiteHalaszPositiveBandMass_nonneg _ _ _ _
  have hH : 0 ≤ H := finiteHalaszPositiveBandMass_nonneg _ _ _ _
  have hF₁ : Continuous F₁ := by
    have hc := continuous_LSeries_primeBand_halaszPoint hbound P₁
      (show 1 < Y by omega)
    have hu : Continuous (fun xi : ℝ ↦ t0 - 2 * Real.pi * xi) := by fun_prop
    have hcomp := hc.comp hu
    simpa only [Function.comp_def, F₁, sAt, sigma,
      Erdos67.MRHalaszEuler.halaszPoint, mul_comm] using hcomp
  have hF₂ : Continuous F₂ := by
    rw [show F₂ = fun xi : ℝ ↦
        logarithmicDirichletPolynomial (Finset.Ioc 1 N)
          (fun n ↦ primeBandCoefficient f (fun p ↦ ¬ P₁ p ∧ P₂ p) n *
            Complex.ofReal ((n : ℝ) ^ (-sigma)))
          (-(t0 - 2 * Real.pi * xi)) by
      funext xi
      exact LSeries_positivePrefixTruncate_eq_logarithmic _ N sigma _]
    unfold logarithmicDirichletPolynomial logarithmicPhase
    fun_prop
  have hF₃ : Continuous F₃ := by
    rw [show F₃ = fun xi : ℝ ↦
        logarithmicDirichletPolynomial (Finset.Ioc 1 N)
          (fun n ↦ primeBandCoefficient f (fun p ↦ ¬ P₁ p ∧ ¬ P₂ p) n *
            Complex.ofReal ((n : ℝ) ^ (-sigma)))
          (-(t0 - 2 * Real.pi * xi)) by
      funext xi
      exact LSeries_positivePrefixTruncate_eq_logarithmic _ N sigma _]
    unfold logarithmicDirichletPolynomial logarithmicPhase
    fun_prop
  have hKc : Continuous K := by
    exact (FourierTransform.fourier
      (logTrapezoidSchwartz delta logA logB hdelta)).continuous
  have hKi : Integrable K :=
    integrable_logTrapezoidKernel delta logA logB hdelta
  have hF₁Global (xi : ℝ) : ‖F₁ xi‖ ≤ Z := by
    exact norm_LSeries_le_finiteHalaszLSeriesAbsoluteMass
      (a := primeBandCoefficient f P₁) hsum₁ (t0 - 2 * Real.pi * xi)
  have hF₂Global (xi : ℝ) : ‖F₂ xi‖ ≤ G := by
    exact norm_LSeries_positivePrefixTruncate_le_bandMass f
      (fun p ↦ ¬ P₁ p ∧ P₂ p) N sigma (t0 - 2 * Real.pi * xi)
  have hF₃Global (xi : ℝ) : ‖F₃ xi‖ ≤ H := by
    exact norm_LSeries_positivePrefixTruncate_le_bandMass f
      (fun p ↦ ¬ P₁ p ∧ ¬ P₂ p) N sigma (t0 - 2 * Real.pi * xi)
  have hF₁Core (xi : ℝ) (hxi : |xi| ≤ R) : ‖F₁ xi‖ ≤ M := by
    have hpi : 0 ≤ 2 * Real.pi := by positivity
    have hmulabs : |2 * Real.pi * xi| ≤ 2 * Real.pi * R := by
      rw [abs_mul, abs_of_nonneg hpi]
      exact mul_le_mul_of_nonneg_left hxi hpi
    have hu : |t0 - 2 * Real.pi * xi| ≤ X := by
      calc
        |t0 - 2 * Real.pi * xi| ≤ |t0| + |2 * Real.pi * xi| := abs_sub _ _
        _ ≤ |t0| + 2 * Real.pi * R := add_le_add le_rfl hmulabs
        _ ≤ X := hfreq
    have he := hEuler P₁ hmul hbound hY hYX hP hnonpret
      (t0 - 2 * Real.pi * xi) hu
    simpa only [F₁, sAt, sigma, M, fixedFiniteHalaszEulerBound,
      Erdos67.MRHalaszEuler.halaszPoint, mul_comm] using he
  have hKCore (xi : ℝ) (_hxi : |xi| ≤ R) : ‖K xi‖ ≤ Q :=
    norm_logTrapezoidKernel_le_uniformBound delta logA logB hdelta xi
  have hcore := norm_integral_four_mul_le_core_tail
    F₁ F₂ F₃ K hR hM hQ hZ hG hH hF₁ hF₂ hF₃ hKc hKi
      hF₁Global hF₂Global hF₃Global hF₁Core hKCore
  rw [← integral_finiteHalaszProduct_mul_logTrapezoidKernel
    hmul hbound P₁ P₂ hN hsigma delta logA logB hdelta hlogB t0]
  simpa only [F₁, F₂, F₃, K, M, Q, Z, G, H, sigma, sAt,
    finiteHalaszPositiveBandCoreEnergy, logTrapezoidKernelTailMass,
    mul_assoc] using hcore

/-- Missing-block specialization of the direct finite-Halasz endpoint.
Both positive complementary bands avoid the same prime block, so their
two half-energy factors collapse to one explicit missing-block energy. -/
theorem exists_uniform_norm_finiteHalaszTypicalWindowSum_le_missingBlock :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (I : ℕ × ℕ) {f : ℕ → ℂ} {A X Y N : ℕ}
        (P₁ P₂ : ℕ → Prop) [DecidablePred P₁] [DecidablePred P₂],
        IsMultiplicativeOnPositiveNat f →
        (∀ n, 0 < n → ‖f n‖ ≤ 1) →
        2 ≤ Y → Y < X → 0 < N →
        (∀ p, p.Prime → p ≤ Y → P₁ p) →
        (∀ p ∈ primesInBlock I, P₁ p) →
        MRArchimedeanNonpretentious f A X →
        ∀ {R t0 : ℝ}, 0 ≤ R →
        |t0| + 2 * Real.pi * R ≤ X →
        ∀ (delta logA logB : ℝ) (hdelta : 0 < delta),
        logB ≤ Real.log N →
        ‖finiteHalaszTypicalWindowSum f P₁ P₂ N
            (Erdos67.EulerResidue.taoExponent Y)
            delta logA logB hdelta t0‖ ≤
          fixedFiniteHalaszEulerBound C A X Y *
              logTrapezoidKernelUniformBound delta logA logB hdelta *
              finiteHalaszMissingBlockCoreBound I N t0 R +
            finiteHalaszLSeriesAbsoluteMass
                (primeBandCoefficient f P₁)
                (Erdos67.EulerResidue.taoExponent Y) *
              finiteHalaszPositiveBandMass f
                (fun p ↦ ¬ P₁ p ∧ P₂ p) N
                (Erdos67.EulerResidue.taoExponent Y) *
              finiteHalaszPositiveBandMass f
                (fun p ↦ ¬ P₁ p ∧ ¬ P₂ p) N
                (Erdos67.EulerResidue.taoExponent Y) *
              logTrapezoidKernelTailMass delta logA logB hdelta R := by
  obtain ⟨C, hC, hbase⟩ :=
    exists_uniform_norm_finiteHalaszTypicalWindowSum_le_core_tail
  refine ⟨C, hC, ?_⟩
  intro I f A X Y N P₁ P₂ _ _ hmul hbound hY hYX hN hP hblock
    hnonpret R t0 hR hfreq delta logA logB hdelta hlogB
  have h := hbase P₁ P₂ hmul hbound hY hYX hN hP hnonpret hR hfreq
    delta logA logB hdelta hlogB
  let E₂ : ℝ := finiteHalaszPositiveBandCoreEnergy f
    (fun p ↦ ¬ P₁ p ∧ P₂ p) N
    (Erdos67.EulerResidue.taoExponent Y) t0 R
  let E₃ : ℝ := finiteHalaszPositiveBandCoreEnergy f
    (fun p ↦ ¬ P₁ p ∧ ¬ P₂ p) N
    (Erdos67.EulerResidue.taoExponent Y) t0 R
  let E : ℝ := finiteHalaszMissingBlockCoreBound I N t0 R
  have hdisj₂ : ∀ p ∈ primesInBlock I, ¬ (¬ P₁ p ∧ P₂ p) := by
    intro p hp hq
    exact hq.1 (hblock p hp)
  have hdisj₃ : ∀ p ∈ primesInBlock I, ¬ (¬ P₁ p ∧ ¬ P₂ p) := by
    intro p hp hq
    exact hq.1 (hblock p hp)
  have hE₂ : E₂ ≤ E := by
    exact finiteHalaszPositiveBandCoreEnergy_le_missingBlock
      I (fun p ↦ ¬ P₁ p ∧ P₂ p) hdisj₂ f hbound hN
        (Erdos67.EulerResidue.one_lt_taoExponent (show 1 < Y by omega)).le
        hR t0
  have hE₃ : E₃ ≤ E := by
    exact finiteHalaszPositiveBandCoreEnergy_le_missingBlock
      I (fun p ↦ ¬ P₁ p ∧ ¬ P₂ p) hdisj₃ f hbound hN
        (Erdos67.EulerResidue.one_lt_taoExponent (show 1 < Y by omega)).le
        hR t0
  have hE₂0 : 0 ≤ E₂ := finiteHalaszPositiveBandCoreEnergy_nonneg _ _ _ _ _ _
  have hE₃0 : 0 ≤ E₃ := finiteHalaszPositiveBandCoreEnergy_nonneg _ _ _ _ _ _
  have hE0 : 0 ≤ E := finiteHalaszMissingBlockCoreBound_nonneg I N t0 hR
  have hhalf :
      E₂ ^ ((1 : ℝ) / 2) * E₃ ^ ((1 : ℝ) / 2) ≤ E :=
    rpow_half_mul_rpow_half_le hE₂0 hE₃0 hE0 hE₂ hE₃
  have hM : 0 ≤ fixedFiniteHalaszEulerBound C A X Y := by
    unfold fixedFiniteHalaszEulerBound
    positivity
  have hQ : 0 ≤ logTrapezoidKernelUniformBound delta logA logB hdelta :=
    logTrapezoidKernelUniformBound_nonneg delta logA logB hdelta
  unfold finiteHalaszTypicalWindowSum
  refine h.trans ?_
  apply add_le_add
  · calc
      fixedFiniteHalaszEulerBound C A X Y *
            logTrapezoidKernelUniformBound delta logA logB hdelta *
          finiteHalaszPositiveBandCoreEnergy f
              (fun p ↦ ¬ P₁ p ∧ P₂ p) N
              (Erdos67.EulerResidue.taoExponent Y) t0 R ^ ((1 : ℝ) / 2) *
          finiteHalaszPositiveBandCoreEnergy f
              (fun p ↦ ¬ P₁ p ∧ ¬ P₂ p) N
              (Erdos67.EulerResidue.taoExponent Y) t0 R ^ ((1 : ℝ) / 2) =
        fixedFiniteHalaszEulerBound C A X Y *
            logTrapezoidKernelUniformBound delta logA logB hdelta *
          (E₂ ^ ((1 : ℝ) / 2) * E₃ ^ ((1 : ℝ) / 2)) := by
            dsimp [E₂, E₃]
            ring
      _ ≤ fixedFiniteHalaszEulerBound C A X Y *
            logTrapezoidKernelUniformBound delta logA logB hdelta * E :=
        mul_le_mul_of_nonneg_left hhalf (mul_nonneg hM hQ)
      _ = fixedFiniteHalaszEulerBound C A X Y *
            logTrapezoidKernelUniformBound delta logA logB hdelta *
          finiteHalaszMissingBlockCoreBound I N t0 R := by rfl
  · exact le_rfl

end

end Erdos67.MRHalaszBands
