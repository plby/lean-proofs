import ErdosProblems.Erdos67b.MRFiniteHalaszCoreTail

/-!
# A direct finite dyadic Halasz endpoint on `Re s = 1`

The Euler-product estimate is naturally available on the absolutely
convergent line `Re s = sigma > 1`.  This file uses the exponentially
tilted compact logarithmic window to move the *finite coefficient side*
back to `Re s = 1`.  The passage is an exact Fourier identity: there is no
comparison of a complete L-series with a finite tail.
-/

open scoped BigOperators LSeries.notation
open Complex Finset MeasureTheory Set

namespace Erdos67b.MRHalaszBands

noncomputable section

open Erdos67b.MRFiniteHalaszSmoothing

/-- Countable Fourier smoothing with an exponential Mellin tilt.  Absolute
convergence justifies interchanging the complete L-series and the integral;
compact support will subsequently make its coefficient side finite. -/
theorem integral_LSeries_mul_tiltedLogTrapezoidKernel
    (a : ℕ → ℂ) (sigma rho : ℝ)
    (hsum : LSeriesSummable a (sigma : ℂ))
    (delta A B : ℝ) (hdelta : 0 < delta) (t0 : ℝ) :
    (∫ xi : ℝ,
        LSeries a
            ((sigma : ℂ) + Complex.I * ((t0 - 2 * Real.pi * xi : ℝ) : ℂ)) *
          tiltedLogTrapezoidKernel rho delta A B hdelta xi) =
      ∑' n : ℕ,
        LSeries.term a (sigma : ℂ) n * logarithmicPhase n (-t0) *
          ((Real.exp (rho * Real.log n) : ℂ) *
            logTrapezoidWindow delta A B hdelta (Real.log n)) := by
  let s0 : ℂ := (sigma : ℂ)
  let sAt : ℝ → ℂ := fun xi ↦
    (sigma : ℂ) + Complex.I * ((t0 - 2 * Real.pi * xi : ℝ) : ℂ)
  let K : ℝ → ℂ := tiltedLogTrapezoidKernel rho delta A B hdelta
  let F : ℕ → ℝ → ℂ := fun n xi ↦ LSeries.term a (sAt xi) n * K xi
  have hK : Integrable K :=
    integrable_tiltedLogTrapezoidKernel rho delta A B hdelta
  have hnormTerm (n : ℕ) (xi : ℝ) :
      ‖LSeries.term a (sAt xi) n‖ = ‖LSeries.term a s0 n‖ := by
    simp only [LSeries.norm_term_eq]
    congr 2
    simp [sAt, s0]
  have htermPhase (n : ℕ) (xi : ℝ) :
      LSeries.term a (sAt xi) n =
        LSeries.term a s0 n *
          logarithmicPhase n (-t0 + 2 * Real.pi * xi) := by
    by_cases hn : n = 0
    · subst n
      simp
    · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
      dsimp [sAt, s0]
      rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn,
        div_eq_mul_inv, div_eq_mul_inv, ← Complex.cpow_neg,
        ← Complex.cpow_neg]
      rw [← ofReal_rpow_mul_logarithmicPhase_neg_eq_cpow_neg
        hnpos sigma (t0 - 2 * Real.pi * xi)]
      have hreal : (n : ℂ) ^ (-((sigma : ℝ) : ℂ)) =
          Complex.ofReal ((n : ℝ) ^ (-sigma)) := by
        simpa using
          (Complex.ofReal_cpow (show (0 : ℝ) ≤ n by positivity) (-sigma)).symm
      rw [hreal]
      have hphase :
          logarithmicPhase n (-(t0 - 2 * Real.pi * xi)) =
            logarithmicPhase n (-t0 + 2 * Real.pi * xi) := by
        unfold logarithmicPhase
        congr 1
        push_cast
        ring
      rw [hphase]
      ring
  have hFint : ∀ n : ℕ, Integrable (F n) := by
    intro n
    have hmajor : Integrable (fun xi : ℝ ↦ ‖LSeries.term a s0 n‖ * ‖K xi‖) :=
      hK.norm.const_mul _
    refine hmajor.mono' ?_ ?_
    · have htermMeas : AEStronglyMeasurable (fun xi : ℝ ↦
          LSeries.term a (sAt xi) n) := by
        rw [show (fun xi : ℝ ↦ LSeries.term a (sAt xi) n) =
              fun xi ↦ LSeries.term a s0 n *
                logarithmicPhase n (-t0 + 2 * Real.pi * xi) by
          funext xi
          exact htermPhase n xi]
        have hc : Continuous (fun xi : ℝ ↦
            LSeries.term a s0 n *
              logarithmicPhase n (-t0 + 2 * Real.pi * xi)) := by
          unfold logarithmicPhase
          fun_prop
        exact hc.aestronglyMeasurable
      exact htermMeas.mul hK.aestronglyMeasurable
    · filter_upwards with xi
      rw [norm_mul, hnormTerm]
  have hintNorm (n : ℕ) :
      (∫ xi : ℝ, ‖F n xi‖) =
        ‖LSeries.term a s0 n‖ *
          tiltedLogTrapezoidKernelMass rho delta A B hdelta := by
    simp_rw [F, norm_mul, hnormTerm]
    rw [integral_const_mul]
    rfl
  have hsumInt : Summable (fun n : ℕ ↦ ∫ xi : ℝ, ‖F n xi‖) := by
    rw [show (fun n : ℕ ↦ ∫ xi : ℝ, ‖F n xi‖) =
        fun n ↦ ‖LSeries.term a s0 n‖ *
          tiltedLogTrapezoidKernelMass rho delta A B hdelta by
      funext n
      exact hintNorm n]
    exact Summable.mul_right _ hsum.norm
  have hinterchange :
      (∑' n : ℕ, ∫ xi : ℝ, F n xi) =
        ∫ xi : ℝ, ∑' n : ℕ, F n xi :=
    MeasureTheory.integral_tsum_of_summable_integral_norm hFint hsumInt
  have hterm (n : ℕ) :
      (∫ xi : ℝ, F n xi) =
        LSeries.term a s0 n * logarithmicPhase n (-t0) *
          ((Real.exp (rho * Real.log n) : ℂ) *
            logTrapezoidWindow delta A B hdelta (Real.log n)) := by
    by_cases hn : n = 0
    · subst n
      simp [F, sAt, s0]
    · have hsingle :=
        integral_logarithmicDirichletPolynomial_mul_tiltedKernel
          ({n} : Finset ℕ) (fun _ ↦ LSeries.term a s0 n)
          rho delta A B hdelta t0
      simpa only [F, K, htermPhase, logarithmicDirichletPolynomial,
        Finset.sum_singleton] using hsingle
  calc
    (∫ xi : ℝ,
        LSeries a
            ((sigma : ℂ) + Complex.I * ((t0 - 2 * Real.pi * xi : ℝ) : ℂ)) *
          tiltedLogTrapezoidKernel rho delta A B hdelta xi) =
      ∫ xi : ℝ, ∑' n : ℕ, F n xi := by
        apply integral_congr_ae
        filter_upwards with xi
        rw [show (∑' n : ℕ, F n xi) = LSeries a (sAt xi) * K xi by
          simp only [F, LSeries, tsum_mul_right]]
    _ = ∑' n : ℕ, ∫ xi : ℝ, F n xi := hinterchange.symm
    _ = ∑' n : ℕ,
        LSeries.term a (sigma : ℂ) n * logarithmicPhase n (-t0) *
          ((Real.exp (rho * Real.log n) : ℂ) *
            logTrapezoidWindow delta A B hdelta (Real.log n)) := by
      apply tsum_congr
      intro n
      simpa only [s0] using hterm n

/-- Exact cancellation of the shifted L-series coefficient against the
Mellin tilt.  This is the algebraic step which recovers `f(n)/n`. -/
theorem LSeries_term_mul_exp_shift_eq_div
    (f : ℕ → ℂ) {n : ℕ} (hn : 0 < n) (sigma : ℝ) :
    LSeries.term f (sigma : ℂ) n *
        (Real.exp ((sigma - 1) * Real.log n) : ℂ) =
      f n / (n : ℂ) := by
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have htilt :
      (Real.exp ((sigma - 1) * Real.log n) : ℂ) =
        (n : ℂ) ^ ((sigma - 1 : ℝ) : ℂ) := by
    rw [← Complex.ofReal_natCast]
    rw [← Complex.ofReal_cpow hnR.le]
    rw [Real.rpow_def_of_pos hnR]
    congr 2
    ring
  rw [LSeries.term_of_ne_zero hn.ne', htilt]
  rw [show ((sigma - 1 : ℝ) : ℂ) = (sigma : ℂ) - 1 by push_cast; ring]
  rw [Complex.cpow_sub _ _ hnC, Complex.cpow_one]
  have hpow : (n : ℂ) ^ (sigma : ℂ) ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl hnC)
  field_simp

/-- The tilted countable identity with compact support already used to
truncate the coefficient side and with the real-part shift cancelled. -/
theorem integral_LSeries_mul_tiltedKernel_eq_harmonicFinitePrefix
    (f : ℕ → ℂ) {sigma : ℝ}
    (hsum : LSeriesSummable f (sigma : ℂ))
    {N : ℕ} (hN : 0 < N)
    (delta A B : ℝ) (hdelta : 0 < delta)
    (hB : B ≤ Real.log N) (t0 : ℝ) :
    (∫ xi : ℝ,
        LSeries f
            ((sigma : ℂ) + Complex.I * ((t0 - 2 * Real.pi * xi : ℝ) : ℂ)) *
          tiltedLogTrapezoidKernel (sigma - 1) delta A B hdelta xi) =
      ∑ n ∈ Finset.Ioc 0 N,
        (f n / (n : ℂ)) * logarithmicPhase n (-t0) *
          logTrapezoidWindow delta A B hdelta (Real.log n) := by
  classical
  rw [integral_LSeries_mul_tiltedLogTrapezoidKernel
    f sigma (sigma - 1) hsum delta A B hdelta t0]
  rw [tsum_eq_sum (s := Finset.Ioc 0 N)]
  · apply Finset.sum_congr rfl
    intro n hn
    have hnpos : 0 < n := (Finset.mem_Ioc.mp hn).1
    rw [show
      LSeries.term f (sigma : ℂ) n * logarithmicPhase n (-t0) *
          ((Real.exp ((sigma - 1) * Real.log n) : ℂ) *
            logTrapezoidWindow delta A B hdelta (Real.log n)) =
        (LSeries.term f (sigma : ℂ) n *
            (Real.exp ((sigma - 1) * Real.log n) : ℂ)) *
          logarithmicPhase n (-t0) *
            logTrapezoidWindow delta A B hdelta (Real.log n) by ring]
    rw [LSeries_term_mul_exp_shift_eq_div f hnpos sigma]
  · intro n hn
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
      mul_zero, mul_zero]

/-- Exact compact tilted smoothing of the one-complete/two-finite hybrid.
On the coefficient side the Halasz-line shift has already cancelled, so
the result is the harmonic (`Re s = 1`) typical coefficient. -/
theorem integral_finiteHalaszProduct_mul_tiltedKernel_harmonic
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    (P₁ P₂ : ℕ → Prop) [DecidablePred P₁] [DecidablePred P₂]
    {N : ℕ} (hN : 0 < N) {sigma : ℝ} (hsigma : 1 < sigma)
    (delta A B : ℝ) (hdelta : 0 < delta) (hB : B ≤ Real.log N)
    (t0 : ℝ) :
    (∫ xi : ℝ,
        (LSeries (primeBandCoefficient f P₁)
              ((sigma : ℂ) + Complex.I *
                ((t0 - 2 * Real.pi * xi : ℝ) : ℂ)) *
          (LSeries
              (positivePrefixTruncate
                (primeBandCoefficient f (fun p ↦ ¬ P₁ p ∧ P₂ p)) N)
              ((sigma : ℂ) + Complex.I *
                ((t0 - 2 * Real.pi * xi : ℝ) : ℂ)) *
            LSeries
              (positivePrefixTruncate
                (primeBandCoefficient f (fun p ↦ ¬ P₁ p ∧ ¬ P₂ p)) N)
              ((sigma : ℂ) + Complex.I *
                ((t0 - 2 * Real.pi * xi : ℝ) : ℂ)))) *
          tiltedLogTrapezoidKernel (sigma - 1) delta A B hdelta xi) =
      ∑ n ∈ Finset.Ioc 1 N,
        (finiteHalaszTypicalCoefficient f P₁ P₂ n / (n : ℂ)) *
          logarithmicPhase n (-t0) *
          logTrapezoidWindow delta A B hdelta (Real.log n) := by
  classical
  have hsum : LSeriesSummable (finiteHalaszHybridCoefficient f P₁ P₂ N)
      (sigma : ℂ) :=
    finiteHalaszHybridCoefficient_LSeriesSummable hbound P₁ P₂ N
      (by simpa using hsigma)
  rw [← show
      (∫ xi : ℝ,
        LSeries (finiteHalaszHybridCoefficient f P₁ P₂ N)
            ((sigma : ℂ) + Complex.I *
              ((t0 - 2 * Real.pi * xi : ℝ) : ℂ)) *
          tiltedLogTrapezoidKernel (sigma - 1) delta A B hdelta xi) =
        ∑ n ∈ Finset.Ioc 1 N,
          (finiteHalaszTypicalCoefficient f P₁ P₂ n / (n : ℂ)) *
            logarithmicPhase n (-t0) *
            logTrapezoidWindow delta A B hdelta (Real.log n) by
    rw [integral_LSeries_mul_tiltedLogTrapezoidKernel
      (finiteHalaszHybridCoefficient f P₁ P₂ N) sigma (sigma - 1)
      hsum delta A B hdelta t0]
    rw [tsum_eq_sum (s := Finset.Ioc 1 N)]
    · apply Finset.sum_congr rfl
      intro n hn
      have hnI := Finset.mem_Ioc.mp hn
      have hnpos : 0 < n := by omega
      rw [show
        LSeries.term (finiteHalaszHybridCoefficient f P₁ P₂ N)
              (sigma : ℂ) n * logarithmicPhase n (-t0) *
            ((Real.exp ((sigma - 1) * Real.log n) : ℂ) *
              logTrapezoidWindow delta A B hdelta (Real.log n)) =
          (LSeries.term (finiteHalaszHybridCoefficient f P₁ P₂ N)
                (sigma : ℂ) n *
              (Real.exp ((sigma - 1) * Real.log n) : ℂ)) *
            logarithmicPhase n (-t0) *
              logTrapezoidWindow delta A B hdelta (Real.log n) by ring]
      rw [LSeries_term_mul_exp_shift_eq_div _ hnpos sigma,
        finiteHalaszHybridCoefficient_apply hmul P₁ P₂ hnpos hnI.2]
    · intro n hn
      by_cases hn0 : n = 0
      · subst n
        simp
      by_cases hn1 : n ≤ 1
      · have hnEq : n = 1 := by omega
        subst n
        rw [LSeries.term_of_ne_zero (by norm_num),
          finiteHalaszHybridCoefficient_apply hmul P₁ P₂ (by norm_num)
            (by omega)]
        simp [finiteHalaszTypicalCoefficient, HasPrimeFactor]
      · have hNn : N < n := by
          by_contra hnot
          exact hn (Finset.mem_Ioc.mpr ⟨Nat.lt_of_not_ge hn1,
            Nat.le_of_not_gt hnot⟩)
        have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
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
          mul_zero, mul_zero]]
  apply integral_congr_ae
  filter_upwards with xi
  have hsxi :
      1 < (((sigma : ℂ) + Complex.I *
        ((t0 - 2 * Real.pi * xi : ℝ) : ℂ))).re := by
    simpa using hsigma
  rw [show
      LSeries (finiteHalaszHybridCoefficient f P₁ P₂ N)
          ((sigma : ℂ) + Complex.I *
            ((t0 - 2 * Real.pi * xi : ℝ) : ℂ)) =
        LSeries (primeBandCoefficient f P₁)
            ((sigma : ℂ) + Complex.I *
              ((t0 - 2 * Real.pi * xi : ℝ) : ℂ)) *
          (LSeries
              (positivePrefixTruncate
                (primeBandCoefficient f (fun p ↦ ¬ P₁ p ∧ P₂ p)) N)
              ((sigma : ℂ) + Complex.I *
                ((t0 - 2 * Real.pi * xi : ℝ) : ℂ)) *
            LSeries
              (positivePrefixTruncate
                (primeBandCoefficient f (fun p ↦ ¬ P₁ p ∧ ¬ P₂ p)) N)
              ((sigma : ℂ) + Complex.I *
                ((t0 - 2 * Real.pi * xi : ℝ) : ℂ))) by
      unfold finiteHalaszHybridCoefficient
      exact LSeries_convolution_oneFull_twoPositiveTruncated
        hbound P₁ P₂ N hsxi]

/-- Exact `L¹` tail of the tilted kernel outside a real symmetric core. -/
def tiltedFiniteHalaszKernelTailMass
    (rho delta A B : ℝ) (hdelta : 0 < delta) (R : ℝ) : ℝ :=
  ∫ xi in (Set.Icc (-R) R)ᶜ,
    ‖tiltedLogTrapezoidKernel rho delta A B hdelta xi‖

/-- Frequency-uniform bound for the explicit tilted Fourier kernel. -/
def tiltedFiniteHalaszKernelUniformBound
    (rho delta A B : ℝ) (hdelta : 0 < delta) : ℝ :=
  ‖(tiltedLogTrapezoidSchwartz rho delta A B hdelta).toLp 1‖

theorem tiltedFiniteHalaszKernelUniformBound_nonneg
    (rho delta A B : ℝ) (hdelta : 0 < delta) :
    0 ≤ tiltedFiniteHalaszKernelUniformBound rho delta A B hdelta :=
  norm_nonneg _

theorem norm_tiltedLogTrapezoidKernel_le_uniformBound
    (rho delta A B : ℝ) (hdelta : 0 < delta) (xi : ℝ) :
    ‖tiltedLogTrapezoidKernel rho delta A B hdelta xi‖ ≤
      tiltedFiniteHalaszKernelUniformBound rho delta A B hdelta := by
  exact SchwartzMap.norm_fourier_apply_le_toLp_one
    (tiltedLogTrapezoidSchwartz rho delta A B hdelta) xi

/-- Three-band direct finite Halasz endpoint on `Re s = 1`.  This is the
quantitatively useful form: the zeta-sized complete Euler factor is paired
with the square roots of two actual finite complementary-band energies. -/
theorem exists_uniform_norm_finiteHalaszTypicalHarmonicWindowSum_le_core_tail :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {f : ℕ → ℂ} {A0 X Y N : ℕ}
        (P₁ P₂ : ℕ → Prop) [DecidablePred P₁] [DecidablePred P₂],
        IsMultiplicativeOnPositiveNat f →
        (∀ n, 0 < n → ‖f n‖ ≤ 1) →
        2 ≤ Y → Y < X → 0 < N →
        (∀ p, p.Prime → p ≤ Y → P₁ p) →
        MRArchimedeanNonpretentious f A0 X →
        ∀ {R t0 : ℝ}, 0 ≤ R →
        |t0| + 2 * Real.pi * R ≤ X →
        ∀ (delta logA logB : ℝ) (hdelta : 0 < delta),
        logB ≤ Real.log N →
        ‖∑ n ∈ Finset.Ioc 1 N,
            (finiteHalaszTypicalCoefficient f P₁ P₂ n / (n : ℂ)) *
              logarithmicPhase n (-t0) *
              logTrapezoidWindow delta logA logB hdelta (Real.log n)‖ ≤
          fixedFiniteHalaszEulerBound C A0 X Y *
              tiltedFiniteHalaszKernelUniformBound
                (Erdos67b.EulerResidue.taoExponent Y - 1)
                delta logA logB hdelta *
              (finiteHalaszPositiveBandCoreEnergy f
                (fun p ↦ ¬ P₁ p ∧ P₂ p) N
                (Erdos67b.EulerResidue.taoExponent Y) t0 R) ^
                  ((1 : ℝ) / 2) *
              (finiteHalaszPositiveBandCoreEnergy f
                (fun p ↦ ¬ P₁ p ∧ ¬ P₂ p) N
                (Erdos67b.EulerResidue.taoExponent Y) t0 R) ^
                  ((1 : ℝ) / 2) +
            finiteHalaszLSeriesAbsoluteMass
                (primeBandCoefficient f P₁)
                (Erdos67b.EulerResidue.taoExponent Y) *
              finiteHalaszPositiveBandMass f
                (fun p ↦ ¬ P₁ p ∧ P₂ p) N
                (Erdos67b.EulerResidue.taoExponent Y) *
              finiteHalaszPositiveBandMass f
                (fun p ↦ ¬ P₁ p ∧ ¬ P₂ p) N
                (Erdos67b.EulerResidue.taoExponent Y) *
              tiltedFiniteHalaszKernelTailMass
                (Erdos67b.EulerResidue.taoExponent Y - 1)
                delta logA logB hdelta R := by
  obtain ⟨C, hC, hEuler⟩ :=
    exists_uniform_norm_fixedBand_LSeries_lower_halaszPoint_le
  refine ⟨C, hC, ?_⟩
  intro f A0 X Y N P₁ P₂ _ _ hmul hbound hY hYX hN hP hnonpret
    R t0 hR hfreq delta logA logB hdelta hlogB
  let sigma : ℝ := Erdos67b.EulerResidue.taoExponent Y
  let rho : ℝ := sigma - 1
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
  let K : ℝ → ℂ :=
    tiltedLogTrapezoidKernel rho delta logA logB hdelta
  let M : ℝ := fixedFiniteHalaszEulerBound C A0 X Y
  let Q : ℝ := tiltedFiniteHalaszKernelUniformBound
    rho delta logA logB hdelta
  let Z : ℝ := finiteHalaszLSeriesAbsoluteMass
    (primeBandCoefficient f P₁) sigma
  let G : ℝ := finiteHalaszPositiveBandMass f
    (fun p ↦ ¬ P₁ p ∧ P₂ p) N sigma
  let H : ℝ := finiteHalaszPositiveBandMass f
    (fun p ↦ ¬ P₁ p ∧ ¬ P₂ p) N sigma
  have hsigma : 1 < sigma := by
    dsimp [sigma]
    exact Erdos67b.EulerResidue.one_lt_taoExponent (by omega)
  have hsum₁ : LSeriesSummable (primeBandCoefficient f P₁) (sigma : ℂ) :=
    primeBandCoefficient_LSeriesSummable hbound P₁ (by simpa using hsigma)
  have hM : 0 ≤ M := by dsimp [M, fixedFiniteHalaszEulerBound]; positivity
  have hQ : 0 ≤ Q := by
    exact tiltedFiniteHalaszKernelUniformBound_nonneg rho delta logA logB hdelta
  have hZ : 0 ≤ Z := finiteHalaszLSeriesAbsoluteMass_nonneg _ _
  have hG : 0 ≤ G := finiteHalaszPositiveBandMass_nonneg _ _ _ _
  have hH : 0 ≤ H := finiteHalaszPositiveBandMass_nonneg _ _ _ _
  have hF₁ : Continuous F₁ := by
    have hc := continuous_LSeries_primeBand_halaszPoint hbound P₁
      (show 1 < Y by omega)
    have hu : Continuous (fun xi : ℝ ↦ t0 - 2 * Real.pi * xi) := by fun_prop
    have hcomp := hc.comp hu
    simpa only [Function.comp_def, F₁, sAt, sigma,
      Erdos67b.MRHalaszEuler.halaszPoint, mul_comm] using hcomp
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
      (tiltedLogTrapezoidSchwartz rho delta logA logB hdelta)).continuous
  have hKi : Integrable K :=
    integrable_tiltedLogTrapezoidKernel rho delta logA logB hdelta
  have hF₁Global (xi : ℝ) : ‖F₁ xi‖ ≤ Z :=
    norm_LSeries_le_finiteHalaszLSeriesAbsoluteMass
      (a := primeBandCoefficient f P₁) hsum₁ (t0 - 2 * Real.pi * xi)
  have hF₂Global (xi : ℝ) : ‖F₂ xi‖ ≤ G :=
    norm_LSeries_positivePrefixTruncate_le_bandMass f
      (fun p ↦ ¬ P₁ p ∧ P₂ p) N sigma (t0 - 2 * Real.pi * xi)
  have hF₃Global (xi : ℝ) : ‖F₃ xi‖ ≤ H :=
    norm_LSeries_positivePrefixTruncate_le_bandMass f
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
      Erdos67b.MRHalaszEuler.halaszPoint, mul_comm] using he
  have hKCore (xi : ℝ) (_hxi : |xi| ≤ R) : ‖K xi‖ ≤ Q :=
    norm_tiltedLogTrapezoidKernel_le_uniformBound
      rho delta logA logB hdelta xi
  have hcore := norm_integral_four_mul_le_core_tail
    F₁ F₂ F₃ K hR hM hQ hZ hG hH hF₁ hF₂ hF₃ hKc hKi
      hF₁Global hF₂Global hF₃Global hF₁Core hKCore
  rw [← integral_finiteHalaszProduct_mul_tiltedKernel_harmonic
    hmul hbound P₁ P₂ hN hsigma delta logA logB hdelta hlogB t0]
  simpa only [F₁, F₂, F₃, K, M, Q, Z, G, H, sigma, rho, sAt,
    finiteHalaszPositiveBandCoreEnergy, tiltedFiniteHalaszKernelTailMass,
    mul_assoc] using hcore

/-- Missing-prime-block specialization of the three-band harmonic endpoint.
Both complementary factors avoid the selected block, so the product of
their half-energies is bounded by one explicit finite missing-block term. -/
theorem exists_uniform_norm_finiteHalaszTypicalHarmonicWindowSum_le_missingBlock :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (Iblock : ℕ × ℕ) {f : ℕ → ℂ} {A0 X Y N : ℕ}
        (P₁ P₂ : ℕ → Prop) [DecidablePred P₁] [DecidablePred P₂],
        IsMultiplicativeOnPositiveNat f →
        (∀ n, 0 < n → ‖f n‖ ≤ 1) →
        2 ≤ Y → Y < X → 0 < N →
        (∀ p, p.Prime → p ≤ Y → P₁ p) →
        (∀ p ∈ primesInBlock Iblock, P₁ p) →
        MRArchimedeanNonpretentious f A0 X →
        ∀ {R t0 : ℝ}, 0 ≤ R →
        |t0| + 2 * Real.pi * R ≤ X →
        ∀ (delta logA logB : ℝ) (hdelta : 0 < delta),
        logB ≤ Real.log N →
        ‖∑ n ∈ Finset.Ioc 1 N,
            (finiteHalaszTypicalCoefficient f P₁ P₂ n / (n : ℂ)) *
              logarithmicPhase n (-t0) *
              logTrapezoidWindow delta logA logB hdelta (Real.log n)‖ ≤
          fixedFiniteHalaszEulerBound C A0 X Y *
              tiltedFiniteHalaszKernelUniformBound
                (Erdos67b.EulerResidue.taoExponent Y - 1)
                delta logA logB hdelta *
              finiteHalaszMissingBlockCoreBound Iblock N t0 R +
            finiteHalaszLSeriesAbsoluteMass
                (primeBandCoefficient f P₁)
                (Erdos67b.EulerResidue.taoExponent Y) *
              finiteHalaszPositiveBandMass f
                (fun p ↦ ¬ P₁ p ∧ P₂ p) N
                (Erdos67b.EulerResidue.taoExponent Y) *
              finiteHalaszPositiveBandMass f
                (fun p ↦ ¬ P₁ p ∧ ¬ P₂ p) N
                (Erdos67b.EulerResidue.taoExponent Y) *
              tiltedFiniteHalaszKernelTailMass
                (Erdos67b.EulerResidue.taoExponent Y - 1)
                delta logA logB hdelta R := by
  obtain ⟨C, hC, hbase⟩ :=
    exists_uniform_norm_finiteHalaszTypicalHarmonicWindowSum_le_core_tail
  refine ⟨C, hC, ?_⟩
  intro Iblock f A0 X Y N P₁ P₂ _ _ hmul hbound hY hYX hN hP hblock
    hnonpret R t0 hR hfreq delta logA logB hdelta hlogB
  have h := hbase P₁ P₂ hmul hbound hY hYX hN hP hnonpret hR hfreq
    delta logA logB hdelta hlogB
  let E₂ : ℝ := finiteHalaszPositiveBandCoreEnergy f
    (fun p ↦ ¬ P₁ p ∧ P₂ p) N
    (Erdos67b.EulerResidue.taoExponent Y) t0 R
  let E₃ : ℝ := finiteHalaszPositiveBandCoreEnergy f
    (fun p ↦ ¬ P₁ p ∧ ¬ P₂ p) N
    (Erdos67b.EulerResidue.taoExponent Y) t0 R
  let E : ℝ := finiteHalaszMissingBlockCoreBound Iblock N t0 R
  have hdisj₂ : ∀ p ∈ primesInBlock Iblock, ¬ (¬ P₁ p ∧ P₂ p) := by
    intro p hp hq
    exact hq.1 (hblock p hp)
  have hdisj₃ : ∀ p ∈ primesInBlock Iblock, ¬ (¬ P₁ p ∧ ¬ P₂ p) := by
    intro p hp hq
    exact hq.1 (hblock p hp)
  have hE₂ : E₂ ≤ E :=
    finiteHalaszPositiveBandCoreEnergy_le_missingBlock
      Iblock (fun p ↦ ¬ P₁ p ∧ P₂ p) hdisj₂ f hbound hN
        (Erdos67b.EulerResidue.one_lt_taoExponent (show 1 < Y by omega)).le
        hR t0
  have hE₃ : E₃ ≤ E :=
    finiteHalaszPositiveBandCoreEnergy_le_missingBlock
      Iblock (fun p ↦ ¬ P₁ p ∧ ¬ P₂ p) hdisj₃ f hbound hN
        (Erdos67b.EulerResidue.one_lt_taoExponent (show 1 < Y by omega)).le
        hR t0
  have hE₂0 : 0 ≤ E₂ := finiteHalaszPositiveBandCoreEnergy_nonneg _ _ _ _ _ _
  have hE₃0 : 0 ≤ E₃ := finiteHalaszPositiveBandCoreEnergy_nonneg _ _ _ _ _ _
  have hE0 : 0 ≤ E := finiteHalaszMissingBlockCoreBound_nonneg Iblock N t0 hR
  have hhalf : E₂ ^ ((1 : ℝ) / 2) * E₃ ^ ((1 : ℝ) / 2) ≤ E :=
    rpow_half_mul_rpow_half_le hE₂0 hE₃0 hE0 hE₂ hE₃
  have hM : 0 ≤ fixedFiniteHalaszEulerBound C A0 X Y := by
    unfold fixedFiniteHalaszEulerBound
    positivity
  have hQ : 0 ≤ tiltedFiniteHalaszKernelUniformBound
      (Erdos67b.EulerResidue.taoExponent Y - 1)
      delta logA logB hdelta :=
    tiltedFiniteHalaszKernelUniformBound_nonneg _ _ _ _ _
  refine h.trans ?_
  apply add_le_add
  · calc
      fixedFiniteHalaszEulerBound C A0 X Y *
            tiltedFiniteHalaszKernelUniformBound
              (Erdos67b.EulerResidue.taoExponent Y - 1)
              delta logA logB hdelta *
          finiteHalaszPositiveBandCoreEnergy f
              (fun p ↦ ¬ P₁ p ∧ P₂ p) N
              (Erdos67b.EulerResidue.taoExponent Y) t0 R ^ ((1 : ℝ) / 2) *
          finiteHalaszPositiveBandCoreEnergy f
              (fun p ↦ ¬ P₁ p ∧ ¬ P₂ p) N
              (Erdos67b.EulerResidue.taoExponent Y) t0 R ^ ((1 : ℝ) / 2) =
        fixedFiniteHalaszEulerBound C A0 X Y *
            tiltedFiniteHalaszKernelUniformBound
              (Erdos67b.EulerResidue.taoExponent Y - 1)
              delta logA logB hdelta *
          (E₂ ^ ((1 : ℝ) / 2) * E₃ ^ ((1 : ℝ) / 2)) := by
            dsimp [E₂, E₃]
            ring
      _ ≤ fixedFiniteHalaszEulerBound C A0 X Y *
            tiltedFiniteHalaszKernelUniformBound
              (Erdos67b.EulerResidue.taoExponent Y - 1)
              delta logA logB hdelta * E :=
        mul_le_mul_of_nonneg_left hhalf (mul_nonneg hM hQ)
      _ = fixedFiniteHalaszEulerBound C A0 X Y *
            tiltedFiniteHalaszKernelUniformBound
              (Erdos67b.EulerResidue.taoExponent Y - 1)
              delta logA logB hdelta *
          finiteHalaszMissingBlockCoreBound Iblock N t0 R := by rfl
  · exact le_rfl

/-- Two-block version used when the two complementary prime bands omit
different prime packets.  The two explicit missing-block energies remain
separate, as required by the source three-band argument. -/
theorem exists_uniform_norm_finiteHalaszTypicalHarmonicWindowSum_le_twoMissingBlocks :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (I₂ I₃ : ℕ × ℕ) {f : ℕ → ℂ} {A0 X Y N : ℕ}
        (P₁ P₂ : ℕ → Prop) [DecidablePred P₁] [DecidablePred P₂],
        IsMultiplicativeOnPositiveNat f →
        (∀ n, 0 < n → ‖f n‖ ≤ 1) →
        2 ≤ Y → Y < X → 0 < N →
        (∀ p, p.Prime → p ≤ Y → P₁ p) →
        (∀ p ∈ primesInBlock I₂, ¬ (¬ P₁ p ∧ P₂ p)) →
        (∀ p ∈ primesInBlock I₃, ¬ (¬ P₁ p ∧ ¬ P₂ p)) →
        MRArchimedeanNonpretentious f A0 X →
        ∀ {R t0 : ℝ}, 0 ≤ R →
        |t0| + 2 * Real.pi * R ≤ X →
        ∀ (delta logA logB : ℝ) (hdelta : 0 < delta),
        logB ≤ Real.log N →
        ‖∑ n ∈ Finset.Ioc 1 N,
            (finiteHalaszTypicalCoefficient f P₁ P₂ n / (n : ℂ)) *
              logarithmicPhase n (-t0) *
              logTrapezoidWindow delta logA logB hdelta (Real.log n)‖ ≤
          fixedFiniteHalaszEulerBound C A0 X Y *
              tiltedFiniteHalaszKernelUniformBound
                (Erdos67b.EulerResidue.taoExponent Y - 1)
                delta logA logB hdelta *
              (finiteHalaszMissingBlockCoreBound I₂ N t0 R) ^ ((1 : ℝ) / 2) *
              (finiteHalaszMissingBlockCoreBound I₃ N t0 R) ^ ((1 : ℝ) / 2) +
            finiteHalaszLSeriesAbsoluteMass
                (primeBandCoefficient f P₁)
                (Erdos67b.EulerResidue.taoExponent Y) *
              finiteHalaszPositiveBandMass f
                (fun p ↦ ¬ P₁ p ∧ P₂ p) N
                (Erdos67b.EulerResidue.taoExponent Y) *
              finiteHalaszPositiveBandMass f
                (fun p ↦ ¬ P₁ p ∧ ¬ P₂ p) N
                (Erdos67b.EulerResidue.taoExponent Y) *
              tiltedFiniteHalaszKernelTailMass
                (Erdos67b.EulerResidue.taoExponent Y - 1)
                delta logA logB hdelta R := by
  obtain ⟨C, hC, hbase⟩ :=
    exists_uniform_norm_finiteHalaszTypicalHarmonicWindowSum_le_core_tail
  refine ⟨C, hC, ?_⟩
  intro I₂ I₃ f A0 X Y N P₁ P₂ _ _ hmul hbound hY hYX hN hP
    hdisj₂ hdisj₃ hnonpret R t0 hR hfreq delta logA logB hdelta hlogB
  have h := hbase P₁ P₂ hmul hbound hY hYX hN hP hnonpret hR hfreq
    delta logA logB hdelta hlogB
  have hE₂ := finiteHalaszPositiveBandCoreEnergy_le_missingBlock
    I₂ (fun p ↦ ¬ P₁ p ∧ P₂ p) hdisj₂ f hbound hN
      (Erdos67b.EulerResidue.one_lt_taoExponent (show 1 < Y by omega)).le
      hR t0
  have hE₃ := finiteHalaszPositiveBandCoreEnergy_le_missingBlock
    I₃ (fun p ↦ ¬ P₁ p ∧ ¬ P₂ p) hdisj₃ f hbound hN
      (Erdos67b.EulerResidue.one_lt_taoExponent (show 1 < Y by omega)).le
      hR t0
  have hE₂' : finiteHalaszPositiveBandCoreEnergy f
      (fun p ↦ ¬ P₁ p ∧ P₂ p) N
      (Erdos67b.EulerResidue.taoExponent Y) t0 R ≤
        finiteHalaszMissingBlockCoreBound I₂ N t0 R := by
    simpa [finiteHalaszMissingBlockCoreBound] using hE₂
  have hE₃' : finiteHalaszPositiveBandCoreEnergy f
      (fun p ↦ ¬ P₁ p ∧ ¬ P₂ p) N
      (Erdos67b.EulerResidue.taoExponent Y) t0 R ≤
        finiteHalaszMissingBlockCoreBound I₃ N t0 R := by
    simpa [finiteHalaszMissingBlockCoreBound] using hE₃
  have hE₂0 := finiteHalaszPositiveBandCoreEnergy_nonneg f
    (fun p ↦ ¬ P₁ p ∧ P₂ p) N
      (Erdos67b.EulerResidue.taoExponent Y) t0 R
  have hE₃0 := finiteHalaszPositiveBandCoreEnergy_nonneg f
    (fun p ↦ ¬ P₁ p ∧ ¬ P₂ p) N
      (Erdos67b.EulerResidue.taoExponent Y) t0 R
  have hB₂0 := finiteHalaszMissingBlockCoreBound_nonneg I₂ N t0 hR
  have hB₃0 := finiteHalaszMissingBlockCoreBound_nonneg I₃ N t0 hR
  have hsqrt₂ := Real.rpow_le_rpow hE₂0 hE₂' (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hsqrt₃ := Real.rpow_le_rpow hE₃0 hE₃' (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hM : 0 ≤ fixedFiniteHalaszEulerBound C A0 X Y := by
    unfold fixedFiniteHalaszEulerBound
    positivity
  have hQ : 0 ≤ tiltedFiniteHalaszKernelUniformBound
      (Erdos67b.EulerResidue.taoExponent Y - 1) delta logA logB hdelta :=
    tiltedFiniteHalaszKernelUniformBound_nonneg _ _ _ _ _
  refine h.trans ?_
  apply add_le_add
  · gcongr
  · exact le_rfl

/-- Direct finite Halasz endpoint for a compactly smoothed harmonic
polynomial.  The main term has the nonpretentious exponential saving on a
bounded frequency core; the sole far-frequency error is an exact Schwartz
tail. -/
theorem exists_uniform_norm_finiteHalaszHarmonicWindowSum_le_core_tail :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {f : ℕ → ℂ} {A0 X Y N : ℕ},
        IsMultiplicativeOnPositiveNat f →
        (∀ n, 0 < n → ‖f n‖ ≤ 1) →
        2 ≤ Y → Y < X → 0 < N →
        MRArchimedeanNonpretentious f A0 X →
        ∀ {R t0 : ℝ}, 0 ≤ R →
        |t0| + 2 * Real.pi * R ≤ X →
        ∀ (delta logA logB : ℝ) (hdelta : 0 < delta),
        logB ≤ Real.log N →
        ‖∑ n ∈ Finset.Ioc 0 N,
            (f n / (n : ℂ)) * logarithmicPhase n (-t0) *
              logTrapezoidWindow delta logA logB hdelta (Real.log n)‖ ≤
          fixedFiniteHalaszEulerBound C A0 X Y *
              (∫ xi in Set.Icc (-R) R,
                ‖tiltedLogTrapezoidKernel
                  (Erdos67b.EulerResidue.taoExponent Y - 1)
                  delta logA logB hdelta xi‖) +
            finiteHalaszLSeriesAbsoluteMass f
                (Erdos67b.EulerResidue.taoExponent Y) *
              tiltedFiniteHalaszKernelTailMass
                (Erdos67b.EulerResidue.taoExponent Y - 1)
                delta logA logB hdelta R := by
  obtain ⟨C, hC, hEuler⟩ :=
    Erdos67b.MRMultiplicativeEuler.exists_uniform_norm_LSeries_lower_halaszPoint_le
  refine ⟨C, hC, ?_⟩
  intro f A0 X Y N hmul hbound hY hYX hN hnonpret R t0 hR hfreq
    delta logA logB hdelta hlogB
  let sigma : ℝ := Erdos67b.EulerResidue.taoExponent Y
  let rho : ℝ := sigma - 1
  let F : ℝ → ℂ := fun xi ↦
    LSeries f ((sigma : ℂ) + Complex.I *
      ((t0 - 2 * Real.pi * xi : ℝ) : ℂ))
  let K : ℝ → ℂ :=
    tiltedLogTrapezoidKernel rho delta logA logB hdelta
  let M : ℝ := fixedFiniteHalaszEulerBound C A0 X Y
  let Z : ℝ := finiteHalaszLSeriesAbsoluteMass f sigma
  have hsigma : 1 < sigma := by
    dsimp [sigma]
    exact Erdos67b.EulerResidue.one_lt_taoExponent (by omega)
  have hsum : LSeriesSummable f (sigma : ℂ) :=
    LSeriesSummable_of_bounded_of_one_lt_re
      (fun n hn ↦ hbound n (Nat.pos_of_ne_zero hn)) (by simpa using hsigma)
  have hF : Continuous F := by
    have hc := continuous_LSeries_halaszPoint_of_oneBounded hbound
      (show 1 < Y by omega)
    have hu : Continuous (fun xi : ℝ ↦ t0 - 2 * Real.pi * xi) := by fun_prop
    have hcomp := hc.comp hu
    simpa only [Function.comp_def, F, sigma,
      Erdos67b.MRHalaszEuler.halaszPoint, mul_comm] using hcomp
  have hKc : Continuous K := by
    exact (FourierTransform.fourier
      (tiltedLogTrapezoidSchwartz rho delta logA logB hdelta)).continuous
  have hKi : Integrable K :=
    integrable_tiltedLogTrapezoidKernel rho delta logA logB hdelta
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
      Erdos67b.MRHalaszEuler.halaszPoint, mul_comm] using he
  have hcore := norm_integral_mul_le_core_tail F K hR hM hZ hF hKc hKi
    hFGlobal hFCore
  rw [← integral_LSeries_mul_tiltedKernel_eq_harmonicFinitePrefix
    f hsum hN delta logA logB hdelta hlogB t0]
  simpa only [F, K, M, Z, sigma, rho,
    tiltedFiniteHalaszKernelTailMass] using hcore

/-! ## Extraction of the sharp dyadic polynomial -/

/-- Harmonic mass of the two logarithmic boundary ramps in the dyadic
interval.  This is a finite, completely explicit error term. -/
def finiteHalaszDyadicBoundaryMass
    (f : ℕ → ℂ) (X : ℕ) (delta : ℝ) : ℝ :=
  ∑ n ∈ logSmoothingBoundary (Finset.Ioc X (2 * X)) delta
      (Real.log X) (Real.log (2 * X)),
    ‖f n / (n : ℂ)‖

theorem finiteHalaszDyadicBoundaryMass_nonneg
    (f : ℕ → ℂ) (X : ℕ) (delta : ℝ) :
    0 ≤ finiteHalaszDyadicBoundaryMass f X delta := by
  unfold finiteHalaszDyadicBoundaryMass
  positivity

/-- The boundary harmonic mass is at most its cardinality divided by the
dyadic scale.  Thus any `o(X)` boundary-cardinality estimate immediately
turns this term into `o(1)`. -/
theorem finiteHalaszDyadicBoundaryMass_le_card_div
    {f : ℕ → ℂ} {X : ℕ} (hX : 0 < X)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    (delta : ℝ) :
    finiteHalaszDyadicBoundaryMass f X delta ≤
      ((logSmoothingBoundary (Finset.Ioc X (2 * X)) delta
        (Real.log X) (Real.log (2 * X))).card : ℝ) / X := by
  classical
  have hXR : (0 : ℝ) < X := by exact_mod_cast hX
  unfold finiteHalaszDyadicBoundaryMass
  calc
    (∑ n ∈ logSmoothingBoundary (Finset.Ioc X (2 * X)) delta
        (Real.log X) (Real.log (2 * X)), ‖f n / (n : ℂ)‖) ≤
      ∑ _n ∈ logSmoothingBoundary (Finset.Ioc X (2 * X)) delta
        (Real.log X) (Real.log (2 * X)), (X : ℝ)⁻¹ := by
      apply Finset.sum_le_sum
      intro n hn
      have hnD : n ∈ Finset.Ioc X (2 * X) := by
        exact (Finset.mem_filter.mp hn).1
      have hnX : X < n := (Finset.mem_Ioc.mp hnD).1
      have hnpos : 0 < n := hX.trans hnX
      have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
      rw [norm_div, Complex.norm_natCast]
      calc
        ‖f n‖ / (n : ℝ) ≤ 1 / (n : ℝ) :=
          div_le_div_of_nonneg_right (hbound n hnpos) hnR.le
        _ = (n : ℝ)⁻¹ := one_div _
        _ ≤ (X : ℝ)⁻¹ := by
          apply inv_anti₀ hXR
          exact_mod_cast (Finset.mem_Ioc.mp hnD).1.le
    _ = ((logSmoothingBoundary (Finset.Ioc X (2 * X)) delta
      (Real.log X) (Real.log (2 * X))).card : ℝ) / X := by
      rw [Finset.sum_const, nsmul_eq_mul]
      rw [div_eq_mul_inv]

/-- The sharp unrestricted dyadic polynomial differs from its compact
logarithmic smoothing only on the two finite boundary ramps and at the
single lower endpoint `X`.  Under one-boundedness the endpoint costs at
most `1/X`. -/
theorem norm_dyadicVerticalDirichletPolynomial_le_harmonicWindow_add_boundary
    {f : ℕ → ℂ} {X : ℕ} (hX : 0 < X)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    (delta : ℝ) (hdelta : 0 < delta) (t0 : ℝ) :
    ‖dyadicVerticalDirichletPolynomial (Finset.Ioc X (2 * X)) f X t0‖ ≤
      ‖∑ n ∈ Finset.Ioc 0 (2 * X),
          (f n / (n : ℂ)) * logarithmicPhase n (-t0) *
            logTrapezoidWindow delta (Real.log X) (Real.log (2 * X))
              hdelta (Real.log n)‖ +
        (X : ℝ)⁻¹ + 2 * finiteHalaszDyadicBoundaryMass f X delta := by
  classical
  let D : Finset ℕ := Finset.Ioc X (2 * X)
  let I : Finset ℕ := logSmoothingInterior D delta
    (Real.log X) (Real.log (2 * X))
  let E : Finset ℕ := logSmoothingBoundary D delta
    (Real.log X) (Real.log (2 * X))
  let c : ℕ → ℂ := fun n ↦
    (f n / (n : ℂ)) * logarithmicPhase n (-t0)
  let W : ℕ → ℂ := fun n ↦
    logTrapezoidWindow delta (Real.log X) (Real.log (2 * X))
      hdelta (Real.log n)
  let P : ℂ := ∑ n ∈ Finset.Ioc 0 (2 * X), c n * W n
  let Q : ℂ := c X * W X
  let SI : ℂ := ∑ n ∈ I, c n
  let SE : ℂ := ∑ n ∈ E, c n * W n
  let SB : ℂ := ∑ n ∈ E, c n
  have hXR : (0 : ℝ) < X := by exact_mod_cast hX
  have htwoXR : (0 : ℝ) < 2 * X := by positivity
  have hlow : (∑ n ∈ Finset.Ioc 0 X, c n * W n) = Q := by
    apply Finset.sum_eq_single X
    · intro n hn hne
      have hnpos : 0 < n := (Finset.mem_Ioc.mp hn).1
      have hnlt : n < X := lt_of_le_of_ne (Finset.mem_Ioc.mp hn).2 hne
      have hloglt : Real.log (n : ℝ) < Real.log (X : ℝ) := by
        rw [Real.strictMonoOn_log.lt_iff_lt
          (show (n : ℝ) ∈ Set.Ioi 0 by
            rw [Set.mem_Ioi]
            exact_mod_cast hnpos)
          (show (X : ℝ) ∈ Set.Ioi 0 by
            rw [Set.mem_Ioi]
            exact_mod_cast hX)]
        exact_mod_cast hnlt
      have hnotmem : Real.log (n : ℝ) ∉
          Set.Icc (Real.log X) (Real.log (2 * X)) := by
        intro hm
        linarith [hm.1]
      have hWzero : W n = 0 := by
        exact logTrapezoidWindow_eq_zero_of_not_mem delta
          (Real.log X) (Real.log (2 * X)) hdelta hnotmem
      rw [hWzero, mul_zero]
    · intro hnot
      exact (hnot (Finset.mem_Ioc.mpr ⟨hX, le_rfl⟩)).elim
  have hsplitP : P = Q + ∑ n ∈ D, c n * W n := by
    have hdisj : Disjoint (Finset.Ioc 0 X) D := by
      rw [Finset.disjoint_left]
      intro n hn0 hnD
      have hle := (Finset.mem_Ioc.mp hn0).2
      have hlt := (Finset.mem_Ioc.mp hnD).1
      omega
    have hunion : Finset.Ioc 0 X ∪ D = Finset.Ioc 0 (2 * X) := by
      simpa only [D] using
        (Finset.Ioc_union_Ioc_eq_Ioc (show 0 ≤ X by omega)
          (show X ≤ 2 * X by omega))
    dsimp only [P]
    rw [← hunion, Finset.sum_union hdisj, hlow]
  have houter (n : ℕ) (hn : n ∈ D) :
      Real.log (n : ℝ) ∈ Set.Icc (Real.log X) (Real.log (2 * X)) := by
    have hnI := Finset.mem_Ioc.mp hn
    have hnpos : 0 < n := by omega
    constructor
    · rw [Real.strictMonoOn_log.le_iff_le
        (show (X : ℝ) ∈ Set.Ioi 0 by
          rw [Set.mem_Ioi]
          exact_mod_cast hX)
        (show (n : ℝ) ∈ Set.Ioi 0 by
          rw [Set.mem_Ioi]
          exact_mod_cast hnpos)]
      exact_mod_cast hnI.1.le
    · rw [Real.strictMonoOn_log.le_iff_le
        (show (n : ℝ) ∈ Set.Ioi 0 by
          rw [Set.mem_Ioi]
          exact_mod_cast hnpos)
        (show (2 * X : ℝ) ∈ Set.Ioi 0 by
          rw [Set.mem_Ioi]
          exact_mod_cast (show 0 < 2 * X by omega))]
      exact_mod_cast hnI.2
  have hsplitSharp : (∑ n ∈ D, c n) = SI + SB := by
    simp only [I, E, logSmoothingInterior, logSmoothingBoundary,
      Finset.sum_filter, SI, SB]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro n hn
    have ho := houter n hn
    by_cases hi : Real.log (n : ℝ) ∈
        Set.Icc (Real.log X + 2 * delta) (Real.log (2 * X) - 2 * delta)
    · simp [hi]
    · simp [hi, ho]
  have hsplitSmooth : (∑ n ∈ D, c n * W n) = SI + SE := by
    have h := sum_mul_logTrapezoidWindow_eq_interior_add_boundary
      D c delta (Real.log X) (Real.log (2 * X)) hdelta
    simpa only [W, I, E, SI, SE] using h
  have hdyadic :
      dyadicVerticalDirichletPolynomial (Finset.Ioc X (2 * X)) f X t0 =
        ∑ n ∈ D, c n := by
    unfold dyadicVerticalDirichletPolynomial logarithmicDirichletPolynomial
    have hsupport :
        dyadicRestrictedSupport (Finset.Ioc X (2 * X)) X = D := by
      ext n
      simp [dyadicRestrictedSupport, D]
    rw [hsupport]
  have halgebra :
      dyadicVerticalDirichletPolynomial (Finset.Ioc X (2 * X)) f X t0 =
        P - Q - SE + SB := by
    rw [hdyadic, hsplitSharp, hsplitP, hsplitSmooth]
    ring
  have hQ : ‖Q‖ ≤ (X : ℝ)⁻¹ := by
    dsimp only [Q, c, W]
    rw [norm_mul, norm_mul, norm_logarithmicPhase, mul_one]
    have hwindow := norm_logTrapezoidWindow_le_one delta
      (Real.log X) (Real.log (2 * X)) hdelta (Real.log X)
    have hcoeff : ‖f X / (X : ℂ)‖ ≤ (X : ℝ)⁻¹ := by
      rw [norm_div, Complex.norm_natCast]
      calc
        ‖f X‖ / (X : ℝ) ≤ 1 / (X : ℝ) :=
          div_le_div_of_nonneg_right (hbound X hX) hXR.le
        _ = (X : ℝ)⁻¹ := one_div _
    exact (mul_le_mul_of_nonneg_left hwindow (norm_nonneg _)).trans
      (by simpa using hcoeff)
  have hSE : ‖SE‖ ≤ finiteHalaszDyadicBoundaryMass f X delta := by
    dsimp only [SE]
    calc
      ‖∑ n ∈ E, c n * W n‖ ≤ ∑ n ∈ E, ‖c n * W n‖ :=
        norm_sum_le _ _
      _ ≤ ∑ n ∈ E, ‖f n / (n : ℂ)‖ := by
        apply Finset.sum_le_sum
        intro n hn
        rw [norm_mul, norm_mul, norm_logarithmicPhase, mul_one]
        exact mul_le_of_le_one_right (norm_nonneg _)
          (norm_logTrapezoidWindow_le_one delta
            (Real.log X) (Real.log (2 * X)) hdelta (Real.log n))
      _ = finiteHalaszDyadicBoundaryMass f X delta := by
        rfl
  have hSB : ‖SB‖ ≤ finiteHalaszDyadicBoundaryMass f X delta := by
    dsimp only [SB]
    calc
      ‖∑ n ∈ E, c n‖ ≤ ∑ n ∈ E, ‖c n‖ := norm_sum_le _ _
      _ = ∑ n ∈ E, ‖f n / (n : ℂ)‖ := by
        apply Finset.sum_congr rfl
        intro n hn
        rw [norm_mul, norm_logarithmicPhase, mul_one]
      _ = finiteHalaszDyadicBoundaryMass f X delta := by rfl
  rw [halgebra]
  calc
    ‖P - Q - SE + SB‖ ≤ ‖P - Q - SE‖ + ‖SB‖ := norm_add_le _ _
    _ ≤ (‖P - Q‖ + ‖SE‖) + ‖SB‖ :=
      add_le_add (norm_sub_le _ _) le_rfl
    _ ≤ ((‖P‖ + ‖Q‖) + ‖SE‖) + ‖SB‖ := by
      gcongr
      exact norm_sub_le P Q
    _ ≤ ((‖P‖ + (X : ℝ)⁻¹) +
          finiteHalaszDyadicBoundaryMass f X delta) +
          finiteHalaszDyadicBoundaryMass f X delta := by gcongr
    _ = ‖P‖ + (X : ℝ)⁻¹ +
          2 * finiteHalaszDyadicBoundaryMass f X delta := by ring

/-- Quantitative direct finite-dyadic Halasz endpoint.  The leading term is
the propagated nonpretentious exponential on the bounded near-frequency
band.  The remaining terms are an exact Schwartz tail, the single endpoint
`1/X`, and the explicit harmonic mass of the two shrinking boundary ramps. -/
theorem exists_uniform_norm_dyadicVerticalDirichletPolynomial_le_core_tail :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {f : ℕ → ℂ} {A0 X Y : ℕ},
        IsMultiplicativeOnPositiveNat f →
        (∀ n, 0 < n → ‖f n‖ ≤ 1) →
        2 ≤ Y → Y < X →
        MRArchimedeanNonpretentious f A0 X →
        ∀ {R t0 : ℝ}, 0 ≤ R →
        |t0| + 2 * Real.pi * R ≤ X →
        ∀ (delta : ℝ) (hdelta : 0 < delta),
        ‖dyadicVerticalDirichletPolynomial (Finset.Ioc X (2 * X)) f X t0‖ ≤
          fixedFiniteHalaszEulerBound C A0 X Y *
              (∫ xi in Set.Icc (-R) R,
                ‖tiltedLogTrapezoidKernel
                  (Erdos67b.EulerResidue.taoExponent Y - 1)
                  delta (Real.log X) (Real.log (2 * X)) hdelta xi‖) +
            finiteHalaszLSeriesAbsoluteMass f
                (Erdos67b.EulerResidue.taoExponent Y) *
              tiltedFiniteHalaszKernelTailMass
                (Erdos67b.EulerResidue.taoExponent Y - 1)
                delta (Real.log X) (Real.log (2 * X)) hdelta R +
            (X : ℝ)⁻¹ + 2 * finiteHalaszDyadicBoundaryMass f X delta := by
  obtain ⟨C, hC, hwindow⟩ :=
    exists_uniform_norm_finiteHalaszHarmonicWindowSum_le_core_tail
  refine ⟨C, hC, ?_⟩
  intro f A0 X Y hmul hbound hY hYX hnonpret R t0 hR hfreq delta hdelta
  have hX : 0 < X := by omega
  have hN : 0 < 2 * X := by omega
  have hlogB : Real.log (2 * (X : ℝ)) ≤ Real.log ((2 * X : ℕ) : ℝ) := by
    norm_num
  have hsmooth := hwindow hmul hbound hY hYX hN hnonpret hR hfreq
    delta (Real.log X) (Real.log (2 * X)) hdelta hlogB
  have hsharp :=
    norm_dyadicVerticalDirichletPolynomial_le_harmonicWindow_add_boundary
      hX hbound delta hdelta t0
  exact hsharp.trans (by linarith)

end

end Erdos67b.MRHalaszBands
