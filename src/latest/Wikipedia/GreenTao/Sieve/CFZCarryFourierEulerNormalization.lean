import Wikipedia.GreenTao.Sieve.CFZCarryEulerFactorization
import Wikipedia.GreenTao.Sieve.WTrickedEulerCorrectionLimit
import Wikipedia.GreenTao.Sieve.WTrickedFourierNormalization

/-!
# Normalized completed Euler model on CFZ carry blocks

This file assembles three pieces that were previously separate:

* the exact Selberg/Fourier/singular-zeta normalization;
* the exact small-prime/large-prime factorization for a carry block;
* the uniform limits of the normalized small-prime correction, completed
  zeta factor, and large-prime correction.

The resulting pointwise identity is the normalized form of the *completed
Euler model*.  It deliberately does not identify that model with the
finite `d ≤ R` divisor sum; the honest truncation-to-Euler splice remains a
separate analytic theorem.
-/

namespace Wikipedia.SzemeredisTheorem

open Filter MeasureTheory Topology
open scoped BigOperators

/-- The product of the three residual factors left after exact Selberg and
singular-zeta normalization. -/
noncomputable def normalizedCompletedFourierEulerCorrection
    {κ : Type*} [Fintype κ]
    (R w : ℕ) (t u : κ → ℝ) (largeCorrection : ℂ) : ℂ :=
  normalizedSmallPrimeZetaCorrection R w t u *
    cutoffZetaSystemFactor R t u *
    largeCorrection

/-- **Exact normalized carry Euler model.**  The complete arithmetic/zeta
ratio product can be split into the finite small-prime correction and the
convergent carry-dependent large-prime correction.  After the exact scalar
normalization, only the normalized archimedean kernel and the three
residual factors remain. -/
theorem normalizedSelberg_fourier_completeCarryEuler_eq
    {k : ℕ} (hk : 2 ≤ k)
    (χ : SmoothSieveCutoff)
    (d : SelectedCFZCarryFourierBlockData k)
    (hR : 2 ≤ d.R)
    (hw :
      wTrickedCFZComplexExceptionalBound k ≤ d.w)
    (hwb : (primorial d.w).Coprime d.b) :
    (normalizedSelbergScale χ.normalizer d.R
          (primorial d.w) : ℂ) ^
            Fintype.card (SelectedCFZFormIndex d.e) *
        (((Real.log (d.R : ℝ) ^ 2 : ℝ) : ℂ) ^
            Fintype.card (SelectedCFZFormIndex d.e) *
          (χ.fourierProductTransform d.t *
            χ.fourierProductTransform d.u *
            cutoffZetaSingularFactor d.R d.t d.u)) *
        cutoffZetaSystemFactor d.R d.t d.u *
        (∏' p : Nat.Primes,
          d.primeArithmeticToZetaLocalRatio p) =
      ((χ.normalizer : ℂ)⁻¹) ^
            Fintype.card (SelectedCFZFormIndex d.e) *
        χ.cutoffNormalizerSeparatedProduct (d.t, d.u) *
        normalizedCompletedFourierEulerCorrection
          d.R d.w d.t d.u d.largePrimeEulerCorrection := by
  have hratio :
      (∏' p : Nat.Primes,
          d.primeArithmeticToZetaLocalRatio p) =
        smallPrimeZetaCorrection d.R d.w d.t d.u *
          d.largePrimeEulerCorrection :=
    (smallPrimeZetaCorrection_mul_selectedCFZCarryLargePrimeEulerCorrection
      hk d hR hw hwb).symm
  rw [hratio]
  have hnormalization :=
    normalizedSelberg_fourier_zeta_smallPrime_eq
      χ (show 1 < d.R by omega) d.w d.t d.u
  unfold normalizedCompletedFourierEulerCorrection
  calc
    (normalizedSelbergScale χ.normalizer d.R
          (primorial d.w) : ℂ) ^
            Fintype.card (SelectedCFZFormIndex d.e) *
        (((Real.log (d.R : ℝ) ^ 2 : ℝ) : ℂ) ^
            Fintype.card (SelectedCFZFormIndex d.e) *
          (χ.fourierProductTransform d.t *
            χ.fourierProductTransform d.u *
            cutoffZetaSingularFactor d.R d.t d.u)) *
        cutoffZetaSystemFactor d.R d.t d.u *
        (smallPrimeZetaCorrection d.R d.w d.t d.u *
          d.largePrimeEulerCorrection) =
      ((normalizedSelbergScale χ.normalizer d.R
            (primorial d.w) : ℂ) ^
              Fintype.card (SelectedCFZFormIndex d.e) *
          (((Real.log (d.R : ℝ) ^ 2 : ℝ) : ℂ) ^
              Fintype.card (SelectedCFZFormIndex d.e) *
            (χ.fourierProductTransform d.t *
              χ.fourierProductTransform d.u *
              cutoffZetaSingularFactor d.R d.t d.u)) *
          smallPrimeZetaCorrection d.R d.w d.t d.u) *
        cutoffZetaSystemFactor d.R d.t d.u *
        d.largePrimeEulerCorrection := by
      ring
    _ =
      (((χ.normalizer : ℂ)⁻¹) ^
            Fintype.card (SelectedCFZFormIndex d.e) *
          χ.cutoffNormalizerSeparatedProduct (d.t, d.u) *
          normalizedSmallPrimeZetaCorrection
            d.R d.w d.t d.u) *
        cutoffZetaSystemFactor d.R d.t d.u *
        d.largePrimeEulerCorrection := by
      rw [hnormalization]
    _ =
      ((χ.normalizer : ℂ)⁻¹) ^
            Fintype.card (SelectedCFZFormIndex d.e) *
        χ.cutoffNormalizerSeparatedProduct (d.t, d.u) *
        (normalizedSmallPrimeZetaCorrection d.R d.w d.t d.u *
          cutoffZetaSystemFactor d.R d.t d.u *
          d.largePrimeEulerCorrection) := by
      ring

/-! ## Uniform convergence of the residual factors -/

/-- The completed finite zeta factor tends to one along any growing
Fourier box, provided the cutoff scale tends to infinity. -/
theorem tendsto_cutoffZetaSystemFactor_on_growing_box
    {κ : Type*} [Fintype κ]
    (R : ℕ → ℕ) (t u : ℕ → κ → ℝ)
    (hR : Tendsto R atTop atTop)
    (ht :
      ∀ᶠ n in atTop, ∀ q,
        |t n q| ≤ Real.sqrt (Real.log (R n)))
    (hu :
      ∀ᶠ n in atTop, ∀ q,
        |u n q| ≤ Real.sqrt (Real.log (R n))) :
    Tendsto
      (fun n => cutoffZetaSystemFactor (R n) (t n) (u n))
      atTop (𝓝 1) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨R₀, hclose⟩ :=
    exists_threshold_cutoffZetaSystemFactor_close
      (κ := κ) hε
  have hR₀ : ∀ᶠ n in atTop, R₀ ≤ R n :=
    hR (eventually_ge_atTop R₀)
  filter_upwards [hR₀, ht, hu] with n hRn htn hun
  simpa only [dist_eq_norm] using
    hclose (R n) hRn (t n) (u n) htn hun

/-- Joint convergence of all residual normalized Euler factors.  The
small-prime condition is the explicit scale from
`WTrickedEulerCorrectionLimit`; the completed zeta factor only needs the
standard `sqrt (log R)` box; the final factor may be any independently
proved large-prime correction tending to one. -/
theorem tendsto_normalizedCompletedFourierEulerCorrection_one
    {κ : Type*} [Fintype κ]
    (R w : ℕ → ℕ) (T : ℕ → ℝ)
    (t u : ℕ → κ → ℝ)
    (largeCorrection : ℕ → ℂ)
    (hRtop : Tendsto R atTop atTop)
    (hR : ∀ᶠ n in atTop, 1 < R n)
    (hw : ∀ᶠ n in atTop, 2 ≤ w n)
    (hT : ∀ᶠ n in atTop, 0 ≤ T n)
    (ht : ∀ᶠ n in atTop, ∀ q, |t n q| ≤ T n)
    (hu : ∀ᶠ n in atTop, ∀ q, |u n q| ≤ T n)
    (hTsqrt :
      ∀ᶠ n in atTop,
        T n ≤ Real.sqrt (Real.log (R n)))
    (hscale :
      Tendsto
        (fun n =>
          (((w n + 1 : ℕ) : ℝ) *
            cutoffPhaseMagnitudeBound
                (R n) (w n) (T n) ^ 2))
        atTop (𝓝 0))
    (hlarge :
      Tendsto largeCorrection atTop (𝓝 1)) :
    Tendsto
      (fun n =>
        normalizedCompletedFourierEulerCorrection
          (R n) (w n) (t n) (u n)
          (largeCorrection n))
      atTop (𝓝 1) := by
  have hsmall :=
    tendsto_normalizedSmallPrimeZetaCorrection_of_joint_scale
      R w T t u hR hw hT ht hu hscale
  have htbox :
      ∀ᶠ n in atTop, ∀ q,
        |t n q| ≤ Real.sqrt (Real.log (R n)) := by
    filter_upwards [ht, hTsqrt] with n htn hTn q
    exact (htn q).trans hTn
  have hubox :
      ∀ᶠ n in atTop, ∀ q,
        |u n q| ≤ Real.sqrt (Real.log (R n)) := by
    filter_upwards [hu, hTsqrt] with n hun hTn q
    exact (hun q).trans hTn
  have hzeta :=
    tendsto_cutoffZetaSystemFactor_on_growing_box
      R t u hRtop htbox hubox
  unfold normalizedCompletedFourierEulerCorrection
  simpa using (hsmall.mul hzeta).mul hlarge

end Wikipedia.SzemeredisTheorem
