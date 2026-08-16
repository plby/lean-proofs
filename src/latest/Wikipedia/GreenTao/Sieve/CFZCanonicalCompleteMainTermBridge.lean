import Wikipedia.GreenTao.Sieve.CFZCanonicalEulerCompletionTail
import Wikipedia.GreenTao.Sieve.CFZCanonicalCyclicBoundaryLimit
import Wikipedia.GreenTao.Sieve.CFZCarryFourierEulerNormalization

/-!
# Canonical complete-Euler main-term bridge

This file joins the two exact full-space cancellations in the canonical
CFZ expansion.

* Coordinatewise divisor truncation has zero full-space Fourier integral.
* Completing the finite prime support to the honest Euler support has zero
  full-space Fourier integral in the primorial exceptional-prime regime.

Consequently the canonical cyclic-boundary main term is exactly the
Selberg-scaled full-space integral of the complete Euler integrand.

The second half separates this integral into the standard growing Fourier
box and its complement.  The completed complement is already uniformly
controlled by `CFZCanonicalEulerCompletionTail`; the sole remaining input
is an interior pointwise comparison with the normalized archimedean
baseline.
-/

namespace Wikipedia.SzemeredisTheorem

open Filter MeasureTheory Topology
open scoped BigOperators

/-! ## Integrability of the complete canonical Euler model -/

/-- The complete Euler integrand is strongly measurable.  It is a finite
carry sum of absolutely convergent support series whose individual terms
are integrable. -/
theorem
    SmoothSieveCutoff.aestronglyMeasurable_cfzCanonicalCarryCompleteEulerIntegrand
    {k N w b : ℕ} [NeZero N]
    (χ : SmoothSieveCutoff)
    (e : LinearFormsExponent k)
    (R : ℕ) :
    AEStronglyMeasurable
      (χ.cfzCanonicalCarryCompleteEulerIntegrand
        (N := N) (primorial w) b R
        (fun q : SelectedCFZFormIndex e => q.1))
      (volume.prod volume) := by
  classical
  have hseries
      (carry : SelectedCFZFormIndex e → ℤ) :
      AEStronglyMeasurable
        (fun tu :
            (SelectedCFZFormIndex e → ℝ) ×
              (SelectedCFZFormIndex e → ℝ) =>
          pairedCutoffFourierEnvelope χ tu.1 tu.2 *
            cfzCanonicalCarryCompletePrimeSupportSeries
              N (primorial w) b R
              (fun q : SelectedCFZFormIndex e => q.1)
              carry tu.1 tu.2)
        (volume.prod volume) := by
    have hterms :
        ∀ S : Finset Nat.Primes,
          AEStronglyMeasurable
            (fun tu :
                (SelectedCFZFormIndex e → ℝ) ×
                  (SelectedCFZFormIndex e → ℝ) =>
              pairedCutoffFourierEnvelope χ tu.1 tu.2 *
                unrestrictedPrimeSupportTerm
                  (cfzCanonicalCarryPairedFourierPrimeLocalFactor
                    N (primorial w) b R
                    (fun q : SelectedCFZFormIndex e => q.1)
                    carry tu.1 tu.2) S)
            (volume.prod volume) := by
      intro S
      change AEStronglyMeasurable
        (fun tu :
            (SelectedCFZFormIndex e → ℝ) ×
              (SelectedCFZFormIndex e → ℝ) =>
          pairedCutoffFourierEnvelope χ tu.1 tu.2 *
            unrestrictedPrimeSupportTerm
              (pairedFourierPrimeLocalFactor R
                (cfzCarryAdjustedFamilyAtVector
                  N (primorial w) b
                  (fun q : SelectedCFZFormIndex e => q.1)
                  carry)
                tu.1 tu.2) S)
        (volume.prod volume)
      exact
        (χ.integrable_pairedEnvelope_mul_unrestrictedPrimeSupportTerm
          R
          (cfzCarryAdjustedFamilyAtVector
            N (primorial w) b
            (fun q : SelectedCFZFormIndex e => q.1)
            carry)
          S).aestronglyMeasurable
    have htsum :
        AEStronglyMeasurable
          (fun tu :
              (SelectedCFZFormIndex e → ℝ) ×
                (SelectedCFZFormIndex e → ℝ) =>
            ∑' S : Finset Nat.Primes,
              pairedCutoffFourierEnvelope χ tu.1 tu.2 *
                unrestrictedPrimeSupportTerm
                  (cfzCanonicalCarryPairedFourierPrimeLocalFactor
                    N (primorial w) b R
                    (fun q : SelectedCFZFormIndex e => q.1)
                    carry tu.1 tu.2) S)
          (volume.prod volume) :=
      AEStronglyMeasurable.tsum hterms
    convert htsum using 1
    funext tu
    unfold cfzCanonicalCarryCompletePrimeSupportSeries
    rw [tsum_mul_left]
  unfold SmoothSieveCutoff.cfzCanonicalCarryCompleteEulerIntegrand
    cfzCanonicalCarryCompleteFourierAverage
  have hsum :=
    Finset.aestronglyMeasurable_sum
      (cfzCanonicalCarryVectorChoices
        (SelectedCFZFormIndex e) k)
      (fun carry _hcarry =>
        (hseries carry).const_mul
          (cfzCanonicalCarryCellDensity
            (N := N)
            (fun q : SelectedCFZFormIndex e => q.1)
            carry : ℂ))
  convert hsum using 1
  funext tu
  rw [Finset.mul_sum]
  simp only [Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro carry _hcarry
  ring

/-- Absolute integrability of the complete canonical Euler integrand. -/
theorem SmoothSieveCutoff.integrable_cfzCanonicalCarryCompleteEulerIntegrand
    {k N w b : ℕ} [NeZero N]
    (χ : SmoothSieveCutoff)
    (hk : 2 ≤ k)
    (hbound :
      exceptionalPrimeBound
          (fun q : CFZFormIndex k => cfzAffineForm q) ≤ w)
    (hwb : (primorial w).Coprime b)
    (e : LinearFormsExponent k)
    {R : ℕ} (hR : 2 ≤ R) :
    Integrable
      (χ.cfzCanonicalCarryCompleteEulerIntegrand
        (N := N) (primorial w) b R
        (fun q : SelectedCFZFormIndex e => q.1))
      (volume.prod volume) := by
  let mass := selectedCFZCanonicalCompleteSupportMass e R
  let density :=
    χ.selectedCFZPairedFourierAbsoluteDensity e
  have hmajorant :
      Integrable
        (fun tu :
            (SelectedCFZFormIndex e → ℝ) ×
              (SelectedCFZFormIndex e → ℝ) =>
          mass * density tu)
        (volume.prod volume) :=
    (χ.integrable_selectedCFZPairedFourierAbsoluteDensity e).const_mul
      mass
  apply hmajorant.mono
  · exact
      χ.aestronglyMeasurable_cfzCanonicalCarryCompleteEulerIntegrand
        (N := N) (w := w) (b := b) e R
  · exact ae_of_all _ fun tu => by
      have hmass :
          0 ≤ mass :=
        selectedCFZCanonicalCompleteSupportMass_nonneg e R
      have hdensity :
          0 ≤ density tu :=
        χ.selectedCFZPairedFourierAbsoluteDensity_nonneg e tu
      simpa only [mass, density, Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg hmass hdensity)] using
        χ.norm_cfzCanonicalCarryCompleteEulerIntegrand_le
          (N := N) hk hbound hwb e hR tu

/-! ## Exact finite-to-complete main term -/

/-- The finite unrestricted canonical Euler integrand is integrable.  This
is deduced from the original finite divisor Fourier integrand and the exact
coordinatewise truncation splice. -/
theorem
    SmoothSieveCutoff.integrable_pairedEnvelope_mul_cfzCanonicalCarryUnrestrictedFourierAverage
    {k N : ℕ} [NeZero N]
    (χ : SmoothSieveCutoff)
    (W b : ℕ) {R : ℕ} (hR : 2 ≤ R)
    (e : LinearFormsExponent k) :
    Integrable
      (fun tu :
          (SelectedCFZFormIndex e → ℝ) ×
            (SelectedCFZFormIndex e → ℝ) =>
        pairedCutoffFourierEnvelope χ tu.1 tu.2 *
          cfzCanonicalCarryUnrestrictedFourierAverage
            (N := N) W b R
            (fun q : SelectedCFZFormIndex e => q.1)
            tu.1 tu.2)
      (volume.prod volume) := by
  let finiteIntegrand :=
    fun tu :
        (SelectedCFZFormIndex e → ℝ) ×
          (SelectedCFZFormIndex e → ℝ) =>
      χ.divisorExpansionFourierIntegrand R
        (fun z =>
          cfzCanonicalCarryEulerAverage
            (N := N) W b
            (fun q : SelectedCFZFormIndex e => q.1) z)
        tu
  let truncation :=
    fun tu :
        (SelectedCFZFormIndex e → ℝ) ×
          (SelectedCFZFormIndex e → ℝ) =>
      cfzCanonicalCarryTruncationDiscrepancy
        (N := N) χ W b R
        (fun q : SelectedCFZFormIndex e => q.1)
        tu.1 tu.2
  have hfinite :
      Integrable finiteIntegrand (volume.prod volume) :=
    χ.integrable_divisorExpansionFourierIntegrand R
      (fun z =>
        cfzCanonicalCarryEulerAverage
          (N := N) W b
          (fun q : SelectedCFZFormIndex e => q.1) z)
  have htruncation :
      Integrable truncation (volume.prod volume) := by
    exact
      integrable_cfzCanonicalCarryTruncationDiscrepancy
        χ W b hR
          (fun q : SelectedCFZFormIndex e => q.1)
  have hdifference :
      (fun tu :
          (SelectedCFZFormIndex e → ℝ) ×
            (SelectedCFZFormIndex e → ℝ) =>
        pairedCutoffFourierEnvelope χ tu.1 tu.2 *
          cfzCanonicalCarryUnrestrictedFourierAverage
            (N := N) W b R
            (fun q : SelectedCFZFormIndex e => q.1)
            tu.1 tu.2) =
        fun tu => finiteIntegrand tu - truncation tu := by
    funext tu
    have hsplice :=
      χ.selectedCFZCanonicalEulerFourierIntegrand_eq_unrestricted_add_discrepancy
        (N := N) R W b e tu.1 tu.2
    dsimp [finiteIntegrand, truncation]
    rw [hsplice]
    ring
  rw [hdifference]
  exact hfinite.sub htruncation

/-- The Euler-completion discrepancy is integrable. -/
theorem
    SmoothSieveCutoff.integrable_cfzCanonicalCarryEulerCompletionDiscrepancy
    {k N w b : ℕ} [NeZero N]
    (χ : SmoothSieveCutoff)
    (hk : 2 ≤ k)
    (hbound :
      exceptionalPrimeBound
          (fun q : CFZFormIndex k => cfzAffineForm q) ≤ w)
    (hwb : (primorial w).Coprime b)
    (e : LinearFormsExponent k)
    {R : ℕ} (hR : 2 ≤ R) :
    Integrable
      (χ.cfzCanonicalCarryEulerCompletionDiscrepancy
        (N := N) (primorial w) b R
        (fun q : SelectedCFZFormIndex e => q.1))
      (volume.prod volume) := by
  unfold SmoothSieveCutoff.cfzCanonicalCarryEulerCompletionDiscrepancy
  exact
    (χ.integrable_pairedEnvelope_mul_cfzCanonicalCarryUnrestrictedFourierAverage
      (N := N) (primorial w) b hR e).sub
      (χ.integrable_cfzCanonicalCarryCompleteEulerIntegrand
        (N := N) hk hbound hwb e hR)

/-- **Exact complete-main-term identity.**  In the primorial regime, the
canonical Fourier main term is exactly the Selberg-scaled full-space
integral of the honest complete Euler integrand. -/
theorem
    SmoothSieveCutoff.selectedCFZCanonicalEulerFourierMainTerm_eq_completeEulerIntegral
    {k N w b : ℕ} [NeZero N]
    (χ : SmoothSieveCutoff)
    (hk : 2 ≤ k)
    (hbound :
      exceptionalPrimeBound
          (fun q : CFZFormIndex k => cfzAffineForm q) ≤ w)
    (hwb : (primorial w).Coprime b)
    (e : LinearFormsExponent k)
    {R : ℕ} (hR : 2 ≤ R) :
    χ.selectedCFZCanonicalEulerFourierMainTerm
        (N := N) R (primorial w) b e =
      (normalizedSelbergScale
          χ.normalizer R (primorial w) : ℂ) ^
          Fintype.card (SelectedCFZFormIndex e) *
        (((Real.log R ^ 2 : ℝ) : ℂ) ^
            Fintype.card (SelectedCFZFormIndex e) *
          ∫ tu :
              (SelectedCFZFormIndex e → ℝ) ×
                (SelectedCFZFormIndex e → ℝ),
            χ.cfzCanonicalCarryCompleteEulerIntegrand
              (N := N) (primorial w) b R
              (fun q : SelectedCFZFormIndex e => q.1) tu
            ∂(volume.prod volume)) := by
  let unrestricted :=
    fun tu :
        (SelectedCFZFormIndex e → ℝ) ×
          (SelectedCFZFormIndex e → ℝ) =>
      pairedCutoffFourierEnvelope χ tu.1 tu.2 *
        cfzCanonicalCarryUnrestrictedFourierAverage
          (N := N) (primorial w) b R
          (fun q : SelectedCFZFormIndex e => q.1)
          tu.1 tu.2
  let truncation :=
    fun tu :
        (SelectedCFZFormIndex e → ℝ) ×
          (SelectedCFZFormIndex e → ℝ) =>
      cfzCanonicalCarryTruncationDiscrepancy
        (N := N) χ (primorial w) b R
        (fun q : SelectedCFZFormIndex e => q.1)
        tu.1 tu.2
  let complete :=
    χ.cfzCanonicalCarryCompleteEulerIntegrand
      (N := N) (primorial w) b R
      (fun q : SelectedCFZFormIndex e => q.1)
  let completion :=
    χ.cfzCanonicalCarryEulerCompletionDiscrepancy
      (N := N) (primorial w) b R
      (fun q : SelectedCFZFormIndex e => q.1)
  have hunrestricted :
      Integrable unrestricted (volume.prod volume) :=
    χ.integrable_pairedEnvelope_mul_cfzCanonicalCarryUnrestrictedFourierAverage
      (N := N) (primorial w) b hR e
  have htruncation :
      Integrable truncation (volume.prod volume) :=
    integrable_cfzCanonicalCarryTruncationDiscrepancy
      χ (primorial w) b hR
        (fun q : SelectedCFZFormIndex e => q.1)
  have hcomplete :
      Integrable complete (volume.prod volume) :=
    χ.integrable_cfzCanonicalCarryCompleteEulerIntegrand
      (N := N) hk hbound hwb e hR
  have hcompletion :
      Integrable completion (volume.prod volume) :=
    χ.integrable_cfzCanonicalCarryEulerCompletionDiscrepancy
      (N := N) hk hbound hwb e hR
  have htruncationIntegral :
      (∫ tu, truncation tu ∂(volume.prod volume)) = 0 := by
    exact
      integral_cfzCanonicalCarryTruncationDiscrepancy_eq_zero
        χ (primorial w) b hR
          (fun q : SelectedCFZFormIndex e => q.1)
  have hcompletionIntegral :
      (∫ tu, completion tu ∂(volume.prod volume)) = 0 := by
    exact
      χ.integral_cfzCanonicalCarryEulerCompletionDiscrepancy_eq_zero
        (N := N) hk hbound hwb e hR
  have hunrestrictedIntegral :
      (∫ tu, unrestricted tu ∂(volume.prod volume)) =
        ∫ tu, complete tu ∂(volume.prod volume) := by
    have hsub :
        (∫ tu, unrestricted tu - complete tu
            ∂(volume.prod volume)) = 0 := by
      simpa [completion, unrestricted, complete,
        SmoothSieveCutoff.cfzCanonicalCarryEulerCompletionDiscrepancy]
        using hcompletionIntegral
    rw [integral_sub hunrestricted hcomplete] at hsub
    exact sub_eq_zero.mp hsub
  rw [
    χ.selectedCFZCanonicalEulerFourierMainTerm_eq_integral_unrestricted_add_discrepancy
      (N := N) R (primorial w) b e]
  congr 2
  rw [integral_add hunrestricted htruncation,
    htruncationIntegral, add_zero, hunrestrictedIntegral]

/-! ## Scaled integrand and normalized archimedean baseline -/

/-- The complete canonical Euler integrand with both Selberg prefactors
placed pointwise inside the Fourier integral. -/
noncomputable def
    SmoothSieveCutoff.selectedCFZCanonicalCompleteEulerScaledIntegrand
    {k N : ℕ} [NeZero N]
    (χ : SmoothSieveCutoff)
    (w b R : ℕ) (e : LinearFormsExponent k)
    (tu :
      (SelectedCFZFormIndex e → ℝ) ×
        (SelectedCFZFormIndex e → ℝ)) : ℂ :=
  (normalizedSelbergScale
      χ.normalizer R (primorial w) : ℂ) ^
        Fintype.card (SelectedCFZFormIndex e) *
    (((Real.log R ^ 2 : ℝ) : ℂ) ^
        Fintype.card (SelectedCFZFormIndex e) *
      χ.cfzCanonicalCarryCompleteEulerIntegrand
        (N := N) (primorial w) b R
        (fun q : SelectedCFZFormIndex e => q.1) tu)

/-- The normalized archimedean product which remains after exact
Selberg/zeta normalization. -/
noncomputable def
    SmoothSieveCutoff.selectedCFZCanonicalArchimedeanBaseline
    {k : ℕ} (χ : SmoothSieveCutoff)
    (e : LinearFormsExponent k)
    (tu :
      (SelectedCFZFormIndex e → ℝ) ×
        (SelectedCFZFormIndex e → ℝ)) : ℂ :=
  ((χ.normalizer : ℂ)⁻¹) ^
      Fintype.card (SelectedCFZFormIndex e) *
    χ.cutoffNormalizerSeparatedProduct tu

/-- The scaled complete integrand is integrable. -/
theorem
    SmoothSieveCutoff.integrable_selectedCFZCanonicalCompleteEulerScaledIntegrand
    {k N w b : ℕ} [NeZero N]
    (χ : SmoothSieveCutoff)
    (hk : 2 ≤ k)
    (hbound :
      exceptionalPrimeBound
          (fun q : CFZFormIndex k => cfzAffineForm q) ≤ w)
    (hwb : (primorial w).Coprime b)
    (e : LinearFormsExponent k)
    {R : ℕ} (hR : 2 ≤ R) :
    Integrable
      (χ.selectedCFZCanonicalCompleteEulerScaledIntegrand
        (N := N) w b R e)
      (volume.prod volume) := by
  unfold
    SmoothSieveCutoff.selectedCFZCanonicalCompleteEulerScaledIntegrand
  exact
    (χ.integrable_cfzCanonicalCarryCompleteEulerIntegrand
      (N := N) hk hbound hwb e hR).const_mul _
      |>.const_mul _

/-- The normalized archimedean baseline is integrable. -/
theorem
    SmoothSieveCutoff.integrable_selectedCFZCanonicalArchimedeanBaseline
    {k : ℕ} (χ : SmoothSieveCutoff)
    (e : LinearFormsExponent k) :
    Integrable
      (χ.selectedCFZCanonicalArchimedeanBaseline e)
      (volume.prod volume) := by
  change
    Integrable
      (fun tu =>
        ((χ.normalizer : ℂ)⁻¹) ^
            Fintype.card (SelectedCFZFormIndex e) *
          χ.cutoffNormalizerSeparatedProduct tu)
      (volume.prod volume)
  exact
    χ.integrable_invNormalizerPow_mul_cutoffNormalizerSeparatedProduct
      (κ := SelectedCFZFormIndex e)

/-- The full normalized archimedean integral is exactly one. -/
theorem
    SmoothSieveCutoff.integral_selectedCFZCanonicalArchimedeanBaseline_eq_one
    {k : ℕ} (χ : SmoothSieveCutoff)
    (e : LinearFormsExponent k) :
    (∫ tu :
        (SelectedCFZFormIndex e → ℝ) ×
          (SelectedCFZFormIndex e → ℝ),
      χ.selectedCFZCanonicalArchimedeanBaseline e tu
      ∂(volume.prod volume)) = 1 := by
  change
    (∫ tu :
        (SelectedCFZFormIndex e → ℝ) ×
          (SelectedCFZFormIndex e → ℝ),
      ((χ.normalizer : ℂ)⁻¹) ^
          Fintype.card (SelectedCFZFormIndex e) *
        χ.cutoffNormalizerSeparatedProduct tu
      ∂(volume.prod volume)) = 1
  exact
    χ.integral_invNormalizerPow_mul_cutoffNormalizerSeparatedProduct_eq_one
      (κ := SelectedCFZFormIndex e)

/-- Pointwise scaling commutes with the full integral. -/
theorem
    SmoothSieveCutoff.integral_selectedCFZCanonicalCompleteEulerScaledIntegrand
    {k N : ℕ} [NeZero N]
    (χ : SmoothSieveCutoff)
    (w b R : ℕ) (e : LinearFormsExponent k) :
    (∫ tu :
        (SelectedCFZFormIndex e → ℝ) ×
          (SelectedCFZFormIndex e → ℝ),
      χ.selectedCFZCanonicalCompleteEulerScaledIntegrand
        (N := N) w b R e tu
      ∂(volume.prod volume)) =
      (normalizedSelbergScale
          χ.normalizer R (primorial w) : ℂ) ^
          Fintype.card (SelectedCFZFormIndex e) *
        (((Real.log R ^ 2 : ℝ) : ℂ) ^
            Fintype.card (SelectedCFZFormIndex e) *
          ∫ tu :
              (SelectedCFZFormIndex e → ℝ) ×
                (SelectedCFZFormIndex e → ℝ),
            χ.cfzCanonicalCarryCompleteEulerIntegrand
              (N := N) (primorial w) b R
              (fun q : SelectedCFZFormIndex e => q.1) tu
            ∂(volume.prod volume)) := by
  unfold
    SmoothSieveCutoff.selectedCFZCanonicalCompleteEulerScaledIntegrand
  rw [integral_const_mul, integral_const_mul]

/-- The exact complete-main-term identity with all scalar factors moved
inside the integral. -/
theorem
    SmoothSieveCutoff.selectedCFZCanonicalEulerFourierMainTerm_eq_integral_completeEulerScaledIntegrand
    {k N w b : ℕ} [NeZero N]
    (χ : SmoothSieveCutoff)
    (hk : 2 ≤ k)
    (hbound :
      exceptionalPrimeBound
          (fun q : CFZFormIndex k => cfzAffineForm q) ≤ w)
    (hwb : (primorial w).Coprime b)
    (e : LinearFormsExponent k)
    {R : ℕ} (hR : 2 ≤ R) :
    χ.selectedCFZCanonicalEulerFourierMainTerm
        (N := N) R (primorial w) b e =
      ∫ tu :
          (SelectedCFZFormIndex e → ℝ) ×
            (SelectedCFZFormIndex e → ℝ),
        χ.selectedCFZCanonicalCompleteEulerScaledIntegrand
          (N := N) w b R e tu
        ∂(volume.prod volume) := by
  rw [
    χ.selectedCFZCanonicalEulerFourierMainTerm_eq_completeEulerIntegral
      (N := N) hk hbound hwb e hR,
    χ.integral_selectedCFZCanonicalCompleteEulerScaledIntegrand
      (N := N) w b R e]

/-- Any integrable function splits exactly into the selected Fourier box
and its complement. -/
theorem integral_eq_selectedCFZPairedFourierBox_add_compl
    {k : ℕ} (e : LinearFormsExponent k)
    (T : ℝ)
    {f :
      ((SelectedCFZFormIndex e → ℝ) ×
        (SelectedCFZFormIndex e → ℝ)) → ℂ}
    (hf : Integrable f (volume.prod volume)) :
    (∫ tu, f tu ∂(volume.prod volume)) =
      (∫ tu in SmoothSieveCutoff.selectedCFZPairedFourierBox e T,
          f tu ∂(volume.prod volume)) +
        ∫ tu in
            (SmoothSieveCutoff.selectedCFZPairedFourierBox e T)ᶜ,
          f tu ∂(volume.prod volume) := by
  exact
    (integral_add_compl
      (SmoothSieveCutoff.measurableSet_selectedCFZPairedFourierBox e T) hf).symm

/-- The integral of any fixed integrable function over the complement of
the selected paired Fourier box tends to zero. -/
theorem tendsto_integral_selectedCFZPairedFourierBox_compl_atTop
    {k : ℕ} (e : LinearFormsExponent k)
    {f :
      ((SelectedCFZFormIndex e → ℝ) ×
        (SelectedCFZFormIndex e → ℝ)) → ℂ}
    (hf : Integrable f (volume.prod volume)) :
    Tendsto
      (fun T : ℝ =>
        ∫ tu in
            (SmoothSieveCutoff.selectedCFZPairedFourierBox e T)ᶜ,
          f tu ∂(volume.prod volume))
      atTop (𝓝 0) := by
  have hcover :
      AECover (volume.prod volume) atTop
        (fun T : ℝ =>
          SmoothSieveCutoff.selectedCFZPairedFourierBox e T) := by
    have hclosed :
        AECover (volume.prod volume) atTop
          (fun T : ℝ =>
            Metric.closedBall
              (0 :
                (SelectedCFZFormIndex e → ℝ) ×
                  (SelectedCFZFormIndex e → ℝ))
              T) :=
      aecover_closedBall tendsto_id
    convert hclosed using 1
    funext T
    exact
      SmoothSieveCutoff.selectedCFZPairedFourierBox_eq_closedBall e T
  have hinside :
      Tendsto
        (fun T : ℝ =>
          ∫ tu in
              SmoothSieveCutoff.selectedCFZPairedFourierBox e T,
            f tu ∂(volume.prod volume))
        atTop
        (𝓝 (∫ tu, f tu ∂(volume.prod volume))) :=
    hcover.integral_tendsto_of_countably_generated hf
  have hconst :
      Tendsto
        (fun _ : ℝ =>
          ∫ tu, f tu ∂(volume.prod volume))
        atTop
        (𝓝 (∫ tu, f tu ∂(volume.prod volume))) :=
    tendsto_const_nhds
  have hsub :
      Tendsto
        (fun T : ℝ =>
          (∫ tu, f tu ∂(volume.prod volume)) -
            ∫ tu in
                SmoothSieveCutoff.selectedCFZPairedFourierBox e T,
              f tu ∂(volume.prod volume))
        atTop (𝓝 0) := by
    convert hconst.sub hinside using 1
    all_goals simp
  refine hsub.congr' (Filter.Eventually.of_forall fun T => ?_)
  symm
  exact
    setIntegral_compl
      (SmoothSieveCutoff.measurableSet_selectedCFZPairedFourierBox e T)
      hf

/-- The complete-model complementary-box norm is exactly the tail norm
controlled by `CFZCanonicalEulerCompletionTail`. -/
theorem
    SmoothSieveCutoff.norm_integral_selectedCFZCanonicalCompleteEulerScaledIntegrand_compl_eq
    {k N : ℕ} [NeZero N]
    (χ : SmoothSieveCutoff)
    (w b R : ℕ) (e : LinearFormsExponent k) (T : ℝ) :
    ‖∫ tu in
        (SmoothSieveCutoff.selectedCFZPairedFourierBox e T)ᶜ,
        χ.selectedCFZCanonicalCompleteEulerScaledIntegrand
          (N := N) w b R e tu
        ∂(volume.prod volume)‖ =
      χ.selectedCFZCanonicalCompleteEulerScaledTailNorm
        (N := N) w b R e T := by
  unfold
    SmoothSieveCutoff.selectedCFZCanonicalCompleteEulerScaledIntegrand
    SmoothSieveCutoff.selectedCFZCanonicalCompleteEulerScaledTailNorm
  rw [integral_const_mul, integral_const_mul]

/-- The fixed archimedean baseline has vanishing complementary integral
along every sieve-radius sequence tending to infinity. -/
theorem
    SmoothSieveCutoff.tendsto_norm_integral_selectedCFZCanonicalArchimedeanBaseline_compl_sqrt_log
    {k : ℕ} (χ : SmoothSieveCutoff)
    (Rseq : ℕ → ℕ)
    (hRseq : Tendsto Rseq atTop atTop)
    (e : LinearFormsExponent k) :
    Tendsto
      (fun n : ℕ =>
        ‖∫ tu in
            (SmoothSieveCutoff.selectedCFZPairedFourierBox e
              (Real.sqrt (Real.log (Rseq n))))ᶜ,
          χ.selectedCFZCanonicalArchimedeanBaseline e tu
          ∂(volume.prod volume)‖)
      atTop (𝓝 0) := by
  have hintegral :
      Tendsto
        (fun n : ℕ =>
          ∫ tu in
              (SmoothSieveCutoff.selectedCFZPairedFourierBox e
                (Real.sqrt (Real.log (Rseq n))))ᶜ,
            χ.selectedCFZCanonicalArchimedeanBaseline e tu
            ∂(volume.prod volume))
        atTop (𝓝 0) :=
    (tendsto_integral_selectedCFZPairedFourierBox_compl_atTop e
      (χ.integrable_selectedCFZCanonicalArchimedeanBaseline e)).comp
        (SmoothSieveCutoff.tendsto_sqrt_log_nat_atTop.comp hRseq)
  simpa using hintegral.norm

/-! ## Interior comparison and the complete integration estimate -/

/-- Quantitative bridge from a pointwise interior comparison to the whole
complete main term.  The two complementary contributions are kept in their
exact norms so that the schedule-uniform completion theorem can consume
the first one directly. -/
theorem
    SmoothSieveCutoff.norm_selectedCFZCanonicalEulerFourierMainTerm_sub_one_le_of_interior
    {k N w b : ℕ} [NeZero N]
    (χ : SmoothSieveCutoff)
    (hk : 2 ≤ k)
    (hbound :
      exceptionalPrimeBound
          (fun q : CFZFormIndex k => cfzAffineForm q) ≤ w)
    (hwb : (primorial w).Coprime b)
    (e : LinearFormsExponent k)
    {R : ℕ} (hR : 2 ≤ R)
    {δ T : ℝ} (hδ : 0 ≤ δ)
    (hinterior :
      ∀ tu ∈ SmoothSieveCutoff.selectedCFZPairedFourierBox e T,
        ‖χ.selectedCFZCanonicalCompleteEulerScaledIntegrand
              (N := N) w b R e tu -
            χ.selectedCFZCanonicalArchimedeanBaseline e tu‖ ≤
          δ *
            ‖χ.selectedCFZCanonicalArchimedeanBaseline e tu‖) :
    ‖χ.selectedCFZCanonicalEulerFourierMainTerm
          (N := N) R (primorial w) b e - 1‖ ≤
      δ *
          ∫ tu :
              (SelectedCFZFormIndex e → ℝ) ×
                (SelectedCFZFormIndex e → ℝ),
            ‖χ.selectedCFZCanonicalArchimedeanBaseline e tu‖
            ∂(volume.prod volume) +
        χ.selectedCFZCanonicalCompleteEulerScaledTailNorm
          (N := N) w b R e T +
        ‖∫ tu in
            (SmoothSieveCutoff.selectedCFZPairedFourierBox e T)ᶜ,
            χ.selectedCFZCanonicalArchimedeanBaseline e tu
            ∂(volume.prod volume)‖ := by
  let scaled :=
    χ.selectedCFZCanonicalCompleteEulerScaledIntegrand
      (N := N) w b R e
  let baseline :=
    χ.selectedCFZCanonicalArchimedeanBaseline e
  let box := SmoothSieveCutoff.selectedCFZPairedFourierBox e T
  have hscaled :
      Integrable scaled (volume.prod volume) :=
    χ.integrable_selectedCFZCanonicalCompleteEulerScaledIntegrand
      (N := N) hk hbound hwb e hR
  have hbaseline :
      Integrable baseline (volume.prod volume) :=
    χ.integrable_selectedCFZCanonicalArchimedeanBaseline e
  have hboxDifference :
      ‖∫ tu in box, scaled tu - baseline tu
          ∂(volume.prod volume)‖ ≤
        δ *
          ∫ tu :
              (SelectedCFZFormIndex e → ℝ) ×
                (SelectedCFZFormIndex e → ℝ),
            ‖baseline tu‖ ∂(volume.prod volume) := by
    have hdom :
        ∀ᵐ tu ∂(volume.prod volume).restrict box,
          ‖scaled tu - baseline tu‖ ≤
            δ * ‖baseline tu‖ :=
      ae_restrict_of_forall_mem
        (SmoothSieveCutoff.measurableSet_selectedCFZPairedFourierBox e T)
        (fun tu htu => hinterior tu htu)
    have hboundIntegrable :
        Integrable
          (fun tu :
              (SelectedCFZFormIndex e → ℝ) ×
                (SelectedCFZFormIndex e → ℝ) =>
            δ * ‖baseline tu‖)
          (volume.prod volume) :=
      hbaseline.norm.const_mul δ
    have hnorm :=
      norm_integral_le_of_norm_le
        hboundIntegrable.integrableOn hdom
    have hsetLe :
        (∫ tu in box,
            δ * ‖baseline tu‖
            ∂(volume.prod volume)) ≤
          δ *
            ∫ tu :
                (SelectedCFZFormIndex e → ℝ) ×
                  (SelectedCFZFormIndex e → ℝ),
              ‖baseline tu‖ ∂(volume.prod volume) := by
      rw [integral_const_mul]
      apply mul_le_mul_of_nonneg_left _ hδ
      exact setIntegral_le_integral
        hbaseline.norm
        (ae_of_all _ fun tu => norm_nonneg _)
    exact hnorm.trans hsetLe
  have hboxSub :
      (∫ tu in box, scaled tu ∂(volume.prod volume)) -
          ∫ tu in box, baseline tu ∂(volume.prod volume) =
        ∫ tu in box, scaled tu - baseline tu
          ∂(volume.prod volume) := by
    symm
    exact integral_sub hscaled.integrableOn hbaseline.integrableOn
  have hmain :
      χ.selectedCFZCanonicalEulerFourierMainTerm
          (N := N) R (primorial w) b e =
        (∫ tu in box, scaled tu ∂(volume.prod volume)) +
          ∫ tu in boxᶜ, scaled tu
            ∂(volume.prod volume) := by
    rw [
      χ.selectedCFZCanonicalEulerFourierMainTerm_eq_integral_completeEulerScaledIntegrand
        (N := N) hk hbound hwb e hR]
    exact integral_eq_selectedCFZPairedFourierBox_add_compl
      e T hscaled
  have hbase :
      (1 : ℂ) =
        (∫ tu in box, baseline tu ∂(volume.prod volume)) +
          ∫ tu in boxᶜ, baseline tu
            ∂(volume.prod volume) := by
    rw [← χ.integral_selectedCFZCanonicalArchimedeanBaseline_eq_one e]
    exact integral_eq_selectedCFZPairedFourierBox_add_compl
      e T hbaseline
  calc
    ‖χ.selectedCFZCanonicalEulerFourierMainTerm
          (N := N) R (primorial w) b e - 1‖ =
        ‖((∫ tu in box, scaled tu ∂(volume.prod volume)) -
            ∫ tu in box, baseline tu ∂(volume.prod volume)) +
          ((∫ tu in boxᶜ, scaled tu ∂(volume.prod volume)) -
            ∫ tu in boxᶜ, baseline tu
              ∂(volume.prod volume))‖ := by
      rw [hmain, hbase]
      congr 1
      ring
    _ ≤
        ‖(∫ tu in box, scaled tu ∂(volume.prod volume)) -
            ∫ tu in box, baseline tu ∂(volume.prod volume)‖ +
          ‖∫ tu in boxᶜ, scaled tu
            ∂(volume.prod volume)‖ +
          ‖∫ tu in boxᶜ, baseline tu
            ∂(volume.prod volume)‖ := by
      calc
        _ ≤
            ‖(∫ tu in box, scaled tu ∂(volume.prod volume)) -
                ∫ tu in box, baseline tu ∂(volume.prod volume)‖ +
              ‖(∫ tu in boxᶜ, scaled tu ∂(volume.prod volume)) -
                ∫ tu in boxᶜ, baseline tu
                  ∂(volume.prod volume)‖ :=
          norm_add_le _ _
        _ ≤
            ‖(∫ tu in box, scaled tu ∂(volume.prod volume)) -
                ∫ tu in box, baseline tu ∂(volume.prod volume)‖ +
              (‖∫ tu in boxᶜ, scaled tu
                  ∂(volume.prod volume)‖ +
                ‖∫ tu in boxᶜ, baseline tu
                  ∂(volume.prod volume)‖) :=
          add_le_add_right
            (norm_sub_le
              (∫ tu in boxᶜ, scaled tu
                ∂(volume.prod volume))
              (∫ tu in boxᶜ, baseline tu
                ∂(volume.prod volume)))
            ‖(∫ tu in box, scaled tu ∂(volume.prod volume)) -
                ∫ tu in box, baseline tu
                  ∂(volume.prod volume)‖
        _ = _ := (add_assoc _ _ _).symm
    _ ≤
        δ *
            ∫ tu :
                (SelectedCFZFormIndex e → ℝ) ×
                  (SelectedCFZFormIndex e → ℝ),
              ‖baseline tu‖ ∂(volume.prod volume) +
          χ.selectedCFZCanonicalCompleteEulerScaledTailNorm
            (N := N) w b R e T +
          ‖∫ tu in boxᶜ, baseline tu
            ∂(volume.prod volume)‖ := by
      rw [hboxSub,
        χ.norm_integral_selectedCFZCanonicalCompleteEulerScaledIntegrand_compl_eq
          (N := N) w b R e T]
      linarith

/-- Schedule-uniform complete-main-term limit.  After the exact divisor
truncation and Euler-completion cancellations, the only model-specific
analytic input is the eventual pointwise comparison on the growing
Fourier box.  The cyclic modulus, primorial cutoff, residue, and sieve
radius may all vary. -/
theorem
    SmoothSieveCutoff.tendsto_selectedCFZCanonicalEulerFourierMainTerm_one_of_interior
    {k : ℕ}
    (χ : SmoothSieveCutoff)
    (hk : 2 ≤ k)
    (Nseq wseq bseq Rseq : ℕ → ℕ)
    (hN : ∀ n, Nseq n ≠ 0)
    (hbound :
      ∀ n,
        exceptionalPrimeBound
            (fun q : CFZFormIndex k => cfzAffineForm q) ≤
          wseq n)
    (hcoprime :
      ∀ n, (primorial (wseq n)).Coprime (bseq n))
    (hRseq : Tendsto Rseq atTop atTop)
    (e : LinearFormsExponent k)
    (δ : ℕ → ℝ)
    (hδnonneg : ∀ᶠ n : ℕ in atTop, 0 ≤ δ n)
    (hδzero : Tendsto δ atTop (𝓝 0))
    (hinterior :
      ∀ᶠ n : ℕ in atTop,
        letI : NeZero (Nseq n) := ⟨hN n⟩
        ∀ tu ∈
            SmoothSieveCutoff.selectedCFZPairedFourierBox e
              (Real.sqrt (Real.log (Rseq n))),
          ‖χ.selectedCFZCanonicalCompleteEulerScaledIntegrand
                (N := Nseq n) (wseq n) (bseq n) (Rseq n) e tu -
              χ.selectedCFZCanonicalArchimedeanBaseline e tu‖ ≤
            δ n *
              ‖χ.selectedCFZCanonicalArchimedeanBaseline e tu‖) :
    Tendsto
      (fun n : ℕ =>
        letI : NeZero (Nseq n) := ⟨hN n⟩
        χ.selectedCFZCanonicalEulerFourierMainTerm
          (N := Nseq n) (Rseq n)
          (primorial (wseq n)) (bseq n) e)
      atTop (𝓝 1) := by
  have hRtwo :
      ∀ᶠ n : ℕ in atTop, 2 ≤ Rseq n :=
    hRseq.eventually (eventually_ge_atTop 2)
  have hδmass :
      Tendsto
        (fun n : ℕ =>
          δ n *
            ∫ tu :
                (SelectedCFZFormIndex e → ℝ) ×
                  (SelectedCFZFormIndex e → ℝ),
              ‖χ.selectedCFZCanonicalArchimedeanBaseline e tu‖
              ∂(volume.prod volume))
        atTop (𝓝 0) := by
    simpa only [zero_mul] using
      (hδzero.mul
        (tendsto_const_nhds :
          Tendsto
            (fun _ : ℕ =>
              ∫ tu :
                  (SelectedCFZFormIndex e → ℝ) ×
                    (SelectedCFZFormIndex e → ℝ),
                ‖χ.selectedCFZCanonicalArchimedeanBaseline e tu‖
                ∂(volume.prod volume))
            atTop
            (𝓝
              (∫ tu :
                  (SelectedCFZFormIndex e → ℝ) ×
                    (SelectedCFZFormIndex e → ℝ),
                ‖χ.selectedCFZCanonicalArchimedeanBaseline e tu‖
                ∂(volume.prod volume)))))
  have hcomplete :=
    χ.tendsto_selectedCFZCanonicalCompleteEulerScaledTailNorm_sqrt_log
      hk Nseq wseq bseq Rseq hN hbound hcoprime hRseq e
  have hbaseline :=
    χ.tendsto_norm_integral_selectedCFZCanonicalArchimedeanBaseline_compl_sqrt_log
      Rseq hRseq e
  have hupper :
      Tendsto
        (fun n : ℕ =>
          letI : NeZero (Nseq n) := ⟨hN n⟩
          δ n *
              ∫ tu :
                  (SelectedCFZFormIndex e → ℝ) ×
                    (SelectedCFZFormIndex e → ℝ),
                ‖χ.selectedCFZCanonicalArchimedeanBaseline e tu‖
                ∂(volume.prod volume) +
            χ.selectedCFZCanonicalCompleteEulerScaledTailNorm
              (N := Nseq n) (wseq n) (bseq n) (Rseq n) e
              (Real.sqrt (Real.log (Rseq n))) +
            ‖∫ tu in
                (SmoothSieveCutoff.selectedCFZPairedFourierBox e
                  (Real.sqrt (Real.log (Rseq n))))ᶜ,
              χ.selectedCFZCanonicalArchimedeanBaseline e tu
              ∂(volume.prod volume)‖)
        atTop (𝓝 0) := by
    simpa only [zero_add] using
      (hδmass.add hcomplete).add hbaseline
  apply tendsto_iff_norm_sub_tendsto_zero.2
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall fun n => by
      letI : NeZero (Nseq n) := ⟨hN n⟩
      exact norm_nonneg _
  · filter_upwards [hRtwo, hδnonneg, hinterior] with
      n hRn hδn hinteriorn
    letI : NeZero (Nseq n) := ⟨hN n⟩
    exact
      χ.norm_selectedCFZCanonicalEulerFourierMainTerm_sub_one_le_of_interior
        (N := Nseq n) hk (hbound n) (hcoprime n) e hRn
        hδn hinteriorn
  · exact hupper

end Wikipedia.SzemeredisTheorem
