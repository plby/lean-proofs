import Wikipedia.GreenTao.Sieve.CFZCanonicalCompleteMainTermBridge
import Wikipedia.GreenTao.Sieve.CFZCanonicalCarryFourierNormalization

/-!
# Interior comparison for the canonical carry average

The complete canonical Euler integrand is a probability-weighted average
over the canonical carry vectors.  Exact normalization of each arbitrary
carry vector separates its contribution into three factors:

* the normalized archimedean baseline;
* a finite correction common to every carry vector;
* the carry-dependent large-prime Euler correction.

This file factors the complete scaled integrand accordingly.  Since the
canonical carry densities are nonnegative and sum to one, a uniform bound
for every arbitrary-carry large-prime correction passes directly to their
weighted average.  No realizability split is needed for zero-density carry
vectors.
-/

namespace Wikipedia.SzemeredisTheorem

open MeasureTheory
open scoped BigOperators

/-! ## The common correction and the carry-weighted large-prime average -/

/-- The normalized finite correction shared by every canonical carry
vector at fixed Fourier frequencies. -/
noncomputable def selectedCFZCanonicalCommonFiniteCorrection
    {κ : Type*} [Fintype κ]
    (R w : ℕ) (t u : κ → ℝ) : ℂ :=
  normalizedSmallPrimeZetaCorrection R w t u *
    cutoffZetaSystemFactor R t u

/-- Package an arbitrary canonical carry vector at the displayed
parameters. -/
def selectedCFZCanonicalCarryFourierDataAt
    {k N : ℕ} [NeZero N]
    (w b R : ℕ) (e : LinearFormsExponent k)
    (carry : SelectedCFZFormIndex e → ℤ)
    (t u : SelectedCFZFormIndex e → ℝ) :
    SelectedCFZCanonicalCarryFourierData k where
  N := N
  N_neZero := inferInstance
  R := R
  w := w
  b := b
  e := e
  carry := carry
  t := t
  u := u

/-- Probability-weighted average of the arbitrary-carry large-prime
corrections. -/
noncomputable def selectedCFZCanonicalCarryLargePrimeCorrectionAverage
    {k N : ℕ} [NeZero N]
    (w b R : ℕ) (e : LinearFormsExponent k)
    (t u : SelectedCFZFormIndex e → ℝ) : ℂ :=
  ∑ carry ∈ cfzCanonicalCarryVectorChoices
      (SelectedCFZFormIndex e) k,
    (cfzCanonicalCarryCellDensity
        (N := N)
        (fun q : SelectedCFZFormIndex e => q.1)
        carry : ℂ) *
      (selectedCFZCanonicalCarryFourierDataAt
        (N := N) w b R e carry t u).largePrimeEulerCorrection

/-! ## Exact factorization -/

/-- Exact normalized identity for one arbitrary carry vector, rewritten
with the common finite correction separated from its large-prime
correction. -/
theorem
    SmoothSieveCutoff.selectedCFZCanonicalCarryScaledCompletePrimeSupport_eq
    {k N : ℕ} [NeZero N]
    (χ : SmoothSieveCutoff)
    (hk : 2 ≤ k)
    (w b R : ℕ)
    (hw : wTrickedCFZComplexExceptionalBound k ≤ w)
    (hwb : (primorial w).Coprime b)
    (e : LinearFormsExponent k)
    (carry : SelectedCFZFormIndex e → ℤ)
    (t u : SelectedCFZFormIndex e → ℝ)
    (hR : 2 ≤ R) :
    (normalizedSelbergScale χ.normalizer R
          (primorial w) : ℂ) ^
            Fintype.card (SelectedCFZFormIndex e) *
        (((Real.log R ^ 2 : ℝ) : ℂ) ^
            Fintype.card (SelectedCFZFormIndex e) *
          (pairedCutoffFourierEnvelope χ t u *
            cfzCanonicalCarryCompletePrimeSupportSeries
              N (primorial w) b R
              (fun q : SelectedCFZFormIndex e => q.1)
              carry t u)) =
      χ.selectedCFZCanonicalArchimedeanBaseline e (t, u) *
        selectedCFZCanonicalCommonFiniteCorrection R w t u *
        (selectedCFZCanonicalCarryFourierDataAt
          (N := N) w b R e carry t u).largePrimeEulerCorrection := by
  let d :=
    selectedCFZCanonicalCarryFourierDataAt
      (N := N) w b R e carry t u
  have hnormalized :=
    normalizedSelberg_fourier_canonicalCarryCompletePrimeSupportSeries_eq
      hk χ d hR hw hwb
  calc
    _ =
        χ.selectedCFZCanonicalArchimedeanBaseline e (t, u) *
          normalizedCompletedFourierEulerCorrection
            R w t u
            (selectedCFZCanonicalCarryFourierDataAt
              (N := N) w b R e carry t u).largePrimeEulerCorrection := by
      convert hnormalized using 1 <;>
        simp only [
          d,
          selectedCFZCanonicalCarryFourierDataAt,
          SelectedCFZCanonicalCarryFourierData.completePrimeSupportSeries,
          SmoothSieveCutoff.selectedCFZCanonicalArchimedeanBaseline] <;>
        rfl
    _ = _ := by
      unfold
        normalizedCompletedFourierEulerCorrection
        selectedCFZCanonicalCommonFiniteCorrection
      ring

/-- Exact factorization of the complete scaled integrand into its
archimedean baseline, the common finite correction, and the
carry-density-weighted average of arbitrary-carry large-prime
corrections. -/
theorem
    SmoothSieveCutoff.selectedCFZCanonicalCompleteEulerScaledIntegrand_eq_baseline_mul_corrections
    {k N : ℕ} [NeZero N]
    (χ : SmoothSieveCutoff)
    (hk : 2 ≤ k)
    (w b R : ℕ)
    (hw : wTrickedCFZComplexExceptionalBound k ≤ w)
    (hwb : (primorial w).Coprime b)
    (e : LinearFormsExponent k)
    (tu :
      (SelectedCFZFormIndex e → ℝ) ×
        (SelectedCFZFormIndex e → ℝ))
    (hR : 2 ≤ R) :
    χ.selectedCFZCanonicalCompleteEulerScaledIntegrand
        (N := N) w b R e tu =
      χ.selectedCFZCanonicalArchimedeanBaseline e tu *
        selectedCFZCanonicalCommonFiniteCorrection
          R w tu.1 tu.2 *
        selectedCFZCanonicalCarryLargePrimeCorrectionAverage
          (N := N) w b R e tu.1 tu.2 := by
  classical
  unfold
    SmoothSieveCutoff.selectedCFZCanonicalCompleteEulerScaledIntegrand
    SmoothSieveCutoff.cfzCanonicalCarryCompleteEulerIntegrand
    cfzCanonicalCarryCompleteFourierAverage
    selectedCFZCanonicalCarryLargePrimeCorrectionAverage
  calc
    (normalizedSelbergScale χ.normalizer R
          (primorial w) : ℂ) ^
            Fintype.card (SelectedCFZFormIndex e) *
        (((Real.log R ^ 2 : ℝ) : ℂ) ^
            Fintype.card (SelectedCFZFormIndex e) *
          (pairedCutoffFourierEnvelope χ tu.1 tu.2 *
            ∑ carry ∈ cfzCanonicalCarryVectorChoices
                (SelectedCFZFormIndex e) k,
              (cfzCanonicalCarryCellDensity
                  (N := N)
                  (fun q : SelectedCFZFormIndex e => q.1)
                  carry : ℂ) *
                cfzCanonicalCarryCompletePrimeSupportSeries
                  N (primorial w) b R
                  (fun q : SelectedCFZFormIndex e => q.1)
                  carry tu.1 tu.2)) =
      ∑ carry ∈ cfzCanonicalCarryVectorChoices
          (SelectedCFZFormIndex e) k,
        (cfzCanonicalCarryCellDensity
            (N := N)
            (fun q : SelectedCFZFormIndex e => q.1)
            carry : ℂ) *
          ((normalizedSelbergScale χ.normalizer R
                (primorial w) : ℂ) ^
                  Fintype.card (SelectedCFZFormIndex e) *
              (((Real.log R ^ 2 : ℝ) : ℂ) ^
                  Fintype.card (SelectedCFZFormIndex e) *
                (pairedCutoffFourierEnvelope χ tu.1 tu.2 *
                  cfzCanonicalCarryCompletePrimeSupportSeries
                    N (primorial w) b R
                    (fun q : SelectedCFZFormIndex e => q.1)
                    carry tu.1 tu.2))) := by
      rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro carry _hcarry
      ring
    _ =
      ∑ carry ∈ cfzCanonicalCarryVectorChoices
          (SelectedCFZFormIndex e) k,
        (cfzCanonicalCarryCellDensity
            (N := N)
            (fun q : SelectedCFZFormIndex e => q.1)
            carry : ℂ) *
          (χ.selectedCFZCanonicalArchimedeanBaseline e tu *
            selectedCFZCanonicalCommonFiniteCorrection
              R w tu.1 tu.2 *
            (selectedCFZCanonicalCarryFourierDataAt
              (N := N) w b R e carry
              tu.1 tu.2).largePrimeEulerCorrection) := by
      apply Finset.sum_congr rfl
      intro carry _hcarry
      rw [
        χ.selectedCFZCanonicalCarryScaledCompletePrimeSupport_eq
          (N := N) hk w b R hw hwb e carry tu.1 tu.2 hR]
    _ =
      χ.selectedCFZCanonicalArchimedeanBaseline e tu *
        selectedCFZCanonicalCommonFiniteCorrection
          R w tu.1 tu.2 *
        ∑ carry ∈ cfzCanonicalCarryVectorChoices
            (SelectedCFZFormIndex e) k,
          (cfzCanonicalCarryCellDensity
              (N := N)
              (fun q : SelectedCFZFormIndex e => q.1)
              carry : ℂ) *
            (selectedCFZCanonicalCarryFourierDataAt
              (N := N) w b R e carry
              tu.1 tu.2).largePrimeEulerCorrection := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro carry _hcarry
      ring

/-! ## Probability-average and product estimates -/

/-- A convex combination of complex corrections which are uniformly
`ε`-close to one is itself `ε`-close to one. -/
theorem norm_nonnegWeightedAverage_sub_one_le
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι)
    (weight : ι → ℝ)
    (correction : ι → ℂ)
    {ε : ℝ}
    (hweight : ∀ i ∈ s, 0 ≤ weight i)
    (hsum : ∑ i ∈ s, weight i = 1)
    (hclose : ∀ i ∈ s, ‖correction i - 1‖ ≤ ε) :
    ‖(∑ i ∈ s, (weight i : ℂ) * correction i) - 1‖ ≤ ε := by
  have hsumComplex :
      (∑ i ∈ s, (weight i : ℂ)) = 1 := by
    exact_mod_cast hsum
  have hrecenter :
      (∑ i ∈ s, (weight i : ℂ) * correction i) - 1 =
        ∑ i ∈ s,
          (weight i : ℂ) * (correction i - 1) := by
    calc
      (∑ i ∈ s, (weight i : ℂ) * correction i) - 1 =
          (∑ i ∈ s, (weight i : ℂ) * correction i) -
            ∑ i ∈ s, (weight i : ℂ) := by
        rw [hsumComplex]
      _ =
          ∑ i ∈ s,
            ((weight i : ℂ) * correction i -
              (weight i : ℂ)) := by
        rw [Finset.sum_sub_distrib]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i _hi
        ring
  rw [hrecenter]
  calc
    ‖∑ i ∈ s,
        (weight i : ℂ) * (correction i - 1)‖ ≤
        ∑ i ∈ s,
          ‖(weight i : ℂ) * (correction i - 1)‖ :=
      norm_sum_le _ _
    _ ≤
        ∑ i ∈ s, weight i * ε := by
      apply Finset.sum_le_sum
      intro i hi
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (hweight i hi)]
      exact
        mul_le_mul_of_nonneg_left
          (hclose i hi) (hweight i hi)
    _ = ε := by
      rw [← Finset.sum_mul, hsum, one_mul]

/-- Uniform arbitrary-carry control passes unchanged to the canonical
carry-density-weighted large-prime average.  The estimate is requested for
every carry vector, so zero-density vectors require no special case. -/
theorem
    norm_selectedCFZCanonicalCarryLargePrimeCorrectionAverage_sub_one_le
    {k N : ℕ} [NeZero N]
    (w b R : ℕ) (e : LinearFormsExponent k)
    (t u : SelectedCFZFormIndex e → ℝ)
    {εL : ℝ}
    (hlarge :
      ∀ carry : SelectedCFZFormIndex e → ℤ,
        ‖(selectedCFZCanonicalCarryFourierDataAt
              (N := N) w b R e carry t u).largePrimeEulerCorrection -
            1‖ ≤ εL) :
    ‖selectedCFZCanonicalCarryLargePrimeCorrectionAverage
          (N := N) w b R e t u - 1‖ ≤ εL := by
  classical
  unfold selectedCFZCanonicalCarryLargePrimeCorrectionAverage
  apply
    norm_nonnegWeightedAverage_sub_one_le
      (cfzCanonicalCarryVectorChoices
        (SelectedCFZFormIndex e) k)
      (fun carry =>
        cfzCanonicalCarryCellDensity
          (N := N)
          (fun q : SelectedCFZFormIndex e => q.1)
          carry)
      (fun carry =>
        (selectedCFZCanonicalCarryFourierDataAt
          (N := N) w b R e carry t u).largePrimeEulerCorrection)
  · intro carry _hcarry
    exact
      cfzCanonicalCarryCellDensity_nonneg
        (N := N)
        (fun q : SelectedCFZFormIndex e => q.1)
        carry
  · exact
      sum_cfzCanonicalCarryCellDensity_eq_one
        (N := N)
        (fun q : SelectedCFZFormIndex e => q.1)
  · intro carry _hcarry
    exact hlarge carry

/-- The existing arbitrary-carry Euler-tail theorem therefore controls
the entire carry average uniformly in every datum other than the ambient
number of forms. -/
theorem
    exists_uniform_cutoff_selectedCFZCanonicalCarryLargePrimeCorrectionAverage_close_one
    {k : ℕ} (hk : 2 ≤ k)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ w₀ : ℕ,
      ∀ {N : ℕ} [NeZero N]
        (w b R : ℕ) (e : LinearFormsExponent k)
        (t u : SelectedCFZFormIndex e → ℝ),
        w₀ ≤ w →
        2 ≤ R →
        ‖selectedCFZCanonicalCarryLargePrimeCorrectionAverage
              (N := N) w b R e t u - 1‖ < ε := by
  obtain ⟨w₀, hcutoff⟩ :=
    exists_uniform_cutoff_selectedCFZCanonicalCarryLargePrimeEulerCorrection_close_one
      hk (half_pos hε)
  refine ⟨w₀, ?_⟩
  intro N _inst w b R e t u hw hR
  have havg :
      ‖selectedCFZCanonicalCarryLargePrimeCorrectionAverage
            (N := N) w b R e t u - 1‖ ≤ ε / 2 := by
    apply
      norm_selectedCFZCanonicalCarryLargePrimeCorrectionAverage_sub_one_le
        (N := N) w b R e t u
    intro carry
    exact
      (hcutoff
        (selectedCFZCanonicalCarryFourierDataAt
          (N := N) w b R e carry t u)
        hw hR).le
  exact havg.trans_lt (half_lt_self hε)

/-- Multiplying two corrections respectively `εf`- and `εL`-close to one
costs at most `εf + εL + εf * εL`. -/
theorem norm_mul_sub_one_le_add_add_mul
    (finiteCorrection largeCorrection : ℂ)
    {εf εL : ℝ}
    (hεf : 0 ≤ εf)
    (_hεL : 0 ≤ εL)
    (hfinite :
      ‖finiteCorrection - 1‖ ≤ εf)
    (hlarge :
      ‖largeCorrection - 1‖ ≤ εL) :
    ‖finiteCorrection * largeCorrection - 1‖ ≤
      εf + εL + εf * εL := by
  have hproduct :
      ‖(finiteCorrection - 1) *
          (largeCorrection - 1)‖ ≤
        εf * εL := by
    rw [norm_mul]
    exact
      mul_le_mul hfinite hlarge
        (norm_nonneg _) hεf
  calc
    ‖finiteCorrection * largeCorrection - 1‖ =
        ‖(finiteCorrection - 1) *
              (largeCorrection - 1) +
            (finiteCorrection - 1) +
            (largeCorrection - 1)‖ := by
      congr 1
      ring
    _ ≤
        ‖(finiteCorrection - 1) *
              (largeCorrection - 1) +
            (finiteCorrection - 1)‖ +
          ‖largeCorrection - 1‖ :=
      norm_add_le _ _
    _ ≤
        (‖(finiteCorrection - 1) *
              (largeCorrection - 1)‖ +
            ‖finiteCorrection - 1‖) +
          ‖largeCorrection - 1‖ :=
      add_le_add
        (norm_add_le _ _) le_rfl
    _ ≤
        (εf * εL + εf) + εL :=
      add_le_add
        (add_le_add hproduct hfinite) hlarge
    _ = εf + εL + εf * εL := by
      ring

/-! ## The baseline-relative interior comparison -/

/-- Clean pointwise interior estimate for the canonical carry average.
It uses only a common finite-correction estimate and a uniform
arbitrary-carry large-prime estimate. -/
theorem
    SmoothSieveCutoff.norm_selectedCFZCanonicalCompleteEulerScaledIntegrand_sub_baseline_le
    {k N : ℕ} [NeZero N]
    (χ : SmoothSieveCutoff)
    (hk : 2 ≤ k)
    (w b R : ℕ)
    (hw : wTrickedCFZComplexExceptionalBound k ≤ w)
    (hwb : (primorial w).Coprime b)
    (e : LinearFormsExponent k)
    (tu :
      (SelectedCFZFormIndex e → ℝ) ×
        (SelectedCFZFormIndex e → ℝ))
    (hR : 2 ≤ R)
    {εf εL : ℝ}
    (hεf : 0 ≤ εf)
    (hεL : 0 ≤ εL)
    (hfinite :
      ‖selectedCFZCanonicalCommonFiniteCorrection
            R w tu.1 tu.2 - 1‖ ≤ εf)
    (hlarge :
      ∀ carry : SelectedCFZFormIndex e → ℤ,
        ‖(selectedCFZCanonicalCarryFourierDataAt
              (N := N) w b R e carry
              tu.1 tu.2).largePrimeEulerCorrection -
            1‖ ≤ εL) :
    ‖χ.selectedCFZCanonicalCompleteEulerScaledIntegrand
          (N := N) w b R e tu -
        χ.selectedCFZCanonicalArchimedeanBaseline e tu‖ ≤
      (εf + εL + εf * εL) *
        ‖χ.selectedCFZCanonicalArchimedeanBaseline e tu‖ := by
  let finiteCorrection :=
    selectedCFZCanonicalCommonFiniteCorrection
      R w tu.1 tu.2
  let largeCorrection :=
    selectedCFZCanonicalCarryLargePrimeCorrectionAverage
      (N := N) w b R e tu.1 tu.2
  have hlargeAverage :
      ‖largeCorrection - 1‖ ≤ εL := by
    exact
      norm_selectedCFZCanonicalCarryLargePrimeCorrectionAverage_sub_one_le
        (N := N) w b R e tu.1 tu.2 hlarge
  have hcorrection :
      ‖finiteCorrection * largeCorrection - 1‖ ≤
        εf + εL + εf * εL :=
    norm_mul_sub_one_le_add_add_mul
      finiteCorrection largeCorrection hεf hεL hfinite hlargeAverage
  rw [
    χ.selectedCFZCanonicalCompleteEulerScaledIntegrand_eq_baseline_mul_corrections
      (N := N) hk w b R hw hwb e tu hR]
  change
    ‖χ.selectedCFZCanonicalArchimedeanBaseline e tu *
          finiteCorrection * largeCorrection -
        χ.selectedCFZCanonicalArchimedeanBaseline e tu‖ ≤
      (εf + εL + εf * εL) *
        ‖χ.selectedCFZCanonicalArchimedeanBaseline e tu‖
  calc
    ‖χ.selectedCFZCanonicalArchimedeanBaseline e tu *
          finiteCorrection * largeCorrection -
        χ.selectedCFZCanonicalArchimedeanBaseline e tu‖ =
      ‖χ.selectedCFZCanonicalArchimedeanBaseline e tu *
          (finiteCorrection * largeCorrection - 1)‖ := by
        congr 1
        ring
    _ =
        ‖χ.selectedCFZCanonicalArchimedeanBaseline e tu‖ *
          ‖finiteCorrection * largeCorrection - 1‖ := by
      rw [norm_mul]
    _ ≤
        ‖χ.selectedCFZCanonicalArchimedeanBaseline e tu‖ *
          (εf + εL + εf * εL) :=
      mul_le_mul_of_nonneg_left
        hcorrection (norm_nonneg _)
    _ = _ := by
      ring

end Wikipedia.SzemeredisTheorem
