import Wikipedia.GreenTao.FinalTransferenceAssembly
import Wikipedia.GreenTao.Sieve.CFZCanonicalCarryAverageInterior
import Wikipedia.GreenTao.Sieve.CFZUniformFiniteFourierCorrection
import Wikipedia.GreenTao.Sieve.CyclicMajorantSchedule
import Wikipedia.GreenTao.Sieve.ReducedResidueCyclicLinearFormsAssembly

/-!
# The standard cyclic Selberg majorant satisfies the linear-forms condition

This file closes the smooth-sieve input to Green--Tao transference.  Given
a requested error, the primorial cutoff is chosen first so that it covers
the canonical exceptional primes and the uniform arbitrary-carry
large-prime Euler tail.  Only after fixing that cutoff does the cyclic
modulus tend to infinity.

The finite Fourier correction is uniform on the growing box

`T = sqrt (log (sieveLevel k (M + 1)))`.

The complete canonical main term is compared with one through the
baseline-relative interior estimate and the two complementary Fourier
tails.  The cyclic boundary is then added by a final triangle inequality,
followed by finite intersection over the reduced residues and Boolean
selected exponents.
-/

namespace Wikipedia.SzemeredisTheorem

open Filter MeasureTheory Topology
open scoped BigOperators

/-- The standard smooth cyclic Selberg majorant satisfies the exact
linear-forms interface consumed by final Green--Tao transference. -/
theorem hasStandardCyclicMajorantLinearForms :
    HasStandardCyclicMajorantLinearForms := by
  classical
  intro k hk η hη
  let χ := standardSmoothSieveCutoff
  let baselineMass : LinearFormsExponent k → ℝ :=
    fun e =>
      ∫ tu :
          (SelectedCFZFormIndex e → ℝ) ×
            (SelectedCFZFormIndex e → ℝ),
        ‖χ.selectedCFZCanonicalArchimedeanBaseline e tu‖
        ∂(volume.prod volume)
  let baselineMassBound : ℝ :=
    1 + ∑ e : LinearFormsExponent k, baselineMass e
  have hmassNonneg :
      ∀ e : LinearFormsExponent k, 0 ≤ baselineMass e := by
    intro e
    dsimp [baselineMass]
    exact integral_nonneg fun _tu => norm_nonneg _
  have hmassBoundPos : 0 < baselineMassBound := by
    have hsum :
        0 ≤ ∑ e : LinearFormsExponent k, baselineMass e :=
      Finset.sum_nonneg fun e _he => hmassNonneg e
    dsimp [baselineMassBound]
    linarith
  have hmassLe :
      ∀ e : LinearFormsExponent k,
        baselineMass e ≤ baselineMassBound := by
    intro e
    have hsingle :
        baselineMass e ≤
          ∑ e' : LinearFormsExponent k, baselineMass e' := by
      exact
        Finset.single_le_sum
          (fun e' _he' => hmassNonneg e')
          (Finset.mem_univ e)
    dsimp [baselineMassBound]
    linarith
  let correctionError : ℝ :=
    η / (18 * baselineMassBound + η)
  have hdenominator :
      0 < 18 * baselineMassBound + η := by
    nlinarith
  have hcorrectionError :
      0 < correctionError := by
    exact div_pos hη hdenominator
  have hcorrectionErrorNonneg :
      0 ≤ correctionError :=
    hcorrectionError.le
  have hcorrectionErrorLeOne :
      correctionError ≤ 1 := by
    dsimp [correctionError]
    exact
      (div_le_one hdenominator).2
        (by nlinarith [hmassBoundPos])
  let interiorError : ℝ :=
    correctionError + correctionError +
      correctionError * correctionError
  have hcorrectionSquare :
      correctionError * correctionError ≤ correctionError := by
    have hproduct :
        0 ≤ correctionError * (1 - correctionError) :=
      mul_nonneg hcorrectionErrorNonneg
        (sub_nonneg.mpr hcorrectionErrorLeOne)
    nlinarith
  have hinteriorErrorNonneg :
      0 ≤ interiorError := by
    dsimp [interiorError]
    positivity
  have hinteriorErrorLe :
      interiorError ≤ 3 * correctionError := by
    dsimp [interiorError]
    nlinarith
  have hthreeCorrectionMass :
      3 * correctionError * baselineMassBound ≤ η / 6 := by
    have hnumerator :
        18 * η * baselineMassBound ≤
          η * (18 * baselineMassBound + η) := by
      nlinarith [sq_nonneg η]
    have hquotient :
        (18 * η * baselineMassBound) /
              (18 * baselineMassBound + η) ≤
            η :=
      (div_le_iff₀ hdenominator).2 hnumerator
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 6)]
    calc
      3 * correctionError * baselineMassBound * 6 =
          (18 * η * baselineMassBound) /
            (18 * baselineMassBound + η) := by
        dsimp [correctionError]
        ring
      _ ≤ η := hquotient
  have hinteriorMass :
      ∀ e : LinearFormsExponent k,
        interiorError * baselineMass e ≤ η / 6 := by
    intro e
    calc
      interiorError * baselineMass e ≤
          (3 * correctionError) * baselineMass e :=
        mul_le_mul_of_nonneg_right
          hinteriorErrorLe (hmassNonneg e)
      _ ≤
          3 * correctionError * baselineMassBound :=
        mul_le_mul_of_nonneg_left
          (hmassLe e)
          (mul_nonneg (by norm_num) hcorrectionErrorNonneg)
      _ ≤ η / 6 := hthreeCorrectionMass
  have hkTwo : 2 ≤ k := by omega
  obtain ⟨largePrimeCutoff, hlargePrime⟩ :=
    exists_uniform_cutoff_selectedCFZCanonicalCarryLargePrimeEulerCorrection_close_one
      hkTwo hcorrectionError
  let w : ℕ :=
    max 2
      (max
        (wTrickedCFZComplexExceptionalBound k)
        largePrimeCutoff)
  have hwTwo : 2 ≤ w := by
    exact le_max_left _ _
  have hwCanonical :
      wTrickedCFZComplexExceptionalBound k ≤ w := by
    exact
      (le_max_left
        (wTrickedCFZComplexExceptionalBound k)
        largePrimeCutoff).trans
        (le_max_right 2 _)
  have hwLarge : largePrimeCutoff ≤ w := by
    exact
      (le_max_right
        (wTrickedCFZComplexExceptionalBound k)
        largePrimeCutoff).trans
        (le_max_right 2 _)
  have hwExceptional :
      exceptionalPrimeBound
          (fun q : CFZFormIndex k => cfzAffineForm q) ≤ w := by
    exact
      (le_max_left
        (exceptionalPrimeBound
          (fun q : CFZFormIndex k => cfzAffineForm q))
        (complexZetaModelNonzeroCutoff
          (Fintype.card (CFZFormIndex k)))).trans
        hwCanonical
  let Nseq : ℕ → ℕ := fun M => M + 1
  let Rseq : ℕ → ℕ :=
    fun M => sieveLevel k (M + 1)
  have hRseq : Tendsto Rseq atTop atTop := by
    exact
      (tendsto_sieveLevel_atTop hk).comp
        (tendsto_add_atTop_nat 1)
  have hRtwo :
      ∀ᶠ M : ℕ in atTop, 2 ≤ Rseq M :=
    hRseq.eventually (eventually_ge_atTop 2)
  have hfiniteN :=
    eventually_uniform_selectedCFZFiniteFourierCorrection_sieveLevel
      hk hwCanonical hcorrectionError
  have hfinite :
      ∀ᶠ M : ℕ in atTop,
        ∀ e : LinearFormsExponent k,
          ∀ tu ∈
              SmoothSieveCutoff.selectedCFZPairedFourierBox e
                (Real.sqrt (Real.log (Rseq M))),
            ‖selectedCFZCanonicalCommonFiniteCorrection
                  (Rseq M) w tu.1 tu.2 -
                1‖ < correctionError := by
    have hshift :=
      (tendsto_add_atTop_nat 1).eventually hfiniteN
    simpa only [Rseq, Nseq,
      selectedCFZCanonicalCommonFiniteCorrection] using hshift
  refine ⟨w, hwExceptional, ?_⟩
  let ν :
      (M : ℕ) → ℕ → ZMod (M + 1) → ℝ :=
    fun M b =>
      χ.cyclicMajorant
        (sieveLevel k (M + 1))
        (primorial w) b
  let canonicalMainTerm :
      ℕ → ℕ → LinearFormsExponent k → ℂ :=
    fun M b e =>
      letI : NeZero (M + 1) := ⟨Nat.succ_ne_zero M⟩
      χ.selectedCFZCanonicalEulerFourierMainTerm
        (N := M + 1)
        (sieveLevel k (M + 1))
        (primorial w) b e
  have hcyclic :
      ∀ b, b ∈ reducedResidues (primorial w) →
        ∀ e : LinearFormsExponent k,
          ∀ᶠ M : ℕ in atTop,
            ‖(mean
                  (linearFormsProduct k (M + 1)
                    (ν M b) e) : ℂ) -
                canonicalMainTerm M b e‖ ≤ η / 2 := by
    intro b hb e
    have hcoprime :
        (primorial w).Coprime b :=
      (mem_reducedResidues.mp hb).2
    have hprimorialTwo : 2 ≤ primorial w := by
      simpa using primorial_mono hwTwo
    have hbPos : 0 < b := by
      apply Nat.pos_of_ne_zero
      intro hbZero
      subst b
      have hprimorialOne : primorial w = 1 := by
        simpa using hcoprime
      omega
    have hboundary :=
      χ.tendsto_norm_cyclicMajorant_sub_canonicalEulerFourierMainTerm_sieveLevel
        (w := w) hk hbPos e
    have hclose :=
      (Metric.tendsto_nhds.mp hboundary)
        (η / 2) (half_pos hη)
    filter_upwards [hclose] with M hM
    have hM' :
        |‖(mean
              (linearFormsProduct k (M + 1)
                (χ.cyclicMajorant
                  (sieveLevel k (M + 1))
                  (primorial w) b) e) : ℂ) -
            χ.selectedCFZCanonicalEulerFourierMainTerm
              (N := M + 1)
              (sieveLevel k (M + 1))
              (primorial w) b e‖| < η / 2 := by
      simpa only [Real.dist_eq, sub_zero] using hM
    simpa only [ν, canonicalMainTerm,
      abs_of_nonneg (norm_nonneg _)] using hM'.le
  have hmainTerm :
      ∀ b, b ∈ reducedResidues (primorial w) →
        ∀ e : LinearFormsExponent k,
          ∀ᶠ M : ℕ in atTop,
            ‖canonicalMainTerm M b e - 1‖ ≤ η / 2 := by
    intro b hb e
    have hcoprime :
        (primorial w).Coprime b :=
      (mem_reducedResidues.mp hb).2
    have hcomplete :=
      χ.tendsto_selectedCFZCanonicalCompleteEulerScaledTailNorm_sqrt_log
        hkTwo
        Nseq (fun _M => w) (fun _M => b) Rseq
        (fun M => Nat.succ_ne_zero M)
        (fun _M => hwExceptional)
        (fun _M => hcoprime)
        hRseq e
    have hcompleteClose :
        ∀ᶠ M : ℕ in atTop,
          χ.selectedCFZCanonicalCompleteEulerScaledTailNorm
              (N := Nseq M) w b (Rseq M) e
              (Real.sqrt (Real.log (Rseq M))) ≤
            η / 6 := by
      have hclose :=
        (Metric.tendsto_nhds.mp hcomplete)
          (η / 6) (by positivity)
      filter_upwards [hclose] with M hM
      have hM' :
          |χ.selectedCFZCanonicalCompleteEulerScaledTailNorm
              (N := Nseq M) w b (Rseq M) e
              (Real.sqrt (Real.log (Rseq M)))| < η / 6 := by
        simpa only [Real.dist_eq, sub_zero] using hM
      exact (le_abs_self _).trans hM'.le
    have hbaseline :=
      χ.tendsto_norm_integral_selectedCFZCanonicalArchimedeanBaseline_compl_sqrt_log
        Rseq hRseq e
    have hbaselineClose :
        ∀ᶠ M : ℕ in atTop,
          ‖∫ tu in
              (SmoothSieveCutoff.selectedCFZPairedFourierBox e
                (Real.sqrt (Real.log (Rseq M))))ᶜ,
            χ.selectedCFZCanonicalArchimedeanBaseline e tu
            ∂(volume.prod volume)‖ ≤
          η / 6 := by
      have hclose :=
        (Metric.tendsto_nhds.mp hbaseline)
          (η / 6) (by positivity)
      filter_upwards [hclose] with M hM
      have hM' :
          |‖∫ tu in
              (SmoothSieveCutoff.selectedCFZPairedFourierBox e
                (Real.sqrt (Real.log (Rseq M))))ᶜ,
            χ.selectedCFZCanonicalArchimedeanBaseline e tu
            ∂(volume.prod volume)‖| < η / 6 := by
        simpa only [Real.dist_eq, sub_zero] using hM
      simpa only [abs_of_nonneg (norm_nonneg _)] using hM'.le
    filter_upwards
        [hRtwo, hfinite, hcompleteClose, hbaselineClose] with
      M hRM hfiniteM hcompleteM hbaselineM
    letI : NeZero (Nseq M) := ⟨Nat.succ_ne_zero M⟩
    have hinterior :
        ∀ tu ∈
            SmoothSieveCutoff.selectedCFZPairedFourierBox e
              (Real.sqrt (Real.log (Rseq M))),
          ‖χ.selectedCFZCanonicalCompleteEulerScaledIntegrand
                (N := Nseq M) w b (Rseq M) e tu -
              χ.selectedCFZCanonicalArchimedeanBaseline e tu‖ ≤
            interiorError *
              ‖χ.selectedCFZCanonicalArchimedeanBaseline e tu‖ := by
      intro tu htu
      apply
        χ.norm_selectedCFZCanonicalCompleteEulerScaledIntegrand_sub_baseline_le
          hkTwo w b (Rseq M) hwCanonical hcoprime e tu hRM
          hcorrectionErrorNonneg hcorrectionErrorNonneg
      · exact
          (by
            simpa only [
              selectedCFZCanonicalCommonFiniteCorrection] using
              (hfiniteM e tu htu).le)
      · intro carry
        exact
          (hlargePrime
            (selectedCFZCanonicalCarryFourierDataAt
              (N := Nseq M) w b (Rseq M) e carry
              tu.1 tu.2)
            hwLarge hRM).le
    have hmain :=
      χ.norm_selectedCFZCanonicalEulerFourierMainTerm_sub_one_le_of_interior
        (N := Nseq M) hkTwo hwExceptional hcoprime e hRM
        hinteriorErrorNonneg hinterior
    have hmassIdentity :
        (∫ tu :
            (SelectedCFZFormIndex e → ℝ) ×
              (SelectedCFZFormIndex e → ℝ),
          ‖χ.selectedCFZCanonicalArchimedeanBaseline e tu‖
          ∂(volume.prod volume)) =
        baselineMass e := by
      rfl
    rw [hmassIdentity] at hmain
    have hinteriorM := hinteriorMass e
    have hbound :
        ‖χ.selectedCFZCanonicalEulerFourierMainTerm
              (N := Nseq M) (Rseq M)
              (primorial w) b e -
            1‖ ≤ η / 2 := by
      exact hmain.trans (by linarith)
    simpa only [canonicalMainTerm, Nseq, Rseq] using hbound
  have hassembly :=
    eventually_reducedResidues_hasLinearFormsCondition_of_eventually_complex_triangle_error_le
      ν canonicalMainTerm
      (cyclicError := η / 2)
      (mainTermError := η / 2)
      hcyclic hmainTerm
  have hhalf : η / 2 + η / 2 = η := by
    ring
  simpa only [ν, χ, hhalf] using hassembly

end Wikipedia.SzemeredisTheorem
