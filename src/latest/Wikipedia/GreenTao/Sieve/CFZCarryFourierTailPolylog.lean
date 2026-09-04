import Wikipedia.GreenTao.Sieve.CFZCarryHarmonicLcmEulerBound
import Wikipedia.GreenTao.Sieve.PrimeHarmonicProductBound

/-!
# Polylogarithmic closure of the carry Fourier tail

The harmonic LCM mass is bounded by a finite prime product.  The latter is
polylogarithmic, while the cutoff Fourier transform is Schwartz.  This file
makes the quantitative comparison explicit.

For every natural `q`, a finite constant controls

`T ^ q * selectedCFZPairedFourierAbsoluteTail e T`.

Choosing `q` larger than twice the exponent of the prime-product bound makes
the complementary carry Fourier integral vanish at
`T = sqrt (log R)`, without an eventual bounded-mass hypothesis.
-/

namespace Wikipedia.SzemeredisTheorem

open Filter MeasureTheory Set
open scoped BigOperators Topology

namespace SmoothSieveCutoff

/-! ## Arbitrarily high paired Fourier moments -/

/-- Put the moment `q` on one distinguished Fourier coordinate. -/
def singleCoordinateMomentExponent
    {κ : Type*} [DecidableEq κ]
    (i : κ) (q : ℕ) : κ → ℕ :=
  fun j => if j = i then q else 0

theorem fourierProductMomentDensity_singleCoordinate
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (χ : SmoothSieveCutoff) (i : κ) (q : ℕ)
    (t : κ → ℝ) :
    χ.fourierProductMomentDensity
        (singleCoordinateMomentExponent i q) t =
      ‖t i‖ ^ q *
        χ.fourierProductMomentDensity (fun _ => 0) t := by
  classical
  unfold fourierProductMomentDensity fourierMomentDensity
    singleCoordinateMomentExponent
  rw [Finset.prod_eq_mul_prod_sdiff_singleton_of_mem
    (Finset.mem_univ i)]
  rw [Finset.prod_eq_mul_prod_sdiff_singleton_of_mem
    (Finset.mem_univ i)]
  simp only [if_pos, pow_zero, one_mul]
  have hprod :
      (∏ j ∈ Finset.univ \ {i},
        (‖t j‖ ^ if j = i then q else 0) *
          ‖χ.cutoffFourierTransform (t j)‖) =
        ∏ j ∈ Finset.univ \ {i},
          ‖χ.cutoffFourierTransform (t j)‖ := by
    apply Finset.prod_congr rfl
    intro j hj
    have hji : j ≠ i := by
      exact Finset.notMem_singleton.mp
        (Finset.mem_sdiff.mp hj).2
    simp [hji]
  rw [hprod]
  ring

/-- Sum of the `q`-th moments obtained by placing the weight on one
coordinate at a time. -/
noncomputable def selectedCFZOneSideFourierMomentDensity
    {k : ℕ} (χ : SmoothSieveCutoff)
    (e : LinearFormsExponent k) (q : ℕ)
    (t : SelectedCFZFormIndex e → ℝ) : ℝ :=
  ∑ i,
    χ.fourierProductMomentDensity
      (singleCoordinateMomentExponent i q) t

theorem selectedCFZOneSideFourierMomentDensity_nonneg
    {k : ℕ} (χ : SmoothSieveCutoff)
    (e : LinearFormsExponent k) (q : ℕ)
    (t : SelectedCFZFormIndex e → ℝ) :
    0 ≤ χ.selectedCFZOneSideFourierMomentDensity e q t := by
  unfold selectedCFZOneSideFourierMomentDensity
  exact Finset.sum_nonneg fun i _ =>
    χ.fourierProductMomentDensity_nonneg
      (singleCoordinateMomentExponent i q) t

theorem integrable_selectedCFZOneSideFourierMomentDensity
    {k : ℕ} (χ : SmoothSieveCutoff)
    (e : LinearFormsExponent k) (q : ℕ) :
    Integrable
      (χ.selectedCFZOneSideFourierMomentDensity e q) := by
  unfold selectedCFZOneSideFourierMomentDensity
  exact integrable_finsetSum Finset.univ fun i _ =>
    χ.integrable_fourierProductMomentDensity
      (singleCoordinateMomentExponent i q)

/-- A paired moment majorant: the high moment may lie on either Fourier
side. -/
noncomputable def selectedCFZPairedFourierMomentDensity
    {k : ℕ} (χ : SmoothSieveCutoff)
    (e : LinearFormsExponent k) (q : ℕ)
    (tu :
      (SelectedCFZFormIndex e → ℝ) ×
        (SelectedCFZFormIndex e → ℝ)) : ℝ :=
  χ.selectedCFZOneSideFourierMomentDensity e q tu.1 *
      χ.fourierProductMomentDensity (fun _ => 0) tu.2 +
    χ.fourierProductMomentDensity (fun _ => 0) tu.1 *
      χ.selectedCFZOneSideFourierMomentDensity e q tu.2

theorem selectedCFZPairedFourierMomentDensity_nonneg
    {k : ℕ} (χ : SmoothSieveCutoff)
    (e : LinearFormsExponent k) (q : ℕ)
    (tu :
      (SelectedCFZFormIndex e → ℝ) ×
        (SelectedCFZFormIndex e → ℝ)) :
    0 ≤ χ.selectedCFZPairedFourierMomentDensity e q tu := by
  unfold selectedCFZPairedFourierMomentDensity
  exact add_nonneg
    (mul_nonneg
      (χ.selectedCFZOneSideFourierMomentDensity_nonneg e q tu.1)
      (χ.fourierProductMomentDensity_nonneg (fun _ => 0) tu.2))
    (mul_nonneg
      (χ.fourierProductMomentDensity_nonneg (fun _ => 0) tu.1)
      (χ.selectedCFZOneSideFourierMomentDensity_nonneg e q tu.2))

theorem integrable_selectedCFZPairedFourierMomentDensity
    {k : ℕ} (χ : SmoothSieveCutoff)
    (e : LinearFormsExponent k) (q : ℕ) :
    Integrable
      (χ.selectedCFZPairedFourierMomentDensity e q)
      (volume.prod volume) := by
  unfold selectedCFZPairedFourierMomentDensity
  exact
    ((χ.integrable_selectedCFZOneSideFourierMomentDensity e q).mul_prod
      (χ.integrable_fourierProductMomentDensity (fun _ => 0))).add
    ((χ.integrable_fourierProductMomentDensity (fun _ => 0)).mul_prod
      (χ.integrable_selectedCFZOneSideFourierMomentDensity e q))

/-- The finite total paired `q`-th moment. -/
noncomputable def selectedCFZPairedFourierAbsoluteMoment
    {k : ℕ} (χ : SmoothSieveCutoff)
    (e : LinearFormsExponent k) (q : ℕ) : ℝ :=
  ∫ tu,
    χ.selectedCFZPairedFourierMomentDensity e q tu
    ∂(volume.prod volume)

theorem selectedCFZPairedFourierAbsoluteMoment_nonneg
    {k : ℕ} (χ : SmoothSieveCutoff)
    (e : LinearFormsExponent k) (q : ℕ) :
    0 ≤ χ.selectedCFZPairedFourierAbsoluteMoment e q := by
  unfold selectedCFZPairedFourierAbsoluteMoment
  exact integral_nonneg fun tu =>
    χ.selectedCFZPairedFourierMomentDensity_nonneg e q tu

theorem pow_mul_fourierProductZeroDensity_le_oneSideMoment
    {k : ℕ} (χ : SmoothSieveCutoff)
    (e : LinearFormsExponent k) (q : ℕ)
    {T : ℝ} (hT : 0 ≤ T)
    (t : SelectedCFZFormIndex e → ℝ)
    (ht : t ∉ fourierProductBox T) :
    T ^ q * χ.fourierProductMomentDensity (fun _ => 0) t ≤
      χ.selectedCFZOneSideFourierMomentDensity e q t := by
  classical
  have hnotAll :
      ¬∀ i : SelectedCFZFormIndex e, |t i| ≤ T := by
    intro hall
    exact ht ((mem_fourierProductBox_iff hT t).2 hall)
  obtain ⟨i, hi⟩ := Classical.not_forall.mp hnotAll
  have hTi : T ≤ ‖t i‖ := by
    simpa only [Real.norm_eq_abs] using le_of_not_ge hi
  calc
    T ^ q * χ.fourierProductMomentDensity (fun _ => 0) t ≤
        ‖t i‖ ^ q *
          χ.fourierProductMomentDensity (fun _ => 0) t := by
      exact mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ hT hTi q)
        (χ.fourierProductMomentDensity_nonneg (fun _ => 0) t)
    _ = χ.fourierProductMomentDensity
          (singleCoordinateMomentExponent i q) t := by
      symm
      exact χ.fourierProductMomentDensity_singleCoordinate i q t
    _ ≤ χ.selectedCFZOneSideFourierMomentDensity e q t := by
      unfold selectedCFZOneSideFourierMomentDensity
      exact Finset.single_le_sum
        (fun j _ =>
          χ.fourierProductMomentDensity_nonneg
            (singleCoordinateMomentExponent j q) t)
        (Finset.mem_univ i)

theorem pow_mul_selectedCFZPairedFourierAbsoluteDensity_le_moment
    {k : ℕ} (χ : SmoothSieveCutoff)
    (e : LinearFormsExponent k) (q : ℕ)
    {T : ℝ} (hT : 0 ≤ T)
    (tu :
      (SelectedCFZFormIndex e → ℝ) ×
        (SelectedCFZFormIndex e → ℝ))
    (htu : tu ∈ (selectedCFZPairedFourierBox e T)ᶜ) :
    T ^ q * χ.selectedCFZPairedFourierAbsoluteDensity e tu ≤
      χ.selectedCFZPairedFourierMomentDensity e q tu := by
  have hnot :
      tu.1 ∉ fourierProductBox T ∨
        tu.2 ∉ fourierProductBox T := by
    by_contra hboth
    apply htu
    push Not at hboth
    unfold selectedCFZPairedFourierBox
    exact ⟨hboth.1, hboth.2⟩
  unfold selectedCFZPairedFourierAbsoluteDensity
    selectedCFZPairedFourierMomentDensity
  rcases hnot with hleft | hright
  · calc
      T ^ q *
          (χ.fourierProductMomentDensity (fun _ => 0) tu.1 *
            χ.fourierProductMomentDensity (fun _ => 0) tu.2) =
          (T ^ q *
              χ.fourierProductMomentDensity (fun _ => 0) tu.1) *
            χ.fourierProductMomentDensity (fun _ => 0) tu.2 := by
        ring
      _ ≤ χ.selectedCFZOneSideFourierMomentDensity e q tu.1 *
            χ.fourierProductMomentDensity (fun _ => 0) tu.2 := by
        exact mul_le_mul_of_nonneg_right
          (χ.pow_mul_fourierProductZeroDensity_le_oneSideMoment
            e q hT tu.1 hleft)
          (χ.fourierProductMomentDensity_nonneg (fun _ => 0) tu.2)
      _ ≤
          χ.selectedCFZOneSideFourierMomentDensity e q tu.1 *
              χ.fourierProductMomentDensity (fun _ => 0) tu.2 +
            χ.fourierProductMomentDensity (fun _ => 0) tu.1 *
              χ.selectedCFZOneSideFourierMomentDensity e q tu.2 := by
        exact le_add_of_nonneg_right
          (mul_nonneg
            (χ.fourierProductMomentDensity_nonneg (fun _ => 0) tu.1)
            (χ.selectedCFZOneSideFourierMomentDensity_nonneg e q tu.2))
  · calc
      T ^ q *
          (χ.fourierProductMomentDensity (fun _ => 0) tu.1 *
            χ.fourierProductMomentDensity (fun _ => 0) tu.2) =
          χ.fourierProductMomentDensity (fun _ => 0) tu.1 *
            (T ^ q *
              χ.fourierProductMomentDensity (fun _ => 0) tu.2) := by
        ring
      _ ≤ χ.fourierProductMomentDensity (fun _ => 0) tu.1 *
            χ.selectedCFZOneSideFourierMomentDensity e q tu.2 := by
        exact mul_le_mul_of_nonneg_left
          (χ.pow_mul_fourierProductZeroDensity_le_oneSideMoment
            e q hT tu.2 hright)
          (χ.fourierProductMomentDensity_nonneg (fun _ => 0) tu.1)
      _ ≤
          χ.selectedCFZOneSideFourierMomentDensity e q tu.1 *
              χ.fourierProductMomentDensity (fun _ => 0) tu.2 +
            χ.fourierProductMomentDensity (fun _ => 0) tu.1 *
              χ.selectedCFZOneSideFourierMomentDensity e q tu.2 := by
        exact le_add_of_nonneg_left
          (mul_nonneg
            (χ.selectedCFZOneSideFourierMomentDensity_nonneg e q tu.1)
            (χ.fourierProductMomentDensity_nonneg (fun _ => 0) tu.2))

theorem pow_mul_selectedCFZPairedFourierAbsoluteTail_le_moment
    {k : ℕ} (χ : SmoothSieveCutoff)
    (e : LinearFormsExponent k) (q : ℕ)
    {T : ℝ} (hT : 0 ≤ T) :
    T ^ q * χ.selectedCFZPairedFourierAbsoluteTail e T ≤
      χ.selectedCFZPairedFourierAbsoluteMoment e q := by
  unfold selectedCFZPairedFourierAbsoluteTail
    selectedCFZPairedFourierAbsoluteMoment
  calc
    T ^ q *
        (∫ tu in (selectedCFZPairedFourierBox e T)ᶜ,
          χ.selectedCFZPairedFourierAbsoluteDensity e tu
          ∂(volume.prod volume)) =
        ∫ tu in (selectedCFZPairedFourierBox e T)ᶜ,
          T ^ q * χ.selectedCFZPairedFourierAbsoluteDensity e tu
          ∂(volume.prod volume) := by
      rw [integral_const_mul]
    _ ≤
        ∫ tu in (selectedCFZPairedFourierBox e T)ᶜ,
          χ.selectedCFZPairedFourierMomentDensity e q tu
          ∂(volume.prod volume) := by
      apply setIntegral_mono_on
      · exact
          ((χ.integrable_selectedCFZPairedFourierAbsoluteDensity e).const_mul
            (T ^ q)).integrableOn
      · exact
          (χ.integrable_selectedCFZPairedFourierMomentDensity e q).integrableOn
      · exact (measurableSet_selectedCFZPairedFourierBox e T).compl
      · intro tu htu
        exact
          χ.pow_mul_selectedCFZPairedFourierAbsoluteDensity_le_moment
            e q hT tu htu
    _ ≤
        ∫ tu,
          χ.selectedCFZPairedFourierMomentDensity e q tu
          ∂(volume.prod volume) := by
      exact setIntegral_le_integral
        (χ.integrable_selectedCFZPairedFourierMomentDensity e q)
        (Filter.Eventually.of_forall fun tu =>
          χ.selectedCFZPairedFourierMomentDensity_nonneg e q tu)

theorem selectedCFZPairedFourierAbsoluteTail_le_moment_div_pow
    {k : ℕ} (χ : SmoothSieveCutoff)
    (e : LinearFormsExponent k) (q : ℕ)
    {T : ℝ} (hT : 0 < T) :
    χ.selectedCFZPairedFourierAbsoluteTail e T ≤
      χ.selectedCFZPairedFourierAbsoluteMoment e q / T ^ q := by
  rw [le_div_iff₀ (pow_pos hT q)]
  simpa only [mul_comm] using
    χ.pow_mul_selectedCFZPairedFourierAbsoluteTail_le_moment
      e q hT.le

theorem selectedCFZPairedFourierAbsoluteTail_sqrt_log_le
    {k : ℕ} (χ : SmoothSieveCutoff)
    (e : LinearFormsExponent k) (n : ℕ)
    {R : ℕ} (hR : 2 ≤ R) :
    χ.selectedCFZPairedFourierAbsoluteTail e
        (Real.sqrt (Real.log R)) ≤
      χ.selectedCFZPairedFourierAbsoluteMoment e (2 * n) /
        (Real.log R) ^ n := by
  have hRone : (1 : ℝ) < R := by exact_mod_cast hR
  have hlog : 0 < Real.log R := Real.log_pos hRone
  have hsqrt : 0 < Real.sqrt (Real.log R) :=
    Real.sqrt_pos.2 hlog
  have hpow :
      Real.sqrt (Real.log R) ^ (2 * n) =
        (Real.log R) ^ n := by
    calc
      Real.sqrt (Real.log R) ^ (2 * n) =
          (Real.sqrt (Real.log R) ^ 2) ^ n := by
        rw [pow_mul]
      _ = (Real.log R) ^ n := by
        rw [Real.sq_sqrt hlog.le]
  rw [← hpow]
  exact
    χ.selectedCFZPairedFourierAbsoluteTail_le_moment_div_pow
      e (2 * n) hsqrt

/-! ## Polylogarithmic arithmetic growth -/

/-- Natural coefficient in the harmonic LCM Euler product. -/
def selectedCFZHarmonicEulerCoefficient
    {k : ℕ} (e : LinearFormsExponent k) : ℕ :=
  2 ^ (2 * Fintype.card (SelectedCFZFormIndex e)) - 1

/-- Total polylogarithmic exponent: one power of `log R` for each Selberg
normalization and `3A` powers from the shifted-zeta prime-product bound. -/
def selectedCFZCarryFourierPolylogExponent
    {k : ℕ} (e : LinearFormsExponent k) : ℕ :=
  Fintype.card (SelectedCFZFormIndex e) +
    3 * selectedCFZHarmonicEulerCoefficient e

theorem pairedDivisorHarmonicEulerMajorant_selected_le_polylog
    {k : ℕ} (e : LinearFormsExponent k)
    {R : ℕ} (hR : 2 ≤ R) :
    pairedDivisorHarmonicEulerMajorant
        (SelectedCFZFormIndex e) R ≤
      (1 + Real.log R) ^
        (3 * selectedCFZHarmonicEulerCoefficient e) := by
  unfold pairedDivisorHarmonicEulerMajorant
    selectedCFZHarmonicEulerCoefficient
  exact prod_primesLE_one_add_nat_div_le_one_add_log_pow
    (2 ^ (2 * Fintype.card (SelectedCFZFormIndex e)) - 1)
    R hR

theorem abs_normalizedSelbergScale_mul_logSq_le
    (χ : SmoothSieveCutoff)
    {R : ℕ} (hR : 2 ≤ R) (w : ℕ) :
    |normalizedSelbergScale χ.normalizer R (primorial w)| *
        |Real.log R ^ 2| ≤
      χ.normalizer⁻¹ * (1 + Real.log R) := by
  have hRone : (1 : ℝ) < R := by exact_mod_cast hR
  have hlog : 0 < Real.log R := Real.log_pos hRone
  have hW : 0 < primorial w := primorial_pos w
  have hc : 0 < χ.normalizer := χ.normalizer_pos
  have hscale :
      0 ≤ normalizedSelbergScale
        χ.normalizer R (primorial w) := by
    unfold normalizedSelbergScale
    positivity
  have hdensity :
      (((primorial w).totient : ℝ) / (primorial w : ℝ)) ≤ 1 := by
    rw [div_le_one (by exact_mod_cast hW)]
    exact_mod_cast Nat.totient_le (primorial w)
  rw [abs_of_nonneg hscale, abs_of_nonneg (sq_nonneg (Real.log R))]
  unfold normalizedSelbergScale
  have hrewrite :
      ((((primorial w).totient : ℝ) / (primorial w : ℝ)) /
            (χ.normalizer * Real.log R)) *
          Real.log R ^ 2 =
        (((primorial w).totient : ℝ) / (primorial w : ℝ)) *
          χ.normalizer⁻¹ * Real.log R := by
    field_simp [hc.ne', hlog.ne',
      (show (primorial w : ℝ) ≠ 0 by exact_mod_cast hW.ne')]
  rw [hrewrite]
  calc
    (((primorial w).totient : ℝ) / (primorial w : ℝ)) *
          χ.normalizer⁻¹ * Real.log R ≤
        1 * χ.normalizer⁻¹ * Real.log R := by
      gcongr
    _ ≤ χ.normalizer⁻¹ * (1 + Real.log R) := by
      have hcInv : 0 ≤ χ.normalizer⁻¹ := inv_nonneg.mpr hc.le
      nlinarith

theorem selectedCFZScaledHarmonicEulerMajorant_le_polylog
    {k : ℕ} (χ : SmoothSieveCutoff)
    (e : LinearFormsExponent k)
    {R : ℕ} (hR : 2 ≤ R) (w : ℕ) :
    χ.selectedCFZScaledHarmonicEulerMajorant
        R (primorial w) e ≤
      χ.normalizer⁻¹ ^
          Fintype.card (SelectedCFZFormIndex e) *
        (1 + Real.log R) ^
          selectedCFZCarryFourierPolylogExponent e := by
  let m := Fintype.card (SelectedCFZFormIndex e)
  let A := selectedCFZHarmonicEulerCoefficient e
  have hbase :
      |normalizedSelbergScale χ.normalizer R (primorial w)| *
          |Real.log R ^ 2| ≤
        χ.normalizer⁻¹ * (1 + Real.log R) :=
    χ.abs_normalizedSelbergScale_mul_logSq_le hR w
  have hbaseNonneg :
      0 ≤
        |normalizedSelbergScale χ.normalizer R (primorial w)| *
          |Real.log R ^ 2| := by positivity
  have hprime :
      pairedDivisorHarmonicEulerMajorant
          (SelectedCFZFormIndex e) R ≤
        (1 + Real.log R) ^ (3 * A) := by
    simpa [A] using
      pairedDivisorHarmonicEulerMajorant_selected_le_polylog
        e hR
  have hprimeNonneg :
      0 ≤ pairedDivisorHarmonicEulerMajorant
        (SelectedCFZFormIndex e) R :=
    pairedDivisorHarmonicEulerMajorant_nonneg
      (SelectedCFZFormIndex e) R
  unfold selectedCFZScaledHarmonicEulerMajorant
  change
    |normalizedSelbergScale χ.normalizer R (primorial w)| ^ m *
        |Real.log R ^ 2| ^ m *
        pairedDivisorHarmonicEulerMajorant
          (SelectedCFZFormIndex e) R ≤
      χ.normalizer⁻¹ ^ m *
        (1 + Real.log R) ^ (m + 3 * A)
  calc
    |normalizedSelbergScale χ.normalizer R (primorial w)| ^ m *
          |Real.log R ^ 2| ^ m *
          pairedDivisorHarmonicEulerMajorant
            (SelectedCFZFormIndex e) R =
        (|normalizedSelbergScale χ.normalizer R (primorial w)| *
            |Real.log R ^ 2|) ^ m *
          pairedDivisorHarmonicEulerMajorant
            (SelectedCFZFormIndex e) R := by
      rw [mul_pow]
    _ ≤
        (χ.normalizer⁻¹ * (1 + Real.log R)) ^ m *
          (1 + Real.log R) ^ (3 * A) := by
      exact mul_le_mul
        (pow_le_pow_left₀ hbaseNonneg hbase m)
        hprime hprimeNonneg
        (pow_nonneg
          (mul_nonneg (inv_nonneg.mpr χ.normalizer_pos.le)
            (by
              have hlogNonneg : 0 ≤ Real.log R :=
                (Real.log_pos (by
                  exact_mod_cast hR : (1 : ℝ) < R)).le
              linarith)) m)
    _ =
        χ.normalizer⁻¹ ^ m *
          (1 + Real.log R) ^ (m + 3 * A) := by
      rw [mul_pow]
      calc
        χ.normalizer⁻¹ ^ m * (1 + Real.log R) ^ m *
              (1 + Real.log R) ^ (3 * A) =
            χ.normalizer⁻¹ ^ m *
              ((1 + Real.log R) ^ m *
                (1 + Real.log R) ^ (3 * A)) := by
          ring
        _ = χ.normalizer⁻¹ ^ m *
              (1 + Real.log R) ^ (m + 3 * A) := by
          rw [pow_add]

/-! ## Cancellation of arithmetic growth by a higher Fourier moment -/

/-- One more power in the denominator beats any fixed polylogarithmic
numerator. -/
theorem one_add_pow_div_pow_succ_le_inv
    (E : ℕ) {L : ℝ} (hL : 1 ≤ L) :
    (1 + L) ^ E / L ^ (E + 1) ≤
      2 ^ E / L := by
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hbaseNonneg : 0 ≤ 1 + L := by linarith
  have hbase : 1 + L ≤ 2 * L := by linarith
  calc
    (1 + L) ^ E / L ^ (E + 1) ≤
        (2 * L) ^ E / L ^ (E + 1) := by
      exact div_le_div_of_nonneg_right
        (pow_le_pow_left₀ hbaseNonneg hbase E)
        (pow_nonneg hLpos.le (E + 1))
    _ = 2 ^ E / L := by
      rw [mul_pow, pow_succ]
      field_simp [hLpos.ne']

/-- Quantitative fully scaled carry-tail estimate.  The moment order is
twice one more than the complete arithmetic polylogarithmic exponent. -/
theorem
    selectedCFZCarryScaledFourierTailNorm_sqrt_log_le_polylogMoment
    {k N w b : ℕ} [NeZero N]
    (χ : SmoothSieveCutoff)
    (hk : 2 ≤ k)
    (hbound :
      exceptionalPrimeBound
          (fun q : CFZFormIndex k => cfzAffineForm q) ≤ w)
    (hwb : (primorial w).Coprime b)
    (e : LinearFormsExponent k)
    {R : ℕ} (hR : 2 ≤ R) :
    χ.selectedCFZCarryScaledFourierTailNorm
        (N := N) R (primorial w) b e
        (Real.sqrt (Real.log R)) ≤
      χ.normalizer⁻¹ ^
          Fintype.card (SelectedCFZFormIndex e) *
        χ.selectedCFZPairedFourierAbsoluteMoment e
          (2 * (selectedCFZCarryFourierPolylogExponent e + 1)) *
        ((1 + Real.log R) ^
            selectedCFZCarryFourierPolylogExponent e /
          (Real.log R) ^
            (selectedCFZCarryFourierPolylogExponent e + 1)) := by
  let E := selectedCFZCarryFourierPolylogExponent e
  let m := Fintype.card (SelectedCFZFormIndex e)
  have hlog :
      0 < Real.log R := by
    exact Real.log_pos (by exact_mod_cast hR : (1 : ℝ) < R)
  have hmajorant :
      χ.selectedCFZScaledHarmonicEulerMajorant
          R (primorial w) e ≤
        χ.normalizer⁻¹ ^ m *
          (1 + Real.log R) ^ E := by
    simpa [m, E] using
      χ.selectedCFZScaledHarmonicEulerMajorant_le_polylog
        e hR w
  have htail :
      χ.selectedCFZPairedFourierAbsoluteTail e
          (Real.sqrt (Real.log R)) ≤
        χ.selectedCFZPairedFourierAbsoluteMoment e
            (2 * (E + 1)) /
          (Real.log R) ^ (E + 1) := by
    simpa [E] using
      χ.selectedCFZPairedFourierAbsoluteTail_sqrt_log_le
        e (E + 1) hR
  have hmajorantNonneg :
      0 ≤ χ.selectedCFZScaledHarmonicEulerMajorant
        R (primorial w) e :=
    χ.selectedCFZScaledHarmonicEulerMajorant_nonneg
      R (primorial w) e
  have htailNonneg :
      0 ≤ χ.selectedCFZPairedFourierAbsoluteTail e
        (Real.sqrt (Real.log R)) :=
    χ.selectedCFZPairedFourierAbsoluteTail_nonneg e _
  calc
    χ.selectedCFZCarryScaledFourierTailNorm
        (N := N) R (primorial w) b e
        (Real.sqrt (Real.log R)) ≤
      χ.selectedCFZScaledHarmonicEulerMajorant
          R (primorial w) e *
        χ.selectedCFZPairedFourierAbsoluteTail e
          (Real.sqrt (Real.log R)) :=
      χ.selectedCFZCarryScaledFourierTailNorm_le_harmonicEulerMajorant_primorial
        (N := N) hk hbound hwb e R _
    _ ≤
        (χ.normalizer⁻¹ ^ m *
            (1 + Real.log R) ^ E) *
          (χ.selectedCFZPairedFourierAbsoluteMoment e
              (2 * (E + 1)) /
            (Real.log R) ^ (E + 1)) := by
      exact mul_le_mul hmajorant htail htailNonneg
        (mul_nonneg
          (pow_nonneg (inv_nonneg.mpr χ.normalizer_pos.le) m)
          (pow_nonneg (by linarith : 0 ≤ 1 + Real.log R) E))
    _ =
        χ.normalizer⁻¹ ^ m *
          χ.selectedCFZPairedFourierAbsoluteMoment e
            (2 * (E + 1)) *
          ((1 + Real.log R) ^ E /
            (Real.log R) ^ (E + 1)) := by
      ring
    _ =
        χ.normalizer⁻¹ ^
            Fintype.card (SelectedCFZFormIndex e) *
          χ.selectedCFZPairedFourierAbsoluteMoment e
            (2 *
              (selectedCFZCarryFourierPolylogExponent e + 1)) *
          ((1 + Real.log R) ^
                selectedCFZCarryFourierPolylogExponent e /
            (Real.log R) ^
              (selectedCFZCarryFourierPolylogExponent e + 1)) := by
      rfl

/-- Once `log R ≥ 1`, the complete bound is an explicit constant times
`1 / log R`, uniformly in the cyclic modulus and primorial cutoff. -/
theorem
    selectedCFZCarryScaledFourierTailNorm_sqrt_log_le_const_div_log
    {k N w b : ℕ} [NeZero N]
    (χ : SmoothSieveCutoff)
    (hk : 2 ≤ k)
    (hbound :
      exceptionalPrimeBound
          (fun q : CFZFormIndex k => cfzAffineForm q) ≤ w)
    (hwb : (primorial w).Coprime b)
    (e : LinearFormsExponent k)
    {R : ℕ} (hR : 2 ≤ R)
    (hlogOne : 1 ≤ Real.log R) :
    χ.selectedCFZCarryScaledFourierTailNorm
        (N := N) R (primorial w) b e
        (Real.sqrt (Real.log R)) ≤
      (χ.normalizer⁻¹ ^
            Fintype.card (SelectedCFZFormIndex e) *
          χ.selectedCFZPairedFourierAbsoluteMoment e
            (2 *
              (selectedCFZCarryFourierPolylogExponent e + 1)) *
          (2 : ℝ) ^
            selectedCFZCarryFourierPolylogExponent e) /
        Real.log R := by
  let E := selectedCFZCarryFourierPolylogExponent e
  let m := Fintype.card (SelectedCFZFormIndex e)
  let C :=
    χ.normalizer⁻¹ ^ m *
      χ.selectedCFZPairedFourierAbsoluteMoment e (2 * (E + 1))
  have hC : 0 ≤ C := by
    unfold C
    exact mul_nonneg
      (pow_nonneg (inv_nonneg.mpr χ.normalizer_pos.le) m)
      (χ.selectedCFZPairedFourierAbsoluteMoment_nonneg e
        (2 * (E + 1)))
  calc
    χ.selectedCFZCarryScaledFourierTailNorm
        (N := N) R (primorial w) b e
        (Real.sqrt (Real.log R)) ≤
      C *
        ((1 + Real.log R) ^ E /
          (Real.log R) ^ (E + 1)) := by
      simpa [C, E, m] using
        χ.selectedCFZCarryScaledFourierTailNorm_sqrt_log_le_polylogMoment
          (N := N) hk hbound hwb e hR
    _ ≤ C * ((2 : ℝ) ^ E / Real.log R) := by
      exact mul_le_mul_of_nonneg_left
        (one_add_pow_div_pow_succ_le_inv E hlogOne) hC
    _ = (C * (2 : ℝ) ^ E) / Real.log R := by
      ring
    _ =
        (χ.normalizer⁻¹ ^
              Fintype.card (SelectedCFZFormIndex e) *
            χ.selectedCFZPairedFourierAbsoluteMoment e
              (2 *
                (selectedCFZCarryFourierPolylogExponent e + 1)) *
            (2 : ℝ) ^
              selectedCFZCarryFourierPolylogExponent e) /
          Real.log R := by
      rfl

/-- Unconditional growing-primorial vanishing of the fully scaled
complementary carry integral.  No bounded arithmetic-mass hypothesis remains:
the explicit Euler product has only polylogarithmic growth, which is absorbed
by one additional Schwartz moment. -/
theorem
    tendsto_selectedCFZCarryScaledFourierTailNorm_sqrt_log_primorial
    {k : ℕ}
    (χ : SmoothSieveCutoff)
    (hk : 2 ≤ k)
    (Nseq wseq bseq : ℕ → ℕ)
    (hN : ∀ R, Nseq R ≠ 0)
    (hbound :
      ∀ R,
        exceptionalPrimeBound
            (fun q : CFZFormIndex k => cfzAffineForm q) ≤
          wseq R)
    (hcoprime :
      ∀ R, (primorial (wseq R)).Coprime (bseq R))
    (e : LinearFormsExponent k) :
    Tendsto
      (fun R : ℕ =>
        letI : NeZero (Nseq R) := ⟨hN R⟩
        χ.selectedCFZCarryScaledFourierTailNorm
          (N := Nseq R) R (primorial (wseq R)) (bseq R) e
          (Real.sqrt (Real.log R)))
      atTop (𝓝 0) := by
  let E := selectedCFZCarryFourierPolylogExponent e
  let m := Fintype.card (SelectedCFZFormIndex e)
  let C : ℝ :=
    χ.normalizer⁻¹ ^ m *
      χ.selectedCFZPairedFourierAbsoluteMoment e (2 * (E + 1)) *
      2 ^ E
  have hlogTop :
      Tendsto (fun R : ℕ => Real.log R) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hinvLog :
      Tendsto (fun R : ℕ => (Real.log R)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hlogTop
  have hupper :
      Tendsto (fun R : ℕ => C / Real.log R) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using
      (tendsto_const_nhds.mul hinvLog :
        Tendsto
          (fun R : ℕ => C * (Real.log R)⁻¹)
          atTop (𝓝 (C * 0)))
  have hRtwo : ∀ᶠ R : ℕ in atTop, 2 ≤ R :=
    eventually_ge_atTop 2
  have hlogOne : ∀ᶠ R : ℕ in atTop, 1 ≤ Real.log R :=
    hlogTop.eventually (eventually_ge_atTop 1)
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall fun R => by
      let : NeZero (Nseq R) := ⟨hN R⟩
      exact
        χ.selectedCFZCarryScaledFourierTailNorm_nonneg
          (N := Nseq R) R (primorial (wseq R)) (bseq R) e _
  · filter_upwards [hRtwo, hlogOne] with R hR hlogR
    let : NeZero (Nseq R) := ⟨hN R⟩
    simpa [C, E, m] using
      χ.selectedCFZCarryScaledFourierTailNorm_sqrt_log_le_const_div_log
        (N := Nseq R) hk (hbound R) (hcoprime R) e hR hlogR
  · simpa [C, E, m] using hupper

end SmoothSieveCutoff

end Wikipedia.SzemeredisTheorem
