import ErdosProblems.Erdos1002.GaussPrefixAnnularSeparatedMarked

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Midpoint-band deletion for annular marked Fourier coefficients

This leaf recombines the separately compiled cardinal, one-digit, and
replacement estimates.  It is kept outside the foundational separated
file so downstream users of the cylinder bounds do not pay for this
specialization.
-/

open Filter MeasureTheory Set Finset
open scoped BigOperators Topology

namespace Erdos1002

noncomputable section

local instance gaussPrefixAnnularMidpointBandPropDecidable (P : Prop) :
    Decidable P := Classical.propDecidable P

/-- Explicit limiting mass majorant of the relative midpoint band. -/
def annularCanonicalMidpointBandMassLimit
    (ε A rho : ℝ) {grid : ℕ}
    (k : AnnularGridIndex grid → ℕ) : ℝ :=
  (2 * Real.log 2) *
    ((MixedOccurrenceCount k : ℝ) * 2 *
      (rho / gaussRoofMean) *
      (1 / gaussRoofMean) ^ (MixedOccurrenceCount k - 1)) *
    (7 : ℝ) ^ (MixedOccurrenceCount k - 1) *
    (Fintype.card
        (Fin (MixedOccurrenceCount k) ≃
          GaussPrefixMixedOccurrence k) : ℝ) *
    annularOccurrenceSignedDensity ε A k

/-- Algebraic transport which keeps a common additive error on the
right. -/
theorem mul_add_le_add_right_of_mul_le
    {c d e u : ℝ} (h : c * d ≤ u) :
    c * (d + e) ≤ u + c * e := by
  rw [mul_add]
  exact add_le_add_left h _

/-- On the canonical parity boxes, the signed Gauss midpoint mass is
exactly the oriented positive-window mass. -/
theorem
    annularCanonicalGaussMidpointBandSignedMass_eq_oriented
    {ε A rho : ℝ} {N : ℕ} {grid : ℕ}
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k)
    (mode :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Fin (MixedOccurrenceCount k) → ℤ)
    (hmode : ∀ e, mode e ≠ 0) :
    (∑ e : Fin (MixedOccurrenceCount k) ≃
          GaussPrefixMixedOccurrence k,
        gaussMovingSignedApproximationTupleSum
          (Real.log (N : ℝ))
          (flattenedAnnularSignedLower ε A e)
          (flattenedAnnularSignedUpper ε A e)
          (annularCanonicalLaterMidpointBandTaggedTupleFamily
            rho N k hr mode hmode e)) =
      annularCanonicalGaussOrientedMidpointBandApproximationMass
        ε A rho N k hr mode hmode := by
  unfold annularCanonicalGaussOrientedMidpointBandApproximationMass
  apply Finset.sum_congr rfl
  intro e _he
  exact gaussMovingSignedApproximationTupleSum_eq_oriented
    (Real.log (N : ℝ))
    (flattenedAnnularParity e)
    (flattenedAnnularSignedLower ε A e)
    (flattenedAnnularSignedUpper ε A e)
    (annularCanonicalLaterMidpointBandTaggedTupleFamily
      rho N k hr mode hmode e)
    (fun t ht j ↦
      canonicalAnnularGridTupleFamily_parity N k e t
        (annularCanonicalLaterMidpointBandTupleFamily_subset_canonical
          rho N k hr e (mode e) (hmode e) ht) j)

/-- Fourier-to-Gauss-mass domination specialized to the tagged midpoint
family. -/
theorem
    norm_annularCanonicalUniformMidpointBandMarkedFourierSum_le_gaussMass
    {ε A rho : ℝ} {N : ℕ} {grid : ℕ}
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k)
    (mode :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Fin (MixedOccurrenceCount k) → ℤ)
    (hmode : ∀ e, mode e ≠ 0) :
    ‖annularCanonicalUniformMidpointBandMarkedFourierSum
        ε A rho N k hr mode hmode‖ ≤
      (2 * Real.log 2) *
        ∑ e : Fin (MixedOccurrenceCount k) ≃
            GaussPrefixMixedOccurrence k,
          gaussMovingSignedApproximationTupleSum
            (Real.log (N : ℝ))
            (flattenedAnnularSignedLower ε A e)
            (flattenedAnnularSignedUpper ε A e)
            (annularCanonicalLaterMidpointBandTaggedTupleFamily
              rho N k hr mode hmode e) := by
  simpa only [annularCanonicalUniformMidpointBandMarkedFourierSum] using!
    norm_sum_uniformMovingSignedMarkedFourierTupleSum_le_gaussMass
      N (Real.log (N : ℝ))
      (fun e ↦ flattenedAnnularSignedLower ε A e)
      (fun e ↦ flattenedAnnularSignedUpper ε A e)
      mode
      (fun e ↦ annularCanonicalLaterMidpointBandTaggedTupleFamily
        rho N k hr mode hmode e)

set_option maxHeartbeats 800000

/-- Scaled exact-to-digit replacement on the midpoint band. -/
theorem
    twoLog_mul_annularCanonicalGaussMidpointBandApproximationMass_le
    {ε A rho : ℝ} {N : ℕ} {grid : ℕ}
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k)
    (mode :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Fin (MixedOccurrenceCount k) → ℤ)
    (hmode : ∀ e, mode e ≠ 0) :
    (2 * Real.log 2) *
        annularCanonicalGaussOrientedMidpointBandApproximationMass
          ε A rho N k hr mode hmode ≤
      (2 * Real.log 2) *
        (annularCanonicalGaussOrientedMidpointBandDigitMass
            ε A rho N k hr mode hmode +
          annularCanonicalGaussOrientedReplacementError ε A N k) := by
  exact mul_le_mul_of_nonneg_left
    (annularCanonicalGaussOrientedMidpointBandApproximationMass_le
      k hr mode hmode)
    (by positivity)

/-- The scaled midpoint digit mass is below the explicit envelope, with
the replacement error carried unchanged. -/
theorem
    twoLog_mul_annularCanonicalGaussMidpointBandDigit_add_error_le
    {ε A rho : ℝ} {N : ℕ} (hN : 1 < N)
    {grid : ℕ} (hgrid : 0 < grid)
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k)
    (htime : ∀ i, 0 < k i → i.time.1 < grid)
    (mode :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Fin (MixedOccurrenceCount k) → ℤ)
    (hmode : ∀ e, mode e ≠ 0) :
    (2 * Real.log 2) *
        (annularCanonicalGaussOrientedMidpointBandDigitMass
            ε A rho N k hr mode hmode +
          annularCanonicalGaussOrientedReplacementError ε A N k) ≤
      annularCanonicalMidpointBandDigitMassUpper ε A rho N k +
        (2 * Real.log 2) *
          annularCanonicalGaussOrientedReplacementError ε A N k := by
  exact mul_add_le_add_right_of_mul_le
    (annularCanonicalGaussMidpointBandDigitMass_le_upper
      (ε := ε) (A := A) (rho := rho) (N := N)
      hN hgrid k hr htime mode hmode)

/-- The oriented exact Gauss midpoint mass is controlled by the explicit
digit envelope plus the vanishing complete-family replacement error. -/
theorem
    twoLog_mul_annularCanonicalGaussMidpointBandMass_le
    {ε A rho : ℝ} {N : ℕ} (hN : 1 < N)
    {grid : ℕ} (hgrid : 0 < grid)
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k)
    (htime : ∀ i, 0 < k i → i.time.1 < grid)
    (mode :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Fin (MixedOccurrenceCount k) → ℤ)
    (hmode : ∀ e, mode e ≠ 0) :
    (2 * Real.log 2) *
        annularCanonicalGaussOrientedMidpointBandApproximationMass
          ε A rho N k hr mode hmode ≤
      annularCanonicalMidpointBandDigitMassUpper ε A rho N k +
        (2 * Real.log 2) *
          annularCanonicalGaussOrientedReplacementError ε A N k := by
  exact
    (twoLog_mul_annularCanonicalGaussMidpointBandApproximationMass_le
      k hr mode hmode).trans
      (twoLog_mul_annularCanonicalGaussMidpointBandDigit_add_error_le
        hN hgrid k hr htime mode hmode)

/-- Complete deterministic midpoint-band bound for the actual uniform
marked Fourier aggregate.  The first term has an explicit `O(rho)`
limit; the second is the complete-canonical replacement error and tends
to zero. -/
theorem norm_annularCanonicalUniformMidpointBandMarkedFourierSum_le
    {ε A rho : ℝ} {N : ℕ} (hN : 1 < N)
    {grid : ℕ} (hgrid : 0 < grid)
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k)
    (htime : ∀ i, 0 < k i → i.time.1 < grid)
    (mode :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Fin (MixedOccurrenceCount k) → ℤ)
    (hmode : ∀ e, mode e ≠ 0) :
    ‖annularCanonicalUniformMidpointBandMarkedFourierSum
        ε A rho N k hr mode hmode‖ ≤
      annularCanonicalMidpointBandDigitMassUpper ε A rho N k +
        (2 * Real.log 2) *
          annularCanonicalGaussOrientedReplacementError ε A N k := by
  calc
    ‖annularCanonicalUniformMidpointBandMarkedFourierSum
        ε A rho N k hr mode hmode‖ ≤
      (2 * Real.log 2) *
        ∑ e : Fin (MixedOccurrenceCount k) ≃
            GaussPrefixMixedOccurrence k,
          gaussMovingSignedApproximationTupleSum
            (Real.log (N : ℝ))
            (flattenedAnnularSignedLower ε A e)
            (flattenedAnnularSignedUpper ε A e)
            (annularCanonicalLaterMidpointBandTaggedTupleFamily
              rho N k hr mode hmode e) := by
      exact
        norm_annularCanonicalUniformMidpointBandMarkedFourierSum_le_gaussMass
          k hr mode hmode
    _ =
      (2 * Real.log 2) *
        annularCanonicalGaussOrientedMidpointBandApproximationMass
          ε A rho N k hr mode hmode := by
      rw [annularCanonicalGaussMidpointBandSignedMass_eq_oriented
        k hr mode hmode]
    _ ≤
      annularCanonicalMidpointBandDigitMassUpper ε A rho N k +
        (2 * Real.log 2) *
          annularCanonicalGaussOrientedReplacementError ε A N k :=
      twoLog_mul_annularCanonicalGaussMidpointBandMass_le
        hN hgrid k hr htime mode hmode

set_option maxHeartbeats 200000

/-- The deterministic midpoint majorant converges to the explicit
quantity linear in `rho`. -/
theorem tendsto_annularCanonicalMidpointBandMarkedMajorant
    {ε A rho : ℝ} (hε : 0 < ε) (hεA : ε < A)
    (hrho : 0 ≤ rho)
    {grid : ℕ} (hgrid : 0 < grid)
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k)
    (htime : ∀ i, 0 < k i → i.time.1 < grid)
    (hsigned : ∀ i, 0 < k i → i.signed.1 < grid) :
    Tendsto
      (fun N : ℕ ↦
        annularCanonicalMidpointBandDigitMassUpper ε A rho N k +
          (2 * Real.log 2) *
            annularCanonicalGaussOrientedReplacementError ε A N k)
      atTop
      (nhds (annularCanonicalMidpointBandMassLimit ε A rho k)) := by
  have hdigit :=
    tendsto_annularCanonicalMidpointBandDigitMassUpper
      hε hεA hrho hgrid k hsigned
  have herror :=
    tendsto_annularCanonicalGaussOrientedReplacementError_zero
      hε hεA hgrid k hr htime hsigned
  have hscaledError :
      Tendsto
        (fun N : ℕ ↦
          (2 * Real.log 2) *
            annularCanonicalGaussOrientedReplacementError ε A N k)
        atTop (nhds 0) := by
    simpa only [mul_zero] using!
      (tendsto_const_nhds.mul herror)
  have hadd := hdigit.add hscaledError
  simpa only [add_zero, annularCanonicalMidpointBandMassLimit] using! hadd

/-- For fixed positive `rho`, the midpoint Fourier aggregate is
eventually below its explicit limiting majorant plus any prescribed
positive slack. -/
theorem
    eventually_norm_annularCanonicalUniformMidpointBandMarkedFourierSum_lt
    {ε A rho η : ℝ} (hε : 0 < ε) (hεA : ε < A)
    (hrho : 0 ≤ rho) (hη : 0 < η)
    {grid : ℕ} (hgrid : 0 < grid)
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k)
    (htime : ∀ i, 0 < k i → i.time.1 < grid)
    (hsigned : ∀ i, 0 < k i → i.signed.1 < grid)
    (mode :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Fin (MixedOccurrenceCount k) → ℤ)
    (hmode : ∀ e, mode e ≠ 0) :
    ∀ᶠ N : ℕ in atTop,
      ‖annularCanonicalUniformMidpointBandMarkedFourierSum
          ε A rho N k hr mode hmode‖ <
        annularCanonicalMidpointBandMassLimit ε A rho k + η := by
  have hmajorant :=
    tendsto_annularCanonicalMidpointBandMarkedMajorant
      hε hεA hrho hgrid k hr htime hsigned
  filter_upwards
    [eventually_ge_atTop 2,
      hmajorant.eventually_lt_const
        (lt_add_of_pos_right
          (annularCanonicalMidpointBandMassLimit ε A rho k) hη)] with
      N hN hupper
  exact
    (norm_annularCanonicalUniformMidpointBandMarkedFourierSum_le
      (by omega) hgrid k hr htime mode hmode).trans_lt hupper

/-- The fixed-rho midpoint majorant vanishes in the outer limit
`rho → 0`. -/
theorem tendsto_annularCanonicalMidpointBandMassLimit_zero
    (ε A : ℝ) {grid : ℕ}
    (k : AnnularGridIndex grid → ℕ) :
    Tendsto
      (fun rho : ℝ ↦ annularCanonicalMidpointBandMassLimit ε A rho k)
      (nhds 0) (nhds 0) := by
  let C : ℝ :=
    (2 * Real.log 2) *
      ((MixedOccurrenceCount k : ℝ) * 2 *
        (1 / gaussRoofMean) *
        (1 / gaussRoofMean) ^ (MixedOccurrenceCount k - 1)) *
      (7 : ℝ) ^ (MixedOccurrenceCount k - 1) *
      (Fintype.card
          (Fin (MixedOccurrenceCount k) ≃
            GaussPrefixMixedOccurrence k) : ℝ) *
      annularOccurrenceSignedDensity ε A k
  have hC :
      Tendsto (fun rho : ℝ ↦ C * rho) (nhds 0) (nhds 0) := by
    have h :=
      (tendsto_const_nhds :
        Tendsto (fun _rho : ℝ ↦ C) (nhds 0) (nhds C)).mul
        tendsto_id
    simpa only [mul_zero] using! h
  apply hC.congr'
  filter_upwards with rho
  unfold annularCanonicalMidpointBandMassLimit
  dsimp only [C]
  ring

end

end Erdos1002
