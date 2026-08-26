import ErdosProblems.Erdos1002.GaussPrefixAnnularMidpointBand
import ErdosProblems.Erdos1002.GaussPrefixAnnularRetainedGapGrowth
import ErdosProblems.Erdos1002.GaussPrefixAnnularTimeZeroShortMarked
import ErdosProblems.Erdos1002.GaussPrefixAnnularInteriorMeasure

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Recombination of the annular midpoint decomposition

For a fixed positive relative width, the interior separated family is the
disjoint union of the moving midpoint band, the lower retained family, and
the upper retained family.  This file records that exact finite identity
and the outer `rho ↓ 0` argument.  The two retained cancellation estimates
remain separate inputs, so their analytic proofs can be audited
independently.
-/

open Filter MeasureTheory Set Finset
open scoped BigOperators Topology

namespace Erdos1002

noncomputable section

local instance gaussPrefixAnnularMidpointAssemblyPropDecidable
    (P : Prop) : Decidable P := Classical.propDecidable P

/-- Aggregate marked Fourier contribution of the lower retained family. -/
def annularCanonicalUniformLowerRetainedMarkedFourierSum
    (ε A rho : ℝ) (N : ℕ) {grid : ℕ}
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k)
    (mode :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Fin (MixedOccurrenceCount k) → ℤ)
    (hmode : ∀ e, mode e ≠ 0) : ℂ :=
  ∑ e : Fin (MixedOccurrenceCount k) ≃
      GaussPrefixMixedOccurrence k,
    uniformMovingSignedMarkedFourierTupleSum
      N (Real.log (N : ℝ))
      (flattenedAnnularSignedLower ε A e)
      (flattenedAnnularSignedUpper ε A e)
      (mode e)
      (annularCanonicalLaterLowerMidpointTupleFamily
        rho N k hr e (mode e) (hmode e))

/-- Aggregate marked Fourier contribution of the upper retained family. -/
def annularCanonicalUniformUpperRetainedMarkedFourierSum
    (ε A rho : ℝ) (N : ℕ) {grid : ℕ}
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k)
    (mode :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Fin (MixedOccurrenceCount k) → ℤ)
    (hmode : ∀ e, mode e ≠ 0) : ℂ :=
  ∑ e : Fin (MixedOccurrenceCount k) ≃
      GaussPrefixMixedOccurrence k,
    uniformMovingSignedMarkedFourierTupleSum
      N (Real.log (N : ℝ))
      (flattenedAnnularSignedLower ε A e)
      (flattenedAnnularSignedUpper ε A e)
      (mode e)
      (annularCanonicalLaterUpperMidpointTupleFamily
        rho N k hr e (mode e) (hmode e))

/-- Aggregate marked Fourier contribution of the entire interior separated
family. -/
def annularCanonicalUniformInteriorSeparatedMarkedFourierSum
    (ε A : ℝ) (N : ℕ) {grid : ℕ}
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k)
    (mode :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Fin (MixedOccurrenceCount k) → ℤ) : ℂ :=
  ∑ e : Fin (MixedOccurrenceCount k) ≃
      GaussPrefixMixedOccurrence k,
    uniformMovingSignedMarkedFourierTupleSum
      N (Real.log (N : ℝ))
      (flattenedAnnularSignedLower ε A e)
      (flattenedAnnularSignedUpper ε A e)
      (mode e)
      (interiorSeparatedCanonicalAnnularGridTupleFamily N k hr e)

/-- The exact one-tag finite-sum decomposition. -/
theorem uniformInteriorSeparatedMarkedFourier_eq_midpoint_add_lower_add_upper
    {ε A rho : ℝ} {N grid : ℕ}
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k)
    (e : Fin (MixedOccurrenceCount k) ≃
      GaussPrefixMixedOccurrence k)
    (mode : Fin (MixedOccurrenceCount k) → ℤ)
    (hmode : mode ≠ 0)
    (hW : 0 < annularMidpointBandWidth rho N) :
    uniformMovingSignedMarkedFourierTupleSum
        N (Real.log (N : ℝ))
        (flattenedAnnularSignedLower ε A e)
        (flattenedAnnularSignedUpper ε A e)
        mode
        (interiorSeparatedCanonicalAnnularGridTupleFamily N k hr e) =
      uniformMovingSignedMarkedFourierTupleSum
          N (Real.log (N : ℝ))
          (flattenedAnnularSignedLower ε A e)
          (flattenedAnnularSignedUpper ε A e)
          mode
          (annularCanonicalLaterMidpointBandTupleFamily
            rho N k hr e mode hmode) +
        uniformMovingSignedMarkedFourierTupleSum
          N (Real.log (N : ℝ))
          (flattenedAnnularSignedLower ε A e)
          (flattenedAnnularSignedUpper ε A e)
          mode
          (annularCanonicalLaterLowerMidpointTupleFamily
            rho N k hr e mode hmode) +
        uniformMovingSignedMarkedFourierTupleSum
          N (Real.log (N : ℝ))
          (flattenedAnnularSignedLower ε A e)
          (flattenedAnnularSignedUpper ε A e)
          mode
          (annularCanonicalLaterUpperMidpointTupleFamily
            rho N k hr e mode hmode) := by
  classical
  let interior :=
    interiorSeparatedCanonicalAnnularGridTupleFamily N k hr e
  let band :=
    annularCanonicalLaterMidpointBandTupleFamily
      rho N k hr e mode hmode
  let lower :=
    annularCanonicalLaterLowerMidpointTupleFamily
      rho N k hr e mode hmode
  let upper :=
    annularCanonicalLaterUpperMidpointTupleFamily
      rho N k hr e mode hmode
  let f : (Fin (MixedOccurrenceCount k) → ℕ) → ℂ := fun times ↦
    ∫ x, gaussMovingSignedMarkedTupleIntegrand
      N (Real.log (N : ℝ))
      (flattenedAnnularSignedLower ε A e)
      (flattenedAnnularSignedUpper ε A e)
      mode times x ∂uniform01Measure
  have hband : band ⊆ interior := by
    intro t ht
    exact (mem_laterMidpointBandNatTupleFamily_iff.mp ht).1
  have houtside : interior \ band = lower ∪ upper := by
    simpa only [interior, band, lower, upper] using!
      (interior_sdiff_annularCanonicalLaterMidpointBand_eq_lower_union_upper
        rho N k hr e mode hmode)
  have hdisjoint : Disjoint lower upper := by
    exact disjoint_annularCanonicalLaterLower_upper
      k hr e mode hmode hW
  unfold uniformMovingSignedMarkedFourierTupleSum
    movingSignedMarkedFourierTupleSum
  change (∑ t ∈ interior, f t) =
    (∑ t ∈ band, f t) + (∑ t ∈ lower, f t) + ∑ t ∈ upper, f t
  have hsplit := Finset.sum_sdiff (f := f) hband
  change
    (∑ t ∈ interior \ band, f t) + (∑ t ∈ band, f t) =
      ∑ t ∈ interior, f t at hsplit
  calc
    (∑ t ∈ interior, f t) =
        (∑ t ∈ interior \ band, f t) + ∑ t ∈ band, f t :=
      hsplit.symm
    _ = (∑ t ∈ lower ∪ upper, f t) + ∑ t ∈ band, f t := by
      rw [houtside]
    _ = ((∑ t ∈ lower, f t) + ∑ t ∈ upper, f t) +
        ∑ t ∈ band, f t := by
      rw [Finset.sum_union hdisjoint]
    _ = (∑ t ∈ band, f t) + (∑ t ∈ lower, f t) +
        ∑ t ∈ upper, f t := by
      ac_rfl

/-- The aggregate version of the exact finite decomposition. -/
theorem annularUniformInterior_eq_midpoint_add_lower_add_upper
    {ε A rho : ℝ} {N grid : ℕ}
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k)
    (mode :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Fin (MixedOccurrenceCount k) → ℤ)
    (hmode : ∀ e, mode e ≠ 0)
    (hW : 0 < annularMidpointBandWidth rho N) :
    annularCanonicalUniformInteriorSeparatedMarkedFourierSum
        ε A N k hr mode =
      annularCanonicalUniformMidpointBandMarkedFourierSum
          ε A rho N k hr mode hmode +
        annularCanonicalUniformLowerRetainedMarkedFourierSum
          ε A rho N k hr mode hmode +
        annularCanonicalUniformUpperRetainedMarkedFourierSum
          ε A rho N k hr mode hmode := by
  classical
  unfold annularCanonicalUniformInteriorSeparatedMarkedFourierSum
    annularCanonicalUniformMidpointBandMarkedFourierSum
    annularCanonicalUniformLowerRetainedMarkedFourierSum
    annularCanonicalUniformUpperRetainedMarkedFourierSum
    annularCanonicalLaterMidpointBandTaggedTupleFamily
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e _he
  exact uniformInteriorSeparatedMarkedFourier_eq_midpoint_add_lower_add_upper
    k hr e (mode e) (hmode e) hW

/-- If both retained pieces cancel for every fixed positive `rho`, then
the whole interior separated Fourier aggregate tends to zero.  The proof
first chooses `rho` so that the explicit midpoint majorant is small and
only then lets `N → ∞`; no diagonal choice is hidden. -/
theorem
    tendsto_annularUniformInteriorSeparatedMarkedFourier_zero_of_retained
    {ε A : ℝ} (hε : 0 < ε) (hεA : ε < A)
    {grid : ℕ} (hgrid : 0 < grid)
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k)
    (htime : ∀ i, 0 < k i → i.time.1 < grid)
    (hsigned : ∀ i, 0 < k i → i.signed.1 < grid)
    (mode :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Fin (MixedOccurrenceCount k) → ℤ)
    (hmode : ∀ e, mode e ≠ 0)
    (hlower : ∀ rho : ℝ, 0 < rho →
      Tendsto
        (fun N : ℕ ↦
          annularCanonicalUniformLowerRetainedMarkedFourierSum
            ε A rho N k hr mode hmode)
        atTop (nhds 0))
    (hupper : ∀ rho : ℝ, 0 < rho →
      Tendsto
        (fun N : ℕ ↦
          annularCanonicalUniformUpperRetainedMarkedFourierSum
            ε A rho N k hr mode hmode)
        atTop (nhds 0)) :
    Tendsto
      (fun N : ℕ ↦
        annularCanonicalUniformInteriorSeparatedMarkedFourierSum
          ε A N k hr mode)
      atTop (nhds 0) := by
  rw [Metric.tendsto_nhds]
  intro δ hδ
  have hbandRho :
      Tendsto
        (fun rho : ℝ ↦
          annularCanonicalMidpointBandMassLimit ε A rho k)
        (nhds 0) (nhds 0) :=
    tendsto_annularCanonicalMidpointBandMassLimit_zero ε A k
  have heventRho :
      ∀ᶠ rho : ℝ in nhds 0,
        ‖annularCanonicalMidpointBandMassLimit ε A rho k‖ < δ / 6 :=
    by
      simpa only [dist_zero_right] using!
        (Metric.tendsto_nhds.mp hbandRho) (δ / 6) (by positivity)
  rcases
      (mem_nhds_iff_exists_Ioo_subset
        (s := {rho : ℝ |
          ‖annularCanonicalMidpointBandMassLimit ε A rho k‖ < δ / 6})
        (a := 0)).mp heventRho with
    ⟨a, b, ⟨ha, hb⟩, hab⟩
  let rho : ℝ := min (b / 2) (-a / 2)
  have hrho : 0 < rho := by
    dsimp only [rho]
    exact lt_min (half_pos hb) (half_pos (neg_pos.mpr ha))
  have hrhoMem : rho ∈ Ioo a b := by
    constructor
    · have hle : rho ≤ -a / 2 := min_le_right _ _
      linarith
    · have hle : rho ≤ b / 2 := min_le_left _ _
      linarith
  have hlimitSmall :
      annularCanonicalMidpointBandMassLimit ε A rho k < δ / 6 := by
    have habs := hab hrhoMem
    exact lt_of_le_of_lt (le_abs_self _) habs
  have hband :=
    eventually_norm_annularCanonicalUniformMidpointBandMarkedFourierSum_lt
      hε hεA hrho.le (show 0 < δ / 6 by positivity)
      hgrid k hr htime hsigned mode hmode
  have hlower' :=
    (Metric.tendsto_nhds.mp (hlower rho hrho)) (δ / 3) (by positivity)
  have hupper' :=
    (Metric.tendsto_nhds.mp (hupper rho hrho)) (δ / 3) (by positivity)
  have hwidth :=
    (tendsto_annularMidpointBandWidth_atTop hrho).eventually_gt_atTop 0
  filter_upwards [hband, hlower', hupper', hwidth] with
      N hbandN hlowerN hupperN hwidthN
  rw [annularUniformInterior_eq_midpoint_add_lower_add_upper
    k hr mode hmode hwidthN]
  rw [dist_zero_right] at hlowerN hupperN ⊢
  calc
    ‖annularCanonicalUniformMidpointBandMarkedFourierSum
          ε A rho N k hr mode hmode +
        annularCanonicalUniformLowerRetainedMarkedFourierSum
          ε A rho N k hr mode hmode +
        annularCanonicalUniformUpperRetainedMarkedFourierSum
          ε A rho N k hr mode hmode‖
        ≤
      ‖annularCanonicalUniformMidpointBandMarkedFourierSum
          ε A rho N k hr mode hmode‖ +
        ‖annularCanonicalUniformLowerRetainedMarkedFourierSum
          ε A rho N k hr mode hmode‖ +
        ‖annularCanonicalUniformUpperRetainedMarkedFourierSum
          ε A rho N k hr mode hmode‖ := by
      calc
        ‖annularCanonicalUniformMidpointBandMarkedFourierSum
              ε A rho N k hr mode hmode +
            annularCanonicalUniformLowerRetainedMarkedFourierSum
              ε A rho N k hr mode hmode +
            annularCanonicalUniformUpperRetainedMarkedFourierSum
              ε A rho N k hr mode hmode‖ ≤
            ‖annularCanonicalUniformMidpointBandMarkedFourierSum
                ε A rho N k hr mode hmode +
              annularCanonicalUniformLowerRetainedMarkedFourierSum
                ε A rho N k hr mode hmode‖ +
              ‖annularCanonicalUniformUpperRetainedMarkedFourierSum
                ε A rho N k hr mode hmode‖ :=
          norm_add_le _ _
        _ ≤
            (‖annularCanonicalUniformMidpointBandMarkedFourierSum
                ε A rho N k hr mode hmode‖ +
              ‖annularCanonicalUniformLowerRetainedMarkedFourierSum
                ε A rho N k hr mode hmode‖) +
              ‖annularCanonicalUniformUpperRetainedMarkedFourierSum
                ε A rho N k hr mode hmode‖ := by
          gcongr
          exact norm_add_le _ _
    _ < (annularCanonicalMidpointBandMassLimit ε A rho k + δ / 6) +
          δ / 3 + δ / 3 := by
      gcongr
    _ < δ := by
      linarith

/-! ## The exact retained interfaces and global Fourier closure -/

/-- Uniform cancellation of every lower retained tagged aggregate. -/
def GaussPrefixAnnularLowerRetainedFourierLimits : Prop :=
  ∀ {ε A : ℝ}, 0 < ε → ε < A →
    ∀ {grid : ℕ}, 0 < grid →
      ∀ (k : AnnularGridIndex grid → ℕ),
        ∀ (hr : 0 < MixedOccurrenceCount k),
        ∀ (_htime : ∀ i, 0 < k i → i.time.1 < grid),
        ∀ (_hsigned : ∀ i, 0 < k i → i.signed.1 < grid),
        ∀ (mode :
          (Fin (MixedOccurrenceCount k) ≃
              GaussPrefixMixedOccurrence k) →
            Fin (MixedOccurrenceCount k) → ℤ),
          ∀ (hmode : ∀ e, mode e ≠ 0),
          ∀ rho : ℝ, 0 < rho →
            Tendsto
              (fun N : ℕ ↦
                annularCanonicalUniformLowerRetainedMarkedFourierSum
                  ε A rho N k hr mode hmode)
              atTop (nhds 0)

/-- Uniform cancellation of every upper retained tagged aggregate. -/
def GaussPrefixAnnularUpperRetainedFourierLimits : Prop :=
  ∀ {ε A : ℝ}, 0 < ε → ε < A →
    ∀ {grid : ℕ}, 0 < grid →
      ∀ (k : AnnularGridIndex grid → ℕ),
        ∀ (hr : 0 < MixedOccurrenceCount k),
        ∀ (_htime : ∀ i, 0 < k i → i.time.1 < grid),
        ∀ (_hsigned : ∀ i, 0 < k i → i.signed.1 < grid),
        ∀ (mode :
          (Fin (MixedOccurrenceCount k) ≃
              GaussPrefixMixedOccurrence k) →
            Fin (MixedOccurrenceCount k) → ℤ),
          ∀ (hmode : ∀ e, mode e ≠ 0),
          ∀ rho : ℝ, 0 < rho →
            Tendsto
              (fun N : ℕ ↦
                annularCanonicalUniformUpperRetainedMarkedFourierSum
                  ε A rho N k hr mode hmode)
              atTop (nhds 0)

/-- The two retained cancellation theorems close every nonzero
reference-coordinate Fourier mode of the canonical annular marked
measure. -/
theorem gaussPrefixAnnularReindexedNonzeroFourierLimits_of_retained
    (hlower : GaussPrefixAnnularLowerRetainedFourierLimits)
    (hupper : GaussPrefixAnnularUpperRetainedFourierLimits) :
    GaussPrefixAnnularReindexedNonzeroFourierLimits := by
  intro ε A hε hεA grid hgrid k hr htime hsigned e₀ mode hmode
  let tagMode :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Fin (MixedOccurrenceCount k) → ℤ :=
    fun e j ↦ mode (e₀.symm (e j))
  have htagMode :
      ∀ e : Fin (MixedOccurrenceCount k) ≃
          GaussPrefixMixedOccurrence k, tagMode e ≠ 0 := by
    intro e
    exact annularOrderPulledMode_ne_zero e₀ e mode hmode
  have hinterior :
      Tendsto
        (fun N : ℕ ↦
          annularCanonicalUniformInteriorSeparatedMarkedFourierSum
            ε A N k hr tagMode)
        atTop (nhds 0) := by
    apply
      tendsto_annularUniformInteriorSeparatedMarkedFourier_zero_of_retained
        hε hεA hgrid k hr htime hsigned tagMode htagMode
    · intro rho hrho
      exact
        hlower hε hεA hgrid k hr htime hsigned
          tagMode htagMode rho hrho
    · intro rho hrho
      exact
        hupper hε hεA hgrid k hr htime hsigned
          tagMode htagMode rho hrho
  have hseparated :
      Tendsto
        (fun N : ℕ ↦
          ∑ e : Fin (MixedOccurrenceCount k) ≃
              GaussPrefixMixedOccurrence k,
            uniformMovingSignedMarkedFourierTupleSum
              N (Real.log (N : ℝ))
              (flattenedAnnularSignedLower ε A e)
              (flattenedAnnularSignedUpper ε A e)
              (tagMode e)
              (separatedCanonicalAnnularGridTupleFamily N k e))
        atTop (nhds 0) := by
    apply
      tendsto_annularCanonicalUniformSeparatedMarkedFourier_zero_of_interior
        hε hεA hgrid k hr htime hsigned tagMode
    simpa only
      [annularCanonicalUniformInteriorSeparatedMarkedFourierSum] using!
      hinterior
  have hcanonical :
      Tendsto
        (fun N : ℕ ↦
          ∑ e : Fin (MixedOccurrenceCount k) ≃
              GaussPrefixMixedOccurrence k,
            uniformMovingSignedMarkedFourierTupleSum
              N (Real.log (N : ℝ))
              (flattenedAnnularSignedLower ε A e)
              (flattenedAnnularSignedUpper ε A e)
              (tagMode e)
              (canonicalAnnularGridTupleFamily N k e))
        atTop (nhds 0) :=
    tendsto_annularCanonicalUniformMarkedFourier_zero_of_separated_including_time_zero
      hε hεA hgrid k hr htime hsigned tagMode hseparated
  simpa only [reindexedAnnularUniformMarkedFourierTupleSum, tagMode] using!
    hcanonical

end

end Erdos1002
