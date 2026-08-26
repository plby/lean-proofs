import ErdosProblems.Erdos1002.GaussPrefixAnnularUpperFreezingBoundaryAsymptotic

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Pure-digit domination of delayed-prefix endpoint strips

The exact delayed-prefix endpoint event is not a finite-prefix event: an
exact continued-fraction approximation coordinate still contains a future
tail.  Before applying prefix--future mixing we therefore dominate every
prefix coordinate by the enlarged one-digit window from the audited
exact-to-digit replacement lemma.  The future coordinates are left
unchanged.  The resulting full chronological event is a pure `r`-digit
tuple.  Its distinguished coordinate has mass `O((log N)⁻²)` and every
other coordinate has mass `O((log N)⁻¹)`.
-/

open Filter Finset MeasureTheory Set
open scoped BigOperators Topology

namespace Erdos1002

noncomputable section

set_option maxHeartbeats 2000000

local instance gaussPrefixAnnularUpperBoundaryDigitMassPropDecidable
    (P : Prop) : Decidable P := Classical.propDecidable P

variable {eta rho ε A : ℝ} {N grid : ℕ}
variable {k : AnnularGridIndex grid → ℕ}
variable {hr : 0 < MixedOccurrenceCount k}
variable
  {mode :
    (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
      Fin (MixedOccurrenceCount k) → ℤ}
variable {hmode : ∀ e, mode e ≠ 0}

/-- Lower endpoint of the full pure-digit dominating tuple. -/
def annularContractedUpperRetainedBoundaryDominatingDigitLower
    (ε A eta rho : ℝ) (N : ℕ)
    (p : AnnularContractedUpperRetainedTaggedTuple
      eta rho N k hr mode hmode)
    (i₀ : Fin (Fintype.card
      (GaussPrefixMixedPrefixOccurrence N k
        (annularContractedUpperRetainedRealization p).1
        (annularContractedUpperRetainedDelayedDepth p))))
    (upperEndpoint : Bool)
    (j : Fin (MixedOccurrenceCount k)) : ℝ :=
  annularContractedUpperRetainedBoundaryOrientedLower
    ε A eta rho N p i₀ upperEndpoint j

/-- Upper endpoint of the full pure-digit dominating tuple.  Prefix
coordinates receive precisely the deterministic `8 u² / log N`
enlargement; genuine future coordinates are unchanged. -/
def annularContractedUpperRetainedBoundaryDominatingDigitUpper
    (ε A eta rho : ℝ) (N : ℕ)
    (p : AnnularContractedUpperRetainedTaggedTuple
      eta rho N k hr mode hmode)
    (i₀ : Fin (Fintype.card
      (GaussPrefixMixedPrefixOccurrence N k
        (annularContractedUpperRetainedRealization p).1
        (annularContractedUpperRetainedDelayedDepth p))))
    (upperEndpoint : Bool)
    (j : Fin (MixedOccurrenceCount k)) : ℝ :=
  let u :=
    annularContractedUpperRetainedBoundaryOrientedUpper
      ε A eta rho N p i₀ upperEndpoint j
  if annularContractedUpperRetainedTimes p j ≤
      annularContractedUpperRetainedDelayedDepth p then
    u + 8 * u ^ 2 / Real.log (N : ℝ)
  else
    u

/-- The complete pure-digit event which dominates the digitized prefix
endpoint event intersected with the literal complete future block. -/
def annularContractedUpperRetainedBoundaryDominatingDigitEvent
    (ε A eta rho : ℝ) (N : ℕ)
    (p : AnnularContractedUpperRetainedTaggedTuple
      eta rho N k hr mode hmode)
    (i₀ : Fin (Fintype.card
      (GaussPrefixMixedPrefixOccurrence N k
        (annularContractedUpperRetainedRealization p).1
        (annularContractedUpperRetainedDelayedDepth p))))
    (upperEndpoint : Bool) : Set ℝ :=
  gaussHeterogeneousDigitTupleEvent
    (Real.log (N : ℝ))
    (annularContractedUpperRetainedBoundaryDominatingDigitLower
      ε A eta rho N p i₀ upperEndpoint)
    (annularContractedUpperRetainedBoundaryDominatingDigitUpper
      ε A eta rho N p i₀ upperEndpoint)
    (annularContractedUpperRetainedTimes p)

/-- The neutral one-digit event.  It has Gauss mass one, but unlike
`Set.univ` it is genuinely a one-digit event and can therefore be passed
to the digit `psi`-mixing theorem. -/
def gaussNeutralOneDigitEvent : Set ℝ := Ioc (0 : ℝ) 1

theorem measurableSet_gaussNeutralOneDigitEvent :
    MeasurableSet gaussNeutralOneDigitEvent :=
  measurableSet_Ioc

theorem isGaussOneDigitEvent_gaussNeutralOneDigitEvent :
    IsGaussOneDigitEvent gaussNeutralOneDigitEvent := by
  refine ⟨Set.univ, ?_⟩
  ext x
  simp [gaussNeutralOneDigitEvent]

theorem gaussMeasure_real_gaussNeutralOneDigitEvent :
    gaussMeasure.real gaussNeutralOneDigitEvent = 1 := by
  rw [measureReal_def, gaussNeutralOneDigitEvent, gaussMeasure_unit]
  norm_num

/-- Prefix-side mask of a chronological one-digit tuple. -/
def chronologicalPrefixDigitMaskEvent
    {r : ℕ} (cutoff : ℕ) (times : Fin r → ℕ)
    (events : Fin r → Set ℝ) : Set ℝ :=
  orderedEventIntersection <| List.ofFn fun i ↦
    (gaussOrbit (times i)) ⁻¹'
      if times i ≤ cutoff then events i else gaussNeutralOneDigitEvent

/-- Complementary future-side mask of the same chronological tuple. -/
def chronologicalFutureDigitMaskEvent
    {r : ℕ} (cutoff : ℕ) (times : Fin r → ℕ)
    (events : Fin r → Set ℝ) : Set ℝ :=
  orderedEventIntersection <| List.ofFn fun i ↦
    (gaussOrbit (times i)) ⁻¹'
      if cutoff < times i then events i else gaussNeutralOneDigitEvent

/-- Two separate applications of digit `psi`-mixing retain exactly one
rare coordinate factor at every chronological index.  Thus the product
of the prefix-mask mass and the future-mask mass has the same full
`r`-coordinate product as the complete tuple, at the cost of only one
additional fixed mixing factor. -/
theorem gaussMeasure_real_prefixMask_mul_futureMask_le
    {rate : ℕ → ℝ} (hpsi : GaussDigitPsiMixing rate)
    {r : ℕ} (hr : 0 < r) (cutoff : ℕ)
    (times : Fin r → ℕ) (events : Fin r → Set ℝ)
    (gap : ℕ) (hgap0 : 0 < gap)
    (hEvents : ∀ i, MeasurableSet (events i))
    (hOneDigit : ∀ i, IsGaussOneDigitEvent (events i))
    (hgap : ∀ i j, i < j → times i + gap ≤ times j)
    (hrate : 0 ≤ rate gap) :
    gaussMeasure.real
          (chronologicalPrefixDigitMaskEvent cutoff times events) *
        gaussMeasure.real
          (chronologicalFutureDigitMaskEvent cutoff times events) ≤
      (1 + rate gap) ^ (2 * (r - 1)) *
        ∏ i, gaussMeasure.real (events i) := by
  let prefixEvents : Fin r → Set ℝ := fun i ↦
    if times i ≤ cutoff then events i else gaussNeutralOneDigitEvent
  let futureEvents : Fin r → Set ℝ := fun i ↦
    if cutoff < times i then events i else gaussNeutralOneDigitEvent
  have hprefixMeas : ∀ i, MeasurableSet (prefixEvents i) := by
    intro i
    by_cases hi : times i ≤ cutoff
    · simpa only [prefixEvents, if_pos hi] using! hEvents i
    · simpa only [prefixEvents, if_neg hi] using!
        measurableSet_gaussNeutralOneDigitEvent
  have hfutureMeas : ∀ i, MeasurableSet (futureEvents i) := by
    intro i
    by_cases hi : cutoff < times i
    · simpa only [futureEvents, if_pos hi] using! hEvents i
    · simpa only [futureEvents, if_neg hi] using!
        measurableSet_gaussNeutralOneDigitEvent
  have hprefixOne : ∀ i, IsGaussOneDigitEvent (prefixEvents i) := by
    intro i
    by_cases hi : times i ≤ cutoff
    · simpa only [prefixEvents, if_pos hi] using! hOneDigit i
    · simpa only [prefixEvents, if_neg hi] using!
        isGaussOneDigitEvent_gaussNeutralOneDigitEvent
  have hfutureOne : ∀ i, IsGaussOneDigitEvent (futureEvents i) := by
    intro i
    by_cases hi : cutoff < times i
    · simpa only [futureEvents, if_pos hi] using! hOneDigit i
    · simpa only [futureEvents, if_neg hi] using!
        isGaussOneDigitEvent_gaussNeutralOneDigitEvent
  have hp :=
    hpsi.measure_orderedIntersection_le hr times prefixEvents gap
      hprefixMeas hprefixOne hgap0 hgap hrate
  have hf :=
    hpsi.measure_orderedIntersection_le hr times futureEvents gap
      hfutureMeas hfutureOne hgap0 hgap hrate
  have hprod :
      (∏ i, gaussMeasure.real (prefixEvents i)) *
          ∏ i, gaussMeasure.real (futureEvents i) =
        ∏ i, gaussMeasure.real (events i) := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i _hi
    by_cases hi : times i ≤ cutoff
    · have hnot : ¬cutoff < times i := Nat.not_lt.mpr hi
      simp only [prefixEvents, futureEvents, if_pos hi, if_neg hnot,
        gaussMeasure_real_gaussNeutralOneDigitEvent, mul_one]
    · have hlt : cutoff < times i := Nat.lt_of_not_ge hi
      simp only [prefixEvents, futureEvents, if_neg hi, if_pos hlt,
        gaussMeasure_real_gaussNeutralOneDigitEvent, one_mul]
  have hmixNonneg : 0 ≤ (1 + rate gap) ^ (r - 1) := by
    positivity
  calc
    gaussMeasure.real
          (chronologicalPrefixDigitMaskEvent cutoff times events) *
        gaussMeasure.real
          (chronologicalFutureDigitMaskEvent cutoff times events) ≤
      ((1 + rate gap) ^ (r - 1) *
          ∏ i, gaussMeasure.real (prefixEvents i)) *
        ((1 + rate gap) ^ (r - 1) *
          ∏ i, gaussMeasure.real (futureEvents i)) := by
      apply mul_le_mul hp hf measureReal_nonneg
      exact mul_nonneg hmixNonneg
        (Finset.prod_nonneg fun _i _hi ↦ measureReal_nonneg)
    _ = (1 + rate gap) ^ (2 * (r - 1)) *
        ∏ i, gaussMeasure.real (events i) := by
      calc
        ((1 + rate gap) ^ (r - 1) *
              ∏ i, gaussMeasure.real (prefixEvents i)) *
            ((1 + rate gap) ^ (r - 1) *
              ∏ i, gaussMeasure.real (futureEvents i)) =
          ((1 + rate gap) ^ (r - 1) *
              (1 + rate gap) ^ (r - 1)) *
            ((∏ i, gaussMeasure.real (prefixEvents i)) *
              ∏ i, gaussMeasure.real (futureEvents i)) := by ring
        _ =
          ((1 + rate gap) ^ (r - 1) *
              (1 + rate gap) ^ (r - 1)) *
            ∏ i, gaussMeasure.real (events i) := by rw [hprod]
        _ = _ := by
          rw [← pow_add]
          congr 2
          omega

/-- Uniform distinguished-coordinate numerator.  It depends only on the
fixed outer endpoint `A`, never on the tag or on `N`. -/
def annularUpperBoundaryDominatingDigitNumerator (A : ℝ) : ℝ :=
  40 * A ^ 2 + 10 * (A + 16 * A ^ 2) ^ 2

/-- Coordinate-product majorant before the chronological `psi`-mixing
factor is inserted. -/
def annularUpperBoundaryDominatingDigitCoordinateMassBound
    (r : ℕ) (scale A : ℝ) : ℝ :=
  ((annularUpperBoundaryDominatingDigitNumerator A / scale ^ 2) /
      Real.log 2) *
    ((((4 * A + 40 * A ^ 2) / scale) / Real.log 2) ^ (r - 1))

/-- Uniform mass majorant for one full pure-digit dominating event. -/
def annularUpperBoundaryDominatingDigitMassBound
    (r : ℕ) (scale A : ℝ) : ℝ :=
  (1 + gaussDigitExponentialRate 1) ^ (r - 1) *
    (((annularUpperBoundaryDominatingDigitNumerator A / scale ^ 2) /
        Real.log 2) *
      ((((4 * A + 40 * A ^ 2) / scale) / Real.log 2) ^ (r - 1)))

theorem annularUpperBoundaryDominatingDigitMassBound_nonneg
    (r : ℕ) {scale A : ℝ} (hscale : 0 < scale) (hA : 0 ≤ A) :
    0 ≤ annularUpperBoundaryDominatingDigitMassBound r scale A := by
  have hrate : 0 ≤ gaussDigitExponentialRate 1 :=
    gaussDigitExponentialRate_nonnegative 1
  have hlog : 0 < Real.log 2 := Real.log_pos one_lt_two
  unfold annularUpperBoundaryDominatingDigitMassBound
    annularUpperBoundaryDominatingDigitNumerator
  positivity

/-- The product of all one-coordinate masses has the sharp boundary
order `scale⁻(r+1)`, before any mixing factor is paid. -/
theorem finprod_gaussMeasure_real_annularContractedUpperRetainedBoundaryDominatingDigit_le
    (hε : 0 < ε) (hεA : ε < A) (hgrid : 0 < grid)
    (hsigned : ∀ i, 0 < k i → i.signed.1 < grid)
    (p : AnnularContractedUpperRetainedTaggedTuple
      eta rho N k hr mode hmode)
    (i₀ : Fin (Fintype.card
      (GaussPrefixMixedPrefixOccurrence N k
        (annularContractedUpperRetainedRealization p).1
        (annularContractedUpperRetainedDelayedDepth p))))
    (upperEndpoint : Bool)
    (hN : 1 < N)
    (hscaleOne : 1 ≤ Real.log (N : ℝ))
    (hv :
      annularContractedUpperRetainedPrefixValueRadius eta rho N p ≤
        ε / 4)
    (hvScale :
      annularContractedUpperRetainedPrefixValueRadius eta rho N p *
          Real.log (N : ℝ) ≤
        (2 * A) ^ 2)
    (hlargeScale : 128 * A ^ 2 ≤ ε * Real.log (N : ℝ)) :
    (∏ j : Fin (MixedOccurrenceCount k),
        gaussMeasure.real
          (scaledGaussFirstDigitWindow
            (Real.log (N : ℝ))
            (annularContractedUpperRetainedBoundaryDominatingDigitLower
              ε A eta rho N p i₀ upperEndpoint j)
            (annularContractedUpperRetainedBoundaryDominatingDigitUpper
              ε A eta rho N p i₀ upperEndpoint j))) ≤
      annularUpperBoundaryDominatingDigitCoordinateMassBound
        (MixedOccurrenceCount k) (Real.log (N : ℝ)) A := by
  let r := MixedOccurrenceCount k
  let scale := Real.log (N : ℝ)
  let rawLower :=
    annularContractedUpperRetainedBoundaryOrientedLower
      ε A eta rho N p i₀ upperEndpoint
  let rawUpper :=
    annularContractedUpperRetainedBoundaryOrientedUpper
      ε A eta rho N p i₀ upperEndpoint
  let lower :=
    annularContractedUpperRetainedBoundaryDominatingDigitLower
      ε A eta rho N p i₀ upperEndpoint
  let upper :=
    annularContractedUpperRetainedBoundaryDominatingDigitUpper
      ε A eta rho N p i₀ upperEndpoint
  let times := annularContractedUpperRetainedTimes p
  let j₀ :=
    annularContractedUpperRetainedPrefixChronologicalIndex p i₀
  let v :=
    annularContractedUpperRetainedPrefixValueRadius eta rho N p
  let center :=
    annularContractedUpperRetainedBoundaryOrientedCenter
      ε A p i₀ upperEndpoint
  let rawDistUpper := rawUpper j₀
  let shiftedCenter := center + 4 * rawDistUpper ^ 2 / scale
  let shiftedWidth := v * scale + 4 * rawDistUpper ^ 2
  let boundaryMass :=
    (annularUpperBoundaryDominatingDigitNumerator A / scale ^ 2) /
      Real.log 2
  let windowMass :=
    ((4 * A + 40 * A ^ 2) / scale) / Real.log 2
  have hscale : 0 < scale := by
    dsimp only [scale]
    exact Real.log_pos (by exact_mod_cast hN)
  have hvpos : 0 < v := by
    simpa only [v] using!
      annularContractedUpperRetainedPrefixValueRadius_pos p hN
  have hcenterMem : center ∈ Icc ε A := by
    simpa only [center] using!
      annularContractedUpperRetainedBoundaryOrientedCenter_mem_Icc
        hεA hgrid hsigned p i₀ upperEndpoint
  have hcenterPos : 0 < center := hε.trans_le hcenterMem.1
  have hApos : 0 < A := hε.trans hεA
  have hrawLower : ∀ j, 0 < rawLower j := by
    intro j
    exact lt_of_lt_of_le (by linarith)
      (annularContractedUpperRetainedBoundaryOrientedLower_ge_half
        hε hεA hgrid hsigned p i₀ upperEndpoint hv j)
  have hrawUpper : ∀ j, rawLower j < rawUpper j := by
    intro j
    exact
      annularContractedUpperRetainedBoundaryOrientedLower_lt_upper
        hεA hgrid p i₀ upperEndpoint
          (by simpa only [v] using! hvpos) j
  have hrawUpperA : ∀ j, rawUpper j ≤ 2 * A := by
    intro j
    exact
      annularContractedUpperRetainedBoundaryOrientedUpper_le_two
        hε hεA hgrid hsigned p i₀ upperEndpoint hv j
  have hrawUpperPos : ∀ j, 0 < rawUpper j :=
    fun j ↦ (hrawLower j).trans (hrawUpper j)
  have hlarge : ∀ j, 16 * (rawUpper j) ^ 2 ≤
      rawLower j * scale := by
    intro j
    simpa only [rawLower, rawUpper, scale] using!
      annularContractedUpperRetainedBoundary_large
        hε hεA hgrid hsigned p i₀ upperEndpoint hv
          (by simpa only [scale] using! hscale) hlargeScale j
  have hjPrefix :
      times j₀ ≤ annularContractedUpperRetainedDelayedDepth p := by
    simpa only [times, j₀] using!
      annularContractedUpperRetainedPrefixChronologicalIndex_le_delayed
        p i₀
  have hjLower : rawLower j₀ = center - v := by
    simpa only [rawLower, center, v, j₀] using!
      annularContractedUpperRetainedBoundaryOrientedLower_of_distinguished
        (ε := ε) (A := A) p i₀ upperEndpoint
  have hjUpper : rawDistUpper = center + v := by
    simpa only [rawDistUpper, rawUpper, center, v, j₀] using!
      annularContractedUpperRetainedBoundaryOrientedUpper_of_distinguished
        (ε := ε) (A := A) p i₀ upperEndpoint
  have hrawDistUpperPos : 0 < rawDistUpper := by
    simpa only [rawDistUpper] using! hrawUpperPos j₀
  have hrawDistUpperA : rawDistUpper ≤ 2 * A := by
    simpa only [rawDistUpper] using! hrawUpperA j₀
  have hshiftedCenterPos : 0 < shiftedCenter := by
    dsimp only [shiftedCenter]
    positivity
  have hshiftedWidthPos : 0 < shiftedWidth := by
    dsimp only [shiftedWidth]
    positivity
  have hshiftedWidthBound : shiftedWidth ≤ 20 * A ^ 2 := by
    have hsquare : rawDistUpper ^ 2 ≤ (2 * A) ^ 2 := by
      nlinarith [hrawDistUpperPos, hrawDistUpperA]
    dsimp only [shiftedWidth]
    nlinarith [hvScale, hsquare]
  have hshiftedCenterBound :
      shiftedCenter ≤ A + 16 * A ^ 2 := by
    have hsquare : rawDistUpper ^ 2 ≤ (2 * A) ^ 2 := by
      nlinarith [hrawDistUpperPos, hrawDistUpperA]
    have hdiv :
        4 * rawDistUpper ^ 2 / scale ≤ 16 * A ^ 2 := by
      have hscaleInv : 1 / scale ≤ 1 := by
        rw [div_eq_mul_inv]
        simpa only [one_mul] using! (inv_le_one₀ hscale).2 hscaleOne
      calc
        4 * rawDistUpper ^ 2 / scale =
            (4 * rawDistUpper ^ 2) * (1 / scale) := by ring
        _ ≤ (4 * rawDistUpper ^ 2) * 1 := by
          gcongr
        _ ≤ 16 * A ^ 2 := by nlinarith
    dsimp only [shiftedCenter]
    nlinarith [hcenterMem.2]
  have hshiftedSize :
      2 * shiftedWidth ≤ shiftedCenter * scale := by
    have hwidth :
        2 * shiftedWidth ≤ 40 * A ^ 2 := by
      linarith [hshiftedWidthBound]
    have hcenterScale :
        128 * A ^ 2 ≤ shiftedCenter * scale := by
      have hc : ε ≤ shiftedCenter := by
        calc
          ε ≤ center := hcenterMem.1
          _ ≤ shiftedCenter := by
            dsimp only [shiftedCenter]
            exact le_add_of_nonneg_right (by positivity)
      have := mul_le_mul_of_nonneg_right hc hscale.le
      exact hlargeScale.trans this
    linarith [sq_nonneg A]
  have hdistinguishedSet :
      scaledGaussFirstDigitWindow scale (lower j₀) (upper j₀) =
        scaledGaussFirstDigitBoundaryStrip
          scale shiftedCenter shiftedWidth := by
    rw [scaledGaussFirstDigitBoundaryStrip_eq_window]
    have hlowerDef : lower j₀ = rawLower j₀ := rfl
    have hupperDef :
        upper j₀ =
          rawDistUpper + 8 * rawDistUpper ^ 2 / scale := by
      dsimp only [upper,
        annularContractedUpperRetainedBoundaryDominatingDigitUpper]
      rw [if_pos (by simpa only [times] using! hjPrefix)]
    congr 1
    · rw [hlowerDef, hjLower]
      dsimp only [shiftedCenter, shiftedWidth]
      field_simp [ne_of_gt hscale]
      ring
    · rw [hupperDef, hjUpper]
      dsimp only [shiftedCenter, shiftedWidth]
      rw [hjUpper]
      field_simp [ne_of_gt hscale]
      ring
  have hboundary :
      gaussMeasure.real
          (scaledGaussFirstDigitWindow scale (lower j₀) (upper j₀)) ≤
        boundaryMass := by
    rw [hdistinguishedSet]
    have hraw :=
      gaussMeasure_real_scaledGaussFirstDigitBoundaryStrip_le
        hscale hshiftedCenterPos hshiftedWidthPos hshiftedSize
    have hcenterSq :
        shiftedCenter ^ 2 ≤ (A + 16 * A ^ 2) ^ 2 := by
      apply (sq_le_sq₀ hshiftedCenterPos.le (by positivity)).2
      exact hshiftedCenterBound
    calc
      gaussMeasure.real
          (scaledGaussFirstDigitBoundaryStrip
            scale shiftedCenter shiftedWidth) ≤
        ((2 * shiftedWidth + 10 * shiftedCenter ^ 2) / scale ^ 2) /
          Real.log 2 := hraw
      _ ≤ boundaryMass := by
        dsimp only [boundaryMass,
          annularUpperBoundaryDominatingDigitNumerator]
        apply (div_le_div_iff_of_pos_right
          (Real.log_pos one_lt_two)).2
        apply (div_le_div_iff_of_pos_right (sq_pos_of_pos hscale)).2
        nlinarith [hshiftedWidthBound, hcenterSq]
  have hwindow :
      ∀ j, j ≠ j₀ →
        gaussMeasure.real
            (scaledGaussFirstDigitWindow scale (lower j) (upper j)) ≤
          windowMass := by
    intro j _hj
    have hrawBound :=
      gaussMeasure_real_gaussEnlargedDigitWindow_le
        hscale hscaleOne (hrawLower j) (hrawUpper j) (hlarge j)
    have hrawSq : (rawUpper j) ^ 2 ≤ (2 * A) ^ 2 := by
      nlinarith [hrawUpperPos j, hrawUpperA j]
    have hnum :
        2 * rawUpper j + 10 * (rawUpper j) ^ 2 ≤
          4 * A + 40 * A ^ 2 := by
      nlinarith [hrawUpperA j, hrawSq]
    by_cases hj :
        times j ≤ annularContractedUpperRetainedDelayedDepth p
    · have heq :
          scaledGaussFirstDigitWindow scale (lower j) (upper j) =
            gaussEnlargedDigitWindow scale (rawLower j) (rawUpper j) := by
        unfold gaussEnlargedDigitWindow
        have hlowerDef : lower j = rawLower j := rfl
        have hupperDef :
            upper j = rawUpper j + 8 * rawUpper j ^ 2 / scale := by
          dsimp only [upper,
            annularContractedUpperRetainedBoundaryDominatingDigitUpper]
          rw [if_pos (by simpa only [times] using! hj)]
        rw [hlowerDef, hupperDef]
      rw [heq]
      exact hrawBound.trans <| by
        dsimp only [windowMass]
        apply (div_le_div_iff_of_pos_right
          (Real.log_pos one_lt_two)).2
        exact (div_le_div_iff_of_pos_right hscale).2 hnum
    · have hsubset :
          scaledGaussFirstDigitWindow scale (lower j) (upper j) ⊆
            gaussEnlargedDigitWindow scale (rawLower j) (rawUpper j) := by
        have hbase :
            scaledGaussFirstDigitWindow scale (rawLower j) (rawUpper j) ⊆
              gaussEnlargedDigitWindow scale (rawLower j) (rawUpper j) :=
          scaledGaussFirstDigitWindow_subset_gaussEnlargedDigitWindow
            hscale
        have hlowerDef : lower j = rawLower j := rfl
        have hupperDef : upper j = rawUpper j := by
          dsimp only [upper,
            annularContractedUpperRetainedBoundaryDominatingDigitUpper]
          rw [if_neg (by simpa only [times] using! hj)]
        simpa only [hlowerDef, hupperDef] using! hbase
      exact (measureReal_mono hsubset).trans <| hrawBound.trans <| by
        dsimp only [windowMass]
        apply (div_le_div_iff_of_pos_right
          (Real.log_pos one_lt_two)).2
        exact (div_le_div_iff_of_pos_right hscale).2 hnum
  have hprod :=
    fin_prod_measure_le_boundary_mul_window_pow
      (fun j ↦
        scaledGaussFirstDigitWindow scale (lower j) (upper j))
      j₀
      (boundaryMass := boundaryMass)
      (windowMass := windowMass)
      (by
        dsimp only [boundaryMass,
          annularUpperBoundaryDominatingDigitNumerator]
        positivity)
      hboundary hwindow
  simpa only [
    lower, upper, boundaryMass, windowMass, r,
    annularUpperBoundaryDominatingDigitCoordinateMassBound] using! hprod

/-- Uniform full-event mass bound obtained by inserting the single
chronological mixing factor into the coordinate-product estimate. -/
theorem gaussMeasure_real_annularContractedUpperRetainedBoundaryDominatingDigitEvent_le
    (hε : 0 < ε) (hεA : ε < A) (hgrid : 0 < grid)
    (hsigned : ∀ i, 0 < k i → i.signed.1 < grid)
    (p : AnnularContractedUpperRetainedTaggedTuple
      eta rho N k hr mode hmode)
    (i₀ : Fin (Fintype.card
      (GaussPrefixMixedPrefixOccurrence N k
        (annularContractedUpperRetainedRealization p).1
        (annularContractedUpperRetainedDelayedDepth p))))
    (upperEndpoint : Bool)
    (hN : 1 < N)
    (hscaleOne : 1 ≤ Real.log (N : ℝ))
    (hv :
      annularContractedUpperRetainedPrefixValueRadius eta rho N p ≤
        ε / 4)
    (hvScale :
      annularContractedUpperRetainedPrefixValueRadius eta rho N p *
          Real.log (N : ℝ) ≤
        (2 * A) ^ 2)
    (hlargeScale : 128 * A ^ 2 ≤ ε * Real.log (N : ℝ)) :
    gaussMeasure.real
        (annularContractedUpperRetainedBoundaryDominatingDigitEvent
          ε A eta rho N p i₀ upperEndpoint) ≤
      annularUpperBoundaryDominatingDigitMassBound
        (MixedOccurrenceCount k) (Real.log (N : ℝ)) A := by
  let lower :=
    annularContractedUpperRetainedBoundaryDominatingDigitLower
      ε A eta rho N p i₀ upperEndpoint
  let upper :=
    annularContractedUpperRetainedBoundaryDominatingDigitUpper
      ε A eta rho N p i₀ upperEndpoint
  let times := annularContractedUpperRetainedTimes p
  have hgap : ∀ i j, i < j → times i + 1 ≤ times j := by
    simpa only [times] using!
      contractedAnnularCanonicalLaterUpperMidpointTupleFamily_chronological
        k hr p.1 (mode p.1) (hmode p.1)
          (annularContractedUpperRetainedTimes p) p.2.2
  have hbase :=
    gaussDigitPsiMixing_exponential.measure_heterogeneousDigitTupleEvent_le
      (scale := Real.log (N : ℝ))
      hr lower upper times 1 (by norm_num) hgap
        (gaussDigitExponentialRate_nonnegative 1)
  have hprod :=
    finprod_gaussMeasure_real_annularContractedUpperRetainedBoundaryDominatingDigit_le
      hε hεA hgrid hsigned p i₀ upperEndpoint
        hN hscaleOne hv hvScale hlargeScale
  exact hbase.trans <| by
    apply mul_le_mul_of_nonneg_left hprod
    exact pow_nonneg
      (by
        have hrate := gaussDigitExponentialRate_nonnegative 1
        linarith)
      _

theorem annularUpperBoundaryDominatingDigitMassBound_eq_scale
    (r : ℕ) (hr : 0 < r) (A scale : ℝ) (hscale : scale ≠ 0) :
    annularUpperBoundaryDominatingDigitMassBound r scale A =
      annularUpperBoundaryDominatingDigitMassBound r 1 A *
        scale⁻¹ ^ (r + 1) := by
  have hlog : Real.log 2 ≠ 0 :=
    ne_of_gt (Real.log_pos one_lt_two)
  have hrPow : r + 1 = 2 + (r - 1) := by omega
  unfold annularUpperBoundaryDominatingDigitMassBound
  rw [hrPow, pow_add]
  have hwindow :
      ((4 * A + 40 * A ^ 2) / scale) / Real.log 2 =
        (((4 * A + 40 * A ^ 2) / 1) / Real.log 2) * scale⁻¹ := by
    field_simp [hscale, hlog]
  rw [hwindow, mul_pow]
  field_simp [hscale, hlog]

theorem tendsto_annularDepth_pow_mul_boundaryDominatingDigitMassBound_zero
    (r : ℕ) (hr : 0 < r) (A : ℝ) :
    Tendsto
      (fun N : ℕ ↦
        (annularDepthAmbientSize N : ℝ) ^ r *
          annularUpperBoundaryDominatingDigitMassBound
            r (Real.log (N : ℝ)) A)
      atTop (nhds 0) := by
  let C := annularUpperBoundaryDominatingDigitMassBound r 1 A
  have hratio := tendsto_annularDepthAmbientSize_div_log.pow r
  have hinv :
      Tendsto (fun N : ℕ ↦ (Real.log (N : ℝ))⁻¹)
        atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp tendsto_log_natCast_atTop
  have hproduct :=
    ((tendsto_const_nhds.mul hratio).mul hinv :
      Tendsto
        (fun N : ℕ ↦
          C *
            ((annularDepthAmbientSize N : ℝ) /
              Real.log (N : ℝ)) ^ r *
            (Real.log (N : ℝ))⁻¹)
        atTop
        (nhds (C * (1 / gaussRoofMean) ^ r * 0)))
  have hzero :
      Tendsto
        (fun N : ℕ ↦
          C *
            ((annularDepthAmbientSize N : ℝ) /
              Real.log (N : ℝ)) ^ r *
            (Real.log (N : ℝ))⁻¹)
        atTop (nhds 0) := by
    simpa only [mul_zero] using! hproduct
  apply hzero.congr'
  filter_upwards
    [tendsto_log_natCast_atTop.eventually_gt_atTop 0] with N hlog
  have hlogNe : Real.log (N : ℝ) ≠ 0 := ne_of_gt hlog
  rw [annularUpperBoundaryDominatingDigitMassBound_eq_scale
    r hr A (Real.log (N : ℝ)) hlogNe]
  dsimp only [C]
  rw [div_pow]
  rw [show r + 1 = Nat.succ r by omega, pow_succ]
  field_simp [hlogNe]
  rw [one_div_pow]
  field_simp [hlogNe]

end

end Erdos1002
