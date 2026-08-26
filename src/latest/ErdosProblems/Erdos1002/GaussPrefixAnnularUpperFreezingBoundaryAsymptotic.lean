import ErdosProblems.Erdos1002.GaussPrefixAnnularUpperFreezingEventBridge
import ErdosProblems.Erdos1002.GaussPrefixAnnularUpperFreezingPhaseAsymptotic
import ErdosProblems.Erdos1002.GaussPrefixAnnularUpperDensityAggregate

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Quantitative endpoint-strip summation for upper character freezing

Each endpoint error is first associated with a complete chronological
masked event.  The distinguished coordinate has width twice the freezing
radius; all remaining prefix rare windows and the entire future digit block
stay attached.  The heterogeneous boundary estimate therefore supplies one
extra inverse logarithm, which survives the sharp `O(H^r)` tagged-family
summation.
-/

open Filter Finset MeasureTheory Set
open scoped BigOperators Topology symmDiff

namespace Erdos1002

noncomputable section

set_option maxHeartbeats 2000000

local instance gaussPrefixAnnularUpperFreezingBoundaryAsymptoticPropDecidable
    (P : Prop) : Decidable P := Classical.propDecidable P

variable {eta rho ε A : ℝ} {N grid : ℕ}
variable {k : AnnularGridIndex grid → ℕ}
variable {hr : 0 < MixedOccurrenceCount k}
variable
  {mode :
    (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
      Fin (MixedOccurrenceCount k) → ℤ}
variable {hmode : ∀ e, mode e ≠ 0}

private theorem measureReal_mono_ae_of_finite_local
    {α : Type*} [MeasurableSpace α]
    (mu : Measure α) [IsFiniteMeasure mu] {s t : Set α}
    (h : s ≤ᶠ[ae mu] t) :
    mu.real s ≤ mu.real t := by
  rw [measureReal_def, measureReal_def,
    ENNReal.toReal_le_toReal (measure_ne_top mu s) (measure_ne_top mu t)]
  exact measure_mono_ae h

theorem annularContractedUpperRetainedPrefixValueRadius_pos
    (p : AnnularContractedUpperRetainedTaggedTuple
      eta rho N k hr mode hmode)
    (hN : 1 < N) :
    0 <
      annularContractedUpperRetainedPrefixValueRadius eta rho N p := by
  unfold annularContractedUpperRetainedPrefixValueRadius
    gaussPrefixGoodValueFreezingRadius
  exact mul_pos
    (mul_pos (by norm_num) (Real.log_pos (by exact_mod_cast hN)))
    (Real.exp_pos _)

theorem annularContractedUpperRetainedBoundaryOrientedCenter_mem_Icc
    (hεA : ε < A) (hgrid : 0 < grid)
    (hsigned : ∀ i, 0 < k i → i.signed.1 < grid)
    (p : AnnularContractedUpperRetainedTaggedTuple
      eta rho N k hr mode hmode)
    (i₀ : Fin (Fintype.card
      (GaussPrefixMixedPrefixOccurrence N k
        (annularContractedUpperRetainedRealization p).1
        (annularContractedUpperRetainedDelayedDepth p))))
    (upperEndpoint : Bool) :
    annularContractedUpperRetainedBoundaryOrientedCenter
        ε A p i₀ upperEndpoint ∈ Icc ε A := by
  let j₀ :=
    annularContractedUpperRetainedPrefixChronologicalIndex p i₀
  have hlower :=
    annularContractedUpperRetainedBaseOrientedLower_ge
      hεA hgrid hsigned p j₀
  have hupper :=
    annularContractedUpperRetainedBaseOrientedUpper_le
      hεA hgrid hsigned p j₀
  have hstrict :=
    annularContractedUpperRetainedBaseOrientedLower_lt_upper
      hεA hgrid p j₀
  have hlowerA :
      gaussParityOrientedLower
          (annularContractedUpperRetainedTimes p j₀)
          (flattenedAnnularSignedLower ε A p.1 j₀)
          (flattenedAnnularSignedUpper ε A p.1 j₀) ≤ A :=
    hstrict.le.trans hupper
  have hupperE :
      ε ≤
        gaussParityOrientedUpper
          (annularContractedUpperRetainedTimes p j₀)
          (flattenedAnnularSignedLower ε A p.1 j₀)
          (flattenedAnnularSignedUpper ε A p.1 j₀) :=
    hlower.trans hstrict.le
  cases upperEndpoint with
  | false =>
      by_cases hn :
          Even (annularContractedUpperRetainedTimes p j₀)
      · constructor
        · simpa only [
            annularContractedUpperRetainedBoundaryOrientedCenter,
            annularContractedUpperRetainedBoundarySignedCenter,
            Bool.false_eq_true, ↓reduceIte, j₀, if_pos hn,
            gaussParityOrientedLower, if_pos hn] using! hlower
        · simpa only [
            annularContractedUpperRetainedBoundaryOrientedCenter,
            annularContractedUpperRetainedBoundarySignedCenter,
            Bool.false_eq_true, ↓reduceIte, j₀, if_pos hn,
            gaussParityOrientedLower, if_pos hn] using! hlowerA
      · constructor
        · simpa only [
            annularContractedUpperRetainedBoundaryOrientedCenter,
            annularContractedUpperRetainedBoundarySignedCenter,
            Bool.false_eq_true, ↓reduceIte, j₀, if_neg hn,
            gaussParityOrientedUpper, if_neg hn] using! hupperE
        · simpa only [
            annularContractedUpperRetainedBoundaryOrientedCenter,
            annularContractedUpperRetainedBoundarySignedCenter,
            Bool.false_eq_true, ↓reduceIte, j₀, if_neg hn,
            gaussParityOrientedUpper, if_neg hn] using! hupper
  | true =>
      by_cases hn :
          Even (annularContractedUpperRetainedTimes p j₀)
      · constructor
        · simpa only [
            annularContractedUpperRetainedBoundaryOrientedCenter,
            annularContractedUpperRetainedBoundarySignedCenter,
            ↓reduceIte, j₀, if_pos hn,
            gaussParityOrientedUpper, if_pos hn] using! hupperE
        · simpa only [
            annularContractedUpperRetainedBoundaryOrientedCenter,
            annularContractedUpperRetainedBoundarySignedCenter,
            ↓reduceIte, j₀, if_pos hn,
            gaussParityOrientedUpper, if_pos hn] using! hupper
      · constructor
        · simpa only [
            annularContractedUpperRetainedBoundaryOrientedCenter,
            annularContractedUpperRetainedBoundarySignedCenter,
            ↓reduceIte, j₀, if_neg hn,
            gaussParityOrientedLower, if_neg hn] using! hlower
        · simpa only [
            annularContractedUpperRetainedBoundaryOrientedCenter,
            annularContractedUpperRetainedBoundarySignedCenter,
            ↓reduceIte, j₀, if_neg hn,
            gaussParityOrientedLower, if_neg hn] using! hlowerA

theorem annularContractedUpperRetainedBoundaryOrientedLower_ge_half
    (hε : 0 < ε) (hεA : ε < A) (hgrid : 0 < grid)
    (hsigned : ∀ i, 0 < k i → i.signed.1 < grid)
    (p : AnnularContractedUpperRetainedTaggedTuple
      eta rho N k hr mode hmode)
    (i₀ : Fin (Fintype.card
      (GaussPrefixMixedPrefixOccurrence N k
        (annularContractedUpperRetainedRealization p).1
        (annularContractedUpperRetainedDelayedDepth p))))
    (upperEndpoint : Bool)
    (hv :
      annularContractedUpperRetainedPrefixValueRadius eta rho N p ≤
        ε / 4)
    (j : Fin (MixedOccurrenceCount k)) :
    ε / 2 ≤
      annularContractedUpperRetainedBoundaryOrientedLower
        ε A eta rho N p i₀ upperEndpoint j := by
  rw [annularContractedUpperRetainedBoundaryOrientedLower_eq]
  by_cases hj :
      annularContractedUpperRetainedTimes p j ≤
        annularContractedUpperRetainedDelayedDepth p
  · rw [if_pos hj]
    by_cases hj₀ :
        j = annularContractedUpperRetainedPrefixChronologicalIndex p i₀
    · rw [if_pos hj₀]
      have hc :=
        (annularContractedUpperRetainedBoundaryOrientedCenter_mem_Icc
          hεA hgrid hsigned p i₀ upperEndpoint).1
      linarith
    · rw [if_neg hj₀]
      have hb :=
        annularContractedUpperRetainedBaseOrientedLower_ge
          hεA hgrid hsigned p j
      linarith
  · rw [if_neg hj]
    exact
      (by linarith :
        ε / 2 ≤ ε).trans
        (annularContractedUpperRetainedBaseOrientedLower_ge
          hεA hgrid hsigned p j)

theorem annularContractedUpperRetainedBoundaryOrientedUpper_le_two
    (hε : 0 < ε) (hεA : ε < A) (hgrid : 0 < grid)
    (hsigned : ∀ i, 0 < k i → i.signed.1 < grid)
    (p : AnnularContractedUpperRetainedTaggedTuple
      eta rho N k hr mode hmode)
    (i₀ : Fin (Fintype.card
      (GaussPrefixMixedPrefixOccurrence N k
        (annularContractedUpperRetainedRealization p).1
        (annularContractedUpperRetainedDelayedDepth p))))
    (upperEndpoint : Bool)
    (hv :
      annularContractedUpperRetainedPrefixValueRadius eta rho N p ≤
        ε / 4)
    (j : Fin (MixedOccurrenceCount k)) :
    annularContractedUpperRetainedBoundaryOrientedUpper
        ε A eta rho N p i₀ upperEndpoint j ≤ 2 * A := by
  rw [annularContractedUpperRetainedBoundaryOrientedUpper_eq]
  by_cases hj :
      annularContractedUpperRetainedTimes p j ≤
        annularContractedUpperRetainedDelayedDepth p
  · rw [if_pos hj]
    by_cases hj₀ :
        j = annularContractedUpperRetainedPrefixChronologicalIndex p i₀
    · rw [if_pos hj₀]
      have hc :=
        (annularContractedUpperRetainedBoundaryOrientedCenter_mem_Icc
          hεA hgrid hsigned p i₀ upperEndpoint).2
      linarith
    · rw [if_neg hj₀]
      have hb :=
        annularContractedUpperRetainedBaseOrientedUpper_le
          hεA hgrid hsigned p j
      linarith
  · rw [if_neg hj]
    exact
      (annularContractedUpperRetainedBaseOrientedUpper_le
        hεA hgrid hsigned p j).trans (by linarith)

theorem annularContractedUpperRetainedBoundaryOrientedLower_lt_upper
    (hεA : ε < A) (hgrid : 0 < grid)
    (p : AnnularContractedUpperRetainedTaggedTuple
      eta rho N k hr mode hmode)
    (i₀ : Fin (Fintype.card
      (GaussPrefixMixedPrefixOccurrence N k
        (annularContractedUpperRetainedRealization p).1
        (annularContractedUpperRetainedDelayedDepth p))))
    (upperEndpoint : Bool)
    (hvpos :
      0 <
        annularContractedUpperRetainedPrefixValueRadius eta rho N p)
    (j : Fin (MixedOccurrenceCount k)) :
    annularContractedUpperRetainedBoundaryOrientedLower
        ε A eta rho N p i₀ upperEndpoint j <
      annularContractedUpperRetainedBoundaryOrientedUpper
        ε A eta rho N p i₀ upperEndpoint j := by
  rw [annularContractedUpperRetainedBoundaryOrientedLower_eq,
    annularContractedUpperRetainedBoundaryOrientedUpper_eq]
  by_cases hj :
      annularContractedUpperRetainedTimes p j ≤
        annularContractedUpperRetainedDelayedDepth p
  · rw [if_pos hj, if_pos hj]
    by_cases hj₀ :
        j = annularContractedUpperRetainedPrefixChronologicalIndex p i₀
    · rw [if_pos hj₀, if_pos hj₀]
      linarith
    · rw [if_neg hj₀, if_neg hj₀]
      have hb :=
        annularContractedUpperRetainedBaseOrientedLower_lt_upper
          hεA hgrid p j
      linarith
  · rw [if_neg hj, if_neg hj]
    exact annularContractedUpperRetainedBaseOrientedLower_lt_upper
      hεA hgrid p j

theorem annularContractedUpperRetainedBoundary_large
    (hε : 0 < ε) (hεA : ε < A) (hgrid : 0 < grid)
    (hsigned : ∀ i, 0 < k i → i.signed.1 < grid)
    (p : AnnularContractedUpperRetainedTaggedTuple
      eta rho N k hr mode hmode)
    (i₀ : Fin (Fintype.card
      (GaussPrefixMixedPrefixOccurrence N k
        (annularContractedUpperRetainedRealization p).1
        (annularContractedUpperRetainedDelayedDepth p))))
    (upperEndpoint : Bool)
    (hv :
      annularContractedUpperRetainedPrefixValueRadius eta rho N p ≤
        ε / 4)
    (hscale : 0 < Real.log (N : ℝ))
    (hlargeScale : 128 * A ^ 2 ≤ ε * Real.log (N : ℝ))
    (j : Fin (MixedOccurrenceCount k)) :
    16 *
        (annularContractedUpperRetainedBoundaryOrientedUpper
          ε A eta rho N p i₀ upperEndpoint j) ^ 2 ≤
      annularContractedUpperRetainedBoundaryOrientedLower
          ε A eta rho N p i₀ upperEndpoint j *
        Real.log (N : ℝ) := by
  let lower :=
    annularContractedUpperRetainedBoundaryOrientedLower
      ε A eta rho N p i₀ upperEndpoint j
  let upper :=
    annularContractedUpperRetainedBoundaryOrientedUpper
      ε A eta rho N p i₀ upperEndpoint j
  have hlower :
      ε / 2 ≤ lower :=
    annularContractedUpperRetainedBoundaryOrientedLower_ge_half
      hε hεA hgrid hsigned p i₀ upperEndpoint hv j
  have hupper :
      upper ≤ 2 * A :=
    annularContractedUpperRetainedBoundaryOrientedUpper_le_two
      hε hεA hgrid hsigned p i₀ upperEndpoint hv j
  have hlowerPos : 0 < lower := lt_of_lt_of_le (by linarith) hlower
  have hvpos :
      0 <
        annularContractedUpperRetainedPrefixValueRadius eta rho N p := by
    unfold annularContractedUpperRetainedPrefixValueRadius
      gaussPrefixGoodValueFreezingRadius
    exact mul_pos (mul_pos (by norm_num) hscale) (Real.exp_pos _)
  have hupperPos : 0 < upper := by
    exact hlowerPos.trans
      (annularContractedUpperRetainedBoundaryOrientedLower_lt_upper
        hεA hgrid p i₀ upperEndpoint hvpos j)
  have hApos : 0 < A := hε.trans hεA
  have hsq : upper ^ 2 ≤ (2 * A) ^ 2 := by
    nlinarith
  have hmul :
      ε / 2 * Real.log (N : ℝ) ≤
        lower * Real.log (N : ℝ) :=
    mul_le_mul_of_nonneg_right hlower hscale.le
  dsimp only [lower, upper] at hlower hupper hlowerPos hupperPos hsq hmul ⊢
  nlinarith

/-! ## One-tag full-dimensional mass bound -/

def annularUpperBoundaryExactMassBound
    (r : ℕ) (scale A₀ : ℝ) : ℝ :=
  (1 + gaussDigitExponentialRate 1) ^ (r - 1) *
      (((12 * A₀ ^ 2 / scale ^ 2) / Real.log 2) *
        (((2 * A₀ + 10 * A₀ ^ 2) / scale) /
          Real.log 2) ^ (r - 1)) +
    (r : ℝ) *
      (2 * ((1 + gaussDigitExponentialRate 1) ^ (r - 1) *
        ((((26 * A₀ ^ 2 / scale ^ 2) / Real.log 2)) *
          (((2 * A₀ + 10 * A₀ ^ 2) / scale) /
            Real.log 2) ^ (r - 1))))

def annularUpperBoundaryMaskedReplacementMassBound
    (r : ℕ) (scale A₀ : ℝ) : ℝ :=
  (r : ℝ) *
    (2 * ((1 + gaussDigitExponentialRate 1) ^ (r - 1) *
      ((((26 * A₀ ^ 2 / scale ^ 2) / Real.log 2)) *
        (((2 * A₀ + 10 * A₀ ^ 2) / scale) /
          Real.log 2) ^ (r - 1))))

def annularUpperBoundaryMaskedMassBound
    (r : ℕ) (scale A₀ : ℝ) : ℝ :=
  annularUpperBoundaryExactMassBound r scale A₀ +
    annularUpperBoundaryMaskedReplacementMassBound r scale A₀

theorem gaussMeasure_real_annularContractedUpperRetainedBoundaryMaskedEvent_le
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
        (annularContractedUpperRetainedBoundaryMaskedEvent
          ε A eta rho N p i₀ upperEndpoint) ≤
      annularUpperBoundaryMaskedMassBound
        (MixedOccurrenceCount k) (Real.log (N : ℝ)) (2 * A) := by
  let r := MixedOccurrenceCount k
  let lower :=
    annularContractedUpperRetainedBoundaryOrientedLower
      ε A eta rho N p i₀ upperEndpoint
  let upper :=
    annularContractedUpperRetainedBoundaryOrientedUpper
      ε A eta rho N p i₀ upperEndpoint
  let times := annularContractedUpperRetainedTimes p
  let j₀ :=
    annularContractedUpperRetainedPrefixChronologicalIndex p i₀
  let v :=
    annularContractedUpperRetainedPrefixValueRadius eta rho N p
  let center :=
    annularContractedUpperRetainedBoundaryOrientedCenter
      ε A p i₀ upperEndpoint
  have hscale : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast hN)
  have hvpos : 0 < v := by
    simpa only [v] using!
      annularContractedUpperRetainedPrefixValueRadius_pos p hN
  have hcenterMem : center ∈ Icc ε A := by
    simpa only [center] using!
      annularContractedUpperRetainedBoundaryOrientedCenter_mem_Icc
        hεA hgrid hsigned p i₀ upperEndpoint
  have hcenterPos : 0 < center := hε.trans_le hcenterMem.1
  have hcenterA : center ≤ 2 * A :=
    hcenterMem.2.trans (by linarith)
  have hA₀ : 0 ≤ 2 * A := by linarith
  have hvCenter : 2 * v ≤ center := by
    dsimp only [v] at hvpos ⊢
    linarith [hcenterMem.1]
  have hlower : ∀ j, 0 < lower j := by
    intro j
    exact lt_of_lt_of_le (by linarith)
      (annularContractedUpperRetainedBoundaryOrientedLower_ge_half
        hε hεA hgrid hsigned p i₀ upperEndpoint hv j)
  have hupper : ∀ j, lower j < upper j := by
    intro j
    exact
      annularContractedUpperRetainedBoundaryOrientedLower_lt_upper
        hεA hgrid p i₀ upperEndpoint
          (by simpa only [v] using! hvpos) j
  have hupperA : ∀ j, upper j ≤ 2 * A := by
    intro j
    exact
      annularContractedUpperRetainedBoundaryOrientedUpper_le_two
        hε hεA hgrid hsigned p i₀ upperEndpoint hv j
  have hjLower : lower j₀ = center - v := by
    simpa only [lower, center, v, j₀] using!
      annularContractedUpperRetainedBoundaryOrientedLower_of_distinguished
        (ε := ε) (A := A) p i₀ upperEndpoint
  have hjUpper : upper j₀ = center + v := by
    simpa only [upper, center, v, j₀] using!
      annularContractedUpperRetainedBoundaryOrientedUpper_of_distinguished
        (ε := ε) (A := A) p i₀ upperEndpoint
  have hlarge : ∀ j, 16 * (upper j) ^ 2 ≤
      lower j * Real.log (N : ℝ) := by
    intro j
    exact
      annularContractedUpperRetainedBoundary_large
        hε hεA hgrid hsigned p i₀ upperEndpoint hv hscale hlargeScale j
  have hgap : ∀ i j, i < j → times i + 1 ≤ times j := by
    simpa only [times] using!
      contractedAnnularCanonicalLaterUpperMidpointTupleFamily_chronological
        k hr p.1 (mode p.1) (hmode p.1)
          (annularContractedUpperRetainedTimes p) p.2.2
  have hexact :=
    gaussMeasure_real_heterogeneousApproximationTupleEvent_le_boundary
      hr lower upper times j₀ 1 (by norm_num)
      hscale hscaleOne hA₀ hcenterPos hcenterA hvpos hvCenter
      (by simpa only [v] using! hvScale)
      hlower hupper hupperA hjLower hjUpper hlarge hgap
  have hreplace :=
    gaussMeasure_real_symmDiff_heterogeneousMaskedTuple_le_explicit
      hr lower upper times
      (annularContractedUpperRetainedDelayedFutureMask p)
      1 (by norm_num) hscale hscaleOne hA₀
      hlower hupper hupperA hlarge hgap
  have htriangle :=
    measureReal_le_add_measureReal_symmDiff gaussMeasure
      (annularContractedUpperRetainedBoundaryMaskedEvent
        ε A eta rho N p i₀ upperEndpoint)
      (gaussHeterogeneousApproximationTupleEvent
        (Real.log (N : ℝ)) lower upper times)
  calc
    gaussMeasure.real
        (annularContractedUpperRetainedBoundaryMaskedEvent
          ε A eta rho N p i₀ upperEndpoint) ≤
      gaussMeasure.real
          (gaussHeterogeneousApproximationTupleEvent
            (Real.log (N : ℝ)) lower upper times) +
        gaussMeasure.real
          (annularContractedUpperRetainedBoundaryMaskedEvent
              ε A eta rho N p i₀ upperEndpoint ∆
            gaussHeterogeneousApproximationTupleEvent
              (Real.log (N : ℝ)) lower upper times) := htriangle
    _ =
      gaussMeasure.real
          (gaussHeterogeneousApproximationTupleEvent
            (Real.log (N : ℝ)) lower upper times) +
        gaussMeasure.real
          (gaussHeterogeneousApproximationTupleEvent
              (Real.log (N : ℝ)) lower upper times ∆
            annularContractedUpperRetainedBoundaryMaskedEvent
              ε A eta rho N p i₀ upperEndpoint) := by
        rw [symmDiff_comm
          (annularContractedUpperRetainedBoundaryMaskedEvent
            ε A eta rho N p i₀ upperEndpoint)]
    _ ≤
      annularUpperBoundaryExactMassBound r (Real.log (N : ℝ)) (2 * A) +
        annularUpperBoundaryMaskedReplacementMassBound
          r (Real.log (N : ℝ)) (2 * A) := by
      apply add_le_add
      · simpa only [r, annularUpperBoundaryExactMassBound] using! hexact
      · simpa only [r, lower, upper, times,
          annularContractedUpperRetainedBoundaryMaskedEvent,
          annularUpperBoundaryMaskedReplacementMassBound] using! hreplace
    _ =
      annularUpperBoundaryMaskedMassBound
        (MixedOccurrenceCount k) (Real.log (N : ℝ)) (2 * A) := by
      rfl

theorem gaussMeasure_real_annularContractedUpperRetainedCompleteBoundaryEvent_le
    (hε : 0 < ε) (hεA : ε < A) (hgrid : 0 < grid)
    (htime : ∀ i, 0 < k i → i.time.1 < grid)
    (hsigned : ∀ i, 0 < k i → i.signed.1 < grid)
    (p : AnnularContractedUpperRetainedTaggedTuple
      eta rho N k hr mode hmode)
    (i₀ : Fin (Fintype.card
      (GaussPrefixMixedPrefixOccurrence N k
        (annularContractedUpperRetainedRealization p).1
        (annularContractedUpperRetainedDelayedDepth p))))
    (hN : 1 < N)
    (hW : 0 < annularMidpointBandWidth rho N)
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
        (annularContractedUpperRetainedCompleteBoundaryEvent
          ε A eta rho N p i₀) ≤
      2 * annularUpperBoundaryMaskedMassBound
        (MixedOccurrenceCount k) (Real.log (N : ℝ)) (2 * A) := by
  have hmono :
      gaussMeasure.real
          (annularContractedUpperRetainedCompleteBoundaryEvent
            ε A eta rho N p i₀) ≤
        gaussMeasure.real
          (annularContractedUpperRetainedBoundaryMaskedEvent
              ε A eta rho N p i₀ false ∪
            annularContractedUpperRetainedBoundaryMaskedEvent
              ε A eta rho N p i₀ true) := by
    exact measureReal_mono_ae_of_finite_local gaussMeasure
      (ae_annularContractedUpperRetainedCompleteBoundaryEvent_subset_union
        (ε := ε) (A := A) hgrid htime p i₀ hN hW)
  calc
    gaussMeasure.real
        (annularContractedUpperRetainedCompleteBoundaryEvent
          ε A eta rho N p i₀) ≤
      gaussMeasure.real
          (annularContractedUpperRetainedBoundaryMaskedEvent
              ε A eta rho N p i₀ false ∪
            annularContractedUpperRetainedBoundaryMaskedEvent
              ε A eta rho N p i₀ true) := hmono
    _ ≤
      gaussMeasure.real
          (annularContractedUpperRetainedBoundaryMaskedEvent
            ε A eta rho N p i₀ false) +
        gaussMeasure.real
          (annularContractedUpperRetainedBoundaryMaskedEvent
            ε A eta rho N p i₀ true) :=
      measureReal_union_le _ _
    _ ≤
      annularUpperBoundaryMaskedMassBound
          (MixedOccurrenceCount k) (Real.log (N : ℝ)) (2 * A) +
        annularUpperBoundaryMaskedMassBound
          (MixedOccurrenceCount k) (Real.log (N : ℝ)) (2 * A) := by
      apply add_le_add
      · exact
          gaussMeasure_real_annularContractedUpperRetainedBoundaryMaskedEvent_le
            hε hεA hgrid hsigned p i₀ false hN hscaleOne hv
              hvScale hlargeScale
      · exact
          gaussMeasure_real_annularContractedUpperRetainedBoundaryMaskedEvent_le
            hε hεA hgrid hsigned p i₀ true hN hscaleOne hv
              hvScale hlargeScale
    _ = _ := by ring

theorem card_gaussPrefixMixedPrefixOccurrence_le
    (p : AnnularContractedUpperRetainedTaggedTuple
      eta rho N k hr mode hmode) :
    Fintype.card
        (GaussPrefixMixedPrefixOccurrence N k
          (annularContractedUpperRetainedRealization p).1
          (annularContractedUpperRetainedDelayedDepth p)) ≤
      MixedOccurrenceCount k := by
  calc
    Fintype.card
        (GaussPrefixMixedPrefixOccurrence N k
          (annularContractedUpperRetainedRealization p).1
          (annularContractedUpperRetainedDelayedDepth p)) ≤
      Fintype.card (GaussPrefixMixedOccurrence k) :=
        Fintype.card_le_of_injective
          (fun z :
            GaussPrefixMixedPrefixOccurrence N k
              (annularContractedUpperRetainedRealization p).1
              (annularContractedUpperRetainedDelayedDepth p) ↦ z.1)
          Subtype.val_injective
    _ = MixedOccurrenceCount k := rfl

/-- Sharp ambient cardinality bound: contraction only removes points from
the canonical chronological `r`-box, so there is no spurious extra power
of the depth horizon. -/
theorem card_annularContractedUpperRetainedTaggedTuple_le_ambient
    (eta rho : ℝ) (N : ℕ) (hgrid : 0 < grid)
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k)
    (htime : ∀ i, 0 < k i → i.time.1 < grid)
    (mode :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Fin (MixedOccurrenceCount k) → ℤ)
    (hmode : ∀ e, mode e ≠ 0)
    (hN : 1 < N) :
    Fintype.card
        (AnnularContractedUpperRetainedTaggedTuple
          eta rho N k hr mode hmode) ≤
      Fintype.card
          (Fin (MixedOccurrenceCount k) ≃
            GaussPrefixMixedOccurrence k) *
        annularDepthAmbientSize N ^ MixedOccurrenceCount k := by
  calc
    Fintype.card
        (AnnularContractedUpperRetainedTaggedTuple
          eta rho N k hr mode hmode) =
      ∑ e : Fin (MixedOccurrenceCount k) ≃
          GaussPrefixMixedOccurrence k,
        (contractedAnnularCanonicalLaterUpperMidpointTupleFamily
          eta rho N k hr e (mode e) (hmode e)).card := by
        simp [AnnularContractedUpperRetainedTaggedTuple]
    _ ≤
      ∑ e : Fin (MixedOccurrenceCount k) ≃
          GaussPrefixMixedOccurrence k,
        (canonicalAnnularGridTupleFamily N k e).card := by
      apply Finset.sum_le_sum
      intro e _he
      exact Finset.card_le_card
        (contractedAnnularCanonicalLaterUpperMidpointTupleFamily_subset_canonical
          k hr e (mode e) (hmode e))
    _ = aggregateTupleFamilyCard
        (fun e ↦ canonicalAnnularGridTupleFamily N k e) := rfl
    _ ≤ _ :=
      aggregate_canonicalAnnularGridTupleFamily_card_le
        hgrid k htime hN

theorem annularUpperBoundaryMaskedMassBound_eq_scale
    (r : ℕ) (hr : 0 < r) (scale A₀ : ℝ) (hscale : scale ≠ 0) :
    annularUpperBoundaryMaskedMassBound r scale A₀ =
      annularUpperBoundaryMaskedMassBound r 1 A₀ *
        scale⁻¹ ^ (r + 1) := by
  have hlog : Real.log 2 ≠ 0 :=
    ne_of_gt (Real.log_pos one_lt_two)
  have hrPow : r + 1 = 2 + (r - 1) := by omega
  unfold annularUpperBoundaryMaskedMassBound
    annularUpperBoundaryExactMassBound
    annularUpperBoundaryMaskedReplacementMassBound
  rw [hrPow, pow_add]
  field_simp [hscale, hlog]
  rw [show
    A₀ * (2 + A₀ * 10) / (scale * Real.log 2) =
        (A₀ * (2 + A₀ * 10) / Real.log 2) * (1 / scale) by
      field_simp [hscale, hlog],
    mul_pow]
  ring

theorem tendsto_annularDepth_pow_mul_boundaryMaskedMassBound_zero
    (r : ℕ) (hr : 0 < r) (A₀ : ℝ) :
    Tendsto
      (fun N : ℕ ↦
        (annularDepthAmbientSize N : ℝ) ^ r *
          annularUpperBoundaryMaskedMassBound
            r (Real.log (N : ℝ)) A₀)
      atTop (nhds 0) := by
  let C := annularUpperBoundaryMaskedMassBound r 1 A₀
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
        (nhds
          (C * (1 / gaussRoofMean) ^ r * 0)))
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
  rw [annularUpperBoundaryMaskedMassBound_eq_scale
    r hr (Real.log (N : ℝ)) A₀ hlogNe]
  dsimp only [C]
  rw [div_pow]
  rw [show r + 1 = Nat.succ r by omega, pow_succ]
  field_simp [hlogNe]
  rw [one_div_pow]
  field_simp [hlogNe]

theorem annularUpperBoundaryMaskedMassBound_nonneg
    (r : ℕ) {scale A₀ : ℝ} (hscale : 0 < scale) (hA₀ : 0 ≤ A₀) :
    0 ≤ annularUpperBoundaryMaskedMassBound r scale A₀ := by
  have hrate : 0 ≤ gaussDigitExponentialRate 1 :=
    gaussDigitExponentialRate_nonnegative 1
  have hlog : 0 < Real.log 2 := Real.log_pos one_lt_two
  unfold annularUpperBoundaryMaskedMassBound
    annularUpperBoundaryExactMassBound
    annularUpperBoundaryMaskedReplacementMassBound
  positivity

def annularContractedUpperRetainedBoundaryMassSum
    (ε A eta rho : ℝ) (N : ℕ) {grid : ℕ}
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k)
    (mode :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Fin (MixedOccurrenceCount k) → ℤ)
    (hmode : ∀ e, mode e ≠ 0) : ℝ :=
  ∑ p : AnnularContractedUpperRetainedTaggedTuple
      eta rho N k hr mode hmode,
    ∑ i : Fin (Fintype.card
      (GaussPrefixMixedPrefixOccurrence N k
        (annularContractedUpperRetainedRealization p).1
        (annularContractedUpperRetainedDelayedDepth p))),
      gaussMeasure.real
        (annularContractedUpperRetainedCompleteBoundaryEvent
          ε A eta rho N p i)

theorem tendsto_annularContractedUpperRetainedBoundaryMassSum_zero
    {eta rho ε A : ℝ} (hrho : 0 < rho)
    (hε : 0 < ε) (hεA : ε < A)
    {grid : ℕ} (hgrid : 0 < grid)
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k)
    (htime : ∀ i, 0 < k i → i.time.1 < grid)
    (hsigned : ∀ i, 0 < k i → i.signed.1 < grid)
    (mode :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Fin (MixedOccurrenceCount k) → ℤ)
    (hmode : ∀ e, mode e ≠ 0) :
    Tendsto
      (fun N : ℕ ↦
        annularContractedUpperRetainedBoundaryMassSum
          ε A eta rho N k hr mode hmode)
      atTop (nhds 0) := by
  let r := MixedOccurrenceCount k
  let Ctag :=
    Fintype.card
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k)
  let C : ℝ := (Ctag : ℝ) * (r : ℝ) * 2
  let upper : ℕ → ℝ := fun N ↦
    C * (annularDepthAmbientSize N : ℝ) ^ r *
      annularUpperBoundaryMaskedMassBound
        r (Real.log (N : ℝ)) (2 * A)
  have hupperZero : Tendsto upper atTop (nhds 0) := by
    have h :=
      (tendsto_annularDepth_pow_mul_boundaryMaskedMassBound_zero
        r hr (2 * A)).const_mul C
    simpa only [upper, mul_assoc, mul_zero] using! h
  have hN : ∀ᶠ N : ℕ in atTop, 1 < N := eventually_ge_atTop 2
  have hW :
      ∀ᶠ N : ℕ in atTop, 0 < annularMidpointBandWidth rho N :=
    (tendsto_annularMidpointBandWidth_atTop hrho).eventually_gt_atTop 0
  have hscaleOne :
      ∀ᶠ N : ℕ in atTop, 1 ≤ Real.log (N : ℝ) :=
    tendsto_log_natCast_atTop.eventually (eventually_ge_atTop 1)
  have henvSmall :
      ∀ᶠ N : ℕ in atTop,
        annularUpperFreezingValueRadiusEnvelope rho N < ε / 4 :=
    (tendsto_annularUpperFreezingValueRadiusEnvelope_zero hrho
      ).eventually_lt_const (by linarith)
  have hscaleEnvelopeZero :=
    tendsto_const_mul_annularDepth_pow_mul_valueRadiusEnvelope_zero
      gaussRoofMean 1 gaussRoofMean_pos.le hrho
  have hscaleEnvelopeSmall :
      ∀ᶠ N : ℕ in atTop,
        gaussRoofMean * (annularDepthAmbientSize N : ℝ) ^ 1 *
            annularUpperFreezingValueRadiusEnvelope rho N <
          (2 * A) ^ 2 :=
    hscaleEnvelopeZero.eventually_lt_const (by
      have hA : 0 < A := hε.trans hεA
      positivity)
  have hlargeScale :
      ∀ᶠ N : ℕ in atTop,
        128 * A ^ 2 ≤ ε * Real.log (N : ℝ) := by
    have hlogLarge :=
      tendsto_log_natCast_atTop.eventually_gt_atTop
        (128 * A ^ 2 / ε)
    filter_upwards [hlogLarge] with N hlogLargeN
    have hmul :=
      (div_lt_iff₀ hε).mp hlogLargeN
    nlinarith
  apply squeeze_zero'
  · exact Eventually.of_forall fun N ↦ by
      unfold annularContractedUpperRetainedBoundaryMassSum
      exact Finset.sum_nonneg fun _p _hp ↦
        Finset.sum_nonneg fun _i _hi ↦ measureReal_nonneg
  · filter_upwards [hN, hW, hscaleOne, henvSmall,
      hscaleEnvelopeSmall, hlargeScale] with
      N hN hW hscaleOne henvSmall hscaleEnvelopeSmall hlargeScale
    have hlog : 0 < Real.log (N : ℝ) :=
      Real.log_pos (by exact_mod_cast hN)
    have hA : 0 < A := hε.trans hεA
    have hboundNonneg :
        0 ≤ annularUpperBoundaryMaskedMassBound
          r (Real.log (N : ℝ)) (2 * A) :=
      annularUpperBoundaryMaskedMassBound_nonneg r hlog (by linarith)
    have hlogUpper :
        Real.log (N : ℝ) ≤
          gaussRoofMean * (annularDepthAmbientSize N : ℝ) := by
      have hraw :=
        log_natCast_le_ambient_sub_one_mul_gaussRoofMean
          (show 1 ≤ N by omega)
      nlinarith [gaussRoofMean_pos]
    have htagCard :=
      card_annularContractedUpperRetainedTaggedTuple_le_ambient
        eta rho N hgrid k hr htime mode hmode hN
    have htagCardReal :
        (Fintype.card
            (AnnularContractedUpperRetainedTaggedTuple
              eta rho N k hr mode hmode) : ℝ) ≤
          (Ctag : ℝ) *
            (annularDepthAmbientSize N : ℝ) ^ r := by
      exact_mod_cast htagCard
    have hvBound :
        ∀ p : AnnularContractedUpperRetainedTaggedTuple
            eta rho N k hr mode hmode,
          annularContractedUpperRetainedPrefixValueRadius
              eta rho N p ≤ ε / 4 := by
      intro p
      exact
        (gaussPrefixGoodValueFreezingRadius_le_annularUpperEnvelope
          hgrid k hr htime mode hmode hN hW p).trans henvSmall.le
    have hvScale :
        ∀ p : AnnularContractedUpperRetainedTaggedTuple
            eta rho N k hr mode hmode,
          annularContractedUpperRetainedPrefixValueRadius eta rho N p *
              Real.log (N : ℝ) ≤
            (2 * A) ^ 2 := by
      intro p
      have hvEnv :=
        gaussPrefixGoodValueFreezingRadius_le_annularUpperEnvelope
          hgrid k hr htime mode hmode hN hW p
      have henvNonneg :
          0 ≤ annularUpperFreezingValueRadiusEnvelope rho N := by
        unfold annularUpperFreezingValueRadiusEnvelope
        have hlogNonneg : 0 ≤ Real.log (N : ℝ) := hlog.le
        positivity
      calc
        annularContractedUpperRetainedPrefixValueRadius eta rho N p *
              Real.log (N : ℝ) ≤
            annularUpperFreezingValueRadiusEnvelope rho N *
              Real.log (N : ℝ) :=
          mul_le_mul_of_nonneg_right hvEnv hlog.le
        _ ≤
            gaussRoofMean * (annularDepthAmbientSize N : ℝ) *
              annularUpperFreezingValueRadiusEnvelope rho N := by
          simpa only [mul_comm, mul_left_comm, mul_assoc] using!
            mul_le_mul_of_nonneg_left hlogUpper henvNonneg
        _ ≤ (2 * A) ^ 2 := by
          simpa only [pow_one, mul_assoc] using! hscaleEnvelopeSmall.le
    unfold annularContractedUpperRetainedBoundaryMassSum
    calc
      (∑ p : AnnularContractedUpperRetainedTaggedTuple
          eta rho N k hr mode hmode,
        ∑ i : Fin (Fintype.card
          (GaussPrefixMixedPrefixOccurrence N k
            (annularContractedUpperRetainedRealization p).1
            (annularContractedUpperRetainedDelayedDepth p))),
          gaussMeasure.real
            (annularContractedUpperRetainedCompleteBoundaryEvent
              ε A eta rho N p i)) ≤
        ∑ _p : AnnularContractedUpperRetainedTaggedTuple
            eta rho N k hr mode hmode,
          (r : ℝ) *
            (2 * annularUpperBoundaryMaskedMassBound
              r (Real.log (N : ℝ)) (2 * A)) := by
        apply Finset.sum_le_sum
        intro p _hp
        calc
          (∑ i : Fin (Fintype.card
              (GaussPrefixMixedPrefixOccurrence N k
                (annularContractedUpperRetainedRealization p).1
                (annularContractedUpperRetainedDelayedDepth p))),
            gaussMeasure.real
              (annularContractedUpperRetainedCompleteBoundaryEvent
                ε A eta rho N p i)) ≤
            ∑ _i : Fin (Fintype.card
                (GaussPrefixMixedPrefixOccurrence N k
                  (annularContractedUpperRetainedRealization p).1
                  (annularContractedUpperRetainedDelayedDepth p))),
              2 * annularUpperBoundaryMaskedMassBound
                r (Real.log (N : ℝ)) (2 * A) := by
              apply Finset.sum_le_sum
              intro i _hi
              exact
                gaussMeasure_real_annularContractedUpperRetainedCompleteBoundaryEvent_le
                  hε hεA hgrid htime hsigned p i hN hW hscaleOne
                    (hvBound p) (hvScale p) hlargeScale
          _ =
            (Fintype.card
                (GaussPrefixMixedPrefixOccurrence N k
                  (annularContractedUpperRetainedRealization p).1
                  (annularContractedUpperRetainedDelayedDepth p)) : ℝ) *
              (2 * annularUpperBoundaryMaskedMassBound
                r (Real.log (N : ℝ)) (2 * A)) := by simp
          _ ≤
            (r : ℝ) *
              (2 * annularUpperBoundaryMaskedMassBound
                r (Real.log (N : ℝ)) (2 * A)) := by
            apply mul_le_mul_of_nonneg_right _ (mul_nonneg (by norm_num)
              hboundNonneg)
            exact_mod_cast card_gaussPrefixMixedPrefixOccurrence_le p
      _ =
        (Fintype.card
            (AnnularContractedUpperRetainedTaggedTuple
              eta rho N k hr mode hmode) : ℝ) *
          ((r : ℝ) *
            (2 * annularUpperBoundaryMaskedMassBound
              r (Real.log (N : ℝ)) (2 * A))) := by simp
      _ ≤
        ((Ctag : ℝ) *
            (annularDepthAmbientSize N : ℝ) ^ r) *
          ((r : ℝ) *
            (2 * annularUpperBoundaryMaskedMassBound
              r (Real.log (N : ℝ)) (2 * A))) := by
        exact mul_le_mul_of_nonneg_right htagCardReal
          (mul_nonneg (Nat.cast_nonneg r)
            (mul_nonneg (by norm_num) hboundNonneg))
      _ = upper N := by
        dsimp only [upper, C]
        ring
  · exact hupperZero

/-! ## Integrated and summed freezing error -/

theorem annularContractedUpperRetainedPhaseFreezingMajorant_nonneg
    (p : AnnularContractedUpperRetainedTaggedTuple
      eta rho N k hr mode hmode) :
    0 ≤ annularContractedUpperRetainedPhaseFreezingMajorant
      eta rho N k hr mode hmode p := by
  unfold annularContractedUpperRetainedPhaseFreezingMajorant
  positivity

theorem norm_weightedLiveDigitJoint_sub_weightedAffineDigitJoint_le
    (hε : 0 < ε) (hεA : ε < A)
    (hgrid : 0 < grid)
    (htime : ∀ i, 0 < k i → i.time.1 < grid)
    (hsigned : ∀ i, 0 < k i → i.signed.1 < grid)
    (p : AnnularContractedUpperRetainedTaggedTuple
      eta rho N k hr mode hmode)
    (hN : 2 ≤ N)
    (hW : 0 < annularMidpointBandWidth rho N)
    (hsmall : A / Real.log (N : ℝ) < (1 : ℝ) / 2)
    (hmargin :
      upperGoodTransferDenominatorTolerance eta rho *
          (annularDepthAmbientSize N : ℝ) ≤
        eta * Real.log (N : ℝ)) :
    ‖annularContractedUpperRetainedLebesgueWeightedLiveDigitJoint
          ε A eta rho N k hr mode hmode p -
        annularContractedUpperRetainedLebesgueWeightedAffineDigitJoint
          ε A eta rho N k hr mode hmode p‖ ≤
      (2 * Real.log 2) *
        (annularContractedUpperRetainedPhaseFreezingMajorant
              eta rho N k hr mode hmode p *
            gaussMeasure.real
              (annularContractedUpperRetainedCompletePhaseEvent
                ε A eta rho N p) +
          ∑ i,
            gaussMeasure.real
              (annularContractedUpperRetainedCompleteBoundaryEvent
                ε A eta rho N p i)) := by
  let B : AnnularGridIndex grid → Set (ℝ × ℝ × ℝ) :=
    fun i ↦ compactValueMarkedRegion
      (activeAnnularOccurrenceSignedLower k ε A i)
      (activeAnnularOccurrenceSignedUpper k ε A i)
  let G :=
    gaussDenominatorPrefixGoodEvent
      (annularContractedUpperRetainedDelayedDepth p)
      (annularDepthAmbientSize N)
      (upperGoodTransferDenominatorTolerance eta rho)
  let pref : ℝ → ℂ :=
    gaussPrefixMarkedMixedPrefixCharacter N B k
      (unflattenedAnnularFourierMode p.1 (mode p.1))
      (annularContractedUpperRetainedRealization p).1
      (annularContractedUpperRetainedDelayedDepth p)
  let affine : ℝ → ℂ :=
    gaussPrefixAffineFrozenCompactCharacter
      N
      (activeAnnularOccurrenceSignedLower k ε A)
      (activeAnnularOccurrenceSignedUpper k ε A)
      k
      (unflattenedAnnularFourierMode p.1 (mode p.1))
      (annularContractedUpperRetainedRealization p).1
      (annularContractedUpperRetainedDelayedDepth p)
      (annularContractedUpperRetainedGoodWords eta rho N p)
  let future : ℝ → ℂ :=
    annularContractedUpperRetainedFutureDigitBlock ε A p
  let f : ℝ → ℂ := fun x ↦
    (gaussLebesguePrefixWeight x : ℂ) *
      G.indicator (fun y ↦ pref y * future y) x
  let g : ℝ → ℂ := fun x ↦
    (gaussLebesguePrefixWeight x : ℂ) * affine x * future x
  have hprefixMeas : Measurable pref := by
    dsimp only [pref]
    unfold gaussPrefixMarkedMixedPrefixCharacter
    apply Finset.measurable_fun_prod
    intro z _hz
    exact measurable_gaussPrefixMarkedDepthCharacter N
      ((annularContractedUpperRetainedRealization p).1 z.1 z.2)
      (measurableSet_compactValueMarkedRegion
        (activeAnnularOccurrenceSignedLower k ε A z.1)
        (activeAnnularOccurrenceSignedUpper k ε A z.1))
      (unflattenedAnnularFourierMode p.1 (mode p.1) z.1 z.2)
  have haffineMeas : Measurable affine := by
    dsimp only [affine]
    exact
      (measurable_gaussPrefixAffineFrozenCompactCharacter_prefix
        N
        (activeAnnularOccurrenceSignedLower k ε A)
        (activeAnnularOccurrenceSignedUpper k ε A)
        k
        (unflattenedAnnularFourierMode p.1 (mode p.1))
        (annularContractedUpperRetainedRealization p).1
        (annularContractedUpperRetainedDelayedDepth p)
        (annularContractedUpperRetainedGoodWords eta rho N p)).mono
          (gaussPrefixMeasurableSpace_le
            (annularContractedUpperRetainedDelayedDepth p)) le_rfl
  have hfutureMeas : Measurable future := by
    dsimp only [future]
    have heq :
        annularContractedUpperRetainedFutureDigitBlock ε A p =
          (annularUpperRetainedFutureDigitTupleEvent ε A
            (annularContractedUpperRetainedToUpper p)).indicator
              (fun _ ↦ (1 : ℂ)) := by
      funext x
      exact annularUpperRetainedFutureDigitBlock_eq_eventIndicator
        (ε := ε) (A := A)
        (annularContractedUpperRetainedToUpper p) x
    rw [heq]
    exact Measurable.ite
      (measurableSet_annularUpperRetainedFutureDigitTupleEvent
        (ε := ε) (A := A)
        (annularContractedUpperRetainedToUpper p))
      measurable_const measurable_const
  have hfMeas : Measurable f := by
    exact measurable_gaussLebesguePrefixWeight.complex_ofReal.mul
      ((hprefixMeas.mul hfutureMeas).indicator
        (measurableSet_gaussDenominatorPrefixGoodEvent
          (annularContractedUpperRetainedDelayedDepth p)
          (annularDepthAmbientSize N)
          (upperGoodTransferDenominatorTolerance eta rho)))
  have hgMeas : Measurable g :=
    (measurable_gaussLebesguePrefixWeight.complex_ofReal.mul
      haffineMeas).mul hfutureMeas
  have hweight :
      ∀ᵐ x ∂gaussMeasure,
        ‖(gaussLebesguePrefixWeight x : ℂ)‖ ≤
          2 * Real.log 2 := by
    filter_upwards [gaussMeasure_unit_ae] with x hx
    have hxIcc : x ∈ Icc (0 : ℝ) 1 := ⟨hx.1.le, hx.2⟩
    have hb := gaussLebesguePrefixWeight_bounds hxIcc
    have hnonneg :
        0 ≤ gaussLebesguePrefixWeight x :=
      (Real.log_pos one_lt_two).le.trans hb.1
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnonneg]
    exact hb.2
  have hfutureNorm : ∀ x, ‖future x‖ ≤ 1 := by
    intro x
    dsimp only [future]
    unfold annularContractedUpperRetainedFutureDigitBlock
    rw [annularUpperRetainedFutureDigitBlock_eq_eventIndicator]
    by_cases hx :
        x ∈ annularUpperRetainedFutureDigitTupleEvent ε A
          (annularContractedUpperRetainedToUpper p) <;>
      simp [Set.indicator, hx]
  have hfInt : Integrable f gaussMeasure := by
    apply Integrable.of_bound hfMeas.aestronglyMeasurable (2 * Real.log 2)
    filter_upwards [hweight] with x hweightx
    dsimp only [f]
    by_cases hxG : x ∈ G
    · rw [Set.indicator_of_mem hxG, norm_mul, norm_mul]
      have hpref :
          ‖pref x‖ ≤ 1 := by
        simpa only [pref, B] using!
          norm_gaussPrefixMarkedMixedPrefixCharacter_le_one
            N B k
            (unflattenedAnnularFourierMode p.1 (mode p.1))
            (annularContractedUpperRetainedRealization p).1
            (annularContractedUpperRetainedDelayedDepth p) x
      calc
        ‖(gaussLebesguePrefixWeight x : ℂ)‖ *
            (‖pref x‖ * ‖future x‖) ≤
          (2 * Real.log 2) * (‖pref x‖ * ‖future x‖) :=
            mul_le_mul_of_nonneg_right hweightx
              (mul_nonneg (norm_nonneg _) (norm_nonneg _))
        _ ≤ (2 * Real.log 2) * (1 * 1) := by
          gcongr
          exact hfutureNorm x
        _ = 2 * Real.log 2 := by ring
    · rw [Set.indicator_of_notMem hxG, norm_mul, norm_zero, mul_zero]
      exact (mul_nonneg (by norm_num)
        (Real.log_pos one_lt_two).le)
  have hgInt : Integrable g gaussMeasure := by
    apply Integrable.of_bound hgMeas.aestronglyMeasurable (2 * Real.log 2)
    filter_upwards [hweight] with x hweightx
    dsimp only [g]
    rw [norm_mul, norm_mul]
    have haffine :
        ‖affine x‖ ≤ 1 := by
      simpa only [affine] using!
        norm_gaussPrefixAffineFrozenCompactCharacter_le_one
          N
          (activeAnnularOccurrenceSignedLower k ε A)
          (activeAnnularOccurrenceSignedUpper k ε A)
          k
          (unflattenedAnnularFourierMode p.1 (mode p.1))
          (annularContractedUpperRetainedRealization p).1
          (annularContractedUpperRetainedDelayedDepth p)
          (annularContractedUpperRetainedGoodWords eta rho N p) x
    calc
      ‖(gaussLebesguePrefixWeight x : ℂ)‖ *
          ‖affine x‖ * ‖future x‖ ≤
        (2 * Real.log 2) * ‖affine x‖ * ‖future x‖ := by
          gcongr
      _ ≤ (2 * Real.log 2) * 1 * 1 := by
        gcongr
        exact hfutureNorm x
      _ = 2 * Real.log 2 := by ring
  have henvelopeInt :
      Integrable
        (fun x ↦
          (2 * Real.log 2) *
            annularContractedUpperRetainedJointFreezingEnvelope
              ε A eta rho N k hr mode hmode p x)
        gaussMeasure := by
    have hphase :=
      measurableSet_annularContractedUpperRetainedCompletePhaseEvent
        ε A eta rho N p
    have hboundary :
        ∀ i, MeasurableSet
          (annularContractedUpperRetainedCompleteBoundaryEvent
            ε A eta rho N p i) :=
      measurableSet_annularContractedUpperRetainedCompleteBoundaryEvent
        ε A eta rho N p
    rw [show
      (fun x ↦
        (2 * Real.log 2) *
          annularContractedUpperRetainedJointFreezingEnvelope
            ε A eta rho N k hr mode hmode p x) =
        (fun x ↦
          (2 * Real.log 2) *
            (annularContractedUpperRetainedPhaseFreezingMajorant
                eta rho N k hr mode hmode p *
              (annularContractedUpperRetainedCompletePhaseEvent
                ε A eta rho N p).indicator (fun _ ↦ (1 : ℝ)) x +
            ∑ i,
              (annularContractedUpperRetainedCompleteBoundaryEvent
                ε A eta rho N p i).indicator
                  (fun _ ↦ (1 : ℝ)) x)) by
      funext x
      rw [
        annularContractedUpperRetainedJointFreezingEnvelope_eq_events]]
    exact
      ((((integrable_const (1 : ℝ)).indicator hphase).const_mul
          (annularContractedUpperRetainedPhaseFreezingMajorant
            eta rho N k hr mode hmode p)).add
        (integrable_finset_sum _ fun i _hi ↦
          (integrable_const (1 : ℝ)).indicator (hboundary i))).const_mul
        (2 * Real.log 2)
  unfold annularContractedUpperRetainedLebesgueWeightedLiveDigitJoint
    annularContractedUpperRetainedLebesgueWeightedAffineDigitJoint
  change ‖(∫ x, f x ∂gaussMeasure) - ∫ x, g x ∂gaussMeasure‖ ≤ _
  rw [← integral_sub hfInt hgInt]
  calc
    ‖∫ x, f x - g x ∂gaussMeasure‖ ≤
        ∫ x,
          (2 * Real.log 2) *
            annularContractedUpperRetainedJointFreezingEnvelope
              ε A eta rho N k hr mode hmode p x ∂gaussMeasure := by
      apply norm_integral_le_of_norm_le henvelopeInt
      filter_upwards [ae_nonterminating_gaussMeasure] with x hx
      have hpoint :=
        norm_weightedLive_sub_weightedAffine_le_jointFreezingEnvelope
          hε hεA hgrid htime hsigned p hN hW hsmall hmargin
            hx.1 hx.2
      by_cases hxG : x ∈ G
      · simpa only [f, g, pref, affine, future, G, B,
          Set.indicator_of_mem hxG, gaussOrbit, mul_assoc] using! hpoint
      · simpa only [f, g, pref, affine, future, G, B,
          Set.indicator_of_notMem hxG, gaussOrbit, mul_assoc,
          mul_zero, zero_mul] using! hpoint
    _ =
        (2 * Real.log 2) *
          (∫ x,
            annularContractedUpperRetainedJointFreezingEnvelope
              ε A eta rho N k hr mode hmode p x ∂gaussMeasure) := by
      rw [integral_const_mul]
    _ = _ := by
      rw [integral_annularContractedUpperRetainedJointFreezingEnvelope_eq]

/-- The absolute prefix-freezing error, summed over every retained
chronological tag.  Both the complete delayed-prefix event and the complete
future digit block remain inside each summand. -/
def annularContractedUpperRetainedWeightedFreezingNormSum
    (ε A eta rho : ℝ) (N : ℕ) {grid : ℕ}
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k)
    (mode :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Fin (MixedOccurrenceCount k) → ℤ)
    (hmode : ∀ e, mode e ≠ 0) : ℝ :=
  ∑ p : AnnularContractedUpperRetainedTaggedTuple
      eta rho N k hr mode hmode,
    ‖annularContractedUpperRetainedLebesgueWeightedLiveDigitJoint
          ε A eta rho N k hr mode hmode p -
        annularContractedUpperRetainedLebesgueWeightedAffineDigitJoint
          ε A eta rho N k hr mode hmode p‖

/-- The total weighted live-to-affine prefix-freezing error tends to zero.
The phase error is summed with its complete-event mass bounded by one; the
endpoint error is the full-dimensional boundary mass sum proved above. -/
theorem
    tendsto_annularContractedUpperRetainedWeightedFreezingNormSum_zero
    {eta rho ε A : ℝ} (heta : 0 < eta) (hrho : 0 < rho)
    (hε : 0 < ε) (hεA : ε < A)
    {grid : ℕ} (hgrid : 0 < grid)
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k)
    (htime : ∀ i, 0 < k i → i.time.1 < grid)
    (hsigned : ∀ i, 0 < k i → i.signed.1 < grid)
    (mode :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Fin (MixedOccurrenceCount k) → ℤ)
    (hmode : ∀ e, mode e ≠ 0) :
    Tendsto
      (fun N : ℕ ↦
        annularContractedUpperRetainedWeightedFreezingNormSum
          ε A eta rho N k hr mode hmode)
      atTop (nhds 0) := by
  let phaseSum : ℕ → ℝ := fun N ↦
    ∑ p : AnnularContractedUpperRetainedTaggedTuple
        eta rho N k hr mode hmode,
      annularContractedUpperRetainedPhaseFreezingMajorant
        eta rho N k hr mode hmode p
  let boundarySum : ℕ → ℝ := fun N ↦
    annularContractedUpperRetainedBoundaryMassSum
      ε A eta rho N k hr mode hmode
  let major : ℕ → ℝ := fun N ↦
    (2 * Real.log 2) * (phaseSum N + boundarySum N)
  have hphaseZero : Tendsto phaseSum atTop (nhds 0) := by
    exact
      tendsto_sum_annularContractedUpperRetainedPhaseFreezingMajorant_zero
        hrho hgrid k hr htime mode hmode
  have hboundaryZero : Tendsto boundarySum atTop (nhds 0) := by
    exact
      tendsto_annularContractedUpperRetainedBoundaryMassSum_zero
        hrho hε hεA hgrid k hr htime hsigned mode hmode
  have hmajorZero : Tendsto major atTop (nhds 0) := by
    have h :=
      (hphaseZero.add hboundaryZero).const_mul (2 * Real.log 2)
    simpa only [major, zero_add, mul_zero] using! h
  have hN : ∀ᶠ N : ℕ in atTop, 2 ≤ N := eventually_ge_atTop 2
  have hW :
      ∀ᶠ N : ℕ in atTop, 0 < annularMidpointBandWidth rho N :=
    (tendsto_annularMidpointBandWidth_atTop hrho).eventually_gt_atTop 0
  have hsmall :
      ∀ᶠ N : ℕ in atTop,
        A / Real.log (N : ℝ) < (1 : ℝ) / 2 := by
    have hlogTwoA :
        ∀ᶠ N : ℕ in atTop, 2 * A < Real.log (N : ℝ) :=
      tendsto_log_natCast_atTop.eventually_gt_atTop (2 * A)
    filter_upwards
      [hlogTwoA,
        tendsto_log_natCast_atTop.eventually_gt_atTop 0] with
        N htwoA hlog
    exact (div_lt_iff₀ hlog).2 (by linarith)
  have hmargin :
      ∀ᶠ N : ℕ in atTop,
        upperGoodTransferDenominatorTolerance eta rho *
            (annularDepthAmbientSize N : ℝ) ≤
          eta * Real.log (N : ℝ) :=
    eventually_upperGoodTransferDenominatorTolerance_mul_ambient_le_margin
      heta hrho
  apply squeeze_zero'
  · exact Eventually.of_forall fun _N ↦ by
      unfold annularContractedUpperRetainedWeightedFreezingNormSum
      exact Finset.sum_nonneg fun _p _hp ↦ norm_nonneg _
  · filter_upwards [hN, hW, hsmall, hmargin] with
      N hN hW hsmall hmargin
    have hconst : 0 ≤ 2 * Real.log 2 :=
      mul_nonneg (by norm_num) (Real.log_pos one_lt_two).le
    unfold annularContractedUpperRetainedWeightedFreezingNormSum
    calc
      (∑ p : AnnularContractedUpperRetainedTaggedTuple
          eta rho N k hr mode hmode,
        ‖annularContractedUpperRetainedLebesgueWeightedLiveDigitJoint
              ε A eta rho N k hr mode hmode p -
            annularContractedUpperRetainedLebesgueWeightedAffineDigitJoint
              ε A eta rho N k hr mode hmode p‖) ≤
          ∑ p : AnnularContractedUpperRetainedTaggedTuple
              eta rho N k hr mode hmode,
            (2 * Real.log 2) *
              (annularContractedUpperRetainedPhaseFreezingMajorant
                    eta rho N k hr mode hmode p *
                  gaussMeasure.real
                    (annularContractedUpperRetainedCompletePhaseEvent
                      ε A eta rho N p) +
                ∑ i,
                  gaussMeasure.real
                    (annularContractedUpperRetainedCompleteBoundaryEvent
                      ε A eta rho N p i)) := by
        apply Finset.sum_le_sum
        intro p _hp
        exact
          norm_weightedLiveDigitJoint_sub_weightedAffineDigitJoint_le
            hε hεA hgrid htime hsigned p hN hW hsmall hmargin
      _ ≤
          ∑ p : AnnularContractedUpperRetainedTaggedTuple
              eta rho N k hr mode hmode,
            (2 * Real.log 2) *
              (annularContractedUpperRetainedPhaseFreezingMajorant
                  eta rho N k hr mode hmode p +
                ∑ i,
                  gaussMeasure.real
                    (annularContractedUpperRetainedCompleteBoundaryEvent
                      ε A eta rho N p i)) := by
        apply Finset.sum_le_sum
        intro p _hp
        apply mul_le_mul_of_nonneg_left _ hconst
        gcongr
        exact mul_le_of_le_one_right
          (annularContractedUpperRetainedPhaseFreezingMajorant_nonneg p)
          measureReal_le_one
      _ = major N := by
        rw [← Finset.mul_sum, Finset.sum_add_distrib]
        rfl
  · exact hmajorZero

/-- Aggregate weighted live joint, before prefix freezing. -/
def annularContractedUpperRetainedLebesgueWeightedLiveDigitJointSum
    (ε A eta rho : ℝ) (N : ℕ) {grid : ℕ}
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k)
    (mode :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Fin (MixedOccurrenceCount k) → ℤ)
    (hmode : ∀ e, mode e ≠ 0) : ℂ :=
  ∑ p : AnnularContractedUpperRetainedTaggedTuple
      eta rho N k hr mode hmode,
    annularContractedUpperRetainedLebesgueWeightedLiveDigitJoint
      ε A eta rho N k hr mode hmode p

/-- The aggregate live-minus-affine norm is bounded by the corresponding
sum of one-tag norms. -/
theorem
    norm_annularContractedUpperRetainedLebesgueWeightedLiveDigitJointSum_sub_affine_le
    (ε A eta rho : ℝ) (N : ℕ) {grid : ℕ}
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k)
    (mode :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Fin (MixedOccurrenceCount k) → ℤ)
    (hmode : ∀ e, mode e ≠ 0) :
    ‖annularContractedUpperRetainedLebesgueWeightedLiveDigitJointSum
          ε A eta rho N k hr mode hmode -
        annularContractedUpperRetainedLebesgueWeightedAffineDigitJointSum
          ε A eta rho N k hr mode hmode‖ ≤
      annularContractedUpperRetainedWeightedFreezingNormSum
        ε A eta rho N k hr mode hmode := by
  unfold
    annularContractedUpperRetainedLebesgueWeightedLiveDigitJointSum
    annularContractedUpperRetainedLebesgueWeightedAffineDigitJointSum
    annularContractedUpperRetainedWeightedFreezingNormSum
  rw [← Finset.sum_sub_distrib]
  exact norm_sum_le _ _

/-- Prefix freezing changes the complete weighted aggregate by a quantity
tending to zero. -/
theorem
    tendsto_annularContractedUpperRetainedLebesgueWeightedLiveDigitJointSum_sub_affine_zero
    {eta rho ε A : ℝ} (heta : 0 < eta) (hrho : 0 < rho)
    (hε : 0 < ε) (hεA : ε < A)
    {grid : ℕ} (hgrid : 0 < grid)
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k)
    (htime : ∀ i, 0 < k i → i.time.1 < grid)
    (hsigned : ∀ i, 0 < k i → i.signed.1 < grid)
    (mode :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Fin (MixedOccurrenceCount k) → ℤ)
    (hmode : ∀ e, mode e ≠ 0) :
    Tendsto
      (fun N : ℕ ↦
        annularContractedUpperRetainedLebesgueWeightedLiveDigitJointSum
              ε A eta rho N k hr mode hmode -
          annularContractedUpperRetainedLebesgueWeightedAffineDigitJointSum
            ε A eta rho N k hr mode hmode)
      atTop (nhds 0) := by
  have hnorm :=
    tendsto_annularContractedUpperRetainedWeightedFreezingNormSum_zero
      heta hrho hε hεA hgrid k hr htime hsigned mode hmode
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  exact squeeze_zero'
    (Eventually.of_forall fun _N ↦ norm_nonneg _)
    (Eventually.of_forall fun N ↦
      norm_annularContractedUpperRetainedLebesgueWeightedLiveDigitJointSum_sub_affine_le
        ε A eta rho N k hr mode hmode)
    hnorm

end

end Erdos1002
