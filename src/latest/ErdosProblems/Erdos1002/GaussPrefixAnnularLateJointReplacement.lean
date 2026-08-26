import ErdosProblems.Erdos1002.GaussHeterogeneousMaskedTupleReplacement
import ErdosProblems.Erdos1002.GaussPrefixAnnularLateFutureBlock

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Joint future replacement in the upper retained annular family

Only coordinates after the midpoint split are replaced by one-digit
events.  The error is nevertheless estimated as a complete chronological
`r`-tuple.  Thus every prefix exact rare window remains in the replacement
witness, and the aggregate error is `O(1 / log N)`.
-/

open Filter Finset MeasureTheory Set
open scoped BigOperators Topology symmDiff

namespace Erdos1002

noncomputable section

local instance gaussPrefixAnnularLateJointReplacementPropDecidable
    (P : Prop) : Decidable P := Classical.propDecidable P

/-! ## Upper-retained annular specialization -/

/-- Raw midpoint predicate used as the replacement mask.  It is defined
for every natural tuple; membership in the upper-retained family is only
needed later to identify it with the packaged future block. -/
def annularUpperRetainedFutureMask
    (N : ℕ) {grid : ℕ}
    {k : AnnularGridIndex grid → ℕ}
    (_e : Fin (MixedOccurrenceCount k) ≃
      GaussPrefixMixedOccurrence k)
    (mode : Fin (MixedOccurrenceCount k) → ℤ)
    (hmode : mode ≠ 0)
    (t : Fin (MixedOccurrenceCount k) → ℕ)
    (j : Fin (MixedOccurrenceCount k)) : Bool :=
  decide
    (midpointPrefixSplitDepth
        (annularLastNonzeroIndex mode hmode)
        (annularDepthAmbientSize N) t < t j)

/-- Mixed exact/digit event for the upper-retained split, retaining the
exact prefix coordinates and replacing only genuine future coordinates. -/
def annularUpperRetainedMaskedApproximationDigitEvent
    (ε A : ℝ) (N : ℕ) {grid : ℕ}
    {k : AnnularGridIndex grid → ℕ}
    (e : Fin (MixedOccurrenceCount k) ≃
      GaussPrefixMixedOccurrence k)
    (mode : Fin (MixedOccurrenceCount k) → ℤ)
    (hmode : mode ≠ 0)
    (t : Fin (MixedOccurrenceCount k) → ℕ) : Set ℝ :=
  maskedOrderedEventIntersection
    (fun j ↦ gaussApproximationWindow
      (Real.log (N : ℝ)) (t j)
      (gaussPrescribedParityOrientedLower
        (flattenedAnnularParity e)
        (flattenedAnnularSignedLower ε A e)
        (flattenedAnnularSignedUpper ε A e) j)
      (gaussPrescribedParityOrientedUpper
        (flattenedAnnularParity e)
        (flattenedAnnularSignedLower ε A e)
        (flattenedAnnularSignedUpper ε A e) j))
    (fun j ↦ gaussDigitWindowAt
      (Real.log (N : ℝ)) (t j)
      (gaussPrescribedParityOrientedLower
        (flattenedAnnularParity e)
        (flattenedAnnularSignedLower ε A e)
        (flattenedAnnularSignedUpper ε A e) j)
      (gaussPrescribedParityOrientedUpper
        (flattenedAnnularParity e)
        (flattenedAnnularSignedLower ε A e)
        (flattenedAnnularSignedUpper ε A e) j))
    (annularUpperRetainedFutureMask N e mode hmode t)

/-- The total upper-retained tagged cardinality is bounded by the complete
canonical tagged cardinality. -/
theorem aggregate_annularUpperRetained_card_le_canonical
    (rho : ℝ) (N : ℕ) {grid : ℕ}
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k)
    (mode :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Fin (MixedOccurrenceCount k) → ℤ)
    (hmode : ∀ e, mode e ≠ 0) :
    aggregateTupleFamilyCard
        (fun e ↦ annularCanonicalLaterUpperMidpointTupleFamily
          rho N k hr e (mode e) (hmode e)) ≤
      totalCanonicalAnnularGridTupleCard N k := by
  unfold aggregateTupleFamilyCard totalCanonicalAnnularGridTupleCard
  apply Finset.sum_le_sum
  intro e _he
  apply Finset.card_le_card
  intro t ht
  have hupper :=
    (mem_laterUpperMidpointNatTupleFamily_iff.mp ht).1
  have hlate := (mem_lateFirstNatTupleFamily_iff.mp hupper).1
  exact (mem_separatedNatTupleFamily_iff.mp hlate).1

/-- Complete aggregate exact-to-future-digit replacement error on the
upper-retained family. -/
def aggregateAnnularUpperRetainedJointFutureReplacementError
    (ε A rho : ℝ) (N : ℕ) {grid : ℕ}
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k)
    (mode :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Fin (MixedOccurrenceCount k) → ℤ)
    (hmode : ∀ e, mode e ≠ 0) : ℝ :=
  ∑ e : Fin (MixedOccurrenceCount k) ≃
      GaussPrefixMixedOccurrence k,
    ∑ t ∈ annularCanonicalLaterUpperMidpointTupleFamily
        rho N k hr e (mode e) (hmode e),
      gaussMeasure.real
        (gaussHeterogeneousApproximationTupleEvent
              (Real.log (N : ℝ))
              (gaussPrescribedParityOrientedLower
                (flattenedAnnularParity e)
                (flattenedAnnularSignedLower ε A e)
                (flattenedAnnularSignedUpper ε A e))
              (gaussPrescribedParityOrientedUpper
                (flattenedAnnularParity e)
                (flattenedAnnularSignedLower ε A e)
                (flattenedAnnularSignedUpper ε A e)) t ∆
          annularUpperRetainedMaskedApproximationDigitEvent
            ε A N e (mode e) (hmode e) t)

set_option maxHeartbeats 2000000 in
/-- The exact-to-future-digit error of the complete upper-retained tagged
family tends to zero.  The absolute event error is inside both finite sums,
and its proof retains every prefix rare-window factor. -/
theorem tendsto_annularUpperRetained_jointFutureReplacement_zero
    {ε A : ℝ} (hε : 0 < ε) (hεA : ε < A)
    (rho : ℝ) {grid : ℕ} (hgrid : 0 < grid)
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k)
    (htime : ∀ i, 0 < k i → i.time.1 < grid)
    (hsigned : ∀ i, 0 < k i → i.signed.1 < grid)
    (mode :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Fin (MixedOccurrenceCount k) → ℤ)
    (hmode : ∀ e, mode e ≠ 0) :
    Tendsto
      (fun N ↦
        aggregateAnnularUpperRetainedJointFutureReplacementError
          ε A rho N k hr mode hmode)
      atTop (nhds 0) := by
  let tag :=
    Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k
  let scale : ℕ → ℝ := fun N ↦ Real.log (N : ℝ)
  let lower : tag → Fin (MixedOccurrenceCount k) → ℝ :=
    fun e ↦ gaussPrescribedParityOrientedLower
      (flattenedAnnularParity e)
      (flattenedAnnularSignedLower ε A e)
      (flattenedAnnularSignedUpper ε A e)
  let upper : tag → Fin (MixedOccurrenceCount k) → ℝ :=
    fun e ↦ gaussPrescribedParityOrientedUpper
      (flattenedAnnularParity e)
      (flattenedAnnularSignedLower ε A e)
      (flattenedAnnularSignedUpper ε A e)
  let tuples : ℕ → tag →
      Finset (Fin (MixedOccurrenceCount k) → ℕ) :=
    fun N e ↦ annularCanonicalLaterUpperMidpointTupleFamily
      rho N k hr e (mode e) (hmode e)
  let normalized : ℕ → ℝ := fun N ↦
    (aggregateTupleFamilyCard (tuples N) : ℝ) /
      scale N ^ MixedOccurrenceCount k
  let C : ℝ :=
    (MixedOccurrenceCount k : ℝ) * 2 *
      (1 + gaussDigitExponentialRate 1) ^
        (MixedOccurrenceCount k - 1) *
      (26 * A ^ 2 / Real.log 2) *
      ((2 * A + 10 * A ^ 2) / Real.log 2) ^
        (MixedOccurrenceCount k - 1)
  have hscale : Tendsto scale atTop atTop := by
    simpa only [scale] using! tendsto_log_natCast_atTop
  have hscalePos := hscale.eventually_gt_atTop 0
  have hscaleOne := hscale.eventually (eventually_ge_atTop (1 : ℝ))
  have hlower : ∀ e i, 0 < lower e i := by
    intro e i
    exact flattenedAnnular_oriented_lower_pos
      hε hεA hgrid hsigned e i
  have hlowerUpper : ∀ e i, lower e i < upper e i := by
    intro e i
    exact flattenedAnnular_oriented_lower_lt_upper
      hεA hgrid e i
  have hupperA : ∀ e i, upper e i ≤ A := by
    intro e i
    exact flattenedAnnular_oriented_upper_le
      hεA hgrid hsigned e i
  have hlarge :
      ∀ᶠ N : ℕ in atTop, ∀ e : tag, ∀ i,
        16 * (upper e i) ^ 2 ≤ lower e i * scale N := by
    apply Filter.eventually_all.mpr
    intro e
    exact eventually_movingHeterogeneousApproximationWindow_large
      scale hscale (lower e) (upper e) (hlower e)
  have htotal :
      Tendsto
        (fun N ↦
          (totalCanonicalAnnularGridTupleCard N k : ℝ) /
            scale N ^ MixedOccurrenceCount k)
        atTop (nhds (annularOccurrenceTimeDensity k)) := by
    simpa only [scale] using!
      tendsto_totalCanonicalAnnularGridTupleCard_density
        hgrid k hr htime
  have hnormalizedBound :
      ∀ᶠ N : ℕ in atTop,
        normalized N ≤ |annularOccurrenceTimeDensity k| + 1 := by
    have hfullAbs := htotal.norm
    have hfullBound :=
      hfullAbs.eventually_lt_const
        (show ‖annularOccurrenceTimeDensity k‖ <
            |annularOccurrenceTimeDensity k| + 1 by
          rw [Real.norm_eq_abs]
          linarith)
    filter_upwards [hscalePos, hfullBound] with N hscaleN hfullN
    have hcard :
        aggregateTupleFamilyCard (tuples N) ≤
          totalCanonicalAnnularGridTupleCard N k := by
      simpa only [tuples] using!
        aggregate_annularUpperRetained_card_le_canonical
          rho N k hr mode hmode
    have hratio :
        normalized N ≤
          (totalCanonicalAnnularGridTupleCard N k : ℝ) /
            scale N ^ MixedOccurrenceCount k := by
      dsimp only [normalized]
      apply div_le_div_of_nonneg_right
      · exact_mod_cast hcard
      · positivity
    exact hratio.trans
      ((le_abs_self _).trans hfullN.le)
  have hCdiv :
      Tendsto (fun N : ℕ ↦ C / scale N) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop hscale
  have hupperZero :
      Tendsto (fun N ↦ normalized N * (C / scale N))
        atTop (nhds 0) := by
    apply tendsto_bounded_nonneg_mul_zero
      normalized (fun N ↦ C / scale N)
      (C := |annularOccurrenceTimeDensity k| + 1) (by positivity)
    · filter_upwards [hscalePos] with N hscaleN
      dsimp only [normalized]
      positivity
    · exact hnormalizedBound
    · exact hCdiv
  apply squeeze_zero'
  · exact Eventually.of_forall fun N ↦ by
      unfold aggregateAnnularUpperRetainedJointFutureReplacementError
      exact Finset.sum_nonneg fun _e _he ↦
        Finset.sum_nonneg fun _t _ht ↦ measureReal_nonneg
  · filter_upwards [hscalePos, hscaleOne, hlarge] with
      N hscaleN hscaleOneN hlargeN
    change
      aggregateAnnularUpperRetainedJointFutureReplacementError
          ε A rho N k hr mode hmode ≤
        normalized N * (C / scale N)
    let common : ℝ :=
      (MixedOccurrenceCount k : ℝ) *
        (2 * ((1 + gaussDigitExponentialRate 1) ^
          (MixedOccurrenceCount k - 1) *
          ((((26 * A ^ 2 / scale N ^ 2) / Real.log 2)) *
            (((2 * A + 10 * A ^ 2) / scale N) /
              Real.log 2) ^ (MixedOccurrenceCount k - 1))))
    have hsum :
        aggregateAnnularUpperRetainedJointFutureReplacementError
            ε A rho N k hr mode hmode ≤
          (aggregateTupleFamilyCard (tuples N) : ℝ) * common := by
      unfold aggregateAnnularUpperRetainedJointFutureReplacementError
      calc
        (∑ e : tag, ∑ t ∈ tuples N e,
            gaussMeasure.real
              (gaussHeterogeneousApproximationTupleEvent
                    (scale N) (lower e) (upper e) t ∆
                maskedOrderedEventIntersection
                  (fun i ↦ gaussApproximationWindow
                    (scale N) (t i) (lower e i) (upper e i))
                  (fun i ↦ gaussDigitWindowAt
                    (scale N) (t i) (lower e i) (upper e i))
                  (annularUpperRetainedFutureMask
                    N e (mode e) (hmode e) t))) ≤
            ∑ e : tag, ((tuples N e).card : ℝ) * common := by
          apply Finset.sum_le_sum
          intro e _he
          simpa only [common] using!
            sum_gaussMeasure_real_symmDiff_heterogeneousMaskedTuples_le_explicit
              hr (lower e) (upper e) (tuples N e)
              (fun t ↦ annularUpperRetainedFutureMask
                N e (mode e) (hmode e) t)
              1 (by norm_num) hscaleN hscaleOneN
              (hε.le.trans hεA.le) (hlower e) (hlowerUpper e)
              (hupperA e) (hlargeN e)
              (fun t ht i j hij ↦ by
                have hupperMem :=
                  (mem_laterUpperMidpointNatTupleFamily_iff.mp ht).1
                have hlate :=
                  (mem_lateFirstNatTupleFamily_iff.mp hupperMem).1
                exact
                  canonicalAnnularGridTupleFamily_chronological
                    N k e t
                    (mem_separatedNatTupleFamily_iff.mp hlate).1
                    i j hij)
        _ = (aggregateTupleFamilyCard (tuples N) : ℝ) * common := by
          unfold aggregateTupleFamilyCard
          rw [Nat.cast_sum, Finset.sum_mul]
    refine hsum.trans_eq ?_
    dsimp only [normalized, C, common]
    have hsne : scale N ≠ 0 := ne_of_gt hscaleN
    have hboundary :
        (26 * A ^ 2 / scale N ^ 2) / Real.log 2 =
          (26 * A ^ 2 / Real.log 2) / scale N ^ 2 := by
      field_simp
    have hwindow :
        ((2 * A + 10 * A ^ 2) / scale N) / Real.log 2 =
          ((2 * A + 10 * A ^ 2) / Real.log 2) / scale N := by
      field_simp
    rw [hboundary, hwindow, div_pow]
    have hpow : scale N ^ MixedOccurrenceCount k =
        scale N ^ (MixedOccurrenceCount k - 1) * scale N := by
      conv_lhs =>
        rw [show MixedOccurrenceCount k =
          (MixedOccurrenceCount k - 1) + 1 by omega, pow_succ]
    rw [hpow]
    field_simp [hsne]
  · exact hupperZero

end

end Erdos1002
