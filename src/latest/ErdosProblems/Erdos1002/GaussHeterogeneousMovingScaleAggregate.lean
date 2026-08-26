import ErdosProblems.Erdos1002.GaussMovingSignedMarkedFourier

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Finite tagged aggregates at a moving scale

The canonical sorting of labeled annular occurrences produces a finite
family indexed by the occurrence-order equivalence `e`.  The individual
order-class densities need not be identified.  This file proves the
moving-scale factorial theorem directly for the tagged finite sum from
only the aggregate total and short-gap densities.  Tags are never erased
by taking a union of tuple finsets.
-/

open Filter MeasureTheory Set Finset
open scoped BigOperators Topology symmDiff

namespace Erdos1002

noncomputable section

local instance (P : Prop) : Decidable P := Classical.propDecidable P

variable {β : Type*} [Fintype β]

def aggregateTupleFamilyCard {r : ℕ}
    (tuples : β → Finset (Fin r → ℕ)) : ℕ :=
  ∑ b, (tuples b).card

def aggregateShortTupleFamilyCard {r gap : ℕ}
    (tuples : β → Finset (Fin r → ℕ)) : ℕ :=
  ∑ b, (shortNatTupleFamily gap (tuples b)).card

def aggregateSeparatedTupleFamilyCard {r gap : ℕ}
    (tuples : β → Finset (Fin r → ℕ)) : ℕ :=
  ∑ b, (separatedNatTupleFamily gap (tuples b)).card

theorem aggregate_short_add_separated_card {r gap : ℕ}
    (tuples : β → Finset (Fin r → ℕ)) :
    aggregateShortTupleFamilyCard (gap := gap) tuples +
      aggregateSeparatedTupleFamilyCard (gap := gap) tuples =
        aggregateTupleFamilyCard tuples := by
  unfold aggregateShortTupleFamilyCard
    aggregateSeparatedTupleFamilyCard aggregateTupleFamilyCard
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro b hb
  exact card_shortNatTupleFamily_add_card_separatedNatTupleFamily
    (gap := gap) (tuples b)

theorem tendsto_component_card_div_scale_zero_of_aggregate_zero
    {r : ℕ} (scale : ℕ → ℝ)
    (hscalePos : ∀ᶠ n : ℕ in atTop, 0 < scale n)
    (tuples : ℕ → β → Finset (Fin r → ℕ))
    (haggregate : Tendsto
      (fun n ↦ (aggregateTupleFamilyCard (tuples n) : ℝ) /
        scale n ^ r) atTop (nhds 0))
    (b : β) :
    Tendsto
      (fun n ↦ ((tuples n b).card : ℝ) / scale n ^ r)
      atTop (nhds 0) := by
  refine squeeze_zero' ?_ ?_ haggregate
  · filter_upwards [hscalePos] with n hn
    positivity
  · filter_upwards [hscalePos] with n hn
    apply div_le_div_of_nonneg_right
    · have hnat :
          (tuples n b).card ≤ aggregateTupleFamilyCard (tuples n) := by
        unfold aggregateTupleFamilyCard
        exact Finset.single_le_sum
          (fun c _hc ↦ Nat.zero_le ((tuples n c).card))
          (Finset.mem_univ b)
      exact_mod_cast hnat
    · positivity

theorem eventually_component_card_div_scale_le_of_aggregate_tendsto
    {r : ℕ} {density : ℝ}
    (scale : ℕ → ℝ)
    (hscalePos : ∀ᶠ n : ℕ in atTop, 0 < scale n)
    (tuples : ℕ → β → Finset (Fin r → ℕ))
    (haggregate : Tendsto
      (fun n ↦ (aggregateTupleFamilyCard (tuples n) : ℝ) /
        scale n ^ r) atTop (nhds density)) :
    ∀ᶠ n : ℕ in atTop, ∀ b,
      ((tuples n b).card : ℝ) / scale n ^ r ≤
        |density| + 1 := by
  have hclose : ∀ᶠ n : ℕ in atTop,
      dist ((aggregateTupleFamilyCard (tuples n) : ℝ) /
        scale n ^ r) density < 1 := by
    simpa only [Metric.mem_ball] using!
      haggregate.eventually
        (Metric.ball_mem_nhds density zero_lt_one)
  filter_upwards [hscalePos, hclose] with n hn hdist
  intro b
  let component : ℝ :=
    ((tuples n b).card : ℝ) / scale n ^ r
  let total : ℝ :=
    (aggregateTupleFamilyCard (tuples n) : ℝ) / scale n ^ r
  have hcompTotal : component ≤ total := by
    dsimp only [component, total]
    apply div_le_div_of_nonneg_right
    · have hnat :
          (tuples n b).card ≤ aggregateTupleFamilyCard (tuples n) := by
        unfold aggregateTupleFamilyCard
        exact Finset.single_le_sum
          (fun c _hc ↦ Nat.zero_le ((tuples n c).card))
          (Finset.mem_univ b)
      exact_mod_cast hnat
    · positivity
  have htotal :
      total ≤ |density| + 1 := by
    have hlt : total < |density| + 1 := by
      calc
        total = (total - density) + density := by ring
        _ ≤ |total - density| + |density| :=
          add_le_add (le_abs_self _) (le_abs_self _)
        _ < 1 + |density| := by
          have : |total - density| < 1 := by
            simpa only [total, Real.dist_eq] using! hdist
          linarith
        _ = |density| + 1 := by ring
    exact hlt.le
  exact hcompTotal.trans htotal

theorem tendsto_bounded_nonneg_mul_zero
    (a b : ℕ → ℝ) {C : ℝ} (hC : 0 ≤ C)
    (ha0 : ∀ᶠ n : ℕ in atTop, 0 ≤ a n)
    (haC : ∀ᶠ n : ℕ in atTop, a n ≤ C)
    (hb : Tendsto b atTop (nhds 0)) :
    Tendsto (fun n ↦ a n * b n) atTop (nhds 0) := by
  rw [tendsto_zero_iff_abs_tendsto_zero]
  apply squeeze_zero'
  · exact Eventually.of_forall fun n ↦ abs_nonneg _
  · filter_upwards [ha0, haC] with n ha0n haCn
    change |a n * b n| ≤ C * |b n|
    rw [abs_mul, abs_of_nonneg ha0n]
    exact mul_le_mul haCn (le_rfl) (abs_nonneg _) hC
  · have habs : Tendsto (fun n ↦ |b n|) atTop (nhds 0) := by
      simpa only [abs_zero] using! hb.abs
    simpa only [mul_zero] using!
      (tendsto_const_nhds : Tendsto
        (fun _n : ℕ ↦ C) atTop (nhds C)).mul habs

theorem
    tendsto_aggregate_card_mul_movingRareDigitProduct_of_density_common
    {r : ℕ} {density common : ℝ}
    (scale : ℕ → ℝ) (hscale : Tendsto scale atTop atTop)
    (lower upper : β → Fin r → ℝ)
    (hlower : ∀ b i, 0 < lower b i)
    (hupper : ∀ b i, lower b i < upper b i)
    (hcommon : ∀ b,
      (∏ i, (upper b i - lower b i) / Real.log 2) = common)
    (tuples : ℕ → β → Finset (Fin r → ℕ))
    (haggregate : Tendsto
      (fun n ↦ (aggregateTupleFamilyCard (tuples n) : ℝ) /
        scale n ^ r) atTop (nhds density)) :
    Tendsto
      (fun n ↦ ∑ b,
        ((tuples n b).card : ℝ) *
          ∏ i, gaussMeasure.real
            (scaledGaussFirstDigitWindow
              (scale n) (lower b i) (upper b i)))
      atTop (nhds (density * common)) := by
  let component : β → ℕ → ℝ := fun b n ↦
    ((tuples n b).card : ℝ) / scale n ^ r
  let scaledProduct : β → ℕ → ℝ := fun b n ↦
    ∏ i, scale n *
      gaussMeasure.real
        (scaledGaussFirstDigitWindow
          (scale n) (lower b i) (upper b i))
  let deviation : β → ℕ → ℝ := fun b n ↦
    scaledProduct b n - common
  have hscalePos := hscale.eventually_gt_atTop 0
  have hcomponentBound :=
    eventually_component_card_div_scale_le_of_aggregate_tendsto
      scale hscalePos tuples haggregate
  have hcomponentNonneg : ∀ b,
      ∀ᶠ n : ℕ in atTop, 0 ≤ component b n := by
    intro b
    filter_upwards [hscalePos] with n hn
    dsimp only [component]
    positivity
  have hdeviation : ∀ b,
      Tendsto (deviation b) atTop (nhds 0) := by
    intro b
    have hscaled :=
      tendsto_movingGaussHeterogeneousRareDigitProduct
        scale hscale (lower b) (upper b) (hlower b) (hupper b)
    have hsub := hscaled.sub
      (tendsto_const_nhds : Tendsto
        (fun _n : ℕ ↦ common) atTop (nhds common))
    simpa only [deviation, scaledProduct, hcommon b, sub_self] using! hsub
  have hcomponentDeviation : ∀ b,
      Tendsto (fun n ↦ component b n * deviation b n)
        atTop (nhds 0) := by
    intro b
    exact tendsto_bounded_nonneg_mul_zero
      (component b) (deviation b)
      (add_nonneg (abs_nonneg density) zero_le_one)
      (hcomponentNonneg b)
      (by
        filter_upwards [hcomponentBound] with n hn
        exact hn b)
      (hdeviation b)
  have hsumDeviation :
      Tendsto (fun n ↦ ∑ b, component b n * deviation b n)
        atTop (nhds 0) :=
    by
      simpa using! tendsto_finset_sum Finset.univ
        (fun b _hb ↦ hcomponentDeviation b)
  have hmain :=
    (tendsto_const_nhds : Tendsto
      (fun _n : ℕ ↦ common) atTop (nhds common)).mul haggregate
  have hadd := hsumDeviation.add hmain
  have hadd' : Tendsto
      (fun n ↦
        (∑ b, component b n * deviation b n) +
          common *
            ((aggregateTupleFamilyCard (tuples n) : ℝ) /
              scale n ^ r))
      atTop (nhds (density * common)) := by
    simpa only [zero_add, mul_comm] using! hadd
  apply hadd'.congr'
  filter_upwards [hscalePos] with n hn
  have hsne : scale n ≠ 0 := ne_of_gt hn
  have hscaled (b : β) :
      scaledProduct b n =
        scale n ^ r *
          ∏ i, gaussMeasure.real
            (scaledGaussFirstDigitWindow
              (scale n) (lower b i) (upper b i)) := by
    dsimp only [scaledProduct]
    rw [Finset.prod_mul_distrib]
    simp only [Finset.prod_const, Finset.card_univ,
      Fintype.card_fin]
  have hcomponentSum :
      (∑ b, component b n) =
        (aggregateTupleFamilyCard (tuples n) : ℝ) /
          scale n ^ r := by
    dsimp only [component, aggregateTupleFamilyCard]
    rw [← Finset.sum_div]
    push_cast
    rfl
  symm
  calc
    (∑ b,
        ((tuples n b).card : ℝ) *
          ∏ i, gaussMeasure.real
            (scaledGaussFirstDigitWindow
              (scale n) (lower b i) (upper b i))) =
      ∑ b, component b n * scaledProduct b n := by
        apply Finset.sum_congr rfl
        intro b hb
        rw [hscaled]
        dsimp only [component]
        field_simp [hsne]
    _ = (∑ b, component b n * deviation b n) +
          common * ∑ b, component b n := by
      dsimp only [deviation]
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro b hb
      ring
    _ = (∑ b, component b n * deviation b n) +
          common *
            ((aggregateTupleFamilyCard (tuples n) : ℝ) /
              scale n ^ r) := by
      rw [hcomponentSum]

def aggregateGaussMovingHeterogeneousDigitTupleSum
    {r : ℕ} (scale : ℝ)
    (lower upper : β → Fin r → ℝ)
    (tuples : β → Finset (Fin r → ℕ)) : ℝ :=
  ∑ b, gaussMovingHeterogeneousDigitTupleSum
    scale (lower b) (upper b) (tuples b)

def aggregateGaussMovingHeterogeneousApproximationTupleSum
    {r : ℕ} (scale : ℝ)
    (lower upper : β → Fin r → ℝ)
    (tuples : β → Finset (Fin r → ℕ)) : ℝ :=
  ∑ b, gaussMovingHeterogeneousApproximationTupleSum
    scale (lower b) (upper b) (tuples b)

theorem tendsto_aggregateGaussMovingHeterogeneousDigitTupleSum
    {r : ℕ} (hr : 0 < r) {density common : ℝ}
    (scale : ℕ → ℝ) (hscale : Tendsto scale atTop atTop)
    (lower upper : β → Fin r → ℝ)
    (hlower : ∀ b i, 0 < lower b i)
    (hupper : ∀ b i, lower b i < upper b i)
    (hcommon : ∀ b,
      (∏ i, (upper b i - lower b i) / Real.log 2) = common)
    (gap : ℕ → ℕ) (hgapTop : Tendsto gap atTop atTop)
    (hgapPos : ∀ᶠ n : ℕ in atTop, 0 < gap n)
    (tuples : ℕ → β → Finset (Fin r → ℕ))
    (hchronological : ∀ n b, ∀ t ∈ tuples n b,
      IsChronologicalNatTuple t)
    (htotalDensity : Tendsto
      (fun n ↦ (aggregateTupleFamilyCard (tuples n) : ℝ) /
        scale n ^ r) atTop (nhds density))
    (hshortDensity : Tendsto
      (fun n ↦
        (aggregateShortTupleFamilyCard
          (gap := gap n) (tuples n) : ℝ) /
            scale n ^ r)
      atTop (nhds 0)) :
    Tendsto
      (fun n ↦ aggregateGaussMovingHeterogeneousDigitTupleSum
        (scale n) lower upper (tuples n))
      atTop (nhds (density * common)) := by
  let short : ℕ → β → Finset (Fin r → ℕ) := fun n b ↦
    shortNatTupleFamily (gap n) (tuples n b)
  let separated : ℕ → β → Finset (Fin r → ℕ) := fun n b ↦
    separatedNatTupleFamily (gap n) (tuples n b)
  have hscalePos := hscale.eventually_gt_atTop 0
  have hshortComponent : ∀ b,
      Tendsto
        (fun n ↦ ((short n b).card : ℝ) / scale n ^ r)
        atTop (nhds 0) := by
    intro b
    apply tendsto_component_card_div_scale_zero_of_aggregate_zero
      scale hscalePos short
    simpa only [short, aggregateTupleFamilyCard] using! hshortDensity
  have hshortSumComponent : ∀ b,
      Tendsto
        (fun n ↦ gaussMovingHeterogeneousDigitTupleSum
          (scale n) (lower b) (upper b) (short n b))
        atTop (nhds 0) := by
    intro b
    have hweight :=
      tendsto_card_mul_movingGaussHeterogeneousRareDigitProduct_of_density
        scale hscale (lower b) (upper b) (hlower b) (hupper b)
          (short · b) (hshortComponent b)
    have hweight0 : Tendsto
        (fun n ↦ ((short n b).card : ℝ) *
          ∏ i, gaussMeasure.real
            (scaledGaussFirstDigitWindow
              (scale n) (lower b i) (upper b i)))
        atTop (nhds 0) := by
      simpa only [zero_mul] using! hweight
    have hupperBound : Tendsto
        (fun n ↦ ((short n b).card : ℝ) *
          (7 ^ (r - 1) *
            ∏ i, gaussMeasure.real
              (scaledGaussFirstDigitWindow
                (scale n) (lower b i) (upper b i))))
        atTop (nhds 0) := by
      have hraw :=
        (tendsto_const_nhds : Tendsto
          (fun _n : ℕ ↦ (7 : ℝ) ^ (r - 1))
          atTop (nhds ((7 : ℝ) ^ (r - 1)))).mul hweight0
      have hraw' : Tendsto
          (fun n ↦ (7 : ℝ) ^ (r - 1) *
            (((short n b).card : ℝ) *
              ∏ i, gaussMeasure.real
                (scaledGaussFirstDigitWindow
                  (scale n) (lower b i) (upper b i))))
          atTop (nhds 0) := by
        simpa only [mul_zero] using! hraw
      apply hraw'.congr'
      filter_upwards with n
      ring
    apply squeeze_zero'
    · exact Eventually.of_forall fun n ↦
        Finset.sum_nonneg fun _t _ht ↦ measureReal_nonneg
    · filter_upwards with n
      simpa only [short] using!
        gaussMovingHeterogeneousDigitTupleSum_short_le
          hr (lower b) (upper b) (tuples n b)
            (hchronological n b)
    · exact hupperBound
  have hshortSum :
      Tendsto
        (fun n ↦ ∑ b,
          gaussMovingHeterogeneousDigitTupleSum
            (scale n) (lower b) (upper b) (short n b))
        atTop (nhds 0) := by
    simpa using! tendsto_finset_sum Finset.univ
      (fun b _hb ↦ hshortSumComponent b)
  have hseparatedDensity : Tendsto
      (fun n ↦
        (aggregateTupleFamilyCard (separated n) : ℝ) /
          scale n ^ r)
      atTop (nhds density) := by
    have hsub := htotalDensity.sub hshortDensity
    have hsub' : Tendsto
        (fun n : ℕ ↦
          (aggregateTupleFamilyCard (tuples n) : ℝ) /
              scale n ^ r -
            (aggregateShortTupleFamilyCard
              (gap := gap n) (tuples n) : ℝ) /
                scale n ^ r)
        atTop (nhds density) := by
      simpa only [sub_zero] using! hsub
    apply hsub'.congr'
    filter_upwards [hscalePos] with n hn
    have hcard :=
      aggregate_short_add_separated_card
        (β := β) (gap := gap n) (tuples n)
    have hcardReal :
        (aggregateShortTupleFamilyCard
              (gap := gap n) (tuples n) : ℝ) +
          (aggregateSeparatedTupleFamilyCard
              (gap := gap n) (tuples n) : ℝ) =
            (aggregateTupleFamilyCard (tuples n) : ℝ) := by
      exact_mod_cast hcard
    change
      (aggregateTupleFamilyCard (tuples n) : ℝ) / scale n ^ r -
          (aggregateShortTupleFamilyCard
            (gap := gap n) (tuples n) : ℝ) / scale n ^ r =
        (aggregateSeparatedTupleFamilyCard
          (gap := gap n) (tuples n) : ℝ) / scale n ^ r
    rw [← hcardReal]
    ring
  have hseparatedProduct :=
    tendsto_aggregate_card_mul_movingRareDigitProduct_of_density_common
      scale hscale lower upper hlower hupper hcommon
        separated hseparatedDensity
  have hseparatedBound :=
    eventually_component_card_div_scale_le_of_aggregate_tendsto
      scale hscalePos separated hseparatedDensity
  have hmix :=
    tendsto_gaussDigitRelativeMixingFactor (r := r) hgapTop
  have hscaledProduct : ∀ b,
      Tendsto
        (fun n ↦ ∏ i, scale n *
          gaussMeasure.real
            (scaledGaussFirstDigitWindow
              (scale n) (lower b i) (upper b i)))
        atTop (nhds common) := by
    intro b
    simpa only [hcommon b] using!
      tendsto_movingGaussHeterogeneousRareDigitProduct
        scale hscale (lower b) (upper b) (hlower b) (hupper b)
  have herrorUpperComponent : ∀ b,
      Tendsto
        (fun n ↦ ((separated n b).card : ℝ) *
          (((1 + gaussDigitExponentialRate (gap n)) ^ (r - 1) - 1) *
            ∏ i, gaussMeasure.real
              (scaledGaussFirstDigitWindow
                (scale n) (lower b i) (upper b i))))
        atTop (nhds 0) := by
    intro b
    let normalized : ℕ → ℝ := fun n ↦
      ((separated n b).card : ℝ) / scale n ^ r
    let vanishing : ℕ → ℝ := fun n ↦
      ((1 + gaussDigitExponentialRate (gap n)) ^ (r - 1) - 1) *
        ∏ i, scale n *
          gaussMeasure.real
            (scaledGaussFirstDigitWindow
              (scale n) (lower b i) (upper b i))
    have hv : Tendsto vanishing atTop (nhds 0) := by
      have hraw := hmix.mul (hscaledProduct b)
      simpa only [vanishing, zero_mul] using! hraw
    have hnorm0 : ∀ᶠ n : ℕ in atTop, 0 ≤ normalized n := by
      filter_upwards [hscalePos] with n hn
      dsimp only [normalized]
      positivity
    have hnormBound : ∀ᶠ n : ℕ in atTop,
        normalized n ≤ |density| + 1 := by
      filter_upwards [hseparatedBound] with n hn
      exact hn b
    have hprod :=
      tendsto_bounded_nonneg_mul_zero normalized vanishing
        (add_nonneg (abs_nonneg density) zero_le_one)
        hnorm0 hnormBound hv
    apply hprod.congr'
    filter_upwards [hscalePos] with n hn
    have hsne : scale n ≠ 0 := ne_of_gt hn
    dsimp only [normalized, vanishing]
    rw [Finset.prod_mul_distrib]
    simp only [Finset.prod_const, Finset.card_univ,
      Fintype.card_fin]
    field_simp [hsne]
  have hseparatedErrorComponent : ∀ b,
      Tendsto
        (fun n ↦
          gaussMovingHeterogeneousDigitTupleSum
              (scale n) (lower b) (upper b) (separated n b) -
            ((separated n b).card : ℝ) *
              ∏ i, gaussMeasure.real
                (scaledGaussFirstDigitWindow
                  (scale n) (lower b i) (upper b i)))
        atTop (nhds 0) := by
    intro b
    rw [tendsto_zero_iff_abs_tendsto_zero]
    apply squeeze_zero'
    · exact Eventually.of_forall fun n ↦ abs_nonneg _
    · filter_upwards [hgapPos] with n hgap
      simpa only [separated] using!
        abs_gaussMovingHeterogeneousDigitTupleSum_separated_sub_product_le
          hr hgap (lower b) (upper b) (tuples n b)
    · exact herrorUpperComponent b
  have hseparatedError :
      Tendsto
        (fun n ↦ ∑ b,
          (gaussMovingHeterogeneousDigitTupleSum
              (scale n) (lower b) (upper b) (separated n b) -
            ((separated n b).card : ℝ) *
              ∏ i, gaussMeasure.real
                (scaledGaussFirstDigitWindow
                  (scale n) (lower b i) (upper b i))))
        atTop (nhds 0) := by
    simpa using! tendsto_finset_sum Finset.univ
      (fun b _hb ↦ hseparatedErrorComponent b)
  have hseparatedSum : Tendsto
      (fun n ↦ ∑ b,
        gaussMovingHeterogeneousDigitTupleSum
          (scale n) (lower b) (upper b) (separated n b))
      atTop (nhds (density * common)) := by
    have hadd := hseparatedError.add hseparatedProduct
    have hadd' : Tendsto
        (fun n ↦
          (∑ b,
            (gaussMovingHeterogeneousDigitTupleSum
                (scale n) (lower b) (upper b) (separated n b) -
              ((separated n b).card : ℝ) *
                ∏ i, gaussMeasure.real
                  (scaledGaussFirstDigitWindow
                    (scale n) (lower b i) (upper b i)))) +
          ∑ b, ((separated n b).card : ℝ) *
            ∏ i, gaussMeasure.real
              (scaledGaussFirstDigitWindow
                (scale n) (lower b i) (upper b i)))
        atTop (nhds (density * common)) := by
      simpa only [zero_add] using! hadd
    apply hadd'.congr'
    filter_upwards with n
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro b hb
    ring
  have hsum := hshortSum.add hseparatedSum
  have hsum' : Tendsto
      (fun n ↦
        (∑ b, gaussMovingHeterogeneousDigitTupleSum
          (scale n) (lower b) (upper b) (short n b)) +
        ∑ b, gaussMovingHeterogeneousDigitTupleSum
          (scale n) (lower b) (upper b) (separated n b))
      atTop (nhds (density * common)) := by
    simpa only [zero_add] using! hsum
  apply hsum'.congr'
  filter_upwards with n
  unfold aggregateGaussMovingHeterogeneousDigitTupleSum
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro b hb
  simpa only [short, separated] using!
    (gaussMovingHeterogeneousDigitTupleSum_eq_short_add_separated
      (gap n) (lower b) (upper b) (tuples n b)).symm

theorem
    tendsto_aggregateGaussMovingHeterogeneousApproximationTupleSum_sub_digit_zero
    {r : ℕ} (hr : 0 < r) {A density : ℝ}
    (scale : ℕ → ℝ) (hscale : Tendsto scale atTop atTop)
    (lower upper : β → Fin r → ℝ)
    (hA : 0 ≤ A)
    (hlower : ∀ b i, 0 < lower b i)
    (hupper : ∀ b i, lower b i < upper b i)
    (hupperA : ∀ b i, upper b i ≤ A)
    (tuples : ℕ → β → Finset (Fin r → ℕ))
    (hchronological : ∀ n b, ∀ t ∈ tuples n b,
      IsChronologicalNatTuple t)
    (htotalDensity : Tendsto
      (fun n ↦ (aggregateTupleFamilyCard (tuples n) : ℝ) /
        scale n ^ r) atTop (nhds density)) :
    Tendsto
      (fun n ↦
        aggregateGaussMovingHeterogeneousApproximationTupleSum
            (scale n) lower upper (tuples n) -
          aggregateGaussMovingHeterogeneousDigitTupleSum
            (scale n) lower upper (tuples n))
      atTop (nhds 0) := by
  let C : ℝ :=
    (r : ℝ) * 2 *
      (1 + gaussDigitExponentialRate 1) ^ (r - 1) *
      (26 * A ^ 2 / Real.log 2) *
      ((2 * A + 10 * A ^ 2) / Real.log 2) ^ (r - 1)
  have hscalePos := hscale.eventually_gt_atTop 0
  have hscaleOne := hscale.eventually (eventually_ge_atTop (1 : ℝ))
  have hcomponentBound :=
    eventually_component_card_div_scale_le_of_aggregate_tendsto
      scale hscalePos tuples htotalDensity
  have hCdiv : Tendsto (fun n : ℕ ↦ C / scale n)
      atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop hscale
  have herrorComponent : ∀ b,
      Tendsto
        (fun n : ℕ ↦
          ∑ t ∈ tuples n b,
            gaussMeasure.real
              (gaussHeterogeneousApproximationTupleEvent
                  (scale n) (lower b) (upper b) t ∆
                gaussHeterogeneousDigitWindowTupleEvent
                  (scale n) (lower b) (upper b) t))
        atTop (nhds 0) := by
    intro b
    let err : ℕ → ℝ := fun n ↦
      ∑ t ∈ tuples n b,
        gaussMeasure.real
          (gaussHeterogeneousApproximationTupleEvent
              (scale n) (lower b) (upper b) t ∆
            gaussHeterogeneousDigitWindowTupleEvent
              (scale n) (lower b) (upper b) t)
    let normalized : ℕ → ℝ := fun n ↦
      ((tuples n b).card : ℝ) / scale n ^ r
    have hlarge :=
      eventually_movingHeterogeneousApproximationWindow_large
        scale hscale (lower b) (upper b) (hlower b)
    have herrUpper : ∀ᶠ n : ℕ in atTop,
        err n ≤ normalized n * (C / scale n) := by
      filter_upwards [hlarge, hscalePos, hscaleOne] with
        n hlargeN hpos hone
      have hraw :=
        sum_gaussMeasure_real_symmDiff_heterogeneousTuples_le_explicit
          hr (lower b) (upper b) (tuples n b) 1 (by norm_num)
            hpos hone hA (hlower b) (hupper b) (hupperA b)
            hlargeN
            (fun t ht i k hik ↦
              hchronological n b t ht i k hik)
      refine hraw.trans_eq ?_
      dsimp only [C, normalized]
      have hsne : scale n ≠ 0 := ne_of_gt hpos
      have hboundary :
          (26 * A ^ 2 / scale n ^ 2) / Real.log 2 =
            (26 * A ^ 2 / Real.log 2) / scale n ^ 2 := by
        field_simp
      have hwindow :
          ((2 * A + 10 * A ^ 2) / scale n) / Real.log 2 =
            ((2 * A + 10 * A ^ 2) / Real.log 2) /
              scale n := by
        field_simp
      rw [hboundary, hwindow, div_pow]
      have hpow : scale n ^ r =
          scale n ^ (r - 1) * scale n := by
        conv_lhs =>
          rw [show r = (r - 1) + 1 by omega, pow_succ]
      rw [hpow]
      field_simp [hsne]
    have hnormalized0 :
        ∀ᶠ n : ℕ in atTop, 0 ≤ normalized n := by
      filter_upwards [hscalePos] with n hn
      dsimp only [normalized]
      positivity
    have hnormalizedBound :
        ∀ᶠ n : ℕ in atTop,
          normalized n ≤ |density| + 1 := by
      filter_upwards [hcomponentBound] with n hn
      exact hn b
    have hupperZero :=
      tendsto_bounded_nonneg_mul_zero normalized
        (fun n ↦ C / scale n)
        (add_nonneg (abs_nonneg density) zero_le_one)
        hnormalized0 hnormalizedBound hCdiv
    change Tendsto err atTop (nhds 0)
    apply squeeze_zero'
    · exact Eventually.of_forall fun n ↦
        Finset.sum_nonneg fun _t _ht ↦ measureReal_nonneg
    · exact herrUpper
    · exact hupperZero
  have hdifferenceComponent : ∀ b,
      Tendsto
        (fun n ↦
          gaussMovingHeterogeneousApproximationTupleSum
              (scale n) (lower b) (upper b) (tuples n b) -
            gaussMovingHeterogeneousDigitTupleSum
              (scale n) (lower b) (upper b) (tuples n b))
        atTop (nhds 0) := by
    intro b
    rw [tendsto_zero_iff_abs_tendsto_zero]
    apply squeeze_zero'
    · exact Eventually.of_forall fun n ↦ abs_nonneg _
    · filter_upwards with n
      exact
        abs_gaussMovingHeterogeneousApproximationTupleSum_sub_digit_le
          (scale n) (lower b) (upper b) (tuples n b)
    · exact herrorComponent b
  have hsum : Tendsto
      (fun n ↦ ∑ b,
        (gaussMovingHeterogeneousApproximationTupleSum
            (scale n) (lower b) (upper b) (tuples n b) -
          gaussMovingHeterogeneousDigitTupleSum
            (scale n) (lower b) (upper b) (tuples n b)))
      atTop (nhds 0) := by
    simpa using! tendsto_finset_sum Finset.univ
      (fun b _hb ↦ hdifferenceComponent b)
  apply hsum.congr'
  filter_upwards with n
  unfold aggregateGaussMovingHeterogeneousApproximationTupleSum
    aggregateGaussMovingHeterogeneousDigitTupleSum
  rw [Finset.sum_sub_distrib]

theorem tendsto_aggregateGaussMovingHeterogeneousApproximationTupleSum
    {r : ℕ} (hr : 0 < r) {A density common : ℝ}
    (scale : ℕ → ℝ) (hscale : Tendsto scale atTop atTop)
    (lower upper : β → Fin r → ℝ)
    (hA : 0 ≤ A)
    (hlower : ∀ b i, 0 < lower b i)
    (hupper : ∀ b i, lower b i < upper b i)
    (hupperA : ∀ b i, upper b i ≤ A)
    (hcommon : ∀ b,
      (∏ i, (upper b i - lower b i) / Real.log 2) = common)
    (gap : ℕ → ℕ) (hgapTop : Tendsto gap atTop atTop)
    (hgapPos : ∀ᶠ n : ℕ in atTop, 0 < gap n)
    (tuples : ℕ → β → Finset (Fin r → ℕ))
    (hchronological : ∀ n b, ∀ t ∈ tuples n b,
      IsChronologicalNatTuple t)
    (htotalDensity : Tendsto
      (fun n ↦ (aggregateTupleFamilyCard (tuples n) : ℝ) /
        scale n ^ r) atTop (nhds density))
    (hshortDensity : Tendsto
      (fun n ↦
        (aggregateShortTupleFamilyCard
          (gap := gap n) (tuples n) : ℝ) /
            scale n ^ r)
      atTop (nhds 0)) :
    Tendsto
      (fun n ↦
        aggregateGaussMovingHeterogeneousApproximationTupleSum
          (scale n) lower upper (tuples n))
      atTop (nhds (density * common)) := by
  have hreplacement :=
    tendsto_aggregateGaussMovingHeterogeneousApproximationTupleSum_sub_digit_zero
      hr scale hscale lower upper hA hlower hupper hupperA
        tuples hchronological htotalDensity
  have hdigit :=
    tendsto_aggregateGaussMovingHeterogeneousDigitTupleSum
      hr scale hscale lower upper hlower hupper hcommon
        gap hgapTop hgapPos tuples hchronological
        htotalDensity hshortDensity
  have hadd := hreplacement.add hdigit
  have hadd' : Tendsto
      (fun n ↦
        (aggregateGaussMovingHeterogeneousApproximationTupleSum
            (scale n) lower upper (tuples n) -
          aggregateGaussMovingHeterogeneousDigitTupleSum
            (scale n) lower upper (tuples n)) +
        aggregateGaussMovingHeterogeneousDigitTupleSum
          (scale n) lower upper (tuples n))
      atTop (nhds (density * common)) := by
    simpa only [zero_add] using! hadd
  apply hadd'.congr'
  filter_upwards with n
  ring

def aggregateGaussMovingSignedApproximationTupleSum
    {r : ℕ} (scale : ℝ)
    (signedLower signedUpper : β → Fin r → ℝ)
    (tuples : β → Finset (Fin r → ℕ)) : ℝ :=
  ∑ b, gaussMovingSignedApproximationTupleSum
    scale (signedLower b) (signedUpper b) (tuples b)

theorem tendsto_aggregateGaussMovingSignedApproximationTupleSum
    {r : ℕ} (hr : 0 < r) {A density common : ℝ}
    (scale : ℕ → ℝ) (hscale : Tendsto scale atTop atTop)
    (signedLower signedUpper : β → Fin r → ℝ)
    (parity : β → Fin r → Fin 2)
    (hA : 0 ≤ A)
    (hlower : ∀ b i, 0 <
      gaussPrescribedParityOrientedLower
        (parity b) (signedLower b) (signedUpper b) i)
    (hupper : ∀ b i,
      gaussPrescribedParityOrientedLower
          (parity b) (signedLower b) (signedUpper b) i <
        gaussPrescribedParityOrientedUpper
          (parity b) (signedLower b) (signedUpper b) i)
    (hupperA : ∀ b i,
      gaussPrescribedParityOrientedUpper
        (parity b) (signedLower b) (signedUpper b) i ≤ A)
    (hcommon : ∀ b,
      (∏ i,
        (gaussPrescribedParityOrientedUpper
              (parity b) (signedLower b) (signedUpper b) i -
          gaussPrescribedParityOrientedLower
              (parity b) (signedLower b) (signedUpper b) i) /
            Real.log 2) = common)
    (gap : ℕ → ℕ) (hgapTop : Tendsto gap atTop atTop)
    (hgapPos : ∀ᶠ n : ℕ in atTop, 0 < gap n)
    (tuples : ℕ → β → Finset (Fin r → ℕ))
    (hchronological : ∀ n b, ∀ t ∈ tuples n b,
      IsChronologicalNatTuple t)
    (hparity : ∀ n b, ∀ t ∈ tuples n b, ∀ i,
      t i % 2 = (parity b i).1)
    (htotalDensity : Tendsto
      (fun n ↦ (aggregateTupleFamilyCard (tuples n) : ℝ) /
        scale n ^ r) atTop (nhds density))
    (hshortDensity : Tendsto
      (fun n ↦
        (aggregateShortTupleFamilyCard
          (gap := gap n) (tuples n) : ℝ) /
            scale n ^ r)
      atTop (nhds 0)) :
    Tendsto
      (fun n ↦
        aggregateGaussMovingSignedApproximationTupleSum
          (scale n) signedLower signedUpper (tuples n))
      atTop (nhds (density * common)) := by
  let lower : β → Fin r → ℝ := fun b ↦
    gaussPrescribedParityOrientedLower
      (parity b) (signedLower b) (signedUpper b)
  let upper : β → Fin r → ℝ := fun b ↦
    gaussPrescribedParityOrientedUpper
      (parity b) (signedLower b) (signedUpper b)
  have hpositive :=
    tendsto_aggregateGaussMovingHeterogeneousApproximationTupleSum
      hr scale hscale lower upper hA hlower hupper hupperA hcommon
        gap hgapTop hgapPos tuples hchronological
        htotalDensity hshortDensity
  apply hpositive.congr'
  filter_upwards with n
  unfold aggregateGaussMovingSignedApproximationTupleSum
    aggregateGaussMovingHeterogeneousApproximationTupleSum
  apply Finset.sum_congr rfl
  intro b hb
  exact
    (gaussMovingSignedApproximationTupleSum_eq_oriented
      (scale n) (parity b) (signedLower b) (signedUpper b)
      (tuples n b) (hparity n b)).symm

def aggregateGaussMovingSignedMarkedFourierTupleSum
    {r : ℕ} (N : ℕ) (scale : ℝ)
    (signedLower signedUpper : β → Fin r → ℝ)
    (mode : β → Fin r → ℤ)
    (tuples : β → Finset (Fin r → ℕ)) : ℂ :=
  ∑ b, gaussMovingSignedMarkedFourierTupleSum
    N scale (signedLower b) (signedUpper b) (mode b) (tuples b)

@[simp] theorem aggregateGaussMovingSignedMarkedFourierTupleSum_zero
    {r : ℕ} (N : ℕ) (scale : ℝ)
    (signedLower signedUpper : β → Fin r → ℝ)
    (tuples : β → Finset (Fin r → ℕ)) :
    aggregateGaussMovingSignedMarkedFourierTupleSum
        N scale signedLower signedUpper (fun _b _i ↦ 0) tuples =
      (aggregateGaussMovingSignedApproximationTupleSum
        scale signedLower signedUpper tuples : ℂ) := by
  unfold aggregateGaussMovingSignedMarkedFourierTupleSum
    aggregateGaussMovingSignedApproximationTupleSum
  simp only [gaussMovingSignedMarkedFourierTupleSum_zero,
    Complex.ofReal_sum]

theorem tendsto_aggregateGaussMovingSignedMarkedFourierTupleSum_zero
    {r : ℕ} (hr : 0 < r) {A density common : ℝ}
    (N : ℕ → ℕ)
    (scale : ℕ → ℝ) (hscale : Tendsto scale atTop atTop)
    (signedLower signedUpper : β → Fin r → ℝ)
    (parity : β → Fin r → Fin 2)
    (hA : 0 ≤ A)
    (hlower : ∀ b i, 0 <
      gaussPrescribedParityOrientedLower
        (parity b) (signedLower b) (signedUpper b) i)
    (hupper : ∀ b i,
      gaussPrescribedParityOrientedLower
          (parity b) (signedLower b) (signedUpper b) i <
        gaussPrescribedParityOrientedUpper
          (parity b) (signedLower b) (signedUpper b) i)
    (hupperA : ∀ b i,
      gaussPrescribedParityOrientedUpper
        (parity b) (signedLower b) (signedUpper b) i ≤ A)
    (hcommon : ∀ b,
      (∏ i,
        (gaussPrescribedParityOrientedUpper
              (parity b) (signedLower b) (signedUpper b) i -
          gaussPrescribedParityOrientedLower
              (parity b) (signedLower b) (signedUpper b) i) /
            Real.log 2) = common)
    (gap : ℕ → ℕ) (hgapTop : Tendsto gap atTop atTop)
    (hgapPos : ∀ᶠ n : ℕ in atTop, 0 < gap n)
    (tuples : ℕ → β → Finset (Fin r → ℕ))
    (hchronological : ∀ n b, ∀ t ∈ tuples n b,
      IsChronologicalNatTuple t)
    (hparity : ∀ n b, ∀ t ∈ tuples n b, ∀ i,
      t i % 2 = (parity b i).1)
    (htotalDensity : Tendsto
      (fun n ↦ (aggregateTupleFamilyCard (tuples n) : ℝ) /
        scale n ^ r) atTop (nhds density))
    (hshortDensity : Tendsto
      (fun n ↦
        (aggregateShortTupleFamilyCard
          (gap := gap n) (tuples n) : ℝ) /
            scale n ^ r)
      atTop (nhds 0)) :
    Tendsto
      (fun n ↦
        aggregateGaussMovingSignedMarkedFourierTupleSum
          (N n) (scale n) signedLower signedUpper
            (fun _b _i ↦ 0) (tuples n))
      atTop (nhds ((density * common : ℝ) : ℂ)) := by
  have hreal :=
    tendsto_aggregateGaussMovingSignedApproximationTupleSum
      hr scale hscale signedLower signedUpper parity hA
        hlower hupper hupperA hcommon gap hgapTop hgapPos
        tuples hchronological hparity htotalDensity hshortDensity
  have hcomplex := hreal.ofReal
  apply hcomplex.congr'
  filter_upwards with n
  exact
    (aggregateGaussMovingSignedMarkedFourierTupleSum_zero
      (β := β) (N n) (scale n) signedLower signedUpper
        (tuples n)).symm

end

end Erdos1002
