import ErdosProblems.Erdos1002.GaussTransferAdjoint
import ErdosProblems.Erdos1002.GaussRareDigitQuantitative
import ErdosProblems.Erdos1002.FactorialMomentBounds
import Mathlib.Analysis.SpecialFunctions.Choose
import Mathlib.Topology.MetricSpace.Bounded

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Unmarked factorial limits for rare continued-fraction digits

This file closes the unmarked rare-event calculation under the proved
exponential digit mixing theorem.  There is no abstract mixing hypothesis:
all tuple estimates are instantiated with
`gaussDigitPsiMixing_exponential` and the explicit rate
`gaussDigitExponentialRate`.

The first layer is deliberately phrased for deterministic finite tuple
families.  This makes it reusable for parity-restricted index boxes and for
the finite unions of boxes used by the marked point-process argument.
-/

open Filter MeasureTheory Set Finset
open scoped BigOperators ENNReal Topology symmDiff

namespace Erdos1002

noncomputable section

/-! ## Exact tuple sums -/

/-- Sum of exact continued-fraction approximation-coordinate tuple masses. -/
def gaussApproximationTupleSum
    {r L : ℕ} (lower upper : ℝ)
    (tuples : Finset (Fin r → Fin L)) : ℝ :=
  ∑ t ∈ tuples,
    gaussMeasure.real
      (gaussApproximationTupleEvent (L : ℝ) lower upper
        (fun i ↦ (t i).1))

/-- Sum of the corresponding one-digit surrogate tuple masses. -/
def gaussDigitTupleSum
    {r L : ℕ} (lower upper : ℝ)
    (tuples : Finset (Fin r → Fin L)) : ℝ :=
  ∑ t ∈ tuples,
    gaussMeasure.real
      (gaussDigitTupleEvent (L : ℝ) lower upper
        (fun i ↦ (t i).1))

theorem measurableSet_gaussApproximationTupleEvent
    {r : ℕ} (scale lower upper : ℝ) (times : Fin r → ℕ) :
    MeasurableSet (gaussApproximationTupleEvent scale lower upper times) := by
  apply measurableSet_orderedEventIntersection
  intro A hA
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hA
  exact measurableSet_gaussApproximationWindow scale (times i) lower upper

theorem measurableSet_gaussDigitTupleEvent
    {r : ℕ} (scale lower upper : ℝ) (times : Fin r → ℕ) :
    MeasurableSet (gaussDigitTupleEvent scale lower upper times) := by
  apply measurableSet_orderedEventIntersection
  intro A hA
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hA
  exact measurableSet_gaussDigitWindowAt scale (times i) lower upper

/-- Chronological distinctness with the minimal positive gap. -/
def IsChronologicalTuple {r L : ℕ} (t : Fin r → Fin L) : Prop :=
  ∀ i k, i < k → (t i).1 + 1 ≤ (t k).1

/-- Separation by a prescribed deterministic gap. -/
def IsSeparatedTuple {r L : ℕ} (gap : ℕ) (t : Fin r → Fin L) : Prop :=
  ∀ i k, i < k → (t i).1 + gap ≤ (t k).1

theorem abs_gaussApproximationTupleSum_sub_gaussDigitTupleSum_le
    {r L : ℕ} (lower upper : ℝ)
    (tuples : Finset (Fin r → Fin L)) :
    |gaussApproximationTupleSum lower upper tuples -
        gaussDigitTupleSum lower upper tuples| ≤
      ∑ t ∈ tuples,
        gaussMeasure.real
          (gaussApproximationTupleEvent (L : ℝ) lower upper
              (fun i ↦ (t i).1) ∆
            gaussDigitTupleEvent (L : ℝ) lower upper
              (fun i ↦ (t i).1)) := by
  classical
  unfold gaussApproximationTupleSum gaussDigitTupleSum
  rw [← Finset.sum_sub_distrib]
  calc
    |∑ t ∈ tuples,
        (gaussMeasure.real
            (gaussApproximationTupleEvent (L : ℝ) lower upper
              (fun i ↦ (t i).1)) -
          gaussMeasure.real
            (gaussDigitTupleEvent (L : ℝ) lower upper
              (fun i ↦ (t i).1)))| ≤
        ∑ t ∈ tuples,
          |gaussMeasure.real
              (gaussApproximationTupleEvent (L : ℝ) lower upper
                (fun i ↦ (t i).1)) -
            gaussMeasure.real
              (gaussDigitTupleEvent (L : ℝ) lower upper
                (fun i ↦ (t i).1))| := by
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro t ht
      exact abs_measureReal_sub_le_measureReal_symmDiff
        (measurableSet_gaussApproximationTupleEvent (L : ℝ) lower upper
          (fun i ↦ (t i).1)).nullMeasurableSet
        (measurableSet_gaussDigitTupleEvent (L : ℝ) lower upper
          (fun i ↦ (t i).1)).nullMeasurableSet

/-- Unconditional `exact θ`-tuple to one-digit tuple replacement at
factorial scale. -/
theorem tendsto_gaussApproximationTupleSum_sub_gaussDigitTupleSum_zero
    {r : ℕ} (hr : 0 < r) {lower upper : ℝ}
    (hlower : 0 < lower) (hupper : lower < upper)
    (tuples : ∀ L : ℕ, Finset (Fin r → Fin L))
    (hchronological : ∀ L, ∀ t ∈ tuples L, IsChronologicalTuple t) :
    Tendsto
      (fun L : ℕ ↦
        gaussApproximationTupleSum lower upper (tuples L) -
          gaussDigitTupleSum lower upper (tuples L))
      atTop (𝓝 0) := by
  have hsymm : Tendsto
      (fun L : ℕ ↦
        ∑ t ∈ tuples L,
          gaussMeasure.real
            (gaussApproximationTupleEvent (L : ℝ) lower upper
                (fun i ↦ (t i).1) ∆
              gaussDigitTupleEvent (L : ℝ) lower upper
                (fun i ↦ (t i).1)))
      atTop (𝓝 0) := by
    exact tendsto_sum_gaussMeasure_real_symmDiff_closeTupleFamily_zero
      gaussDigitPsiMixing_exponential hr (R := 6) tuples hlower hupper
      hchronological (gaussDigitExponentialRate_nonnegative 1)
      (by simp [gaussDigitExponentialRate])
  rw [Metric.tendsto_atTop]
  intro η hη
  obtain ⟨L₀, hL₀⟩ := (Metric.tendsto_atTop.mp hsymm) η hη
  refine ⟨L₀, fun L hL ↦ ?_⟩
  rw [Real.dist_eq, sub_zero]
  have hsum := hL₀ L hL
  rw [Real.dist_eq, sub_zero,
    abs_of_nonneg (Finset.sum_nonneg fun _ _ ↦ measureReal_nonneg)] at hsum
  exact (abs_gaussApproximationTupleSum_sub_gaussDigitTupleSum_le
    lower upper (tuples L)).trans_lt hsum

/-! ## Exact one-point scale and digit tuple estimates -/

/-- Natural-scale rare-window intensity. -/
theorem tendsto_natCast_mul_gaussRareDigitWindow
    {lower upper : ℝ} (hlower : 0 < lower) (hupper : lower < upper) :
    Tendsto
      (fun L : ℕ ↦ (L : ℝ) * gaussMeasure.real
        (scaledGaussFirstDigitWindow (L : ℝ) lower upper))
      atTop (𝓝 ((upper - lower) / Real.log 2)) := by
  have hmain := tendsto_scaled_gaussFirstDigitBlock_floorCeil
    (fun L : ℕ ↦ (L : ℝ)) tendsto_natCast_atTop_atTop hlower hupper
  apply hmain.congr'
  filter_upwards [eventually_gt_atTop 0] with L hL
  rw [gaussFirstDigitBlock_floorCeil_eq_scaledWindow
    (by exact_mod_cast hL) hlower hupper]

/-- Removing the redundant initial-state restriction from a pure digit
tuple changes no Gauss mass. -/
theorem gaussMeasure_real_gaussDigitTupleEvent_eq_iInter
    {r : ℕ} (hr : 0 < r) (scale lower upper : ℝ)
    (times : Fin r → ℕ) :
    gaussMeasure.real (gaussDigitTupleEvent scale lower upper times) =
      gaussMeasure.real
        (⋂ i, (gaussOrbit (times i)) ⁻¹'
          scaledGaussFirstDigitWindow scale lower upper) := by
  let U : Set ℝ := Ioc (0 : ℝ) 1
  let H : Set ℝ := ⋂ i, (gaussOrbit (times i)) ⁻¹'
    scaledGaussFirstDigitWindow scale lower upper
  have hset : gaussDigitTupleEvent scale lower upper times = U ∩ H := by
    ext x
    simp only [gaussDigitTupleEvent, mem_orderedEventIntersection_ofFn_iff,
      gaussDigitWindowAt, mem_inter_iff, Set.mem_preimage, U, H, mem_iInter]
    constructor
    · intro h
      exact ⟨(h ⟨0, hr⟩).1, fun i ↦ (h i).2⟩
    · rintro ⟨hxU, hxH⟩ i
      exact ⟨hxU, hxH i⟩
  rw [hset]
  apply measureReal_congr
  filter_upwards [gaussMeasure_unit_ae] with x hx
  change ((x ∈ Ioc (0 : ℝ) 1) ∧ x ∈ H) = (x ∈ H)
  apply propext
  exact and_iff_right hx

/-- Uniform gap-one quasi-Bernoulli bound for a digit tuple, with the
explicit constant coming from the proved exponential rate. -/
theorem gaussMeasure_real_gaussDigitTupleEvent_le
    {r : ℕ} (hr : 0 < r) {scale lower upper : ℝ}
    (times : Fin r → ℕ)
    (hchronological : ∀ i k, i < k → times i + 1 ≤ times k) :
    gaussMeasure.real (gaussDigitTupleEvent scale lower upper times) ≤
      7 ^ (r - 1) *
        gaussMeasure.real
          (scaledGaussFirstDigitWindow scale lower upper) ^ r := by
  rw [gaussMeasure_real_gaussDigitTupleEvent_eq_iInter hr]
  have hmix := GaussDigitPsiMixing.measure_orderedIntersection_le
    gaussDigitPsiMixing_exponential hr times
    (fun _ : Fin r ↦ scaledGaussFirstDigitWindow scale lower upper) 1
    (fun _ ↦ measurableSet_scaledGaussFirstDigitWindow _ _ _)
    (fun _ ↦ isGaussOneDigitEvent_scaledGaussFirstDigitWindow _ _ _)
    (by norm_num) hchronological
    (gaussDigitExponentialRate_nonnegative 1)
  rw [orderedEventIntersection_ofFn] at hmix
  norm_num [gaussDigitExponentialRate] at hmix ⊢
  exact hmix

/-- Long-gap relative product estimate, again with no assumed mixing
interface. -/
theorem abs_gaussMeasure_real_gaussDigitTupleEvent_sub_pow_le
    {r : ℕ} (hr : 0 < r) {scale lower upper : ℝ}
    (times : Fin r → ℕ) (gap : ℕ) (hgap0 : 0 < gap)
    (hseparated : ∀ i k, i < k → times i + gap ≤ times k) :
    |gaussMeasure.real (gaussDigitTupleEvent scale lower upper times) -
        gaussMeasure.real
          (scaledGaussFirstDigitWindow scale lower upper) ^ r| ≤
      ((1 + gaussDigitExponentialRate gap) ^ (r - 1) - 1) *
        gaussMeasure.real
          (scaledGaussFirstDigitWindow scale lower upper) ^ r := by
  rw [gaussMeasure_real_gaussDigitTupleEvent_eq_iInter hr]
  have hmix := gaussMeasureReal_iInter_oneDigitEvents_factorization_error_le
    hr times (fun _ : Fin r ↦
      scaledGaussFirstDigitWindow scale lower upper) gap
    (fun _ ↦ measurableSet_scaledGaussFirstDigitWindow _ _ _)
    (fun _ ↦ isGaussOneDigitEvent_scaledGaussFirstDigitWindow _ _ _)
    hgap0 hseparated
  simpa using! hmix

/-! ## Deterministic short/long decomposition -/

/-- Tuples whose successive chronological gaps are all at least `gap`. -/
def separatedTupleFamily {r L : ℕ} (gap : ℕ)
    (tuples : Finset (Fin r → Fin L)) : Finset (Fin r → Fin L) := by
  classical
  exact tuples.filter (IsSeparatedTuple gap)

/-- Complementary family of tuples having at least one short gap. -/
def shortTupleFamily {r L : ℕ} (gap : ℕ)
    (tuples : Finset (Fin r → Fin L)) : Finset (Fin r → Fin L) := by
  classical
  exact tuples.filter (fun t ↦ ¬ IsSeparatedTuple gap t)

@[simp] theorem mem_separatedTupleFamily_iff
    {r L : ℕ} {gap : ℕ} {tuples : Finset (Fin r → Fin L)}
    {t : Fin r → Fin L} :
    t ∈ separatedTupleFamily gap tuples ↔
      t ∈ tuples ∧ IsSeparatedTuple gap t := by
  classical
  simp [separatedTupleFamily]

@[simp] theorem mem_shortTupleFamily_iff
    {r L : ℕ} {gap : ℕ} {tuples : Finset (Fin r → Fin L)}
    {t : Fin r → Fin L} :
    t ∈ shortTupleFamily gap tuples ↔
      t ∈ tuples ∧ ¬ IsSeparatedTuple gap t := by
  classical
  simp [shortTupleFamily]

theorem gaussDigitTupleSum_eq_short_add_separated
    {r L : ℕ} (gap : ℕ) (lower upper : ℝ)
    (tuples : Finset (Fin r → Fin L)) :
    gaussDigitTupleSum lower upper tuples =
      gaussDigitTupleSum lower upper (shortTupleFamily gap tuples) +
        gaussDigitTupleSum lower upper (separatedTupleFamily gap tuples) := by
  classical
  unfold gaussDigitTupleSum shortTupleFamily separatedTupleFamily
  simpa [add_comm] using!
    (Finset.sum_filter_add_sum_filter_not tuples
      (IsSeparatedTuple gap)
      (fun t ↦ gaussMeasure.real
        (gaussDigitTupleEvent (L : ℝ) lower upper
          (fun i ↦ (t i).1)))).symm

/-- Every short tuple has the uniform gap-one rare-event bound. -/
theorem gaussDigitTupleSum_short_le
    {r L gap : ℕ} (hr : 0 < r) {lower upper : ℝ}
    (tuples : Finset (Fin r → Fin L))
    (hchronological : ∀ t ∈ tuples, IsChronologicalTuple t) :
    gaussDigitTupleSum lower upper (shortTupleFamily gap tuples) ≤
      ((shortTupleFamily gap tuples).card : ℝ) *
        (7 ^ (r - 1) *
          gaussMeasure.real
            (scaledGaussFirstDigitWindow (L : ℝ) lower upper) ^ r) := by
  classical
  unfold gaussDigitTupleSum
  calc
    (∑ t ∈ shortTupleFamily gap tuples,
        gaussMeasure.real
          (gaussDigitTupleEvent (L : ℝ) lower upper
            (fun i ↦ (t i).1))) ≤
        ∑ _t ∈ shortTupleFamily gap tuples,
          (7 ^ (r - 1) *
            gaussMeasure.real
              (scaledGaussFirstDigitWindow (L : ℝ) lower upper) ^ r) := by
      apply Finset.sum_le_sum
      intro t ht
      exact gaussMeasure_real_gaussDigitTupleEvent_le hr _
        (hchronological t (mem_shortTupleFamily_iff.mp ht).1)
    _ = ((shortTupleFamily gap tuples).card : ℝ) *
          (7 ^ (r - 1) *
            gaussMeasure.real
              (scaledGaussFirstDigitWindow (L : ℝ) lower upper) ^ r) := by
      simp

/-- Aggregate product error on the long-gap family. -/
theorem abs_gaussDigitTupleSum_separated_sub_product_le
    {r L gap : ℕ} (hr : 0 < r) (hgap0 : 0 < gap)
    {lower upper : ℝ} (tuples : Finset (Fin r → Fin L)) :
    |gaussDigitTupleSum lower upper (separatedTupleFamily gap tuples) -
        ((separatedTupleFamily gap tuples).card : ℝ) *
          gaussMeasure.real
            (scaledGaussFirstDigitWindow (L : ℝ) lower upper) ^ r| ≤
      ((separatedTupleFamily gap tuples).card : ℝ) *
        (((1 + gaussDigitExponentialRate gap) ^ (r - 1) - 1) *
          gaussMeasure.real
            (scaledGaussFirstDigitWindow (L : ℝ) lower upper) ^ r) := by
  classical
  let p : ℝ := gaussMeasure.real
    (scaledGaussFirstDigitWindow (L : ℝ) lower upper)
  let q : ℝ := (1 + gaussDigitExponentialRate gap) ^ (r - 1) - 1
  have hrearrange :
      gaussDigitTupleSum lower upper (separatedTupleFamily gap tuples) -
          ((separatedTupleFamily gap tuples).card : ℝ) * p ^ r =
        ∑ t ∈ separatedTupleFamily gap tuples,
          (gaussMeasure.real
              (gaussDigitTupleEvent (L : ℝ) lower upper
                (fun i ↦ (t i).1)) - p ^ r) := by
    unfold gaussDigitTupleSum
    simp
  rw [hrearrange]
  calc
    |∑ t ∈ separatedTupleFamily gap tuples,
        (gaussMeasure.real
            (gaussDigitTupleEvent (L : ℝ) lower upper
              (fun i ↦ (t i).1)) - p ^ r)| ≤
        ∑ t ∈ separatedTupleFamily gap tuples,
          |gaussMeasure.real
              (gaussDigitTupleEvent (L : ℝ) lower upper
                (fun i ↦ (t i).1)) - p ^ r| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _t ∈ separatedTupleFamily gap tuples, q * p ^ r := by
      apply Finset.sum_le_sum
      intro t ht
      exact abs_gaussMeasure_real_gaussDigitTupleEvent_sub_pow_le
        hr _ gap hgap0 (mem_separatedTupleFamily_iff.mp ht).2
    _ = ((separatedTupleFamily gap tuples).card : ℝ) *
          (q * p ^ r) := by simp

/-- Aggregate product error on the complementary short-gap family. -/
theorem abs_gaussDigitTupleSum_short_sub_product_le
    {r L gap : ℕ} (hr : 0 < r) {lower upper : ℝ}
    (tuples : Finset (Fin r → Fin L))
    (hchronological : ∀ t ∈ tuples, IsChronologicalTuple t) :
    |gaussDigitTupleSum lower upper (shortTupleFamily gap tuples) -
        ((shortTupleFamily gap tuples).card : ℝ) *
          gaussMeasure.real
            (scaledGaussFirstDigitWindow (L : ℝ) lower upper) ^ r| ≤
      ((shortTupleFamily gap tuples).card : ℝ) *
        ((7 ^ (r - 1) + 1) *
          gaussMeasure.real
            (scaledGaussFirstDigitWindow (L : ℝ) lower upper) ^ r) := by
  classical
  let p : ℝ := gaussMeasure.real
    (scaledGaussFirstDigitWindow (L : ℝ) lower upper)
  have hp0 : 0 ≤ p ^ r := pow_nonneg measureReal_nonneg _
  have hrearrange :
      gaussDigitTupleSum lower upper (shortTupleFamily gap tuples) -
          ((shortTupleFamily gap tuples).card : ℝ) * p ^ r =
        ∑ t ∈ shortTupleFamily gap tuples,
          (gaussMeasure.real
              (gaussDigitTupleEvent (L : ℝ) lower upper
                (fun i ↦ (t i).1)) - p ^ r) := by
    unfold gaussDigitTupleSum
    simp
  rw [hrearrange]
  calc
    |∑ t ∈ shortTupleFamily gap tuples,
        (gaussMeasure.real
            (gaussDigitTupleEvent (L : ℝ) lower upper
              (fun i ↦ (t i).1)) - p ^ r)| ≤
        ∑ t ∈ shortTupleFamily gap tuples,
          |gaussMeasure.real
              (gaussDigitTupleEvent (L : ℝ) lower upper
                (fun i ↦ (t i).1)) - p ^ r| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _t ∈ shortTupleFamily gap tuples,
        ((7 ^ (r - 1) + 1) * p ^ r) := by
      apply Finset.sum_le_sum
      intro t ht
      calc
        |gaussMeasure.real
            (gaussDigitTupleEvent (L : ℝ) lower upper
              (fun i ↦ (t i).1)) - p ^ r| ≤
            |gaussMeasure.real
              (gaussDigitTupleEvent (L : ℝ) lower upper
                (fun i ↦ (t i).1))| + |p ^ r| := abs_sub _ _
        _ = gaussMeasure.real
              (gaussDigitTupleEvent (L : ℝ) lower upper
                (fun i ↦ (t i).1)) + p ^ r := by
          rw [abs_of_nonneg measureReal_nonneg, abs_of_nonneg hp0]
        _ ≤ 7 ^ (r - 1) * p ^ r + p ^ r := by
          gcongr
          exact gaussMeasure_real_gaussDigitTupleEvent_le hr _
            (hchronological t (mem_shortTupleFamily_iff.mp ht).1)
        _ = (7 ^ (r - 1) + 1) * p ^ r := by ring
    _ = ((shortTupleFamily gap tuples).card : ℝ) *
          ((7 ^ (r - 1) + 1) * p ^ r) := by simp

theorem card_shortTupleFamily_add_card_separatedTupleFamily
    {r L gap : ℕ} (tuples : Finset (Fin r → Fin L)) :
    (shortTupleFamily gap tuples).card +
        (separatedTupleFamily gap tuples).card = tuples.card := by
  classical
  simpa [shortTupleFamily, separatedTupleFamily, add_comm] using!
    (Finset.card_filter_add_card_filter_not
      (s := tuples) (IsSeparatedTuple gap))

/-! ## Factorial-scale limits -/

/-- Turning a deterministic tuple-cardinality density into the corresponding
independent rare-event mass.  The equality is only rearranged for positive
`L`; the finitely many initial indices play no role in the limit. -/
theorem tendsto_card_mul_gaussRareDigitWindow_pow_of_density
    {r : ℕ} {lower upper density : ℝ}
    (hlower : 0 < lower) (hupper : lower < upper)
    (family : ∀ L : ℕ, Finset (Fin r → Fin L))
    (hdensity : Tendsto
      (fun L : ℕ ↦ ((family L).card : ℝ) / (L : ℝ) ^ r)
      atTop (𝓝 density)) :
    Tendsto
      (fun L : ℕ ↦ ((family L).card : ℝ) *
        gaussMeasure.real
          (scaledGaussFirstDigitWindow (L : ℝ) lower upper) ^ r)
      atTop (𝓝 (density * ((upper - lower) / Real.log 2) ^ r)) := by
  have hp := tendsto_natCast_mul_gaussRareDigitWindow hlower hupper
  have hproduct := hdensity.mul (hp.pow r)
  apply hproduct.congr'
  filter_upwards [eventually_gt_atTop 0] with L hL
  have hLne : (L : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hL)
  field_simp [hLne]
  ring

/-- The explicit exponential mixing factor tends to zero along every
deterministic gap tending to infinity. -/
theorem tendsto_gaussDigitRelativeMixingFactor
    {r : ℕ} {gap : ℕ → ℕ} (hgap : Tendsto gap atTop atTop) :
    Tendsto
      (fun L : ℕ ↦
        (1 + gaussDigitExponentialRate (gap L)) ^ (r - 1) - 1)
      atTop (𝓝 0) := by
  have hrate := tendsto_gaussDigitExponentialRate.comp hgap
  have hone : Tendsto
      (fun L : ℕ ↦ 1 + gaussDigitExponentialRate (gap L))
      atTop (𝓝 1) := by
    simpa only [add_zero] using! tendsto_const_nhds.add hrate
  have honeConst : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (𝓝 1) :=
    tendsto_const_nhds
  have hpow := (hone.pow (r - 1)).sub honeConst
  simpa using! hpow

/-- Removing a short-gap subfamily of density `o(L^r)` costs `o(1)` in
digit factorial mass. -/
theorem tendsto_gaussDigitTupleSum_short_zero
    {r : ℕ} (hr : 0 < r) {lower upper : ℝ}
    (hlower : 0 < lower) (hupper : lower < upper)
    (gap : ℕ → ℕ)
    (tuples : ∀ L : ℕ, Finset (Fin r → Fin L))
    (hchronological : ∀ L, ∀ t ∈ tuples L, IsChronologicalTuple t)
    (hshortDensity : Tendsto
      (fun L : ℕ ↦
        ((shortTupleFamily (gap L) (tuples L)).card : ℝ) /
          (L : ℝ) ^ r)
      atTop (𝓝 0)) :
    Tendsto
      (fun L : ℕ ↦ gaussDigitTupleSum lower upper
        (shortTupleFamily (gap L) (tuples L)))
      atTop (𝓝 0) := by
  let short : ∀ L : ℕ, Finset (Fin r → Fin L) :=
    fun L ↦ shortTupleFamily (gap L) (tuples L)
  have hweight :=
    tendsto_card_mul_gaussRareDigitWindow_pow_of_density
      (r := r) hlower hupper short (by simpa only [short] using! hshortDensity)
  have hweight0 : Tendsto
      (fun L : ℕ ↦ ((short L).card : ℝ) *
        gaussMeasure.real
          (scaledGaussFirstDigitWindow (L : ℝ) lower upper) ^ r)
      atTop (𝓝 0) := by
    simpa only [zero_mul] using! hweight
  let C : ℝ := 7 ^ (r - 1)
  have hupper : Tendsto
      (fun L : ℕ ↦ ((short L).card : ℝ) *
        (C * gaussMeasure.real
          (scaledGaussFirstDigitWindow (L : ℝ) lower upper) ^ r))
      atTop (𝓝 0) := by
    have hC : Tendsto (fun _ : ℕ ↦ C) atTop (𝓝 C) := tendsto_const_nhds
    have hraw := hC.mul hweight0
    have heq :
        (fun L : ℕ ↦ C * (((short L).card : ℝ) *
          gaussMeasure.real
            (scaledGaussFirstDigitWindow (L : ℝ) lower upper) ^ r)) =ᶠ[atTop]
        (fun L : ℕ ↦ ((short L).card : ℝ) *
          (C * gaussMeasure.real
            (scaledGaussFirstDigitWindow (L : ℝ) lower upper) ^ r)) := by
      filter_upwards with L
      ring
    have htarget := hraw.congr' heq
    simpa only [mul_zero] using! htarget
  apply squeeze_zero'
  · filter_upwards with L
    exact Finset.sum_nonneg fun _ _ ↦ measureReal_nonneg
  · filter_upwards with L
    simpa only [short, C] using!
      gaussDigitTupleSum_short_le hr (tuples L) (hchronological L)
  · exact hupper

/-- The normalized density of the separated family is the total density
minus the negligible short-gap density. -/
theorem tendsto_separatedTupleFamily_density
    {r : ℕ} {density : ℝ} (gap : ℕ → ℕ)
    (tuples : ∀ L : ℕ, Finset (Fin r → Fin L))
    (htotalDensity : Tendsto
      (fun L : ℕ ↦ ((tuples L).card : ℝ) / (L : ℝ) ^ r)
      atTop (𝓝 density))
    (hshortDensity : Tendsto
      (fun L : ℕ ↦
        ((shortTupleFamily (gap L) (tuples L)).card : ℝ) /
          (L : ℝ) ^ r)
      atTop (𝓝 0)) :
    Tendsto
      (fun L : ℕ ↦
        ((separatedTupleFamily (gap L) (tuples L)).card : ℝ) /
          (L : ℝ) ^ r)
      atTop (𝓝 density) := by
  have hdiff := htotalDensity.sub hshortDensity
  have heq :
      (fun L : ℕ ↦ ((tuples L).card : ℝ) / (L : ℝ) ^ r -
        ((shortTupleFamily (gap L) (tuples L)).card : ℝ) /
          (L : ℝ) ^ r) =ᶠ[atTop]
      (fun L : ℕ ↦
        ((separatedTupleFamily (gap L) (tuples L)).card : ℝ) /
          (L : ℝ) ^ r) := by
    filter_upwards with L
    rw [← card_shortTupleFamily_add_card_separatedTupleFamily
      (gap := gap L) (tuples L)]
    push_cast
    ring
  have htarget := hdiff.congr' heq
  simpa only [sub_zero] using! htarget

/-- On long-gap tuples, exponential digit mixing makes the aggregate
joint-product error `o(1)`. -/
theorem tendsto_gaussDigitTupleSum_separated_sub_product_zero
    {r : ℕ} (hr : 0 < r) {lower upper density : ℝ}
    (hlower : 0 < lower) (hupper : lower < upper)
    (gap : ℕ → ℕ) (hgapTop : Tendsto gap atTop atTop)
    (hgapPos : ∀ᶠ L : ℕ in atTop, 0 < gap L)
    (tuples : ∀ L : ℕ, Finset (Fin r → Fin L))
    (htotalDensity : Tendsto
      (fun L : ℕ ↦ ((tuples L).card : ℝ) / (L : ℝ) ^ r)
      atTop (𝓝 density))
    (hshortDensity : Tendsto
      (fun L : ℕ ↦
        ((shortTupleFamily (gap L) (tuples L)).card : ℝ) /
          (L : ℝ) ^ r)
      atTop (𝓝 0)) :
    Tendsto
      (fun L : ℕ ↦
        gaussDigitTupleSum lower upper
            (separatedTupleFamily (gap L) (tuples L)) -
          ((separatedTupleFamily (gap L) (tuples L)).card : ℝ) *
            gaussMeasure.real
              (scaledGaussFirstDigitWindow (L : ℝ) lower upper) ^ r)
      atTop (𝓝 0) := by
  let separated : ∀ L : ℕ, Finset (Fin r → Fin L) :=
    fun L ↦ separatedTupleFamily (gap L) (tuples L)
  have hseparatedDensity := tendsto_separatedTupleFamily_density
    gap tuples htotalDensity hshortDensity
  have hp := tendsto_natCast_mul_gaussRareDigitWindow hlower hupper
  have hmix := tendsto_gaussDigitRelativeMixingFactor (r := r) hgapTop
  have hupperRaw := hseparatedDensity.mul (hmix.mul (hp.pow r))
  have hupper : Tendsto
      (fun L : ℕ ↦ ((separated L).card : ℝ) *
        (((1 + gaussDigitExponentialRate (gap L)) ^ (r - 1) - 1) *
          gaussMeasure.real
            (scaledGaussFirstDigitWindow (L : ℝ) lower upper) ^ r))
      atTop (𝓝 0) := by
    have hzero : density *
        (0 * ((upper - lower) / Real.log 2) ^ r) = 0 := by ring
    rw [hzero] at hupperRaw
    apply hupperRaw.congr'
    filter_upwards [eventually_gt_atTop 0] with L hL
    have hLne : (L : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hL)
    dsimp only [separated]
    field_simp [hLne]
    ring
  rw [tendsto_zero_iff_abs_tendsto_zero]
  apply squeeze_zero'
  · filter_upwards with L
    exact abs_nonneg _
  · filter_upwards [hgapPos] with L hgapL
    simpa only [separated] using!
      abs_gaussDigitTupleSum_separated_sub_product_le
        hr hgapL (tuples L)
  · exact hupper

/-- The separated digit sum has the independent-product limit. -/
theorem tendsto_gaussDigitTupleSum_separated
    {r : ℕ} (hr : 0 < r) {lower upper density : ℝ}
    (hlower : 0 < lower) (hupper : lower < upper)
    (gap : ℕ → ℕ) (hgapTop : Tendsto gap atTop atTop)
    (hgapPos : ∀ᶠ L : ℕ in atTop, 0 < gap L)
    (tuples : ∀ L : ℕ, Finset (Fin r → Fin L))
    (htotalDensity : Tendsto
      (fun L : ℕ ↦ ((tuples L).card : ℝ) / (L : ℝ) ^ r)
      atTop (𝓝 density))
    (hshortDensity : Tendsto
      (fun L : ℕ ↦
        ((shortTupleFamily (gap L) (tuples L)).card : ℝ) /
          (L : ℝ) ^ r)
      atTop (𝓝 0)) :
    Tendsto
      (fun L : ℕ ↦ gaussDigitTupleSum lower upper
        (separatedTupleFamily (gap L) (tuples L)))
      atTop
      (𝓝 (density * ((upper - lower) / Real.log 2) ^ r)) := by
  have herr :=
    tendsto_gaussDigitTupleSum_separated_sub_product_zero
      hr hlower hupper gap hgapTop hgapPos tuples htotalDensity hshortDensity
  have hseparatedDensity := tendsto_separatedTupleFamily_density
    gap tuples htotalDensity hshortDensity
  have hproduct :=
    tendsto_card_mul_gaussRareDigitWindow_pow_of_density
      (r := r) hlower hupper
      (fun L ↦ separatedTupleFamily (gap L) (tuples L))
      hseparatedDensity
  have hadd := herr.add hproduct
  have heq :
      (fun L : ℕ ↦
        (gaussDigitTupleSum lower upper
            (separatedTupleFamily (gap L) (tuples L)) -
          ((separatedTupleFamily (gap L) (tuples L)).card : ℝ) *
            gaussMeasure.real
              (scaledGaussFirstDigitWindow (L : ℝ) lower upper) ^ r) +
          ((separatedTupleFamily (gap L) (tuples L)).card : ℝ) *
            gaussMeasure.real
              (scaledGaussFirstDigitWindow (L : ℝ) lower upper) ^ r) =ᶠ[atTop]
      (fun L : ℕ ↦ gaussDigitTupleSum lower upper
        (separatedTupleFamily (gap L) (tuples L))) := by
    filter_upwards with L
    ring
  have htarget := hadd.congr' heq
  simpa only [zero_add] using! htarget

/-- Unmarked digit factorial limit for every deterministic chronological
tuple family with a limiting density and a negligible short-gap density. -/
theorem tendsto_gaussDigitTupleSum
    {r : ℕ} (hr : 0 < r) {lower upper density : ℝ}
    (hlower : 0 < lower) (hupper : lower < upper)
    (gap : ℕ → ℕ) (hgapTop : Tendsto gap atTop atTop)
    (hgapPos : ∀ᶠ L : ℕ in atTop, 0 < gap L)
    (tuples : ∀ L : ℕ, Finset (Fin r → Fin L))
    (hchronological : ∀ L, ∀ t ∈ tuples L, IsChronologicalTuple t)
    (htotalDensity : Tendsto
      (fun L : ℕ ↦ ((tuples L).card : ℝ) / (L : ℝ) ^ r)
      atTop (𝓝 density))
    (hshortDensity : Tendsto
      (fun L : ℕ ↦
        ((shortTupleFamily (gap L) (tuples L)).card : ℝ) /
          (L : ℝ) ^ r)
      atTop (𝓝 0)) :
    Tendsto
      (fun L : ℕ ↦ gaussDigitTupleSum lower upper (tuples L))
      atTop
      (𝓝 (density * ((upper - lower) / Real.log 2) ^ r)) := by
  have hshort := tendsto_gaussDigitTupleSum_short_zero
    hr hlower hupper gap tuples hchronological hshortDensity
  have hseparated := tendsto_gaussDigitTupleSum_separated
    hr hlower hupper gap hgapTop hgapPos tuples htotalDensity hshortDensity
  have hadd := hshort.add hseparated
  have heq :
      (fun L : ℕ ↦
        gaussDigitTupleSum lower upper
            (shortTupleFamily (gap L) (tuples L)) +
          gaussDigitTupleSum lower upper
            (separatedTupleFamily (gap L) (tuples L))) =ᶠ[atTop]
      (fun L : ℕ ↦ gaussDigitTupleSum lower upper (tuples L)) := by
    filter_upwards with L
    exact (gaussDigitTupleSum_eq_short_add_separated
      (gap L) lower upper (tuples L)).symm
  have htarget := hadd.congr' heq
  simpa only [zero_add] using! htarget

/-- Final exact-`θ` unmarked factorial limit.  All stochastic input has been
discharged by the proved exponential Gauss-digit mixing theorem; the only
hypotheses left are deterministic tuple counting statements. -/
theorem tendsto_gaussApproximationTupleSum
    {r : ℕ} (hr : 0 < r) {lower upper density : ℝ}
    (hlower : 0 < lower) (hupper : lower < upper)
    (gap : ℕ → ℕ) (hgapTop : Tendsto gap atTop atTop)
    (hgapPos : ∀ᶠ L : ℕ in atTop, 0 < gap L)
    (tuples : ∀ L : ℕ, Finset (Fin r → Fin L))
    (hchronological : ∀ L, ∀ t ∈ tuples L, IsChronologicalTuple t)
    (htotalDensity : Tendsto
      (fun L : ℕ ↦ ((tuples L).card : ℝ) / (L : ℝ) ^ r)
      atTop (𝓝 density))
    (hshortDensity : Tendsto
      (fun L : ℕ ↦
        ((shortTupleFamily (gap L) (tuples L)).card : ℝ) /
          (L : ℝ) ^ r)
      atTop (𝓝 0)) :
    Tendsto
      (fun L : ℕ ↦ gaussApproximationTupleSum lower upper (tuples L))
      atTop
      (𝓝 (density * ((upper - lower) / Real.log 2) ^ r)) := by
  have hreplacement :=
    tendsto_gaussApproximationTupleSum_sub_gaussDigitTupleSum_zero
      hr hlower hupper tuples hchronological
  have hdigit := tendsto_gaussDigitTupleSum
    hr hlower hupper gap hgapTop hgapPos tuples hchronological
      htotalDensity hshortDensity
  have hadd := hreplacement.add hdigit
  have heq :
      (fun L : ℕ ↦
        (gaussApproximationTupleSum lower upper (tuples L) -
          gaussDigitTupleSum lower upper (tuples L)) +
            gaussDigitTupleSum lower upper (tuples L)) =ᶠ[atTop]
      (fun L : ℕ ↦ gaussApproximationTupleSum lower upper (tuples L)) := by
    filter_upwards with L
    ring
  have htarget := hadd.congr' heq
  simpa only [zero_add] using! htarget

/-- Every exact tuple factorial sum covered by the preceding theorem is
uniformly bounded at the fixed order `r`.  This is the precise uniform
factorial-moment input used for uniform integrability. -/
theorem exists_uniform_gaussApproximationTupleSum_bound
    {r : ℕ} (hr : 0 < r) {lower upper density : ℝ}
    (hlower : 0 < lower) (hupper : lower < upper)
    (gap : ℕ → ℕ) (hgapTop : Tendsto gap atTop atTop)
    (hgapPos : ∀ᶠ L : ℕ in atTop, 0 < gap L)
    (tuples : ∀ L : ℕ, Finset (Fin r → Fin L))
    (hchronological : ∀ L, ∀ t ∈ tuples L, IsChronologicalTuple t)
    (htotalDensity : Tendsto
      (fun L : ℕ ↦ ((tuples L).card : ℝ) / (L : ℝ) ^ r)
      atTop (𝓝 density))
    (hshortDensity : Tendsto
      (fun L : ℕ ↦
        ((shortTupleFamily (gap L) (tuples L)).card : ℝ) /
          (L : ℝ) ^ r)
      atTop (𝓝 0)) :
    ∃ C : ℝ, ∀ L : ℕ,
      |gaussApproximationTupleSum lower upper (tuples L)| ≤ C := by
  have hlimit := tendsto_gaussApproximationTupleSum
    hr hlower hupper gap hgapTop hgapPos tuples hchronological
      htotalDensity hshortDensity
  have hbounded := Metric.isBounded_range_of_tendsto
    (fun L : ℕ ↦ gaussApproximationTupleSum lower upper (tuples L)) hlimit
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp hbounded
  refine ⟨C, fun L ↦ ?_⟩
  simpa only [Real.norm_eq_abs] using! hC _ ⟨L, rfl⟩

/-! ## Parity-restricted deterministic index boxes -/

/-- Chronologically ordered tuples selected from labeled deterministic index
boxes, with one prescribed parity in each coordinate.  This is the literal
finite family occurring after a labeled factorial rectangle is split into
its possible chronological orders. -/
def chronologicalParityBoxTuples {r L : ℕ}
    (parity : Fin r → Fin 2) (boxes : Fin r → Finset (Fin L)) :
    Finset (Fin r → Fin L) := by
  classical
  exact Finset.univ.filter fun t ↦
    IsChronologicalTuple t ∧
      ∀ i, t i ∈ boxes i ∧ (t i).1 % 2 = (parity i).1

@[simp] theorem mem_chronologicalParityBoxTuples_iff
    {r L : ℕ} {parity : Fin r → Fin 2}
    {boxes : Fin r → Finset (Fin L)} {t : Fin r → Fin L} :
    t ∈ chronologicalParityBoxTuples parity boxes ↔
      IsChronologicalTuple t ∧
        ∀ i, t i ∈ boxes i ∧ (t i).1 % 2 = (parity i).1 := by
  classical
  simp [chronologicalParityBoxTuples]

theorem chronologicalParityBoxTuples_isChronological
    {r L : ℕ} (parity : Fin r → Fin 2)
    (boxes : Fin r → Finset (Fin L))
    (t : Fin r → Fin L) (ht : t ∈ chronologicalParityBoxTuples parity boxes) :
    IsChronologicalTuple t :=
  (mem_chronologicalParityBoxTuples_iff.mp ht).1

/-- Paper-facing unmarked factorial theorem for parity-restricted labeled
index boxes.  The two cardinal-density hypotheses are deterministic: the
first is the Riemann-count limit of the boxes, and the second is the usual
`O(gap * L^(r-1)) = o(L^r)` short-gap count.  Exponential Gauss mixing,
one-point rare-digit asymptotics, and exact-`θ` replacement are all already
discharged internally.

The conjunction records both the exact factorial limit and its fixed-order
uniform bound, so downstream uniform-integrability arguments do not need to
repeat the analytic proof. -/
theorem gaussApproximationTupleSum_chronologicalParityBoxes_limit_and_bound
    {r : ℕ} (hr : 0 < r) {lower upper density : ℝ}
    (hlower : 0 < lower) (hupper : lower < upper)
    (parity : Fin r → Fin 2)
    (boxes : ∀ L : ℕ, Fin r → Finset (Fin L))
    (gap : ℕ → ℕ) (hgapTop : Tendsto gap atTop atTop)
    (hgapPos : ∀ᶠ L : ℕ in atTop, 0 < gap L)
    (htotalDensity : Tendsto
      (fun L : ℕ ↦
        ((chronologicalParityBoxTuples parity (boxes L)).card : ℝ) /
          (L : ℝ) ^ r)
      atTop (𝓝 density))
    (hshortDensity : Tendsto
      (fun L : ℕ ↦
        ((shortTupleFamily (gap L)
            (chronologicalParityBoxTuples parity (boxes L))).card : ℝ) /
          (L : ℝ) ^ r)
      atTop (𝓝 0)) :
    Tendsto
        (fun L : ℕ ↦ gaussApproximationTupleSum lower upper
          (chronologicalParityBoxTuples parity (boxes L)))
        atTop
        (𝓝 (density * ((upper - lower) / Real.log 2) ^ r)) ∧
      ∃ C : ℝ, ∀ L : ℕ,
        |gaussApproximationTupleSum lower upper
          (chronologicalParityBoxTuples parity (boxes L))| ≤ C := by
  let tuples : ∀ L : ℕ, Finset (Fin r → Fin L) :=
    fun L ↦ chronologicalParityBoxTuples parity (boxes L)
  have hchronological : ∀ L, ∀ t ∈ tuples L, IsChronologicalTuple t := by
    intro L t ht
    exact chronologicalParityBoxTuples_isChronological parity (boxes L) t ht
  constructor
  · exact tendsto_gaussApproximationTupleSum
      hr hlower hupper gap hgapTop hgapPos tuples hchronological
        (by simpa only [tuples] using! htotalDensity)
        (by simpa only [tuples] using! hshortDensity)
  · exact exists_uniform_gaussApproximationTupleSum_bound
      hr hlower hupper gap hgapTop hgapPos tuples hchronological
        (by simpa only [tuples] using! htotalDensity)
        (by simpa only [tuples] using! hshortDensity)

end

end Erdos1002
