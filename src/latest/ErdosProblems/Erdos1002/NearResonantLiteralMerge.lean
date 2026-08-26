import ErdosProblems.Erdos1002.NearResonantZeroCarrierParameters
import ErdosProblems.Erdos1002.NearResonantSmallDenominators

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Exact merge of the smooth near carrier and the literal hard cutoff

The smooth cutoff cannot be compared with a sharp sub-sum merely by set
containment, because deleting summands may destroy cancellation.  This file
therefore records an exact pointwise decomposition.  The hard near sum is
the smooth Bernoulli shot minus two explicitly defined transition sums:
the lower smoothing layer and the outer fixed-away layer.
-/

open Filter MeasureTheory Set Finset
open scoped BigOperators ComplexConjugate ENNReal Real

namespace Erdos1002

noncomputable section

/-! ## Pointwise carrier reconstruction -/

/-- On the open fundamental interval the absolutely convergent Bernoulli
carrier series is exactly the literal smooth primitive shot tail. -/
theorem tsum_smoothNearPrimitivePoleCarrierTail_eq_literal
    (N : ℕ) (a ε : ℝ) (Q U : ℕ) (alpha : ℝ)
    (hQ : 1 ≤ Q) (ha : 0 < a) (hε : 0 < ε)
    (haε : a ≤ ε / 4) (hεhalf : ε ≤ 1 / 2)
    (halpha : alpha ∈ Set.Ioo (0 : ℝ) 1) :
    (∑' ell : ℤ,
        smoothNearPrimitivePoleCarrierTail N ell a ε Q U alpha) =
      smoothNearLiteralShotTail N a ε Q U alpha := by
  calc
    (∑' ell : ℤ,
        smoothNearPrimitivePoleCarrierTail N ell a ε Q U alpha) =
      smoothNearBernoulliShotTail N a ε Q U alpha :=
        tsum_smoothNearPrimitivePoleCarrierTail N a ε Q U alpha
    _ = smoothNearLiteralShotTail N a ε Q U alpha :=
      smoothNearBernoulliShotTail_eq_literal
        N a ε Q U alpha hQ ha hε haε hεhalf halpha

/-- The zero Bernoulli carrier is exactly `1/12` times the unmarked smooth
primitive pole tail. -/
theorem smoothNearPrimitivePoleCarrierTail_zero
    (N : ℕ) (a ε : ℝ) (Q U : ℕ) (alpha : ℝ) :
    smoothNearPrimitivePoleCarrierTail N 0 a ε Q U alpha =
      (1 / 12 : ℂ) * smoothNearPrimitivePoleTail a ε Q U alpha := by
  unfold smoothNearPrimitivePoleCarrierTail
    smoothNearPrimitivePoleCarrierTerm unitModulate
    nearBernoulliCarrierFrequency smoothNearPrimitivePoleTail
  simp [paperExp, bernoulliMarkFourierCoefficient, Finset.mul_sum]

/-! ## Literal hard near window for denominators `p>2` -/

def nearMinorLargeDenominatorTerm
    (N : ℕ) (A ε : ℝ) (p : ℕ) (alpha : ℝ) : ℂ :=
  if A < Real.log (N : ℝ) *
        |(p : ℝ) * resonanceDelta p alpha| ∧
      |(p : ℝ) * resonanceDelta p alpha| ≤ ε / 4 then
    (primitiveShot N p alpha : ℂ)
  else 0

def nearMinorLargeDenominatorSum
    (N : ℕ) (A ε : ℝ) (alpha : ℝ) : ℂ :=
  ∑ p ∈ Finset.Ioc 2 N,
    nearMinorLargeDenominatorTerm N A ε p alpha

theorem measurable_nearMinorLargeDenominatorTerm
    (N p : ℕ) (A ε : ℝ) :
    Measurable (nearMinorLargeDenominatorTerm N A ε p) := by
  let x : ℝ → ℝ := fun alpha ↦
    |(p : ℝ) * resonanceDelta p alpha|
  have hx : Measurable x :=
    (measurable_const.mul (measurable_resonanceDelta p)).abs
  unfold nearMinorLargeDenominatorTerm
  apply Measurable.ite
  · exact (measurableSet_lt measurable_const (measurable_const.mul hx)).inter
      (measurableSet_le hx measurable_const)
  · exact (measurable_primitiveShot N p).complex_ofReal
  · exact measurable_const

theorem measurable_nearMinorLargeDenominatorSum
    (N : ℕ) (A ε : ℝ) :
    Measurable (nearMinorLargeDenominatorSum N A ε) := by
  unfold nearMinorLargeDenominatorSum
  exact Finset.measurable_fun_sum (Finset.Ioc 2 N) fun p _hp ↦
    measurable_nearMinorLargeDenominatorTerm N p A ε

/-- The literal hard near sum, with the two exceptional denominators kept
separate from the carrier tail.  This is the decomposition used by the
global estimate: `p=1,2` are treated directly and `p>2` by Fourier
carriers. -/
def nearMinorHardNearSum
    (N : ℕ) (A ε : ℝ) (alpha : ℝ) : ℂ :=
  nearMinorSmallDenominatorSum N A ε alpha +
    nearMinorLargeDenominatorSum N A ε alpha

theorem measurable_nearMinorHardNearSum
    (N : ℕ) (A ε : ℝ) :
    Measurable (nearMinorHardNearSum N A ε) := by
  exact (measurable_nearMinorSmallDenominatorSum N A ε).add
    (measurable_nearMinorLargeDenominatorSum N A ε)

/-- On the hard near window, the smooth term at inner scale `A/(2L)` is
exactly the literal primitive shot. -/
theorem nearMinorLargeDenominatorTerm_eq_smooth_of_window
    (N p : ℕ) (A ε alpha : ℝ)
    (hA : 0 < A) (hL : 0 < Real.log (N : ℝ)) (hε : 0 < ε)
    (hwindow : A < Real.log (N : ℝ) *
          |(p : ℝ) * resonanceDelta p alpha| ∧
        |(p : ℝ) * resonanceDelta p alpha| ≤ ε / 4) :
    nearMinorLargeDenominatorTerm N A ε p alpha =
      smoothNearLiteralShotTerm N p
        (A / (2 * Real.log (N : ℝ))) ε alpha := by
  let L : ℝ := Real.log (N : ℝ)
  let a : ℝ := A / (2 * L)
  have ha : 0 < a := by dsimp [a, L]; positivity
  have hdiv : A / L < |(p : ℝ) * resonanceDelta p alpha| := by
    apply (div_lt_iff₀ (by simpa only [L] using! hL)).2
    simpa only [mul_comm] using! hwindow.1
  have htwo : 2 * a ≤ |(p : ℝ) * resonanceDelta p alpha| := by
    have hscale : 2 * a = A / L := by
      dsimp [a]
      field_simp [hL.ne']
    rw [hscale]
    exact hdiv.le
  have hsmooth := smoothNearLiteralShotTerm_eq_primitiveShot_of_plateau
    N p a ε alpha ha hε htwo hwindow.2
  unfold nearMinorLargeDenominatorTerm
  rw [if_pos (by simpa only [L] using! hwindow)]
  simpa only [a, L] using! hsmooth.symm

/-! ## Exact transition decomposition -/

/-- The residual smooth contribution on the lower side of the fixed-away
split.  It is defined as a difference, not as a containing sharp band, so
the ensuing identity retains every cancellation exactly. -/
def nearMinorLowerTransitionTerm
    (N : ℕ) (A ε : ℝ) (p : ℕ) (alpha : ℝ) : ℂ :=
  if |(p : ℝ) * resonanceDelta p alpha| ≤ ε / 4 then
    smoothNearLiteralShotTerm N p
        (A / (2 * Real.log (N : ℝ))) ε alpha -
      nearMinorLargeDenominatorTerm N A ε p alpha
  else 0

/-- The residual smooth contribution above `ε/4`.  The cutoff itself
forces this term to vanish once the coordinate reaches `ε`. -/
def nearMinorUpperTransitionTerm
    (N : ℕ) (A ε : ℝ) (p : ℕ) (alpha : ℝ) : ℂ :=
  if ε / 4 < |(p : ℝ) * resonanceDelta p alpha| then
    smoothNearLiteralShotTerm N p
      (A / (2 * Real.log (N : ℝ))) ε alpha
  else 0

def nearMinorLowerTransitionSum
    (N : ℕ) (A ε : ℝ) (alpha : ℝ) : ℂ :=
  ∑ p ∈ Finset.Ioc 2 N,
    nearMinorLowerTransitionTerm N A ε p alpha

def nearMinorUpperTransitionSum
    (N : ℕ) (A ε : ℝ) (alpha : ℝ) : ℂ :=
  ∑ p ∈ Finset.Ioc 2 N,
    nearMinorUpperTransitionTerm N A ε p alpha

theorem measurable_nearMinorLowerTransitionTerm
    (N p : ℕ) (A ε : ℝ)
    (hA : 0 < A) (hL : 0 < Real.log (N : ℝ))
    (haε : A / (2 * Real.log (N : ℝ)) ≤ ε / 4) :
    Measurable (nearMinorLowerTransitionTerm N A ε p) := by
  let x : ℝ → ℝ := fun alpha ↦
    |(p : ℝ) * resonanceDelta p alpha|
  have hx : Measurable x :=
    (measurable_const.mul (measurable_resonanceDelta p)).abs
  have ha : 0 < A / (2 * Real.log (N : ℝ)) := by positivity
  unfold nearMinorLowerTransitionTerm
  apply Measurable.ite (measurableSet_le hx measurable_const)
  · exact (measurable_smoothNearLiteralShotTerm N p
      (A / (2 * Real.log (N : ℝ))) ε ha haε).sub
        (measurable_nearMinorLargeDenominatorTerm N p A ε)
  · exact measurable_const

theorem measurable_nearMinorUpperTransitionTerm
    (N p : ℕ) (A ε : ℝ)
    (hA : 0 < A) (hL : 0 < Real.log (N : ℝ))
    (haε : A / (2 * Real.log (N : ℝ)) ≤ ε / 4) :
    Measurable (nearMinorUpperTransitionTerm N A ε p) := by
  let x : ℝ → ℝ := fun alpha ↦
    |(p : ℝ) * resonanceDelta p alpha|
  have hx : Measurable x :=
    (measurable_const.mul (measurable_resonanceDelta p)).abs
  have ha : 0 < A / (2 * Real.log (N : ℝ)) := by positivity
  unfold nearMinorUpperTransitionTerm
  apply Measurable.ite (measurableSet_lt measurable_const hx)
  · exact measurable_smoothNearLiteralShotTerm N p
      (A / (2 * Real.log (N : ℝ))) ε ha haε
  · exact measurable_const

theorem measurable_nearMinorLowerTransitionSum
    (N : ℕ) (A ε : ℝ)
    (hA : 0 < A) (hL : 0 < Real.log (N : ℝ))
    (haε : A / (2 * Real.log (N : ℝ)) ≤ ε / 4) :
    Measurable (nearMinorLowerTransitionSum N A ε) := by
  unfold nearMinorLowerTransitionSum
  exact Finset.measurable_fun_sum (Finset.Ioc 2 N) fun p _hp ↦
    measurable_nearMinorLowerTransitionTerm N p A ε hA hL haε

theorem measurable_nearMinorUpperTransitionSum
    (N : ℕ) (A ε : ℝ)
    (hA : 0 < A) (hL : 0 < Real.log (N : ℝ))
    (haε : A / (2 * Real.log (N : ℝ)) ≤ ε / 4) :
    Measurable (nearMinorUpperTransitionSum N A ε) := by
  unfold nearMinorUpperTransitionSum
  exact Finset.measurable_fun_sum (Finset.Ioc 2 N) fun p _hp ↦
    measurable_nearMinorUpperTransitionTerm N p A ε hA hL haε

/-- Exact one-denominator identity, including both transition layers. -/
theorem smoothNearLiteralShotTerm_eq_hard_add_transitions
    (N p : ℕ) (A ε alpha : ℝ) :
    smoothNearLiteralShotTerm N p
        (A / (2 * Real.log (N : ℝ))) ε alpha =
      nearMinorLargeDenominatorTerm N A ε p alpha +
        nearMinorLowerTransitionTerm N A ε p alpha +
        nearMinorUpperTransitionTerm N A ε p alpha := by
  by_cases hquarter :
      |(p : ℝ) * resonanceDelta p alpha| ≤ ε / 4
  · have hnotUpper : ¬ ε / 4 <
        |(p : ℝ) * resonanceDelta p alpha| := not_lt.mpr hquarter
    simp only [nearMinorLowerTransitionTerm, nearMinorUpperTransitionTerm,
      if_pos hquarter, if_neg hnotUpper]
    ring
  · have hupper : ε / 4 <
        |(p : ℝ) * resonanceDelta p alpha| := lt_of_not_ge hquarter
    have hhard : ¬ (A < Real.log (N : ℝ) *
          |(p : ℝ) * resonanceDelta p alpha| ∧
        |(p : ℝ) * resonanceDelta p alpha| ≤ ε / 4) :=
      fun h ↦ hquarter h.2
    simp only [nearMinorLowerTransitionTerm, nearMinorUpperTransitionTerm,
      nearMinorLargeDenominatorTerm, if_neg hquarter, if_pos hupper,
      if_neg hhard, zero_add]

/-- Exact finite-sum identity for all denominators `2<p≤N`. -/
theorem smoothNearLiteralShotTail_eq_hard_add_transitions
    (N : ℕ) (A ε alpha : ℝ) :
    smoothNearLiteralShotTail N
        (A / (2 * Real.log (N : ℝ))) ε 2 N alpha =
      nearMinorLargeDenominatorSum N A ε alpha +
        nearMinorLowerTransitionSum N A ε alpha +
        nearMinorUpperTransitionSum N A ε alpha := by
  unfold smoothNearLiteralShotTail nearMinorLargeDenominatorSum
    nearMinorLowerTransitionSum nearMinorUpperTransitionSum
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p _hp
  exact smoothNearLiteralShotTerm_eq_hard_add_transitions N p A ε alpha

/-- Rearranged form used when bounding the literal hard near sum. -/
theorem nearMinorLargeDenominatorSum_eq_smooth_sub_transitions
    (N : ℕ) (A ε alpha : ℝ) :
    nearMinorLargeDenominatorSum N A ε alpha =
      smoothNearLiteralShotTail N
          (A / (2 * Real.log (N : ℝ))) ε 2 N alpha -
        nearMinorLowerTransitionSum N A ε alpha -
        nearMinorUpperTransitionSum N A ε alpha := by
  rw [smoothNearLiteralShotTail_eq_hard_add_transitions]
  ring

/-- Exact full hard-near decomposition, including the separately controlled
endpoint denominators.  No norm inequality or deletion of summands is used
in this identity. -/
theorem nearMinorHardNearSum_eq_endpoint_add_smooth_sub_transitions
    (N : ℕ) (A ε alpha : ℝ) :
    nearMinorHardNearSum N A ε alpha =
      nearMinorSmallDenominatorSum N A ε alpha +
        smoothNearLiteralShotTail N
          (A / (2 * Real.log (N : ℝ))) ε 2 N alpha -
        nearMinorLowerTransitionSum N A ε alpha -
        nearMinorUpperTransitionSum N A ε alpha := by
  unfold nearMinorHardNearSum
  rw [nearMinorLargeDenominatorSum_eq_smooth_sub_transitions]
  ring

/-- Pointwise reconstruction of the complete hard-near sum by the carrier
series.  The hypotheses are exactly those needed to identify the smooth
cell representative with the literal primitive-resonance pole. -/
theorem nearMinorHardNearSum_eq_endpoint_add_carriers_sub_transitions
    (N : ℕ) (A ε alpha : ℝ)
    (hA : 0 < A) (hL : 0 < Real.log (N : ℝ))
    (hε : 0 < ε)
    (haε : A / (2 * Real.log (N : ℝ)) ≤ ε / 4)
    (hεhalf : ε ≤ 1 / 2)
    (halpha : alpha ∈ Set.Ioo (0 : ℝ) 1) :
    nearMinorHardNearSum N A ε alpha =
      nearMinorSmallDenominatorSum N A ε alpha +
        (∑' ell : ℤ,
          smoothNearPrimitivePoleCarrierTail N ell
            (A / (2 * Real.log (N : ℝ))) ε 2 N alpha) -
        nearMinorLowerTransitionSum N A ε alpha -
        nearMinorUpperTransitionSum N A ε alpha := by
  rw [nearMinorHardNearSum_eq_endpoint_add_smooth_sub_transitions]
  rw [tsum_smoothNearPrimitivePoleCarrierTail_eq_literal
    N (A / (2 * Real.log (N : ℝ))) ε 2 N alpha (by omega)
      (by positivity) hε haε hεhalf halpha]

/-- If the inner hard threshold has reached the outer near window, the
entire literal near sum is empty.  This case is important for a rectangular
two-parameter limit: no relation between the growth rates of `A` and `N`
is silently assumed. -/
theorem nearMinorHardNearSum_eq_zero_of_outer_le_inner
    (N : ℕ) (A ε : ℝ)
    (hL : 0 < Real.log (N : ℝ))
    (hcut : ε / 4 ≤ A / Real.log (N : ℝ)) :
    nearMinorHardNearSum N A ε = (fun _alpha : ℝ ↦ 0) := by
  funext alpha
  have hzero (p : ℕ) :
      ¬ (A < Real.log (N : ℝ) *
          |(p : ℝ) * resonanceDelta p alpha| ∧
        |(p : ℝ) * resonanceDelta p alpha| ≤ ε / 4) := by
    rintro ⟨hlower, hupper⟩
    have hdiv : A / Real.log (N : ℝ) <
        |(p : ℝ) * resonanceDelta p alpha| := by
      apply (div_lt_iff₀ hL).2
      simpa only [mul_comm] using! hlower
    linarith
  change nearMinorHardNearSum N A ε alpha = (0 : ℂ)
  unfold nearMinorHardNearSum nearMinorSmallDenominatorSum
    nearMinorSmallDenominatorTerm nearMinorLargeDenominatorSum
    nearMinorLargeDenominatorTerm
  rw [if_neg (hzero 1), if_neg (hzero 2), zero_add]
  simp only [Finset.sum_eq_zero fun p _hp ↦ if_neg (hzero p), add_zero]

/-! ## Exact split of the complete literal minor shot -/

/-- Complex-valued copy of the manuscript's real minor shot.  Introducing
this finite-sum form avoids hiding casts in the exact decomposition below. -/
def complexMinorResonanceShotSum
    (N : ℕ) (A : ℝ) (alpha : ℝ) : ℂ :=
  ∑ p ∈ Finset.Icc 1 N,
    if A < |scaledResonanceCoordinate N p alpha| then
      (primitiveShot N p alpha : ℂ)
    else 0

theorem complexMinorResonanceShotSum_eq_cast
    (N : ℕ) (A alpha : ℝ) :
    complexMinorResonanceShotSum N A alpha =
      (minorResonanceShotSum N A alpha : ℂ) := by
  unfold complexMinorResonanceShotSum minorResonanceShotSum
  push_cast
  apply Finset.sum_congr rfl
  intro p _hp
  by_cases h : A < |scaledResonanceCoordinate N p alpha| <;> simp [h]

/-- The sharp fixed-away part paired with the present convention for the
near window. -/
def minorFixedAwaySharpTerm
    (N p : ℕ) (t : ℝ) (alpha : ℝ) : ℂ :=
  if t < |(p : ℝ) * resonanceDelta p alpha| then
    (primitiveShot N p alpha : ℂ)
  else 0

def minorFixedAwaySharpSum
    (N : ℕ) (t : ℝ) (alpha : ℝ) : ℂ :=
  ∑ p ∈ Finset.Icc 1 N, minorFixedAwaySharpTerm N p t alpha

theorem measurable_minorFixedAwaySharpTerm
    (N p : ℕ) (t : ℝ) :
    Measurable (minorFixedAwaySharpTerm N p t) := by
  unfold minorFixedAwaySharpTerm
  apply Measurable.ite
  · exact measurableSet_lt measurable_const
      ((measurable_const.mul (measurable_resonanceDelta p)).abs)
  · exact (measurable_primitiveShot N p).complex_ofReal
  · exact measurable_const

theorem measurable_minorFixedAwaySharpSum
    (N : ℕ) (t : ℝ) :
    Measurable (minorFixedAwaySharpSum N t) := by
  unfold minorFixedAwaySharpSum
  exact Finset.measurable_fun_sum (Finset.Icc 1 N) fun p _hp ↦
    measurable_minorFixedAwaySharpTerm N p t

theorem nearMinorSmallDenominatorTerm_eq_large
    (N p : ℕ) (A ε alpha : ℝ) :
    nearMinorSmallDenominatorTerm N A ε p alpha =
      nearMinorLargeDenominatorTerm N A ε p alpha := by
  rfl

/-- The endpoint-plus-tail definition is exactly a single sum over
`1≤p≤N`; the assumption `N≥2` is stated because the endpoint block
contains both `p=1` and `p=2`. -/
theorem nearMinorHardNearSum_eq_finset
    (N : ℕ) (A ε alpha : ℝ) (hN : 2 ≤ N) :
    nearMinorHardNearSum N A ε alpha =
      ∑ p ∈ Finset.Icc 1 N,
        nearMinorLargeDenominatorTerm N A ε p alpha := by
  have hset : Finset.Icc 1 N =
      insert 1 (insert 2 (Finset.Ioc 2 N)) := by
    ext p
    simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_Ioc]
    omega
  rw [hset, Finset.sum_insert, Finset.sum_insert]
  · unfold nearMinorHardNearSum nearMinorSmallDenominatorSum
      nearMinorLargeDenominatorSum
    rw [nearMinorSmallDenominatorTerm_eq_large,
      nearMinorSmallDenominatorTerm_eq_large]
    ring
  · simp
  · simp

/-- One-denominator partition of the minor condition at the fixed threshold
`ε/4`.  Positivity of `log N` is used explicitly when translating
`|L pδ_p|` into `L|pδ_p|`. -/
theorem complexMinorTerm_eq_near_add_fixedAway
    (N p : ℕ) (A ε alpha : ℝ)
    (hL : 0 < Real.log (N : ℝ))
    (hAquarter : A < Real.log (N : ℝ) * (ε / 4)) :
    (if A < |scaledResonanceCoordinate N p alpha| then
        (primitiveShot N p alpha : ℂ)
      else 0) =
      nearMinorLargeDenominatorTerm N A ε p alpha +
        minorFixedAwaySharpTerm N p (ε / 4) alpha := by
  let L : ℝ := Real.log (N : ℝ)
  let x : ℝ := |(p : ℝ) * resonanceDelta p alpha|
  have hscaled : |scaledResonanceCoordinate N p alpha| = L * x := by
    unfold scaledResonanceCoordinate
    dsimp [L, x]
    rw [abs_mul, abs_mul, abs_of_pos hL]
    rw [abs_mul]
    ring
  rw [hscaled]
  by_cases hquarter : x ≤ ε / 4
  · have hnotFar : ¬ ε / 4 < x := not_lt.mpr hquarter
    by_cases hminor : A < L * x
    · unfold nearMinorLargeDenominatorTerm minorFixedAwaySharpTerm
      rw [if_pos hminor, if_pos ⟨by simpa only [L, x] using! hminor,
        by simpa only [x] using! hquarter⟩,
        if_neg (by simpa only [x] using! hnotFar), add_zero]
    · unfold nearMinorLargeDenominatorTerm minorFixedAwaySharpTerm
      rw [if_neg hminor,
        if_neg (fun h ↦ hminor (by simpa only [L, x] using! h.1)),
        if_neg (by simpa only [x] using! hnotFar), zero_add]
  · have hfar : ε / 4 < x := lt_of_not_ge hquarter
    have hminor : A < L * x := by
      calc
        A < L * (ε / 4) := by simpa only [L] using! hAquarter
        _ < L * x := mul_lt_mul_of_pos_left hfar (by simpa only [L] using! hL)
    have hnotNear : ¬ (A < L * x ∧ x ≤ ε / 4) :=
      fun h ↦ hquarter h.2
    unfold nearMinorLargeDenominatorTerm minorFixedAwaySharpTerm
    rw [if_pos hminor, if_neg (by simpa only [L, x] using! hnotNear),
      if_pos (by simpa only [x] using! hfar), zero_add]

/-- Exact finite-sum decomposition of the complete minor shot.  This is the
literal bridge needed before any probabilistic or `L²` estimate is invoked. -/
theorem complexMinorResonanceShotSum_eq_hardNear_add_fixedAway
    (N : ℕ) (A ε alpha : ℝ)
    (hN : 2 ≤ N) (hL : 0 < Real.log (N : ℝ))
    (hAquarter : A < Real.log (N : ℝ) * (ε / 4)) :
    complexMinorResonanceShotSum N A alpha =
      nearMinorHardNearSum N A ε alpha +
        minorFixedAwaySharpSum N (ε / 4) alpha := by
  rw [nearMinorHardNearSum_eq_finset N A ε alpha hN]
  unfold complexMinorResonanceShotSum minorFixedAwaySharpSum
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p _hp
  exact complexMinorTerm_eq_near_add_fixedAway
    N p A ε alpha hL hAquarter

/-- The lower residual vanishes throughout the hard plateau. -/
theorem nearMinorLowerTransitionTerm_eq_zero_of_window
    (N p : ℕ) (A ε alpha : ℝ)
    (hA : 0 < A) (hL : 0 < Real.log (N : ℝ)) (hε : 0 < ε)
    (hwindow : A < Real.log (N : ℝ) *
          |(p : ℝ) * resonanceDelta p alpha| ∧
        |(p : ℝ) * resonanceDelta p alpha| ≤ ε / 4) :
    nearMinorLowerTransitionTerm N A ε p alpha = 0 := by
  unfold nearMinorLowerTransitionTerm
  rw [if_pos hwindow.2,
    nearMinorLargeDenominatorTerm_eq_smooth_of_window
      N p A ε alpha hA hL hε hwindow, sub_self]

/-- The outer residual is supported above `ε/4`. -/
theorem nearMinorUpperTransitionTerm_eq_zero_of_abs_le_quarter
    (N p : ℕ) (A ε alpha : ℝ)
    (hquarter : |(p : ℝ) * resonanceDelta p alpha| ≤ ε / 4) :
    nearMinorUpperTransitionTerm N A ε p alpha = 0 := by
  unfold nearMinorUpperTransitionTerm
  rw [if_neg (not_lt.mpr hquarter)]

/-- The outer transition is confined to the finite annulus
`ε/4 < |pδ_p| < ε`; at and beyond `ε` the smooth cutoff vanishes
identically. -/
theorem nearMinorUpperTransitionTerm_eq_zero_of_epsilon_le_abs
    (N p : ℕ) (A ε alpha : ℝ)
    (hA : 0 < A) (hL : 0 < Real.log (N : ℝ))
    (hε : 0 < ε)
    (haε : A / (2 * Real.log (N : ℝ)) ≤ ε / 4)
    (houter : ε ≤ |(p : ℝ) * resonanceDelta p alpha|) :
    nearMinorUpperTransitionTerm N A ε p alpha = 0 := by
  have ha : 0 < A / (2 * Real.log (N : ℝ)) := by positivity
  have hrho : nearRho (A / (2 * Real.log (N : ℝ))) ε
      ((p : ℝ) * resonanceDelta p alpha) = 0 :=
    nearRho_eq_zero_of_epsilon_le_abs
      (A / (2 * Real.log (N : ℝ))) ε
      ((p : ℝ) * resonanceDelta p alpha) ha hε haε houter
  unfold nearMinorUpperTransitionTerm
  by_cases hquarter : ε / 4 <
      |(p : ℝ) * resonanceDelta p alpha|
  · rw [if_pos hquarter,
      smoothNearLiteralShotTerm_eq_rho_mul_primitiveShot, hrho, zero_mul]
  · rw [if_neg hquarter]

end

end Erdos1002
