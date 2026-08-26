import ErdosProblems.Erdos1002.GaussPrefixAnnularUpperShallowAggregate

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Shallow cancellation with a caller-supplied denominator tolerance

The contracted moving-to-Gauss transfer uses a tolerance depending on the
time-box contraction parameter.  It need not equal the convenient
`mu * rho / 6` tolerance used in the first shallow aggregate theorem.
This file exposes the actual monotonicity needed downstream: every fixed
nonnegative tolerance no larger than `upperRetainedShallowDenominatorTolerance
rho` enjoys the same aggregate cancellation.
-/

open Filter Finset MeasureTheory Set
open scoped BigOperators Topology

namespace Erdos1002

noncomputable section

local instance gaussPrefixAnnularUpperShallowVariableTolerancePropDecidable
    (P : Prop) : Decidable P := Classical.propDecidable P

/-- The shallow prefix-good integral at an arbitrary denominator
tolerance. -/
def annularUpperRetainedShallowPrefixGoodIntegralWithTolerance
    (ε A rho Delta : ℝ) (N : ℕ) {grid : ℕ}
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k)
    (mode :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Fin (MixedOccurrenceCount k) → ℤ)
    (hmode : ∀ e, mode e ≠ 0)
    (p : AnnularUpperRetainedTaggedTuple rho N k hr mode hmode) : ℂ :=
  ∑ w ∈ shallowExactDepthPrefixGoodCells N
      (annularUpperRetainedShallowSplitDepth p)
      (annularDepthAmbientSize N) Delta,
    ∫ y in exactDepthBoundedCylinder w,
      gaussPrefixMarkedMixedPrefixCharacter N
        (fun i ↦ compactValueMarkedRegion
          (annularOccurrenceSignedLower ε A i)
          (annularOccurrenceSignedUpper ε A i))
        k (unflattenedAnnularFourierMode p.1 (mode p.1))
        (annularUpperRetainedRealization p).1
        (annularUpperRetainedShallowSplitDepth p) y
        ∂uniform01Measure

set_option maxHeartbeats 800000 in
/-- Uniform one-tuple bound at the caller-supplied tolerance. -/
theorem
    norm_annularUpperRetainedShallowPrefixGoodIntegralWithTolerance_le
    {ε A rho Delta : ℝ} {N grid : ℕ}
    (hε : 0 < ε) (hεA : ε < A)
    (hDelta : 0 ≤ Delta)
    (hN : 2 ≤ N) (hgrid : 0 < grid)
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k)
    (htime : ∀ i, 0 < k i → i.time.1 < grid)
    (hsigned : ∀ i, 0 < k i → i.signed.1 < grid)
    (mode :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Fin (MixedOccurrenceCount k) → ℤ)
    (hmode : ∀ e, mode e ≠ 0)
    (p : AnnularUpperRetainedTaggedTuple rho N k hr mode hmode)
    (hW : 0 < annularMidpointBandWidth rho N)
    (hsmall : A / Real.log (N : ℝ) < (1 : ℝ) / 2)
    (hweightBudget :
      2 * (∑ z : GaussPrefixMixedOccurrence k,
        |(unflattenedAnnularFourierMode p.1 (mode p.1)
          z.1 z.2 : ℝ)|) ≤
        ((2 ^ (annularSeparationGap N / 2) : ℕ) : ℝ)) :
    ‖annularUpperRetainedShallowPrefixGoodIntegralWithTolerance
        ε A rho Delta N k hr mode hmode p‖ ≤
      (36 / Real.pi) *
        Real.exp
          (upperRetainedShallowUniformExponent rho Delta N) := by
  let lower : AnnularGridIndex grid → ℝ :=
    annularActiveSignedLower ε A k
  let upper : AnnularGridIndex grid → ℝ :=
    annularActiveSignedUpper ε A k
  have hlower : ∀ i, |lower i| ≤ A := by
    intro i
    exact abs_annularActiveSignedLower_le
      hε hεA hgrid k hsigned i
  have hupper : ∀ i, |upper i| ≤ A := by
    intro i
    exact abs_annularActiveSignedUpper_le
      hε hεA hgrid k hsigned i
  have hraw :=
    norm_sum_annularUpperRetained_shallowPrefixGoodCells_le_envelope
      hN hgrid htime p hW hDelta hweightBudget
      lower upper hlower hupper hsmall
  have heq :
      annularUpperRetainedShallowPrefixGoodIntegralWithTolerance
          ε A rho Delta N k hr mode hmode p =
        ∑ w ∈ shallowExactDepthPrefixGoodCells N
            (annularUpperRetainedShallowSplitDepth p)
            (annularDepthAmbientSize N) Delta,
          ∫ y in exactDepthBoundedCylinder w,
            gaussPrefixMarkedMixedPrefixCharacter N
              (fun i ↦ compactValueMarkedRegion (lower i) (upper i))
              k (unflattenedAnnularFourierMode p.1 (mode p.1))
              (annularUpperRetainedRealization p).1
              (annularUpperRetainedShallowSplitDepth p) y
              ∂uniform01Measure := by
    unfold annularUpperRetainedShallowPrefixGoodIntegralWithTolerance
    apply Finset.sum_congr rfl
    intro w _hw
    apply MeasureTheory.integral_congr_ae
    filter_upwards with y
    symm
    exact gaussPrefixMarkedMixedPrefixCharacter_activeEndpoints_eq
      k (unflattenedAnnularFourierMode p.1 (mode p.1))
      (annularUpperRetainedRealization p).1
      (annularUpperRetainedShallowSplitDepth p) y
  rw [heq]
  exact hraw.trans
    (shallowPrefixCylinderEnvelope_le_upperUniform
      hgrid htime p hN hW)

/-- The uniform shallow exponent is monotone in the denominator
tolerance. -/
theorem upperRetainedShallowUniformExponent_mono_tolerance
    {rho Delta Delta' : ℝ} {N : ℕ}
    (hDelta : Delta ≤ Delta') :
    upperRetainedShallowUniformExponent rho Delta N ≤
      upperRetainedShallowUniformExponent rho Delta' N := by
  unfold upperRetainedShallowUniformExponent
  have hambient : 0 ≤ (annularDepthAmbientSize N : ℝ) := by positivity
  nlinarith

set_option maxHeartbeats 800000 in
/-- Polynomially many shallow prefix-good means cancel for every fixed
admissible tolerance. -/
theorem
    tendsto_sum_norm_annularUpperRetainedShallowPrefixGoodIntegralWithTolerance_zero
    {ε A rho Delta : ℝ}
    (hε : 0 < ε) (hεA : ε < A) (hrho : 0 < rho)
    (hDelta : 0 ≤ Delta)
    (hDeltaUpper :
      Delta ≤ upperRetainedShallowDenominatorTolerance rho)
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
        ∑ p : AnnularUpperRetainedTaggedTuple
            rho N k hr mode hmode,
          ‖annularUpperRetainedShallowPrefixGoodIntegralWithTolerance
            ε A rho Delta N k hr mode hmode p‖)
      atTop (nhds 0) := by
  let C : ℝ := 36 / Real.pi
  let r : ℕ := MixedOccurrenceCount k + 1
  let Delta₀ : ℝ := upperRetainedShallowDenominatorTolerance rho
  have hzero :
      Tendsto
        (fun N : ℕ ↦
          C * (annularDepthAmbientSize N : ℝ) ^ r *
            Real.exp
              (upperRetainedShallowUniformExponent rho Delta₀ N))
        atTop (nhds 0) := by
    simpa only [Delta₀] using!
      tendsto_const_mul_annularDepth_pow_mul_exp_upperShallowUniform_zero
        C r (by dsimp only [C]; positivity) hrho
  have hbudget :
      ∀ᶠ N : ℕ in atTop,
        ∀ e : Fin (MixedOccurrenceCount k) ≃
            GaussPrefixMixedOccurrence k,
          2 * (∑ z : GaussPrefixMixedOccurrence k,
            |(unflattenedAnnularFourierMode e (mode e)
              z.1 z.2 : ℝ)|) ≤
            ((2 ^ (annularSeparationGap N / 2) : ℕ) : ℝ) :=
    Filter.eventually_all.mpr fun e ↦
      eventually_annularSeparationGap_totalFourierWeightBudget
        (unflattenedAnnularFourierMode e (mode e))
  have hsmall :
      ∀ᶠ N : ℕ in atTop,
        A / Real.log (N : ℝ) < (1 : ℝ) / 2 :=
    (tendsto_log_natCast_atTop.const_div_atTop A).eventually_lt_const
      (by norm_num)
  have hwidth :=
    (tendsto_annularMidpointBandWidth_atTop hrho).eventually_gt_atTop 0
  have hcard :=
    eventually_nestedPairCount_annularUpperRetained_le_ambient_pow_succ
      (rho := rho) hgrid k hr htime mode hmode
  apply squeeze_zero'
  · exact Eventually.of_forall fun N ↦
      Finset.sum_nonneg fun _p _hp ↦ norm_nonneg _
  · filter_upwards
      [eventually_ge_atTop 2, hwidth, hsmall, hbudget, hcard] with
      N hN hW hsmallN hbudgetN hcardN
    have hcardTagged :
        Fintype.card
            (AnnularUpperRetainedTaggedTuple
              rho N k hr mode hmode) ≤
          annularDepthAmbientSize N ^ r := by
      rw [card_annularUpperRetainedTaggedTuple_eq_nestedPairCount]
      simpa only [r] using! hcardN
    have hExp :
        Real.exp
            (upperRetainedShallowUniformExponent rho Delta N) ≤
          Real.exp
            (upperRetainedShallowUniformExponent rho Delta₀ N) :=
      Real.exp_le_exp.mpr
        (upperRetainedShallowUniformExponent_mono_tolerance
          (N := N) hDeltaUpper)
    calc
      (∑ p : AnnularUpperRetainedTaggedTuple
          rho N k hr mode hmode,
        ‖annularUpperRetainedShallowPrefixGoodIntegralWithTolerance
          ε A rho Delta N k hr mode hmode p‖) ≤
        ∑ _p : AnnularUpperRetainedTaggedTuple
            rho N k hr mode hmode,
          C * Real.exp
            (upperRetainedShallowUniformExponent rho Delta N) := by
        apply Finset.sum_le_sum
        intro p _hp
        exact
          norm_annularUpperRetainedShallowPrefixGoodIntegralWithTolerance_le
            hε hεA hDelta hN hgrid k hr htime hsigned mode hmode
            p hW hsmallN (hbudgetN p.1)
      _ ≤ ∑ _p : AnnularUpperRetainedTaggedTuple
            rho N k hr mode hmode,
          C * Real.exp
            (upperRetainedShallowUniformExponent rho Delta₀ N) := by
        apply Finset.sum_le_sum
        intro _p _hp
        exact mul_le_mul_of_nonneg_left hExp (by positivity)
      _ = (Fintype.card
            (AnnularUpperRetainedTaggedTuple
              rho N k hr mode hmode) : ℝ) *
          (C * Real.exp
            (upperRetainedShallowUniformExponent rho Delta₀ N)) := by
        simp
      _ ≤ (annularDepthAmbientSize N : ℝ) ^ r *
          (C * Real.exp
            (upperRetainedShallowUniformExponent rho Delta₀ N)) := by
        apply mul_le_mul_of_nonneg_right
        · exact_mod_cast hcardTagged
        · positivity
      _ = C * (annularDepthAmbientSize N : ℝ) ^ r *
          Real.exp
            (upperRetainedShallowUniformExponent rho Delta₀ N) := by
        ring
  · exact hzero

end

end Erdos1002
