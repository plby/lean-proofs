import ErdosProblems.Erdos1002.GaussPrefixAnnularUpperShallowAsymptotic
import ErdosProblems.Erdos1002.GaussPrefixAnnularLateErrorAssembly

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Aggregate shallow-prefix cancellation for the upper retained family

The one-tuple carrier estimate is summed here over every chronological tag
and every upper-retained tuple.  The only tuple-dependent object is the
chosen canonical realization; the bound is uniform.  A finite-order
Fourier budget holds eventually for every tag, and the polynomial
cardinality of the tagged family is absorbed by the power-saving shallow
exponent.
-/

open Filter Finset MeasureTheory Set
open scoped BigOperators Topology

namespace Erdos1002

noncomputable section

local instance gaussPrefixAnnularUpperShallowAggregatePropDecidable
    (P : Prop) : Decidable P := Classical.propDecidable P

/-- Inactive labels never occur in the mixed product.  Setting their
endpoint to zero supplies a globally bounded endpoint family without
changing any mixed character. -/
def annularActiveSignedLower
    (ε A : ℝ) {grid : ℕ} (k : AnnularGridIndex grid → ℕ)
    (i : AnnularGridIndex grid) : ℝ :=
  if 0 < k i then annularOccurrenceSignedLower ε A i else 0

def annularActiveSignedUpper
    (ε A : ℝ) {grid : ℕ} (k : AnnularGridIndex grid → ℕ)
    (i : AnnularGridIndex grid) : ℝ :=
  if 0 < k i then annularOccurrenceSignedUpper ε A i else 0

theorem abs_annularActiveSignedLower_le
    {ε A : ℝ} (hε : 0 < ε) (hεA : ε < A)
    {grid : ℕ} (hgrid : 0 < grid)
    (k : AnnularGridIndex grid → ℕ)
    (hsigned : ∀ i, 0 < k i → i.signed.1 < grid)
    (i : AnnularGridIndex grid) :
    |annularActiveSignedLower ε A k i| ≤ A := by
  by_cases hi : 0 < k i
  · rw [annularActiveSignedLower, if_pos hi]
    exact abs_annularOccurrenceSignedLower_le
      hε hεA hgrid i (hsigned i hi)
  · rw [annularActiveSignedLower, if_neg hi, abs_zero]
    exact (lt_trans hε hεA).le

theorem abs_annularActiveSignedUpper_le
    {ε A : ℝ} (hε : 0 < ε) (hεA : ε < A)
    {grid : ℕ} (hgrid : 0 < grid)
    (k : AnnularGridIndex grid → ℕ)
    (hsigned : ∀ i, 0 < k i → i.signed.1 < grid)
    (i : AnnularGridIndex grid) :
    |annularActiveSignedUpper ε A k i| ≤ A := by
  by_cases hi : 0 < k i
  · rw [annularActiveSignedUpper, if_pos hi]
    exact abs_annularOccurrenceSignedUpper_le
      hε hεA hgrid i (hsigned i hi)
  · rw [annularActiveSignedUpper, if_neg hi, abs_zero]
    exact (lt_trans hε hεA).le

/-- Replacing inactive endpoints by zero does not change a literal mixed
prefix character. -/
theorem gaussPrefixMarkedMixedPrefixCharacter_activeEndpoints_eq
    {ε A : ℝ} {N grid : ℕ}
    (k : AnnularGridIndex grid → ℕ)
    (h : ∀ i, Fin (k i) → ℤ)
    (F : GaussPrefixMixedDepthTuple N k)
    (m : ℕ) (x : ℝ) :
    gaussPrefixMarkedMixedPrefixCharacter N
        (fun i ↦ compactValueMarkedRegion
          (annularActiveSignedLower ε A k i)
          (annularActiveSignedUpper ε A k i))
        k h F m x =
      gaussPrefixMarkedMixedPrefixCharacter N
        (fun i ↦ compactValueMarkedRegion
          (annularOccurrenceSignedLower ε A i)
          (annularOccurrenceSignedUpper ε A i))
        k h F m x := by
  unfold gaussPrefixMarkedMixedPrefixCharacter
  apply Finset.prod_congr rfl
  intro z _hz
  have hactive : 0 < k z.1 := by
    have hzlt := z.2.isLt
    omega
  simp only [annularActiveSignedLower, annularActiveSignedUpper,
    if_pos hactive]

/-- The exact shallow prefix-good cylinder integral belonging to one
upper-retained tagged tuple. -/
def annularUpperRetainedShallowPrefixGoodIntegral
    (ε A rho : ℝ) (N : ℕ) {grid : ℕ}
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k)
    (mode :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Fin (MixedOccurrenceCount k) → ℤ)
    (hmode : ∀ e, mode e ≠ 0)
    (p : AnnularUpperRetainedTaggedTuple rho N k hr mode hmode) : ℂ :=
  ∑ w ∈ shallowExactDepthPrefixGoodCells N
      (annularUpperRetainedShallowSplitDepth p)
      (annularDepthAmbientSize N)
      (upperRetainedShallowDenominatorTolerance rho),
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
/-- Pointwise uniform bound for the actual annular endpoints. -/
theorem norm_annularUpperRetainedShallowPrefixGoodIntegral_le
    {ε A rho : ℝ} {N grid : ℕ}
    (hε : 0 < ε) (hεA : ε < A) (hrho : 0 < rho)
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
    ‖annularUpperRetainedShallowPrefixGoodIntegral
        ε A rho N k hr mode hmode p‖ ≤
      (36 / Real.pi) *
        Real.exp
          (upperRetainedShallowUniformExponent rho
            (upperRetainedShallowDenominatorTolerance rho) N) := by
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
      hN hgrid htime p hW
      (upperRetainedShallowDenominatorTolerance_pos hrho).le
      hweightBudget lower upper hlower hupper hsmall
  have heq :
      annularUpperRetainedShallowPrefixGoodIntegral
          ε A rho N k hr mode hmode p =
        ∑ w ∈ shallowExactDepthPrefixGoodCells N
            (annularUpperRetainedShallowSplitDepth p)
            (annularDepthAmbientSize N)
            (upperRetainedShallowDenominatorTolerance rho),
          ∫ y in exactDepthBoundedCylinder w,
            gaussPrefixMarkedMixedPrefixCharacter N
              (fun i ↦ compactValueMarkedRegion (lower i) (upper i))
              k (unflattenedAnnularFourierMode p.1 (mode p.1))
              (annularUpperRetainedRealization p).1
              (annularUpperRetainedShallowSplitDepth p) y
              ∂uniform01Measure := by
    unfold annularUpperRetainedShallowPrefixGoodIntegral
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

/-- The total fixed Fourier weight (without deleting the carrier) is
eventually absorbed by the canonical separation power. -/
theorem eventually_annularSeparationGap_totalFourierWeightBudget
    {grid : ℕ} {k : AnnularGridIndex grid → ℕ}
    (h : ∀ i, Fin (k i) → ℤ) :
    ∀ᶠ N : ℕ in atTop,
      2 * (∑ z : GaussPrefixMixedOccurrence k,
        |(h z.1 z.2 : ℝ)|) ≤
          ((2 ^ (annularSeparationGap N / 2) : ℕ) : ℝ) := by
  have hgapHalf :
      Tendsto (fun N ↦ annularSeparationGap N / 2) atTop atTop :=
    (Nat.tendsto_div_const_atTop (by norm_num)).comp
      tendsto_annularSeparationGap_atTop
  have hpowNat :
      Tendsto (fun N ↦ 2 ^ (annularSeparationGap N / 2))
        atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt
      (show (1 : ℕ) < 2 by norm_num)).comp hgapHalf
  have hpowReal :
      Tendsto
        (fun N ↦ ((2 ^ (annularSeparationGap N / 2) : ℕ) : ℝ))
        atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hpowNat
  exact hpowReal.eventually_ge_atTop
    (2 * ∑ z : GaussPrefixMixedOccurrence k,
      |(h z.1 z.2 : ℝ)|)

/-- Exact cardinal identity for the sigma type of tagged retained tuples. -/
theorem card_annularUpperRetainedTaggedTuple_eq_nestedPairCount
    {rho : ℝ} {N grid : ℕ}
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k)
    (mode :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Fin (MixedOccurrenceCount k) → ℤ)
    (hmode : ∀ e, mode e ≠ 0) :
    Fintype.card
        (AnnularUpperRetainedTaggedTuple rho N k hr mode hmode) =
      nestedPairCount
        (Finset.univ :
          Finset (Fin (MixedOccurrenceCount k) ≃
            GaussPrefixMixedOccurrence k))
        (fun e ↦ annularCanonicalLaterUpperMidpointTupleFamily
          rho N k hr e (mode e) (hmode e)) := by
  unfold AnnularUpperRetainedTaggedTuple nestedPairCount
  rw [Fintype.card_sigma]
  apply Finset.sum_congr rfl
  intro e _he
  exact Fintype.card_coe _

set_option maxHeartbeats 800000 in
/-- Polynomially many upper-retained shallow prefix-good means cancel in
absolute sum. -/
theorem tendsto_sum_norm_annularUpperRetainedShallowPrefixGoodIntegral_zero
    {ε A rho : ℝ} (hε : 0 < ε) (hεA : ε < A) (hrho : 0 < rho)
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
          ‖annularUpperRetainedShallowPrefixGoodIntegral
            ε A rho N k hr mode hmode p‖)
      atTop (nhds 0) := by
  let C : ℝ := 36 / Real.pi
  let r : ℕ := MixedOccurrenceCount k + 1
  have hzero :
      Tendsto
        (fun N : ℕ ↦
          C * (annularDepthAmbientSize N : ℝ) ^ r *
            Real.exp
              (upperRetainedShallowUniformExponent rho
                (upperRetainedShallowDenominatorTolerance rho) N))
        atTop (nhds 0) :=
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
    calc
      (∑ p : AnnularUpperRetainedTaggedTuple
          rho N k hr mode hmode,
        ‖annularUpperRetainedShallowPrefixGoodIntegral
          ε A rho N k hr mode hmode p‖) ≤
        ∑ _p : AnnularUpperRetainedTaggedTuple
            rho N k hr mode hmode,
          C * Real.exp
            (upperRetainedShallowUniformExponent rho
              (upperRetainedShallowDenominatorTolerance rho) N) := by
        apply Finset.sum_le_sum
        intro p _hp
        exact norm_annularUpperRetainedShallowPrefixGoodIntegral_le
          hε hεA hrho hN hgrid k hr htime hsigned mode hmode
          p hW hsmallN (hbudgetN p.1)
      _ = (Fintype.card
            (AnnularUpperRetainedTaggedTuple
              rho N k hr mode hmode) : ℝ) *
          (C * Real.exp
            (upperRetainedShallowUniformExponent rho
              (upperRetainedShallowDenominatorTolerance rho) N)) := by
        simp
      _ ≤ (annularDepthAmbientSize N : ℝ) ^ r *
          (C * Real.exp
            (upperRetainedShallowUniformExponent rho
              (upperRetainedShallowDenominatorTolerance rho) N)) := by
        apply mul_le_mul_of_nonneg_right
        · exact_mod_cast hcardTagged
        · positivity
      _ = C * (annularDepthAmbientSize N : ℝ) ^ r *
          Real.exp
            (upperRetainedShallowUniformExponent rho
              (upperRetainedShallowDenominatorTolerance rho) N) := by
        ring
  · exact hzero

end

end Erdos1002
