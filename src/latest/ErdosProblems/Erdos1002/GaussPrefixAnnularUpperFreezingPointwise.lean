import ErdosProblems.Erdos1002.GaussPrefixAnnularUpperFrozenJoint
import ErdosProblems.Erdos1002.GaussPrefixAnnularUpperDelayedFloor
import ErdosProblems.Erdos1002.GaussPrefixAnnularUpperShallowCancellation

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Pointwise character freezing for contracted upper annular tuples

The future digit block is kept as a multiplicative factor in every
statement.  The only pointwise simplification is the exact
Lebesgue-to-Gauss density bound.  In particular, no future indicator is
replaced by `1` before the complete joint freezing envelope has been
formed.
-/

open Filter Finset MeasureTheory Set
open scoped BigOperators Topology

namespace Erdos1002

noncomputable section

set_option maxHeartbeats 800000

local instance gaussPrefixAnnularUpperFreezingPointwisePropDecidable
    (P : Prop) : Decidable P := Classical.propDecidable P

variable {eta rho ε A : ℝ} {N grid : ℕ}
variable {k : AnnularGridIndex grid → ℕ}
variable {hr : 0 < MixedOccurrenceCount k}
variable
  {mode :
    (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
      Fin (MixedOccurrenceCount k) → ℤ}
variable {hmode : ∀ e, mode e ≠ 0}

private theorem
    oscillatoryPrefixFreezingEnvelope_le_of_phaseCoefficient_le
    {r : ℕ} (a b coordinate : Fin r → ℝ)
    (K phaseRadius valueRadius phaseCoefficient : ℝ)
    (hphase :
      2 * Real.pi * |K| * phaseRadius ≤ phaseCoefficient) :
    oscillatoryPrefixFreezingEnvelope
        a b coordinate K phaseRadius valueRadius ≤
      phaseCoefficient *
          closedIntervalIndicatorProduct
            (fun i ↦ a i - valueRadius)
            (fun i ↦ b i + valueRadius) coordinate +
        ∑ i,
          closedIntervalBoundaryIndicator
              (a i) (b i) valueRadius (coordinate i) *
            ∏ j ∈ (Finset.univ : Finset (Fin r)).erase i,
              closedIntervalIndicator
                (a j - valueRadius) (b j + valueRadius)
                (coordinate j) := by
  unfold oscillatoryPrefixFreezingEnvelope
  apply add_le_add
  · apply mul_le_mul_of_nonneg_right hphase
    unfold closedIntervalIndicatorProduct
    apply Finset.prod_nonneg
    intro i _hi
    unfold closedIntervalIndicator
    split <;> positivity
  · exact le_rfl

/-- The delayed freezing depth still lies below the contracted time-one
endpoint.  A genuine future occurrence supplies the comparison, so the
claim does not use a rounded heuristic for the midpoint. -/
theorem
    annularContractedUpperRetainedDelayedDepth_lt_contractedTimeOne
    (hgrid : 0 < grid)
    (htime : ∀ i, 0 < k i → i.time.1 < grid)
    (p : AnnularContractedUpperRetainedTaggedTuple
      eta rho N k hr mode hmode)
    (hN : 2 ≤ N)
    (hW : 0 < annularMidpointBandWidth rho N) :
    annularContractedUpperRetainedDelayedDepth p <
      gaussLogDepthEndpoint N (1 - eta) := by
  let q := annularContractedUpperRetainedUpperTag p
  obtain ⟨j, hj⟩ := annularUpperRetained_exists_after_split q hW
  have hjDelayed :
      annularContractedUpperRetainedDelayedDepth p <
        annularUpperRetainedTimes q j := by
    exact
      (annularUpperRetained_after_delayed_iff_after_split
        hgrid htime q (by omega) hW j).2 hj
  have hbox :
      annularUpperRetainedTimes q j ∈
        contractedAnnularTimeDepthBox N eta (q.1 j).1 := by
    simpa only [q, annularContractedUpperRetainedUpperTag,
      annularUpperRetainedTimes,
      annularContractedUpperRetainedTimes] using!
      contractedAnnularCanonicalLaterUpperMidpointTupleFamily_boxes
        p.2.2 j
  have hactive : 0 < k (q.1 j).1 := by
    have hjlt := (q.1 j).2.isLt
    omega
  have hfutureUpper :
      annularUpperRetainedTimes q j <
        gaussLogDepthEndpoint N (1 - eta) := by
    exact
      lt_gaussLogDepthEndpoint_one_sub_of_mem_contractedAnnularTimeDepthBox
        hgrid
        (Real.log_pos (by exact_mod_cast hN))
        (q.1 j).1 (htime (q.1 j).1 hactive) hbox
  exact hjDelayed.trans hfutureUpper

/-- On the delayed prefix-good event, contraction makes the complete
depth-`b` selected word denominator-bounded by the process cutoff `N`.
This supplies the genuine finite exact-depth cylinder required by the
pointwise freezing theorem. -/
theorem
    selectedDelayedTerminalDenominator_le_of_prefixGood
    (hgrid : 0 < grid)
    (htime : ∀ i, 0 < k i → i.time.1 < grid)
    (p : AnnularContractedUpperRetainedTaggedTuple
      eta rho N k hr mode hmode)
    (hN : 2 ≤ N)
    (hW : 0 < annularMidpointBandWidth rho N)
    (hmargin :
      upperGoodTransferDenominatorTolerance eta rho *
          (annularDepthAmbientSize N : ℝ) ≤
        eta * Real.log (N : ℝ))
    {x : ℝ}
    (hxGood :
      x ∈ gaussDenominatorPrefixGoodEvent
        (annularContractedUpperRetainedDelayedDepth p)
        (annularDepthAmbientSize N)
        (upperGoodTransferDenominatorTolerance eta rho)) :
    cfTerminalDenominator
        (selectedGaussPrefixWord
          (annularContractedUpperRetainedDelayedDepth p) x).1 ≤ N := by
  let b := annularContractedUpperRetainedDelayedDepth p
  let w : PositiveDigitWord b := selectedGaussPrefixWord b x
  have hwGood :
      w ∈ gaussDenominatorPrefixGoodWords b
        (annularDepthAmbientSize N)
        (upperGoodTransferDenominatorTolerance eta rho) := by
    simpa only [gaussDenominatorPrefixGoodEvent, Set.mem_preimage,
      b, w] using! hxGood
  have hdenUpper :=
    (positiveWordTerminalDenominator_exp_bounds_of_mem_prefixGoodWords
      w hwGood (show b ≤ b by rfl)).2
  have htake : w.1.take b = w.1 := by
    exact List.take_of_length_le w.2.1.le
  have hdenUpper' :
      (cfTerminalDenominator w.1 : ℝ) ≤
        Real.exp
          ((b : ℝ) * gaussRoofMean +
            upperGoodTransferDenominatorTolerance eta rho *
              (annularDepthAmbientSize N : ℝ)) := by
    simpa only [positiveDigitWordTake_val, htake] using! hdenUpper
  have hbEndpoint :=
    annularContractedUpperRetainedDelayedDepth_lt_contractedTimeOne
      hgrid htime p hN hW
  have hbReal :
      (b : ℝ) <
        (1 - eta) * Real.log (N : ℝ) / gaussRoofMean := by
    exact Nat.lt_ceil.mp (by
      simpa only [gaussLogDepthEndpoint, b] using! hbEndpoint)
  have hbMu :
      (b : ℝ) * gaussRoofMean <
        (1 - eta) * Real.log (N : ℝ) :=
    (lt_div_iff₀ gaussRoofMean_pos).mp hbReal
  have hexponent :
      (b : ℝ) * gaussRoofMean +
          upperGoodTransferDenominatorTolerance eta rho *
            (annularDepthAmbientSize N : ℝ) <
        Real.log (N : ℝ) := by
    linarith
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le (by norm_num) hN)
  have hdenReal :
      (cfTerminalDenominator w.1 : ℝ) < N := by
    calc
      (cfTerminalDenominator w.1 : ℝ) ≤
          Real.exp
            ((b : ℝ) * gaussRoofMean +
              upperGoodTransferDenominatorTolerance eta rho *
                (annularDepthAmbientSize N : ℝ)) := hdenUpper'
      _ < Real.exp (Real.log (N : ℝ)) :=
        Real.exp_lt_exp.mpr hexponent
      _ = (N : ℝ) := Real.exp_log hNpos
  exact_mod_cast hdenReal.le

/-- Canonical enumeration of the selected occurrences at or before the
delayed cutoff. -/
def annularContractedUpperRetainedPrefixOccurrenceEquiv
    (p : AnnularContractedUpperRetainedTaggedTuple
      eta rho N k hr mode hmode) :
    Fin (Fintype.card
      (GaussPrefixMixedPrefixOccurrence N k
        (annularContractedUpperRetainedRealization p).1
        (annularContractedUpperRetainedDelayedDepth p))) ≃
      GaussPrefixMixedPrefixOccurrence N k
        (annularContractedUpperRetainedRealization p).1
        (annularContractedUpperRetainedDelayedDepth p) :=
  (Fintype.equivFin _).symm

/-- Every selected occurrence in the delayed prefix was already present
at the shallow cutoff. -/
theorem annularContractedUpperRetainedPrefixOccurrence_depth_le_shallow
    (hgrid : 0 < grid)
    (htime : ∀ i, 0 < k i → i.time.1 < grid)
    (p : AnnularContractedUpperRetainedTaggedTuple
      eta rho N k hr mode hmode)
    (hN : 2 ≤ N)
    (hW : 0 < annularMidpointBandWidth rho N)
    (z : GaussPrefixMixedPrefixOccurrence N k
      (annularContractedUpperRetainedRealization p).1
      (annularContractedUpperRetainedDelayedDepth p)) :
    ((annularContractedUpperRetainedRealization p).1
        z.1.1 z.1.2 : ℕ) ≤
      annularContractedUpperRetainedShallowDepth p := by
  let q := annularContractedUpperRetainedUpperTag p
  have hdelayed :
      ((annularUpperRetainedRealization q).1
          z.1.1 z.1.2 : ℕ) ≤
        annularUpperRetainedDelayedSplitDepth q := by
    simpa only [q, annularContractedUpperRetainedUpperTag,
      annularContractedUpperRetainedRealization,
      annularContractedUpperRetainedDelayedDepth] using! z.2
  have hnotSplit :
      ¬annularUpperRetainedSplitDepth q <
        ((annularUpperRetainedRealization q).1
          z.1.1 z.1.2 : ℕ) := by
    exact
      (not_congr
        (annularUpperRetained_labeled_after_delayed_iff_after_split
          hgrid htime q (by omega) hW z.1)).mp
        (not_lt_of_ge hdelayed)
  have hsplit :
      ((annularUpperRetainedRealization q).1
          z.1.1 z.1.2 : ℕ) ≤
        annularUpperRetainedSplitDepth q := by
    exact Nat.le_of_not_gt hnotSplit
  exact
    (annularUpperRetained_labeled_le_shallow_iff_le_split
      hgrid htime q (by omega) hW z.1).2 hsplit

theorem annularContractedUpperRetainedShallowDepth_le_delayed
    (p : AnnularContractedUpperRetainedTaggedTuple
      eta rho N k hr mode hmode) :
    annularContractedUpperRetainedShallowDepth p ≤
      annularContractedUpperRetainedDelayedDepth p := by
  unfold annularContractedUpperRetainedShallowDepth
    annularContractedUpperRetainedDelayedDepth
    annularContractedUpperRetainedUpperTag
    annularUpperRetainedShallowSplitDepth
    annularUpperRetainedDelayedSplitDepth
  exact (Nat.sub_le _ _).trans (Nat.le_add_right _ _)

/-- The actual last nonzero Fourier depth.  The phase coefficient must be
stopped here, rather than at the later shallow cutoff, in order for the
midpoint arithmetic to expose the retained-gap decay. -/
def annularContractedUpperRetainedCenterDepth
    (p : AnnularContractedUpperRetainedTaggedTuple
      eta rho N k hr mode hmode) : ℕ :=
  annularContractedUpperRetainedTimes p
    (annularLastNonzeroIndex (mode p.1) (hmode p.1))

theorem annularContractedUpperRetainedCenterDepth_le_shallow
    (hgrid : 0 < grid)
    (htime : ∀ i, 0 < k i → i.time.1 < grid)
    (p : AnnularContractedUpperRetainedTaggedTuple
      eta rho N k hr mode hmode)
    (hN : 2 ≤ N)
    (hW : 0 < annularMidpointBandWidth rho N) :
    annularContractedUpperRetainedCenterDepth p ≤
      annularContractedUpperRetainedShallowDepth p := by
  simpa only [annularContractedUpperRetainedCenterDepth,
    annularContractedUpperRetainedShallowDepth,
    annularContractedUpperRetainedUpperTag,
    ← annularContractedUpperRetainedTimes_embedding] using!
    annularUpperRetained_centerDepth_le_shallow
      hgrid htime (annularContractedUpperRetainedUpperTag p)
        (by omega) hW

/-- Every nonzero labeled coefficient lies no later than the actual last
nonzero center.  The proof works directly with the contracted chronology,
avoiding any coercion between dependent tagged subtypes. -/
theorem annularContractedUpperRetained_nonzero_depth_le_center
    (p : AnnularContractedUpperRetainedTaggedTuple
      eta rho N k hr mode hmode)
    (z : GaussPrefixMixedOccurrence k)
    (hz :
      unflattenedAnnularFourierMode p.1 (mode p.1)
        z.1 z.2 ≠ 0) :
    ((annularContractedUpperRetainedRealization p).1
        z.1 z.2 : ℕ) ≤
      annularContractedUpperRetainedCenterDepth p := by
  let s := annularLastNonzeroIndex (mode p.1) (hmode p.1)
  let j : Fin (MixedOccurrenceCount k) := p.1.symm z
  have hjMode : mode p.1 j ≠ 0 := by
    simpa only [unflattenedAnnularFourierMode, j] using! hz
  have hjle : j ≤ s := by
    apply le_of_not_gt
    intro hsj
    exact hjMode
      (annularLastNonzeroIndex_zero_after
        (mode p.1) (hmode p.1) j hsj)
  have hchron :
      IsChronologicalNatTuple
        (annularContractedUpperRetainedTimes p) :=
    contractedAnnularCanonicalLaterUpperMidpointTupleFamily_chronological
      k hr p.1 (mode p.1) (hmode p.1)
        (annularContractedUpperRetainedTimes p) p.2.2
  have htimeLe :
      annularContractedUpperRetainedTimes p j ≤
        annularContractedUpperRetainedTimes p s := by
    by_cases hjs : j = s
    · rw [hjs]
    · exact
        (Nat.le_add_right _ 1).trans
          (hchron j s (lt_of_le_of_ne hjle hjs))
  have htimes :=
    congrFun (annularContractedUpperRetainedRealization_times p) j
  change
    ((annularContractedUpperRetainedRealization p).1
        (p.1 j).1 (p.1 j).2 : ℕ) =
      annularContractedUpperRetainedTimes p j at htimes
  have hej : p.1 j = z := p.1.apply_symm_apply z
  rw [hej] at htimes
  change
    ((annularContractedUpperRetainedRealization p).1
        z.1 z.2 : ℕ) ≤
      annularContractedUpperRetainedTimes p s
  rw [htimes]
  exact htimeLe

/-- Word-dependent freezing envelope, with all radii fixed by the common
prefix-good event. -/
def annularContractedUpperRetainedCharacterFreezingEnvelope
    (ε A eta rho : ℝ) (N : ℕ)
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k)
    (mode :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Fin (MixedOccurrenceCount k) → ℤ)
    (hmode : ∀ e, mode e ≠ 0)
    (p : AnnularContractedUpperRetainedTaggedTuple
      eta rho N k hr mode hmode)
    (x : ℝ) : ℝ :=
  let e := annularContractedUpperRetainedPrefixOccurrenceEquiv p
  let b := annularContractedUpperRetainedDelayedDepth p
  let d := annularContractedUpperRetainedShallowDepth p
  let F := (annularContractedUpperRetainedRealization p).1
  let h := unflattenedAnnularFourierMode p.1 (mode p.1)
  let w := selectedGaussPrefixWord b x
  oscillatoryPrefixFreezingEnvelope
    (fun i ↦ activeAnnularOccurrenceSignedLower k ε A (e i).1.1)
    (fun i ↦ activeAnnularOccurrenceSignedUpper k ε A (e i).1.1)
    (fun i ↦
      (gaussPrefixMarkedPoint N (F (e i).1.1 (e i).1.2)
        (selectedGaussPrefixWord (F (e i).1.1 (e i).1.2) x) x).2.1)
    ((N : ℝ) * gaussPrefixWordMixedPrefixCarrier N k h F b w)
    (gaussPrefixGoodCylinderPhaseRadius b
      (annularDepthAmbientSize N)
      (upperGoodTransferDenominatorTolerance eta rho))
    (gaussPrefixGoodValueFreezingRadius N d b
      (annularDepthAmbientSize N)
      (upperGoodTransferDenominatorTolerance eta rho))

/-- Word-independent majorant for the phase coefficient in the preceding
envelope. -/
def annularContractedUpperRetainedPhaseFreezingMajorant
    (eta rho : ℝ) (N : ℕ)
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k)
    (mode :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Fin (MixedOccurrenceCount k) → ℤ)
    (hmode : ∀ e, mode e ≠ 0)
    (p : AnnularContractedUpperRetainedTaggedTuple
      eta rho N k hr mode hmode) : ℝ :=
  let b := annularContractedUpperRetainedDelayedDepth p
  let s := annularContractedUpperRetainedCenterDepth p
  let F := (annularContractedUpperRetainedRealization p).1
  let h := unflattenedAnnularFourierMode p.1 (mode p.1)
  4 * Real.pi * (N : ℝ) *
      ((∑ z : GaussPrefixMixedPrefixOccurrence N k F b,
          |(h z.1.1 z.1.2 : ℝ)|) *
        Real.exp
          ((s : ℝ) * gaussRoofMean +
            upperGoodTransferDenominatorTolerance eta rho *
              (annularDepthAmbientSize N : ℝ))) /
    Real.exp
      ((b : ℝ) * gaussRoofMean -
        upperGoodTransferDenominatorTolerance eta rho *
          (annularDepthAmbientSize N : ℝ)) ^ 2

/-- Deterministic-coefficient version of the character envelope.  Its
event indicators are unchanged; only the word-dependent phase coefficient
has been replaced by the preceding common majorant. -/
def annularContractedUpperRetainedDeterministicCharacterFreezingEnvelope
    (ε A eta rho : ℝ) (N : ℕ)
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k)
    (mode :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Fin (MixedOccurrenceCount k) → ℤ)
    (hmode : ∀ e, mode e ≠ 0)
    (p : AnnularContractedUpperRetainedTaggedTuple
      eta rho N k hr mode hmode)
    (x : ℝ) : ℝ :=
  let e := annularContractedUpperRetainedPrefixOccurrenceEquiv p
  let b := annularContractedUpperRetainedDelayedDepth p
  let d := annularContractedUpperRetainedShallowDepth p
  let F := (annularContractedUpperRetainedRealization p).1
  let coordinate : Fin (Fintype.card
      (GaussPrefixMixedPrefixOccurrence N k F b)) → ℝ :=
    fun i ↦
      (gaussPrefixMarkedPoint N (F (e i).1.1 (e i).1.2)
        (selectedGaussPrefixWord (F (e i).1.1 (e i).1.2) x) x).2.1
  let valueRadius :=
    gaussPrefixGoodValueFreezingRadius N d b
      (annularDepthAmbientSize N)
      (upperGoodTransferDenominatorTolerance eta rho)
  annularContractedUpperRetainedPhaseFreezingMajorant
      eta rho N k hr mode hmode p *
    closedIntervalIndicatorProduct
      (fun i ↦
        activeAnnularOccurrenceSignedLower k ε A (e i).1.1 -
          valueRadius)
      (fun i ↦
        activeAnnularOccurrenceSignedUpper k ε A (e i).1.1 +
          valueRadius)
      coordinate +
    ∑ i,
      closedIntervalBoundaryIndicator
          (activeAnnularOccurrenceSignedLower k ε A (e i).1.1)
          (activeAnnularOccurrenceSignedUpper k ε A (e i).1.1)
          valueRadius (coordinate i) *
        ∏ j ∈
            (Finset.univ : Finset
              (Fin (Fintype.card
                (GaussPrefixMixedPrefixOccurrence N k F b)))).erase i,
          closedIntervalIndicator
            (activeAnnularOccurrenceSignedLower k ε A (e j).1.1 -
              valueRadius)
            (activeAnnularOccurrenceSignedUpper k ε A (e j).1.1 +
              valueRadius)
            (coordinate j)

/-- The complete joint envelope.  The future block is deliberately still
present. -/
def annularContractedUpperRetainedJointFreezingEnvelope
    (ε A eta rho : ℝ) (N : ℕ)
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k)
    (mode :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Fin (MixedOccurrenceCount k) → ℤ)
    (hmode : ∀ e, mode e ≠ 0)
    (p : AnnularContractedUpperRetainedTaggedTuple
      eta rho N k hr mode hmode)
    (x : ℝ) : ℝ :=
  (gaussDenominatorPrefixGoodEvent
    (annularContractedUpperRetainedDelayedDepth p)
    (annularDepthAmbientSize N)
    (upperGoodTransferDenominatorTolerance eta rho)).indicator
    (fun y ↦
      annularContractedUpperRetainedDeterministicCharacterFreezingEnvelope
          ε A eta rho N k hr mode hmode p y *
        ‖annularContractedUpperRetainedFutureDigitBlock ε A p y‖) x

/-- Pointwise freezing with the exact density and complete future block
attached. -/
theorem
    norm_weightedLive_sub_weightedAffine_le_jointFreezingEnvelope
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
        eta * Real.log (N : ℝ))
    {x : ℝ} (hxUnit : x ∈ Ioo (0 : ℝ) 1)
    (hxNonterm : ∀ q : ℕ, (gaussMap^[q]) x ≠ 0) :
    ‖(gaussLebesguePrefixWeight x : ℂ) *
          (gaussDenominatorPrefixGoodEvent
            (annularContractedUpperRetainedDelayedDepth p)
            (annularDepthAmbientSize N)
            (upperGoodTransferDenominatorTolerance eta rho)).indicator
            (gaussPrefixMarkedMixedPrefixCharacter N
              (fun i ↦ compactValueMarkedRegion
                (activeAnnularOccurrenceSignedLower k ε A i)
                (activeAnnularOccurrenceSignedUpper k ε A i))
              k
              (unflattenedAnnularFourierMode p.1 (mode p.1))
              (annularContractedUpperRetainedRealization p).1
              (annularContractedUpperRetainedDelayedDepth p)) x *
          annularContractedUpperRetainedFutureDigitBlock ε A p x -
        (gaussLebesguePrefixWeight x : ℂ) *
          gaussPrefixAffineFrozenCompactCharacter
            N
            (activeAnnularOccurrenceSignedLower k ε A)
            (activeAnnularOccurrenceSignedUpper k ε A)
            k
            (unflattenedAnnularFourierMode p.1 (mode p.1))
            (annularContractedUpperRetainedRealization p).1
            (annularContractedUpperRetainedDelayedDepth p)
            (annularContractedUpperRetainedGoodWords eta rho N p) x *
          annularContractedUpperRetainedFutureDigitBlock ε A p x‖ ≤
      (2 * Real.log 2) *
        annularContractedUpperRetainedJointFreezingEnvelope
          ε A eta rho N k hr mode hmode p x := by
  classical
  let G :=
    gaussDenominatorPrefixGoodEvent
      (annularContractedUpperRetainedDelayedDepth p)
      (annularDepthAmbientSize N)
      (upperGoodTransferDenominatorTolerance eta rho)
  by_cases hxGood : x ∈ G
  · let b := annularContractedUpperRetainedDelayedDepth p
    let d := annularContractedUpperRetainedShallowDepth p
    let selected : PositiveDigitWord b := selectedGaussPrefixWord b x
    have hden :
        cfTerminalDenominator selected.1 ≤ N := by
      exact
        selectedDelayedTerminalDenominator_le_of_prefixGood
          hgrid htime p hN hW hmargin (by
            simpa only [G] using! hxGood)
    have hbpos : 0 < b := by
      have hsepPos : 0 < annularSeparationGap N :=
        Nat.sqrt_pos.mpr (by
          unfold annularDepthAmbientSize
          omega)
      have hfloor :=
        annularSeparationGap_le_annularUpperRetainedDelayedSplitDepth
          hgrid htime (annularContractedUpperRetainedUpperTag p)
          (by omega)
      exact hsepPos.trans_le (by
        simpa only [b, annularContractedUpperRetainedDelayedDepth,
          annularContractedUpperRetainedUpperTag] using! hfloor)
    have hnonempty : selected.1 ≠ [] := by
      intro hempty
      have hlen : selected.1.length = 0 := by simp [hempty]
      rw [selected.2.1] at hlen
      omega
    let bounded : BoundedPositiveTerminalWord N :=
      ⟨selected.1, hnonempty, selected.2.2, hden⟩
    let w : ExactDepthBoundedPositiveWord N b :=
      ⟨bounded, selected.2.1⟩
    have hwToPositive : w.toPositive = selected := by
      rfl
    have hxDomain : x ∈ positivePrefixDomain b :=
      mem_positivePrefixDomain_of_nonterminating hxUnit hxNonterm
    have hxCylinder :
        x ∈ exactDepthBoundedCylinder w := by
      change x ∈ positivePrefixCylinder b w.toPositive
      rw [hwToPositive]
      exact selectedGaussPrefixWord_mem hxDomain
    have hwGood :
        w.toPositive ∈
          annularContractedUpperRetainedGoodWords eta rho N p := by
      simpa only [annularContractedUpperRetainedGoodWords,
        G, gaussDenominatorPrefixGoodEvent, Set.mem_preimage,
        b, hwToPositive] using! hxGood
    let e := annularContractedUpperRetainedPrefixOccurrenceEquiv p
    let s := annularContractedUpperRetainedCenterDepth p
    have hpoint :=
      norm_mixedPrefixCharacter_sub_affineFrozen_le_commonGoodEnvelope
        N hN
        (activeAnnularOccurrenceSignedLower k ε A)
        (activeAnnularOccurrenceSignedUpper k ε A)
        (abs_activeAnnularOccurrenceSignedLower_le
          hε hεA hgrid hsigned)
        (abs_activeAnnularOccurrenceSignedUpper_le
          hε hεA hgrid hsigned)
        hsmall k
        (unflattenedAnnularFourierMode p.1 (mode p.1))
        (annularContractedUpperRetainedRealization p).1
        (annularContractedUpperRetainedShallowDepth_le_delayed p)
        (annularContractedUpperRetainedPrefixOccurrence_depth_le_shallow
          hgrid htime p hN hW)
        w hwGood e
        (annularContractedUpperRetainedGoodWords eta rho N p)
        hwGood hxUnit hxNonterm hxCylinder
    have hsle :
        s ≤ b := by
      exact
        (annularContractedUpperRetainedCenterDepth_le_shallow
          hgrid htime p hN hW).trans
          (annularContractedUpperRetainedShallowDepth_le_delayed p)
    have hphaseMajorant :
        2 * Real.pi *
              |(N : ℝ) *
                gaussPrefixWordMixedPrefixCarrier N k
                  (unflattenedAnnularFourierMode p.1 (mode p.1))
                  (annularContractedUpperRetainedRealization p).1
                  b selected| *
              gaussPrefixGoodCylinderPhaseRadius b
                (annularDepthAmbientSize N)
                (upperGoodTransferDenominatorTolerance eta rho) ≤
            annularContractedUpperRetainedPhaseFreezingMajorant
              eta rho N k hr mode hmode p := by
      simpa only [
        annularContractedUpperRetainedPhaseFreezingMajorant,
        b, s, selected] using!
        (goodEnvelope_phaseCoefficient_le
          N k
          (unflattenedAnnularFourierMode p.1 (mode p.1))
          (annularContractedUpperRetainedRealization p).1
          hsle
          selected hwGood
          (fun z hz ↦ by
            simpa only using!
              annularContractedUpperRetained_nonzero_depth_le_center
                p z.1 hz))
    have hrawLe :
        annularContractedUpperRetainedCharacterFreezingEnvelope
            ε A eta rho N k hr mode hmode p x ≤
          annularContractedUpperRetainedDeterministicCharacterFreezingEnvelope
            ε A eta rho N k hr mode hmode p x := by
      unfold annularContractedUpperRetainedCharacterFreezingEnvelope
        annularContractedUpperRetainedDeterministicCharacterFreezingEnvelope
      apply oscillatoryPrefixFreezingEnvelope_le_of_phaseCoefficient_le
      simpa only [b, d, selected] using! hphaseMajorant
    rw [Set.indicator_of_mem hxGood]
    have hweight :
        ‖(gaussLebesguePrefixWeight x : ℂ)‖ ≤
          2 * Real.log 2 := by
      rw [Complex.norm_real, Real.norm_eq_abs]
      have hxIcc : x ∈ Icc (0 : ℝ) 1 :=
        ⟨hxUnit.1.le, hxUnit.2.le⟩
      have hbounds := gaussLebesguePrefixWeight_bounds hxIcc
      have hnonneg :
          0 ≤ gaussLebesguePrefixWeight x :=
        (Real.log_pos one_lt_two).le.trans hbounds.1
      simpa only [abs_of_nonneg hnonneg] using! hbounds.2
    have halgebra :
        (gaussLebesguePrefixWeight x : ℂ) *
              gaussPrefixMarkedMixedPrefixCharacter N
                (fun i ↦ compactValueMarkedRegion
                  (activeAnnularOccurrenceSignedLower k ε A i)
                  (activeAnnularOccurrenceSignedUpper k ε A i))
                k
                (unflattenedAnnularFourierMode p.1 (mode p.1))
                (annularContractedUpperRetainedRealization p).1
                (annularContractedUpperRetainedDelayedDepth p) x *
              annularContractedUpperRetainedFutureDigitBlock ε A p x -
            (gaussLebesguePrefixWeight x : ℂ) *
              gaussPrefixAffineFrozenCompactCharacter
                N
                (activeAnnularOccurrenceSignedLower k ε A)
                (activeAnnularOccurrenceSignedUpper k ε A)
                k
                (unflattenedAnnularFourierMode p.1 (mode p.1))
                (annularContractedUpperRetainedRealization p).1
                (annularContractedUpperRetainedDelayedDepth p)
                (annularContractedUpperRetainedGoodWords eta rho N p) x *
              annularContractedUpperRetainedFutureDigitBlock ε A p x =
          (gaussLebesguePrefixWeight x : ℂ) *
            (gaussPrefixMarkedMixedPrefixCharacter N
                (fun i ↦ compactValueMarkedRegion
                  (activeAnnularOccurrenceSignedLower k ε A i)
                  (activeAnnularOccurrenceSignedUpper k ε A i))
                k
                (unflattenedAnnularFourierMode p.1 (mode p.1))
                (annularContractedUpperRetainedRealization p).1
                (annularContractedUpperRetainedDelayedDepth p) x -
              gaussPrefixAffineFrozenCompactCharacter
                N
                (activeAnnularOccurrenceSignedLower k ε A)
                (activeAnnularOccurrenceSignedUpper k ε A)
                k
                (unflattenedAnnularFourierMode p.1 (mode p.1))
                (annularContractedUpperRetainedRealization p).1
                (annularContractedUpperRetainedDelayedDepth p)
                (annularContractedUpperRetainedGoodWords eta rho N p) x) *
            annularContractedUpperRetainedFutureDigitBlock ε A p x := by
      ring
    rw [halgebra, norm_mul, norm_mul]
    calc
      ‖(gaussLebesguePrefixWeight x : ℂ)‖ *
          ‖gaussPrefixMarkedMixedPrefixCharacter N
              (fun i ↦ compactValueMarkedRegion
                (activeAnnularOccurrenceSignedLower k ε A i)
                (activeAnnularOccurrenceSignedUpper k ε A i))
              k
              (unflattenedAnnularFourierMode p.1 (mode p.1))
              (annularContractedUpperRetainedRealization p).1
              (annularContractedUpperRetainedDelayedDepth p) x -
            gaussPrefixAffineFrozenCompactCharacter
              N
              (activeAnnularOccurrenceSignedLower k ε A)
              (activeAnnularOccurrenceSignedUpper k ε A)
              k
              (unflattenedAnnularFourierMode p.1 (mode p.1))
              (annularContractedUpperRetainedRealization p).1
              (annularContractedUpperRetainedDelayedDepth p)
              (annularContractedUpperRetainedGoodWords eta rho N p) x‖ *
          ‖annularContractedUpperRetainedFutureDigitBlock ε A p x‖ ≤
        (2 * Real.log 2) *
          annularContractedUpperRetainedDeterministicCharacterFreezingEnvelope
            ε A eta rho N k hr mode hmode p x *
          ‖annularContractedUpperRetainedFutureDigitBlock ε A p x‖ := by
        gcongr
        apply le_trans ?_ hrawLe
        simpa only [
          annularContractedUpperRetainedCharacterFreezingEnvelope,
          e, b, d, selected, hwToPositive] using! hpoint
      _ = (2 * Real.log 2) *
          annularContractedUpperRetainedJointFreezingEnvelope
            ε A eta rho N k hr mode hmode p x := by
        unfold annularContractedUpperRetainedJointFreezingEnvelope
        rw [Set.indicator_of_mem hxGood]
        ring
  · have hxNotWords :
        selectedGaussPrefixWord
            (annularContractedUpperRetainedDelayedDepth p) x ∉
          annularContractedUpperRetainedGoodWords eta rho N p := by
      simpa only [G, annularContractedUpperRetainedGoodWords,
        gaussDenominatorPrefixGoodEvent, Set.mem_preimage] using! hxGood
    rw [Set.indicator_of_notMem hxGood]
    unfold gaussPrefixAffineFrozenCompactCharacter
    dsimp only
    rw [if_neg hxNotWords]
    simp only [mul_zero, zero_mul, sub_zero, norm_zero]
    unfold annularContractedUpperRetainedJointFreezingEnvelope
    rw [Set.indicator_of_notMem hxGood]
    positivity

end

end Erdos1002
