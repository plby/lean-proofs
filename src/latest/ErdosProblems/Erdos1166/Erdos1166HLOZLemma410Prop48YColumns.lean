/- leanprover/lean4:v4.33.0 -/

import ErdosProblems.Erdos1166.Erdos1166HLOZColumnSourceConsumers
import ErdosProblems.Erdos1166.Erdos1166HLOZLemma410Prop48XDirections

/-!
# The two terminal column phases in HLOZ Lemma 4.10

This file assembles the separately conditioned forward and backward terminal
phases of the `Y` deletion.  Their stopped product laws are the theorems in
`Erdos1166HLOZColumnSourceConsumers`; the remaining source input is exactly a
branch cover by those literal atoms.  Only after the two phases have been
reunited do we reflect the full candidate event from `Y` to `Y'`.
-/

namespace Erdos1166.HLOZLemma410Prop48YColumns

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal Topology

open HLOZPairing HLOZPairingProfiles HLOZProp47Prop45YColumns
open HLOZColumnSourceConsumers HLOZLemma410Prop48Connector
open HLOZLemma410Prop48XDirections HLOZLemma410SourceBands
open HLOZLemma410SourceAbsorption HLOZProp47Parameters
open HLOZProp47SourceObjects HLOZProp47SourceAssembly HLOZBandRatios HLOZLemma411
open HLOZLemma411Recursion HLOZLemma412Windows
open HLOZProp48Truncated HLOZProp48SourceBands HLOZProp49Coordinate
open HLOZProp45SourceInterval HLOZProp45SourceMirrors
open HLOZProp45SourceEndpoints
open HLOZProp47Canonical HLOZPairing.ScreeningBridge
open HLOZLemma410PotentialRace HLOZProp47Lemma411412SourceAtoms
open HLOZProp47Lemma411412Connector

abbrev Path := ℕ → Site

/-! ## Theta-free source form for the two temporal phases of `Y` -/

def yLemma410Context
    (m : ℕ) (r : StageIndex) (alpha : ℝ) : Set Path :=
  prefixPairingEvent m yIndex (stageNumber r + 1) ∩
    hlozDirectAvoidanceEvent m (stageNumber r + 1) ∩
    distanceBinEvent m (stageNumber r) alpha

def yCandidateContextualFailure
    (C : ℝ) (m : ℕ) (r : StageIndex) (a : AlphaIndex)
    (j : SourceBetaBandIndex) : Set Path :=
  hlozCandidateCapFailureEvent
      (sourceLemma410Window m (alphaValue a)) m (stageNumber r)
      (sourceBetaCandidateThreshold m (alphaValue a) j)
      (sourceBetaCandidateCap C m (alphaValue a) j) ∩
    yLemma410Context m r (alphaValue a)

/-- Canonical tie-left half of the contextual column candidate failure.  The
small coefficient is used by the stopped Proposition-4.8 law; the separate
large coefficient on the full failure absorbs the domino and creation-site
losses. -/
def yLeftWinnerContextualFailure
    (C : ℝ) (m : ℕ) (r : StageIndex) (a : AlphaIndex)
    (j : SourceBetaBandIndex) : Set Path :=
  hlozLeftWinnerCandidateCapFailureEvent
      (sourceLemma410Window m (alphaValue a)) m (stageNumber r)
      (sourceBetaCandidateThreshold m (alphaValue a) j)
      (sourceLeftWinnerCandidateCap C m (alphaValue a) j) ∩
    yLemma410Context m r (alphaValue a)

/-- Canonical strict-right half of the contextual column candidate failure. -/
def yRightWinnerContextualFailure
    (C : ℝ) (m : ℕ) (r : StageIndex) (a : AlphaIndex)
    (j : SourceBetaBandIndex) : Set Path :=
  hlozRightWinnerCandidateCapFailureEvent
      (sourceLemma410Window m (alphaValue a)) m (stageNumber r)
      (sourceBetaCandidateThreshold m (alphaValue a) j)
      (sourceRightWinnerCandidateCap C m (alphaValue a) j) ∩
    yLemma410Context m r (alphaValue a)

/-- The generic active/free winner-cardinality split specialized to the
canonical `Y` prefix.  This is the column counterpart of the checked
`X`-east cover: the coefficient gap pays the factor two from domino closure
and the at-most-three creation sites. -/
theorem eventually_fullCandidateFailure_subset_smallWinnerFailures_y
    {Csmall Cfull : ℝ} (hsmall : 0 ≤ Csmall)
    (hgap : Csmall + 20 ≤ Cfull) :
    ∀ᶠ m : ℕ in atTop, ∀ r : StageIndex, ∀ a : AlphaIndex,
      alphaValue a ≤ kappaTwo → ∀ j : SourceBetaBandIndex,
      hlozCandidateCapFailureEvent
            (sourceLemma410Window m (alphaValue a)) m (stageNumber r)
            (sourceBetaCandidateThreshold m (alphaValue a) j)
            (sourceBetaCandidateCap Cfull m (alphaValue a) j) ∩
          prefixPairingEvent m yIndex (stageNumber r + 1) ⊆
        (hlozLeftWinnerCandidateCapFailureEvent
              (sourceLemma410Window m (alphaValue a)) m (stageNumber r)
              (sourceBetaCandidateThreshold m (alphaValue a) j)
              (sourceLeftWinnerCandidateCap Csmall m (alphaValue a) j) ∩
            prefixPairingEvent m yIndex (stageNumber r + 1)) ∪
          (hlozRightWinnerCandidateCapFailureEvent
              (sourceLemma410Window m (alphaValue a)) m (stageNumber r)
              (sourceBetaCandidateThreshold m (alphaValue a) j)
              (sourceRightWinnerCandidateCap Csmall m (alphaValue a) j) ∩
            prefixPairingEvent m yIndex (stageNumber r + 1)) := by
  filter_upwards [eventually_ge_atTop 2,
    eventually_two_mul_smallCandidateCap_add_stage_le_largeCandidateCap
      hsmall hgap] with m hm hcap
  intro r a ha j
  apply hlozCandidateCapFailureEvent_inter_subset_winnerFailure_union
      (sourceLemma410Window m (alphaValue a)) m (stageNumber r)
      (sourceBetaCandidateThreshold m (alphaValue a) j)
      (sourceBetaCandidateCap Cfull m (alphaValue a) j)
      (sourceLeftWinnerCandidateCap Csmall m (alphaValue a) j)
      (sourceRightWinnerCandidateCap Csmall m (alphaValue a) j)
      (prefixPairingEvent m yIndex (stageNumber r + 1))
  · omega
  · unfold stageNumber
    omega
  · intro s hs
    exact hs.1
  · rw [sourceLeftWinnerCandidateCap_add_right]
    exact hcap r a ha j

/-- Source-facing column data with no arbitrary forward/backward failure
sets and no caller-supplied union cover.  The two temporal terminal laws are
attached to the canonical tie-left and strict-right winner failures. -/
structure YCanonicalThetaFreeGoodBandData
    (cWindow m : ℕ) (C : ℝ) (r : StageIndex) (a : AlphaIndex)
    (j : SourceBetaBandIndex) where
  forward : ForwardColumnGoodBandDecomposition cWindow m C
    (sourceBeta (alphaValue a) j)
    (yLeftWinnerContextualFailure C m r a j)
    (prop45FailureEvent sourceCanonicalProfiles canonicalCStar
      m yIndex r (alphaValue a))
  backward : PrimedColumnGoodBandDecomposition cWindow m C
    (sourceBeta (alphaValue a) j)
    (yRightWinnerContextualFailure C m r a j)
    (prop45FailureEvent sourceCanonicalProfiles canonicalCStar
      m yIndex r (alphaValue a))

def Prop47Lemma410Prop48CanonicalThetaFreeYTwoPhaseLowBandInputs
    (cWindow : ℕ) (C : ℝ) : Prop :=
  ∀ᶠ m : ℕ in atTop, ∀ r : StageIndex, ∀ a : AlphaIndex,
    alphaValue a ≤ kappaTwo → ∀ j : SourceBetaBandIndex,
    sourceBeta (alphaValue a) j ≤ (7 : ℝ) / 10 →
    Nonempty (YCanonicalThetaFreeGoodBandData cWindow m C r a j)

/-! ### Literal changed-path source form

As in the checkerboard argument, the fixed-profile categorical package in
the preceding interface is stronger than necessary.  The two terminal
column phases already have literal equation-(4.47) path-switch atoms.  The
record below reuses those witnesses at the beta-band active coordinates and
retains only the two deterministic Proposition-4.8 pullbacks. -/

structure YCanonicalPathWitnessGoodBandData
    (cWindow m : ℕ) (witnessRate capCoeff : ℝ)
    (r : StageIndex) (a : AlphaIndex) (j : SourceBetaBandIndex) where
  forward : ℕ → ForwardColumnWinnerSource m
  backward : ℕ → PrimedColumnWinnerSource m
  forwardRemaining : ∀ eta,
    Equation447PathWitnessBranchRemainingData cWindow m witnessRate
      ((1 / 4 : ℝ) * Real.log (m : ℝ) ^ 2)
      (yLeftWinnerContextualFailure capCoeff m r a j)
      (forward eta).pathAtom (forward eta).profile
      (forward eta).lazyVector (forward eta).nextDirection
  backwardRemaining : ∀ eta,
    Equation447PathWitnessBranchRemainingData cWindow m witnessRate
      ((1 / 4 : ℝ) * Real.log (m : ℝ) ^ 2)
      (yRightWinnerContextualFailure capCoeff m r a j)
      (backward eta).pathAtom (backward eta).profile
      (backward eta).lazyVector (backward eta).nextDirection
  forward_failure : ∀ eta,
    yLeftWinnerContextualFailure capCoeff m r a j ∩
        (forward eta).pathAtom ⊆
      (fun s ↦ ((forward eta).lazyVector s,
        (forward eta).nextDirection s)) ⁻¹'
        (((sourceProfileQEvent m
            (sourceAlphaIntervalCount m (sourceBeta (alphaValue a) j))
            (forward eta).profile
            (geometricThreshold (Real.log (m : ℝ) ^ 2)
              (sourceLemma411GrowthFactor cWindow)
              (sourceAlphaIntervalCount m
                (sourceBeta (alphaValue a) j))) ∩
              (forwardRemaining eta).D)) ×ˢ
            (Set.univ : Set Direction))
  backward_failure : ∀ eta,
    yRightWinnerContextualFailure capCoeff m r a j ∩
        (backward eta).pathAtom ⊆
      (fun s ↦ ((backward eta).lazyVector s,
        (backward eta).nextDirection s)) ⁻¹'
        (((sourceProfileQEvent m
            (sourceAlphaIntervalCount m (sourceBeta (alphaValue a) j))
            (backward eta).profile
            (geometricThreshold (Real.log (m : ℝ) ^ 2)
              (sourceLemma411GrowthFactor cWindow)
              (sourceAlphaIntervalCount m
                (sourceBeta (alphaValue a) j))) ∩
              (backwardRemaining eta).D)) ×ˢ
            (Set.univ : Set Direction))
  forward_theta : ∀ eta,
    (yLeftWinnerContextualFailure capCoeff m r a j ∩
      (forward eta).pathAtom) ∩
        (fun s ↦ ((forward eta).lazyVector s,
          (forward eta).nextDirection s)) ⁻¹'
          (sourceProfileThetaUpTo cWindow m
            (sourceAlphaIntervalCount m (sourceBeta (alphaValue a) j))
            (forward eta).profile ×ˢ (Set.univ : Set Direction)) ⊆
      prop45FailureEvent sourceCanonicalProfiles canonicalCStar
        m yIndex r (alphaValue a)
  backward_theta : ∀ eta,
    (yRightWinnerContextualFailure capCoeff m r a j ∩
      (backward eta).pathAtom) ∩
        (fun s ↦ ((backward eta).lazyVector s,
          (backward eta).nextDirection s)) ⁻¹'
          (sourceProfileThetaUpTo cWindow m
            (sourceAlphaIntervalCount m (sourceBeta (alphaValue a) j))
            (backward eta).profile ×ˢ (Set.univ : Set Direction)) ⊆
      prop45FailureEvent sourceCanonicalProfiles canonicalCStar
        m yIndex r (alphaValue a)
  forward_cover : yLeftWinnerContextualFailure capCoeff m r a j ⊆
    ⋃ eta, (forward eta).pathAtom
  backward_cover : yRightWinnerContextualFailure capCoeff m r a j ⊆
    ⋃ eta, (backward eta).pathAtom
  forward_disjoint : Pairwise fun eta zeta ↦
    Disjoint (forward eta).pathAtom (forward zeta).pathAtom
  backward_disjoint : Pairwise fun eta zeta ↦
    Disjoint (backward eta).pathAtom (backward zeta).pathAtom

namespace YCanonicalPathWitnessGoodBandData

variable {cWindow m : ℕ} {witnessRate capCoeff : ℝ}
  {r : StageIndex} {a : AlphaIndex} {j : SourceBetaBandIndex}
  (D : YCanonicalPathWitnessGoodBandData
    cWindow m witnessRate capCoeff r a j)

noncomputable def forwardAtom (eta : ℕ) :
    StoppedEquation447PathWitnessBranchAtom cWindow m witnessRate
      (yLeftWinnerContextualFailure capCoeff m r a j)
      ((1 / 4 : ℝ) * Real.log (m : ℝ) ^ 2) :=
  (D.forward eta).toStoppedEquation447PathWitnessBranchAtom
    cWindow witnessRate ((1 / 4 : ℝ) * Real.log (m : ℝ) ^ 2)
    (yLeftWinnerContextualFailure capCoeff m r a j)
    (D.forwardRemaining eta)

noncomputable def backwardAtom (eta : ℕ) :
    StoppedEquation447PathWitnessBranchAtom cWindow m witnessRate
      (yRightWinnerContextualFailure capCoeff m r a j)
      ((1 / 4 : ℝ) * Real.log (m : ℝ) ^ 2) :=
  (D.backward eta).toStoppedEquation447PathWitnessBranchAtom
    cWindow witnessRate ((1 / 4 : ℝ) * Real.log (m : ℝ) ^ 2)
    (yRightWinnerContextualFailure capCoeff m r a j)
    (D.backwardRemaining eta)

@[simp] theorem forwardAtom_pathAtom (eta : ℕ) :
    (D.forwardAtom eta).pathAtom = (D.forward eta).pathAtom := by
  rfl

@[simp] theorem backwardAtom_pathAtom (eta : ℕ) :
    (D.backwardAtom eta).pathAtom = (D.backward eta).pathAtom := by
  rfl

/-- The two literal terminal phases satisfy the good-band estimate using
the same changed-path base step as equation (4.47). -/
theorem measure_diff_le
    {cWindow m : ℕ} {witnessRate capCoeff cBase : ℝ}
    {r : StageIndex} {a : AlphaIndex} {j : SourceBetaBandIndex}
    (D : YCanonicalPathWitnessGoodBandData
      cWindow m witnessRate capCoeff r a j)
    (G : SourceProp48NumericalAt cWindow m cBase 1 1)
    (hwitnessRate : 0 < witnessRate)
    (halpha : kappaOne ≤ sourceBeta (alphaValue a) j)
    (hAlpha : sourceBeta (alphaValue a) j ≤ (4 : ℝ) / 5)
    (hbaseAbsorb :
      4 * (Real.exp (-witnessRate *
          ((1 / 4 : ℝ) * Real.log (m : ℝ) ^ 2)) *
        (1 - Real.exp (-witnessRate))⁻¹) ≤
          Real.exp (-cBase * Real.log (m : ℝ) ^ 2))
    (tail : ℝ≥0∞)
    (hshift : ENNReal.ofReal (Real.exp (-(min cBase
      (imbalanceRate (Real.exp
        (sourceAdjacentComparisonExponent cWindow))) / 2) *
          Real.log (m : ℝ) ^ 2)) ≤ tail) :
    simpleRandomWalkLaw
        (yLeftWinnerContextualFailure capCoeff m r a j \
          prop45FailureEvent sourceCanonicalProfiles canonicalCStar
            m yIndex r (alphaValue a)) ≤ tail ∧
      simpleRandomWalkLaw
        (yRightWinnerContextualFailure capCoeff m r a j \
          prop45FailureEvent sourceCanonicalProfiles canonicalCStar
            m yIndex r (alphaValue a)) ≤ tail := by
  have hrho : (1 / 4 : ℝ) * Real.log (m : ℝ) ^ 2 ≤
      Real.log (m : ℝ) ^ 2 := by
    nlinarith [sq_nonneg (Real.log (m : ℝ))]
  constructor
  · exact measure_diff_le_of_pathWitnessGoodBandAtoms
      D.forwardAtom D.forward_cover D.forward_disjoint G
      hwitnessRate halpha hAlpha hrho D.forward_failure
      D.forward_theta hbaseAbsorb tail hshift
  · exact measure_diff_le_of_pathWitnessGoodBandAtoms
      D.backwardAtom D.backward_cover D.backward_disjoint G
      hwitnessRate halpha hAlpha hrho D.backward_failure
      D.backward_theta hbaseAbsorb tail hshift

end YCanonicalPathWitnessGoodBandData

def Prop47Lemma410Prop48CanonicalPathWitnessYTwoPhaseLowBandInputs
    (cWindow : ℕ) (witnessRate capCoeff : ℝ) : Prop :=
  ∀ᶠ m : ℕ in atTop, ∀ r : StageIndex, ∀ a : AlphaIndex,
    alphaValue a ≤ kappaTwo → ∀ j : SourceBetaBandIndex,
    sourceBeta (alphaValue a) j ≤ (7 : ℝ) / 10 →
    Nonempty (YCanonicalPathWitnessGoodBandData
      cWindow m witnessRate capCoeff r a j)

/-- The two literal temporal column phases, after removal of one global
Proposition-4.5 event.  The atom records retain only equation-(4.47) coded
data and deterministic event inclusions. -/
structure YTwoPhaseThetaFreeGoodBandData
    (cWindow m : ℕ) (C : ℝ) (r : StageIndex) (a : AlphaIndex)
    (j : SourceBetaBandIndex) where
  forwardFailure : Set Path
  backwardFailure : Set Path
  cover : yCandidateContextualFailure C m r a j ⊆
    forwardFailure ∪ backwardFailure
  forward : ForwardColumnGoodBandDecomposition cWindow m C
    (sourceBeta (alphaValue a) j) forwardFailure
    (prop45FailureEvent sourceCanonicalProfiles canonicalCStar
      m yIndex r (alphaValue a))
  backward : PrimedColumnGoodBandDecomposition cWindow m C
    (sourceBeta (alphaValue a) j) backwardFailure
    (prop45FailureEvent sourceCanonicalProfiles canonicalCStar
      m yIndex r (alphaValue a))

def Prop47Lemma410Prop48ThetaFreeYTwoPhaseLowBandInputs
    (cWindow : ℕ) (C : ℝ) : Prop :=
  ∀ᶠ m : ℕ in atTop, ∀ r : StageIndex, ∀ a : AlphaIndex,
    alphaValue a ≤ kappaTwo → ∀ j : SourceBetaBandIndex,
    sourceBeta (alphaValue a) j ≤ (7 : ℝ) / 10 →
    Nonempty (YTwoPhaseThetaFreeGoodBandData cWindow m C r a j)

/-- Strong atom-conditioned alternative to the global theta-free column
package.  Every forward/backward terminal atom carries one
arbitrary-endpoint Proposition-4.5 input for every recursive profile
interval.  Since stopped conditioning truncates the holding law, the final
literal source closure deliberately uses the theta-free package instead. -/
structure YTwoPhaseSourceBandedGoodBandData
    (cWindow m : ℕ) (C : ℝ) (r : StageIndex) (a : AlphaIndex)
    (j : SourceBetaBandIndex) where
  forwardFailure : Set Path
  backwardFailure : Set Path
  cover : yCandidateContextualFailure C m r a j ⊆
    forwardFailure ∪ backwardFailure
  forward : ForwardColumnSourceBandedGoodBandDecomposition cWindow m C
    (sourceBeta (alphaValue a) j) forwardFailure
  backward : PrimedColumnSourceBandedGoodBandDecomposition cWindow m C
    (sourceBeta (alphaValue a) j) backwardFailure

def Prop47Lemma410Prop48SourceBandedYTwoPhaseLowBandInputs
    (cWindow : ℕ) (C : ℝ) : Prop :=
  ∀ᶠ m : ℕ in atTop, ∀ r : StageIndex, ∀ a : AlphaIndex,
    alphaValue a ≤ kappaTwo → ∀ j : SourceBetaBandIndex,
    sourceBeta (alphaValue a) j ≤ (7 : ℝ) / 10 →
    Nonempty (YTwoPhaseSourceBandedGoodBandData cWindow m C r a j)

/-- The two stopped temporal phases control the contextual candidate event
outside the single global theta event.  Equation (4.47) supplies the base
probability internally; only the two-phase union costs one exponent
doubling. -/
theorem prop47Lemma410Prop48ThetaFree_y_lowBands
    (cWindow : ℕ) {C d : ℝ}
    (hC : 0 < C) (hd : 0 < d)
    (hcompare : 8 * d ≤
      min (Real.log ((C + 1) / C) / 2)
        (imbalanceRate
          (Real.exp (sourceAdjacentComparisonExponent cWindow))) / 2)
    (h : Prop47Lemma410Prop48ThetaFreeYTwoPhaseLowBandInputs cWindow C) :
    ∀ᶠ m : ℕ in atTop, ∀ r : StageIndex, ∀ a : AlphaIndex,
      alphaValue a ≤ kappaTwo → ∀ j : SourceBetaBandIndex,
      sourceBeta (alphaValue a) j ≤ (7 : ℝ) / 10 →
      simpleRandomWalkLaw
          (yCandidateContextualFailure C m r a j \
            prop45FailureEvent sourceCanonicalProfiles canonicalCStar
              m yIndex r (alphaValue a)) ≤
        sourceBetaCandidateTail d m := by
  let cBase := Real.log ((C + 1) / C) / 2
  have hratio : 1 < (C + 1) / C := by
    rw [one_lt_div hC]
    linarith
  have hcBase : 0 < cBase := by
    dsimp [cBase]
    exact div_pos (Real.log_pos hratio) (by norm_num)
  have hgood := eventually_sourceProp48NumericalAt cWindow hcBase
    (show (0 : ℝ) < 1 by norm_num) (show (0 : ℝ) < 1 by norm_num)
  have hbase := eventually_equation447_logSq_profile_base_absorb hC
  have hshift := eventually_prop48Rate_le_sourceBetaCandidateTail
    (rate := min cBase
      (imbalanceRate
        (Real.exp (sourceAdjacentComparisonExponent cWindow))) / 2)
    (d := 2 * d) (by positivity) (by
      dsimp [cBase] at hcompare ⊢
      nlinarith [hcompare])
  have habsorb := eventually_two_mul_sourceBetaCandidateTail_two_mul_le hd
  filter_upwards [h, hgood, hbase, hshift, habsorb] with
      m hm hgoodM hbaseM hshiftM habsorbM
  intro r a ha j hj
  rcases hm r a ha j hj with ⟨D⟩
  have halpha : kappaOne ≤ sourceBeta (alphaValue a) j :=
    kappaOne_le_sourceBeta ha j
  have hAlpha : sourceBeta (alphaValue a) j ≤ (4 : ℝ) / 5 :=
    hj.trans (by norm_num)
  have hforwardRaw :=
    measure_diff_le_of_forwardColumnGoodBandDecomposition D.forward
      hgoodM hC halpha hAlpha (by
        dsimp [cBase]
        exact hbaseM)
      (sourceBetaCandidateTail (2 * d) m) hshiftM
  have hbackwardRaw :=
    measure_diff_le_of_primedColumnGoodBandDecomposition D.backward
      hgoodM hC halpha hAlpha (by
        dsimp [cBase]
        exact hbaseM)
      (sourceBetaCandidateTail (2 * d) m) hshiftM
  let theta := prop45FailureEvent sourceCanonicalProfiles canonicalCStar
    m yIndex r (alphaValue a)
  have hforward : simpleRandomWalkLaw (D.forwardFailure \ theta) ≤
      sourceBetaCandidateTail (2 * d) m := by
    simpa only [theta] using hforwardRaw
  have hbackward : simpleRandomWalkLaw (D.backwardFailure \ theta) ≤
      sourceBetaCandidateTail (2 * d) m := by
    simpa only [theta] using hbackwardRaw
  calc
    simpleRandomWalkLaw
        (yCandidateContextualFailure C m r a j \ theta) ≤
      simpleRandomWalkLaw
        ((D.forwardFailure \ theta) ∪ (D.backwardFailure \ theta)) := by
        apply measure_mono
        intro omega homega
        rcases D.cover homega.1 with hforward' | hbackward'
        · exact Or.inl ⟨hforward', homega.2⟩
        · exact Or.inr ⟨hbackward', homega.2⟩
    _ ≤ simpleRandomWalkLaw (D.forwardFailure \ theta) +
        simpleRandomWalkLaw (D.backwardFailure \ theta) :=
      measure_union_le _ _
    _ ≤ sourceBetaCandidateTail (2 * d) m +
        sourceBetaCandidateTail (2 * d) m :=
      add_le_add hforward hbackward
    _ = 2 * sourceBetaCandidateTail (2 * d) m := by ring
    _ ≤ sourceBetaCandidateTail d m := habsorbM

/-- Canonical theta-free column estimate.  Unlike the legacy wrapper above,
the source package supplies no arbitrary phase events or union cover: the
checked active/free winner split covers the large-coefficient candidate
failure by the small-coefficient tie-left and strict-right failures. -/
theorem prop47Lemma410Prop48CanonicalThetaFree_y_lowBands
    (cWindow : ℕ) {Csmall Cfull d : ℝ}
    (hCsmall : 0 < Csmall) (hgap : Csmall + 20 ≤ Cfull)
    (hd : 0 < d)
    (hcompare : 8 * d ≤
      min (Real.log ((Csmall + 1) / Csmall) / 2)
        (imbalanceRate
          (Real.exp (sourceAdjacentComparisonExponent cWindow))) / 2)
    (h : Prop47Lemma410Prop48CanonicalThetaFreeYTwoPhaseLowBandInputs
      cWindow Csmall) :
    ∀ᶠ m : ℕ in atTop, ∀ r : StageIndex, ∀ a : AlphaIndex,
      alphaValue a ≤ kappaTwo → ∀ j : SourceBetaBandIndex,
      sourceBeta (alphaValue a) j ≤ (7 : ℝ) / 10 →
      simpleRandomWalkLaw
          (yCandidateContextualFailure Cfull m r a j \
            prop45FailureEvent sourceCanonicalProfiles canonicalCStar
              m yIndex r (alphaValue a)) ≤
        sourceBetaCandidateTail d m := by
  let cBase := Real.log ((Csmall + 1) / Csmall) / 2
  have hratio : 1 < (Csmall + 1) / Csmall := by
    rw [one_lt_div hCsmall]
    linarith
  have hcBase : 0 < cBase := by
    dsimp [cBase]
    exact div_pos (Real.log_pos hratio) (by norm_num)
  have hgood := eventually_sourceProp48NumericalAt cWindow hcBase
    (show (0 : ℝ) < 1 by norm_num) (show (0 : ℝ) < 1 by norm_num)
  have hbase := eventually_equation447_logSq_profile_base_absorb hCsmall
  have hshift := eventually_prop48Rate_le_sourceBetaCandidateTail
    (rate := min cBase
      (imbalanceRate
        (Real.exp (sourceAdjacentComparisonExponent cWindow))) / 2)
    (d := 2 * d) (by positivity) (by
      dsimp [cBase] at hcompare ⊢
      nlinarith [hcompare])
  have habsorb := eventually_two_mul_sourceBetaCandidateTail_two_mul_le hd
  have hcover :=
    eventually_fullCandidateFailure_subset_smallWinnerFailures_y
      hCsmall.le hgap
  filter_upwards [h, hgood, hbase, hshift, habsorb, hcover] with
      m hm hgoodM hbaseM hshiftM habsorbM hcoverM
  intro r a ha j hj
  rcases hm r a ha j hj with ⟨D⟩
  have halpha : kappaOne ≤ sourceBeta (alphaValue a) j :=
    kappaOne_le_sourceBeta ha j
  have hAlpha : sourceBeta (alphaValue a) j ≤ (4 : ℝ) / 5 :=
    hj.trans (by norm_num)
  have hforwardRaw :=
    measure_diff_le_of_forwardColumnGoodBandDecomposition D.forward
      hgoodM hCsmall halpha hAlpha (by
        dsimp [cBase]
        exact hbaseM)
      (sourceBetaCandidateTail (2 * d) m) hshiftM
  have hbackwardRaw :=
    measure_diff_le_of_primedColumnGoodBandDecomposition D.backward
      hgoodM hCsmall halpha hAlpha (by
        dsimp [cBase]
        exact hbaseM)
      (sourceBetaCandidateTail (2 * d) m) hshiftM
  let theta := prop45FailureEvent sourceCanonicalProfiles canonicalCStar
    m yIndex r (alphaValue a)
  have hforward : simpleRandomWalkLaw
      (yLeftWinnerContextualFailure Csmall m r a j \ theta) ≤
      sourceBetaCandidateTail (2 * d) m := by
    simpa only [theta] using hforwardRaw
  have hbackward : simpleRandomWalkLaw
      (yRightWinnerContextualFailure Csmall m r a j \ theta) ≤
      sourceBetaCandidateTail (2 * d) m := by
    simpa only [theta] using hbackwardRaw
  have hcontextCover : yCandidateContextualFailure Cfull m r a j ⊆
      yLeftWinnerContextualFailure Csmall m r a j ∪
        yRightWinnerContextualFailure Csmall m r a j := by
    intro omega homega
    have hprefix : omega ∈
        hlozCandidateCapFailureEvent
              (sourceLemma410Window m (alphaValue a)) m (stageNumber r)
              (sourceBetaCandidateThreshold m (alphaValue a) j)
              (sourceBetaCandidateCap Cfull m (alphaValue a) j) ∩
            prefixPairingEvent m yIndex (stageNumber r + 1) := by
      exact ⟨homega.1, homega.2.1.1⟩
    rcases hcoverM r a ha j hprefix with hleft | hright
    · exact Or.inl ⟨hleft.1, homega.2⟩
    · exact Or.inr ⟨hright.1, homega.2⟩
  calc
    simpleRandomWalkLaw
        (yCandidateContextualFailure Cfull m r a j \ theta) ≤
      simpleRandomWalkLaw
        ((yLeftWinnerContextualFailure Csmall m r a j \ theta) ∪
          (yRightWinnerContextualFailure Csmall m r a j \ theta)) := by
        apply measure_mono
        intro omega homega
        rcases hcontextCover homega.1 with hleft | hright
        · exact Or.inl ⟨hleft, homega.2⟩
        · exact Or.inr ⟨hright, homega.2⟩
    _ ≤ simpleRandomWalkLaw
          (yLeftWinnerContextualFailure Csmall m r a j \ theta) +
        simpleRandomWalkLaw
          (yRightWinnerContextualFailure Csmall m r a j \ theta) :=
      measure_union_le _ _
    _ ≤ sourceBetaCandidateTail (2 * d) m +
        sourceBetaCandidateTail (2 * d) m :=
      add_le_add hforward hbackward
    _ = 2 * sourceBetaCandidateTail (2 * d) m := by ring
    _ ≤ sourceBetaCandidateTail d m := habsorbM

/-- Canonical low-band column estimate from the literal changed-path
witness.  The two terminal phases are the only finite union after the
atomwise Proposition-4.8 estimate. -/
theorem prop47Lemma410Prop48PathWitness_y_lowBands
    (cWindow : ℕ) {witnessRate Csmall Cfull d : ℝ}
    (hwitnessRate : 0 < witnessRate)
    (hCsmall : 0 < Csmall) (hgap : Csmall + 20 ≤ Cfull)
    (hd : 0 < d)
    (hcompare : 8 * d ≤
      min (witnessRate / 8)
        (imbalanceRate
          (Real.exp (sourceAdjacentComparisonExponent cWindow))) / 2)
    (h : Prop47Lemma410Prop48CanonicalPathWitnessYTwoPhaseLowBandInputs
      cWindow witnessRate Csmall) :
    ∀ᶠ m : ℕ in atTop, ∀ r : StageIndex, ∀ a : AlphaIndex,
      alphaValue a ≤ kappaTwo → ∀ j : SourceBetaBandIndex,
      sourceBeta (alphaValue a) j ≤ (7 : ℝ) / 10 →
      simpleRandomWalkLaw
          (yCandidateContextualFailure Cfull m r a j \
            prop45FailureEvent sourceCanonicalProfiles canonicalCStar
              m yIndex r (alphaValue a)) ≤
        sourceBetaCandidateTail d m := by
  let cBase := witnessRate / 8
  have hcBase : 0 < cBase := by
    dsimp [cBase]
    positivity
  have hgood := eventually_sourceProp48NumericalAt cWindow hcBase
    (show (0 : ℝ) < 1 by norm_num) (show (0 : ℝ) < 1 by norm_num)
  have hbase := eventually_pathWitnessEquation447_error_absorb
    hwitnessRate (show (0 : ℝ) < 1 / 4 by norm_num)
  have hshift := eventually_prop48Rate_le_sourceBetaCandidateTail
    (rate := min cBase
      (imbalanceRate
        (Real.exp (sourceAdjacentComparisonExponent cWindow))) / 2)
    (d := 2 * d) (by positivity) (by
      dsimp [cBase] at hcompare ⊢
      nlinarith [hcompare])
  have habsorb := eventually_two_mul_sourceBetaCandidateTail_two_mul_le hd
  have hcover :=
    eventually_fullCandidateFailure_subset_smallWinnerFailures_y
      hCsmall.le hgap
  filter_upwards [h, hgood, hbase, hshift, habsorb, hcover] with
      m hm hgoodM hbaseM hshiftM habsorbM hcoverM
  intro r a ha j hj
  rcases hm r a ha j hj with ⟨D⟩
  have halpha : kappaOne ≤ sourceBeta (alphaValue a) j :=
    kappaOne_le_sourceBeta ha j
  have hAlpha : sourceBeta (alphaValue a) j ≤ (4 : ℝ) / 5 :=
    hj.trans (by norm_num)
  have hbaseM' :
      4 * (Real.exp (-witnessRate *
          ((1 / 4 : ℝ) * Real.log (m : ℝ) ^ 2)) *
        (1 - Real.exp (-witnessRate))⁻¹) ≤
          Real.exp (-cBase * Real.log (m : ℝ) ^ 2) := by
    have hraw := hbaseM
      ((1 / 4 : ℝ) * Real.log (m : ℝ) ^ 2) (le_refl _)
    dsimp [cBase]
    convert hraw using 1 <;> ring
  let tailTwo := sourceBetaCandidateTail (2 * d) m
  have hbranches := D.measure_diff_le hgoodM hwitnessRate halpha hAlpha
    hbaseM' tailTwo (by simpa only [tailTwo] using hshiftM)
  rcases hbranches with ⟨hforward, hbackward⟩
  let theta := prop45FailureEvent sourceCanonicalProfiles canonicalCStar
    m yIndex r (alphaValue a)
  have hcontextCover : yCandidateContextualFailure Cfull m r a j ⊆
      yLeftWinnerContextualFailure Csmall m r a j ∪
        yRightWinnerContextualFailure Csmall m r a j := by
    intro omega homega
    have hprefix : omega ∈
        hlozCandidateCapFailureEvent
              (sourceLemma410Window m (alphaValue a)) m (stageNumber r)
              (sourceBetaCandidateThreshold m (alphaValue a) j)
              (sourceBetaCandidateCap Cfull m (alphaValue a) j) ∩
            prefixPairingEvent m yIndex (stageNumber r + 1) := by
      exact ⟨homega.1, homega.2.1.1⟩
    rcases hcoverM r a ha j hprefix with hleft | hright
    · exact Or.inl ⟨hleft.1, homega.2⟩
    · exact Or.inr ⟨hright.1, homega.2⟩
  calc
    simpleRandomWalkLaw
        (yCandidateContextualFailure Cfull m r a j \ theta) ≤
      simpleRandomWalkLaw
        ((yLeftWinnerContextualFailure Csmall m r a j \ theta) ∪
          (yRightWinnerContextualFailure Csmall m r a j \ theta)) := by
        apply measure_mono
        intro omega homega
        rcases hcontextCover homega.1 with hleft | hright
        · exact Or.inl ⟨hleft, homega.2⟩
        · exact Or.inr ⟨hright, homega.2⟩
    _ ≤ simpleRandomWalkLaw
          (yLeftWinnerContextualFailure Csmall m r a j \ theta) +
        simpleRandomWalkLaw
          (yRightWinnerContextualFailure Csmall m r a j \ theta) :=
      measure_union_le _ _
    _ ≤ tailTwo + tailTwo := add_le_add
      (by simpa only [theta] using hforward)
      (by simpa only [theta] using hbackward)
    _ = 2 * sourceBetaCandidateTail (2 * d) m := by
      dsimp [tailTwo]
      ring
    _ ≤ sourceBetaCandidateTail d m := habsorbM

/-- Source-banded low-band estimate for the two terminal phases of `Y`.
The polynomial number of recursive theta intervals is absorbed within each
phase; the only remaining finite union is forward versus backward. -/
theorem prop47Lemma410Prop48SourceBanded_y_lowBands
    (cWindow : ℕ) {C d : ℝ}
    (hC : 0 < C) (hd : 0 < d)
    (hcompare : 16 * d ≤
      min (Real.log ((C + 1) / C) / 2)
        (imbalanceRate
          (Real.exp (sourceAdjacentComparisonExponent cWindow))) / 2)
    (h : Prop47Lemma410Prop48SourceBandedYTwoPhaseLowBandInputs
      cWindow C) :
    ∀ᶠ m : ℕ in atTop, ∀ r : StageIndex, ∀ a : AlphaIndex,
      alphaValue a ≤ kappaTwo → ∀ j : SourceBetaBandIndex,
      sourceBeta (alphaValue a) j ≤ (7 : ℝ) / 10 →
      simpleRandomWalkLaw (yCandidateContextualFailure C m r a j) ≤
        sourceBetaCandidateTail d m := by
  let cBase := Real.log ((C + 1) / C) / 2
  have hratio : 1 < (C + 1) / C := by
    rw [one_lt_div hC]
    linarith
  have hcBase : 0 < cBase := by
    dsimp [cBase]
    exact div_pos (Real.log_pos hratio) (by norm_num)
  have hgood := eventually_sourceProp48NumericalAt cWindow hcBase
    (show (0 : ℝ) < 1 by norm_num) (show (0 : ℝ) < 1 by norm_num)
  have hbase := eventually_equation447_logSq_profile_base_absorb hC
  have hshift := eventually_prop48Rate_le_sourceBetaCandidateTail
    (rate := min cBase
      (imbalanceRate
        (Real.exp (sourceAdjacentComparisonExponent cWindow))) / 2)
    (d := 4 * d) (by positivity) (by
      dsimp [cBase] at hcompare ⊢
      nlinarith [hcompare])
  have htheta :=
    eventually_intervalCount_mul_sourceProp45Error_le_candidateTail
      (show 0 < 4 * d by positivity)
  have habsorbFour :=
    eventually_two_mul_sourceBetaCandidateTail_two_mul_le
      (show 0 < 2 * d by positivity)
  have habsorbTwo := eventually_two_mul_sourceBetaCandidateTail_two_mul_le hd
  have hscales := eventually_sourceRecursiveEndpointScales
  filter_upwards [h, hgood, hbase, hshift, htheta, habsorbFour,
      habsorbTwo, hscales] with m hm hgoodM hbaseM hshiftM hthetaM
        habsorbFourM habsorbTwoM hscalesM
  intro r a ha j hj
  rcases hm r a ha j hj with ⟨D⟩
  have halpha : kappaOne ≤ sourceBeta (alphaValue a) j :=
    kappaOne_le_sourceBeta ha j
  have hAlpha : sourceBeta (alphaValue a) j ≤ (4 : ℝ) / 5 :=
    hj.trans (by norm_num)
  have hbandScales (l : Fin
      (sourceAlphaIntervalCount m (sourceBeta (alphaValue a) j))) :
      SourceIntervalScale m (sourceIntervalLower m (l.1 + 1)) ∧
        SourceUpperScale m (sourceThetaIntervalUpper m (l.1 + 1)) := by
    exact hscalesM (sourceBeta (alphaValue a) j) (l.1 + 1)
      halpha hj (by omega) (by omega)
  let tailFour := sourceBetaCandidateTail (4 * d) m
  let tailTwo := sourceBetaCandidateTail (2 * d) m
  let thetaError :=
    (sourceAlphaIntervalCount m (sourceBeta (alphaValue a) j) : ℝ≥0∞) *
      sourceProp45FourBranchError m
  have hthetaError : thetaError ≤ tailFour := by
    dsimp [thetaError, tailFour]
    exact hthetaM (sourceBeta (alphaValue a) j) hAlpha
  have hforwardRaw := D.forward.measure_le hgoodM hC halpha hAlpha
    hbandScales (by
      dsimp [cBase]
      exact hbaseM) tailFour (by
        dsimp [tailFour]
        exact hshiftM)
  have hbackwardRaw := D.backward.measure_le hgoodM hC halpha hAlpha
    hbandScales (by
      dsimp [cBase]
      exact hbaseM) tailFour (by
        dsimp [tailFour]
        exact hshiftM)
  have hphaseAbsorb : tailFour + thetaError ≤ tailTwo := by
    calc
      tailFour + thetaError ≤ tailFour + tailFour := by gcongr
      _ = 2 * tailFour := by ring
      _ ≤ tailTwo := by
        dsimp [tailFour, tailTwo]
        have h4 : 2 * (2 * d) = 4 * d := by ring
        simpa only [h4] using habsorbFourM
  have hforward : simpleRandomWalkLaw D.forwardFailure ≤ tailTwo :=
    hforwardRaw.trans (by simpa only [thetaError] using hphaseAbsorb)
  have hbackward : simpleRandomWalkLaw D.backwardFailure ≤ tailTwo :=
    hbackwardRaw.trans (by simpa only [thetaError] using hphaseAbsorb)
  calc
    simpleRandomWalkLaw (yCandidateContextualFailure C m r a j) ≤
        simpleRandomWalkLaw (D.forwardFailure ∪ D.backwardFailure) :=
      measure_mono D.cover
    _ ≤ simpleRandomWalkLaw D.forwardFailure +
        simpleRandomWalkLaw D.backwardFailure := measure_union_le _ _
    _ ≤ tailTwo + tailTwo := add_le_add hforward hbackward
    _ = 2 * tailTwo := by ring
    _ ≤ sourceBetaCandidateTail d m := by
      simpa only [tailTwo, mul_assoc] using habsorbTwoM

/-- The high beta bands are deterministically empty. -/
theorem prop47Lemma410Prop48ThetaFree_y
    (cWindow : ℕ) {C d : ℝ}
    (hC : 0 < C) (hd : 0 < d)
    (hcompare : 8 * d ≤
      min (Real.log ((C + 1) / C) / 2)
        (imbalanceRate
          (Real.exp (sourceAdjacentComparisonExponent cWindow))) / 2)
    (h : Prop47Lemma410Prop48ThetaFreeYTwoPhaseLowBandInputs cWindow C) :
    ∀ᶠ m : ℕ in atTop, ∀ r : StageIndex, ∀ a : AlphaIndex,
      alphaValue a ≤ kappaTwo → ∀ j : SourceBetaBandIndex,
      simpleRandomWalkLaw
          (yCandidateContextualFailure C m r a j \
            prop45FailureEvent sourceCanonicalProfiles canonicalCStar
              m yIndex r (alphaValue a)) ≤
        sourceBetaCandidateTail d m := by
  have hlow := prop47Lemma410Prop48ThetaFree_y_lowBands cWindow
    hC hd hcompare h
  have hhigh := eventually_hlozCandidateCapFailureEvent_eq_empty_highBands hC
  filter_upwards [hlow, hhigh] with m hlowM hhighM
  intro r a ha j
  by_cases hj : sourceBeta (alphaValue a) j ≤ (7 : ℝ) / 10
  · exact hlowM r a ha j hj
  · have hempty := hhighM r a ha j (lt_of_not_ge hj)
    rw [yCandidateContextualFailure, hempty, empty_inter, empty_diff,
      measure_empty]
    exact bot_le

/-- The canonical winner split plus the deterministic high-band estimate
controls all source beta bands at the large final coefficient. -/
theorem prop47Lemma410Prop48CanonicalThetaFree_y
    (cWindow : ℕ) {Csmall Cfull d : ℝ}
    (hCsmall : 0 < Csmall) (hgap : Csmall + 20 ≤ Cfull)
    (hd : 0 < d)
    (hcompare : 8 * d ≤
      min (Real.log ((Csmall + 1) / Csmall) / 2)
        (imbalanceRate
          (Real.exp (sourceAdjacentComparisonExponent cWindow))) / 2)
    (h : Prop47Lemma410Prop48CanonicalThetaFreeYTwoPhaseLowBandInputs
      cWindow Csmall) :
    ∀ᶠ m : ℕ in atTop, ∀ r : StageIndex, ∀ a : AlphaIndex,
      alphaValue a ≤ kappaTwo → ∀ j : SourceBetaBandIndex,
      simpleRandomWalkLaw
          (yCandidateContextualFailure Cfull m r a j \
            prop45FailureEvent sourceCanonicalProfiles canonicalCStar
              m yIndex r (alphaValue a)) ≤
        sourceBetaCandidateTail d m := by
  have hlow := prop47Lemma410Prop48CanonicalThetaFree_y_lowBands cWindow
    hCsmall hgap hd hcompare h
  have hCfull : 0 < Cfull := by linarith
  have hhigh :=
    eventually_hlozCandidateCapFailureEvent_eq_empty_highBands hCfull
  filter_upwards [hlow, hhigh] with m hlowM hhighM
  intro r a ha j
  by_cases hj : sourceBeta (alphaValue a) j ≤ (7 : ℝ) / 10
  · exact hlowM r a ha j hj
  · have hempty := hhighM r a ha j (lt_of_not_ge hj)
    rw [yCandidateContextualFailure, hempty, empty_inter, empty_diff,
      measure_empty]
    exact bot_le

/-- Deterministic high-band emptiness completes the literal changed-path
column estimate on every source beta band. -/
theorem prop47Lemma410Prop48PathWitness_y
    (cWindow : ℕ) {witnessRate Csmall Cfull d : ℝ}
    (hwitnessRate : 0 < witnessRate)
    (hCsmall : 0 < Csmall) (hgap : Csmall + 20 ≤ Cfull)
    (hd : 0 < d)
    (hcompare : 8 * d ≤
      min (witnessRate / 8)
        (imbalanceRate
          (Real.exp (sourceAdjacentComparisonExponent cWindow))) / 2)
    (h : Prop47Lemma410Prop48CanonicalPathWitnessYTwoPhaseLowBandInputs
      cWindow witnessRate Csmall) :
    ∀ᶠ m : ℕ in atTop, ∀ r : StageIndex, ∀ a : AlphaIndex,
      alphaValue a ≤ kappaTwo → ∀ j : SourceBetaBandIndex,
      simpleRandomWalkLaw
          (yCandidateContextualFailure Cfull m r a j \
            prop45FailureEvent sourceCanonicalProfiles canonicalCStar
              m yIndex r (alphaValue a)) ≤
        sourceBetaCandidateTail d m := by
  have hlow := prop47Lemma410Prop48PathWitness_y_lowBands cWindow
    hwitnessRate hCsmall hgap hd hcompare h
  have hCfull : 0 < Cfull := by linarith
  have hhigh :=
    eventually_hlozCandidateCapFailureEvent_eq_empty_highBands hCfull
  filter_upwards [hlow, hhigh] with m hlowM hhighM
  intro r a ha j
  by_cases hj : sourceBeta (alphaValue a) j ≤ (7 : ℝ) / 10
  · exact hlowM r a ha j hj
  · have hempty := hhighM r a ha j (lt_of_not_ge hj)
    rw [yCandidateContextualFailure, hempty, empty_inter, empty_diff,
      measure_empty]
    exact bot_le

/-- The deterministic high-band estimate completes the source-banded
two-phase column estimate on all source beta bands. -/
theorem prop47Lemma410Prop48SourceBanded_y
    (cWindow : ℕ) {C d : ℝ}
    (hC : 0 < C) (hd : 0 < d)
    (hcompare : 16 * d ≤
      min (Real.log ((C + 1) / C) / 2)
        (imbalanceRate
          (Real.exp (sourceAdjacentComparisonExponent cWindow))) / 2)
    (h : Prop47Lemma410Prop48SourceBandedYTwoPhaseLowBandInputs
      cWindow C) :
    ∀ᶠ m : ℕ in atTop, ∀ r : StageIndex, ∀ a : AlphaIndex,
      alphaValue a ≤ kappaTwo → ∀ j : SourceBetaBandIndex,
      simpleRandomWalkLaw (yCandidateContextualFailure C m r a j) ≤
        sourceBetaCandidateTail d m := by
  have hlow := prop47Lemma410Prop48SourceBanded_y_lowBands cWindow
    hC hd hcompare h
  have hhigh := eventually_hlozCandidateCapFailureEvent_eq_empty_highBands hC
  filter_upwards [hlow, hhigh] with m hlowM hhighM
  intro r a ha j
  by_cases hj : sourceBeta (alphaValue a) j ≤ (7 : ℝ) / 10
  · exact hlowM r a ha j hj
  · have hempty := hhighM r a ha j (lt_of_not_ge hj)
    rw [yCandidateContextualFailure, hempty, empty_inter, measure_empty]
    exact bot_le

/-- The candidate tails and the planar post-hit race estimate give the
theta-free Lemma-4.10 stretched-log bound for the complete `Y` deletion. -/
theorem prop47Lemma410ThetaFreeStretchedExponential_y
    (cWindow : ℕ) {C d : ℝ}
    (hC : 0 < C) (hd : 0 < d)
    (hcompare : 8 * d ≤
      min (Real.log ((C + 1) / C) / 2)
        (imbalanceRate
          (Real.exp (sourceAdjacentComparisonExponent cWindow))) / 2)
    (h : Prop47Lemma410Prop48ThetaFreeYTwoPhaseLowBandInputs cWindow C) :
    ∀ᶠ m : ℕ in atTop, ∀ r : StageIndex, ∀ a : AlphaIndex,
      alphaValue a ≤ kappaTwo →
      simpleRandomWalkLaw
          (lemma410FailureEvent m yIndex r (alphaValue a) \
            prop45FailureEvent sourceCanonicalProfiles canonicalCStar
              m yIndex r (alphaValue a)) ≤
        ENNReal.ofReal (Real.exp
          (-sourceLemma410AbsorptionConstant d *
            Real.log ((m : ℝ) + 1) ^ 2)) := by
  have htail := prop47Lemma410Prop48ThetaFree_y cWindow hC hd hcompare h
  have hsum := eventually_sourceBetaBand_sum_absorption hC.le hd
  filter_upwards [htail, eventually_sourceLemma410Radius_bounds, hsum,
      eventually_ge_atTop 2] with m htailM hRadius hsumM hm
  intro r a ha
  let alpha := alphaValue a
  let k := stageNumber r
  let window := sourceLemma410Window m alpha
  let theta := prop45FailureEvent sourceCanonicalProfiles canonicalCStar
    m yIndex r alpha
  let P := yLemma410Context m r alpha \ theta
  have hk : 0 < k := by
    dsimp [k, stageNumber]
    omega
  have hcover : lemma410FailureEvent m yIndex r alpha \ theta ⊆
      ⋃ j : SourceBetaBandIndex,
        hlozLemma410BPrimeEvent window m k
          (sourceBetaCandidateThreshold m alpha j)
          (sourceBetaRaceCount m alpha j) ∩ P := by
    intro omega homega
    have hraw := lemma410FailureEvent_subset_sourceBetaBand_cover
      m yIndex r (alphaValue a) hm ha homega.1
    rcases Set.mem_iUnion.mp hraw with ⟨j, hj⟩
    apply Set.mem_iUnion.mpr
    refine ⟨j, hj.1, ?_⟩
    refine ⟨?_, homega.2⟩
    exact ⟨⟨homega.1.1.1.1, homega.1.1.1.2⟩, homega.1.1.2⟩
  have hrace (j : SourceBetaBandIndex) :
      HasHLOZLemma410PostHitRaceEstimate simpleRandomWalkLaw window
        m k (sourceBetaCandidateThreshold m alpha j)
          (sourceBetaRaceCount m alpha j)
          (fun _ ↦ sourceBetaRaceBound m alpha j) := by
    simpa only [sourceBetaRaceBound] using
      planar_hlozLemma410PostHitRaceEstimate_exp
        window m k (sourceBetaCandidateThreshold m alpha j)
          (sourceBetaRaceCount m alpha j)
          (sourceLemma410Radius m alpha) (hRadius a ha).1 (hRadius a ha).2
          (sourceLemma410Window_geometry m alpha)
  have hcap (j : SourceBetaBandIndex) :
      simpleRandomWalkLaw
          (hlozCandidateCapFailureEvent window m k
              (sourceBetaCandidateThreshold m alpha j)
              (sourceBetaCandidateCap C m alpha j) ∩ P) ≤
        sourceBetaCandidateTail d m := by
    have hj := htailM r a ha j
    have heq :
        hlozCandidateCapFailureEvent window m k
              (sourceBetaCandidateThreshold m alpha j)
              (sourceBetaCandidateCap C m alpha j) ∩ P =
          yCandidateContextualFailure C m r a j \ theta := by
      ext omega
      simp only [P, yCandidateContextualFailure, yLemma410Context,
        window, k, alpha, Set.mem_inter_iff, Set.mem_diff]
      tauto
    rw [heq]
    exact hj
  exact (measure_le_sum_candidateCapTail_add_race_of_band_cover
    simpleRandomWalkLaw
    (lemma410FailureEvent m yIndex r alpha \ theta) P
    (fun _ ↦ window) m k
    (sourceBetaCandidateThreshold m alpha)
    (sourceBetaRaceCount m alpha)
    (fun j ↦ sourceBetaCandidateCap C m alpha j)
    (sourceBetaRaceBound m alpha)
    (fun _ ↦ sourceBetaCandidateTail d m)
    (by omega) hk hcover hrace hcap).trans (hsumM a ha)

/-- Stretched-log Lemma-4.10 estimate from the canonical two-phase winner
package.  The race decomposition uses the large candidate coefficient,
whereas Proposition 4.8 is invoked only on the small canonical phase caps. -/
theorem prop47Lemma410CanonicalThetaFreeStretchedExponential_y
    (cWindow : ℕ) {Csmall Cfull d : ℝ}
    (hCsmall : 0 < Csmall) (hgap : Csmall + 20 ≤ Cfull)
    (hd : 0 < d)
    (hcompare : 8 * d ≤
      min (Real.log ((Csmall + 1) / Csmall) / 2)
        (imbalanceRate
          (Real.exp (sourceAdjacentComparisonExponent cWindow))) / 2)
    (h : Prop47Lemma410Prop48CanonicalThetaFreeYTwoPhaseLowBandInputs
      cWindow Csmall) :
    ∀ᶠ m : ℕ in atTop, ∀ r : StageIndex, ∀ a : AlphaIndex,
      alphaValue a ≤ kappaTwo →
      simpleRandomWalkLaw
          (lemma410FailureEvent m yIndex r (alphaValue a) \
            prop45FailureEvent sourceCanonicalProfiles canonicalCStar
              m yIndex r (alphaValue a)) ≤
        ENNReal.ofReal (Real.exp
          (-sourceLemma410AbsorptionConstant d *
            Real.log ((m : ℝ) + 1) ^ 2)) := by
  have htail := prop47Lemma410Prop48CanonicalThetaFree_y cWindow
    hCsmall hgap hd hcompare h
  have hCfull : 0 < Cfull := by linarith
  have hsum := eventually_sourceBetaBand_sum_absorption hCfull.le hd
  filter_upwards [htail, eventually_sourceLemma410Radius_bounds, hsum,
      eventually_ge_atTop 2] with m htailM hRadius hsumM hm
  intro r a ha
  let alpha := alphaValue a
  let k := stageNumber r
  let window := sourceLemma410Window m alpha
  let theta := prop45FailureEvent sourceCanonicalProfiles canonicalCStar
    m yIndex r alpha
  let P := yLemma410Context m r alpha \ theta
  have hk : 0 < k := by
    dsimp [k, stageNumber]
    omega
  have hcover : lemma410FailureEvent m yIndex r alpha \ theta ⊆
      ⋃ j : SourceBetaBandIndex,
        hlozLemma410BPrimeEvent window m k
          (sourceBetaCandidateThreshold m alpha j)
          (sourceBetaRaceCount m alpha j) ∩ P := by
    intro omega homega
    have hraw := lemma410FailureEvent_subset_sourceBetaBand_cover
      m yIndex r (alphaValue a) hm ha homega.1
    rcases Set.mem_iUnion.mp hraw with ⟨j, hj⟩
    apply Set.mem_iUnion.mpr
    refine ⟨j, hj.1, ?_⟩
    refine ⟨?_, homega.2⟩
    exact ⟨⟨homega.1.1.1.1, homega.1.1.1.2⟩, homega.1.1.2⟩
  have hrace (j : SourceBetaBandIndex) :
      HasHLOZLemma410PostHitRaceEstimate simpleRandomWalkLaw window
        m k (sourceBetaCandidateThreshold m alpha j)
          (sourceBetaRaceCount m alpha j)
          (fun _ ↦ sourceBetaRaceBound m alpha j) := by
    simpa only [sourceBetaRaceBound] using
      planar_hlozLemma410PostHitRaceEstimate_exp
        window m k (sourceBetaCandidateThreshold m alpha j)
          (sourceBetaRaceCount m alpha j)
          (sourceLemma410Radius m alpha) (hRadius a ha).1 (hRadius a ha).2
          (sourceLemma410Window_geometry m alpha)
  have hcap (j : SourceBetaBandIndex) :
      simpleRandomWalkLaw
          (hlozCandidateCapFailureEvent window m k
              (sourceBetaCandidateThreshold m alpha j)
              (sourceBetaCandidateCap Cfull m alpha j) ∩ P) ≤
        sourceBetaCandidateTail d m := by
    have hj := htailM r a ha j
    have heq :
        hlozCandidateCapFailureEvent window m k
              (sourceBetaCandidateThreshold m alpha j)
              (sourceBetaCandidateCap Cfull m alpha j) ∩ P =
          yCandidateContextualFailure Cfull m r a j \ theta := by
      ext omega
      simp only [P, yCandidateContextualFailure, yLemma410Context,
        window, k, alpha, Set.mem_inter_iff, Set.mem_diff]
      tauto
    rw [heq]
    exact hj
  exact (measure_le_sum_candidateCapTail_add_race_of_band_cover
    simpleRandomWalkLaw
    (lemma410FailureEvent m yIndex r alpha \ theta) P
    (fun _ ↦ window) m k
    (sourceBetaCandidateThreshold m alpha)
    (sourceBetaRaceCount m alpha)
    (fun j ↦ sourceBetaCandidateCap Cfull m alpha j)
    (sourceBetaRaceBound m alpha)
    (fun _ ↦ sourceBetaCandidateTail d m)
    (by omega) hk hcover hrace hcap).trans (hsumM a ha)

/-- The literal changed-path candidate tails and the planar post-hit race
estimate give the theta-free stretched-log bound for `Y`. -/
theorem prop47Lemma410PathWitnessStretchedExponential_y
    (cWindow : ℕ) {witnessRate Csmall Cfull d : ℝ}
    (hwitnessRate : 0 < witnessRate)
    (hCsmall : 0 < Csmall) (hgap : Csmall + 20 ≤ Cfull)
    (hd : 0 < d)
    (hcompare : 8 * d ≤
      min (witnessRate / 8)
        (imbalanceRate
          (Real.exp (sourceAdjacentComparisonExponent cWindow))) / 2)
    (h : Prop47Lemma410Prop48CanonicalPathWitnessYTwoPhaseLowBandInputs
      cWindow witnessRate Csmall) :
    ∀ᶠ m : ℕ in atTop, ∀ r : StageIndex, ∀ a : AlphaIndex,
      alphaValue a ≤ kappaTwo →
      simpleRandomWalkLaw
          (lemma410FailureEvent m yIndex r (alphaValue a) \
            prop45FailureEvent sourceCanonicalProfiles canonicalCStar
              m yIndex r (alphaValue a)) ≤
        ENNReal.ofReal (Real.exp
          (-sourceLemma410AbsorptionConstant d *
            Real.log ((m : ℝ) + 1) ^ 2)) := by
  have htail := prop47Lemma410Prop48PathWitness_y cWindow
    hwitnessRate hCsmall hgap hd hcompare h
  have hCfull : 0 < Cfull := by linarith
  have hsum := eventually_sourceBetaBand_sum_absorption hCfull.le hd
  filter_upwards [htail, eventually_sourceLemma410Radius_bounds, hsum,
      eventually_ge_atTop 2] with m htailM hRadius hsumM hm
  intro r a ha
  let alpha := alphaValue a
  let k := stageNumber r
  let window := sourceLemma410Window m alpha
  let theta := prop45FailureEvent sourceCanonicalProfiles canonicalCStar
    m yIndex r alpha
  let P := yLemma410Context m r alpha \ theta
  have hk : 0 < k := by
    dsimp [k, stageNumber]
    omega
  have hcover : lemma410FailureEvent m yIndex r alpha \ theta ⊆
      ⋃ j : SourceBetaBandIndex,
        hlozLemma410BPrimeEvent window m k
          (sourceBetaCandidateThreshold m alpha j)
          (sourceBetaRaceCount m alpha j) ∩ P := by
    intro omega homega
    have hraw := lemma410FailureEvent_subset_sourceBetaBand_cover
      m yIndex r (alphaValue a) hm ha homega.1
    rcases Set.mem_iUnion.mp hraw with ⟨j, hj⟩
    apply Set.mem_iUnion.mpr
    refine ⟨j, hj.1, ?_⟩
    refine ⟨?_, homega.2⟩
    exact ⟨⟨homega.1.1.1.1, homega.1.1.1.2⟩, homega.1.1.2⟩
  have hrace (j : SourceBetaBandIndex) :
      HasHLOZLemma410PostHitRaceEstimate simpleRandomWalkLaw window
        m k (sourceBetaCandidateThreshold m alpha j)
          (sourceBetaRaceCount m alpha j)
          (fun _ ↦ sourceBetaRaceBound m alpha j) := by
    simpa only [sourceBetaRaceBound] using
      planar_hlozLemma410PostHitRaceEstimate_exp
        window m k (sourceBetaCandidateThreshold m alpha j)
          (sourceBetaRaceCount m alpha j)
          (sourceLemma410Radius m alpha) (hRadius a ha).1 (hRadius a ha).2
          (sourceLemma410Window_geometry m alpha)
  have hcap (j : SourceBetaBandIndex) :
      simpleRandomWalkLaw
          (hlozCandidateCapFailureEvent window m k
              (sourceBetaCandidateThreshold m alpha j)
              (sourceBetaCandidateCap Cfull m alpha j) ∩ P) ≤
        sourceBetaCandidateTail d m := by
    have hj := htailM r a ha j
    have heq :
        hlozCandidateCapFailureEvent window m k
              (sourceBetaCandidateThreshold m alpha j)
              (sourceBetaCandidateCap Cfull m alpha j) ∩ P =
          yCandidateContextualFailure Cfull m r a j \ theta := by
      ext omega
      simp only [P, yCandidateContextualFailure, yLemma410Context,
        window, k, alpha, Set.mem_inter_iff, Set.mem_diff]
      tauto
    rw [heq]
    exact hj
  exact (measure_le_sum_candidateCapTail_add_race_of_band_cover
    simpleRandomWalkLaw
    (lemma410FailureEvent m yIndex r alpha \ theta) P
    (fun _ ↦ window) m k
    (sourceBetaCandidateThreshold m alpha)
    (sourceBetaRaceCount m alpha)
    (fun j ↦ sourceBetaCandidateCap Cfull m alpha j)
    (sourceBetaRaceBound m alpha)
    (fun _ ↦ sourceBetaCandidateTail d m)
    (by omega) hk hcover hrace hcap).trans (hsumM a ha)

/-- Candidate tails from the source-banded two-phase atomization combine
with the planar post-hit race estimate directly on the complete `Y` event. -/
theorem prop47Lemma410SourceBandedStretchedExponential_y
    (cWindow : ℕ) {C d : ℝ}
    (hC : 0 < C) (hd : 0 < d)
    (hcompare : 16 * d ≤
      min (Real.log ((C + 1) / C) / 2)
        (imbalanceRate
          (Real.exp (sourceAdjacentComparisonExponent cWindow))) / 2)
    (h : Prop47Lemma410Prop48SourceBandedYTwoPhaseLowBandInputs
      cWindow C) :
    ∀ᶠ m : ℕ in atTop, ∀ r : StageIndex, ∀ a : AlphaIndex,
      alphaValue a ≤ kappaTwo →
      simpleRandomWalkLaw
          (lemma410FailureEvent m yIndex r (alphaValue a)) ≤
        ENNReal.ofReal (Real.exp
          (-sourceLemma410AbsorptionConstant d *
            Real.log ((m : ℝ) + 1) ^ 2)) := by
  have htail := prop47Lemma410Prop48SourceBanded_y cWindow hC hd hcompare h
  have hsum := eventually_sourceBetaBand_sum_absorption hC.le hd
  filter_upwards [htail, eventually_sourceLemma410Radius_bounds, hsum,
      eventually_ge_atTop 2] with m htailM hRadius hsumM hm
  intro r a ha
  let alpha := alphaValue a
  let k := stageNumber r
  let window := sourceLemma410Window m alpha
  let P := yLemma410Context m r alpha
  have hk : 0 < k := by
    dsimp [k, stageNumber]
    omega
  have hcover : lemma410FailureEvent m yIndex r alpha ⊆
      ⋃ j : SourceBetaBandIndex,
        hlozLemma410BPrimeEvent window m k
          (sourceBetaCandidateThreshold m alpha j)
          (sourceBetaRaceCount m alpha j) ∩ P := by
    intro omega homega
    have hraw := lemma410FailureEvent_subset_sourceBetaBand_cover
      m yIndex r (alphaValue a) hm ha homega
    rcases Set.mem_iUnion.mp hraw with ⟨j, hj⟩
    apply Set.mem_iUnion.mpr
    refine ⟨j, hj.1, ?_⟩
    exact ⟨⟨homega.1.1.1, homega.1.1.2⟩, homega.1.2⟩
  have hrace (j : SourceBetaBandIndex) :
      HasHLOZLemma410PostHitRaceEstimate simpleRandomWalkLaw window
        m k (sourceBetaCandidateThreshold m alpha j)
          (sourceBetaRaceCount m alpha j)
          (fun _ ↦ sourceBetaRaceBound m alpha j) := by
    simpa only [sourceBetaRaceBound] using
      planar_hlozLemma410PostHitRaceEstimate_exp
        window m k (sourceBetaCandidateThreshold m alpha j)
          (sourceBetaRaceCount m alpha j)
          (sourceLemma410Radius m alpha) (hRadius a ha).1 (hRadius a ha).2
          (sourceLemma410Window_geometry m alpha)
  have hcap (j : SourceBetaBandIndex) :
      simpleRandomWalkLaw
          (hlozCandidateCapFailureEvent window m k
              (sourceBetaCandidateThreshold m alpha j)
              (sourceBetaCandidateCap C m alpha j) ∩ P) ≤
        sourceBetaCandidateTail d m := by
    have hj := htailM r a ha j
    have heq :
        hlozCandidateCapFailureEvent window m k
              (sourceBetaCandidateThreshold m alpha j)
              (sourceBetaCandidateCap C m alpha j) ∩ P =
          yCandidateContextualFailure C m r a j := by
      ext omega
      simp only [P, yCandidateContextualFailure, yLemma410Context,
        window, k, alpha, Set.mem_inter_iff]
    rw [heq]
    exact hj
  exact (measure_le_sum_candidateCapTail_add_race_of_band_cover
    simpleRandomWalkLaw
    (lemma410FailureEvent m yIndex r alpha) P
    (fun _ ↦ window) m k
    (sourceBetaCandidateThreshold m alpha)
    (sourceBetaRaceCount m alpha)
    (fun j ↦ sourceBetaCandidateCap C m alpha j)
    (sourceBetaRaceBound m alpha)
    (fun _ ↦ sourceBetaCandidateTail d m)
    (by omega) hk hcover hrace hcap).trans (hsumM a ha)

private theorem eventually_sourceLemma410Absorption_le_exceptional_y
    {d : ℝ} (hd : 0 < d) :
    ∀ᶠ m : ℕ in atTop,
      ENNReal.ofReal (Real.exp
          (-sourceLemma410AbsorptionConstant d *
            Real.log ((m : ℝ) + 1) ^ 2)) ≤
        sourceExceptionalRateWithPrefactor m 1 kappa := by
  have hc : 0 < sourceLemma410AbsorptionConstant d :=
    sourceLemma410AbsorptionConstant_pos hd
  have hreal := (tendsto_add_atTop_nat 1).eventually
    (eventually_exponential_error_absorbed (c :=
      sourceLemma410AbsorptionConstant d) hc)
  filter_upwards [hreal] with m hm
  have hm' :
      Real.exp (-sourceLemma410AbsorptionConstant d *
          Real.log ((m : ℝ) + 1) ^ 2) ≤
        ((m : ℝ) + 1) ^ (-(3 * kappa)) := by
    simpa [Nat.cast_add, Nat.cast_one] using hm
  rw [sourceExceptionalRateWithPrefactor]
  simp only [Nat.cast_one, one_mul]
  rw [sourceExceptionalRate]
  have hbase : ENNReal.ofReal ((m : ℝ) + 1) = (m : ℝ≥0∞) + 1 := by
    rw [ENNReal.ofReal_add (by positivity) (by positivity)]
    simp
  rw [← hbase, ENNReal.ofReal_rpow_of_pos (by positivity)]
  exact ENNReal.ofReal_le_ofReal hm'

/-- The source-banded package already pays every recursive theta exception,
so the complete `Y` estimate has coefficient one. -/
theorem prop47Lemma410Estimate_y_of_source_banded_inputs
    (cWindow : ℕ) {C d : ℝ}
    (hC : 0 < C) (hd : 0 < d)
    (hcompare : 16 * d ≤
      min (Real.log ((C + 1) / C) / 2)
        (imbalanceRate
          (Real.exp (sourceAdjacentComparisonExponent cWindow))) / 2)
    (h : Prop47Lemma410Prop48SourceBandedYTwoPhaseLowBandInputs
      cWindow C) :
    ∀ᶠ m : ℕ in atTop, ∀ r : StageIndex, ∀ a : AlphaIndex,
      alphaValue a ≤ kappaTwo →
      simpleRandomWalkLaw
          (lemma410FailureEvent m yIndex r (alphaValue a)) ≤
        sourceExceptionalRateWithPrefactor m 1 kappa := by
  have hraw := prop47Lemma410SourceBandedStretchedExponential_y cWindow
    hC hd hcompare h
  have herror := eventually_sourceLemma410Absorption_le_exceptional_y hd
  filter_upwards [hraw, herror] with m hrawM herrorM
  intro r a ha
  exact (hrawM r a ha).trans herrorM

/-- Proposition 4.5 pays the single removed column theta event. -/
theorem prop47Lemma410Estimate_y_of_thetaFree_inputs
    (cWindow prop45Coeff : ℕ) {C d : ℝ}
    (hC : 0 < C) (hd : 0 < d)
    (hcompare : 8 * d ≤
      min (Real.log ((C + 1) / C) / 2)
        (imbalanceRate
          (Real.exp (sourceAdjacentComparisonExponent cWindow))) / 2)
    (h : Prop47Lemma410Prop48ThetaFreeYTwoPhaseLowBandInputs cWindow C)
    (hProp45 : Prop47Prop45Estimate sourceCanonicalProfiles canonicalCStar
      prop45Coeff) :
    ∀ᶠ m : ℕ in atTop, ∀ r : StageIndex, ∀ a : AlphaIndex,
      alphaValue a ≤ kappaTwo →
      simpleRandomWalkLaw
          (lemma410FailureEvent m yIndex r (alphaValue a)) ≤
        sourceExceptionalRateWithPrefactor m (prop45Coeff + 1) kappa := by
  have hdiff := prop47Lemma410ThetaFreeStretchedExponential_y cWindow
    hC hd hcompare h
  have herror := eventually_sourceLemma410Absorption_le_exceptional_y hd
  filter_upwards [hdiff, hProp45, herror] with m hdiffM hthetaM herrorM
  intro r a ha
  let E := lemma410FailureEvent m yIndex r (alphaValue a)
  let theta := prop45FailureEvent sourceCanonicalProfiles canonicalCStar
    m yIndex r (alphaValue a)
  have hsplit : E ⊆ theta ∪ (E \ theta) := by
    intro omega homega
    by_cases htheta : omega ∈ theta
    · exact Or.inl htheta
    · exact Or.inr ⟨homega, htheta⟩
  calc
    simpleRandomWalkLaw E ≤
        simpleRandomWalkLaw theta + simpleRandomWalkLaw (E \ theta) :=
      (measure_mono hsplit).trans (measure_union_le _ _)
    _ ≤ sourceExceptionalRateWithPrefactor m prop45Coeff kappa +
        sourceExceptionalRateWithPrefactor m 1 kappa :=
      add_le_add (hthetaM yIndex r a ha) ((hdiffM r a ha).trans herrorM)
    _ = sourceExceptionalRateWithPrefactor m (prop45Coeff + 1) kappa := by
      simp only [sourceExceptionalRateWithPrefactor]
      push_cast
      ring

/-- Proposition 4.5 completes the canonical two-phase column estimate; the
phase union and full-event cover are now both theorems rather than source
fields. -/
theorem prop47Lemma410Estimate_y_of_canonicalThetaFree_inputs
    (cWindow prop45Coeff : ℕ) {Csmall Cfull d : ℝ}
    (hCsmall : 0 < Csmall) (hgap : Csmall + 20 ≤ Cfull)
    (hd : 0 < d)
    (hcompare : 8 * d ≤
      min (Real.log ((Csmall + 1) / Csmall) / 2)
        (imbalanceRate
          (Real.exp (sourceAdjacentComparisonExponent cWindow))) / 2)
    (h : Prop47Lemma410Prop48CanonicalThetaFreeYTwoPhaseLowBandInputs
      cWindow Csmall)
    (hProp45 : Prop47Prop45Estimate sourceCanonicalProfiles canonicalCStar
      prop45Coeff) :
    ∀ᶠ m : ℕ in atTop, ∀ r : StageIndex, ∀ a : AlphaIndex,
      alphaValue a ≤ kappaTwo →
      simpleRandomWalkLaw
          (lemma410FailureEvent m yIndex r (alphaValue a)) ≤
        sourceExceptionalRateWithPrefactor m (prop45Coeff + 1) kappa := by
  have hdiff := prop47Lemma410CanonicalThetaFreeStretchedExponential_y
    cWindow hCsmall hgap hd hcompare h
  have herror := eventually_sourceLemma410Absorption_le_exceptional_y hd
  filter_upwards [hdiff, hProp45, herror] with m hdiffM hthetaM herrorM
  intro r a ha
  let E := lemma410FailureEvent m yIndex r (alphaValue a)
  let theta := prop45FailureEvent sourceCanonicalProfiles canonicalCStar
    m yIndex r (alphaValue a)
  have hsplit : E ⊆ theta ∪ (E \ theta) := by
    intro omega homega
    by_cases htheta : omega ∈ theta
    · exact Or.inl htheta
    · exact Or.inr ⟨homega, htheta⟩
  calc
    simpleRandomWalkLaw E ≤
        simpleRandomWalkLaw theta + simpleRandomWalkLaw (E \ theta) :=
      (measure_mono hsplit).trans (measure_union_le _ _)
    _ ≤ sourceExceptionalRateWithPrefactor m prop45Coeff kappa +
        sourceExceptionalRateWithPrefactor m 1 kappa :=
      add_le_add (hthetaM yIndex r a ha) ((hdiffM r a ha).trans herrorM)
    _ = sourceExceptionalRateWithPrefactor m (prop45Coeff + 1) kappa := by
      simp only [sourceExceptionalRateWithPrefactor]
      push_cast
      ring

/-- Proposition 4.5 pays the single column theta event after the literal
changed-path Proposition-4.8 estimate. -/
theorem prop47Lemma410Estimate_y_of_pathWitness_inputs
    (cWindow prop45Coeff : ℕ)
    {witnessRate Csmall Cfull d : ℝ}
    (hwitnessRate : 0 < witnessRate)
    (hCsmall : 0 < Csmall) (hgap : Csmall + 20 ≤ Cfull)
    (hd : 0 < d)
    (hcompare : 8 * d ≤
      min (witnessRate / 8)
        (imbalanceRate
          (Real.exp (sourceAdjacentComparisonExponent cWindow))) / 2)
    (h : Prop47Lemma410Prop48CanonicalPathWitnessYTwoPhaseLowBandInputs
      cWindow witnessRate Csmall)
    (hProp45 : Prop47Prop45Estimate sourceCanonicalProfiles canonicalCStar
      prop45Coeff) :
    ∀ᶠ m : ℕ in atTop, ∀ r : StageIndex, ∀ a : AlphaIndex,
      alphaValue a ≤ kappaTwo →
      simpleRandomWalkLaw
          (lemma410FailureEvent m yIndex r (alphaValue a)) ≤
        sourceExceptionalRateWithPrefactor m (prop45Coeff + 1) kappa := by
  have hdiff := prop47Lemma410PathWitnessStretchedExponential_y
    cWindow hwitnessRate hCsmall hgap hd hcompare h
  have herror := eventually_sourceLemma410Absorption_le_exceptional_y hd
  filter_upwards [hdiff, hProp45, herror] with m hdiffM hthetaM herrorM
  intro r a ha
  let E := lemma410FailureEvent m yIndex r (alphaValue a)
  let theta := prop45FailureEvent sourceCanonicalProfiles canonicalCStar
    m yIndex r (alphaValue a)
  have hsplit : E ⊆ theta ∪ (E \ theta) := by
    intro omega homega
    by_cases htheta : omega ∈ theta
    · exact Or.inl htheta
    · exact Or.inr ⟨homega, htheta⟩
  calc
    simpleRandomWalkLaw E ≤
        simpleRandomWalkLaw theta + simpleRandomWalkLaw (E \ theta) :=
      (measure_mono hsplit).trans (measure_union_le _ _)
    _ ≤ sourceExceptionalRateWithPrefactor m prop45Coeff kappa +
        sourceExceptionalRateWithPrefactor m 1 kappa :=
      add_le_add (hthetaM yIndex r a ha) ((hdiffM r a ha).trans herrorM)
    _ = sourceExceptionalRateWithPrefactor m (prop45Coeff + 1) kappa := by
      simp only [sourceExceptionalRateWithPrefactor]
      push_cast
      ring

theorem siteSquaredDistance_reflectSite (x y : Site) :
    siteSquaredDistance (reflectSite x) (reflectSite y) =
      siteSquaredDistance x y := by
  rcases x with ⟨x₁, x₂⟩
  rcases y with ⟨y₁, y₂⟩
  simp only [siteSquaredDistance, reflectSite]
  rw [show -x₁ - -y₁ = -(x₁ - y₁) by ring, Int.natAbs_neg]

theorem sourceLemma410Window_reflectSite
    (m : ℕ) (alpha : ℝ) (c : Site) :
    sourceLemma410Window m alpha (reflectSite c) =
      (sourceLemma410Window m alpha c).image reflectSite := by
  classical
  ext y
  obtain ⟨x, rfl⟩ := reflectSite_surjective y
  rw [Finset.mem_image]
  constructor
  · intro hy
    refine ⟨x, ?_, rfl⟩
    rw [sourceLemma410Window, mem_hlozLatticeBallSq_iff] at hy ⊢
    simpa only [siteSquaredDistance_reflectSite] using hy
  · rintro ⟨z, hz, hzx⟩
    have hzx' : z = x := reflectSite_injective hzx
    subst z
    rw [sourceLemma410Window, mem_hlozLatticeBallSq_iff] at hz ⊢
    simpa only [siteSquaredDistance_reflectSite] using hz

theorem hlozCandidateSitesAtTime_sourceWindow_reflectPath
    (m : ℕ) (alpha : ℝ) (s : Path) (t q : ℕ) :
    hlozCandidateSitesAtTime (sourceLemma410Window m alpha)
        (reflectPath s) t q =
      (hlozCandidateSitesAtTime (sourceLemma410Window m alpha)
        s t q).image reflectSite := by
  classical
  ext y
  obtain ⟨x, rfl⟩ := reflectSite_surjective y
  simp only [hlozCandidateSitesAtTime, Finset.mem_filter, reflectPath,
    sourceLemma410Window_reflectSite, Finset.mem_image, localTime_reflectPath]
  constructor
  · rintro ⟨hwindow, hlocal⟩
    rcases hwindow with ⟨z, hz, hzx⟩
    have hzx' : z = x := reflectSite_injective hzx
    subst z
    exact ⟨x, ⟨hz, hlocal⟩, rfl⟩
  · rintro ⟨z, ⟨hz, hlocal⟩, hzx⟩
    have hzx' : z = x := reflectSite_injective hzx
    subst z
    exact ⟨⟨x, hz, rfl⟩, hlocal⟩

theorem card_hlozCandidateSitesAtTime_sourceWindow_reflectPath
    (m : ℕ) (alpha : ℝ) (s : Path) (t q : ℕ) :
    (hlozCandidateSitesAtTime (sourceLemma410Window m alpha)
        (reflectPath s) t q).card =
      (hlozCandidateSitesAtTime (sourceLemma410Window m alpha)
        s t q).card := by
  rw [hlozCandidateSitesAtTime_sourceWindow_reflectPath]
  exact Finset.card_image_of_injective _ reflectSite_injective

/-- The reunited column candidate event, not either conditional terminal
phase separately, is equivariant under the origin-fixing reflection. -/
theorem candidateCapFailure_inter_prefix_y_reflect_iff
    (s : Path) (m k q cap : ℕ) (alpha : ℝ) :
    s ∈ hlozCandidateCapFailureEvent (sourceLemma410Window m alpha)
          m k q cap ∩ prefixPairingEvent m yIndex (k + 1) ↔
      reflectPath s ∈
        hlozCandidateCapFailureEvent (sourceLemma410Window m alpha)
            m k q cap ∩ prefixPairingEvent m yIndex' (k + 1) := by
  constructor
  · rintro ⟨hcap, hprefix⟩
    constructor
    · unfold hlozCandidateCapFailureEvent at hcap ⊢
      simp only [Set.mem_ofPred_eq]
      rw [firstKSitesReachLevel_reflectPath,
        card_hlozCandidateSitesAtTime_sourceWindow_reflectPath]
      exact hcap
    · exact (prefixPairingEvent_y_reflect_iff s m (k + 1)).mpr hprefix
  · rintro ⟨hcap, hprefix⟩
    constructor
    · unfold hlozCandidateCapFailureEvent at hcap ⊢
      simp only [Set.mem_ofPred_eq] at hcap ⊢
      rw [firstKSitesReachLevel_reflectPath,
        card_hlozCandidateSitesAtTime_sourceWindow_reflectPath] at hcap
      exact hcap
    · exact (prefixPairingEvent_y_reflect_iff s m (k + 1)).mp hprefix

theorem simpleRandomWalkLaw_candidateCapFailure_inter_prefix_yPrime_eq_y
    (m k q cap : ℕ) (alpha : ℝ) :
    simpleRandomWalkLaw
        (hlozCandidateCapFailureEvent (sourceLemma410Window m alpha)
            m k q cap ∩ prefixPairingEvent m yIndex' (k + 1)) =
      simpleRandomWalkLaw
        (hlozCandidateCapFailureEvent (sourceLemma410Window m alpha)
            m k q cap ∩ prefixPairingEvent m yIndex (k + 1)) := by
  let E := hlozCandidateCapFailureEvent (sourceLemma410Window m alpha)
      m k q cap ∩ prefixPairingEvent m yIndex' (k + 1)
  have hE : MeasurableSet E :=
    (measurableSet_hlozCandidateCapFailureEvent _ _ _ _ _).inter
      (measurableSet_prefixPairingEvent _ _ _)
  calc
    simpleRandomWalkLaw E =
        (simpleRandomWalkLaw.map reflectPath) E := by
      rw [simpleRandomWalkLaw_map_reflectPath]
    _ = simpleRandomWalkLaw (reflectPath ⁻¹' E) := by
      rw [Measure.map_apply measurable_reflectPath hE]
    _ = simpleRandomWalkLaw
        (hlozCandidateCapFailureEvent (sourceLemma410Window m alpha)
            m k q cap ∩ prefixPairingEvent m yIndex (k + 1)) := by
      congr 1
      ext s
      exact (candidateCapFailure_inter_prefix_y_reflect_iff
        s m k q cap alpha).symm

theorem siteDistance_reflectSite (x y : Site) :
    siteDistance (reflectSite x) (reflectSite y) = siteDistance x y := by
  unfold siteDistance
  rw [siteSquaredDistance_reflectSite]

theorem hlozDirectAvoidanceEvent_y_reflect_iff
    (s : Path) (m j : ℕ) :
    s ∈ hlozDirectAvoidanceEvent m j ↔
      reflectPath s ∈ hlozDirectAvoidanceEvent m j := by
  simp only [hlozDirectAvoidanceEvent, Set.mem_setOf_eq,
    firstKSitesReachLevel_reflectPath, levelCreationSite_reflectPath,
    reflectPath]
  constructor
  · intro h n hn hn' i hi hi' hEq
    exact h n hn hn' i hi hi' (reflectSite_injective hEq)
  · intro h n hn hn' i hi hi' hEq
    exact h n hn hn' i hi hi' (congrArg reflectSite hEq)

theorem distanceBinEvent_y_reflect_iff
    (s : Path) (m k : ℕ) (alpha : ℝ) :
    s ∈ distanceBinEvent m k alpha ↔
      reflectPath s ∈ distanceBinEvent m k alpha := by
  simp only [distanceBinEvent, Set.mem_setOf_eq,
    firstKSitesReachLevel_reflectPath, levelCreationSite_reflectPath,
    siteDistance_reflectSite]

theorem nextCreationIsCandidateEvent_y_reflect_iff
    (s : Path) (m k : ℕ) (beta : ℝ) :
    s ∈ nextCreationIsCandidateEvent yIndex m k beta ↔
      reflectPath s ∈ nextCreationIsCandidateEvent yIndex' m k beta := by
  simp only [nextCreationIsCandidateEvent, Set.mem_setOf_eq,
    levelCreationSite_reflectPath, nearFavoriteSites_y_reflect,
    Finset.mem_image]
  constructor
  · intro h
    exact ⟨levelCreationSite s m (k + 1), h, rfl⟩
  · rintro ⟨x, hx, hEq⟩
    exact (reflectSite_injective hEq).symm ▸ hx

theorem lemma410FailureEvent_y_reflect_iff
    (s : Path) (m : ℕ) (r : StageIndex) (alpha : ℝ) :
    s ∈ lemma410FailureEvent m yIndex r alpha ↔
      reflectPath s ∈ lemma410FailureEvent m yIndex' r alpha := by
  simp only [lemma410FailureEvent, Set.mem_inter_iff, Set.mem_compl_iff]
  constructor
  · rintro ⟨⟨⟨hprefix, hav ⟩, hdist⟩, hnext⟩
    refine ⟨⟨⟨(prefixPairingEvent_y_reflect_iff s m _).mpr hprefix,
      (hlozDirectAvoidanceEvent_y_reflect_iff s m _).mp hav⟩,
      (distanceBinEvent_y_reflect_iff s m _ alpha).mp hdist⟩, ?_⟩
    exact fun hmem ↦ hnext
      ((nextCreationIsCandidateEvent_y_reflect_iff s m _ _).mpr hmem)
  · rintro ⟨⟨⟨hprefix, hav⟩, hdist⟩, hnext⟩
    refine ⟨⟨⟨(prefixPairingEvent_y_reflect_iff s m _).mp hprefix,
      (hlozDirectAvoidanceEvent_y_reflect_iff s m _).mpr hav⟩,
      (distanceBinEvent_y_reflect_iff s m _ alpha).mpr hdist⟩, ?_⟩
    exact fun hmem ↦ hnext
      ((nextCreationIsCandidateEvent_y_reflect_iff s m _ _).mp hmem)

theorem simpleRandomWalkLaw_lemma410FailureEvent_yPrime_eq_y
    (m : ℕ) (r : StageIndex) (alpha : ℝ) :
    simpleRandomWalkLaw (lemma410FailureEvent m yIndex' r alpha) =
      simpleRandomWalkLaw (lemma410FailureEvent m yIndex r alpha) := by
  let E := lemma410FailureEvent m yIndex' r alpha
  have hE : MeasurableSet E :=
    (((measurableSet_prefixPairingEvent m yIndex' (stageNumber r + 1)).inter
      (measurableSet_hlozDirectAvoidanceEvent m (stageNumber r + 1))).inter
      (measurableSet_distanceBinEvent m (stageNumber r) alpha)).inter
      (measurableSet_nextCreationIsCandidateEvent yIndex' m
        (stageNumber r) (alpha + delta)).compl
  calc
    simpleRandomWalkLaw E = (simpleRandomWalkLaw.map reflectPath) E := by
      rw [simpleRandomWalkLaw_map_reflectPath]
    _ = simpleRandomWalkLaw (reflectPath ⁻¹' E) := by
      rw [Measure.map_apply measurable_reflectPath hE]
    _ = simpleRandomWalkLaw (lemma410FailureEvent m yIndex r alpha) := by
      congr 1
      ext s
      exact (lemma410FailureEvent_y_reflect_iff s m r alpha).symm

/-- The theta-free two-phase `Y` package supplies both column pairings only
after the complete `Y` event has been reflected. -/
def Prop47Lemma410EstimateYColumns (coeff : ℕ) : Prop :=
  ∀ᶠ m : ℕ in atTop, ∀ i : Fin 6, 4 ≤ i.1 →
    ∀ r : StageIndex, ∀ a : AlphaIndex, alphaValue a ≤ kappaTwo →
    simpleRandomWalkLaw (lemma410FailureEvent m i r (alphaValue a)) ≤
      sourceExceptionalRateWithPrefactor m coeff kappa

theorem prop47Lemma410EstimateYColumns_of_thetaFree_inputs
    (cWindow prop45Coeff : ℕ) {C d : ℝ}
    (hC : 0 < C) (hd : 0 < d)
    (hcompare : 8 * d ≤
      min (Real.log ((C + 1) / C) / 2)
        (imbalanceRate
          (Real.exp (sourceAdjacentComparisonExponent cWindow))) / 2)
    (h : Prop47Lemma410Prop48ThetaFreeYTwoPhaseLowBandInputs cWindow C)
    (hProp45 : Prop47Prop45Estimate sourceCanonicalProfiles canonicalCStar
      prop45Coeff) :
    Prop47Lemma410EstimateYColumns (prop45Coeff + 1) := by
  have hy := prop47Lemma410Estimate_y_of_thetaFree_inputs cWindow
    prop45Coeff hC hd hcompare h hProp45
  filter_upwards [hy] with m hm
  intro i hi r a ha
  have hiCases : i = yIndex ∨ i = yIndex' := by
    fin_cases i <;> simp_all [yIndex, yIndex']
  rcases hiCases with rfl | rfl
  · exact hm r a ha
  · rw [simpleRandomWalkLaw_lemma410FailureEvent_yPrime_eq_y]
    exact hm r a ha

/-- Canonical two-phase source data supplies both column pairings after the
complete `Y` event, not the individual terminal atoms, is reflected. -/
theorem prop47Lemma410EstimateYColumns_of_canonicalThetaFree_inputs
    (cWindow prop45Coeff : ℕ) {Csmall Cfull d : ℝ}
    (hCsmall : 0 < Csmall) (hgap : Csmall + 20 ≤ Cfull)
    (hd : 0 < d)
    (hcompare : 8 * d ≤
      min (Real.log ((Csmall + 1) / Csmall) / 2)
        (imbalanceRate
          (Real.exp (sourceAdjacentComparisonExponent cWindow))) / 2)
    (h : Prop47Lemma410Prop48CanonicalThetaFreeYTwoPhaseLowBandInputs
      cWindow Csmall)
    (hProp45 : Prop47Prop45Estimate sourceCanonicalProfiles canonicalCStar
      prop45Coeff) :
    Prop47Lemma410EstimateYColumns (prop45Coeff + 1) := by
  have hy := prop47Lemma410Estimate_y_of_canonicalThetaFree_inputs
    cWindow prop45Coeff hCsmall hgap hd hcompare h hProp45
  filter_upwards [hy] with m hm
  intro i hi r a ha
  have hiCases : i = yIndex ∨ i = yIndex' := by
    fin_cases i <;> simp_all [yIndex, yIndex']
  rcases hiCases with rfl | rfl
  · exact hm r a ha
  · rw [simpleRandomWalkLaw_lemma410FailureEvent_yPrime_eq_y]
    exact hm r a ha

/-- Literal changed-path terminal source data supplies both column pairings
after reflection of the complete reunited `Y` event. -/
theorem prop47Lemma410EstimateYColumns_of_pathWitness_inputs
    (cWindow prop45Coeff : ℕ)
    {witnessRate Csmall Cfull d : ℝ}
    (hwitnessRate : 0 < witnessRate)
    (hCsmall : 0 < Csmall) (hgap : Csmall + 20 ≤ Cfull)
    (hd : 0 < d)
    (hcompare : 8 * d ≤
      min (witnessRate / 8)
        (imbalanceRate
          (Real.exp (sourceAdjacentComparisonExponent cWindow))) / 2)
    (h : Prop47Lemma410Prop48CanonicalPathWitnessYTwoPhaseLowBandInputs
      cWindow witnessRate Csmall)
    (hProp45 : Prop47Prop45Estimate sourceCanonicalProfiles canonicalCStar
      prop45Coeff) :
    Prop47Lemma410EstimateYColumns (prop45Coeff + 1) := by
  have hy := prop47Lemma410Estimate_y_of_pathWitness_inputs
    cWindow prop45Coeff hwitnessRate hCsmall hgap hd hcompare h hProp45
  filter_upwards [hy] with m hm
  intro i hi r a ha
  have hiCases : i = yIndex ∨ i = yIndex' := by
    fin_cases i <;> simp_all [yIndex, yIndex']
  rcases hiCases with rfl | rfl
  · exact hm r a ha
  · rw [simpleRandomWalkLaw_lemma410FailureEvent_yPrime_eq_y]
    exact hm r a ha

/-- The source-banded two-phase `Y` package supplies both column pairings
with coefficient one after reflection of the complete reunited event. -/
theorem prop47Lemma410EstimateYColumns_of_source_banded_inputs
    (cWindow : ℕ) {C d : ℝ}
    (hC : 0 < C) (hd : 0 < d)
    (hcompare : 16 * d ≤
      min (Real.log ((C + 1) / C) / 2)
        (imbalanceRate
          (Real.exp (sourceAdjacentComparisonExponent cWindow))) / 2)
    (h : Prop47Lemma410Prop48SourceBandedYTwoPhaseLowBandInputs
      cWindow C) :
    Prop47Lemma410EstimateYColumns 1 := by
  have hy := prop47Lemma410Estimate_y_of_source_banded_inputs cWindow
    hC hd hcompare h
  filter_upwards [hy] with m hm
  intro i hi r a ha
  have hiCases : i = yIndex ∨ i = yIndex' := by
    fin_cases i <;> simp_all [yIndex, yIndex']
  rcases hiCases with rfl | rfl
  · exact hm r a ha
  · rw [simpleRandomWalkLaw_lemma410FailureEvent_yPrime_eq_y]
    exact hm r a ha

/-- The checked four-X and two-column theta-free estimates assemble the
full six-pairing named Lemma-4.10 estimate with no extra union factor. -/
theorem prop47Lemma410Estimate_of_thetaFree_x_y_inputs
    {coeff : ℕ}
    (hX : Prop47Lemma410EstimateXDirections coeff)
    (hY : Prop47Lemma410EstimateYColumns coeff) :
    Prop47Lemma410Estimate coeff := by
  filter_upwards [hX, hY] with m hXm hYm
  intro i r a ha
  by_cases hi : i.1 < 4
  · let d : Dir := ⟨i.1, hi⟩
    have hindex : xIndex d = i := by
      apply Fin.ext
      rfl
    rw [← hindex]
    exact hXm d r a ha
  · exact hYm i (Nat.le_of_not_gt hi) r a ha

/-- Naming-neutral all-six assembly used by both the legacy theta-free and
the source-banded Lemma-4.10 paths. -/
theorem prop47Lemma410Estimate_of_x_y_inputs
    {coeff : ℕ}
    (hX : Prop47Lemma410EstimateXDirections coeff)
    (hY : Prop47Lemma410EstimateYColumns coeff) :
    Prop47Lemma410Estimate coeff :=
  prop47Lemma410Estimate_of_thetaFree_x_y_inputs hX hY

/-- The literal two-phase source decomposition for one low Lemma-4.10 band.
The forward and backward atom families have independent conditional laws and
are required to cover only their own phase. -/
structure YTwoPhaseStoppedCandidateDecomposition
    (cWindow m : ℕ) (alpha cBase cTheta thetaPower : ℝ)
    (failure : Set Path) where
  forwardFailure : Set Path
  backwardFailure : Set Path
  cover : failure ⊆ forwardFailure ∪ backwardFailure
  forward : ForwardColumnStoppedCandidateDecomposition cWindow m alpha cBase
    cTheta thetaPower forwardFailure
  backward : PrimedColumnStoppedCandidateDecomposition cWindow m alpha cBase
    cTheta thetaPower backwardFailure

/-- Exact source-facing column input.  No stopped product law or probability
tail is a field: those are derived atomwise from the terminal restart laws
and the checked numerical Proposition 4.8 theorem. -/
def Prop47Lemma410Prop48YTwoPhaseLowBandInputs
    (cWindow : ℕ) (C cBase cTheta thetaPower : ℝ) : Prop :=
  ∀ᶠ m : ℕ in atTop, ∀ r : StageIndex, ∀ a : AlphaIndex,
    alphaValue a ≤ kappaTwo → ∀ j : SourceBetaBandIndex,
    sourceBeta (alphaValue a) j ≤ (7 : ℝ) / 10 →
    Nonempty (YTwoPhaseStoppedCandidateDecomposition cWindow m
      (sourceBeta (alphaValue a) j) cBase cTheta thetaPower
      (hlozCandidateCapFailureEvent
          (sourceLemma410Window m (alphaValue a)) m (stageNumber r)
          (sourceBetaCandidateThreshold m (alphaValue a) j)
          (sourceBetaCandidateCap C m (alphaValue a) j) ∩
        prefixPairingEvent m yIndex (stageNumber r + 1)))

theorem prop47Lemma410Prop48StoppedCandidateTail_y_lowBands
    (cWindow : ℕ) {C cBase cTheta thetaPower d : ℝ}
    (hcBase : 0 < cBase) (hcTheta : 0 < cTheta)
    (hthetaPower : 0 < thetaPower) (hd : 0 < d)
    (hcompare : 8 * d ≤
      min cBase
        (imbalanceRate
          (Real.exp (sourceAdjacentComparisonExponent cWindow))) / 2)
    (h : Prop47Lemma410Prop48YTwoPhaseLowBandInputs cWindow C cBase
      cTheta thetaPower) :
    ∀ᶠ m : ℕ in atTop, ∀ r : StageIndex, ∀ a : AlphaIndex,
      alphaValue a ≤ kappaTwo → ∀ j : SourceBetaBandIndex,
      sourceBeta (alphaValue a) j ≤ (7 : ℝ) / 10 →
      simpleRandomWalkLaw
          (hlozCandidateCapFailureEvent
              (sourceLemma410Window m (alphaValue a)) m (stageNumber r)
              (sourceBetaCandidateThreshold m (alphaValue a) j)
              (sourceBetaCandidateCap C m (alphaValue a) j) ∩
            prefixPairingEvent m yIndex (stageNumber r + 1)) ≤
        sourceBetaCandidateTail d m := by
  have hgood := eventually_sourceProp48NumericalAt cWindow hcBase hcTheta
    hthetaPower
  have htwoD : 0 < 2 * d := by positivity
  have hshift := eventually_prop48Rate_le_sourceBetaCandidateTail
    (rate := min cBase
      (imbalanceRate
        (Real.exp (sourceAdjacentComparisonExponent cWindow))) / 2)
    htwoD (by nlinarith [hcompare])
  have habsorb := eventually_two_mul_sourceBetaCandidateTail_two_mul_le hd
  filter_upwards [h, hgood, hshift, habsorb, eventually_ge_atTop 2] with
      m hm hgoodM hshiftM habsorbM hmLarge
  intro r a ha j hj
  rcases hm r a ha j hj with ⟨D⟩
  have hForwardProfile (n : ℕ) :
      sourceTruncatedProfileMeasure m (D.forward.atoms n).source.profile
        (sourceProfileQEvent m
          (sourceAlphaIntervalCount m (sourceBeta (alphaValue a) j))
          (D.forward.atoms n).source.profile
          (geometricThreshold (Real.log (m : ℝ) ^ 2)
            (sourceLemma411GrowthFactor cWindow)
            (sourceAlphaIntervalCount m
              (sourceBeta (alphaValue a) j)))) ≤
        sourceBetaCandidateTail (2 * d) m := by
    exact sourceTruncatedProfile_prop48_band_bound_at_ennreal hgoodM
      (sourceBeta (alphaValue a) j) (D.forward.atoms n).source.profile
      (kappaOne_le_sourceBeta ha j) (hj.trans (by norm_num))
      (D.forward.atoms n).source.profile_lt
      (D.forward.atoms n).base_bound (D.forward.atoms n).theta_bound
      (sourceBetaCandidateTail (2 * d) m) hshiftM
  have hBackwardProfile (n : ℕ) :
      sourceTruncatedProfileMeasure m (D.backward.atoms n).source.profile
        (sourceProfileQEvent m
          (sourceAlphaIntervalCount m (sourceBeta (alphaValue a) j))
          (D.backward.atoms n).source.profile
          (geometricThreshold (Real.log (m : ℝ) ^ 2)
            (sourceLemma411GrowthFactor cWindow)
            (sourceAlphaIntervalCount m
              (sourceBeta (alphaValue a) j)))) ≤
        sourceBetaCandidateTail (2 * d) m := by
    exact sourceTruncatedProfile_prop48_band_bound_at_ennreal hgoodM
      (sourceBeta (alphaValue a) j) (D.backward.atoms n).source.profile
      (kappaOne_le_sourceBeta ha j) (hj.trans (by norm_num))
      (D.backward.atoms n).source.profile_lt
      (D.backward.atoms n).base_bound (D.backward.atoms n).theta_bound
      (sourceBetaCandidateTail (2 * d) m) hshiftM
  have hForward :=
    measure_failure_le_of_forwardColumnStoppedCandidateDecomposition
      D.forward (sourceBetaCandidateTail (2 * d) m) hForwardProfile
  have hBackward :=
    measure_failure_le_of_primedColumnStoppedCandidateDecomposition
      D.backward (sourceBetaCandidateTail (2 * d) m) hBackwardProfile
  calc
    simpleRandomWalkLaw _ ≤
        simpleRandomWalkLaw (D.forwardFailure ∪ D.backwardFailure) :=
      measure_mono D.cover
    _ ≤ simpleRandomWalkLaw D.forwardFailure +
        simpleRandomWalkLaw D.backwardFailure := measure_union_le _ _
    _ ≤ sourceBetaCandidateTail (2 * d) m +
        sourceBetaCandidateTail (2 * d) m := add_le_add hForward hBackward
    _ = (2 : ℝ≥0∞) * sourceBetaCandidateTail (2 * d) m := by ring
    _ ≤ sourceBetaCandidateTail d m := habsorbM

/-- The two literal `Y` phases imply both column candidate tails.  The high
bands are deterministic; the low-band bound for `Y'` is obtained only by
reflecting the already reunited `Y` event. -/
theorem prop47Lemma410Prop48StoppedCandidateTail_yColumns_of_inputs
    (cWindow : ℕ) {C cBase cTheta thetaPower d : ℝ}
    (hC : 0 < C) (hcBase : 0 < cBase) (hcTheta : 0 < cTheta)
    (hthetaPower : 0 < thetaPower) (hd : 0 < d)
    (hcompare : 8 * d ≤
      min cBase
        (imbalanceRate
          (Real.exp (sourceAdjacentComparisonExponent cWindow))) / 2)
    (h : Prop47Lemma410Prop48YTwoPhaseLowBandInputs cWindow C cBase
      cTheta thetaPower) :
    Prop47Lemma410Prop48StoppedCandidateTailYColumns C d := by
  have hlow := prop47Lemma410Prop48StoppedCandidateTail_y_lowBands cWindow
    hcBase hcTheta hthetaPower hd hcompare h
  have hhigh := eventually_hlozCandidateCapFailureEvent_eq_empty_highBands hC
  filter_upwards [hlow, hhigh] with m hlowM hhighM
  intro i hi r a ha j
  by_cases hj : sourceBeta (alphaValue a) j ≤ (7 : ℝ) / 10
  · have hY := hlowM r a ha j hj
    have hiCases : i = yIndex ∨ i = yIndex' := by
      fin_cases i <;> simp_all [yIndex, yIndex']
    rcases hiCases with rfl | rfl
    · exact hY
    · rw [simpleRandomWalkLaw_candidateCapFailure_inter_prefix_yPrime_eq_y]
      exact hY
  · have hempty := hhighM r a ha j (lt_of_not_ge hj)
    rw [hempty, empty_inter, measure_empty]
    exact bot_le

end Erdos1166.HLOZLemma410Prop48YColumns
