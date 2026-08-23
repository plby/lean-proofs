/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos1166.Erdos1166HLOZLemma410Prop48Connector
import ErdosProblems.Erdos1166.Erdos1166HLOZProp47Prop45XRotations
import ErdosProblems.Erdos1166.Erdos1166HLOZProp47Lemma411412SourceAtoms
import ErdosProblems.Erdos1166.Erdos1166HLOZProp47Lemma411412XDirections

/-!
# The four rotated X-pairing cases in HLOZ Lemma 4.10

This file transports the source-faithful four-parity `X₁` Proposition 4.8
argument to the other three checkerboard domino tilings.  The transport is
performed only after the two winner halves have been reunited into the
rotation-invariant candidate-cap event.  The two column pairings `Y,Y'`
remain an explicit residual input.
-/

namespace Erdos1166.HLOZLemma410Prop48XDirections

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal Topology

open HLOZPairing HLOZPairingProfiles HLOZProp47Prop45XRotations
open HLOZProp47Parameters HLOZProp47SourceObjects HLOZProp47SourceAssembly
open HLOZPairing.ScreeningBridge
open HLOZLemma410SourceBands HLOZLemma410SourceAbsorption
open HLOZLemma410PotentialRace
open HLOZLemma410Prop48Connector HLOZProp47NamedEstimateBridges
open HLOZBandRatios HLOZLemma411 HLOZLemma411Recursion HLOZLemma412Windows
open HLOZProp48SourceBands HLOZProp48Truncated
open HLOZProp47Canonical HLOZProp47Lemma411412Connector
  HLOZProp47Lemma411412SourceAtoms HLOZProp47Lemma411412XDirections
  HLOZProp47Lemma411412XEastBridge
open HLOZProp45SourceInterval HLOZProp45SourceMirrors
  HLOZProp45SourceEndpoints

abbrev Path := ℕ → Site

/-! ## Theta-free source form at X-east

The checked fixed-profile recursion now removes all profile-window
exceptions before it runs.  The following contextual events retain the
direct-avoidance and distance-bin factors from the final Lemma-4.10 event,
so their one remaining `Theta` part is exactly paid by Proposition 4.5. -/

def xEastLemma410Context
    (m : ℕ) (r : StageIndex) (alpha : ℝ) : Set Path :=
  prefixPairingEvent m (xIndex east) (stageNumber r + 1) ∩
    hlozDirectAvoidanceEvent m (stageNumber r + 1) ∩
    distanceBinEvent m (stageNumber r) alpha

def xEastLeftWinnerContextualFailure
    (C : ℝ) (m : ℕ) (r : StageIndex) (a : AlphaIndex)
    (j : SourceBetaBandIndex) : Set Path :=
  hlozLeftWinnerCandidateCapFailureEvent
      (sourceLemma410Window m (alphaValue a)) m (stageNumber r)
      (sourceBetaCandidateThreshold m (alphaValue a) j)
      (sourceLeftWinnerCandidateCap C m (alphaValue a) j) ∩
    xEastLemma410Context m r (alphaValue a)

def xEastRightWinnerContextualFailure
    (C : ℝ) (m : ℕ) (r : StageIndex) (a : AlphaIndex)
    (j : SourceBetaBandIndex) : Set Path :=
  hlozRightWinnerCandidateCapFailureEvent
      (sourceLemma410Window m (alphaValue a)) m (stageNumber r)
      (sourceBetaCandidateThreshold m (alphaValue a) j)
      (sourceRightWinnerCandidateCap C m (alphaValue a) j) ∩
    xEastLemma410Context m r (alphaValue a)

def xEastCandidateContextualFailure
    (C : ℝ) (m : ℕ) (r : StageIndex) (a : AlphaIndex)
    (j : SourceBetaBandIndex) : Set Path :=
  hlozCandidateCapFailureEvent
      (sourceLemma410Window m (alphaValue a)) m (stageNumber r)
      (sourceBetaCandidateThreshold m (alphaValue a) j)
      (sourceBetaCandidateCap C m (alphaValue a) j) ∩
    xEastLemma410Context m r (alphaValue a)

/-! ### Canonical stopping-parity split

The four stopped laws are indexed by the parity of the literal creation
horizon `T_m^k`.  Earlier interfaces let the source choose two arbitrary
subevents and separately asked that they cover a winner event.  The source
does not make such a choice: the two subevents are exactly the even and odd
fibres of `T_m^k`. -/

/-- The even fibre of the literal creation horizon `T_m^k`. -/
def xEastEvenStoppedHorizonEvent
    (m k : ℕ) : Set Path :=
  {s | Even (firstKSitesReachLevel m k s).untopA}

/-- The odd fibre of the literal creation horizon `T_m^k`, represented as
the complement of the even fibre.  This is the convention used by the
terminal reconstruction lemmas. -/
def xEastOddStoppedHorizonEvent
    (m k : ℕ) : Set Path :=
  {s | ¬ Even (firstKSitesReachLevel m k s).untopA}

def xEastLeftEvenWinnerContextualFailure
    (C : ℝ) (m : ℕ) (r : StageIndex) (a : AlphaIndex)
    (j : SourceBetaBandIndex) : Set Path :=
  xEastLeftWinnerContextualFailure C m r a j ∩
    xEastEvenStoppedHorizonEvent m (stageNumber r)

def xEastLeftOddTerminalWinnerContextualFailure
    (C : ℝ) (m : ℕ) (r : StageIndex) (a : AlphaIndex)
    (j : SourceBetaBandIndex) : Set Path :=
  xEastLeftWinnerContextualFailure C m r a j ∩
    xEastOddStoppedHorizonEvent m (stageNumber r)

def xEastRightOddWinnerContextualFailure
    (C : ℝ) (m : ℕ) (r : StageIndex) (a : AlphaIndex)
    (j : SourceBetaBandIndex) : Set Path :=
  xEastRightWinnerContextualFailure C m r a j ∩
    xEastOddStoppedHorizonEvent m (stageNumber r)

def xEastRightEvenTerminalWinnerContextualFailure
    (C : ℝ) (m : ℕ) (r : StageIndex) (a : AlphaIndex)
    (j : SourceBetaBandIndex) : Set Path :=
  xEastRightWinnerContextualFailure C m r a j ∩
    xEastEvenStoppedHorizonEvent m (stageNumber r)

theorem xEastLeftWinnerContextualFailure_subset_parity_union
    (C : ℝ) (m : ℕ) (r : StageIndex) (a : AlphaIndex)
    (j : SourceBetaBandIndex) :
    xEastLeftWinnerContextualFailure C m r a j ⊆
      xEastLeftEvenWinnerContextualFailure C m r a j ∪
        xEastLeftOddTerminalWinnerContextualFailure C m r a j := by
  intro s hs
  by_cases hEven : Even
      (firstKSitesReachLevel m (stageNumber r) s).untopA
  · exact Or.inl ⟨hs, hEven⟩
  · exact Or.inr ⟨hs, hEven⟩

theorem xEastRightWinnerContextualFailure_subset_parity_union
    (C : ℝ) (m : ℕ) (r : StageIndex) (a : AlphaIndex)
    (j : SourceBetaBandIndex) :
    xEastRightWinnerContextualFailure C m r a j ⊆
      xEastRightOddWinnerContextualFailure C m r a j ∪
        xEastRightEvenTerminalWinnerContextualFailure C m r a j := by
  intro s hs
  by_cases hEven : Even
      (firstKSitesReachLevel m (stageNumber r) s).untopA
  · exact Or.inr ⟨hs, hEven⟩
  · exact Or.inl ⟨hs, hEven⟩

structure XEastThetaFreeGoodBandData
    (cWindow m : ℕ) (C : ℝ) (r : StageIndex) (a : AlphaIndex)
    (j : SourceBetaBandIndex) where
  left : LeftWinnerParityGoodBandDecomposition cWindow m C
    (sourceBeta (alphaValue a) j)
    (xEastLeftWinnerContextualFailure C m r a j)
    (prop45FailureEvent sourceCanonicalProfiles canonicalCStar
      m (xIndex east) r (alphaValue a))
  right : RightWinnerParityGoodBandDecomposition cWindow m C
    (sourceBeta (alphaValue a) j)
    (xEastRightWinnerContextualFailure C m r a j)
    (prop45FailureEvent sourceCanonicalProfiles canonicalCStar
      m (xIndex east) r (alphaValue a))

/-- Source-faithful X-east data: the source supplies one decomposition for
each of the four literal winner/parity branches, while the branch events and
their union covers are fixed by the definitions above. -/
structure XEastCanonicalThetaFreeGoodBandData
    (cWindow m : ℕ) (C : ℝ) (r : StageIndex) (a : AlphaIndex)
    (j : SourceBetaBandIndex) where
  unprimedEven : UnprimedEvenGoodBandDecomposition cWindow m C
    (sourceBeta (alphaValue a) j)
    (xEastLeftEvenWinnerContextualFailure C m r a j)
    (prop45FailureEvent sourceCanonicalProfiles canonicalCStar
      m (xIndex east) r (alphaValue a))
  unprimedOddTerminal : UnprimedOddTerminalGoodBandDecomposition
    cWindow m C (sourceBeta (alphaValue a) j)
    (xEastLeftOddTerminalWinnerContextualFailure C m r a j)
    (prop45FailureEvent sourceCanonicalProfiles canonicalCStar
      m (xIndex east) r (alphaValue a))
  primedOdd : PrimedOddGoodBandDecomposition cWindow m C
    (sourceBeta (alphaValue a) j)
    (xEastRightOddWinnerContextualFailure C m r a j)
    (prop45FailureEvent sourceCanonicalProfiles canonicalCStar
      m (xIndex east) r (alphaValue a))
  primedEvenTerminal : PrimedEvenTerminalGoodBandDecomposition
    cWindow m C (sourceBeta (alphaValue a) j)
    (xEastRightEvenTerminalWinnerContextualFailure C m r a j)
    (prop45FailureEvent sourceCanonicalProfiles canonicalCStar
      m (xIndex east) r (alphaValue a))

/-! ### The same deleted-path witness as the equation-(4.47) base step

The fixed-profile categorical package in the preceding interface predates
the literal changed-deleted-path proof of (4.47).  The following record is
the narrower source form.  Each of the four stopping-parity/winner branches
contains a literal stopped source atom and the actual path witness from
(4.51)--(4.54).  Proposition 4.8 then needs only its two deterministic
band-specific preimage inclusions.  No second same-profile categorical law
or probability estimate is stored here.

The active coordinates depend on the beta band, so this record deliberately
does not identify them with the fixed `kappaOne` coordinates used later in
Lemmas 4.11--4.12.  What is shared is the checked path-switch mechanism. -/

structure XEastCanonicalPathWitnessGoodBandData
    (cWindow m : ℕ) (witnessRate capCoeff : ℝ)
    (r : StageIndex) (a : AlphaIndex) (j : SourceBetaBandIndex) where
  unprimedEven : ℕ → UnprimedEvenLeftWinnerSource m
  unprimedOddTerminal : ℕ → UnprimedOddTerminalTieLeftSource m
  primedOdd : ℕ → PrimedOddStrictRightWinnerSource m
  primedEvenTerminal : ℕ → PrimedEvenTerminalStrictRightSource m
  unprimedEvenRemaining : ∀ eta,
    Equation447PathWitnessBranchRemainingData cWindow m witnessRate
      ((1 / 4 : ℝ) * Real.log (m : ℝ) ^ 2)
      (xEastLeftEvenWinnerContextualFailure capCoeff m r a j)
      (unprimedEven eta).pathAtom (unprimedEven eta).profile
      (unprimedEven eta).lazyVector (unprimedEven eta).nextDirection
  unprimedOddTerminalRemaining : ∀ eta,
    Equation447PathWitnessBranchRemainingData cWindow m witnessRate
      ((1 / 4 : ℝ) * Real.log (m : ℝ) ^ 2)
      (xEastLeftOddTerminalWinnerContextualFailure capCoeff m r a j)
      (unprimedOddTerminal eta).pathAtom
      (unprimedOddTerminal eta).profile
      (unprimedOddTerminal eta).lazyVector
      (unprimedOddTerminal eta).nextDirection
  primedOddRemaining : ∀ eta,
    Equation447PathWitnessBranchRemainingData cWindow m witnessRate
      ((1 / 4 : ℝ) * Real.log (m : ℝ) ^ 2)
      (xEastRightOddWinnerContextualFailure capCoeff m r a j)
      (primedOdd eta).pathAtom (primedOdd eta).profile
      (primedOdd eta).lazyVector (primedOdd eta).nextDirection
  primedEvenTerminalRemaining : ∀ eta,
    Equation447PathWitnessBranchRemainingData cWindow m witnessRate
      ((1 / 4 : ℝ) * Real.log (m : ℝ) ^ 2)
      (xEastRightEvenTerminalWinnerContextualFailure capCoeff m r a j)
      (primedEvenTerminal eta).pathAtom
      (primedEvenTerminal eta).profile
      (primedEvenTerminal eta).lazyVector
      (primedEvenTerminal eta).nextDirection
  unprimedEven_failure : ∀ eta,
    xEastLeftEvenWinnerContextualFailure capCoeff m r a j ∩
        (unprimedEven eta).pathAtom ⊆
      (fun s ↦ ((unprimedEven eta).lazyVector s,
        (unprimedEven eta).nextDirection s)) ⁻¹'
        (((sourceProfileQEvent m
            (sourceAlphaIntervalCount m (sourceBeta (alphaValue a) j))
            (unprimedEven eta).profile
            (geometricThreshold (Real.log (m : ℝ) ^ 2)
              (sourceLemma411GrowthFactor cWindow)
              (sourceAlphaIntervalCount m
                (sourceBeta (alphaValue a) j))) ∩
              (unprimedEvenRemaining eta).D)) ×ˢ
            (Set.univ : Set Direction))
  unprimedOddTerminal_failure : ∀ eta,
    xEastLeftOddTerminalWinnerContextualFailure capCoeff m r a j ∩
        (unprimedOddTerminal eta).pathAtom ⊆
      (fun s ↦ ((unprimedOddTerminal eta).lazyVector s,
        (unprimedOddTerminal eta).nextDirection s)) ⁻¹'
        (((sourceProfileQEvent m
            (sourceAlphaIntervalCount m (sourceBeta (alphaValue a) j))
            (unprimedOddTerminal eta).profile
            (geometricThreshold (Real.log (m : ℝ) ^ 2)
              (sourceLemma411GrowthFactor cWindow)
              (sourceAlphaIntervalCount m
                (sourceBeta (alphaValue a) j))) ∩
              (unprimedOddTerminalRemaining eta).D)) ×ˢ
            (Set.univ : Set Direction))
  primedOdd_failure : ∀ eta,
    xEastRightOddWinnerContextualFailure capCoeff m r a j ∩
        (primedOdd eta).pathAtom ⊆
      (fun s ↦ ((primedOdd eta).lazyVector s,
        (primedOdd eta).nextDirection s)) ⁻¹'
        (((sourceProfileQEvent m
            (sourceAlphaIntervalCount m (sourceBeta (alphaValue a) j))
            (primedOdd eta).profile
            (geometricThreshold (Real.log (m : ℝ) ^ 2)
              (sourceLemma411GrowthFactor cWindow)
              (sourceAlphaIntervalCount m
                (sourceBeta (alphaValue a) j))) ∩
              (primedOddRemaining eta).D)) ×ˢ
            (Set.univ : Set Direction))
  primedEvenTerminal_failure : ∀ eta,
    xEastRightEvenTerminalWinnerContextualFailure capCoeff m r a j ∩
        (primedEvenTerminal eta).pathAtom ⊆
      (fun s ↦ ((primedEvenTerminal eta).lazyVector s,
        (primedEvenTerminal eta).nextDirection s)) ⁻¹'
        (((sourceProfileQEvent m
            (sourceAlphaIntervalCount m (sourceBeta (alphaValue a) j))
            (primedEvenTerminal eta).profile
            (geometricThreshold (Real.log (m : ℝ) ^ 2)
              (sourceLemma411GrowthFactor cWindow)
              (sourceAlphaIntervalCount m
                (sourceBeta (alphaValue a) j))) ∩
              (primedEvenTerminalRemaining eta).D)) ×ˢ
            (Set.univ : Set Direction))
  unprimedEven_theta : ∀ eta,
    (xEastLeftEvenWinnerContextualFailure capCoeff m r a j ∩
      (unprimedEven eta).pathAtom) ∩
        (fun s ↦ ((unprimedEven eta).lazyVector s,
          (unprimedEven eta).nextDirection s)) ⁻¹'
          (sourceProfileThetaUpTo cWindow m
            (sourceAlphaIntervalCount m (sourceBeta (alphaValue a) j))
            (unprimedEven eta).profile ×ˢ
              (Set.univ : Set Direction)) ⊆
      prop45FailureEvent sourceCanonicalProfiles canonicalCStar
        m (xIndex east) r (alphaValue a)
  unprimedOddTerminal_theta : ∀ eta,
    (xEastLeftOddTerminalWinnerContextualFailure capCoeff m r a j ∩
      (unprimedOddTerminal eta).pathAtom) ∩
        (fun s ↦ ((unprimedOddTerminal eta).lazyVector s,
          (unprimedOddTerminal eta).nextDirection s)) ⁻¹'
          (sourceProfileThetaUpTo cWindow m
            (sourceAlphaIntervalCount m (sourceBeta (alphaValue a) j))
            (unprimedOddTerminal eta).profile ×ˢ
              (Set.univ : Set Direction)) ⊆
      prop45FailureEvent sourceCanonicalProfiles canonicalCStar
        m (xIndex east) r (alphaValue a)
  primedOdd_theta : ∀ eta,
    (xEastRightOddWinnerContextualFailure capCoeff m r a j ∩
      (primedOdd eta).pathAtom) ∩
        (fun s ↦ ((primedOdd eta).lazyVector s,
          (primedOdd eta).nextDirection s)) ⁻¹'
          (sourceProfileThetaUpTo cWindow m
            (sourceAlphaIntervalCount m (sourceBeta (alphaValue a) j))
            (primedOdd eta).profile ×ˢ
              (Set.univ : Set Direction)) ⊆
      prop45FailureEvent sourceCanonicalProfiles canonicalCStar
        m (xIndex east) r (alphaValue a)
  primedEvenTerminal_theta : ∀ eta,
    (xEastRightEvenTerminalWinnerContextualFailure capCoeff m r a j ∩
      (primedEvenTerminal eta).pathAtom) ∩
        (fun s ↦ ((primedEvenTerminal eta).lazyVector s,
          (primedEvenTerminal eta).nextDirection s)) ⁻¹'
          (sourceProfileThetaUpTo cWindow m
            (sourceAlphaIntervalCount m (sourceBeta (alphaValue a) j))
            (primedEvenTerminal eta).profile ×ˢ
              (Set.univ : Set Direction)) ⊆
      prop45FailureEvent sourceCanonicalProfiles canonicalCStar
        m (xIndex east) r (alphaValue a)
  unprimedEven_cover :
    xEastLeftEvenWinnerContextualFailure capCoeff m r a j ⊆
      ⋃ eta, (unprimedEven eta).pathAtom
  unprimedOddTerminal_cover :
    xEastLeftOddTerminalWinnerContextualFailure capCoeff m r a j ⊆
      ⋃ eta, (unprimedOddTerminal eta).pathAtom
  primedOdd_cover :
    xEastRightOddWinnerContextualFailure capCoeff m r a j ⊆
      ⋃ eta, (primedOdd eta).pathAtom
  primedEvenTerminal_cover :
    xEastRightEvenTerminalWinnerContextualFailure capCoeff m r a j ⊆
      ⋃ eta, (primedEvenTerminal eta).pathAtom
  unprimedEven_disjoint : Pairwise fun eta zeta ↦
    Disjoint (unprimedEven eta).pathAtom (unprimedEven zeta).pathAtom
  unprimedOddTerminal_disjoint : Pairwise fun eta zeta ↦
    Disjoint (unprimedOddTerminal eta).pathAtom
      (unprimedOddTerminal zeta).pathAtom
  primedOdd_disjoint : Pairwise fun eta zeta ↦
    Disjoint (primedOdd eta).pathAtom (primedOdd zeta).pathAtom
  primedEvenTerminal_disjoint : Pairwise fun eta zeta ↦
    Disjoint (primedEvenTerminal eta).pathAtom
      (primedEvenTerminal zeta).pathAtom

namespace XEastCanonicalPathWitnessGoodBandData

variable {cWindow m : ℕ} {witnessRate capCoeff : ℝ}
  {r : StageIndex} {a : AlphaIndex} {j : SourceBetaBandIndex}
  (D : XEastCanonicalPathWitnessGoodBandData
    cWindow m witnessRate capCoeff r a j)

noncomputable def unprimedEvenAtom (eta : ℕ) :
    StoppedEquation447PathWitnessBranchAtom cWindow m witnessRate
      (xEastLeftEvenWinnerContextualFailure capCoeff m r a j)
      ((1 / 4 : ℝ) * Real.log (m : ℝ) ^ 2) :=
  (D.unprimedEven eta).toStoppedEquation447PathWitnessBranchAtom
    cWindow witnessRate ((1 / 4 : ℝ) * Real.log (m : ℝ) ^ 2)
    (xEastLeftEvenWinnerContextualFailure capCoeff m r a j)
    (D.unprimedEvenRemaining eta)

noncomputable def unprimedOddTerminalAtom (eta : ℕ) :
    StoppedEquation447PathWitnessBranchAtom cWindow m witnessRate
      (xEastLeftOddTerminalWinnerContextualFailure capCoeff m r a j)
      ((1 / 4 : ℝ) * Real.log (m : ℝ) ^ 2) :=
  (D.unprimedOddTerminal eta).toStoppedEquation447PathWitnessBranchAtom
    cWindow witnessRate ((1 / 4 : ℝ) * Real.log (m : ℝ) ^ 2)
    (xEastLeftOddTerminalWinnerContextualFailure capCoeff m r a j)
    (D.unprimedOddTerminalRemaining eta)

noncomputable def primedOddAtom (eta : ℕ) :
    StoppedEquation447PathWitnessBranchAtom cWindow m witnessRate
      (xEastRightOddWinnerContextualFailure capCoeff m r a j)
      ((1 / 4 : ℝ) * Real.log (m : ℝ) ^ 2) :=
  (D.primedOdd eta).toStoppedEquation447PathWitnessBranchAtom
    cWindow witnessRate ((1 / 4 : ℝ) * Real.log (m : ℝ) ^ 2)
    (xEastRightOddWinnerContextualFailure capCoeff m r a j)
    (D.primedOddRemaining eta)

noncomputable def primedEvenTerminalAtom (eta : ℕ) :
    StoppedEquation447PathWitnessBranchAtom cWindow m witnessRate
      (xEastRightEvenTerminalWinnerContextualFailure capCoeff m r a j)
      ((1 / 4 : ℝ) * Real.log (m : ℝ) ^ 2) :=
  (D.primedEvenTerminal eta).toStoppedEquation447PathWitnessBranchAtom
    cWindow witnessRate ((1 / 4 : ℝ) * Real.log (m : ℝ) ^ 2)
    (xEastRightEvenTerminalWinnerContextualFailure capCoeff m r a j)
    (D.primedEvenTerminalRemaining eta)

@[simp] theorem unprimedEvenAtom_pathAtom (eta : ℕ) :
    (D.unprimedEvenAtom eta).pathAtom = (D.unprimedEven eta).pathAtom := by
  rfl

@[simp] theorem unprimedOddTerminalAtom_pathAtom (eta : ℕ) :
    (D.unprimedOddTerminalAtom eta).pathAtom =
      (D.unprimedOddTerminal eta).pathAtom := by
  rfl

@[simp] theorem primedOddAtom_pathAtom (eta : ℕ) :
    (D.primedOddAtom eta).pathAtom = (D.primedOdd eta).pathAtom := by
  rfl

@[simp] theorem primedEvenTerminalAtom_pathAtom (eta : ℕ) :
    (D.primedEvenTerminalAtom eta).pathAtom =
      (D.primedEvenTerminal eta).pathAtom := by
  rfl

end XEastCanonicalPathWitnessGoodBandData

/-- Countably many literal changed-path atoms control one Proposition-4.8
winner/parity branch.  The only atomwise hypotheses are the two deterministic
band preimage inclusions. -/
theorem measure_diff_le_of_pathWitnessGoodBandAtoms
    {cWindow m : ℕ} {witnessRate cBase alpha rho : ℝ}
    {failure thetaPath : Set Path}
    (atoms : ℕ → StoppedEquation447PathWitnessBranchAtom
      cWindow m witnessRate failure rho)
    (cover : failure ⊆ ⋃ eta, (atoms eta).pathAtom)
    (pairwise_disjoint : Pairwise fun eta zeta ↦
      Disjoint (atoms eta).pathAtom (atoms zeta).pathAtom)
    (G : SourceProp48NumericalAt cWindow m cBase 1 1)
    (hwitnessRate : 0 < witnessRate)
    (halpha : kappaOne ≤ alpha) (hAlpha : alpha ≤ (4 : ℝ) / 5)
    (hrho : rho ≤ Real.log (m : ℝ) ^ 2)
    (failure_subset : ∀ eta, failure ∩ (atoms eta).pathAtom ⊆
      (fun s ↦ ((atoms eta).lazyVector s,
        (atoms eta).nextDirection s)) ⁻¹'
        (((@sourceProfileQEvent (atoms eta).Coord
            (atoms eta).coordFintype m
            (sourceAlphaIntervalCount m alpha) (atoms eta).profile
            (geometricThreshold (Real.log (m : ℝ) ^ 2)
              (sourceLemma411GrowthFactor cWindow)
              (sourceAlphaIntervalCount m alpha)) ∩ (atoms eta).D)) ×ˢ
          (Set.univ : Set Direction)))
    (theta_subset : ∀ eta,
      (failure ∩ (atoms eta).pathAtom) ∩
        (fun s ↦ ((atoms eta).lazyVector s,
          (atoms eta).nextDirection s)) ⁻¹'
          ((@sourceProfileThetaUpTo (atoms eta).Coord
              (atoms eta).coordFintype cWindow m
              (sourceAlphaIntervalCount m alpha) (atoms eta).profile) ×ˢ
            (Set.univ : Set Direction)) ⊆ thetaPath)
    (hbaseAbsorb :
      4 * (Real.exp (-witnessRate * rho) *
          (1 - Real.exp (-witnessRate))⁻¹) ≤
        Real.exp (-cBase * Real.log (m : ℝ) ^ 2))
    (tail : ℝ≥0∞)
    (hshift : ENNReal.ofReal (Real.exp (-(min cBase
      (imbalanceRate (Real.exp
        (sourceAdjacentComparisonExponent cWindow))) / 2) *
          Real.log (m : ℝ) ^ 2)) ≤ tail) :
    simpleRandomWalkLaw (failure \ thetaPath) ≤ tail := by
  apply measure_diff_le_of_disjoint_stopped_atoms
    (fun eta ↦ (atoms eta).pathAtom) tail cover pairwise_disjoint
  · intro eta
    exact (atoms eta).measurableSet_pathAtom
  · intro eta
    exact stoppedEquation447PathWitnessBranchAtom_prop48_good_band_local_bound
      (atoms eta) G hwitnessRate halpha hAlpha hrho
      (failure_subset eta) (theta_subset eta) hbaseAbsorb tail hshift

/-- The four literal winner/parity branches, all controlled by the actual
changed-deleted-path base step. -/
theorem XEastCanonicalPathWitnessGoodBandData.measure_diff_le
    {cWindow m : ℕ} {witnessRate capCoeff cBase : ℝ}
    {r : StageIndex} {a : AlphaIndex} {j : SourceBetaBandIndex}
    (D : XEastCanonicalPathWitnessGoodBandData
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
        (xEastLeftEvenWinnerContextualFailure capCoeff m r a j \
          prop45FailureEvent sourceCanonicalProfiles canonicalCStar
            m (xIndex east) r (alphaValue a)) ≤ tail ∧
      simpleRandomWalkLaw
        (xEastLeftOddTerminalWinnerContextualFailure capCoeff m r a j \
          prop45FailureEvent sourceCanonicalProfiles canonicalCStar
            m (xIndex east) r (alphaValue a)) ≤ tail ∧
      simpleRandomWalkLaw
        (xEastRightOddWinnerContextualFailure capCoeff m r a j \
          prop45FailureEvent sourceCanonicalProfiles canonicalCStar
            m (xIndex east) r (alphaValue a)) ≤ tail ∧
      simpleRandomWalkLaw
        (xEastRightEvenTerminalWinnerContextualFailure capCoeff m r a j \
          prop45FailureEvent sourceCanonicalProfiles canonicalCStar
            m (xIndex east) r (alphaValue a)) ≤ tail := by
  have hrho : (1 / 4 : ℝ) * Real.log (m : ℝ) ^ 2 ≤
      Real.log (m : ℝ) ^ 2 := by
    nlinarith [sq_nonneg (Real.log (m : ℝ))]
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact measure_diff_le_of_pathWitnessGoodBandAtoms
      D.unprimedEvenAtom D.unprimedEven_cover
      D.unprimedEven_disjoint G hwitnessRate halpha hAlpha hrho
      D.unprimedEven_failure D.unprimedEven_theta hbaseAbsorb tail hshift
  · exact measure_diff_le_of_pathWitnessGoodBandAtoms
      D.unprimedOddTerminalAtom D.unprimedOddTerminal_cover
      D.unprimedOddTerminal_disjoint G hwitnessRate halpha hAlpha hrho
      D.unprimedOddTerminal_failure D.unprimedOddTerminal_theta
      hbaseAbsorb tail hshift
  · exact measure_diff_le_of_pathWitnessGoodBandAtoms
      D.primedOddAtom D.primedOdd_cover D.primedOdd_disjoint G
      hwitnessRate halpha hAlpha hrho D.primedOdd_failure
      D.primedOdd_theta hbaseAbsorb tail hshift
  · exact measure_diff_le_of_pathWitnessGoodBandAtoms
      D.primedEvenTerminalAtom D.primedEvenTerminal_cover
      D.primedEvenTerminal_disjoint G hwitnessRate halpha hAlpha hrho
      D.primedEvenTerminal_failure D.primedEvenTerminal_theta
      hbaseAbsorb tail hshift

/-- Literal changed-path Proposition-4.8 input at X-east.  Compared with
`Prop47Lemma410Prop48CanonicalThetaFreeXEastLowBandInputs`, this predicate
does not contain a second fixed-profile categorical package: the base band
is a consequence of the same path-switch estimate as equation (4.47). -/
def Prop47Lemma410Prop48CanonicalPathWitnessXEastLowBandInputs
    (cWindow : ℕ) (witnessRate capCoeff : ℝ) : Prop :=
  ∀ᶠ m : ℕ in atTop, ∀ r : StageIndex, ∀ a : AlphaIndex,
    alphaValue a ≤ kappaTwo → ∀ j : SourceBetaBandIndex,
    sourceBeta (alphaValue a) j ≤ (7 : ℝ) / 10 →
    Nonempty (XEastCanonicalPathWitnessGoodBandData
      cWindow m witnessRate capCoeff r a j)

def XEastCanonicalThetaFreeGoodBandData.toThetaFreeGoodBandData
    {cWindow m : ℕ} {C : ℝ} {r : StageIndex} {a : AlphaIndex}
    {j : SourceBetaBandIndex}
    (D : XEastCanonicalThetaFreeGoodBandData cWindow m C r a j) :
    XEastThetaFreeGoodBandData cWindow m C r a j where
  left :=
    { evenFailure := xEastLeftEvenWinnerContextualFailure C m r a j
      oddTerminalFailure :=
        xEastLeftOddTerminalWinnerContextualFailure C m r a j
      cover := xEastLeftWinnerContextualFailure_subset_parity_union C m r a j
      even := D.unprimedEven
      oddTerminal := D.unprimedOddTerminal }
  right :=
    { oddFailure := xEastRightOddWinnerContextualFailure C m r a j
      evenTerminalFailure :=
        xEastRightEvenTerminalWinnerContextualFailure C m r a j
      cover := xEastRightWinnerContextualFailure_subset_parity_union C m r a j
      odd := D.primedOdd
      evenTerminal := D.primedEvenTerminal }

/-- Literal theta-free Proposition-4.8 input at X-east.  Its atom records
contain equation-(4.47) data and deterministic event identifications only;
the former fixed-profile probability fields are absent. -/
def Prop47Lemma410Prop48ThetaFreeXEastLowBandInputs
    (cWindow : ℕ) (C : ℝ) : Prop :=
  ∀ᶠ m : ℕ in atTop, ∀ r : StageIndex, ∀ a : AlphaIndex,
    alphaValue a ≤ kappaTwo → ∀ j : SourceBetaBandIndex,
    sourceBeta (alphaValue a) j ≤ (7 : ℝ) / 10 →
    Nonempty (XEastThetaFreeGoodBandData cWindow m C r a j)

/-- Canonical version of the X-east theta-free input.  It contains no
caller-chosen stopping-parity events and no parity-cover field. -/
def Prop47Lemma410Prop48CanonicalThetaFreeXEastLowBandInputs
    (cWindow : ℕ) (C : ℝ) : Prop :=
  ∀ᶠ m : ℕ in atTop, ∀ r : StageIndex, ∀ a : AlphaIndex,
    alphaValue a ≤ kappaTwo → ∀ j : SourceBetaBandIndex,
    sourceBeta (alphaValue a) j ≤ (7 : ℝ) / 10 →
    Nonempty (XEastCanonicalThetaFreeGoodBandData cWindow m C r a j)

theorem prop47Lemma410Prop48ThetaFreeXEastLowBandInputs_of_canonical
    {cWindow : ℕ} {C : ℝ}
    (h : Prop47Lemma410Prop48CanonicalThetaFreeXEastLowBandInputs
      cWindow C) :
    Prop47Lemma410Prop48ThetaFreeXEastLowBandInputs cWindow C := by
  filter_upwards [h] with m hm
  intro r a ha j hj
  rcases hm r a ha j hj with ⟨D⟩
  exact ⟨D.toThetaFreeGoodBandData⟩

/-- Strong atom-conditioned alternative to the single-event theta-free
package.  Every stopped atom supplies a separate arbitrary-interval
Proposition-4.5 input for every level in the Proposition-4.8 recursion.
Because stopped conditioning truncates the holding law, this package is not
used by the final literal source closure. -/
structure XEastSourceBandedGoodBandData
    (cWindow m : ℕ) (C : ℝ) (r : StageIndex) (a : AlphaIndex)
    (j : SourceBetaBandIndex) where
  left : LeftWinnerSourceBandedGoodBandDecomposition cWindow m C
    (sourceBeta (alphaValue a) j)
    (xEastLeftWinnerContextualFailure C m r a j)
  right : RightWinnerSourceBandedGoodBandDecomposition cWindow m C
    (sourceBeta (alphaValue a) j)
    (xEastRightWinnerContextualFailure C m r a j)

def Prop47Lemma410Prop48SourceBandedXEastLowBandInputs
    (cWindow : ℕ) (C : ℝ) : Prop :=
  ∀ᶠ m : ℕ in atTop, ∀ r : StageIndex, ∀ a : AlphaIndex,
    alphaValue a ≤ kappaTwo → ∀ j : SourceBetaBandIndex,
    sourceBeta (alphaValue a) j ≤ (7 : ℝ) / 10 →
    Nonempty (XEastSourceBandedGoodBandData cWindow m C r a j)

/-- The literal theta-free stopped decompositions control the complete
contextual `X₁` candidate failure outside the single Proposition-4.5 event.
Equation (4.47) supplies the base estimate internally, and the two binary
unions (stopping parity and winner side) are absorbed by exponent doubling. -/
theorem prop47Lemma410Prop48ThetaFree_xEast_lowBands
    (cWindow : ℕ) {Csmall Cfull d : ℝ}
    (hCsmall : 0 < Csmall) (hgap : Csmall + 20 ≤ Cfull)
    (hd : 0 < d)
    (hcompare : 16 * d ≤
      min (Real.log ((Csmall + 1) / Csmall) / 2)
        (imbalanceRate
          (Real.exp (sourceAdjacentComparisonExponent cWindow))) / 2)
    (h : Prop47Lemma410Prop48ThetaFreeXEastLowBandInputs
      cWindow Csmall) :
    ∀ᶠ m : ℕ in atTop, ∀ r : StageIndex, ∀ a : AlphaIndex,
      alphaValue a ≤ kappaTwo → ∀ j : SourceBetaBandIndex,
      sourceBeta (alphaValue a) j ≤ (7 : ℝ) / 10 →
      simpleRandomWalkLaw
          (xEastCandidateContextualFailure Cfull m r a j \
            prop45FailureEvent sourceCanonicalProfiles canonicalCStar
              m (xIndex east) r (alphaValue a)) ≤
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
    (d := 4 * d) (by positivity) (by
      dsimp [cBase] at hcompare ⊢
      nlinarith [hcompare])
  have habsorbParity :=
    eventually_two_mul_sourceBetaCandidateTail_two_mul_le (show 0 < 2 * d by
      positivity)
  have habsorbWinner :=
    eventually_two_mul_sourceBetaCandidateTail_two_mul_le hd
  have hcover := eventually_fullCandidateFailure_subset_smallWinnerFailures_xEast
    hCsmall.le hgap
  filter_upwards [h, hgood, hbase, hshift, habsorbParity, habsorbWinner,
      hcover] with m hm hgoodM hbaseM hshiftM habsorbParityM
        habsorbWinnerM hcoverM
  intro r a ha j hj
  rcases hm r a ha j hj with ⟨D⟩
  have halpha : kappaOne ≤ sourceBeta (alphaValue a) j :=
    kappaOne_le_sourceBeta ha j
  have hAlpha : sourceBeta (alphaValue a) j ≤ (4 : ℝ) / 5 :=
    hj.trans (by norm_num)
  have habsorbParityM' :
      2 * sourceBetaCandidateTail (4 * d) m ≤
        sourceBetaCandidateTail (2 * d) m := by
    convert habsorbParityM using 1 <;> ring
  have hleftRaw :=
    measure_diff_le_of_leftWinnerParityGoodBandDecomposition D.left
      hgoodM hCsmall halpha hAlpha (by
        dsimp [cBase]
        exact hbaseM)
      (sourceBetaCandidateTail (4 * d) m)
      (sourceBetaCandidateTail (2 * d) m) hshiftM habsorbParityM'
  have hrightRaw :=
    measure_diff_le_of_rightWinnerParityGoodBandDecomposition D.right
      hgoodM hCsmall halpha hAlpha (by
        dsimp [cBase]
        exact hbaseM)
      (sourceBetaCandidateTail (4 * d) m)
      (sourceBetaCandidateTail (2 * d) m) hshiftM habsorbParityM'
  let theta := prop45FailureEvent sourceCanonicalProfiles canonicalCStar
    m (xIndex east) r (alphaValue a)
  have hleft : simpleRandomWalkLaw
      (xEastLeftWinnerContextualFailure Csmall m r a j \ theta) ≤
      sourceBetaCandidateTail (2 * d) m := by
    simpa only [theta] using hleftRaw
  have hright : simpleRandomWalkLaw
      (xEastRightWinnerContextualFailure Csmall m r a j \ theta) ≤
      sourceBetaCandidateTail (2 * d) m := by
    simpa only [theta] using hrightRaw
  have hcontextCover : xEastCandidateContextualFailure Cfull m r a j ⊆
      xEastLeftWinnerContextualFailure Csmall m r a j ∪
        xEastRightWinnerContextualFailure Csmall m r a j := by
    intro omega homega
    have heast : xIndex east = (0 : Fin 6) := by
      apply Fin.ext
      rfl
    have hprefix : omega ∈
        hlozCandidateCapFailureEvent
              (sourceLemma410Window m (alphaValue a)) m (stageNumber r)
              (sourceBetaCandidateThreshold m (alphaValue a) j)
              (sourceBetaCandidateCap Cfull m (alphaValue a) j) ∩
            prefixPairingEvent m (0 : Fin 6) (stageNumber r + 1) := by
      refine ⟨homega.1, ?_⟩
      rw [← heast]
      exact homega.2.1.1
    rcases hcoverM r a ha j hprefix with hleft' | hright'
    · exact Or.inl ⟨hleft'.1, homega.2⟩
    · exact Or.inr ⟨hright'.1, homega.2⟩
  calc
    simpleRandomWalkLaw
        (xEastCandidateContextualFailure Cfull m r a j \ theta) ≤
      simpleRandomWalkLaw
        ((xEastLeftWinnerContextualFailure Csmall m r a j \ theta) ∪
          (xEastRightWinnerContextualFailure Csmall m r a j \ theta)) := by
        apply measure_mono
        intro omega homega
        rcases hcontextCover homega.1 with hleft' | hright'
        · exact Or.inl ⟨hleft', homega.2⟩
        · exact Or.inr ⟨hright', homega.2⟩
    _ ≤ simpleRandomWalkLaw
          (xEastLeftWinnerContextualFailure Csmall m r a j \ theta) +
        simpleRandomWalkLaw
          (xEastRightWinnerContextualFailure Csmall m r a j \ theta) :=
      measure_union_le _ _
    _ ≤ sourceBetaCandidateTail (2 * d) m +
        sourceBetaCandidateTail (2 * d) m := add_le_add hleft hright
    _ = 2 * sourceBetaCandidateTail (2 * d) m := by ring
    _ ≤ sourceBetaCandidateTail d m := habsorbWinnerM

/-- Low-band candidate estimate from the literal changed-deleted-path
witness.  The four branches use the same fixed-cardinality switch as
equation (4.47); the two parity unions and the final winner union are the
only probabilistic losses after the atomwise estimate. -/
theorem prop47Lemma410Prop48PathWitness_xEast_lowBands
    (cWindow : ℕ) {witnessRate Csmall Cfull d : ℝ}
    (hwitnessRate : 0 < witnessRate)
    (hCsmall : 0 < Csmall) (hgap : Csmall + 20 ≤ Cfull)
    (hd : 0 < d)
    (hcompare : 16 * d ≤
      min (witnessRate / 8)
        (imbalanceRate
          (Real.exp (sourceAdjacentComparisonExponent cWindow))) / 2)
    (h : Prop47Lemma410Prop48CanonicalPathWitnessXEastLowBandInputs
      cWindow witnessRate Csmall) :
    ∀ᶠ m : ℕ in atTop, ∀ r : StageIndex, ∀ a : AlphaIndex,
      alphaValue a ≤ kappaTwo → ∀ j : SourceBetaBandIndex,
      sourceBeta (alphaValue a) j ≤ (7 : ℝ) / 10 →
      simpleRandomWalkLaw
          (xEastCandidateContextualFailure Cfull m r a j \
            prop45FailureEvent sourceCanonicalProfiles canonicalCStar
              m (xIndex east) r (alphaValue a)) ≤
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
    (d := 4 * d) (by positivity) (by
      dsimp [cBase] at hcompare ⊢
      nlinarith [hcompare])
  have habsorbParity :=
    eventually_two_mul_sourceBetaCandidateTail_two_mul_le
      (show 0 < 2 * d by positivity)
  have habsorbWinner :=
    eventually_two_mul_sourceBetaCandidateTail_two_mul_le hd
  have hcover := eventually_fullCandidateFailure_subset_smallWinnerFailures_xEast
    hCsmall.le hgap
  filter_upwards [h, hgood, hbase, hshift, habsorbParity,
      habsorbWinner, hcover] with m hm hgoodM hbaseM hshiftM
        habsorbParityM habsorbWinnerM hcoverM
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
  let tailFour := sourceBetaCandidateTail (4 * d) m
  let tailTwo := sourceBetaCandidateTail (2 * d) m
  have hbranches := D.measure_diff_le hgoodM hwitnessRate halpha hAlpha
    hbaseM' tailFour (by simpa only [tailFour] using hshiftM)
  rcases hbranches with ⟨heven, hodd, hrightOdd, hrightEven⟩
  let theta := prop45FailureEvent sourceCanonicalProfiles canonicalCStar
    m (xIndex east) r (alphaValue a)
  have habsorbParityM' : 2 * tailFour ≤ tailTwo := by
    dsimp [tailFour, tailTwo]
    have h4 : 2 * (2 * d) = 4 * d := by ring
    simpa only [h4] using habsorbParityM
  have hleft : simpleRandomWalkLaw
      (xEastLeftWinnerContextualFailure Csmall m r a j \ theta) ≤
        tailTwo := by
    calc
      simpleRandomWalkLaw
          (xEastLeftWinnerContextualFailure Csmall m r a j \ theta) ≤
        simpleRandomWalkLaw
          ((xEastLeftEvenWinnerContextualFailure Csmall m r a j \ theta) ∪
            (xEastLeftOddTerminalWinnerContextualFailure
              Csmall m r a j \ theta)) := by
          apply measure_mono
          intro omega homega
          rcases xEastLeftWinnerContextualFailure_subset_parity_union
              Csmall m r a j homega.1 with h | h
          · exact Or.inl ⟨h, homega.2⟩
          · exact Or.inr ⟨h, homega.2⟩
      _ ≤ simpleRandomWalkLaw
          (xEastLeftEvenWinnerContextualFailure Csmall m r a j \ theta) +
        simpleRandomWalkLaw
          (xEastLeftOddTerminalWinnerContextualFailure
            Csmall m r a j \ theta) := measure_union_le _ _
      _ ≤ tailFour + tailFour := by
        exact add_le_add (by simpa only [theta] using heven)
          (by simpa only [theta] using hodd)
      _ = 2 * tailFour := by ring
      _ ≤ tailTwo := habsorbParityM'
  have hright : simpleRandomWalkLaw
      (xEastRightWinnerContextualFailure Csmall m r a j \ theta) ≤
        tailTwo := by
    calc
      simpleRandomWalkLaw
          (xEastRightWinnerContextualFailure Csmall m r a j \ theta) ≤
        simpleRandomWalkLaw
          ((xEastRightOddWinnerContextualFailure Csmall m r a j \ theta) ∪
            (xEastRightEvenTerminalWinnerContextualFailure
              Csmall m r a j \ theta)) := by
          apply measure_mono
          intro omega homega
          rcases xEastRightWinnerContextualFailure_subset_parity_union
              Csmall m r a j homega.1 with h | h
          · exact Or.inl ⟨h, homega.2⟩
          · exact Or.inr ⟨h, homega.2⟩
      _ ≤ simpleRandomWalkLaw
          (xEastRightOddWinnerContextualFailure Csmall m r a j \ theta) +
        simpleRandomWalkLaw
          (xEastRightEvenTerminalWinnerContextualFailure
            Csmall m r a j \ theta) := measure_union_le _ _
      _ ≤ tailFour + tailFour := by
        exact add_le_add (by simpa only [theta] using hrightOdd)
          (by simpa only [theta] using hrightEven)
      _ = 2 * tailFour := by ring
      _ ≤ tailTwo := habsorbParityM'
  have hcontextCover : xEastCandidateContextualFailure Cfull m r a j ⊆
      xEastLeftWinnerContextualFailure Csmall m r a j ∪
        xEastRightWinnerContextualFailure Csmall m r a j := by
    intro omega homega
    have heast : xIndex east = (0 : Fin 6) := by
      apply Fin.ext
      rfl
    have hprefix : omega ∈
        hlozCandidateCapFailureEvent
              (sourceLemma410Window m (alphaValue a)) m (stageNumber r)
              (sourceBetaCandidateThreshold m (alphaValue a) j)
              (sourceBetaCandidateCap Cfull m (alphaValue a) j) ∩
            prefixPairingEvent m (0 : Fin 6) (stageNumber r + 1) := by
      refine ⟨homega.1, ?_⟩
      rw [← heast]
      exact homega.2.1.1
    rcases hcoverM r a ha j hprefix with hleft' | hright'
    · exact Or.inl ⟨hleft'.1, homega.2⟩
    · exact Or.inr ⟨hright'.1, homega.2⟩
  calc
    simpleRandomWalkLaw
        (xEastCandidateContextualFailure Cfull m r a j \ theta) ≤
      simpleRandomWalkLaw
        ((xEastLeftWinnerContextualFailure Csmall m r a j \ theta) ∪
          (xEastRightWinnerContextualFailure Csmall m r a j \ theta)) := by
        apply measure_mono
        intro omega homega
        rcases hcontextCover homega.1 with hleft' | hright'
        · exact Or.inl ⟨hleft', homega.2⟩
        · exact Or.inr ⟨hright', homega.2⟩
    _ ≤ simpleRandomWalkLaw
          (xEastLeftWinnerContextualFailure Csmall m r a j \ theta) +
        simpleRandomWalkLaw
          (xEastRightWinnerContextualFailure Csmall m r a j \ theta) :=
      measure_union_le _ _
    _ ≤ tailTwo + tailTwo := add_le_add hleft hright
    _ = 2 * tailTwo := by ring
    _ ≤ sourceBetaCandidateTail d m := by
      simpa only [tailTwo] using habsorbWinnerM

/-- The deterministic high-band cardinality estimate completes the literal
changed-path input on all source beta bands. -/
theorem prop47Lemma410Prop48PathWitness_xEast
    (cWindow : ℕ) {witnessRate Csmall Cfull d : ℝ}
    (hwitnessRate : 0 < witnessRate)
    (hCsmall : 0 < Csmall) (hgap : Csmall + 20 ≤ Cfull)
    (hd : 0 < d)
    (hcompare : 16 * d ≤
      min (witnessRate / 8)
        (imbalanceRate
          (Real.exp (sourceAdjacentComparisonExponent cWindow))) / 2)
    (h : Prop47Lemma410Prop48CanonicalPathWitnessXEastLowBandInputs
      cWindow witnessRate Csmall) :
    ∀ᶠ m : ℕ in atTop, ∀ r : StageIndex, ∀ a : AlphaIndex,
      alphaValue a ≤ kappaTwo → ∀ j : SourceBetaBandIndex,
      simpleRandomWalkLaw
          (xEastCandidateContextualFailure Cfull m r a j \
            prop45FailureEvent sourceCanonicalProfiles canonicalCStar
              m (xIndex east) r (alphaValue a)) ≤
        sourceBetaCandidateTail d m := by
  have hlow := prop47Lemma410Prop48PathWitness_xEast_lowBands cWindow
    hwitnessRate hCsmall hgap hd hcompare h
  have hCfull : 0 < Cfull := by linarith
  have hhigh := eventually_hlozCandidateCapFailureEvent_eq_empty_highBands
    hCfull
  filter_upwards [hlow, hhigh] with m hlowM hhighM
  intro r a ha j
  by_cases hj : sourceBeta (alphaValue a) j ≤ (7 : ℝ) / 10
  · exact hlowM r a ha j hj
  · have hempty := hhighM r a ha j (lt_of_not_ge hj)
    rw [xEastCandidateContextualFailure, hempty, empty_inter, empty_diff,
      measure_empty]
    exact bot_le

/-- Source-banded X-east low-band estimate.  The good profile part uses the
checked equation-(4.47) recursion, while each recursive theta band is paid by
its own arbitrary-endpoint Proposition-4.5 input.  The polynomial number of
such bands is absorbed before the two stopping-parity and two winner-side
unions. -/
theorem prop47Lemma410Prop48SourceBanded_xEast_lowBands
    (cWindow : ℕ) {Csmall Cfull d : ℝ}
    (hCsmall : 0 < Csmall) (hgap : Csmall + 20 ≤ Cfull)
    (hd : 0 < d)
    (hcompare : 32 * d ≤
      min (Real.log ((Csmall + 1) / Csmall) / 2)
        (imbalanceRate
          (Real.exp (sourceAdjacentComparisonExponent cWindow))) / 2)
    (h : Prop47Lemma410Prop48SourceBandedXEastLowBandInputs
      cWindow Csmall) :
    ∀ᶠ m : ℕ in atTop, ∀ r : StageIndex, ∀ a : AlphaIndex,
      alphaValue a ≤ kappaTwo → ∀ j : SourceBetaBandIndex,
      sourceBeta (alphaValue a) j ≤ (7 : ℝ) / 10 →
      simpleRandomWalkLaw
          (xEastCandidateContextualFailure Cfull m r a j) ≤
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
    (d := 8 * d) (by positivity) (by
      dsimp [cBase] at hcompare ⊢
      nlinarith [hcompare])
  have htheta :=
    eventually_intervalCount_mul_sourceProp45Error_le_candidateTail
      (show 0 < 8 * d by positivity)
  have habsorbEight :=
    eventually_two_mul_sourceBetaCandidateTail_two_mul_le
      (show 0 < 4 * d by positivity)
  have habsorbFour :=
    eventually_two_mul_sourceBetaCandidateTail_two_mul_le
      (show 0 < 2 * d by positivity)
  have habsorbTwo := eventually_two_mul_sourceBetaCandidateTail_two_mul_le hd
  have hcover := eventually_fullCandidateFailure_subset_smallWinnerFailures_xEast
    hCsmall.le hgap
  have hscales := eventually_sourceRecursiveEndpointScales
  filter_upwards [h, hgood, hbase, hshift, htheta, habsorbEight,
      habsorbFour, habsorbTwo, hcover, hscales] with
      m hm hgoodM hbaseM hshiftM hthetaM habsorbEightM
        habsorbFourM habsorbTwoM hcoverM hscalesM
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
  let tailEight := sourceBetaCandidateTail (8 * d) m
  let tailFour := sourceBetaCandidateTail (4 * d) m
  let tailTwo := sourceBetaCandidateTail (2 * d) m
  let thetaError :=
    (sourceAlphaIntervalCount m (sourceBeta (alphaValue a) j) : ℝ≥0∞) *
      sourceProp45FourBranchError m
  have hthetaError : thetaError ≤ tailEight := by
    dsimp [thetaError, tailEight]
    exact hthetaM (sourceBeta (alphaValue a) j) hAlpha
  have hleftRaw := D.left.measure_le hgoodM hCsmall halpha hAlpha
    hbandScales (by
      dsimp [cBase]
      exact hbaseM) tailEight (by
        dsimp [tailEight]
        exact hshiftM)
  have hrightRaw := D.right.measure_le hgoodM hCsmall halpha hAlpha
    hbandScales (by
      dsimp [cBase]
      exact hbaseM) tailEight (by
        dsimp [tailEight]
        exact hshiftM)
  have hparityAbsorb : 2 * (tailEight + thetaError) ≤ tailTwo := by
    calc
      2 * (tailEight + thetaError) ≤ 2 * (tailEight + tailEight) := by
        gcongr
      _ = 2 * (2 * tailEight) := by ring
      _ ≤ 2 * tailFour := by
        gcongr
        dsimp [tailEight, tailFour]
        have h8 : 2 * (4 * d) = 8 * d := by ring
        simpa only [h8] using habsorbEightM
      _ ≤ tailTwo := by
        dsimp [tailFour, tailTwo]
        have h4 : 2 * (2 * d) = 4 * d := by ring
        simpa only [h4] using habsorbFourM
  have hleft : simpleRandomWalkLaw
      (xEastLeftWinnerContextualFailure Csmall m r a j) ≤ tailTwo :=
    hleftRaw.trans (by simpa only [thetaError] using hparityAbsorb)
  have hright : simpleRandomWalkLaw
      (xEastRightWinnerContextualFailure Csmall m r a j) ≤ tailTwo :=
    hrightRaw.trans (by simpa only [thetaError] using hparityAbsorb)
  have hcontextCover : xEastCandidateContextualFailure Cfull m r a j ⊆
      xEastLeftWinnerContextualFailure Csmall m r a j ∪
        xEastRightWinnerContextualFailure Csmall m r a j := by
    intro omega homega
    have heast : xIndex east = (0 : Fin 6) := by
      apply Fin.ext
      rfl
    have hprefix : omega ∈
        hlozCandidateCapFailureEvent
              (sourceLemma410Window m (alphaValue a)) m (stageNumber r)
              (sourceBetaCandidateThreshold m (alphaValue a) j)
              (sourceBetaCandidateCap Cfull m (alphaValue a) j) ∩
            prefixPairingEvent m (0 : Fin 6) (stageNumber r + 1) := by
      refine ⟨homega.1, ?_⟩
      rw [← heast]
      exact homega.2.1.1
    rcases hcoverM r a ha j hprefix with hleft' | hright'
    · exact Or.inl ⟨hleft'.1, homega.2⟩
    · exact Or.inr ⟨hright'.1, homega.2⟩
  calc
    simpleRandomWalkLaw (xEastCandidateContextualFailure Cfull m r a j) ≤
        simpleRandomWalkLaw
          (xEastLeftWinnerContextualFailure Csmall m r a j ∪
            xEastRightWinnerContextualFailure Csmall m r a j) :=
      measure_mono hcontextCover
    _ ≤ simpleRandomWalkLaw
          (xEastLeftWinnerContextualFailure Csmall m r a j) +
        simpleRandomWalkLaw
          (xEastRightWinnerContextualFailure Csmall m r a j) :=
      measure_union_le _ _
    _ ≤ tailTwo + tailTwo := add_le_add hleft hright
    _ = 2 * tailTwo := by ring
    _ ≤ sourceBetaCandidateTail d m := by
      simpa only [tailTwo, mul_assoc] using habsorbTwoM

/-- The deterministic spatial bound supplies all bands above `7/10`, so the
theta-free contextual estimate holds uniformly on the 454 source bands. -/
theorem prop47Lemma410Prop48ThetaFree_xEast
    (cWindow : ℕ) {Csmall Cfull d : ℝ}
    (hCsmall : 0 < Csmall) (hgap : Csmall + 20 ≤ Cfull)
    (hd : 0 < d)
    (hcompare : 16 * d ≤
      min (Real.log ((Csmall + 1) / Csmall) / 2)
        (imbalanceRate
          (Real.exp (sourceAdjacentComparisonExponent cWindow))) / 2)
    (h : Prop47Lemma410Prop48ThetaFreeXEastLowBandInputs
      cWindow Csmall) :
    ∀ᶠ m : ℕ in atTop, ∀ r : StageIndex, ∀ a : AlphaIndex,
      alphaValue a ≤ kappaTwo → ∀ j : SourceBetaBandIndex,
      simpleRandomWalkLaw
          (xEastCandidateContextualFailure Cfull m r a j \
            prop45FailureEvent sourceCanonicalProfiles canonicalCStar
              m (xIndex east) r (alphaValue a)) ≤
        sourceBetaCandidateTail d m := by
  have hlow := prop47Lemma410Prop48ThetaFree_xEast_lowBands cWindow
    hCsmall hgap hd hcompare h
  have hCfull : 0 < Cfull := by linarith
  have hhigh := eventually_hlozCandidateCapFailureEvent_eq_empty_highBands
    hCfull
  filter_upwards [hlow, hhigh] with m hlowM hhighM
  intro r a ha j
  by_cases hj : sourceBeta (alphaValue a) j ≤ (7 : ℝ) / 10
  · exact hlowM r a ha j hj
  · have hempty := hhighM r a ha j (lt_of_not_ge hj)
    rw [xEastCandidateContextualFailure, hempty, empty_inter, empty_diff,
      measure_empty]
    exact bot_le

/-- The same deterministic high-band argument completes the source-banded
estimate on all 454 beta bands, without deleting a global theta event. -/
theorem prop47Lemma410Prop48SourceBanded_xEast
    (cWindow : ℕ) {Csmall Cfull d : ℝ}
    (hCsmall : 0 < Csmall) (hgap : Csmall + 20 ≤ Cfull)
    (hd : 0 < d)
    (hcompare : 32 * d ≤
      min (Real.log ((Csmall + 1) / Csmall) / 2)
        (imbalanceRate
          (Real.exp (sourceAdjacentComparisonExponent cWindow))) / 2)
    (h : Prop47Lemma410Prop48SourceBandedXEastLowBandInputs
      cWindow Csmall) :
    ∀ᶠ m : ℕ in atTop, ∀ r : StageIndex, ∀ a : AlphaIndex,
      alphaValue a ≤ kappaTwo → ∀ j : SourceBetaBandIndex,
      simpleRandomWalkLaw
          (xEastCandidateContextualFailure Cfull m r a j) ≤
        sourceBetaCandidateTail d m := by
  have hlow := prop47Lemma410Prop48SourceBanded_xEast_lowBands cWindow
    hCsmall hgap hd hcompare h
  have hCfull : 0 < Cfull := by linarith
  have hhigh := eventually_hlozCandidateCapFailureEvent_eq_empty_highBands
    hCfull
  filter_upwards [hlow, hhigh] with m hlowM hhighM
  intro r a ha j
  by_cases hj : sourceBeta (alphaValue a) j ≤ (7 : ℝ) / 10
  · exact hlowM r a ha j hj
  · have hempty := hhighM r a ha j (lt_of_not_ge hj)
    rw [xEastCandidateContextualFailure, hempty, empty_inter, measure_empty]
    exact bot_le

/-- Candidate tails on every beta band imply the full X-east Lemma-4.10
bound after the planar post-hit race estimate and the finite-band
absorption.  This isolates the common deterministic/probabilistic assembly
used by both fixed-profile and literal changed-path base inputs. -/
theorem prop47Lemma410ThetaFreeStretchedExponential_xEast_of_candidateTails
    {Cfull d : ℝ} (hCfull : 0 ≤ Cfull) (hd : 0 < d)
    (htail : ∀ᶠ m : ℕ in atTop, ∀ r : StageIndex,
      ∀ a : AlphaIndex, alphaValue a ≤ kappaTwo →
      ∀ j : SourceBetaBandIndex,
        simpleRandomWalkLaw
            (xEastCandidateContextualFailure Cfull m r a j \
              prop45FailureEvent sourceCanonicalProfiles canonicalCStar
                m (xIndex east) r (alphaValue a)) ≤
          sourceBetaCandidateTail d m) :
    ∀ᶠ m : ℕ in atTop, ∀ r : StageIndex, ∀ a : AlphaIndex,
      alphaValue a ≤ kappaTwo →
      simpleRandomWalkLaw
          (lemma410FailureEvent m (xIndex east) r (alphaValue a) \
            prop45FailureEvent sourceCanonicalProfiles canonicalCStar
              m (xIndex east) r (alphaValue a)) ≤
        ENNReal.ofReal (Real.exp
          (-sourceLemma410AbsorptionConstant d *
            Real.log ((m : ℝ) + 1) ^ 2)) := by
  have hsum := eventually_sourceBetaBand_sum_absorption hCfull hd
  filter_upwards [htail, eventually_sourceLemma410Radius_bounds, hsum,
      eventually_ge_atTop 2] with m htailM hRadius hsumM hm
  intro r a ha
  let alpha := alphaValue a
  let k := stageNumber r
  let window := sourceLemma410Window m alpha
  let theta := prop45FailureEvent sourceCanonicalProfiles canonicalCStar
    m (xIndex east) r alpha
  let P := xEastLemma410Context m r alpha \ theta
  have hk : 0 < k := by
    dsimp [k, stageNumber]
    omega
  have hcover : lemma410FailureEvent m (xIndex east) r alpha \ theta ⊆
      ⋃ j : SourceBetaBandIndex,
        hlozLemma410BPrimeEvent window m k
          (sourceBetaCandidateThreshold m alpha j)
          (sourceBetaRaceCount m alpha j) ∩ P := by
    intro omega homega
    have hraw := lemma410FailureEvent_subset_sourceBetaBand_cover
      m (xIndex east) r (alphaValue a) hm ha homega.1
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
          xEastCandidateContextualFailure Cfull m r a j \ theta := by
      ext omega
      simp only [P, xEastCandidateContextualFailure,
        xEastLemma410Context, window, k, alpha, Set.mem_inter_iff,
        Set.mem_diff]
      tauto
    rw [heq]
    exact hj
  exact (measure_le_sum_candidateCapTail_add_race_of_band_cover
    simpleRandomWalkLaw
    (lemma410FailureEvent m (xIndex east) r alpha \ theta) P
    (fun _ ↦ window) m k
    (sourceBetaCandidateThreshold m alpha)
    (sourceBetaRaceCount m alpha)
    (fun j ↦ sourceBetaCandidateCap Cfull m alpha j)
    (sourceBetaRaceBound m alpha)
    (fun _ ↦ sourceBetaCandidateTail d m)
    (by omega) hk hcover hrace hcap).trans (hsumM a ha)

/-- Literal changed-path candidate tails feed the common beta-band and
post-hit-race assembly. -/
theorem prop47Lemma410PathWitnessStretchedExponential_xEast
    (cWindow : ℕ) {witnessRate Csmall Cfull d : ℝ}
    (hwitnessRate : 0 < witnessRate)
    (hCsmall : 0 < Csmall) (hgap : Csmall + 20 ≤ Cfull)
    (hd : 0 < d)
    (hcompare : 16 * d ≤
      min (witnessRate / 8)
        (imbalanceRate
          (Real.exp (sourceAdjacentComparisonExponent cWindow))) / 2)
    (h : Prop47Lemma410Prop48CanonicalPathWitnessXEastLowBandInputs
      cWindow witnessRate Csmall) :
    ∀ᶠ m : ℕ in atTop, ∀ r : StageIndex, ∀ a : AlphaIndex,
      alphaValue a ≤ kappaTwo →
      simpleRandomWalkLaw
          (lemma410FailureEvent m (xIndex east) r (alphaValue a) \
            prop45FailureEvent sourceCanonicalProfiles canonicalCStar
              m (xIndex east) r (alphaValue a)) ≤
        ENNReal.ofReal (Real.exp
          (-sourceLemma410AbsorptionConstant d *
            Real.log ((m : ℝ) + 1) ^ 2)) := by
  apply prop47Lemma410ThetaFreeStretchedExponential_xEast_of_candidateTails
    (Cfull := Cfull) (d := d) (by linarith) hd
  exact prop47Lemma410Prop48PathWitness_xEast cWindow hwitnessRate
    hCsmall hgap hd hcompare h

/-- After removing the one Proposition-4.5 event, the checked candidate
tails and planar race estimate give the full stretched-log Lemma-4.10 bound
at X-east.  The theta event is kept out of the band union, hence it is not
multiplied by the number of beta bands. -/
theorem prop47Lemma410ThetaFreeStretchedExponential_xEast
    (cWindow : ℕ) {Csmall Cfull d : ℝ}
    (hCsmall : 0 < Csmall) (hgap : Csmall + 20 ≤ Cfull)
    (hd : 0 < d)
    (hcompare : 16 * d ≤
      min (Real.log ((Csmall + 1) / Csmall) / 2)
        (imbalanceRate
          (Real.exp (sourceAdjacentComparisonExponent cWindow))) / 2)
    (h : Prop47Lemma410Prop48ThetaFreeXEastLowBandInputs
      cWindow Csmall) :
    ∀ᶠ m : ℕ in atTop, ∀ r : StageIndex, ∀ a : AlphaIndex,
      alphaValue a ≤ kappaTwo →
      simpleRandomWalkLaw
          (lemma410FailureEvent m (xIndex east) r (alphaValue a) \
            prop45FailureEvent sourceCanonicalProfiles canonicalCStar
              m (xIndex east) r (alphaValue a)) ≤
        ENNReal.ofReal (Real.exp
          (-sourceLemma410AbsorptionConstant d *
            Real.log ((m : ℝ) + 1) ^ 2)) := by
  have htail := prop47Lemma410Prop48ThetaFree_xEast cWindow
    hCsmall hgap hd hcompare h
  have hCfull : 0 ≤ Cfull := by linarith
  have hsum := eventually_sourceBetaBand_sum_absorption hCfull hd
  filter_upwards [htail, eventually_sourceLemma410Radius_bounds, hsum,
      eventually_ge_atTop 2] with m htailM hRadius hsumM hm
  intro r a ha
  let alpha := alphaValue a
  let k := stageNumber r
  let window := sourceLemma410Window m alpha
  let theta := prop45FailureEvent sourceCanonicalProfiles canonicalCStar
    m (xIndex east) r alpha
  let P := xEastLemma410Context m r alpha \ theta
  have hk : 0 < k := by
    dsimp [k, stageNumber]
    omega
  have hcover : lemma410FailureEvent m (xIndex east) r alpha \ theta ⊆
      ⋃ j : SourceBetaBandIndex,
        hlozLemma410BPrimeEvent window m k
          (sourceBetaCandidateThreshold m alpha j)
          (sourceBetaRaceCount m alpha j) ∩ P := by
    intro omega homega
    have hraw := lemma410FailureEvent_subset_sourceBetaBand_cover
      m (xIndex east) r (alphaValue a) hm ha homega.1
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
          xEastCandidateContextualFailure Cfull m r a j \ theta := by
      ext omega
      simp only [P, xEastCandidateContextualFailure,
        xEastLemma410Context, window, k, alpha, Set.mem_inter_iff,
        Set.mem_diff]
      tauto
    rw [heq]
    exact hj
  exact (measure_le_sum_candidateCapTail_add_race_of_band_cover
    simpleRandomWalkLaw
    (lemma410FailureEvent m (xIndex east) r alpha \ theta) P
    (fun _ ↦ window) m k
    (sourceBetaCandidateThreshold m alpha)
    (sourceBetaRaceCount m alpha)
    (fun j ↦ sourceBetaCandidateCap Cfull m alpha j)
    (sourceBetaRaceBound m alpha)
    (fun _ ↦ sourceBetaCandidateTail d m)
    (by omega) hk hcover hrace hcap).trans (hsumM a ha)

/-- Candidate tails from the source-banded atomization combine with the
planar post-hit race estimate directly on the complete Lemma-4.10 event. -/
theorem prop47Lemma410SourceBandedStretchedExponential_xEast
    (cWindow : ℕ) {Csmall Cfull d : ℝ}
    (hCsmall : 0 < Csmall) (hgap : Csmall + 20 ≤ Cfull)
    (hd : 0 < d)
    (hcompare : 32 * d ≤
      min (Real.log ((Csmall + 1) / Csmall) / 2)
        (imbalanceRate
          (Real.exp (sourceAdjacentComparisonExponent cWindow))) / 2)
    (h : Prop47Lemma410Prop48SourceBandedXEastLowBandInputs
      cWindow Csmall) :
    ∀ᶠ m : ℕ in atTop, ∀ r : StageIndex, ∀ a : AlphaIndex,
      alphaValue a ≤ kappaTwo →
      simpleRandomWalkLaw
          (lemma410FailureEvent m (xIndex east) r (alphaValue a)) ≤
        ENNReal.ofReal (Real.exp
          (-sourceLemma410AbsorptionConstant d *
            Real.log ((m : ℝ) + 1) ^ 2)) := by
  have htail := prop47Lemma410Prop48SourceBanded_xEast cWindow
    hCsmall hgap hd hcompare h
  have hCfull : 0 ≤ Cfull := by linarith
  have hsum := eventually_sourceBetaBand_sum_absorption hCfull hd
  filter_upwards [htail, eventually_sourceLemma410Radius_bounds, hsum,
      eventually_ge_atTop 2] with m htailM hRadius hsumM hm
  intro r a ha
  let alpha := alphaValue a
  let k := stageNumber r
  let window := sourceLemma410Window m alpha
  let P := xEastLemma410Context m r alpha
  have hk : 0 < k := by
    dsimp [k, stageNumber]
    omega
  have hcover : lemma410FailureEvent m (xIndex east) r alpha ⊆
      ⋃ j : SourceBetaBandIndex,
        hlozLemma410BPrimeEvent window m k
          (sourceBetaCandidateThreshold m alpha j)
          (sourceBetaRaceCount m alpha j) ∩ P := by
    intro omega homega
    have hraw := lemma410FailureEvent_subset_sourceBetaBand_cover
      m (xIndex east) r (alphaValue a) hm ha homega
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
              (sourceBetaCandidateCap Cfull m alpha j) ∩ P) ≤
        sourceBetaCandidateTail d m := by
    have hj := htailM r a ha j
    have heq :
        hlozCandidateCapFailureEvent window m k
              (sourceBetaCandidateThreshold m alpha j)
              (sourceBetaCandidateCap Cfull m alpha j) ∩ P =
          xEastCandidateContextualFailure Cfull m r a j := by
      ext omega
      simp only [P, xEastCandidateContextualFailure,
        xEastLemma410Context, window, k, alpha, Set.mem_inter_iff]
    rw [heq]
    exact hj
  exact (measure_le_sum_candidateCapTail_add_race_of_band_cover
    simpleRandomWalkLaw
    (lemma410FailureEvent m (xIndex east) r alpha) P
    (fun _ ↦ window) m k
    (sourceBetaCandidateThreshold m alpha)
    (sourceBetaRaceCount m alpha)
    (fun j ↦ sourceBetaCandidateCap Cfull m alpha j)
    (sourceBetaRaceBound m alpha)
    (fun _ ↦ sourceBetaCandidateTail d m)
    (by omega) hk hcover hrace hcap).trans (hsumM a ha)

private theorem eventually_sourceLemma410Absorption_le_exceptional
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

/-- Proposition 4.5 pays the one removed theta event, yielding the named
exceptional scale at X-east with coefficient `prop45Coeff + 1`. -/
theorem prop47Lemma410Estimate_xEast_of_thetaFree_inputs
    (cWindow prop45Coeff : ℕ) {Csmall Cfull d : ℝ}
    (hCsmall : 0 < Csmall) (hgap : Csmall + 20 ≤ Cfull)
    (hd : 0 < d)
    (hcompare : 16 * d ≤
      min (Real.log ((Csmall + 1) / Csmall) / 2)
        (imbalanceRate
          (Real.exp (sourceAdjacentComparisonExponent cWindow))) / 2)
    (h : Prop47Lemma410Prop48ThetaFreeXEastLowBandInputs
      cWindow Csmall)
    (hProp45 : Prop47Prop45Estimate sourceCanonicalProfiles canonicalCStar
      prop45Coeff) :
    ∀ᶠ m : ℕ in atTop, ∀ r : StageIndex, ∀ a : AlphaIndex,
      alphaValue a ≤ kappaTwo →
      simpleRandomWalkLaw
          (lemma410FailureEvent m (xIndex east) r (alphaValue a)) ≤
        sourceExceptionalRateWithPrefactor m (prop45Coeff + 1) kappa := by
  have hdiff := prop47Lemma410ThetaFreeStretchedExponential_xEast cWindow
    hCsmall hgap hd hcompare h
  have herror := eventually_sourceLemma410Absorption_le_exceptional hd
  filter_upwards [hdiff, hProp45, herror] with m hdiffM hthetaM herrorM
  intro r a ha
  let E := lemma410FailureEvent m (xIndex east) r (alphaValue a)
  let theta := prop45FailureEvent sourceCanonicalProfiles canonicalCStar
    m (xIndex east) r (alphaValue a)
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
      add_le_add (hthetaM (xIndex east) r a ha)
        ((hdiffM r a ha).trans herrorM)
    _ = sourceExceptionalRateWithPrefactor m (prop45Coeff + 1) kappa := by
      simp only [sourceExceptionalRateWithPrefactor]
      push_cast
      ring

/-- Proposition 4.5 pays the single path-space theta event after the literal
changed-path Proposition-4.8 estimate. -/
theorem prop47Lemma410Estimate_xEast_of_pathWitness_inputs
    (cWindow prop45Coeff : ℕ)
    {witnessRate Csmall Cfull d : ℝ}
    (hwitnessRate : 0 < witnessRate)
    (hCsmall : 0 < Csmall) (hgap : Csmall + 20 ≤ Cfull)
    (hd : 0 < d)
    (hcompare : 16 * d ≤
      min (witnessRate / 8)
        (imbalanceRate
          (Real.exp (sourceAdjacentComparisonExponent cWindow))) / 2)
    (h : Prop47Lemma410Prop48CanonicalPathWitnessXEastLowBandInputs
      cWindow witnessRate Csmall)
    (hProp45 : Prop47Prop45Estimate sourceCanonicalProfiles canonicalCStar
      prop45Coeff) :
    ∀ᶠ m : ℕ in atTop, ∀ r : StageIndex, ∀ a : AlphaIndex,
      alphaValue a ≤ kappaTwo →
      simpleRandomWalkLaw
          (lemma410FailureEvent m (xIndex east) r (alphaValue a)) ≤
        sourceExceptionalRateWithPrefactor m (prop45Coeff + 1) kappa := by
  have hdiff := prop47Lemma410PathWitnessStretchedExponential_xEast
    cWindow hwitnessRate hCsmall hgap hd hcompare h
  have herror := eventually_sourceLemma410Absorption_le_exceptional hd
  filter_upwards [hdiff, hProp45, herror] with m hdiffM hthetaM herrorM
  intro r a ha
  let E := lemma410FailureEvent m (xIndex east) r (alphaValue a)
  let theta := prop45FailureEvent sourceCanonicalProfiles canonicalCStar
    m (xIndex east) r (alphaValue a)
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
      add_le_add (hthetaM (xIndex east) r a ha)
        ((hdiffM r a ha).trans herrorM)
    _ = sourceExceptionalRateWithPrefactor m (prop45Coeff + 1) kappa := by
      simp only [sourceExceptionalRateWithPrefactor]
      push_cast
      ring

/-- The source-banded package already pays every recursive theta exception,
so no separate global Proposition-4.5 event or coefficient is added here. -/
theorem prop47Lemma410Estimate_xEast_of_source_banded_inputs
    (cWindow : ℕ) {Csmall Cfull d : ℝ}
    (hCsmall : 0 < Csmall) (hgap : Csmall + 20 ≤ Cfull)
    (hd : 0 < d)
    (hcompare : 32 * d ≤
      min (Real.log ((Csmall + 1) / Csmall) / 2)
        (imbalanceRate
          (Real.exp (sourceAdjacentComparisonExponent cWindow))) / 2)
    (h : Prop47Lemma410Prop48SourceBandedXEastLowBandInputs
      cWindow Csmall) :
    ∀ᶠ m : ℕ in atTop, ∀ r : StageIndex, ∀ a : AlphaIndex,
      alphaValue a ≤ kappaTwo →
      simpleRandomWalkLaw
          (lemma410FailureEvent m (xIndex east) r (alphaValue a)) ≤
        sourceExceptionalRateWithPrefactor m 1 kappa := by
  have hraw := prop47Lemma410SourceBandedStretchedExponential_xEast cWindow
    hCsmall hgap hd hcompare h
  have herror := eventually_sourceLemma410Absorption_le_exceptional hd
  filter_upwards [hraw, herror] with m hrawM herrorM
  intro r a ha
  exact (hrawM r a ha).trans herrorM

theorem siteSquaredDistance_orientSite
    (d : Dir) (x y : Site) :
    siteSquaredDistance (orientSite d x) (orientSite d y) =
      siteSquaredDistance x y := by
  rcases x with ⟨x₁, x₂⟩
  rcases y with ⟨y₁, y₂⟩
  have hswap₁ : (y₁ + -x₁).natAbs = (x₁ - y₁).natAbs := by
    rw [show y₁ + -x₁ = -(x₁ - y₁) by ring, Int.natAbs_neg]
  have hswap₂ : (y₂ + -x₂).natAbs = (x₂ - y₂).natAbs := by
    rw [show y₂ + -x₂ = -(x₂ - y₂) by ring, Int.natAbs_neg]
  fin_cases d <;>
    simp [siteSquaredDistance, orientSite, hswap₁, hswap₂, add_comm]

theorem siteDistance_orientSite
    (d : Dir) (x y : Site) :
    siteDistance (orientSite d x) (orientSite d y) = siteDistance x y := by
  unfold siteDistance
  rw [siteSquaredDistance_orientSite]

theorem hlozDirectAvoidanceEvent_x_orient_iff
    (d : Dir) (s : Path) (m j : ℕ) :
    s ∈ hlozDirectAvoidanceEvent m j ↔
      orientPath d s ∈ hlozDirectAvoidanceEvent m j := by
  simp only [hlozDirectAvoidanceEvent, Set.mem_setOf_eq,
    firstKSitesReachLevel_orientPath, levelCreationSite_orientPath,
    orientPath]
  constructor
  · intro h n hn hn' i hi hi' hEq
    exact h n hn hn' i hi hi' (orientSite_injective d hEq)
  · intro h n hn hn' i hi hi' hEq
    exact h n hn hn' i hi hi' (congrArg (orientSite d) hEq)

theorem distanceBinEvent_x_orient_iff
    (d : Dir) (s : Path) (m k : ℕ) (alpha : ℝ) :
    s ∈ distanceBinEvent m k alpha ↔
      orientPath d s ∈ distanceBinEvent m k alpha := by
  simp only [distanceBinEvent, Set.mem_setOf_eq,
    firstKSitesReachLevel_orientPath, levelCreationSite_orientPath,
    siteDistance_orientSite]

theorem nextCreationIsCandidateEvent_x_orient_iff
    (d : Dir) (s : Path) (m k : ℕ) (beta : ℝ) :
    s ∈ nextCreationIsCandidateEvent (xIndex east) m k beta ↔
      orientPath d s ∈ nextCreationIsCandidateEvent (xIndex d) m k beta := by
  simp only [nextCreationIsCandidateEvent, Set.mem_setOf_eq,
    levelCreationSite_orientPath, nearFavoriteSites_x_orient,
    Finset.mem_image]
  constructor
  · intro h
    exact ⟨levelCreationSite s m (k + 1), h, rfl⟩
  · rintro ⟨x, hx, hEq⟩
    exact (orientSite_injective d hEq).symm ▸ hx

theorem lemma410FailureEvent_x_orient_iff
    (d : Dir) (s : Path) (m : ℕ) (r : StageIndex) (alpha : ℝ) :
    s ∈ lemma410FailureEvent m (xIndex east) r alpha ↔
      orientPath d s ∈ lemma410FailureEvent m (xIndex d) r alpha := by
  simp only [lemma410FailureEvent, Set.mem_inter_iff, Set.mem_compl_iff]
  rw [prefixPairingEvent_x_orient_iff,
    hlozDirectAvoidanceEvent_x_orient_iff,
    distanceBinEvent_x_orient_iff,
    nextCreationIsCandidateEvent_x_orient_iff]

theorem simpleRandomWalkLaw_lemma410FailureEvent_x_eq
    (d : Dir) (m : ℕ) (r : StageIndex) (alpha : ℝ) :
    simpleRandomWalkLaw (lemma410FailureEvent m (xIndex d) r alpha) =
      simpleRandomWalkLaw (lemma410FailureEvent m (xIndex east) r alpha) := by
  let E := lemma410FailureEvent m (xIndex d) r alpha
  have hE : MeasurableSet E :=
    (((measurableSet_prefixPairingEvent m (xIndex d) (stageNumber r + 1)).inter
      (measurableSet_hlozDirectAvoidanceEvent m (stageNumber r + 1))).inter
      (measurableSet_distanceBinEvent m (stageNumber r) alpha)).inter
      (measurableSet_nextCreationIsCandidateEvent
        (xIndex d) m (stageNumber r) (alpha + delta)).compl
  calc
    simpleRandomWalkLaw E = (simpleRandomWalkLaw.map (orientPath d)) E := by
      rw [simpleRandomWalkLaw_map_orientPath]
    _ = simpleRandomWalkLaw ((orientPath d) ⁻¹' E) := by
      rw [Measure.map_apply (measurable_orientPath d) hE]
    _ = simpleRandomWalkLaw
        (lemma410FailureEvent m (xIndex east) r alpha) := by
      congr 1
      ext s
      exact (lemma410FailureEvent_x_orient_iff d s m r alpha).symm

/-- The theta-free X-east source package and the already-global
Proposition-4.5 estimate therefore supply all four checkerboard pairings. -/
def Prop47Lemma410EstimateXDirections (coeff : ℕ) : Prop :=
  ∀ᶠ m : ℕ in atTop, ∀ d : Dir, ∀ r : StageIndex, ∀ a : AlphaIndex,
    alphaValue a ≤ kappaTwo →
    simpleRandomWalkLaw
        (lemma410FailureEvent m (xIndex d) r (alphaValue a)) ≤
      sourceExceptionalRateWithPrefactor m coeff kappa

theorem prop47Lemma410EstimateXDirections_of_thetaFree_inputs
    (cWindow prop45Coeff : ℕ) {Csmall Cfull d : ℝ}
    (hCsmall : 0 < Csmall) (hgap : Csmall + 20 ≤ Cfull)
    (hd : 0 < d)
    (hcompare : 16 * d ≤
      min (Real.log ((Csmall + 1) / Csmall) / 2)
        (imbalanceRate
          (Real.exp (sourceAdjacentComparisonExponent cWindow))) / 2)
    (h : Prop47Lemma410Prop48ThetaFreeXEastLowBandInputs
      cWindow Csmall)
    (hProp45 : Prop47Prop45Estimate sourceCanonicalProfiles canonicalCStar
      prop45Coeff) :
    Prop47Lemma410EstimateXDirections (prop45Coeff + 1) := by
  have heast := prop47Lemma410Estimate_xEast_of_thetaFree_inputs
    cWindow prop45Coeff hCsmall hgap hd hcompare h hProp45
  filter_upwards [heast] with m hm
  intro d₀ r a ha
  rw [simpleRandomWalkLaw_lemma410FailureEvent_x_eq]
  exact hm r a ha

/-- Canonical-parity source form of the four-X Lemma-4.10 estimate. -/
theorem prop47Lemma410EstimateXDirections_of_canonicalThetaFree_inputs
    (cWindow prop45Coeff : ℕ) {Csmall Cfull d : ℝ}
    (hCsmall : 0 < Csmall) (hgap : Csmall + 20 ≤ Cfull)
    (hd : 0 < d)
    (hcompare : 16 * d ≤
      min (Real.log ((Csmall + 1) / Csmall) / 2)
        (imbalanceRate
          (Real.exp (sourceAdjacentComparisonExponent cWindow))) / 2)
    (h : Prop47Lemma410Prop48CanonicalThetaFreeXEastLowBandInputs
      cWindow Csmall)
    (hProp45 : Prop47Prop45Estimate sourceCanonicalProfiles canonicalCStar
      prop45Coeff) :
    Prop47Lemma410EstimateXDirections (prop45Coeff + 1) :=
  prop47Lemma410EstimateXDirections_of_thetaFree_inputs
    cWindow prop45Coeff hCsmall hgap hd hcompare
      (prop47Lemma410Prop48ThetaFreeXEastLowBandInputs_of_canonical h)
      hProp45

/-- Quarter-turn transport of the literal changed-path source form. -/
theorem prop47Lemma410EstimateXDirections_of_pathWitness_inputs
    (cWindow prop45Coeff : ℕ)
    {witnessRate Csmall Cfull d : ℝ}
    (hwitnessRate : 0 < witnessRate)
    (hCsmall : 0 < Csmall) (hgap : Csmall + 20 ≤ Cfull)
    (hd : 0 < d)
    (hcompare : 16 * d ≤
      min (witnessRate / 8)
        (imbalanceRate
          (Real.exp (sourceAdjacentComparisonExponent cWindow))) / 2)
    (h : Prop47Lemma410Prop48CanonicalPathWitnessXEastLowBandInputs
      cWindow witnessRate Csmall)
    (hProp45 : Prop47Prop45Estimate sourceCanonicalProfiles canonicalCStar
      prop45Coeff) :
    Prop47Lemma410EstimateXDirections (prop45Coeff + 1) := by
  have heast := prop47Lemma410Estimate_xEast_of_pathWitness_inputs
    cWindow prop45Coeff hwitnessRate hCsmall hgap hd hcompare h hProp45
  filter_upwards [heast] with m hm
  intro d₀ r a ha
  rw [simpleRandomWalkLaw_lemma410FailureEvent_x_eq]
  exact hm r a ha

/-- Quarter-turn transport of the source-banded X-east estimate. -/
theorem prop47Lemma410EstimateXDirections_of_source_banded_inputs
    (cWindow : ℕ) {Csmall Cfull d : ℝ}
    (hCsmall : 0 < Csmall) (hgap : Csmall + 20 ≤ Cfull)
    (hd : 0 < d)
    (hcompare : 32 * d ≤
      min (Real.log ((Csmall + 1) / Csmall) / 2)
        (imbalanceRate
          (Real.exp (sourceAdjacentComparisonExponent cWindow))) / 2)
    (h : Prop47Lemma410Prop48SourceBandedXEastLowBandInputs
      cWindow Csmall) :
    Prop47Lemma410EstimateXDirections 1 := by
  have heast := prop47Lemma410Estimate_xEast_of_source_banded_inputs
    cWindow hCsmall hgap hd hcompare h
  filter_upwards [heast] with m hm
  intro d₀ r a ha
  rw [simpleRandomWalkLaw_lemma410FailureEvent_x_eq]
  exact hm r a ha

/-- The coarse box in the definition of `hlozLatticeBallSq` does not alter
its intended exact squared-distance membership condition. -/
theorem mem_hlozLatticeBallSq_iff
    (D : ℕ) (c x : Site) :
    x ∈ hlozLatticeBallSq D c ↔ siteSquaredDistance x c ≤ D := by
  classical
  constructor
  · intro hx
    exact (Finset.mem_filter.mp hx).2
  · intro hdist
    apply Finset.mem_filter.mpr
    refine ⟨?_, hdist⟩
    have h₁sq : (x.1 - c.1).natAbs ^ 2 ≤ D := by
      unfold siteSquaredDistance at hdist
      omega
    have h₂sq : (x.2 - c.2).natAbs ^ 2 ≤ D := by
      unfold siteSquaredDistance at hdist
      omega
    have hself (n : ℕ) : n ≤ n ^ 2 := by
      cases n <;> nlinarith
    have h₁ : (x.1 - c.1).natAbs ≤ D := (hself _).trans h₁sq
    have h₂ : (x.2 - c.2).natAbs ≤ D := (hself _).trans h₂sq
    have h₁abs : |x.1 - c.1| ≤ (D : ℤ) := by
      rw [← Int.natCast_natAbs]
      exact_mod_cast h₁
    have h₂abs : |x.2 - c.2| ≤ (D : ℤ) := by
      rw [← Int.natCast_natAbs]
      exact_mod_cast h₂
    rcases abs_le.mp h₁abs with ⟨h₁lo, h₁hi⟩
    rcases abs_le.mp h₂abs with ⟨h₂lo, h₂hi⟩
    apply Finset.mem_product.mpr
    constructor <;> apply Finset.mem_Icc.mpr <;> omega

theorem sourceLemma410Window_orientSite
    (d : Dir) (m : ℕ) (alpha : ℝ) (c : Site) :
    sourceLemma410Window m alpha (orientSite d c) =
      (sourceLemma410Window m alpha c).image (orientSite d) := by
  classical
  ext y
  obtain ⟨x, rfl⟩ := orientSite_surjective d y
  rw [Finset.mem_image]
  constructor
  · intro hy
    refine ⟨x, ?_, rfl⟩
    rw [sourceLemma410Window, mem_hlozLatticeBallSq_iff] at hy ⊢
    simpa only [siteSquaredDistance_orientSite] using hy
  · rintro ⟨z, hz, hzx⟩
    have hzx' : z = x := orientSite_injective d hzx
    subst z
    rw [sourceLemma410Window, mem_hlozLatticeBallSq_iff] at hz ⊢
    simpa only [siteSquaredDistance_orientSite] using hz

theorem hlozCandidateSitesAtTime_sourceWindow_orientPath
    (d : Dir) (m : ℕ) (alpha : ℝ) (s : Path) (t q : ℕ) :
    hlozCandidateSitesAtTime (sourceLemma410Window m alpha)
        (orientPath d s) t q =
      (hlozCandidateSitesAtTime (sourceLemma410Window m alpha)
        s t q).image (orientSite d) := by
  classical
  ext y
  obtain ⟨x, rfl⟩ := orientSite_surjective d y
  simp only [hlozCandidateSitesAtTime, Finset.mem_filter,
    orientPath, sourceLemma410Window_orientSite, Finset.mem_image,
    localTime_orientPath]
  constructor
  · rintro ⟨hwindow, hlocal⟩
    rcases hwindow with ⟨z, hz, hzx⟩
    have hzx' : z = x := orientSite_injective d hzx
    subst z
    exact ⟨x, ⟨hz, hlocal⟩, rfl⟩
  · rintro ⟨z, ⟨hz, hlocal⟩, hzx⟩
    have hzx' : z = x := orientSite_injective d hzx
    subst z
    exact ⟨⟨x, hz, rfl⟩, hlocal⟩

theorem card_hlozCandidateSitesAtTime_sourceWindow_orientPath
    (d : Dir) (m : ℕ) (alpha : ℝ) (s : Path) (t q : ℕ) :
    (hlozCandidateSitesAtTime (sourceLemma410Window m alpha)
        (orientPath d s) t q).card =
      (hlozCandidateSitesAtTime (sourceLemma410Window m alpha)
        s t q).card := by
  rw [hlozCandidateSitesAtTime_sourceWindow_orientPath]
  exact Finset.card_image_of_injective _ (orientSite_injective d)

/-- The full source candidate-cap event, together with the matching pairing
history, is carried from `X₁` to `X_d` by the proved quarter turn. -/
theorem candidateCapFailure_inter_prefix_x_orient_iff
    (d : Dir) (s : Path) (m k q cap : ℕ) (alpha : ℝ) :
    s ∈ hlozCandidateCapFailureEvent (sourceLemma410Window m alpha)
          m k q cap ∩ prefixPairingEvent m (xIndex east) (k + 1) ↔
      orientPath d s ∈
        hlozCandidateCapFailureEvent (sourceLemma410Window m alpha)
            m k q cap ∩ prefixPairingEvent m (xIndex d) (k + 1) := by
  constructor
  · rintro ⟨hcap, hprefix⟩
    constructor
    · unfold hlozCandidateCapFailureEvent at hcap ⊢
      simp only [Set.mem_setOf_eq]
      rw [firstKSitesReachLevel_orientPath]
      rw [card_hlozCandidateSitesAtTime_sourceWindow_orientPath]
      exact hcap
    · exact (prefixPairingEvent_x_orient_iff d s m (k + 1)).mp hprefix
  · rintro ⟨hcap, hprefix⟩
    constructor
    · unfold hlozCandidateCapFailureEvent at hcap ⊢
      simp only [Set.mem_setOf_eq] at hcap ⊢
      rw [firstKSitesReachLevel_orientPath,
        card_hlozCandidateSitesAtTime_sourceWindow_orientPath] at hcap
      exact hcap
    · exact (prefixPairingEvent_x_orient_iff d s m (k + 1)).mpr hprefix

theorem simpleRandomWalkLaw_candidateCapFailure_inter_prefix_x_eq
    (d : Dir) (m k q cap : ℕ) (alpha : ℝ) :
    simpleRandomWalkLaw
        (hlozCandidateCapFailureEvent (sourceLemma410Window m alpha)
            m k q cap ∩ prefixPairingEvent m (xIndex d) (k + 1)) =
      simpleRandomWalkLaw
        (hlozCandidateCapFailureEvent (sourceLemma410Window m alpha)
            m k q cap ∩ prefixPairingEvent m (xIndex east) (k + 1)) := by
  let E := hlozCandidateCapFailureEvent (sourceLemma410Window m alpha)
      m k q cap ∩ prefixPairingEvent m (xIndex d) (k + 1)
  have hE : MeasurableSet E :=
    (measurableSet_hlozCandidateCapFailureEvent _ _ _ _ _).inter
      (measurableSet_prefixPairingEvent _ _ _)
  calc
    simpleRandomWalkLaw E =
        (simpleRandomWalkLaw.map (orientPath d)) E := by
      rw [simpleRandomWalkLaw_map_orientPath]
    _ = simpleRandomWalkLaw ((orientPath d) ⁻¹' E) := by
      rw [Measure.map_apply (measurable_orientPath d) hE]
    _ = simpleRandomWalkLaw
        (hlozCandidateCapFailureEvent (sourceLemma410Window m alpha)
            m k q cap ∩ prefixPairingEvent m (xIndex east) (k + 1)) := by
      congr 1
      ext s
      exact (candidateCapFailure_inter_prefix_x_orient_iff
        d s m k q cap alpha).symm

/-! ## Reuniting the winner halves at X-east -/

/-- On the Proposition-4.8 band range, the four stopped terminal-parity
laws control the complete `X₁` candidate failure.  The hypotheses display
both deterministic constant losses: `Csmall + 20 ≤ Cfull` for the source
candidate split, and `16*d ≤ rate` for the two successive binary unions
(terminal parity, then left/right winner). -/
theorem prop47Lemma410Prop48StoppedCandidateTail_xEast_lowBands
    (cWindow : ℕ) {Csmall Cfull cBase cTheta thetaPower d : ℝ}
    (hsmall : 0 ≤ Csmall) (hgap : Csmall + 20 ≤ Cfull)
    (hcBase : 0 < cBase) (hcTheta : 0 < cTheta)
    (hthetaPower : 0 < thetaPower) (hd : 0 < d)
    (hcompare : 16 * d ≤
      min cBase
        (imbalanceRate
          (Real.exp (sourceAdjacentComparisonExponent cWindow))) / 2)
    (hLeft : Prop47Lemma410Prop48LeftParityLowBandInputs
      cWindow Csmall cBase cTheta thetaPower)
    (hRight : Prop47Lemma410Prop48RightParityLowBandInputs
      cWindow Csmall cBase cTheta thetaPower) :
    ∀ᶠ m : ℕ in atTop, ∀ r : StageIndex, ∀ a : AlphaIndex,
      alphaValue a ≤ kappaTwo → ∀ j : SourceBetaBandIndex,
      sourceBeta (alphaValue a) j ≤ (7 : ℝ) / 10 →
      simpleRandomWalkLaw
          (hlozCandidateCapFailureEvent
              (sourceLemma410Window m (alphaValue a)) m (stageNumber r)
              (sourceBetaCandidateThreshold m (alphaValue a) j)
              (sourceBetaCandidateCap Cfull m (alphaValue a) j) ∩
            prefixPairingEvent m (xIndex east) (stageNumber r + 1)) ≤
        sourceBetaCandidateTail d m := by
  have htwoD : 0 < 2 * d := by positivity
  have hcompareTwo : 8 * (2 * d) ≤
      min cBase
        (imbalanceRate
          (Real.exp (sourceAdjacentComparisonExponent cWindow))) / 2 := by
    nlinarith [hcompare]
  have hleftTail :=
    prop47Lemma410Prop48StoppedCandidateTail_leftWinner_lowBands
      cWindow hcBase hcTheta hthetaPower htwoD hcompareTwo hLeft
  have hrightTail :=
    prop47Lemma410Prop48StoppedCandidateTail_rightWinner_lowBands
      cWindow hcBase hcTheta hthetaPower htwoD hcompareTwo hRight
  have hcover :=
    eventually_fullCandidateFailure_subset_smallWinnerFailures_xEast
      hsmall hgap
  have habsorb := eventually_two_mul_sourceBetaCandidateTail_two_mul_le hd
  filter_upwards [hleftTail, hrightTail, hcover, habsorb] with
      m hleftM hrightM hcoverM habsorbM
  intro r a ha j hj
  have hleft := hleftM r a ha j hj
  have hright := hrightM r a ha j hj
  have heast : xIndex east = (0 : Fin 6) := by
    apply Fin.ext
    rfl
  rw [heast]
  calc
    simpleRandomWalkLaw _ ≤ simpleRandomWalkLaw
        ((hlozLeftWinnerCandidateCapFailureEvent
              (sourceLemma410Window m (alphaValue a)) m (stageNumber r)
              (sourceBetaCandidateThreshold m (alphaValue a) j)
              (sourceLeftWinnerCandidateCap Csmall m (alphaValue a) j) ∩
            prefixPairingEvent m (0 : Fin 6) (stageNumber r + 1)) ∪
          (hlozRightWinnerCandidateCapFailureEvent
              (sourceLemma410Window m (alphaValue a)) m (stageNumber r)
              (sourceBetaCandidateThreshold m (alphaValue a) j)
              (sourceRightWinnerCandidateCap Csmall m (alphaValue a) j) ∩
            prefixPairingEvent m (0 : Fin 6) (stageNumber r + 1))) := by
      apply measure_mono
      exact hcoverM r a ha j
    _ ≤ simpleRandomWalkLaw
          (hlozLeftWinnerCandidateCapFailureEvent
              (sourceLemma410Window m (alphaValue a)) m (stageNumber r)
              (sourceBetaCandidateThreshold m (alphaValue a) j)
              (sourceLeftWinnerCandidateCap Csmall m (alphaValue a) j) ∩
            prefixPairingEvent m (0 : Fin 6) (stageNumber r + 1)) +
        simpleRandomWalkLaw
          (hlozRightWinnerCandidateCapFailureEvent
              (sourceLemma410Window m (alphaValue a)) m (stageNumber r)
              (sourceBetaCandidateThreshold m (alphaValue a) j)
              (sourceRightWinnerCandidateCap Csmall m (alphaValue a) j) ∩
            prefixPairingEvent m (0 : Fin 6) (stageNumber r + 1)) :=
      measure_union_le _ _
    _ ≤ sourceBetaCandidateTail (2 * d) m +
        sourceBetaCandidateTail (2 * d) m := add_le_add hleft hright
    _ = (2 : ℝ≥0∞) * sourceBetaCandidateTail (2 * d) m := by ring
    _ ≤ sourceBetaCandidateTail d m := habsorbM

/-- Quarter-turn transport gives the same low-band candidate tail for all
four checkerboard domino tilings. -/
theorem prop47Lemma410Prop48StoppedCandidateTail_xDirections_lowBands
    (cWindow : ℕ) {Csmall Cfull cBase cTheta thetaPower d : ℝ}
    (hsmall : 0 ≤ Csmall) (hgap : Csmall + 20 ≤ Cfull)
    (hcBase : 0 < cBase) (hcTheta : 0 < cTheta)
    (hthetaPower : 0 < thetaPower) (hd : 0 < d)
    (hcompare : 16 * d ≤
      min cBase
        (imbalanceRate
          (Real.exp (sourceAdjacentComparisonExponent cWindow))) / 2)
    (hLeft : Prop47Lemma410Prop48LeftParityLowBandInputs
      cWindow Csmall cBase cTheta thetaPower)
    (hRight : Prop47Lemma410Prop48RightParityLowBandInputs
      cWindow Csmall cBase cTheta thetaPower) :
    ∀ᶠ m : ℕ in atTop, ∀ d₀ : Dir, ∀ r : StageIndex,
      ∀ a : AlphaIndex, alphaValue a ≤ kappaTwo →
      ∀ j : SourceBetaBandIndex,
      sourceBeta (alphaValue a) j ≤ (7 : ℝ) / 10 →
      simpleRandomWalkLaw
          (hlozCandidateCapFailureEvent
              (sourceLemma410Window m (alphaValue a)) m (stageNumber r)
              (sourceBetaCandidateThreshold m (alphaValue a) j)
              (sourceBetaCandidateCap Cfull m (alphaValue a) j) ∩
            prefixPairingEvent m (xIndex d₀) (stageNumber r + 1)) ≤
        sourceBetaCandidateTail d m := by
  have hEast := prop47Lemma410Prop48StoppedCandidateTail_xEast_lowBands
    cWindow hsmall hgap hcBase hcTheta hthetaPower hd hcompare hLeft hRight
  filter_upwards [hEast] with m hm
  intro d₀ r a ha j hj
  rw [simpleRandomWalkLaw_candidateCapFailure_inter_prefix_x_eq]
  exact hm r a ha j hj

/-! ## Adding the deterministic high bands -/

/-- Proposition 4.8 is used only through `β ≤ 7/10`.  Above that cutoff
the spatial candidate cap is deterministically impossible, so the four-X
result holds uniformly over all 454 source bands. -/
theorem prop47Lemma410Prop48StoppedCandidateTail_xDirections
    (cWindow : ℕ) {Csmall Cfull cBase cTheta thetaPower d : ℝ}
    (hsmall : 0 ≤ Csmall) (hgap : Csmall + 20 ≤ Cfull)
    (hcBase : 0 < cBase) (hcTheta : 0 < cTheta)
    (hthetaPower : 0 < thetaPower) (hd : 0 < d)
    (hcompare : 16 * d ≤
      min cBase
        (imbalanceRate
          (Real.exp (sourceAdjacentComparisonExponent cWindow))) / 2)
    (hLeft : Prop47Lemma410Prop48LeftParityLowBandInputs
      cWindow Csmall cBase cTheta thetaPower)
    (hRight : Prop47Lemma410Prop48RightParityLowBandInputs
      cWindow Csmall cBase cTheta thetaPower) :
    ∀ᶠ m : ℕ in atTop, ∀ d₀ : Dir, ∀ r : StageIndex,
      ∀ a : AlphaIndex, alphaValue a ≤ kappaTwo →
      ∀ j : SourceBetaBandIndex,
      simpleRandomWalkLaw
          (hlozCandidateCapFailureEvent
              (sourceLemma410Window m (alphaValue a)) m (stageNumber r)
              (sourceBetaCandidateThreshold m (alphaValue a) j)
              (sourceBetaCandidateCap Cfull m (alphaValue a) j) ∩
            prefixPairingEvent m (xIndex d₀) (stageNumber r + 1)) ≤
        sourceBetaCandidateTail d m := by
  have hlow := prop47Lemma410Prop48StoppedCandidateTail_xDirections_lowBands
    cWindow hsmall hgap hcBase hcTheta hthetaPower hd hcompare hLeft hRight
  have hCfull : 0 < Cfull := by linarith
  have hhigh := eventually_hlozCandidateCapFailureEvent_eq_empty_highBands
    hCfull
  filter_upwards [hlow, hhigh] with m hlowM hhighM
  intro d₀ r a ha j
  by_cases hj : sourceBeta (alphaValue a) j ≤ (7 : ℝ) / 10
  · exact hlowM d₀ r a ha j hj
  · have hempty := hhighM r a ha j (lt_of_not_ge hj)
    rw [hempty, empty_inter, measure_empty]
    exact bot_le

/-! ## Exact all-six residual interface -/

/-- The portion of `Prop47Lemma410Prop48StoppedCandidateTail` proved in
this file: precisely the four checkerboard pairings `i=0,1,2,3`. -/
def Prop47Lemma410Prop48StoppedCandidateTailXDirections
    (C d : ℝ) : Prop :=
  ∀ᶠ m : ℕ in atTop, ∀ d₀ : Dir, ∀ r : StageIndex,
    ∀ a : AlphaIndex, alphaValue a ≤ kappaTwo →
    ∀ j : SourceBetaBandIndex,
    simpleRandomWalkLaw
        (hlozCandidateCapFailureEvent
            (sourceLemma410Window m (alphaValue a)) m (stageNumber r)
            (sourceBetaCandidateThreshold m (alphaValue a) j)
            (sourceBetaCandidateCap C m (alphaValue a) j) ∩
          prefixPairingEvent m (xIndex d₀) (stageNumber r + 1)) ≤
      sourceBetaCandidateTail d m

/-- The honest remaining source input after the quarter-turn argument: the
two column pairings `i=4,5`.  No column law or event identity is hidden in
this predicate. -/
def Prop47Lemma410Prop48StoppedCandidateTailYColumns
    (C d : ℝ) : Prop :=
  ∀ᶠ m : ℕ in atTop, ∀ i : Fin 6, 4 ≤ i.1 →
    ∀ r : StageIndex, ∀ a : AlphaIndex,
    alphaValue a ≤ kappaTwo → ∀ j : SourceBetaBandIndex,
    simpleRandomWalkLaw
        (hlozCandidateCapFailureEvent
            (sourceLemma410Window m (alphaValue a)) m (stageNumber r)
            (sourceBetaCandidateThreshold m (alphaValue a) j)
            (sourceBetaCandidateCap C m (alphaValue a) j) ∩
          prefixPairingEvent m i (stageNumber r + 1)) ≤
      sourceBetaCandidateTail d m

theorem prop47Lemma410Prop48StoppedCandidateTailXDirections_of_inputs
    (cWindow : ℕ) {Csmall Cfull cBase cTheta thetaPower d : ℝ}
    (hsmall : 0 ≤ Csmall) (hgap : Csmall + 20 ≤ Cfull)
    (hcBase : 0 < cBase) (hcTheta : 0 < cTheta)
    (hthetaPower : 0 < thetaPower) (hd : 0 < d)
    (hcompare : 16 * d ≤
      min cBase
        (imbalanceRate
          (Real.exp (sourceAdjacentComparisonExponent cWindow))) / 2)
    (hLeft : Prop47Lemma410Prop48LeftParityLowBandInputs
      cWindow Csmall cBase cTheta thetaPower)
    (hRight : Prop47Lemma410Prop48RightParityLowBandInputs
      cWindow Csmall cBase cTheta thetaPower) :
    Prop47Lemma410Prop48StoppedCandidateTailXDirections Cfull d :=
  prop47Lemma410Prop48StoppedCandidateTail_xDirections cWindow
    hsmall hgap hcBase hcTheta hthetaPower hd hcompare hLeft hRight

/-- Four-X control plus the explicitly separate two-column input is exactly
the existing all-six stopped-candidate predicate. -/
theorem prop47Lemma410Prop48StoppedCandidateTail_of_xDirections_of_yColumns
    {C d : ℝ}
    (hX : Prop47Lemma410Prop48StoppedCandidateTailXDirections C d)
    (hY : Prop47Lemma410Prop48StoppedCandidateTailYColumns C d) :
    Prop47Lemma410Prop48StoppedCandidateTail C d := by
  filter_upwards [hX, hY] with m hXm hYm
  intro i r a ha j
  by_cases hi : i.1 < 4
  · let d₀ : Dir := ⟨i.1, hi⟩
    have hindex : xIndex d₀ = i := by
      apply Fin.ext
      rfl
    rw [← hindex]
    exact hXm d₀ r a ha j
  · exact hYm i (Nat.le_of_not_gt hi) r a ha j

/-- Consequently the checked four-X branch reaches the named Lemma 4.10
estimate as soon as the two literal column candidate tails are supplied. -/
theorem prop47Lemma410Estimate_of_xDirections_of_yColumns
    {C d : ℝ} (hC : 0 ≤ C) (hd : 0 < d)
    (hX : Prop47Lemma410Prop48StoppedCandidateTailXDirections C d)
    (hY : Prop47Lemma410Prop48StoppedCandidateTailYColumns C d) :
    Prop47Lemma410Estimate 1 :=
  prop47Lemma410Estimate_of_prop48StoppedCandidateTail hC hd
    (prop47Lemma410Prop48StoppedCandidateTail_of_xDirections_of_yColumns
      hX hY)

/-- Direct source-facing form: the checked four-parity `X₁` inputs supply
all four checkerboard directions after reunion, quarter-turn transport, and
high-band emptiness.  Only the literal two-column tail remains as an input
to the named Lemma 4.10 estimate. -/
theorem prop47Lemma410Estimate_of_prop48XInputs_of_yColumns
    (cWindow : ℕ) {Csmall Cfull cBase cTheta thetaPower d : ℝ}
    (hsmall : 0 ≤ Csmall) (hgap : Csmall + 20 ≤ Cfull)
    (hcBase : 0 < cBase) (hcTheta : 0 < cTheta)
    (hthetaPower : 0 < thetaPower) (hd : 0 < d)
    (hcompare : 16 * d ≤
      min cBase
        (imbalanceRate
          (Real.exp (sourceAdjacentComparisonExponent cWindow))) / 2)
    (hLeft : Prop47Lemma410Prop48LeftParityLowBandInputs
      cWindow Csmall cBase cTheta thetaPower)
    (hRight : Prop47Lemma410Prop48RightParityLowBandInputs
      cWindow Csmall cBase cTheta thetaPower)
    (hY : Prop47Lemma410Prop48StoppedCandidateTailYColumns Cfull d) :
    Prop47Lemma410Estimate 1 := by
  have hCfull : 0 ≤ Cfull := by linarith
  exact prop47Lemma410Estimate_of_xDirections_of_yColumns hCfull hd
    (prop47Lemma410Prop48StoppedCandidateTailXDirections_of_inputs cWindow
      hsmall hgap hcBase hcTheta hthetaPower hd hcompare hLeft hRight)
    hY

end Erdos1166.HLOZLemma410Prop48XDirections
