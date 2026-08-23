/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos1166.Erdos1166HLOZLemma410CodedAtoms
import ErdosProblems.Erdos1166.Erdos1166HLOZProp47Lemma411412AllDirections

/-!
# Canonically coded outer atoms for HLOZ Lemmas 4.11--4.12

The strict rectangular Equation-(4.47) source packages used to enumerate
each stopped-source branch by `ℕ` and separately assume both a branch cover
and pairwise disjointness of the outer path atoms.  If the enumeration is
the family of fibres of one natural-valued stopped-data code, both facts are
automatic.  The code need not be measurable because every used stopped
source atom already is.  This file records that source-facing form and
forgets it to the already checked all-directions connector.

The first pair of structures retains a literal source object for every code
fibre as a compatibility layer.  The final source-facing pair is stronger:
it is indexed only by fibres meeting the branch failure and pads the natural
enumeration with a zero-mass atom elsewhere.  Consequently the final closure
does not ask for changed-path witnesses on empty Equation-(4.47) fibres.
-/

namespace Erdos1166.HLOZLemma411412CodedAtoms

open Filter Set

open HLOZPairing HLOZPairingProfiles HLOZProp47Prop45XRotations
open HLOZProp47Parameters HLOZProp47SourceObjects HLOZProp47SourceAssembly
open HLOZProp47Canonical
open HLOZProp47Lemma411412Connector HLOZProp47Lemma411412SourceAtoms
open HLOZProp47Lemma411412XEastBridge HLOZColumnSourceConsumers
open HLOZProp47Lemma411412XDirections
open HLOZLemma410CodedAtoms
open HLOZEquation447

abbrev Path := ℕ → Site

private theorem codeFiber_cover
    (rawCode : Path → ℕ) (sourcePathAtom : ℕ → Set Path)
    (pathAtom_eq : ∀ eta,
      sourcePathAtom eta = lemma410RawCodeFiber rawCode eta) :
    Set.univ ⊆ ⋃ eta, sourcePathAtom eta := by
  intro s _
  refine Set.mem_iUnion.mpr ⟨rawCode s, ?_⟩
  rw [pathAtom_eq]
  simp [lemma410RawCodeFiber]

private theorem codeFiber_pairwise
    (rawCode : Path → ℕ) (sourcePathAtom : ℕ → Set Path)
    (pathAtom_eq : ∀ eta,
      sourcePathAtom eta = lemma410RawCodeFiber rawCode eta) :
    Pairwise fun eta zeta ↦
      Disjoint (sourcePathAtom eta) (sourcePathAtom zeta) := by
  intro eta zeta hne
  rw [pathAtom_eq eta, pathAtom_eq zeta]
  exact lemma410RawCodeFiber_pairwise rawCode hne

/-- A path-witness branch indexed only by the code fibres which actually
meet its failure event. -/
structure NonemptyCodedPathWitnessBranch
    (cWindow m : ℕ) (c rho : ℝ)
    (failure thetaTarget : Set Path) where
  rawCode : Path → ℕ
  atom : FailureCode failure rawCode →
    StoppedEquation447PathWitnessBranchAtom cWindow m c failure rho
  pathAtom_eq : ∀ eta,
    (atom eta).pathAtom = lemma410RawCodeFiber rawCode eta.1
  theta_subset : ∀ eta, (atom eta).thetaPathEvent ⊆ thetaTarget

namespace NonemptyCodedPathWitnessBranch

variable {cWindow m : ℕ} {c rho : ℝ}
  {failure thetaTarget : Set Path}

/-- Natural-number enumeration of the nonempty fibres.  Integers outside
the range of the canonical encoder are filled by the zero-mass atom. -/
noncomputable def natAtom
    (D : NonemptyCodedPathWitnessBranch
      cWindow m c rho failure thetaTarget) (n : ℕ) :
    StoppedEquation447PathWitnessBranchAtom cWindow m c failure rho := by
  letI : Encodable (FailureCode failure D.rawCode) :=
    Encodable.ofCountable _
  exact match Encodable.decode₂ (FailureCode failure D.rawCode) n with
    | some eta => D.atom eta
    | none => emptyPathWitnessBranchAtom cWindow m c failure rho

@[simp] theorem natAtom_encode
    (D : NonemptyCodedPathWitnessBranch
      cWindow m c rho failure thetaTarget)
    (eta : FailureCode failure D.rawCode) :
    letI : Encodable (FailureCode failure D.rawCode) :=
      Encodable.ofCountable _
    D.natAtom (Encodable.encode eta) = D.atom eta := by
  letI : Encodable (FailureCode failure D.rawCode) :=
    Encodable.ofCountable _
  simp [natAtom]

theorem cover_natAtom
    (D : NonemptyCodedPathWitnessBranch
      cWindow m c rho failure thetaTarget) :
    failure ∩ HLOZSourceInstantiation.simpleRandomWalkSupport ⊆
      ⋃ n, (D.natAtom n).pathAtom := by
  intro s hs
  let eta : FailureCode failure D.rawCode :=
    ⟨D.rawCode s, ⟨s, hs, by simp [lemma410RawCodeFiber]⟩⟩
  letI : Encodable (FailureCode failure D.rawCode) :=
    Encodable.ofCountable _
  refine Set.mem_iUnion.mpr ⟨Encodable.encode eta, ?_⟩
  rw [D.natAtom_encode eta, D.pathAtom_eq eta]
  simp [lemma410RawCodeFiber, eta]

theorem theta_natAtom
    (D : NonemptyCodedPathWitnessBranch
      cWindow m c rho failure thetaTarget) (n : ℕ) :
    (D.natAtom n).thetaPathEvent ⊆ thetaTarget := by
  letI : Encodable (FailureCode failure D.rawCode) :=
    Encodable.ofCountable _
  simp only [natAtom]
  split
  · rename_i eta hdecode
    exact D.theta_subset eta
  · simp [emptyPathWitnessBranchAtom]

theorem pairwise_natAtom
    (D : NonemptyCodedPathWitnessBranch
      cWindow m c rho failure thetaTarget) :
    Pairwise fun n k ↦
      Disjoint (D.natAtom n).pathAtom (D.natAtom k).pathAtom := by
  letI : Encodable (FailureCode failure D.rawCode) :=
    Encodable.ofCountable _
  intro n k hne
  simp only [natAtom]
  split
  · rename_i eta hn
    split
    · rename_i zeta hk
      have hencodeEta : Encodable.encode eta = n :=
        Encodable.decode₂_eq_some.mp hn
      have hencodeZeta : Encodable.encode zeta = k :=
        Encodable.decode₂_eq_some.mp hk
      have hetazeta : eta ≠ zeta := by
        intro h
        apply hne
        rw [← hencodeEta, ← hencodeZeta, h]
      rw [D.pathAtom_eq eta, D.pathAtom_eq zeta]
      exact lemma410RawCodeFiber_pairwise D.rawCode
        (fun h ↦ hetazeta (Subtype.ext h))
    · simp [emptyPathWitnessBranchAtom]
  · simp [emptyPathWitnessBranchAtom]

end NonemptyCodedPathWitnessBranch

/-! ## The four coded X-east branches -/

/-- Strict rectangular Equation-(4.47) data for the four canonical X-east
branches, with each outer stopped-source family given by a natural code.
The code equations make the four covers and four disjointness proofs formal
consequences. -/
structure XEastCanonicalCodedFourBranchLengthSeparatedRectangularData
    (cWindow m : ℕ) (ratioC : ℝ) (r : StageIndex) where
  unprimedEvenRawCode : Path → ℕ
  unprimedEven : ℕ → UnprimedEvenLeftWinnerSource m
  unprimedEvenPathAtom : ∀ eta,
    (unprimedEven eta).pathAtom =
      lemma410RawCodeFiber unprimedEvenRawCode eta
  unprimedEvenRemaining : ∀ eta,
    Equation447LengthSeparatedRectangularOptimalCategoricalPathWitnessBranchRemainingData
      cWindow m ratioC ((1 / 4 : ℝ) * Real.log (m : ℝ) ^ 2)
      (xEastEquation447UnprimedEvenBranch m r)
      (stoppedThetaEvent (sourceCanonicalProfiles (xIndex east))
        (canonicalCStar (xIndex east)) m (stageNumber r))
      (unprimedEven eta).pathAtom (unprimedEven eta).profile
      (unprimedEven eta).lazyVector (unprimedEven eta).nextDirection

  unprimedOddRawCode : Path → ℕ
  unprimedOdd : ℕ → UnprimedOddTerminalTieLeftSource m
  unprimedOddPathAtom : ∀ eta,
    (unprimedOdd eta).pathAtom =
      lemma410RawCodeFiber unprimedOddRawCode eta
  unprimedOddRemaining : ∀ eta,
    Equation447LengthSeparatedRectangularOptimalCategoricalPathWitnessBranchRemainingData
      cWindow m ratioC ((1 / 4 : ℝ) * Real.log (m : ℝ) ^ 2)
      (xEastEquation447UnprimedOddBranch m r)
      (stoppedThetaEvent (sourceCanonicalProfiles (xIndex east))
        (canonicalCStar (xIndex east)) m (stageNumber r))
      (unprimedOdd eta).pathAtom (unprimedOdd eta).profile
      (unprimedOdd eta).lazyVector (unprimedOdd eta).nextDirection

  primedOddRawCode : Path → ℕ
  primedOdd : ℕ → PrimedOddStrictRightWinnerSource m
  primedOddPathAtom : ∀ eta,
    (primedOdd eta).pathAtom =
      lemma410RawCodeFiber primedOddRawCode eta
  primedOddRemaining : ∀ eta,
    Equation447LengthSeparatedRectangularOptimalCategoricalPathWitnessBranchRemainingData
      cWindow m ratioC ((1 / 4 : ℝ) * Real.log (m : ℝ) ^ 2)
      (xEastEquation447PrimedOddBranch m r)
      (stoppedThetaEvent (sourceCanonicalProfiles (xIndex east))
        (canonicalCStar (xIndex east)) m (stageNumber r))
      (primedOdd eta).pathAtom (primedOdd eta).profile
      (primedOdd eta).lazyVector (primedOdd eta).nextDirection

  primedEvenRawCode : Path → ℕ
  primedEven : ℕ → PrimedEvenTerminalStrictRightSource m
  primedEvenPathAtom : ∀ eta,
    (primedEven eta).pathAtom =
      lemma410RawCodeFiber primedEvenRawCode eta
  primedEvenRemaining : ∀ eta,
    Equation447LengthSeparatedRectangularOptimalCategoricalPathWitnessBranchRemainingData
      cWindow m ratioC ((1 / 4 : ℝ) * Real.log (m : ℝ) ^ 2)
      (xEastEquation447PrimedEvenBranch m r)
      (stoppedThetaEvent (sourceCanonicalProfiles (xIndex east))
        (canonicalCStar (xIndex east)) m (stageNumber r))
      (primedEven eta).pathAtom (primedEven eta).profile
      (primedEven eta).lazyVector (primedEven eta).nextDirection

namespace XEastCanonicalCodedFourBranchLengthSeparatedRectangularData

variable {cWindow m : ℕ} {ratioC : ℝ} {r : StageIndex}

/-- Forget the code and reconstruct the former four explicit covers and
pairwise-disjointness fields. -/
noncomputable def toSourceData
    (D : XEastCanonicalCodedFourBranchLengthSeparatedRectangularData
      cWindow m ratioC r) :
    XEastCanonicalFourBranchLengthSeparatedRectangularOptimalCategoricalPathWitnessSourceData
      cWindow m ratioC r where
  unprimedEven := D.unprimedEven
  unprimedOdd := D.unprimedOdd
  primedOdd := D.primedOdd
  primedEven := D.primedEven
  unprimedEvenRemaining := D.unprimedEvenRemaining
  unprimedOddRemaining := D.unprimedOddRemaining
  primedOddRemaining := D.primedOddRemaining
  primedEvenRemaining := D.primedEvenRemaining
  unprimedEven_cover :=
    (Set.subset_univ _).trans <| codeFiber_cover
      D.unprimedEvenRawCode (fun eta ↦ (D.unprimedEven eta).pathAtom)
        D.unprimedEvenPathAtom
  unprimedOdd_cover :=
    (Set.subset_univ _).trans <| codeFiber_cover
      D.unprimedOddRawCode (fun eta ↦ (D.unprimedOdd eta).pathAtom)
        D.unprimedOddPathAtom
  primedOdd_cover :=
    (Set.subset_univ _).trans <| codeFiber_cover
      D.primedOddRawCode (fun eta ↦ (D.primedOdd eta).pathAtom)
        D.primedOddPathAtom
  primedEven_cover :=
    (Set.subset_univ _).trans <| codeFiber_cover
      D.primedEvenRawCode (fun eta ↦ (D.primedEven eta).pathAtom)
        D.primedEvenPathAtom
  unprimedEven_disjoint := codeFiber_pairwise
    D.unprimedEvenRawCode (fun eta ↦ (D.unprimedEven eta).pathAtom)
      D.unprimedEvenPathAtom
  unprimedOdd_disjoint := codeFiber_pairwise
    D.unprimedOddRawCode (fun eta ↦ (D.unprimedOdd eta).pathAtom)
      D.unprimedOddPathAtom
  primedOdd_disjoint := codeFiber_pairwise
    D.primedOddRawCode (fun eta ↦ (D.primedOdd eta).pathAtom)
      D.primedOddPathAtom
  primedEven_disjoint := codeFiber_pairwise
    D.primedEvenRawCode (fun eta ↦ (D.primedEven eta).pathAtom)
      D.primedEvenPathAtom

end XEastCanonicalCodedFourBranchLengthSeparatedRectangularData

/-- Eventual coded X-east Equation-(4.47) source input. -/
def Prop47Lemma411412XEastCanonicalCodedRectangularInputs
    (cWindow : ℕ) (ratioC : ℝ) : Prop :=
  ∀ᶠ m : ℕ in atTop, ∀ r : StageIndex,
    Nonempty (XEastCanonicalCodedFourBranchLengthSeparatedRectangularData
      cWindow m ratioC r)

theorem xEastRectangularInputs_of_coded
    (cWindow : ℕ) (ratioC : ℝ)
    (h : Prop47Lemma411412XEastCanonicalCodedRectangularInputs
      cWindow ratioC) :
    Prop47Lemma411412XEastCanonicalFourBranchLengthSeparatedRectangularOptimalCategoricalPathWitnessSourceInputs
      cWindow ratioC := by
  filter_upwards [h] with m hm
  intro r
  rcases hm r with ⟨D⟩
  exact ⟨D.toSourceData⟩

/-! ## The two coded temporal column phases -/

/-- Strict rectangular Equation-(4.47) data for the two canonical temporal
column phases, again with the outer stopped-source families supplied by
natural codes. -/
structure YCanonicalCodedTwoPhaseLengthSeparatedRectangularData
    (cWindow m : ℕ) (ratioC : ℝ) (r : StageIndex) where
  forwardRawCode : Path → ℕ
  forwardSource : ℕ → ForwardColumnWinnerSource m
  forwardPathAtom : ∀ eta,
    (forwardSource eta).pathAtom =
      lemma410RawCodeFiber forwardRawCode eta
  forwardRemaining : ∀ eta,
    Equation447LengthSeparatedRectangularOptimalCategoricalPathWitnessBranchRemainingData
      cWindow m ratioC ((1 / 4 : ℝ) * Real.log (m : ℝ) ^ 2)
      (yEquation447ForwardBranch m r)
      (stoppedThetaEvent (sourceCanonicalProfiles yIndex)
        (canonicalCStar yIndex) m (stageNumber r))
      (forwardSource eta).pathAtom (forwardSource eta).profile
      (forwardSource eta).lazyVector (forwardSource eta).nextDirection

  backwardRawCode : Path → ℕ
  backwardSource : ℕ → PrimedColumnWinnerSource m
  backwardPathAtom : ∀ eta,
    (backwardSource eta).pathAtom =
      lemma410RawCodeFiber backwardRawCode eta
  backwardRemaining : ∀ eta,
    Equation447LengthSeparatedRectangularOptimalCategoricalPathWitnessBranchRemainingData
      cWindow m ratioC ((1 / 4 : ℝ) * Real.log (m : ℝ) ^ 2)
      (yEquation447BackwardBranch m r)
      (stoppedThetaEvent (sourceCanonicalProfiles yIndex)
        (canonicalCStar yIndex) m (stageNumber r))
      (backwardSource eta).pathAtom (backwardSource eta).profile
      (backwardSource eta).lazyVector (backwardSource eta).nextDirection

namespace YCanonicalCodedTwoPhaseLengthSeparatedRectangularData

variable {cWindow m : ℕ} {ratioC : ℝ} {r : StageIndex}

noncomputable def toSourceData
    (D : YCanonicalCodedTwoPhaseLengthSeparatedRectangularData
      cWindow m ratioC r) :
    YCanonicalTwoPhaseEquation447LengthSeparatedRectangularOptimalCategoricalPathWitnessSourceData
      cWindow m ratioC r where
  forward := {
    source := D.forwardSource
    remaining := D.forwardRemaining
    cover := (Set.subset_univ _).trans <| codeFiber_cover
      D.forwardRawCode (fun eta ↦ (D.forwardSource eta).pathAtom)
        D.forwardPathAtom
    pairwise_disjoint := codeFiber_pairwise
      D.forwardRawCode (fun eta ↦ (D.forwardSource eta).pathAtom)
        D.forwardPathAtom }
  backward := {
    source := D.backwardSource
    remaining := D.backwardRemaining
    cover := (Set.subset_univ _).trans <| codeFiber_cover
      D.backwardRawCode (fun eta ↦ (D.backwardSource eta).pathAtom)
        D.backwardPathAtom
    pairwise_disjoint := codeFiber_pairwise
      D.backwardRawCode (fun eta ↦ (D.backwardSource eta).pathAtom)
        D.backwardPathAtom }

end YCanonicalCodedTwoPhaseLengthSeparatedRectangularData

/-- Eventual coded temporal-column Equation-(4.47) source input. -/
def Prop47Lemma411412YCanonicalCodedRectangularInputs
    (cWindow : ℕ) (ratioC : ℝ) : Prop :=
  ∀ᶠ m : ℕ in atTop, ∀ r : StageIndex,
    Nonempty (YCanonicalCodedTwoPhaseLengthSeparatedRectangularData
      cWindow m ratioC r)

theorem yRectangularInputs_of_coded
    (cWindow : ℕ) (ratioC : ℝ)
    (h : Prop47Lemma411412YCanonicalCodedRectangularInputs
      cWindow ratioC) :
    Prop47Lemma411412YCanonicalTwoPhaseLengthSeparatedRectangularOptimalCategoricalPathWitnessSourceInputs
      cWindow ratioC := by
  filter_upwards [h] with m hm
  intro r
  rcases hm r with ⟨D⟩
  exact ⟨D.toSourceData⟩

/-! ## Empty-fibre-free strict rectangular packages

The conservative structures above are useful compatibility wrappers, but
they still ask for a literal stopped source on every natural-number fibre.
The structures below retain sources only on `FailureCode`, i.e. on fibres
which actually meet the branch failure.  The zero-mass padding theorem at
the start of this file then supplies the total natural-number family needed
by the finite-branch measure connector.
-/

/-- Convert the strongest rectangular, length-separated source remainder
directly to the deleted-path witness remainder after the checked optimal
binomial layer has been chosen. -/
noncomputable def rectangularLengthSeparatedRemainingToPathWitness
    {Coord : Type} [Fintype Coord]
    {cWindow m : ℕ} {ratioC rho : ℝ}
    {failure thetaPathEvent pathAtom : Set Path}
    {profile : Coord → ℕ}
    {lazyVector : Path → Coord → ℕ}
    {nextDirection : Path → Direction}
    (R :
      Equation447LengthSeparatedRectangularOptimalCategoricalPathWitnessBranchRemainingData
        cWindow m ratioC rho failure thetaPathEvent pathAtom
          profile lazyVector nextDirection)
    (hC : 0 < ratioC)
    (hbinomial : ∀ q, Nat.ceil rho ≤ q →
      ratioC ^ categoricalOptimalWitnessCount ratioC q ≤
        Real.exp (-categoricalOptimalRate ratioC * (q : ℝ)) *
          Nat.choose q (categoricalOptimalWitnessCount ratioC q)) :
    Equation447PathWitnessBranchRemainingData cWindow m
      (categoricalOptimalRate ratioC) rho
      failure pathAtom profile lazyVector nextDirection :=
  R.toLengthSeparatedOptimalCategoricalPathWitnessBranchRemainingData
    |>.toOptimalCategoricalPathWitnessBranchRemainingData
    |>.toRemainingData hC hbinomial

/-- Four X-east strict rectangular branches whose stopped sources are
provided only on code fibres meeting the corresponding failure event. -/
structure XEastCanonicalNonemptyCodedFourBranchRectangularData
    (cWindow m : ℕ) (ratioC : ℝ) (r : StageIndex) where
  unprimedEvenRawCode : Path → ℕ
  unprimedEven : FailureCode
    (xEastEquation447UnprimedEvenBranch m r) unprimedEvenRawCode →
      UnprimedEvenLeftWinnerSource m
  unprimedEvenPathAtom : ∀ eta,
    (unprimedEven eta).pathAtom =
      lemma410RawCodeFiber unprimedEvenRawCode eta.1
  unprimedEvenRemaining : ∀ eta,
    Equation447LengthSeparatedRectangularOptimalCategoricalPathWitnessBranchRemainingData
      cWindow m ratioC ((1 / 4 : ℝ) * Real.log (m : ℝ) ^ 2)
      (xEastEquation447UnprimedEvenBranch m r)
      (stoppedThetaEvent (sourceCanonicalProfiles (xIndex east))
        (canonicalCStar (xIndex east)) m (stageNumber r))
      (unprimedEven eta).pathAtom (unprimedEven eta).profile
      (unprimedEven eta).lazyVector (unprimedEven eta).nextDirection

  unprimedOddRawCode : Path → ℕ
  unprimedOdd : FailureCode
    (xEastEquation447UnprimedOddBranch m r) unprimedOddRawCode →
      UnprimedOddTerminalTieLeftSource m
  unprimedOddPathAtom : ∀ eta,
    (unprimedOdd eta).pathAtom =
      lemma410RawCodeFiber unprimedOddRawCode eta.1
  unprimedOddRemaining : ∀ eta,
    Equation447LengthSeparatedRectangularOptimalCategoricalPathWitnessBranchRemainingData
      cWindow m ratioC ((1 / 4 : ℝ) * Real.log (m : ℝ) ^ 2)
      (xEastEquation447UnprimedOddBranch m r)
      (stoppedThetaEvent (sourceCanonicalProfiles (xIndex east))
        (canonicalCStar (xIndex east)) m (stageNumber r))
      (unprimedOdd eta).pathAtom (unprimedOdd eta).profile
      (unprimedOdd eta).lazyVector (unprimedOdd eta).nextDirection

  primedOddRawCode : Path → ℕ
  primedOdd : FailureCode
    (xEastEquation447PrimedOddBranch m r) primedOddRawCode →
      PrimedOddStrictRightWinnerSource m
  primedOddPathAtom : ∀ eta,
    (primedOdd eta).pathAtom =
      lemma410RawCodeFiber primedOddRawCode eta.1
  primedOddRemaining : ∀ eta,
    Equation447LengthSeparatedRectangularOptimalCategoricalPathWitnessBranchRemainingData
      cWindow m ratioC ((1 / 4 : ℝ) * Real.log (m : ℝ) ^ 2)
      (xEastEquation447PrimedOddBranch m r)
      (stoppedThetaEvent (sourceCanonicalProfiles (xIndex east))
        (canonicalCStar (xIndex east)) m (stageNumber r))
      (primedOdd eta).pathAtom (primedOdd eta).profile
      (primedOdd eta).lazyVector (primedOdd eta).nextDirection

  primedEvenRawCode : Path → ℕ
  primedEven : FailureCode
    (xEastEquation447PrimedEvenBranch m r) primedEvenRawCode →
      PrimedEvenTerminalStrictRightSource m
  primedEvenPathAtom : ∀ eta,
    (primedEven eta).pathAtom =
      lemma410RawCodeFiber primedEvenRawCode eta.1
  primedEvenRemaining : ∀ eta,
    Equation447LengthSeparatedRectangularOptimalCategoricalPathWitnessBranchRemainingData
      cWindow m ratioC ((1 / 4 : ℝ) * Real.log (m : ℝ) ^ 2)
      (xEastEquation447PrimedEvenBranch m r)
      (stoppedThetaEvent (sourceCanonicalProfiles (xIndex east))
        (canonicalCStar (xIndex east)) m (stageNumber r))
      (primedEven eta).pathAtom (primedEven eta).profile
      (primedEven eta).lazyVector (primedEven eta).nextDirection

/-- Two temporal column phases in the same nonempty-code-fibre form. -/
structure YCanonicalNonemptyCodedTwoPhaseRectangularData
    (cWindow m : ℕ) (ratioC : ℝ) (r : StageIndex) where
  forwardRawCode : Path → ℕ
  forwardSource : FailureCode
    (yEquation447ForwardBranch m r) forwardRawCode →
      ForwardColumnWinnerSource m
  forwardPathAtom : ∀ eta,
    (forwardSource eta).pathAtom =
      lemma410RawCodeFiber forwardRawCode eta.1
  forwardRemaining : ∀ eta,
    Equation447LengthSeparatedRectangularOptimalCategoricalPathWitnessBranchRemainingData
      cWindow m ratioC ((1 / 4 : ℝ) * Real.log (m : ℝ) ^ 2)
      (yEquation447ForwardBranch m r)
      (stoppedThetaEvent (sourceCanonicalProfiles yIndex)
        (canonicalCStar yIndex) m (stageNumber r))
      (forwardSource eta).pathAtom (forwardSource eta).profile
      (forwardSource eta).lazyVector (forwardSource eta).nextDirection

  backwardRawCode : Path → ℕ
  backwardSource : FailureCode
    (yEquation447BackwardBranch m r) backwardRawCode →
      PrimedColumnWinnerSource m
  backwardPathAtom : ∀ eta,
    (backwardSource eta).pathAtom =
      lemma410RawCodeFiber backwardRawCode eta.1
  backwardRemaining : ∀ eta,
    Equation447LengthSeparatedRectangularOptimalCategoricalPathWitnessBranchRemainingData
      cWindow m ratioC ((1 / 4 : ℝ) * Real.log (m : ℝ) ^ 2)
      (yEquation447BackwardBranch m r)
      (stoppedThetaEvent (sourceCanonicalProfiles yIndex)
        (canonicalCStar yIndex) m (stageNumber r))
      (backwardSource eta).pathAtom (backwardSource eta).profile
      (backwardSource eta).lazyVector (backwardSource eta).nextDirection

namespace XEastCanonicalNonemptyCodedFourBranchRectangularData

variable {cWindow m : ℕ} {ratioC : ℝ} {r : StageIndex}

noncomputable def unprimedEvenBranch
    (D : XEastCanonicalNonemptyCodedFourBranchRectangularData
      cWindow m ratioC r)
    (hC : 0 < ratioC)
    (hbinomial : ∀ q,
      Nat.ceil ((1 / 4 : ℝ) * Real.log (m : ℝ) ^ 2) ≤ q →
      ratioC ^ categoricalOptimalWitnessCount ratioC q ≤
        Real.exp (-categoricalOptimalRate ratioC * (q : ℝ)) *
          Nat.choose q (categoricalOptimalWitnessCount ratioC q)) :
    NonemptyCodedPathWitnessBranch cWindow m
      (categoricalOptimalRate ratioC)
      ((1 / 4 : ℝ) * Real.log (m : ℝ) ^ 2)
      (xEastEquation447UnprimedEvenBranch m r)
      (stoppedThetaEvent (sourceCanonicalProfiles (xIndex east))
        (canonicalCStar (xIndex east)) m (stageNumber r)) where
  rawCode := D.unprimedEvenRawCode
  atom := fun eta ↦
    (D.unprimedEven eta).toStoppedEquation447PathWitnessBranchAtom
      cWindow (categoricalOptimalRate ratioC)
      ((1 / 4 : ℝ) * Real.log (m : ℝ) ^ 2)
      (xEastEquation447UnprimedEvenBranch m r)
      (rectangularLengthSeparatedRemainingToPathWitness
        (D.unprimedEvenRemaining eta) hC hbinomial)
  pathAtom_eq := D.unprimedEvenPathAtom
  theta_subset := fun _ ↦ Set.Subset.rfl

noncomputable def unprimedOddBranch
    (D : XEastCanonicalNonemptyCodedFourBranchRectangularData
      cWindow m ratioC r)
    (hC : 0 < ratioC)
    (hbinomial : ∀ q,
      Nat.ceil ((1 / 4 : ℝ) * Real.log (m : ℝ) ^ 2) ≤ q →
      ratioC ^ categoricalOptimalWitnessCount ratioC q ≤
        Real.exp (-categoricalOptimalRate ratioC * (q : ℝ)) *
          Nat.choose q (categoricalOptimalWitnessCount ratioC q)) :
    NonemptyCodedPathWitnessBranch cWindow m
      (categoricalOptimalRate ratioC)
      ((1 / 4 : ℝ) * Real.log (m : ℝ) ^ 2)
      (xEastEquation447UnprimedOddBranch m r)
      (stoppedThetaEvent (sourceCanonicalProfiles (xIndex east))
        (canonicalCStar (xIndex east)) m (stageNumber r)) where
  rawCode := D.unprimedOddRawCode
  atom := fun eta ↦
    (D.unprimedOdd eta).toStoppedEquation447PathWitnessBranchAtom
      cWindow (categoricalOptimalRate ratioC)
      ((1 / 4 : ℝ) * Real.log (m : ℝ) ^ 2)
      (xEastEquation447UnprimedOddBranch m r)
      (rectangularLengthSeparatedRemainingToPathWitness
        (D.unprimedOddRemaining eta) hC hbinomial)
  pathAtom_eq := D.unprimedOddPathAtom
  theta_subset := fun _ ↦ Set.Subset.rfl

noncomputable def primedOddBranch
    (D : XEastCanonicalNonemptyCodedFourBranchRectangularData
      cWindow m ratioC r)
    (hC : 0 < ratioC)
    (hbinomial : ∀ q,
      Nat.ceil ((1 / 4 : ℝ) * Real.log (m : ℝ) ^ 2) ≤ q →
      ratioC ^ categoricalOptimalWitnessCount ratioC q ≤
        Real.exp (-categoricalOptimalRate ratioC * (q : ℝ)) *
          Nat.choose q (categoricalOptimalWitnessCount ratioC q)) :
    NonemptyCodedPathWitnessBranch cWindow m
      (categoricalOptimalRate ratioC)
      ((1 / 4 : ℝ) * Real.log (m : ℝ) ^ 2)
      (xEastEquation447PrimedOddBranch m r)
      (stoppedThetaEvent (sourceCanonicalProfiles (xIndex east))
        (canonicalCStar (xIndex east)) m (stageNumber r)) where
  rawCode := D.primedOddRawCode
  atom := fun eta ↦
    (D.primedOdd eta).toStoppedEquation447PathWitnessBranchAtom
      cWindow (categoricalOptimalRate ratioC)
      ((1 / 4 : ℝ) * Real.log (m : ℝ) ^ 2)
      (xEastEquation447PrimedOddBranch m r)
      (rectangularLengthSeparatedRemainingToPathWitness
        (D.primedOddRemaining eta) hC hbinomial)
  pathAtom_eq := D.primedOddPathAtom
  theta_subset := fun _ ↦ Set.Subset.rfl

noncomputable def primedEvenBranch
    (D : XEastCanonicalNonemptyCodedFourBranchRectangularData
      cWindow m ratioC r)
    (hC : 0 < ratioC)
    (hbinomial : ∀ q,
      Nat.ceil ((1 / 4 : ℝ) * Real.log (m : ℝ) ^ 2) ≤ q →
      ratioC ^ categoricalOptimalWitnessCount ratioC q ≤
        Real.exp (-categoricalOptimalRate ratioC * (q : ℝ)) *
          Nat.choose q (categoricalOptimalWitnessCount ratioC q)) :
    NonemptyCodedPathWitnessBranch cWindow m
      (categoricalOptimalRate ratioC)
      ((1 / 4 : ℝ) * Real.log (m : ℝ) ^ 2)
      (xEastEquation447PrimedEvenBranch m r)
      (stoppedThetaEvent (sourceCanonicalProfiles (xIndex east))
        (canonicalCStar (xIndex east)) m (stageNumber r)) where
  rawCode := D.primedEvenRawCode
  atom := fun eta ↦
    (D.primedEven eta).toStoppedEquation447PathWitnessBranchAtom
      cWindow (categoricalOptimalRate ratioC)
      ((1 / 4 : ℝ) * Real.log (m : ℝ) ^ 2)
      (xEastEquation447PrimedEvenBranch m r)
      (rectangularLengthSeparatedRemainingToPathWitness
        (D.primedEvenRemaining eta) hC hbinomial)
  pathAtom_eq := D.primedEvenPathAtom
  theta_subset := fun _ ↦ Set.Subset.rfl

def branchEvent
    (_D : XEastCanonicalNonemptyCodedFourBranchRectangularData
      cWindow m ratioC r) : Fin 4 → Set Path := fun j ↦
  match j.1 with
  | 0 => xEastEquation447UnprimedEvenBranch m r
  | 1 => xEastEquation447UnprimedOddBranch m r
  | 2 => xEastEquation447PrimedOddBranch m r
  | _ => xEastEquation447PrimedEvenBranch m r

noncomputable def rho
    (_D : XEastCanonicalNonemptyCodedFourBranchRectangularData
      cWindow m ratioC r) : Fin 4 → ℝ :=
  fun _ ↦ (1 / 4 : ℝ) * Real.log (m : ℝ) ^ 2

noncomputable def atoms
    (D : XEastCanonicalNonemptyCodedFourBranchRectangularData
      cWindow m ratioC r)
    (hC : 0 < ratioC)
    (hbinomial : ∀ q,
      Nat.ceil ((1 / 4 : ℝ) * Real.log (m : ℝ) ^ 2) ≤ q →
      ratioC ^ categoricalOptimalWitnessCount ratioC q ≤
        Real.exp (-categoricalOptimalRate ratioC * (q : ℝ)) *
          Nat.choose q (categoricalOptimalWitnessCount ratioC q))
    (j : Fin 4) (n : ℕ) :
    StoppedEquation447PathWitnessBranchAtom cWindow m
      (categoricalOptimalRate ratioC) (D.branchEvent j) (D.rho j) := by
  by_cases h0 : j = 0
  · subst j
    exact (D.unprimedEvenBranch hC hbinomial).natAtom n
  by_cases h1 : j = 1
  · subst j
    exact (D.unprimedOddBranch hC hbinomial).natAtom n
  by_cases h2 : j = 2
  · subst j
    exact (D.primedOddBranch hC hbinomial).natAtom n
  have h3 : j = 3 := by
    apply Fin.ext
    omega
  subst j
  exact (D.primedEvenBranch hC hbinomial).natAtom n

theorem finiteBranchWitness
    (D : XEastCanonicalNonemptyCodedFourBranchRectangularData
      cWindow m ratioC r)
    (hm : 0 < m) (hC : 0 < ratioC)
    (hbinomial : ∀ q,
      Nat.ceil ((1 / 4 : ℝ) * Real.log (m : ℝ) ^ 2) ≤ q →
      ratioC ^ categoricalOptimalWitnessCount ratioC q ≤
        Real.exp (-categoricalOptimalRate ratioC * (q : ℝ)) *
          Nat.choose q (categoricalOptimalWitnessCount ratioC q)) :
    ∃ branchFailure : Fin 4 → Set Path,
      ∃ rho : Fin 4 → ℝ,
      ∃ atoms : (j : Fin 4) → ℕ →
          StoppedEquation447PathWitnessBranchAtom cWindow m
            (categoricalOptimalRate ratioC) (branchFailure j) (rho j),
        lemma411412CardinalityFailureEvent m (xIndex east) r ⊆
            ⋃ j, branchFailure j ∧
        (∀ j, (1 / 4 : ℝ) * Real.log (m : ℝ) ^ 2 ≤ rho j) ∧
        (∀ j, branchFailure j ∩
            HLOZSourceInstantiation.simpleRandomWalkSupport ⊆
          ⋃ n, (atoms j n).pathAtom) ∧
        (∀ j n, (atoms j n).thetaPathEvent ⊆
          stoppedThetaEvent (sourceCanonicalProfiles (xIndex east))
            (canonicalCStar (xIndex east)) m (stageNumber r)) ∧
        ∀ j, Pairwise fun n k ↦
          Disjoint (atoms j n).pathAtom (atoms j k).pathAtom := by
  refine ⟨D.branchEvent, D.rho, D.atoms hC hbinomial,
    ?_, ?_, ?_, ?_, ?_⟩
  · intro s hs
    rcases lemma411412CardinalityFailureEvent_xEast_subset_canonicalBranches
        m r hm hs with ((h | h) | h) | h
    · exact Set.mem_iUnion.mpr ⟨0, h⟩
    · exact Set.mem_iUnion.mpr ⟨1, h⟩
    · exact Set.mem_iUnion.mpr ⟨2, h⟩
    · exact Set.mem_iUnion.mpr ⟨3, h⟩
  · intro j
    simp [rho]
  · intro j
    fin_cases j
    · simpa [branchEvent, atoms] using
        (D.unprimedEvenBranch hC hbinomial).cover_natAtom
    · simpa [branchEvent, atoms] using
        (D.unprimedOddBranch hC hbinomial).cover_natAtom
    · simpa [branchEvent, atoms] using
        (D.primedOddBranch hC hbinomial).cover_natAtom
    · simpa [branchEvent, atoms] using
        (D.primedEvenBranch hC hbinomial).cover_natAtom
  · intro j n
    fin_cases j
    · simpa [atoms] using
        (D.unprimedEvenBranch hC hbinomial).theta_natAtom n
    · simpa [atoms] using
        (D.unprimedOddBranch hC hbinomial).theta_natAtom n
    · simpa [atoms] using
        (D.primedOddBranch hC hbinomial).theta_natAtom n
    · simpa [atoms] using
        (D.primedEvenBranch hC hbinomial).theta_natAtom n
  · intro j
    fin_cases j
    · simpa [atoms] using
        (D.unprimedEvenBranch hC hbinomial).pairwise_natAtom
    · simpa [atoms] using
        (D.unprimedOddBranch hC hbinomial).pairwise_natAtom
    · simpa [atoms] using
        (D.primedOddBranch hC hbinomial).pairwise_natAtom
    · simpa [atoms] using
        (D.primedEvenBranch hC hbinomial).pairwise_natAtom

end XEastCanonicalNonemptyCodedFourBranchRectangularData

namespace YCanonicalNonemptyCodedTwoPhaseRectangularData

variable {cWindow m : ℕ} {ratioC : ℝ} {r : StageIndex}

noncomputable def forwardBranch
    (D : YCanonicalNonemptyCodedTwoPhaseRectangularData
      cWindow m ratioC r)
    (hC : 0 < ratioC)
    (hbinomial : ∀ q,
      Nat.ceil ((1 / 4 : ℝ) * Real.log (m : ℝ) ^ 2) ≤ q →
      ratioC ^ categoricalOptimalWitnessCount ratioC q ≤
        Real.exp (-categoricalOptimalRate ratioC * (q : ℝ)) *
          Nat.choose q (categoricalOptimalWitnessCount ratioC q)) :
    NonemptyCodedPathWitnessBranch cWindow m
      (categoricalOptimalRate ratioC)
      ((1 / 4 : ℝ) * Real.log (m : ℝ) ^ 2)
      (yEquation447ForwardBranch m r)
      (stoppedThetaEvent (sourceCanonicalProfiles yIndex)
        (canonicalCStar yIndex) m (stageNumber r)) where
  rawCode := D.forwardRawCode
  atom := fun eta ↦
    (D.forwardSource eta).toStoppedEquation447PathWitnessBranchAtom
      cWindow (categoricalOptimalRate ratioC)
      ((1 / 4 : ℝ) * Real.log (m : ℝ) ^ 2)
      (yEquation447ForwardBranch m r)
      (rectangularLengthSeparatedRemainingToPathWitness
        (D.forwardRemaining eta) hC hbinomial)
  pathAtom_eq := D.forwardPathAtom
  theta_subset := fun _ ↦ Set.Subset.rfl

noncomputable def backwardBranch
    (D : YCanonicalNonemptyCodedTwoPhaseRectangularData
      cWindow m ratioC r)
    (hC : 0 < ratioC)
    (hbinomial : ∀ q,
      Nat.ceil ((1 / 4 : ℝ) * Real.log (m : ℝ) ^ 2) ≤ q →
      ratioC ^ categoricalOptimalWitnessCount ratioC q ≤
        Real.exp (-categoricalOptimalRate ratioC * (q : ℝ)) *
          Nat.choose q (categoricalOptimalWitnessCount ratioC q)) :
    NonemptyCodedPathWitnessBranch cWindow m
      (categoricalOptimalRate ratioC)
      ((1 / 4 : ℝ) * Real.log (m : ℝ) ^ 2)
      (yEquation447BackwardBranch m r)
      (stoppedThetaEvent (sourceCanonicalProfiles yIndex)
        (canonicalCStar yIndex) m (stageNumber r)) where
  rawCode := D.backwardRawCode
  atom := fun eta ↦
    (D.backwardSource eta).toStoppedEquation447PathWitnessBranchAtom
      cWindow (categoricalOptimalRate ratioC)
      ((1 / 4 : ℝ) * Real.log (m : ℝ) ^ 2)
      (yEquation447BackwardBranch m r)
      (rectangularLengthSeparatedRemainingToPathWitness
        (D.backwardRemaining eta) hC hbinomial)
  pathAtom_eq := D.backwardPathAtom
  theta_subset := fun _ ↦ Set.Subset.rfl

def branchEvent
    (_D : YCanonicalNonemptyCodedTwoPhaseRectangularData
      cWindow m ratioC r) : Fin 2 → Set Path := fun j ↦
  match j.1 with
  | 0 => yEquation447ForwardBranch m r
  | _ => yEquation447BackwardBranch m r

noncomputable def rho
    (_D : YCanonicalNonemptyCodedTwoPhaseRectangularData
      cWindow m ratioC r) : Fin 2 → ℝ :=
  fun _ ↦ (1 / 4 : ℝ) * Real.log (m : ℝ) ^ 2

noncomputable def atoms
    (D : YCanonicalNonemptyCodedTwoPhaseRectangularData
      cWindow m ratioC r)
    (hC : 0 < ratioC)
    (hbinomial : ∀ q,
      Nat.ceil ((1 / 4 : ℝ) * Real.log (m : ℝ) ^ 2) ≤ q →
      ratioC ^ categoricalOptimalWitnessCount ratioC q ≤
        Real.exp (-categoricalOptimalRate ratioC * (q : ℝ)) *
          Nat.choose q (categoricalOptimalWitnessCount ratioC q))
    (j : Fin 2) (n : ℕ) :
    StoppedEquation447PathWitnessBranchAtom cWindow m
      (categoricalOptimalRate ratioC) (D.branchEvent j) (D.rho j) := by
  by_cases h0 : j = 0
  · subst j
    exact (D.forwardBranch hC hbinomial).natAtom n
  have h1 : j = 1 := by
    apply Fin.ext
    omega
  subst j
  exact (D.backwardBranch hC hbinomial).natAtom n

theorem finiteBranchWitness
    (D : YCanonicalNonemptyCodedTwoPhaseRectangularData
      cWindow m ratioC r)
    (hC : 0 < ratioC)
    (hbinomial : ∀ q,
      Nat.ceil ((1 / 4 : ℝ) * Real.log (m : ℝ) ^ 2) ≤ q →
      ratioC ^ categoricalOptimalWitnessCount ratioC q ≤
        Real.exp (-categoricalOptimalRate ratioC * (q : ℝ)) *
          Nat.choose q (categoricalOptimalWitnessCount ratioC q)) :
    ∃ branchFailure : Fin 2 → Set Path,
      ∃ rho : Fin 2 → ℝ,
      ∃ atoms : (j : Fin 2) → ℕ →
          StoppedEquation447PathWitnessBranchAtom cWindow m
            (categoricalOptimalRate ratioC) (branchFailure j) (rho j),
        lemma411412CardinalityFailureEvent m yIndex r ⊆
            ⋃ j, branchFailure j ∧
        (∀ j, (1 / 4 : ℝ) * Real.log (m : ℝ) ^ 2 ≤ rho j) ∧
        (∀ j, branchFailure j ∩
            HLOZSourceInstantiation.simpleRandomWalkSupport ⊆
          ⋃ n, (atoms j n).pathAtom) ∧
        (∀ j n, (atoms j n).thetaPathEvent ⊆
          stoppedThetaEvent (sourceCanonicalProfiles yIndex)
            (canonicalCStar yIndex) m (stageNumber r)) ∧
        ∀ j, Pairwise fun n k ↦
          Disjoint (atoms j n).pathAtom (atoms j k).pathAtom := by
  refine ⟨D.branchEvent, D.rho, D.atoms hC hbinomial,
    ?_, ?_, ?_, ?_, ?_⟩
  · intro s hs
    rcases lemma411412CardinalityFailureEvent_y_subset_canonicalBranches
        m r hs with h | h
    · exact Set.mem_iUnion.mpr ⟨0, h⟩
    · exact Set.mem_iUnion.mpr ⟨1, h⟩
  · intro j
    simp [rho]
  · intro j
    fin_cases j
    · simpa [branchEvent, atoms] using
        (D.forwardBranch hC hbinomial).cover_natAtom
    · simpa [branchEvent, atoms] using
        (D.backwardBranch hC hbinomial).cover_natAtom
  · intro j n
    fin_cases j
    · simpa [atoms] using
        (D.forwardBranch hC hbinomial).theta_natAtom n
    · simpa [atoms] using
        (D.backwardBranch hC hbinomial).theta_natAtom n
  · intro j
    fin_cases j
    · simpa [atoms] using
        (D.forwardBranch hC hbinomial).pairwise_natAtom
    · simpa [atoms] using
        (D.backwardBranch hC hbinomial).pairwise_natAtom

end YCanonicalNonemptyCodedTwoPhaseRectangularData

/-- Eventual X-east source input with no witnesses on empty code fibres. -/
def Prop47Lemma411412XEastCanonicalNonemptyCodedRectangularInputs
    (cWindow : ℕ) (ratioC : ℝ) : Prop :=
  ∀ᶠ m : ℕ in atTop, ∀ r : StageIndex,
    Nonempty (XEastCanonicalNonemptyCodedFourBranchRectangularData
      cWindow m ratioC r)

/-- Eventual temporal-column source input with no witnesses on empty code
fibres. -/
def Prop47Lemma411412YCanonicalNonemptyCodedRectangularInputs
    (cWindow : ℕ) (ratioC : ℝ) : Prop :=
  ∀ᶠ m : ℕ in atTop, ∀ r : StageIndex,
    Nonempty (YCanonicalNonemptyCodedTwoPhaseRectangularData
      cWindow m ratioC r)

/-- The nonempty-fibre X-east package directly supplies the path-witness
atomization, with zero-mass atoms padding unused natural numbers. -/
theorem finiteBranchPathWitnessInputsAt_xEast_of_nonemptyCodedRectangular
    (cWindow : ℕ) (ratioC : ℝ) (hC : 0 < ratioC)
    (h : Prop47Lemma411412XEastCanonicalNonemptyCodedRectangularInputs
      cWindow ratioC) :
    Prop47Lemma411412FiniteBranchPathWitnessInputsAt
      (xIndex east) 4 cWindow (categoricalOptimalRate ratioC) (1 / 4 : ℝ) := by
  have hbin := eventually_optimal_binomial_layer_above_quarter_log_sq
    ratioC hC
  filter_upwards [h, hbin, eventually_gt_atTop (0 : ℕ)] with
      m hm hbm hmpos
  intro r
  rcases hm r with ⟨D⟩
  exact D.finiteBranchWitness hmpos hC hbm

/-- The analogous direct two-phase temporal-column atomization. -/
theorem finiteBranchPathWitnessInputsAt_y_of_nonemptyCodedRectangular
    (cWindow : ℕ) (ratioC : ℝ) (hC : 0 < ratioC)
    (h : Prop47Lemma411412YCanonicalNonemptyCodedRectangularInputs
      cWindow ratioC) :
    Prop47Lemma411412FiniteBranchPathWitnessInputsAt
      yIndex 2 cWindow (categoricalOptimalRate ratioC) (1 / 4 : ℝ) := by
  have hbin := eventually_optimal_binomial_layer_above_quarter_log_sq
    ratioC hC
  filter_upwards [h, hbin] with m hm hbm
  intro r
  rcases hm r with ⟨D⟩
  exact D.finiteBranchWitness hC hbm

/-- Reflection of an already assembled two-phase `Y` path-witness input.
This formulation is independent of how its outer atoms were enumerated. -/
theorem finiteBranchPathWitnessAuxThetaInputsAt_yPrime_of_y_inputs
    (cWindow : ℕ) (c : ℝ)
    (h : Prop47Lemma411412FiniteBranchPathWitnessInputsAt
      yIndex 2 cWindow c (1 / 4 : ℝ)) :
    Prop47Lemma411412FiniteBranchPathWitnessAuxThetaInputsAt
      sourceEquation447ThetaTarget yIndex' 2 cWindow c (1 / 4 : ℝ) := by
  filter_upwards [h] with m hm
  intro r
  rcases hm r with
    ⟨branchFailure, rho, atoms, hcover, hthreshold, hatomCover, htheta,
      hdisjoint⟩
  let reflectedFailure : Fin 2 → Set Path :=
    fun j ↦ reflectPath ⁻¹' branchFailure j
  let reflectedAtoms : (j : Fin 2) → ℕ →
      StoppedEquation447PathWitnessBranchAtom cWindow m c
        (reflectedFailure j) (rho j) :=
    fun j n ↦ reflectStoppedEquation447PathWitnessBranchAtom (atoms j n)
  refine ⟨reflectedFailure, rho, reflectedAtoms, ?_, hthreshold,
    ?_, ?_, ?_⟩
  · intro s hs
    have hsource : reflectPath s ∈
        lemma411412CardinalityFailureEvent m yIndex r := by
      change s ∈ reflectPath ⁻¹'
        lemma411412CardinalityFailureEvent m yIndex r
      rw [lemma411412CardinalityFailureEvent_yPrime_preimage]
      exact hs
    rcases Set.mem_iUnion.mp (hcover hsource) with ⟨j, hj⟩
    exact Set.mem_iUnion.mpr ⟨j, hj⟩
  · intro j s hs
    have hsourceSupport : reflectPath s ∈
        HLOZSourceInstantiation.simpleRandomWalkSupport :=
      reflectPath_mem_simpleRandomWalkSupport hs.2
    rcases Set.mem_iUnion.mp
      (hatomCover j ⟨hs.1, hsourceSupport⟩) with ⟨n, hn⟩
    exact Set.mem_iUnion.mpr ⟨n, hn⟩
  · intro j n
    rw [sourceEquation447ThetaTarget_yPrime]
    exact Set.preimage_mono (htheta j n)
  · intro j n k hne
    rw [Set.disjoint_left]
    intro s hsn hsk
    exact Set.disjoint_left.1 (hdisjoint j hne) hsn hsk

/-- The two nonempty-fibre strict rectangular packages assemble all six
pairings directly.  The four X pairings are quarter-turns of X-east; the
two temporal phases are padded to four branches and reflected only after
their reunion. -/
theorem finiteBranchPathWitnessAuxThetaInputs_of_nonemptyCodedRectangular
    (cWindow : ℕ) (ratioC : ℝ) (hC : 0 < ratioC)
    (hX : Prop47Lemma411412XEastCanonicalNonemptyCodedRectangularInputs
      cWindow ratioC)
    (hY : Prop47Lemma411412YCanonicalNonemptyCodedRectangularInputs
      cWindow ratioC) :
    Prop47Lemma411412FiniteBranchPathWitnessAuxThetaInputs
      sourceEquation447ThetaTarget 4 cWindow
        (categoricalOptimalRate ratioC) (1 / 4 : ℝ) := by
  have hEast :=
    finiteBranchPathWitnessInputsAt_xEast_of_nonemptyCodedRectangular
      cWindow ratioC hC hX
  have hColumn :=
    finiteBranchPathWitnessInputsAt_y_of_nonemptyCodedRectangular
      cWindow ratioC hC hY
  apply finiteBranchPathWitnessAuxThetaInputs_of_allAt
    sourceEquation447ThetaTarget
  intro i
  fin_cases i
  · apply finiteBranchPathWitnessAuxThetaInputsAt_of_standard
    · intro m r
      simp [sourceEquation447ThetaTarget, yIndex']
    · convert finiteBranchPathWitnessInputsAt_x_of_east
        (0 : Dir) 4 cWindow (categoricalOptimalRate ratioC) (1 / 4 : ℝ)
          hEast using 1 <;>
        ext <;> norm_num [xIndex]
  · apply finiteBranchPathWitnessAuxThetaInputsAt_of_standard
    · intro m r
      simp [sourceEquation447ThetaTarget, yIndex']
    · convert finiteBranchPathWitnessInputsAt_x_of_east
        (1 : Dir) 4 cWindow (categoricalOptimalRate ratioC) (1 / 4 : ℝ)
          hEast using 1 <;>
        ext <;> norm_num [xIndex]
  · apply finiteBranchPathWitnessAuxThetaInputsAt_of_standard
    · intro m r
      simp [sourceEquation447ThetaTarget, yIndex']
    · convert finiteBranchPathWitnessInputsAt_x_of_east
        (2 : Dir) 4 cWindow (categoricalOptimalRate ratioC) (1 / 4 : ℝ)
          hEast using 1 <;>
        ext <;> norm_num [xIndex]
  · apply finiteBranchPathWitnessAuxThetaInputsAt_of_standard
    · intro m r
      simp [sourceEquation447ThetaTarget, yIndex']
    · convert finiteBranchPathWitnessInputsAt_x_of_east
        (3 : Dir) 4 cWindow (categoricalOptimalRate ratioC) (1 / 4 : ℝ)
          hEast using 1 <;>
        ext <;> norm_num [xIndex]
  · apply finiteBranchPathWitnessAuxThetaInputsAt_of_standard
    · exact sourceEquation447ThetaTarget_y
    · convert finiteBranchPathWitnessInputsAt_four_of_two
        yIndex cWindow (categoricalOptimalRate ratioC) (1 / 4 : ℝ)
          hColumn using 1 <;>
        ext <;> norm_num [yIndex]
  · convert finiteBranchPathWitnessAuxThetaInputsAt_four_of_two
      sourceEquation447ThetaTarget yIndex' cWindow
        (categoricalOptimalRate ratioC) (1 / 4 : ℝ)
        (finiteBranchPathWitnessAuxThetaInputsAt_yPrime_of_y_inputs
          cWindow (categoricalOptimalRate ratioC) hColumn) using 1 <;>
      ext <;> norm_num [yIndex']

end Erdos1166.HLOZLemma411412CodedAtoms
