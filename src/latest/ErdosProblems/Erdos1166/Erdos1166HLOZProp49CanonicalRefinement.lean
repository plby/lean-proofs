import ErdosProblems.Erdos1166.Erdos1166HLOZStoppedFullComplement
import ErdosProblems.Erdos1166.Erdos1166HLOZLemma410Prop48XDirections
import ErdosProblems.Erdos1166.Erdos1166HLOZProp47Lemma411412XDirections
import ErdosProblems.Erdos1166.Erdos1166HLOZColumnSourceConsumers

/-!
# Canonical ordered-history refinement for Proposition 4.9

The source conditions on the ordered level-creation sites.  Earlier
connectors therefore asked a caller to choose, and enumerate by hand, one
ordered creation tuple for every raw stopped atom.  This file removes that
bookkeeping premise.

For a fixed stage the type `Fin (stageNumber r) → Site` is countable.  We
use the canonical `Encodable.decode₂` enumeration of pairs consisting of a
raw-atom index and an ordered creation tuple.  Invalid natural-number codes
give the empty atom.  Valid codes give the raw atom intersected with that
ordered tuple and the complete preceding history.  The canonical coding is
injective on valid codes, so the resulting family is pairwise disjoint; it
covers every raw atom because the actual ordered tuple of a path has a
canonical code.
-/

namespace Erdos1166.HLOZProp49CanonicalRefinement

open Filter MeasureTheory Set
open scoped ENNReal
open HLOZProp47Parameters HLOZProp47SourceAssembly
open HLOZProp47SourceObjects HLOZProp47Canonical HLOZProp47HighEscape
open HLOZPairing HLOZPairingProfiles
open HLOZStoppedHistoryFactorization HLOZProp47LowStageConnector
open HLOZStoppedFullComplement
open HLOZProp47Prop45XRotations HLOZProp47Lemma411412XDirections
open HLOZLemma410Prop48XDirections
open HLOZProp47Prop45YColumns
open HLOZColumnSourceConsumers
open HLOZProp47Lemma411412XEastBridge
open HLOZLemma410Prop48Connector
open HLOZMixedCreationBlocks
open HLOZDecomposition

abbrev Path := ℕ → Site

/-- A quarter turn transports any measurable refined-atom estimate to the
inverse-image atom and screen.  This isolates the purely measure-preserving
part of the remaining first-stage checkerboard transports. -/
theorem refinedAtomScreenEstimate_preimage_orientPath
    (d : HLOZPairing.Dir) (atom screen : Set Path) (rate : ℝ≥0∞)
    (hatom : MeasurableSet atom) (hscreen : MeasurableSet screen)
    (hsource : RefinedAtomScreenEstimate atom screen rate) :
    RefinedAtomScreenEstimate
      (orientPath (rotationInverseDir d) ⁻¹' atom)
      (orientPath (rotationInverseDir d) ⁻¹' screen) rate := by
  rw [RefinedAtomScreenEstimate, ← Set.preimage_inter]
  rw [Measure.measure_preimage_of_map_eq_self
      (simpleRandomWalkLaw_map_orientPath (rotationInverseDir d))
      (hatom.inter hscreen).nullMeasurableSet]
  rw [Measure.measure_preimage_of_map_eq_self
      (simpleRandomWalkLaw_map_orientPath (rotationInverseDir d))
      hatom.nullMeasurableSet]
  exact hsource

@[simp] theorem sourceCanonicalProfiles_xIndex (d : Dir) :
    sourceCanonicalProfiles (xIndex d) =
      deletionProfilePair (xDeletion d) := by
  fin_cases d <;> rfl

@[simp] theorem canonicalCStar_xIndex (d : Dir) :
    canonicalCStar (xIndex d) = 10 := rfl

theorem siteDistance_orientSite (d : Dir) (x y : Site) :
    siteDistance (orientSite d x) (orientSite d y) = siteDistance x y := by
  unfold siteDistance
  rw [HLOZLemma410Prop48XDirections.siteSquaredDistance_orientSite]

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

theorem stoppedThetaSites_empty_x_orient_iff
    (d : Dir) (s : Path) (m k : ℕ) (cStar : ℝ) :
    stoppedThetaSites (deletionProfilePair (xDeletion east)) cStar s m k = ∅ ↔
      stoppedThetaSites (deletionProfilePair (xDeletion d)) cStar
        (orientPath d s) m k = ∅ := by
  have h := stoppedThetaEvent_x_orient_iff d cStar s m k
  simpa only [stoppedThetaEvent, Set.mem_setOf_eq,
    Finset.not_nonempty_iff_eq_empty] using not_congr h

theorem lowScaleStageEvent_x_orient_iff
    (d : Dir) (s : Path) (m k : ℕ) (alpha : ℝ) :
    s ∈ lowScaleStageEvent (sourceCanonicalProfiles (xIndex east))
        (canonicalCStar (xIndex east)) (xIndex east) m k alpha ↔
      orientPath d s ∈
        lowScaleStageEvent (sourceCanonicalProfiles (xIndex d))
          (canonicalCStar (xIndex d)) (xIndex d) m k alpha := by
  simp only [lowScaleStageEvent, Set.mem_inter_iff, Set.mem_setOf_eq,
    sourceCanonicalProfiles_xIndex, canonicalCStar_xIndex]
  rw [hlozDirectAvoidanceEvent_x_orient_iff,
    distanceBinEvent_x_orient_iff,
    nextCreationIsCandidateEvent_x_orient_iff,
    stoppedThetaSites_empty_x_orient_iff,
    nearFavoriteSites_x_orient_card]

theorem prop47StageEvent_x_orient_iff
    (d : Dir) (s : Path) (m : ℕ) (r : StageIndex) (alpha : ℝ) :
    s ∈ prop47StageEvent sourceCanonicalProfiles canonicalCStar
        (xIndex east) m r alpha ↔
      orientPath d s ∈ prop47StageEvent sourceCanonicalProfiles
        canonicalCStar (xIndex d) m r alpha := by
  rw [prop47StageEvent, prop47StageEvent]
  refine and_congr (prefixPairingEvent_x_orient_iff
    d s m (stageNumber r + 1)) ?_
  by_cases hAlpha : alpha ≤ kappaTwo
  · simp only [hAlpha, if_true]
    exact lowScaleStageEvent_x_orient_iff
      d s m (stageNumber r) alpha
  · simp only [hAlpha, if_false, Set.mem_inter_iff]
    exact and_congr
      (hlozDirectAvoidanceEvent_x_orient_iff
        d s m (stageNumber r + 1))
      (distanceBinEvent_x_orient_iff d s m (stageNumber r) alpha)

theorem prop47History_x_orient_iff
    (d : Dir) (s : Path) (m : ℕ) (a : AlphaTriple) (n : ℕ) :
    s ∈ prop47History sourceCanonicalProfiles canonicalCStar
        m (xIndex east) a n ↔
      orientPath d s ∈ prop47History sourceCanonicalProfiles
        canonicalCStar m (xIndex d) a n := by
  induction n with
  | zero =>
      exact prefixPairingEvent_x_orient_iff d s m 1
  | succ n ih =>
      change
        (s ∈ prop47History sourceCanonicalProfiles canonicalCStar
            m (xIndex east) a n ∧
          s ∈ if h : n < 3 then
            prop47StageEvent sourceCanonicalProfiles canonicalCStar
              (xIndex east) m ⟨n, h⟩
                (alphaValue (tripleAlphaIndex a ⟨n, h⟩))
          else Set.univ) ↔
        (orientPath d s ∈ prop47History sourceCanonicalProfiles
            canonicalCStar m (xIndex d) a n ∧
          orientPath d s ∈ if h : n < 3 then
            prop47StageEvent sourceCanonicalProfiles canonicalCStar
              (xIndex d) m ⟨n, h⟩
                (alphaValue (tripleAlphaIndex a ⟨n, h⟩))
          else Set.univ)
      refine and_congr ih ?_
      by_cases hn : n < 3
      · simp only [hn, dite_true]
        exact prop47StageEvent_x_orient_iff d s m ⟨n, hn⟩
          (alphaValue (tripleAlphaIndex a ⟨n, hn⟩))
      · simp only [hn, dite_false, Set.mem_univ]

def rotateCreationTuple (d : Dir) {k : ℕ} (c : Fin k → Site) :
    Fin k → Site := fun j ↦ orientSite (rotationInverseDir d) (c j)

theorem orderedProfileHistoryEvent_x_orient_iff
    (d : Dir) (m : ℕ) (a : AlphaTriple) (r : StageIndex)
    (c : Fin (stageNumber r) → Site) (s : Path) :
    s ∈ orderedProfileHistoryEvent sourceCanonicalProfiles canonicalCStar
        m (xIndex d) a r c ↔
      orientPath (rotationInverseDir d) s ∈
        orderedProfileHistoryEvent sourceCanonicalProfiles canonicalCStar
          m (xIndex east) a r (rotateCreationTuple d c) := by
  let g := orientPath (rotationInverseDir d)
  have hordered :
      s ∈ orderedCreationSitesEvent m (stageNumber r) c ↔
        g s ∈ orderedCreationSitesEvent m (stageNumber r)
          (rotateCreationTuple d c) := by
    constructor
    · intro hs
      unfold orderedCreationSitesEvent at hs ⊢
      funext j
      change levelCreationSite (g s) m (j.1 + 1) = _
      rw [show g s = orientPath (rotationInverseDir d) s by rfl,
        levelCreationSite_orientPath]
      have hsj := congrFun hs j
      change levelCreationSite s m (j.1 + 1) = c j at hsj
      rw [hsj]
      rfl
    · intro hs
      unfold orderedCreationSitesEvent at hs ⊢
      funext j
      apply orientSite_injective (rotationInverseDir d)
      calc
        orientSite (rotationInverseDir d)
            (levelCreationSite s m (j.1 + 1)) =
            levelCreationSite (g s) m (j.1 + 1) := by
              rw [show g s = orientPath (rotationInverseDir d) s by rfl,
                levelCreationSite_orientPath]
        _ = rotateCreationTuple d c j := congrFun hs j
        _ = orientSite (rotationInverseDir d) (c j) := rfl
  have hhistory := prop47History_x_orient_iff
    d (g s) m a r.1
  change
    (s ∈ orderedCreationSitesEvent m (stageNumber r) c ∧
        s ∈ prop47History sourceCanonicalProfiles canonicalCStar
          m (xIndex d) a r.1) ↔
      (g s ∈ orderedCreationSitesEvent m (stageNumber r)
          (rotateCreationTuple d c) ∧
        g s ∈ prop47History sourceCanonicalProfiles canonicalCStar
          m (xIndex east) a r.1)
  simpa only [g, orientPath_rotationInverseDir_right] using
    and_congr hordered hhistory.symm

theorem orderedProfileHistoryPathAtom_x_rotate
    (d : Dir) (m : ℕ) (a : AlphaTriple) (r : StageIndex)
    (c : Fin (stageNumber r) → Site) (baseAtom : Set Path) :
    orderedProfileHistoryPathAtom sourceCanonicalProfiles canonicalCStar
        m (xIndex d) a r c
          (orientPath (rotationInverseDir d) ⁻¹' baseAtom) =
      orientPath (rotationInverseDir d) ⁻¹'
        orderedProfileHistoryPathAtom sourceCanonicalProfiles canonicalCStar
          m (xIndex east) a r (rotateCreationTuple d c) baseAtom := by
  ext s
  exact and_congr_right fun _ ↦
    orderedProfileHistoryEvent_x_orient_iff d m a r c s

theorem ConcreteStoppedProp49AtomData.m_pos
    {m k A : ℕ} {alpha : ℝ} {screen : Set Path}
    (D : ConcreteStoppedProp49AtomData m k A alpha screen) : 0 < m := by
  cases D with
  | unprimedEvenLeft data => exact data.m_pos
  | primedOddStrictRight data => exact data.m_pos
  | unprimedOddTerminalTieLeft data => exact data.m_pos
  | primedEvenTerminalStrictRight data => exact data.m_pos

theorem ConcreteStoppedProp49AtomData.measurableSet_atom
    {m k A : ℕ} {alpha : ℝ} {screen : Set Path}
    (D : ConcreteStoppedProp49AtomData m k A alpha screen) :
    MeasurableSet D.atom := by
  cases D with
  | unprimedEvenLeft data => exact data.toInput.measurable_atom
  | primedOddStrictRight data => exact data.toInput.measurable_atom
  | unprimedOddTerminalTieLeft data => exact data.toInput.measurable_atom
  | primedEvenTerminalStrictRight data => exact data.toInput.measurable_atom

/-- The stronger history-refined product-law interface remains an immediate
constructor for the literal local Proposition-4.9 estimate used below. -/
theorem ConcreteStoppedProp49RefinedAtomMapLaw.toScreenEstimate
    {m k A : ℕ} {alpha : ℝ} {screen refinedAtom : Set Path}
    {D : ConcreteStoppedProp49AtomData m k A alpha screen}
    (F : ConcreteStoppedProp49RefinedAtomMapLaw refinedAtom D) :
    RefinedAtomScreenEstimate refinedAtom screen
      (sourceProp49ScreenRate m A alpha) := by
  rw [RefinedAtomScreenEstimate]
  exact F.screen_measure_le

/-- Transport a literal X-east history-refined Proposition-4.9 estimate to
any checkerboard orientation.  This is the source-faithful direct route; the
full-complement theorem below is a sufficient way to construct its `heast`
premise, but is not required by this transport. -/
theorem xProp49_rotated_screenEstimate
    (d : Dir) {m A : ℕ} {alpha : ℝ} {eastScreen : Set Path}
    {a : AlphaTriple} {r : StageIndex}
    (D : ConcreteStoppedProp49AtomData
      m (stageNumber r) A alpha eastScreen)
    (c : Fin (stageNumber r) → Site)
    (hscreen : MeasurableSet eastScreen)
    (heast : RefinedAtomScreenEstimate
      (orderedProfileHistoryPathAtom sourceCanonicalProfiles canonicalCStar
        m (xIndex east) a r (rotateCreationTuple d c) D.atom)
      eastScreen (sourceProp49ScreenRate m A alpha)) :
    RefinedAtomScreenEstimate
      (orderedProfileHistoryPathAtom sourceCanonicalProfiles canonicalCStar
        m (xIndex d) a r c
          (orientPath (rotationInverseDir d) ⁻¹' D.atom))
      (orientPath (rotationInverseDir d) ⁻¹' eastScreen)
      (sourceProp49ScreenRate m A alpha) := by
  have hmeasurable : MeasurableSet
      (orderedProfileHistoryPathAtom sourceCanonicalProfiles canonicalCStar
        m (xIndex east) a r (rotateCreationTuple d c) D.atom) :=
    measurableSet_orderedProfileHistoryPathAtom sourceCanonicalProfiles
      sourceCanonicalProfiles_oneStepAdapted canonicalCStar m (xIndex east)
        a r (rotateCreationTuple d c) D.atom
          (Erdos1166.HLOZProp49CanonicalRefinement.ConcreteStoppedProp49AtomData.m_pos D)
          (Erdos1166.HLOZProp49CanonicalRefinement.ConcreteStoppedProp49AtomData.measurableSet_atom D)
  rw [orderedProfileHistoryPathAtom_x_rotate]
  exact refinedAtomScreenEstimate_preimage_orientPath d _ _ _
    hmeasurable hscreen heast

/-- All four checkerboard rotations inherit the history-refined coordinate
tail once the literal X-east chronological complement determines the rotated
ordered history. -/
theorem xProp49_rotated_fullComplement_screenEstimate
    (d : Dir) {m A : ℕ} {alpha : ℝ} {eastScreen : Set Path}
    {a : AlphaTriple} {r : StageIndex}
    (D : ConcreteStoppedProp49AtomData
      m (stageNumber r) A alpha eastScreen)
    (c : Fin (stageNumber r) → Site)
    (hscreen : MeasurableSet eastScreen)
    (hdet :
      HLOZStoppedFullComplement.ConcreteStoppedProp49AtomData.FullComplementHistoryDetermined
        D (profiles := sourceCanonicalProfiles) (cStar := canonicalCStar)
          (i := xIndex east) (a := a) (r := r)
            (rotateCreationTuple d c)) :
    RefinedAtomScreenEstimate
      (orderedProfileHistoryPathAtom sourceCanonicalProfiles canonicalCStar
        m (xIndex d) a r c
          (orientPath (rotationInverseDir d) ⁻¹' D.atom))
      (orientPath (rotationInverseDir d) ⁻¹' eastScreen)
      (sourceProp49ScreenRate m A alpha) := by
  have heast :=
    HLOZStoppedFullComplement.ConcreteStoppedProp49AtomData.fullComplement_orderedProfileHistory_screenEstimate
      (profiles := sourceCanonicalProfiles) (cStar := canonicalCStar)
      (i := xIndex east) (a := a) (r := r) D
        (rotateCreationTuple d c) hdet
  exact xProp49_rotated_screenEstimate d D c hscreen heast

def rotateStageZeroCreationTuple (d : Dir) (c : Fin 1 → Site) :
    Fin 1 → Site := rotateCreationTuple d c

theorem orderedProfileHistoryEvent_zero_x_orient_iff
    (profiles : Fin 6 → ExternalProfilePair) (cStar : Fin 6 → ℝ)
    (d : Dir) (m : ℕ) (a : AlphaTriple) (c : Fin 1 → Site)
    (s : Path) :
    s ∈ orderedProfileHistoryEvent profiles cStar m (xIndex d) a 0 c ↔
      orientPath (rotationInverseDir d) s ∈
        orderedProfileHistoryEvent profiles cStar m (xIndex east) a 0
          (rotateStageZeroCreationTuple d c) := by
  let g := orientPath (rotationInverseDir d)
  have hordered :
      s ∈ orderedCreationSitesEvent m 1 c ↔
        g s ∈ orderedCreationSitesEvent m 1
          (rotateStageZeroCreationTuple d c) := by
    constructor
    · intro hs
      unfold orderedCreationSitesEvent at hs ⊢
      funext j
      change levelCreationSite (g s) m (j.1 + 1) = _
      rw [show g s = orientPath (rotationInverseDir d) s by rfl,
        levelCreationSite_orientPath]
      have hsj := congrFun hs j
      change levelCreationSite s m (j.1 + 1) = c j at hsj
      rw [hsj]
      rfl
    · intro hs
      unfold orderedCreationSitesEvent at hs ⊢
      funext j
      apply orientSite_injective (rotationInverseDir d)
      calc
        orientSite (rotationInverseDir d)
            (levelCreationSite s m (j.1 + 1)) =
            levelCreationSite (g s) m (j.1 + 1) := by
              rw [show g s = orientPath (rotationInverseDir d) s by rfl,
                levelCreationSite_orientPath]
        _ = rotateStageZeroCreationTuple d c j := congrFun hs j
        _ = orientSite (rotationInverseDir d) (c j) := rfl
  have hprefix :
      s ∈ prefixPairingEvent m (xIndex d) 1 ↔
        g s ∈ prefixPairingEvent m (xIndex east) 1 := by
    have h := prefixPairingEvent_x_orient_iff d (g s) m 1
    simpa only [g, orientPath_rotationInverseDir_right] using h.symm
  change
    (s ∈ orderedCreationSitesEvent m 1 c ∩
        prop47History profiles cStar m (xIndex d) a 0) ↔
      g s ∈ orderedCreationSitesEvent m 1
          (rotateStageZeroCreationTuple d c) ∩
        prop47History profiles cStar m (xIndex east) a 0
  rw [prop47History_zero, prop47History_zero]
  exact and_congr hordered hprefix

theorem orderedProfileHistoryPathAtom_zero_x_rotate
    (profiles : Fin 6 → ExternalProfilePair) (cStar : Fin 6 → ℝ)
    (d : Dir) (m : ℕ) (a : AlphaTriple) (c : Fin 1 → Site)
    (baseAtom : Set Path) :
    orderedProfileHistoryPathAtom profiles cStar m (xIndex d) a 0 c
        (orientPath (rotationInverseDir d) ⁻¹' baseAtom) =
      orientPath (rotationInverseDir d) ⁻¹'
        orderedProfileHistoryPathAtom profiles cStar m (xIndex east) a 0
          (rotateStageZeroCreationTuple d c) baseAtom := by
  ext s
  exact and_congr_right fun _ ↦
    orderedProfileHistoryEvent_zero_x_orient_iff
      profiles cStar d m a c s

/-- All four checkerboard rotations of a literal first-stage atom inherit
the checked X-east narrow-band estimate.  Only the deterministic atom/screen
identifications remain for a source connector. -/
theorem xStageZeroProp49_rotated_screenEstimate
    (d : Dir) {m A : ℕ} {alpha : ℝ} {eastScreen : Set Path}
    {a : AlphaTriple}
    (D : XEastStageZeroProp49AtomData m A alpha eastScreen)
    (c : Fin 1 → Site) (hscreen : MeasurableSet eastScreen) :
    RefinedAtomScreenEstimate
      (orderedProfileHistoryPathAtom sourceCanonicalProfiles canonicalCStar
        m (xIndex d) a 0 c
          (orientPath (rotationInverseDir d) ⁻¹' D.atom))
      (orientPath (rotationInverseDir d) ⁻¹' eastScreen)
      (sourceProp49ScreenRate m A alpha) := by
  have heast := XEastStageZeroProp49AtomData.screenEstimate
    (profiles := sourceCanonicalProfiles) (cStar := canonicalCStar)
    (a := a) D (rotateStageZeroCreationTuple d c)
  have hmeasurable : MeasurableSet
      (orderedProfileHistoryPathAtom sourceCanonicalProfiles canonicalCStar
        m (xIndex east) a 0 (rotateStageZeroCreationTuple d c) D.atom) :=
    measurableSet_orderedProfileHistoryPathAtom sourceCanonicalProfiles
      sourceCanonicalProfiles_oneStepAdapted canonicalCStar m (xIndex east)
        a 0 (rotateStageZeroCreationTuple d c) D.atom D.m_pos
          D.measurableSet_atom
  rw [orderedProfileHistoryPathAtom_zero_x_rotate]
  exact refinedAtomScreenEstimate_preimage_orientPath d _ _ _
    hmeasurable hscreen heast

/-! ### First-stage column atoms

For the first column stage, the preceding history is just the threshold
and the column pairing condition.  Once the literal terminal atom fixes
the singleton creation set, every nonempty ordered refinement is therefore
the whole terminal atom.  This lets the already checked conditional
terminal law supply the unnormalised refined-atom estimate directly; no
history-independence premise is needed. -/

/-- A conditional screen estimate on a measurable atom implies its
unnormalised form.  The zero-mass case is handled separately, so this
statement does not hide a positivity premise. -/
theorem refinedAtomScreenEstimate_of_conditional
    (atom screen : Set Path) (rate : ℝ≥0∞)
    (hatom : MeasurableSet atom)
    (hcond : (ProbabilityTheory.cond simpleRandomWalkLaw atom)
      (atom ∩ screen) ≤ rate) :
    RefinedAtomScreenEstimate atom screen rate := by
  have hinter : atom ∩ (atom ∩ screen) = atom ∩ screen := by
    ext s
    simp only [Set.mem_inter_iff]
    tauto
  rw [ProbabilityTheory.cond_apply hatom, hinter] at hcond
  by_cases hzero : simpleRandomWalkLaw atom = 0
  · have hnumzero : simpleRandomWalkLaw (atom ∩ screen) = 0 :=
      measure_mono_null Set.inter_subset_left hzero
    simp only [RefinedAtomScreenEstimate, hnumzero, hzero, mul_zero, le_refl]
  · have htop : simpleRandomWalkLaw atom ≠ ∞ :=
      measure_ne_top simpleRandomWalkLaw atom
    calc
      simpleRandomWalkLaw (atom ∩ screen) =
          simpleRandomWalkLaw atom *
            ((simpleRandomWalkLaw atom)⁻¹ *
              simpleRandomWalkLaw (atom ∩ screen)) := by
        rw [← mul_assoc, ENNReal.mul_inv_cancel hzero htop, one_mul]
      _ ≤ simpleRandomWalkLaw atom * rate := by gcongr
      _ = rate * simpleRandomWalkLaw atom := mul_comm _ _

/-- If an event is constant on an atom and the refined atom is nonempty,
then the refinement equals the whole atom. -/
theorem inter_eq_left_of_eventDeterminedByOn_of_nonempty
    {Z : Type*} (atom event : Set Path) (z : Path → Z)
    (hdet : EventDeterminedByOn atom event z)
    (hz : ∀ s t, z s = z t)
    (hnonempty : (atom ∩ event).Nonempty) :
    atom ∩ event = atom := by
  apply Set.inter_eq_left.mpr
  intro s hs
  rcases hnonempty with ⟨t, htAtom, htEvent⟩
  exact (hdet s hs t htAtom (hz s t)).2 htEvent

/-- Literal forward-terminal data sufficient to close Proposition 4.9 at
the first `Y` stage.  The remaining extra fields are deterministic source
identifications: the terminal atom really is a one-creation threshold atom
and its creation set is free for the `Y` pairing. -/
structure ForwardColumnStageZeroProp49AtomData
    (m A : ℕ) (alpha : ℝ) (screen : Set Path) where
  data : ForwardColumnProp49AtomData m A alpha screen
  m_pos : 0 < m
  stage_eq : data.source.k = 1
  threshold : data.source.pathAtom ⊆ hlozThresholdTimeEventK m 1
  creation_fixed : ∀ s ∈ data.source.pathAtom,
    levelCreationSitesUpTo s m 1 = data.source.creationSet
  creation_pairFree : PairFree YPair data.source.creationSet

/-- The independently conditioned backward terminal phase of the same
first-stage `Y` atom. -/
structure PrimedColumnStageZeroProp49AtomData
    (m A : ℕ) (alpha : ℝ) (screen : Set Path) where
  data : PrimedColumnProp49AtomData m A alpha screen
  m_pos : 0 < m
  stage_eq : data.source.k = 1
  threshold : data.source.pathAtom ⊆ hlozThresholdTimeEventK m 1
  creation_fixed : ∀ s ∈ data.source.pathAtom,
    levelCreationSitesUpTo s m 1 = data.source.creationSet
  creation_pairFree : PairFree YPair data.source.creationSet

/-- The two terminal phases are alternatives inside one literal `Y`
stage-zero source atom.  They are not identified with `Y` and `Y'`. -/
inductive YStageZeroProp49AtomData
    (m A : ℕ) (alpha : ℝ) (screen : Set Path) where
  | forward (data : ForwardColumnStageZeroProp49AtomData m A alpha screen)
  | primed (data : PrimedColumnStageZeroProp49AtomData m A alpha screen)

noncomputable def YStageZeroProp49AtomData.atom
    {m A : ℕ} {alpha : ℝ} {screen : Set Path}
    (D : YStageZeroProp49AtomData m A alpha screen) : Set Path :=
  match D with
  | .forward data => data.data.source.pathAtom
  | .primed data => data.data.source.pathAtom

theorem YStageZeroProp49AtomData.measurableSet_atom
    {m A : ℕ} {alpha : ℝ} {screen : Set Path}
    (D : YStageZeroProp49AtomData m A alpha screen) :
    MeasurableSet D.atom := by
  cases D with
  | forward data => exact data.data.source.measurableSet_pathAtom
  | primed data => exact data.data.source.measurableSet_pathAtom

theorem YStageZeroProp49AtomData.m_pos
    {m A : ℕ} {alpha : ℝ} {screen : Set Path}
    (D : YStageZeroProp49AtomData m A alpha screen) : 0 < m := by
  cases D with
  | forward data => exact data.m_pos
  | primed data => exact data.m_pos

/-- Every nonempty ordered refinement of a literal first-stage column atom
inherits the checked terminal narrow-band estimate. -/
theorem YStageZeroProp49AtomData.screenEstimate
    {m A : ℕ} {alpha : ℝ} {screen : Set Path}
    {profiles : Fin 6 → ExternalProfilePair} {cStar : Fin 6 → ℝ}
    {a : AlphaTriple}
    (D : YStageZeroProp49AtomData m A alpha screen)
    (c : Fin 1 → Site)
    (hnonempty :
      (orderedProfileHistoryPathAtom profiles cStar m yIndex a 0 c
        D.atom).Nonempty) :
    RefinedAtomScreenEstimate
      (orderedProfileHistoryPathAtom profiles cStar m yIndex a 0 c D.atom)
      screen (sourceProp49ScreenRate m A alpha) := by
  cases D with
  | forward data =>
      have hdet : EventDeterminedByOn data.data.source.pathAtom
          (orderedProfileHistoryEvent profiles cStar m yIndex a 0 c)
          (fun _ : Path ↦ false) := by
        apply eventDeterminedByOn_orderedProfileHistoryEvent_zero_of_fixed_source
          data.data.source.pathAtom (fun _ : Path ↦ false)
          profiles cStar m yIndex a data.data.source.creationSet c
          data.threshold data.creation_fixed
        simpa using data.creation_pairFree
      have heq : orderedProfileHistoryPathAtom profiles cStar m yIndex a 0 c
            data.data.source.pathAtom = data.data.source.pathAtom := by
        exact inter_eq_left_of_eventDeterminedByOn_of_nonempty
          data.data.source.pathAtom
          (orderedProfileHistoryEvent profiles cStar m yIndex a 0 c)
          (fun _ : Path ↦ false) hdet (fun _ _ ↦ rfl) hnonempty
      have hraw : RefinedAtomScreenEstimate data.data.source.pathAtom screen
          (sourceProp49ScreenRate m A alpha) :=
        refinedAtomScreenEstimate_of_conditional
          data.data.source.pathAtom screen
          (sourceProp49ScreenRate m A alpha)
          data.data.source.measurableSet_pathAtom
          data.data.conditional_screen_le
      simpa only [YStageZeroProp49AtomData.atom, stageNumber, heq] using hraw
  | primed data =>
      have hdet : EventDeterminedByOn data.data.source.pathAtom
          (orderedProfileHistoryEvent profiles cStar m yIndex a 0 c)
          (fun _ : Path ↦ false) := by
        apply eventDeterminedByOn_orderedProfileHistoryEvent_zero_of_fixed_source
          data.data.source.pathAtom (fun _ : Path ↦ false)
          profiles cStar m yIndex a data.data.source.creationSet c
          data.threshold data.creation_fixed
        simpa using data.creation_pairFree
      have heq : orderedProfileHistoryPathAtom profiles cStar m yIndex a 0 c
            data.data.source.pathAtom = data.data.source.pathAtom := by
        exact inter_eq_left_of_eventDeterminedByOn_of_nonempty
          data.data.source.pathAtom
          (orderedProfileHistoryEvent profiles cStar m yIndex a 0 c)
          (fun _ : Path ↦ false) hdet (fun _ _ ↦ rfl) hnonempty
      have hraw : RefinedAtomScreenEstimate data.data.source.pathAtom screen
          (sourceProp49ScreenRate m A alpha) :=
        refinedAtomScreenEstimate_of_conditional
          data.data.source.pathAtom screen
          (sourceProp49ScreenRate m A alpha)
          data.data.source.measurableSet_pathAtom
          data.data.conditional_screen_le
      simpa only [YStageZeroProp49AtomData.atom, stageNumber, heq] using hraw

/-- Literal source data for a genuinely later unreflected `Y` column atom.

The forward and backward terminal parsers have different coordinate types,
so the dependent sum keeps the checked coarse stopped input attached to its
history data.  The source may provide the literal unnormalized local estimate
from Proposition 4.9.  Alternatively it may prove that the full chronological
complement determines the ordered source history on the coarse atom; the
profile-generic checked three-factor law then derives that same estimate.
Neither alternative assumes an exact product law after conditioning on the
whole preceding history. -/
inductive YLaterStageProp49AtomData
    (m A : ℕ) (alpha : ℝ) (screen : Set Path)
    (a : AlphaTriple) (r : StageIndex)
    (c : Fin (stageNumber r) → Site) where
  | forward
      (data : ForwardColumnProp49AtomData m A alpha screen)
      (estimate : RefinedAtomScreenEstimate
        (orderedProfileHistoryPathAtom sourceCanonicalProfiles canonicalCStar
          m yIndex a r c data.source.pathAtom)
        screen (sourceProp49ScreenRate m A alpha))
  | primed
      (data : PrimedColumnProp49AtomData m A alpha screen)
      (estimate : RefinedAtomScreenEstimate
        (orderedProfileHistoryPathAtom sourceCanonicalProfiles canonicalCStar
          m yIndex a r c data.source.pathAtom)
        screen (sourceProp49ScreenRate m A alpha))
  | forwardFullComplement
      (data : ForwardColumnProp49AtomData m A alpha screen)
      (history_determined : EventDeterminedByOn data.source.pathAtom
        (orderedProfileHistoryEvent sourceCanonicalProfiles canonicalCStar
          m yIndex a r c)
        (HLOZColumnFullComplement.forwardTerminalFullComplementPath
          data.source.clock data.source.creationSet data.source.activeBases))
  | primedFullComplement
      (data : PrimedColumnProp49AtomData m A alpha screen)
      (history_determined : EventDeterminedByOn data.source.pathAtom
        (orderedProfileHistoryEvent sourceCanonicalProfiles canonicalCStar
          m yIndex a r c)
        (HLOZColumnFullComplement.primedTerminalFullComplementPath
          data.source.clock data.source.creationSet data.source.activeBases))

noncomputable def YLaterStageProp49AtomData.atom
    {m A : ℕ} {alpha : ℝ} {screen : Set Path}
    {a : AlphaTriple} {r : StageIndex}
    {c : Fin (stageNumber r) → Site}
    (D : YLaterStageProp49AtomData m A alpha screen a r c) : Set Path :=
  match D with
  | .forward data _ => data.source.pathAtom
  | .primed data _ => data.source.pathAtom
  | .forwardFullComplement data _ => data.source.pathAtom
  | .primedFullComplement data _ => data.source.pathAtom

theorem YLaterStageProp49AtomData.measurableSet_atom
    {m A : ℕ} {alpha : ℝ} {screen : Set Path}
    {a : AlphaTriple} {r : StageIndex}
    {c : Fin (stageNumber r) → Site}
    (D : YLaterStageProp49AtomData m A alpha screen a r c) :
    MeasurableSet D.atom := by
  cases D with
  | forward data _ => exact data.source.measurableSet_pathAtom
  | primed data _ => exact data.source.measurableSet_pathAtom
  | forwardFullComplement data _ => exact data.source.measurableSet_pathAtom
  | primedFullComplement data _ => exact data.source.measurableSet_pathAtom

/-- The literal history-conditioned Proposition-4.9 input is already in the
exact unnormalized shape consumed by the canonical finite-branch connector. -/
theorem YLaterStageProp49AtomData.screenEstimate
    {m A : ℕ} {alpha : ℝ} {screen : Set Path}
    {a : AlphaTriple} {r : StageIndex}
    {c : Fin (stageNumber r) → Site}
    (D : YLaterStageProp49AtomData m A alpha screen a r c) :
    RefinedAtomScreenEstimate
      (orderedProfileHistoryPathAtom sourceCanonicalProfiles canonicalCStar
        m yIndex a r c D.atom)
      screen (sourceProp49ScreenRate m A alpha) := by
  cases D with
  | forward data estimate => exact estimate
  | primed data estimate => exact estimate
  | forwardFullComplement data history_determined =>
      exact
        data.fullComplement_orderedProfileHistory_screenEstimate_of_fiberwise
          sourceCanonicalProfiles canonicalCStar c history_determined
  | primedFullComplement data history_determined =>
      exact
        data.fullComplement_orderedProfileHistory_screenEstimate_of_fiberwise
          sourceCanonicalProfiles canonicalCStar c history_determined

/-- Reflection transports a checked coarse Proposition-4.9 atom, including
its stopped statistic, to the reflected path atom and screen.  This is only
the coarse law: a later `Y'` history is deliberately *not* identified with
the reflected `Y` history. -/
noncomputable def reflectedStoppedTruncatedProp49AtomInput
    {ι : Type*} [Fintype ι]
    {m k A : ℕ} {alpha : ℝ} {screen : Set Path}
    (D : @StoppedTruncatedProp49AtomInput ι _ m k A alpha screen) :
    @StoppedTruncatedProp49AtomInput ι _ m k A alpha
      (reflectPath ⁻¹' screen) where
  atom := reflectPath ⁻¹' D.atom
  measurable_atom := D.measurable_atom.preimage measurable_reflectPath
  lazyVector := fun s ↦ D.lazyVector (reflectPath s)
  nextDirection := fun s ↦ D.nextDirection (reflectPath s)
  profile := D.profile
  profile_lt := D.profile_lt
  measurable_joint := D.measurable_joint.comp measurable_reflectPath
  map_law := by
    let statistic : Path → ((ι → ℕ) × Direction) :=
      fun s ↦ (D.lazyVector s, D.nextDirection s)
    have hstat : Measurable statistic := D.measurable_joint
    ext B hB
    change ((simpleRandomWalkLaw.restrict (reflectPath ⁻¹' D.atom)).map
        (statistic ∘ reflectPath)) B = _
    have hpre :
        (statistic ∘ reflectPath) ⁻¹' B ∩
            reflectPath ⁻¹' D.atom =
          reflectPath ⁻¹' (statistic ⁻¹' B ∩ D.atom) := by
      ext s
      rfl
    rw [Measure.map_apply (hstat.comp measurable_reflectPath) hB]
    rw [Measure.restrict_apply (hB.preimage
      (hstat.comp measurable_reflectPath))]
    rw [hpre, simpleRandomWalkLaw_reflectPath_preimage _
      ((hB.preimage hstat).inter D.measurable_atom)]
    rw [← Measure.restrict_apply (hB.preimage hstat)]
    rw [← Measure.map_apply hstat hB, D.map_law]
    rw [Measure.smul_apply, Measure.smul_apply, smul_eq_mul,
      smul_eq_mul]
    rw [simpleRandomWalkLaw_reflectPath_preimage D.atom
      D.measurable_atom]
  candidate := D.candidate
  narrowBand := D.narrowBand
  narrowBand_measurable := D.narrowBand_measurable
  candidate_card := D.candidate_card
  coordinate_bound := D.coordinate_bound
  screen_subset := by
    intro s hs
    have hs' := D.screen_subset hs
    exact hs'

/-- The reflected forward terminal law retains the full chronological
complement.  Thus an actual `Y'` history may be handled by a fibre condition
on that reflected complement, without identifying it with the `Y` history. -/
theorem ForwardColumnProp49AtomData.reflectedFullComplement_orderedProfileHistory_screenEstimate_of_fiberwise
    {m A : ℕ} {alpha : ℝ} {screen : Set Path}
    (profiles : Fin 6 → ExternalProfilePair) (cStar : Fin 6 → ℝ)
    {i : Fin 6} {a : AlphaTriple} {r : StageIndex}
    (D : ForwardColumnProp49AtomData m A alpha screen)
    (c : Fin (stageNumber r) → Site)
    (hdet : EventDeterminedByOn (reflectPath ⁻¹' D.source.pathAtom)
      (orderedProfileHistoryEvent profiles cStar m i a r c)
      (HLOZColumnFullComplement.forwardTerminalFullComplementPath
        D.source.clock D.source.creationSet D.source.activeBases ∘
          reflectPath)) :
    RefinedAtomScreenEstimate
      (orderedProfileHistoryPathAtom profiles cStar m i a r c
        (reflectPath ⁻¹' D.source.pathAtom))
      (reflectPath ⁻¹' screen) (sourceProp49ScreenRate m A alpha) := by
  let RD := reflectedStoppedTruncatedProp49AtomInput D.toInput
  let complementLaw :=
    HLOZColumnFullComplement.columnMixedComplementRunMeasure
      D.source.clock.baseAt m D.source.creationSet D.source.activeBases
        D.source.externalLeft D.source.externalRight
  let z := HLOZColumnFullComplement.forwardTerminalFullComplementPath
    D.source.clock D.source.creationSet D.source.activeBases ∘ reflectPath
  apply refinedAtomScreenEstimate_of_joint_complement_determined
    RD complementLaw z
  · exact
      (HLOZColumnFullComplement.measurable_forwardTerminalFullComplementPath
        D.source.clock D.source.creationSet D.source.activeBases).comp
          measurable_reflectPath
  · exact MeasurableSet.of_discrete
  · exact hdet
  · let f := fun s ↦
        ((D.source.lazyVector s, D.source.nextDirection s),
          HLOZColumnFullComplement.forwardTerminalFullComplementPath
            D.source.clock D.source.creationSet D.source.activeBases s)
    have hf : Measurable f :=
      (D.source.measurable_lazyVector.prodMk
        D.source.measurable_nextDirection).prodMk
          (HLOZColumnFullComplement.measurable_forwardTerminalFullComplementPath
            D.source.clock D.source.creationSet D.source.activeBases)
    change (simpleRandomWalkLaw.restrict
        (reflectPath ⁻¹' D.source.pathAtom)).map (f ∘ reflectPath) = _
    calc
      _ = (simpleRandomWalkLaw.restrict D.source.pathAtom).map f :=
        simpleRandomWalkLaw_restrict_reflectPath_preimage_map_comp
          D.source.pathAtom D.source.measurableSet_pathAtom f hf
      _ = simpleRandomWalkLaw D.source.pathAtom •
          ((HLOZProp48Truncated.sourceTruncatedProfileMeasure
            m D.source.profile).prod directionLaw).prod complementLaw := by
        simpa only [f, complementLaw] using D.source.fullComplement_map_law
      _ = simpleRandomWalkLaw (reflectPath ⁻¹' D.source.pathAtom) •
          ((HLOZProp48Truncated.sourceTruncatedProfileMeasure
            m D.source.profile).prod directionLaw).prod complementLaw := by
        rw [simpleRandomWalkLaw_reflectPath_preimage D.source.pathAtom
          D.source.measurableSet_pathAtom]
      _ = _ := by rfl

/-- Backward/primed reflected full-complement counterpart. -/
theorem PrimedColumnProp49AtomData.reflectedFullComplement_orderedProfileHistory_screenEstimate_of_fiberwise
    {m A : ℕ} {alpha : ℝ} {screen : Set Path}
    (profiles : Fin 6 → ExternalProfilePair) (cStar : Fin 6 → ℝ)
    {i : Fin 6} {a : AlphaTriple} {r : StageIndex}
    (D : PrimedColumnProp49AtomData m A alpha screen)
    (c : Fin (stageNumber r) → Site)
    (hdet : EventDeterminedByOn (reflectPath ⁻¹' D.source.pathAtom)
      (orderedProfileHistoryEvent profiles cStar m i a r c)
      (HLOZColumnFullComplement.primedTerminalFullComplementPath
        D.source.clock D.source.creationSet D.source.activeBases ∘
          reflectPath)) :
    RefinedAtomScreenEstimate
      (orderedProfileHistoryPathAtom profiles cStar m i a r c
        (reflectPath ⁻¹' D.source.pathAtom))
      (reflectPath ⁻¹' screen) (sourceProp49ScreenRate m A alpha) := by
  let RD := reflectedStoppedTruncatedProp49AtomInput D.toInput
  let complementLaw :=
    HLOZColumnFullComplement.columnMixedComplementRunMeasure
      D.source.clock.baseAt m D.source.creationSet D.source.activeBases
        D.source.externalLeft D.source.externalRight
  let z := HLOZColumnFullComplement.primedTerminalFullComplementPath
    D.source.clock D.source.creationSet D.source.activeBases ∘ reflectPath
  apply refinedAtomScreenEstimate_of_joint_complement_determined
    RD complementLaw z
  · exact
      (HLOZColumnFullComplement.measurable_primedTerminalFullComplementPath
        D.source.clock D.source.creationSet D.source.activeBases).comp
          measurable_reflectPath
  · exact MeasurableSet.of_discrete
  · exact hdet
  · let f := fun s ↦
        ((D.source.lazyVector s, D.source.nextDirection s),
          HLOZColumnFullComplement.primedTerminalFullComplementPath
            D.source.clock D.source.creationSet D.source.activeBases s)
    have hf : Measurable f :=
      (D.source.measurable_lazyVector.prodMk
        D.source.measurable_nextDirection).prodMk
          (HLOZColumnFullComplement.measurable_primedTerminalFullComplementPath
            D.source.clock D.source.creationSet D.source.activeBases)
    change (simpleRandomWalkLaw.restrict
        (reflectPath ⁻¹' D.source.pathAtom)).map (f ∘ reflectPath) = _
    calc
      _ = (simpleRandomWalkLaw.restrict D.source.pathAtom).map f :=
        simpleRandomWalkLaw_restrict_reflectPath_preimage_map_comp
          D.source.pathAtom D.source.measurableSet_pathAtom f hf
      _ = simpleRandomWalkLaw D.source.pathAtom •
          ((HLOZProp48Truncated.sourceTruncatedProfileMeasure
            m D.source.profile).prod directionLaw).prod complementLaw := by
        simpa only [f, complementLaw] using D.source.fullComplement_map_law
      _ = simpleRandomWalkLaw (reflectPath ⁻¹' D.source.pathAtom) •
          ((HLOZProp48Truncated.sourceTruncatedProfileMeasure
            m D.source.profile).prod directionLaw).prod complementLaw := by
        rw [simpleRandomWalkLaw_reflectPath_preimage D.source.pathAtom
          D.source.measurableSet_pathAtom]
      _ = _ := by rfl

/-- Reflected forward-column tower with the actual `Y'` history split into
its ordered-site, base-pairing and preceding-stage components.  No equality
between the later `Y` and `Y'` histories is used. -/
theorem ForwardColumnProp49AtomData.reflectedFullComplement_orderedProfileHistory_screenEstimate_of_stages
    {m A : ℕ} {alpha : ℝ} {screen : Set Path}
    (profiles : Fin 6 → ExternalProfilePair) (cStar : Fin 6 → ℝ)
    {i : Fin 6} {a : AlphaTriple} {r : StageIndex}
    (D : ForwardColumnProp49AtomData m A alpha screen)
    (c : Fin (stageNumber r) → Site)
    (hordered : EventDeterminedByOn (reflectPath ⁻¹' D.source.pathAtom)
      (orderedCreationSitesEvent m (stageNumber r) c)
      (HLOZColumnFullComplement.forwardTerminalFullComplementPath
        D.source.clock D.source.creationSet D.source.activeBases ∘ reflectPath))
    (hbase : EventDeterminedByOn (reflectPath ⁻¹' D.source.pathAtom)
      (prefixPairingEvent m i 1)
      (HLOZColumnFullComplement.forwardTerminalFullComplementPath
        D.source.clock D.source.creationSet D.source.activeBases ∘ reflectPath))
    (hstage : ∀ (j : Fin 3), j.1 < r.1 →
      EventDeterminedByOn (reflectPath ⁻¹' D.source.pathAtom)
        (prop47StageEvent profiles cStar i m j
          (alphaValue (tripleAlphaIndex a j)))
        (HLOZColumnFullComplement.forwardTerminalFullComplementPath
          D.source.clock D.source.creationSet D.source.activeBases ∘ reflectPath)) :
    RefinedAtomScreenEstimate
      (orderedProfileHistoryPathAtom profiles cStar m i a r c
        (reflectPath ⁻¹' D.source.pathAtom))
      (reflectPath ⁻¹' screen) (sourceProp49ScreenRate m A alpha) := by
  apply
    Erdos1166.HLOZProp49CanonicalRefinement.ForwardColumnProp49AtomData.reflectedFullComplement_orderedProfileHistory_screenEstimate_of_fiberwise
      profiles cStar D c
  exact eventDeterminedByOn_orderedProfileHistoryEvent_of_stages
    (reflectPath ⁻¹' D.source.pathAtom)
      (HLOZColumnFullComplement.forwardTerminalFullComplementPath
        D.source.clock D.source.creationSet D.source.activeBases ∘ reflectPath)
      profiles cStar m i a r c hordered hbase hstage

/-- Reflected backward/primed componentwise history tower. -/
theorem PrimedColumnProp49AtomData.reflectedFullComplement_orderedProfileHistory_screenEstimate_of_stages
    {m A : ℕ} {alpha : ℝ} {screen : Set Path}
    (profiles : Fin 6 → ExternalProfilePair) (cStar : Fin 6 → ℝ)
    {i : Fin 6} {a : AlphaTriple} {r : StageIndex}
    (D : PrimedColumnProp49AtomData m A alpha screen)
    (c : Fin (stageNumber r) → Site)
    (hordered : EventDeterminedByOn (reflectPath ⁻¹' D.source.pathAtom)
      (orderedCreationSitesEvent m (stageNumber r) c)
      (HLOZColumnFullComplement.primedTerminalFullComplementPath
        D.source.clock D.source.creationSet D.source.activeBases ∘ reflectPath))
    (hbase : EventDeterminedByOn (reflectPath ⁻¹' D.source.pathAtom)
      (prefixPairingEvent m i 1)
      (HLOZColumnFullComplement.primedTerminalFullComplementPath
        D.source.clock D.source.creationSet D.source.activeBases ∘ reflectPath))
    (hstage : ∀ (j : Fin 3), j.1 < r.1 →
      EventDeterminedByOn (reflectPath ⁻¹' D.source.pathAtom)
        (prop47StageEvent profiles cStar i m j
          (alphaValue (tripleAlphaIndex a j)))
        (HLOZColumnFullComplement.primedTerminalFullComplementPath
          D.source.clock D.source.creationSet D.source.activeBases ∘ reflectPath)) :
    RefinedAtomScreenEstimate
      (orderedProfileHistoryPathAtom profiles cStar m i a r c
        (reflectPath ⁻¹' D.source.pathAtom))
      (reflectPath ⁻¹' screen) (sourceProp49ScreenRate m A alpha) := by
  apply
    Erdos1166.HLOZProp49CanonicalRefinement.PrimedColumnProp49AtomData.reflectedFullComplement_orderedProfileHistory_screenEstimate_of_fiberwise
      profiles cStar D c
  exact eventDeterminedByOn_orderedProfileHistoryEvent_of_stages
    (reflectPath ⁻¹' D.source.pathAtom)
      (HLOZColumnFullComplement.primedTerminalFullComplementPath
        D.source.clock D.source.creationSet D.source.activeBases ∘ reflectPath)
      profiles cStar m i a r c hordered hbase hstage

/-- Literal later-stage `Y'` data.  The coarse terminal atom is obtained by
reflecting one of the two checked `Y` phases.  The source may provide the
history-conditioned Proposition-4.9 inequality on the *actual* `Y'` ordered
history, or prove that this history is determined by the reflected full
chronological complement.  The latter route transports the checked joint
law before applying the tower; it does not identify the later `Y` and `Y'`
histories or assume an exact product law after conditioning on either one. -/
inductive YPrimeLaterStageProp49AtomData
    (m A : ℕ) (alpha : ℝ) (yScreen : Set Path)
    (a : AlphaTriple) (r : StageIndex)
    (c : Fin (stageNumber r) → Site) where
  | forward
      (data : ForwardColumnProp49AtomData m A alpha yScreen)
      (estimate : RefinedAtomScreenEstimate
        (orderedProfileHistoryPathAtom sourceCanonicalProfiles canonicalCStar
          m yIndex' a r c (reflectPath ⁻¹' data.source.pathAtom))
        (reflectPath ⁻¹' yScreen) (sourceProp49ScreenRate m A alpha))
  | primed
      (data : PrimedColumnProp49AtomData m A alpha yScreen)
      (estimate : RefinedAtomScreenEstimate
        (orderedProfileHistoryPathAtom sourceCanonicalProfiles canonicalCStar
          m yIndex' a r c (reflectPath ⁻¹' data.source.pathAtom))
        (reflectPath ⁻¹' yScreen) (sourceProp49ScreenRate m A alpha))
  | forwardFullComplement
      (data : ForwardColumnProp49AtomData m A alpha yScreen)
      (history_determined : EventDeterminedByOn
        (reflectPath ⁻¹' data.source.pathAtom)
        (orderedProfileHistoryEvent sourceCanonicalProfiles canonicalCStar
          m yIndex' a r c)
        (HLOZColumnFullComplement.forwardTerminalFullComplementPath
          data.source.clock data.source.creationSet data.source.activeBases ∘
            reflectPath))
  | primedFullComplement
      (data : PrimedColumnProp49AtomData m A alpha yScreen)
      (history_determined : EventDeterminedByOn
        (reflectPath ⁻¹' data.source.pathAtom)
        (orderedProfileHistoryEvent sourceCanonicalProfiles canonicalCStar
          m yIndex' a r c)
        (HLOZColumnFullComplement.primedTerminalFullComplementPath
          data.source.clock data.source.creationSet data.source.activeBases ∘
            reflectPath))

noncomputable def YPrimeLaterStageProp49AtomData.atom
    {m A : ℕ} {alpha : ℝ} {yScreen : Set Path}
    {a : AlphaTriple} {r : StageIndex}
    {c : Fin (stageNumber r) → Site}
    (D : YPrimeLaterStageProp49AtomData m A alpha yScreen a r c) :
    Set Path :=
  match D with
  | .forward data _ => reflectPath ⁻¹' data.source.pathAtom
  | .primed data _ => reflectPath ⁻¹' data.source.pathAtom
  | .forwardFullComplement data _ => reflectPath ⁻¹' data.source.pathAtom
  | .primedFullComplement data _ => reflectPath ⁻¹' data.source.pathAtom

theorem YPrimeLaterStageProp49AtomData.measurableSet_atom
    {m A : ℕ} {alpha : ℝ} {yScreen : Set Path}
    {a : AlphaTriple} {r : StageIndex}
    {c : Fin (stageNumber r) → Site}
    (D : YPrimeLaterStageProp49AtomData m A alpha yScreen a r c) :
    MeasurableSet D.atom := by
  cases D with
  | forward data _ =>
      exact data.source.measurableSet_pathAtom.preimage measurable_reflectPath
  | primed data _ =>
      exact data.source.measurableSet_pathAtom.preimage measurable_reflectPath
  | forwardFullComplement data _ =>
      exact data.source.measurableSet_pathAtom.preimage measurable_reflectPath
  | primedFullComplement data _ =>
      exact data.source.measurableSet_pathAtom.preimage measurable_reflectPath

/-- The literal history-conditioned source estimate supplies the complete
later `Y'` screen estimate. -/
theorem YPrimeLaterStageProp49AtomData.screenEstimate
    {m A : ℕ} {alpha : ℝ} {yScreen : Set Path}
    {a : AlphaTriple} {r : StageIndex}
    {c : Fin (stageNumber r) → Site}
    (D : YPrimeLaterStageProp49AtomData m A alpha yScreen a r c) :
    RefinedAtomScreenEstimate
      (orderedProfileHistoryPathAtom sourceCanonicalProfiles canonicalCStar
        m yIndex' a r c D.atom)
      (reflectPath ⁻¹' yScreen) (sourceProp49ScreenRate m A alpha) := by
  cases D with
  | forward data estimate => exact estimate
  | primed data estimate => exact estimate
  | forwardFullComplement data history_determined =>
      exact
        Erdos1166.HLOZProp49CanonicalRefinement.ForwardColumnProp49AtomData.reflectedFullComplement_orderedProfileHistory_screenEstimate_of_fiberwise
          sourceCanonicalProfiles canonicalCStar data c history_determined
  | primedFullComplement data history_determined =>
      exact
        Erdos1166.HLOZProp49CanonicalRefinement.PrimedColumnProp49AtomData.reflectedFullComplement_orderedProfileHistory_screenEstimate_of_fiberwise
          sourceCanonicalProfiles canonicalCStar data c history_determined

def reflectStageZeroCreationTuple (c : Fin 1 → Site) : Fin 1 → Site :=
  fun j ↦ reflectSite (c j)

/-- Ordered creation sites and the complete zero-stage column history are
equivariant under the reflection exchanging `Y` and `Y'`. -/
theorem orderedProfileHistoryEvent_zero_yPrime_reflect_iff
    (profiles : Fin 6 → ExternalProfilePair) (cStar : Fin 6 → ℝ)
    (m : ℕ) (a : AlphaTriple) (c : Fin 1 → Site) (s : Path) :
    s ∈ orderedProfileHistoryEvent profiles cStar m yIndex' a 0 c ↔
      reflectPath s ∈
        orderedProfileHistoryEvent profiles cStar m yIndex a 0
          (reflectStageZeroCreationTuple c) := by
  have hordered :
      s ∈ orderedCreationSitesEvent m 1 c ↔
        reflectPath s ∈ orderedCreationSitesEvent m 1
          (reflectStageZeroCreationTuple c) := by
    constructor
    · intro hs
      unfold orderedCreationSitesEvent at hs ⊢
      funext j
      change levelCreationSite (reflectPath s) m (j.1 + 1) = _
      rw [levelCreationSite_reflectPath]
      have hsj := congrFun hs j
      change levelCreationSite s m (j.1 + 1) = c j at hsj
      rw [hsj]
      rfl
    · intro hs
      unfold orderedCreationSitesEvent at hs ⊢
      funext j
      apply reflectSite_injective
      calc
        reflectSite (levelCreationSite s m (j.1 + 1)) =
            levelCreationSite (reflectPath s) m (j.1 + 1) := by
              rw [levelCreationSite_reflectPath]
        _ = reflectStageZeroCreationTuple c j := congrFun hs j
        _ = reflectSite (c j) := rfl
  have hprefix :
      s ∈ prefixPairingEvent m yIndex' 1 ↔
        reflectPath s ∈ prefixPairingEvent m yIndex 1 := by
    have h := prefixPairingEvent_y_reflect_iff (reflectPath s) m 1
    change s ∈ prefixPairingEvent m ⟨5, by omega⟩ 1 ↔
      reflectPath s ∈ prefixPairingEvent m ⟨4, by omega⟩ 1
    simpa only [reflectPath_reflectPath] using h
  change
    (s ∈ orderedCreationSitesEvent m 1 c ∩
        prop47History profiles cStar m yIndex' a 0) ↔
      reflectPath s ∈ orderedCreationSitesEvent m 1
          (reflectStageZeroCreationTuple c) ∩
        prop47History profiles cStar m yIndex a 0
  rw [prop47History_zero, prop47History_zero]
  exact and_congr hordered hprefix

theorem orderedProfileHistoryPathAtom_zero_yPrime_reflect
    (profiles : Fin 6 → ExternalProfilePair) (cStar : Fin 6 → ℝ)
    (m : ℕ) (a : AlphaTriple) (c : Fin 1 → Site)
    (baseAtom : Set Path) :
    orderedProfileHistoryPathAtom profiles cStar m yIndex' a 0 c
        (reflectPath ⁻¹' baseAtom) =
      reflectPath ⁻¹'
        orderedProfileHistoryPathAtom profiles cStar m yIndex a 0
          (reflectStageZeroCreationTuple c) baseAtom := by
  ext s
  exact and_congr_right fun _ ↦
    orderedProfileHistoryEvent_zero_yPrime_reflect_iff
      profiles cStar m a c s

/-- Reflection preserves a refined-atom estimate for measurable atoms and
screens. -/
theorem refinedAtomScreenEstimate_preimage_reflectPath
    (atom screen : Set Path) (rate : ℝ≥0∞)
    (hatom : MeasurableSet atom) (hscreen : MeasurableSet screen)
    (hsource : RefinedAtomScreenEstimate atom screen rate) :
    RefinedAtomScreenEstimate
      (reflectPath ⁻¹' atom) (reflectPath ⁻¹' screen) rate := by
  rw [RefinedAtomScreenEstimate, ← Set.preimage_inter]
  rw [simpleRandomWalkLaw_reflectPath_preimage _
      (hatom.inter hscreen),
    simpleRandomWalkLaw_reflectPath_preimage _ hatom]
  exact hsource

/-- A literal first-stage `Y` terminal atom gives the corresponding `Y'`
estimate only after the complete event is reflected.  No temporal phase is
misidentified as `Y'`. -/
theorem yPrimeStageZeroProp49_reflected_screenEstimate
    {m A : ℕ} {alpha : ℝ} {yScreen : Set Path} {a : AlphaTriple}
    (D : YStageZeroProp49AtomData m A alpha yScreen)
    (c : Fin 1 → Site) (hscreen : MeasurableSet yScreen)
    (hnonempty :
      (orderedProfileHistoryPathAtom sourceCanonicalProfiles canonicalCStar
        m yIndex' a 0 c (reflectPath ⁻¹' D.atom)).Nonempty) :
    RefinedAtomScreenEstimate
      (orderedProfileHistoryPathAtom sourceCanonicalProfiles canonicalCStar
        m yIndex' a 0 c (reflectPath ⁻¹' D.atom))
      (reflectPath ⁻¹' yScreen) (sourceProp49ScreenRate m A alpha) := by
  let eastAtom := orderedProfileHistoryPathAtom sourceCanonicalProfiles
    canonicalCStar m yIndex a 0 (reflectStageZeroCreationTuple c) D.atom
  have heq :
      orderedProfileHistoryPathAtom sourceCanonicalProfiles canonicalCStar
          m yIndex' a 0 c (reflectPath ⁻¹' D.atom) =
        reflectPath ⁻¹' eastAtom := by
    exact orderedProfileHistoryPathAtom_zero_yPrime_reflect
      sourceCanonicalProfiles canonicalCStar m a c D.atom
  have hn : eastAtom.Nonempty := by
    rcases hnonempty with ⟨s, hs⟩
    rw [heq] at hs
    exact ⟨reflectPath s, hs⟩
  have hsource : RefinedAtomScreenEstimate eastAtom yScreen
      (sourceProp49ScreenRate m A alpha) := by
    exact D.screenEstimate (reflectStageZeroCreationTuple c) hn
  have hmeasurable : MeasurableSet eastAtom := by
    dsimp only [eastAtom]
    exact measurableSet_orderedProfileHistoryPathAtom
      sourceCanonicalProfiles sourceCanonicalProfiles_oneStepAdapted
      canonicalCStar m yIndex a 0 (reflectStageZeroCreationTuple c) D.atom
        D.m_pos D.measurableSet_atom
  rw [heq]
  exact refinedAtomScreenEstimate_preimage_reflectPath
    eastAtom yScreen (sourceProp49ScreenRate m A alpha)
      hmeasurable hscreen hsource

/-- A natural number canonically decodes to a raw-atom index and an ordered
creation tuple.  Codes outside the range of `Encodable.encode` represent the
empty atom. -/
noncomputable def canonicalOrderedHistoryAtom
    (baseAtom : ℕ → Set Path)
    (profiles : Fin 6 → ExternalProfilePair) (cStar : Fin 6 → ℝ)
    (m : ℕ) (i : Fin 6) (a : AlphaTriple) (r : StageIndex)
    (code : ℕ) : Set Path :=
  match Encodable.decode₂ (ℕ × (Fin (stageNumber r) → Site)) code with
  | none => ∅
  | some (η, c) =>
      orderedProfileHistoryPathAtom profiles cStar m i a r c (baseAtom η)

@[simp] theorem canonicalOrderedHistoryAtom_encode
    (baseAtom : ℕ → Set Path)
    (profiles : Fin 6 → ExternalProfilePair) (cStar : Fin 6 → ℝ)
    (m : ℕ) (i : Fin 6) (a : AlphaTriple) (r : StageIndex)
    (η : ℕ) (c : Fin (stageNumber r) → Site) :
    canonicalOrderedHistoryAtom baseAtom profiles cStar m i a r
        (Encodable.encode (η, c)) =
      orderedProfileHistoryPathAtom profiles cStar m i a r c (baseAtom η) := by
  unfold canonicalOrderedHistoryAtom
  rw [Encodable.decode₂_encode]

theorem canonicalOrderedHistoryAtom_pairwise
    (baseAtom : ℕ → Set Path)
    (profiles : Fin 6 → ExternalProfilePair) (cStar : Fin 6 → ℝ)
    (m : ℕ) (i : Fin 6) (a : AlphaTriple) (r : StageIndex)
    (hdisjoint : Pairwise fun η ζ ↦ Disjoint (baseAtom η) (baseAtom ζ)) :
    Pairwise fun n l ↦ Disjoint
      (canonicalOrderedHistoryAtom baseAtom profiles cStar m i a r n)
      (canonicalOrderedHistoryAtom baseAtom profiles cStar m i a r l) := by
  intro n l hnl
  rw [Set.disjoint_left]
  intro s hsn hsl
  generalize hncode : Encodable.decode₂
      (ℕ × (Fin (stageNumber r) → Site)) n = xn
  generalize hlcode : Encodable.decode₂
      (ℕ × (Fin (stageNumber r) → Site)) l = xl
  cases xn with
  | none => simp [canonicalOrderedHistoryAtom, hncode] at hsn
  | some x =>
      cases xl with
      | none => simp [canonicalOrderedHistoryAtom, hlcode] at hsl
      | some y =>
          rcases x with ⟨η, c⟩
          rcases y with ⟨ζ, d⟩
          rw [canonicalOrderedHistoryAtom, hncode] at hsn
          rw [canonicalOrderedHistoryAtom, hlcode] at hsl
          by_cases hηζ : η = ζ
          · subst ζ
            have hcd : c = d := hsn.2.1.symm.trans hsl.2.1
            subst d
            have hnenc : Encodable.encode (η, c) = n :=
              Encodable.decode₂_eq_some.mp hncode
            have hlenc : Encodable.encode (η, c) = l :=
              Encodable.decode₂_eq_some.mp hlcode
            exact hnl (hnenc.symm.trans hlenc)
          · exact Set.disjoint_left.mp (hdisjoint hηζ) hsn.1 hsl.1

theorem measurableSet_canonicalOrderedHistoryAtom
    (baseAtom : ℕ → Set Path)
    (profiles : Fin 6 → ExternalProfilePair)
    (hadapt : OneStepAdaptedProfiles profiles) (cStar : Fin 6 → ℝ)
    (m : ℕ) (i : Fin 6) (a : AlphaTriple) (r : StageIndex)
    (hm : 0 < m) (hmeasurable : ∀ η, MeasurableSet (baseAtom η))
    (code : ℕ) :
    MeasurableSet
      (canonicalOrderedHistoryAtom baseAtom profiles cStar m i a r code) := by
  generalize hcode : Encodable.decode₂
      (ℕ × (Fin (stageNumber r) → Site)) code = x
  cases x with
  | none => simp [canonicalOrderedHistoryAtom, hcode]
  | some x =>
      rcases x with ⟨η, c⟩
      rw [canonicalOrderedHistoryAtom, hcode]
      exact measurableSet_orderedProfileHistoryPathAtom
        profiles hadapt cStar m i a r c (baseAtom η) hm (hmeasurable η)

theorem canonicalOrderedHistoryAtom_subset_history
    (baseAtom : ℕ → Set Path)
    (profiles : Fin 6 → ExternalProfilePair) (cStar : Fin 6 → ℝ)
    (m : ℕ) (i : Fin 6) (a : AlphaTriple) (r : StageIndex)
    (code : ℕ) :
    canonicalOrderedHistoryAtom baseAtom profiles cStar m i a r code ⊆
      prop47History profiles cStar m i a r.1 := by
  generalize hcode : Encodable.decode₂
      (ℕ × (Fin (stageNumber r) → Site)) code = x
  cases x with
  | none => simp [canonicalOrderedHistoryAtom, hcode]
  | some x =>
      rcases x with ⟨η, c⟩
      rw [canonicalOrderedHistoryAtom, hcode]
      exact orderedProfileHistoryPathAtom_subset_history
        profiles cStar m i a r c (baseAtom η)

/-- Retain a canonical ordered-history atom only when it can contribute to
the branch-screen numerator.  This lets the finite-union connector ignore
off-screen raw-code fibres, whose measurability is irrelevant. -/
noncomputable def canonicalScreenedOrderedHistoryAtom
    (baseAtom : ℕ → Set Path)
    (profiles : Fin 6 → ExternalProfilePair) (cStar : Fin 6 → ℝ)
    (m : ℕ) (i : Fin 6) (a : AlphaTriple) (r : StageIndex)
    (screen : Set Path) (code : ℕ) : Set Path := by
  classical
  let atom := canonicalOrderedHistoryAtom
    baseAtom profiles cStar m i a r code
  exact if (atom ∩ screen).Nonempty then atom else ∅

@[simp] theorem canonicalScreenedOrderedHistoryAtom_of_nonempty
    (baseAtom : ℕ → Set Path)
    (profiles : Fin 6 → ExternalProfilePair) (cStar : Fin 6 → ℝ)
    (m : ℕ) (i : Fin 6) (a : AlphaTriple) (r : StageIndex)
    (screen : Set Path) (code : ℕ)
    (h : (canonicalOrderedHistoryAtom baseAtom profiles cStar
      m i a r code ∩ screen).Nonempty) :
    canonicalScreenedOrderedHistoryAtom baseAtom profiles cStar
      m i a r screen code =
        canonicalOrderedHistoryAtom baseAtom profiles cStar
          m i a r code := by
  simp [canonicalScreenedOrderedHistoryAtom, h]

@[simp] theorem canonicalScreenedOrderedHistoryAtom_of_not_nonempty
    (baseAtom : ℕ → Set Path)
    (profiles : Fin 6 → ExternalProfilePair) (cStar : Fin 6 → ℝ)
    (m : ℕ) (i : Fin 6) (a : AlphaTriple) (r : StageIndex)
    (screen : Set Path) (code : ℕ)
    (h : ¬(canonicalOrderedHistoryAtom baseAtom profiles cStar
      m i a r code ∩ screen).Nonempty) :
    canonicalScreenedOrderedHistoryAtom baseAtom profiles cStar
      m i a r screen code = ∅ := by
  simp [canonicalScreenedOrderedHistoryAtom, h]

theorem canonicalScreenedOrderedHistoryAtom_subset
    (baseAtom : ℕ → Set Path)
    (profiles : Fin 6 → ExternalProfilePair) (cStar : Fin 6 → ℝ)
    (m : ℕ) (i : Fin 6) (a : AlphaTriple) (r : StageIndex)
    (screen : Set Path) (code : ℕ) :
    canonicalScreenedOrderedHistoryAtom baseAtom profiles cStar
        m i a r screen code ⊆
      canonicalOrderedHistoryAtom baseAtom profiles cStar m i a r code := by
  classical
  by_cases h : (canonicalOrderedHistoryAtom baseAtom profiles cStar
      m i a r code ∩ screen).Nonempty
  · rw [canonicalScreenedOrderedHistoryAtom_of_nonempty _ _ _ _ _ _ _ _ _ h]
  · rw [canonicalScreenedOrderedHistoryAtom_of_not_nonempty _ _ _ _ _ _ _ _ _ h]
    exact Set.empty_subset _

theorem canonicalScreenedOrderedHistoryAtom_pairwise
    (baseAtom : ℕ → Set Path)
    (profiles : Fin 6 → ExternalProfilePair) (cStar : Fin 6 → ℝ)
    (m : ℕ) (i : Fin 6) (a : AlphaTriple) (r : StageIndex)
    (screen : Set Path)
    (hdisjoint : Pairwise fun η ζ ↦ Disjoint (baseAtom η) (baseAtom ζ)) :
    Pairwise fun n l ↦ Disjoint
      (canonicalScreenedOrderedHistoryAtom baseAtom profiles cStar
        m i a r screen n)
      (canonicalScreenedOrderedHistoryAtom baseAtom profiles cStar
        m i a r screen l) := by
  intro n l hnl
  exact (canonicalOrderedHistoryAtom_pairwise baseAtom profiles cStar
    m i a r hdisjoint hnl).mono
      (canonicalScreenedOrderedHistoryAtom_subset
        baseAtom profiles cStar m i a r screen n)
      (canonicalScreenedOrderedHistoryAtom_subset
        baseAtom profiles cStar m i a r screen l)

theorem canonicalScreenedOrderedHistoryAtom_subset_history
    (baseAtom : ℕ → Set Path)
    (profiles : Fin 6 → ExternalProfilePair) (cStar : Fin 6 → ℝ)
    (m : ℕ) (i : Fin 6) (a : AlphaTriple) (r : StageIndex)
    (screen : Set Path) (code : ℕ) :
    canonicalScreenedOrderedHistoryAtom baseAtom profiles cStar
        m i a r screen code ⊆
      prop47History profiles cStar m i a r.1 :=
  (canonicalScreenedOrderedHistoryAtom_subset
    baseAtom profiles cStar m i a r screen code).trans
      (canonicalOrderedHistoryAtom_subset_history
        baseAtom profiles cStar m i a r code)

/-- Every path in a covered raw atom belongs to the canonically encoded
ordered-history refinement associated to its actual creation tuple. -/
theorem inter_subset_iUnion_canonicalOrderedHistoryAtom
    (baseAtom : ℕ → Set Path)
    (profiles : Fin 6 → ExternalProfilePair) (cStar : Fin 6 → ℝ)
    (m : ℕ) (i : Fin 6) (a : AlphaTriple) (r : StageIndex)
    (screen : Set Path)
    (hcover : prop47History profiles cStar m i a r.1 ∩ screen ⊆
      ⋃ η, baseAtom η) :
    prop47History profiles cStar m i a r.1 ∩ screen ⊆
      ⋃ code, canonicalOrderedHistoryAtom
        baseAtom profiles cStar m i a r code := by
  intro s hs
  rcases Set.mem_iUnion.mp (hcover hs) with ⟨η, hη⟩
  let c : Fin (stageNumber r) → Site := orderedCreationSites m (stageNumber r) s
  refine Set.mem_iUnion.mpr ⟨Encodable.encode (η, c), ?_⟩
  rw [canonicalOrderedHistoryAtom_encode]
  exact ⟨hη, rfl, hs.1⟩

/-- Source-facing Proposition-4.9 input before ordered-tuple enumeration.

The source supplies a disjoint measurable family of raw stopped atoms in
each phase and the genuine atom-local narrow-band inequality for every
ordered creation tuple.  The tuple itself is not chosen as extra data: the
canonical natural-number refinement above enumerates all of them. -/
def Prop47StoppedProfileProp49CanonicalOrderedFiniteBranchEstimate
    (branchCount localCoeff : ℕ)
    (branchScreen : ℕ → Fin 6 → AlphaTriple → StageIndex →
      Fin branchCount → Set Path)
    (baseAtom : ℕ → Fin 6 → AlphaTriple → StageIndex →
      Fin branchCount → ℕ → Set Path) : Prop :=
  ∀ᶠ m : ℕ in atTop, ∀ i a (r : StageIndex),
    alphaValue (tripleAlphaIndex a r) ≤ kappaTwo →
    let raw := baseAtom m i a r
    let history := prop47History sourceCanonicalProfiles canonicalCStar
      m i a r.1
    let fullScreen := HLOZProp47SourceObjects.lowScaleScreenEvent
      (sourceCanonicalProfiles i) (canonicalCStar i) i m (stageNumber r)
        (alphaValue (tripleAlphaIndex a r) + delta)
    let screen := branchScreen m i a r
    (∀ j, Pairwise fun η ζ ↦ Disjoint (raw j η) (raw j ζ)) ∧
    (∀ j η, MeasurableSet (raw j η)) ∧
    history ∩ fullScreen ⊆ ⋃ j, history ∩ screen j ∧
    (∀ j, history ∩ screen j ⊆ ⋃ η, raw j η) ∧
    ∀ j η (c : Fin (stageNumber r) → Site),
      (orderedProfileHistoryPathAtom sourceCanonicalProfiles canonicalCStar
        m i a r c (raw j η)).Nonempty →
        RefinedAtomScreenEstimate
          (orderedProfileHistoryPathAtom sourceCanonicalProfiles canonicalCStar
            m i a r c (raw j η)) (screen j)
          (sourceProp49ScreenRate m localCoeff
            (alphaValue (tripleAlphaIndex a r)))

/-- Canonical ordered-tuple enumeration converts the raw source family to
the history-contained finite-branch interface used by the low-stage
connector. -/
theorem
    prop47StoppedProfileProp49HistoryContainedFiniteBranchEstimate_of_canonicalOrdered
    (branchCount localCoeff : ℕ)
    (branchScreen : ℕ → Fin 6 → AlphaTriple → StageIndex →
      Fin branchCount → Set Path)
    (baseAtom : ℕ → Fin 6 → AlphaTriple → StageIndex →
      Fin branchCount → ℕ → Set Path)
    (hsource : Prop47StoppedProfileProp49CanonicalOrderedFiniteBranchEstimate
      branchCount localCoeff branchScreen baseAtom) :
    Prop47StoppedProfileProp49HistoryContainedFiniteBranchEstimate
      sourceCanonicalProfiles canonicalCStar branchCount localCoeff
      branchScreen
      (fun m i a r j code ↦ canonicalOrderedHistoryAtom
        (baseAtom m i a r j) sourceCanonicalProfiles canonicalCStar
          m i a r code) := by
  filter_upwards [hsource, eventually_ge_atTop (1 : ℕ)] with m hm hmpos
  intro i a r halpha
  rcases hm i a r halpha with
    ⟨hdisjoint, hmeasurable, hbranchCover, hrawCover, hlocal⟩
  refine ⟨?_, ?_, hbranchCover, ?_, ?_⟩
  · intro j
    exact canonicalOrderedHistoryAtom_pairwise
      (baseAtom m i a r j) sourceCanonicalProfiles canonicalCStar
        m i a r (hdisjoint j)
  · intro j code
    exact measurableSet_canonicalOrderedHistoryAtom
      (baseAtom m i a r j) sourceCanonicalProfiles
      sourceCanonicalProfiles_oneStepAdapted canonicalCStar
      m i a r (by omega) (hmeasurable j) code
  · intro j
    exact inter_subset_iUnion_canonicalOrderedHistoryAtom
      (baseAtom m i a r j) sourceCanonicalProfiles canonicalCStar
        m i a r (branchScreen m i a r j) (hrawCover j)
  · intro j code
    refine ⟨canonicalOrderedHistoryAtom_subset_history
      (baseAtom m i a r j) sourceCanonicalProfiles canonicalCStar
        m i a r code, ?_⟩
    generalize hcode : Encodable.decode₂
        (ℕ × (Fin (stageNumber r) → Site)) code = x
    cases x with
    | none => simp [canonicalOrderedHistoryAtom, hcode,
        RefinedAtomScreenEstimate]
    | some x =>
        rcases x with ⟨η, c⟩
        let A := orderedProfileHistoryPathAtom sourceCanonicalProfiles
          canonicalCStar m i a r c (baseAtom m i a r j η)
        by_cases hA : A.Nonempty
        · simpa only [canonicalOrderedHistoryAtom, hcode, A] using
            hlocal j η c hA
        · have hAempty : A = ∅ := Set.not_nonempty_iff_eq_empty.mp hA
          simp only [canonicalOrderedHistoryAtom, hcode, A, hAempty,
            RefinedAtomScreenEstimate, Set.empty_inter, measure_empty,
            mul_zero, le_refl]

/-! ### Canonical raw-atom fibers

The raw stopped data in the source are themselves countable.  It is more
faithful, and substantially less error-prone, to ask for one measurable
natural-valued code than to ask a caller to manufacture a countable
partition and separately prove its measurability, disjointness, and cover.
The fibers below supply all three facts canonically. -/

/-- The raw stopped atom with code `eta`. -/
def rawCodeFiber (rawCode : Path → ℕ) (eta : ℕ) : Set Path :=
  rawCode ⁻¹' {eta}

theorem rawCodeFiber_pairwise (rawCode : Path → ℕ) :
    Pairwise fun eta zeta ↦
      Disjoint (rawCodeFiber rawCode eta) (rawCodeFiber rawCode zeta) := by
  intro eta zeta hne
  rw [Set.disjoint_left]
  intro s hsEta hsZeta
  have he : rawCode s = eta := by simpa [rawCodeFiber] using hsEta
  have hz : rawCode s = zeta := by simpa [rawCodeFiber] using hsZeta
  exact hne (he.symm.trans hz)

theorem measurableSet_rawCodeFiber (rawCode : Path → ℕ)
    (hrawCode : Measurable rawCode) (eta : ℕ) :
    MeasurableSet (rawCodeFiber rawCode eta) :=
  (measurableSet_singleton eta).preimage hrawCode

theorem iUnion_rawCodeFiber (rawCode : Path → ℕ) :
    (⋃ eta, rawCodeFiber rawCode eta) = Set.univ := by
  ext s
  simp [rawCodeFiber]

/-! ### Canonical winner/parity screens

The branch cover used by Proposition 4.9 is deterministic.  For the four
checkerboard pairings, a nonempty near-favourite set has a nonempty tie-left
or strict-right winner set; the stopping-time parity then selects one of the
four literal stopped laws.  For the column pairing only the two winner
phases are needed.  Quarter turns and the origin-fixing reflection transport
these screens to the other five pairings. -/

/-- The literal tie-left X-east winner set is a measurable finite-set-valued
function.  This is derived from the already measurable near-favourite set
and stopped local times; it is not source data. -/
theorem measurable_xEastLeftNearFavoriteWinnerSites
    (m k : ℕ) (alpha : ℝ) :
    Measurable fun s : Path ↦
      xEastLeftNearFavoriteWinnerSites s m k alpha := by
  have hbase : Measurable fun s : Path ↦
      (nearFavoriteSites (xIndex east) s m k alpha).image
        horizontalChessBase :=
    (measurable_of_countable
      (fun F : Finset Site ↦ F.image horizontalChessBase)).comp
        (measurable_nearFavoriteSites (xIndex east) m k alpha)
  rw [measurable_finset_iff]
  intro x
  simp only [xEastLeftNearFavoriteWinnerSites,
    hlozLeftActiveFreeWinnerCandidateSitesAtTime,
    hlozLeftWinnerCandidateSitesAtTime, hlozCandidateDominoBasesAtTime,
    xEast_nearFavorite_candidateSites_eq, Finset.mem_filter]
  exact (Measurable.and
    ((measurable_finset_mem x).comp hbase)
    (measurableSet_setOfPred.mp (measurableSet_le
      (HLOZLemma410Prop48Connector.measurable_stoppedLocalTime_firstKSites
        m k (x + paperE1))
      (HLOZLemma410Prop48Connector.measurable_stoppedLocalTime_firstKSites
        m k x)))).and
    (measurableSet_setOfPred.mp (measurableSet_lt
      (HLOZLemma410Prop48Connector.measurable_stoppedLocalTime_firstKSites
        m k x) measurable_const))

/-- The literal strict-right X-east winner set is measurable. -/
theorem measurable_xEastRightNearFavoriteWinnerSites
    (m k : ℕ) (alpha : ℝ) :
    Measurable fun s : Path ↦
      xEastRightNearFavoriteWinnerSites s m k alpha := by
  have hbase : Measurable fun s : Path ↦
      (nearFavoriteSites (xIndex east) s m k alpha).image
        horizontalChessBase :=
    (measurable_of_countable
      (fun F : Finset Site ↦ F.image horizontalChessBase)).comp
        (measurable_nearFavoriteSites (xIndex east) m k alpha)
  have hrightBase : Measurable fun s : Path ↦
      ((nearFavoriteSites (xIndex east) s m k alpha).image
        horizontalChessBase).filter fun b ↦
          localTime s (directCreationTime m k s) b <
            localTime s (directCreationTime m k s) (b + paperE1) := by
    rw [measurable_finset_iff]
    intro b
    simp only [Finset.mem_filter]
    exact Measurable.and ((measurable_finset_mem b).comp hbase)
      (measurableSet_setOfPred.mp (measurableSet_lt
        (HLOZLemma410Prop48Connector.measurable_stoppedLocalTime_firstKSites
          m k b)
        (HLOZLemma410Prop48Connector.measurable_stoppedLocalTime_firstKSites
          m k (b + paperE1))))
  have hright : Measurable fun s : Path ↦
      (((nearFavoriteSites (xIndex east) s m k alpha).image
        horizontalChessBase).filter fun b ↦
          localTime s (directCreationTime m k s) b <
            localTime s (directCreationTime m k s) (b + paperE1)).image
              (fun b ↦ b + paperE1) :=
    (measurable_of_countable
      (fun F : Finset Site ↦ F.image (fun b ↦ b + paperE1))).comp hrightBase
  rw [measurable_finset_iff]
  intro x
  simp only [xEastRightNearFavoriteWinnerSites,
    hlozRightActiveFreeWinnerCandidateSitesAtTime,
    hlozRightWinnerCandidateSitesAtTime, hlozCandidateDominoBasesAtTime,
    xEast_nearFavorite_candidateSites_eq, Finset.mem_filter]
  exact Measurable.and ((measurable_finset_mem x).comp hright)
    (measurableSet_setOfPred.mp (measurableSet_lt
      (HLOZLemma410Prop48Connector.measurable_stoppedLocalTime_firstKSites
        m k x) measurable_const))

/-- The tie-left terminal-column winner set is measurable. -/
theorem measurable_yLeftNearFavoriteWinnerBases
    (m k : ℕ) (alpha : ℝ) :
    Measurable fun s : Path ↦ yLeftNearFavoriteWinnerBases s m k alpha := by
  have hbase : Measurable fun s : Path ↦
      yNearFavoriteDominoBases s m k alpha :=
    (measurable_of_countable
      (fun F : Finset Site ↦ F.image yDominoBase)).comp
        (measurable_nearFavoriteSites yIndex m k alpha)
  rw [measurable_finset_iff]
  intro b
  simp only [yLeftNearFavoriteWinnerBases, Finset.mem_filter]
  exact Measurable.and ((measurable_finset_mem b).comp hbase)
    (measurableSet_setOfPred.mp (measurableSet_le
      (HLOZLemma410Prop48Connector.measurable_stoppedLocalTime_firstKSites
        m k (shift b (vec east)))
      (HLOZLemma410Prop48Connector.measurable_stoppedLocalTime_firstKSites
        m k b)))

/-- The strict-right terminal-column winner set is measurable. -/
theorem measurable_yRightNearFavoriteWinnerBases
    (m k : ℕ) (alpha : ℝ) :
    Measurable fun s : Path ↦ yRightNearFavoriteWinnerBases s m k alpha := by
  have hbase : Measurable fun s : Path ↦
      yNearFavoriteDominoBases s m k alpha :=
    (measurable_of_countable
      (fun F : Finset Site ↦ F.image yDominoBase)).comp
        (measurable_nearFavoriteSites yIndex m k alpha)
  rw [measurable_finset_iff]
  intro b
  simp only [yRightNearFavoriteWinnerBases, Finset.mem_filter]
  exact Measurable.and ((measurable_finset_mem b).comp hbase)
    (measurableSet_setOfPred.mp (measurableSet_lt
      (HLOZLemma410Prop48Connector.measurable_stoppedLocalTime_firstKSites
        m k b)
      (HLOZLemma410Prop48Connector.measurable_stoppedLocalTime_firstKSites
        m k (shift b (vec east)))))

/-- The four canonical X-east Proposition-4.9 screens, ordered as
unprimed-even/left, unprimed-odd/left, primed-odd/right, and
primed-even/right. -/
noncomputable def xEastCanonicalProp49BranchScreen
    (m k : ℕ) (beta : ℝ) : Fin 4 → Set Path :=
  let full := lowScaleScreenEvent (sourceCanonicalProfiles (xIndex east))
    (canonicalCStar (xIndex east)) (xIndex east) m k beta
  let left := {s |
    (xEastLeftNearFavoriteWinnerSites s m k beta).Nonempty}
  let right := {s |
    (xEastRightNearFavoriteWinnerSites s m k beta).Nonempty}
  ![
    full ∩ left ∩ {s | Even (directCreationTime m k s)},
    full ∩ left ∩ {s | ¬ Even (directCreationTime m k s)},
    full ∩ right ∩ {s | ¬ Even (directCreationTime m k s)},
    full ∩ right ∩ {s | Even (directCreationTime m k s)}]

theorem measurableSet_xEastCanonicalProp49BranchScreen
    (m k : ℕ) (beta : ℝ) (j : Fin 4) :
    MeasurableSet (xEastCanonicalProp49BranchScreen m k beta j) := by
  have hfull : MeasurableSet
      (lowScaleScreenEvent (sourceCanonicalProfiles (xIndex east))
        (canonicalCStar (xIndex east)) (xIndex east) m k beta) :=
    measurableSet_lowScaleScreenEvent _ _ _ _ _ _
  have hleft : MeasurableSet {s : Path |
      (xEastLeftNearFavoriteWinnerSites s m k beta).Nonempty} :=
    measurableSet_setOfPred.mpr
      ((measurable_of_countable fun F : Finset Site ↦ F.Nonempty).comp
        (measurable_xEastLeftNearFavoriteWinnerSites m k beta))
  have hright : MeasurableSet {s : Path |
      (xEastRightNearFavoriteWinnerSites s m k beta).Nonempty} :=
    measurableSet_setOfPred.mpr
      ((measurable_of_countable fun F : Finset Site ↦ F.Nonempty).comp
        (measurable_xEastRightNearFavoriteWinnerSites m k beta))
  have heven : MeasurableSet {s : Path |
      Even (directCreationTime m k s)} :=
    measurableSet_setOfPred.mpr
      ((measurable_of_countable fun n : ℕ ↦ Even n).comp
        (measurable_directCreationTime m k))
  have hodd : MeasurableSet {s : Path |
      Odd (directCreationTime m k s)} :=
    measurableSet_setOfPred.mpr
      ((measurable_of_countable fun n : ℕ ↦ Odd n).comp
        (measurable_directCreationTime m k))
  fin_cases j <;>
    simp only [xEastCanonicalProp49BranchScreen, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.tail_cons] <;>
    measurability

/-- A nonempty canonical X-east screen is covered by the four winner/parity
screens. -/
theorem lowScaleScreenEvent_xEast_subset_canonicalProp49BranchScreens
    (m k : ℕ) (beta : ℝ) (hm : 0 < m) (hk : 0 < k) :
    lowScaleScreenEvent (sourceCanonicalProfiles (xIndex east))
        (canonicalCStar (xIndex east)) (xIndex east) m k beta ⊆
      ⋃ j, xEastCanonicalProp49BranchScreen m k beta j := by
  intro s hs
  have hnear : (nearFavoriteSites (xIndex east) s m k beta).Nonempty := hs.1
  have hcard := xEast_nearFavorite_card_le_two_mul_winners
    s m k beta hm hk
  have hsum : 0 <
      (xEastLeftNearFavoriteWinnerSites s m k beta).card +
        (xEastRightNearFavoriteWinnerSites s m k beta).card := by
    have hnearCard : 0 <
        (nearFavoriteSites (xIndex east) s m k beta).card :=
      Finset.card_pos.mpr hnear
    omega
  have hwinner :
      (xEastLeftNearFavoriteWinnerSites s m k beta).Nonempty ∨
        (xEastRightNearFavoriteWinnerSites s m k beta).Nonempty := by
    by_cases hleft :
        (xEastLeftNearFavoriteWinnerSites s m k beta).Nonempty
    · exact Or.inl hleft
    · right
      have hleftZero :
          (xEastLeftNearFavoriteWinnerSites s m k beta).card = 0 :=
        Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp hleft)
      exact Finset.card_pos.mp (by omega)
  rcases hwinner with hleft | hright
  · by_cases heven : Even (directCreationTime m k s)
    · refine Set.mem_iUnion.mpr ⟨(0 : Fin 4), ?_⟩
      change s ∈
        (lowScaleScreenEvent (sourceCanonicalProfiles (xIndex east))
            (canonicalCStar (xIndex east)) (xIndex east) m k beta ∩
          {s | (xEastLeftNearFavoriteWinnerSites s m k beta).Nonempty}) ∩
            {s | Even (directCreationTime m k s)}
      exact ⟨⟨hs, hleft⟩, heven⟩
    · refine Set.mem_iUnion.mpr ⟨(1 : Fin 4), ?_⟩
      change s ∈
        (lowScaleScreenEvent (sourceCanonicalProfiles (xIndex east))
            (canonicalCStar (xIndex east)) (xIndex east) m k beta ∩
          {s | (xEastLeftNearFavoriteWinnerSites s m k beta).Nonempty}) ∩
            {s | ¬ Even (directCreationTime m k s)}
      exact ⟨⟨hs, hleft⟩, heven⟩
  · by_cases heven : Even (directCreationTime m k s)
    · refine Set.mem_iUnion.mpr ⟨(3 : Fin 4), ?_⟩
      change s ∈
        (lowScaleScreenEvent (sourceCanonicalProfiles (xIndex east))
            (canonicalCStar (xIndex east)) (xIndex east) m k beta ∩
          {s | (xEastRightNearFavoriteWinnerSites s m k beta).Nonempty}) ∩
            {s | Even (directCreationTime m k s)}
      exact ⟨⟨hs, hright⟩, heven⟩
    · refine Set.mem_iUnion.mpr ⟨(2 : Fin 4), ?_⟩
      change s ∈
        (lowScaleScreenEvent (sourceCanonicalProfiles (xIndex east))
            (canonicalCStar (xIndex east)) (xIndex east) m k beta ∩
          {s | (xEastRightNearFavoriteWinnerSites s m k beta).Nonempty}) ∩
            {s | ¬ Even (directCreationTime m k s)}
      exact ⟨⟨hs, hright⟩, heven⟩

/-- The two canonical unreflected column screens.  The unused last two
indices are empty so that all six pairings share the same `Fin 4` arity. -/
noncomputable def yCanonicalProp49BranchScreen
    (m k : ℕ) (beta : ℝ) : Fin 4 → Set Path :=
  let full := lowScaleScreenEvent (sourceCanonicalProfiles yIndex)
    (canonicalCStar yIndex) yIndex m k beta
  let left := {s | (yLeftNearFavoriteWinnerBases s m k beta).Nonempty}
  let right := {s | (yRightNearFavoriteWinnerBases s m k beta).Nonempty}
  ![full ∩ left, full ∩ right, ∅, ∅]

theorem measurableSet_yCanonicalProp49BranchScreen
    (m k : ℕ) (beta : ℝ) (j : Fin 4) :
    MeasurableSet (yCanonicalProp49BranchScreen m k beta j) := by
  have hfull : MeasurableSet
      (lowScaleScreenEvent (sourceCanonicalProfiles yIndex)
        (canonicalCStar yIndex) yIndex m k beta) :=
    measurableSet_lowScaleScreenEvent _ _ _ _ _ _
  have hleft : MeasurableSet {s : Path |
      (yLeftNearFavoriteWinnerBases s m k beta).Nonempty} :=
    measurableSet_setOfPred.mpr
      ((measurable_of_countable fun F : Finset Site ↦ F.Nonempty).comp
        (measurable_yLeftNearFavoriteWinnerBases m k beta))
  have hright : MeasurableSet {s : Path |
      (yRightNearFavoriteWinnerBases s m k beta).Nonempty} :=
    measurableSet_setOfPred.mpr
      ((measurable_of_countable fun F : Finset Site ↦ F.Nonempty).comp
        (measurable_yRightNearFavoriteWinnerBases m k beta))
  fin_cases j <;>
    simp only [yCanonicalProp49BranchScreen, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.tail_cons] <;>
    measurability

/-- A nonempty `Y` near-favourite set has a winner in one of its two
terminal phases. -/
theorem lowScaleScreenEvent_y_subset_canonicalProp49BranchScreens
    (m k : ℕ) (beta : ℝ) :
    lowScaleScreenEvent (sourceCanonicalProfiles yIndex)
        (canonicalCStar yIndex) yIndex m k beta ⊆
      ⋃ j, yCanonicalProp49BranchScreen m k beta j := by
  intro s hs
  have hnear : (nearFavoriteSites yIndex s m k beta).Nonempty := hs.1
  have hcard := y_nearFavorite_card_le_two_mul_winners s m k beta
  have hsum : 0 <
      (yLeftNearFavoriteWinnerBases s m k beta).card +
        (yRightNearFavoriteWinnerBases s m k beta).card := by
    have hnearCard : 0 < (nearFavoriteSites yIndex s m k beta).card :=
      Finset.card_pos.mpr hnear
    omega
  by_cases hleft : (yLeftNearFavoriteWinnerBases s m k beta).Nonempty
  · refine Set.mem_iUnion.mpr ⟨(0 : Fin 4), ?_⟩
    change s ∈
      lowScaleScreenEvent (sourceCanonicalProfiles yIndex)
          (canonicalCStar yIndex) yIndex m k beta ∩
        {s | (yLeftNearFavoriteWinnerBases s m k beta).Nonempty}
    exact ⟨hs, hleft⟩
  · have hleftZero : (yLeftNearFavoriteWinnerBases s m k beta).card = 0 :=
      Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp hleft)
    have hright : (yRightNearFavoriteWinnerBases s m k beta).Nonempty :=
      Finset.card_pos.mp (by omega)
    refine Set.mem_iUnion.mpr ⟨(1 : Fin 4), ?_⟩
    change s ∈
      lowScaleScreenEvent (sourceCanonicalProfiles yIndex)
          (canonicalCStar yIndex) yIndex m k beta ∩
        {s | (yRightNearFavoriteWinnerBases s m k beta).Nonempty}
    exact ⟨hs, hright⟩

/-- Source-side `Y` screens whose reflection gives the genuine `Y'` screen.
The full-screen factor is pulled back from `Y'`; no invariance of the fixed
temporal deletion profile under the column reflection is assumed. -/
noncomputable def yPrimeSourceCanonicalProp49BranchScreen
    (m k : ℕ) (beta : ℝ) : Fin 4 → Set Path :=
  let fullPrime := reflectPath ⁻¹'
    lowScaleScreenEvent (sourceCanonicalProfiles yIndex')
      (canonicalCStar yIndex') yIndex' m k beta
  let left := {s | (yLeftNearFavoriteWinnerBases s m k beta).Nonempty}
  let right := {s | (yRightNearFavoriteWinnerBases s m k beta).Nonempty}
  ![fullPrime ∩ left, fullPrime ∩ right, ∅, ∅]

theorem measurableSet_yPrimeSourceCanonicalProp49BranchScreen
    (m k : ℕ) (beta : ℝ) (j : Fin 4) :
    MeasurableSet (yPrimeSourceCanonicalProp49BranchScreen m k beta j) := by
  have hfull : MeasurableSet (reflectPath ⁻¹'
      lowScaleScreenEvent (sourceCanonicalProfiles yIndex')
        (canonicalCStar yIndex') yIndex' m k beta) :=
    (measurableSet_lowScaleScreenEvent _ _ _ _ _ _).preimage
      measurable_reflectPath
  have hleft : MeasurableSet {s : Path |
      (yLeftNearFavoriteWinnerBases s m k beta).Nonempty} :=
    measurableSet_setOfPred.mpr
      ((measurable_of_countable fun F : Finset Site ↦ F.Nonempty).comp
        (measurable_yLeftNearFavoriteWinnerBases m k beta))
  have hright : MeasurableSet {s : Path |
      (yRightNearFavoriteWinnerBases s m k beta).Nonempty} :=
    measurableSet_setOfPred.mpr
      ((measurable_of_countable fun F : Finset Site ↦ F.Nonempty).comp
        (measurable_yRightNearFavoriteWinnerBases m k beta))
  fin_cases j <;>
    simp only [yPrimeSourceCanonicalProp49BranchScreen,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.tail_cons] <;>
    measurability

/-- The canonical branch screen at an arbitrary pairing.  Checkerboard
screens are inverse quarter-turn images of the X-east screens; `Y'` is the
inverse reflection image of the assembled two-phase `Y` screens. -/
noncomputable def canonicalProp49BranchScreen
    (m : ℕ) (i : Fin 6) (a : AlphaTriple) (r : StageIndex) :
    Fin 4 → Set Path :=
  let k := stageNumber r
  let beta := alphaValue (tripleAlphaIndex a r) + delta
  if hi : i.1 < 4 then
    fun j ↦ orientPath (rotationInverseDir ⟨i.1, hi⟩) ⁻¹'
      (xEastCanonicalProp49BranchScreen m k beta j)
  else if hy : i = yIndex then
    yCanonicalProp49BranchScreen m k beta
  else
    fun j ↦ reflectPath ⁻¹'
      (yPrimeSourceCanonicalProp49BranchScreen m k beta j)

@[simp] theorem canonicalProp49BranchScreen_xIndex
    (m : ℕ) (d : Dir) (a : AlphaTriple) (r : StageIndex) (j : Fin 4) :
    canonicalProp49BranchScreen m (xIndex d) a r j =
      orientPath (rotationInverseDir d) ⁻¹'
        xEastCanonicalProp49BranchScreen m (stageNumber r)
          (alphaValue (tripleAlphaIndex a r) + delta) j := by
  simp [canonicalProp49BranchScreen, xIndex]

@[simp] theorem canonicalProp49BranchScreen_yIndex
    (m : ℕ) (a : AlphaTriple) (r : StageIndex) (j : Fin 4) :
    canonicalProp49BranchScreen m yIndex a r j =
      yCanonicalProp49BranchScreen m (stageNumber r)
        (alphaValue (tripleAlphaIndex a r) + delta) j := by
  simp [canonicalProp49BranchScreen, yIndex]

@[simp] theorem canonicalProp49BranchScreen_yIndex'
    (m : ℕ) (a : AlphaTriple) (r : StageIndex) (j : Fin 4) :
    canonicalProp49BranchScreen m yIndex' a r j =
      reflectPath ⁻¹'
        yPrimeSourceCanonicalProp49BranchScreen m (stageNumber r)
          (alphaValue (tripleAlphaIndex a r) + delta) j := by
  simp [canonicalProp49BranchScreen, yIndex, yIndex']

theorem measurableSet_canonicalProp49BranchScreen
    (m : ℕ) (i : Fin 6) (a : AlphaTriple) (r : StageIndex)
    (j : Fin 4) :
    MeasurableSet (canonicalProp49BranchScreen m i a r j) := by
  classical
  unfold canonicalProp49BranchScreen
  split
  · exact (measurableSet_xEastCanonicalProp49BranchScreen _ _ _ _).preimage
      (measurable_orientPath _)
  split
  · exact measurableSet_yCanonicalProp49BranchScreen _ _ _ _
  · exact
      (measurableSet_yPrimeSourceCanonicalProp49BranchScreen _ _ _ _).preimage
        measurable_reflectPath

theorem measurableSet_of_preimage_orientPath
    (d : Dir) {S : Set Path}
    (hS : MeasurableSet (orientPath (rotationInverseDir d) ⁻¹' S)) :
    MeasurableSet S := by
  have hpre := hS.preimage (measurable_orientPath d)
  have heq : orientPath d ⁻¹'
      (orientPath (rotationInverseDir d) ⁻¹' S) = S := by
    ext s
    simp only [Set.mem_preimage, orientPath_rotationInverseDir_left]
  rw [heq] at hpre
  exact hpre

theorem measurableSet_of_preimage_reflectPath
    {S : Set Path} (hS : MeasurableSet (reflectPath ⁻¹' S)) :
    MeasurableSet S := by
  have hpre := hS.preimage measurable_reflectPath
  have heq : reflectPath ⁻¹' (reflectPath ⁻¹' S) = S := by
    ext s
    simp only [Set.mem_preimage, reflectPath_reflectPath]
  rw [heq] at hpre
  exact hpre

theorem lowScaleScreenEvent_x_orient_iff
    (d : Dir) (s : Path) (m k : ℕ) (beta : ℝ) :
    s ∈ lowScaleScreenEvent (sourceCanonicalProfiles (xIndex east))
        (canonicalCStar (xIndex east)) (xIndex east) m k beta ↔
      orientPath d s ∈
        lowScaleScreenEvent (sourceCanonicalProfiles (xIndex d))
          (canonicalCStar (xIndex d)) (xIndex d) m k beta := by
  simp only [lowScaleScreenEvent, Set.mem_setOf_eq,
    sourceCanonicalProfiles_xIndex, canonicalCStar_xIndex]
  constructor
  · rintro ⟨hnear, htheta, hcard⟩
    refine ⟨?_,
      (stoppedThetaSites_empty_x_orient_iff d s m k 10).mp htheta, ?_⟩
    · rw [nearFavoriteSites_x_orient]
      simpa only [Finset.image_nonempty] using hnear
    · simpa only [nearFavoriteSites_x_orient_card] using hcard
  · rintro ⟨hnear, htheta, hcard⟩
    refine ⟨?_,
      (stoppedThetaSites_empty_x_orient_iff d s m k 10).mpr htheta, ?_⟩
    · rw [nearFavoriteSites_x_orient] at hnear
      simpa only [Finset.image_nonempty] using hnear
    · simpa only [nearFavoriteSites_x_orient_card] using hcard

/-- The branch-screen cover in Proposition 4.9 is automatic for the fixed
four-branch family at every pairing and every positive source scale. -/
theorem canonicalProp49BranchScreen_cover
    (m : ℕ) (i : Fin 6) (a : AlphaTriple) (r : StageIndex)
    (hm : 0 < m) :
    prop47History sourceCanonicalProfiles canonicalCStar m i a r.1 ∩
        lowScaleScreenEvent (sourceCanonicalProfiles i) (canonicalCStar i)
          i m (stageNumber r)
            (alphaValue (tripleAlphaIndex a r) + delta) ⊆
      ⋃ j, prop47History sourceCanonicalProfiles canonicalCStar m i a r.1 ∩
        canonicalProp49BranchScreen m i a r j := by
  intro s hs
  have hk : 0 < stageNumber r := by
    unfold stageNumber
    omega
  by_cases hi : i.1 < 4
  · let d : Dir := ⟨i.1, hi⟩
    have hid : i = xIndex d := by
      apply Fin.ext
      rfl
    let t := orientPath (rotationInverseDir d) s
    have htScreen : t ∈
        lowScaleScreenEvent (sourceCanonicalProfiles (xIndex east))
          (canonicalCStar (xIndex east)) (xIndex east) m (stageNumber r)
            (alphaValue (tripleAlphaIndex a r) + delta) := by
      have h := lowScaleScreenEvent_x_orient_iff d t m (stageNumber r)
        (alphaValue (tripleAlphaIndex a r) + delta)
      have hs' : s ∈
          lowScaleScreenEvent (sourceCanonicalProfiles (xIndex d))
            (canonicalCStar (xIndex d)) (xIndex d) m (stageNumber r)
              (alphaValue (tripleAlphaIndex a r) + delta) := by
        simpa only [hid] using hs.2
      have htEq : orientPath d t = s := by
        simp only [t, orientPath_rotationInverseDir_right]
      exact h.mpr (by simpa only [htEq] using hs')
    rcases Set.mem_iUnion.mp
        (lowScaleScreenEvent_xEast_subset_canonicalProp49BranchScreens
          m (stageNumber r) _ hm hk htScreen) with ⟨j, hj⟩
    refine Set.mem_iUnion.mpr ⟨j, hs.1, ?_⟩
    simpa only [canonicalProp49BranchScreen, hi, ↓reduceDIte,
      Set.mem_preimage, d, t]
      using hj
  · have hi4 : 4 ≤ i.1 := by omega
    by_cases hy : i = yIndex
    · have hsY : s ∈
          lowScaleScreenEvent (sourceCanonicalProfiles yIndex)
            (canonicalCStar yIndex) yIndex m (stageNumber r)
              (alphaValue (tripleAlphaIndex a r) + delta) := by
        simpa only [hy] using hs.2
      rcases Set.mem_iUnion.mp
          (lowScaleScreenEvent_y_subset_canonicalProp49BranchScreens
            m (stageNumber r) _ hsY) with ⟨j, hj⟩
      refine Set.mem_iUnion.mpr ⟨j, hs.1, ?_⟩
      simp only [canonicalProp49BranchScreen, hi, hy, ↓reduceDIte]
      exact hj
    · have hy' : i = yIndex' := by
        apply Fin.ext
        change i.1 = 5
        have hi6 := i.2
        have hne4 : i.1 ≠ 4 := by
          intro h4
          apply hy
          apply Fin.ext
          exact h4
        omega
      let t := reflectPath s
      have hsY' : s ∈
          lowScaleScreenEvent (sourceCanonicalProfiles yIndex')
            (canonicalCStar yIndex') yIndex' m (stageNumber r)
              (alphaValue (tripleAlphaIndex a r) + delta) := by
        simpa only [hy'] using hs.2
      have htFull : t ∈ reflectPath ⁻¹'
          lowScaleScreenEvent (sourceCanonicalProfiles yIndex')
            (canonicalCStar yIndex') yIndex' m (stageNumber r)
              (alphaValue (tripleAlphaIndex a r) + delta) := by
        simpa only [t, Set.mem_preimage, reflectPath_reflectPath] using hsY'
      have htNear : (nearFavoriteSites yIndex t m (stageNumber r)
          (alphaValue (tripleAlphaIndex a r) + delta)).Nonempty := by
        have hnear : (nearFavoriteSites yIndex' (reflectPath t) m
            (stageNumber r)
              (alphaValue (tripleAlphaIndex a r) + delta)).Nonempty := by
          simpa only [t, reflectPath_reflectPath] using hsY'.1
        rw [nearFavoriteSites_y_reflect] at hnear
        simpa only [Finset.image_nonempty] using hnear
      have hcard := y_nearFavorite_card_le_two_mul_winners t m
        (stageNumber r) (alphaValue (tripleAlphaIndex a r) + delta)
      have hsum : 0 <
          (yLeftNearFavoriteWinnerBases t m (stageNumber r)
              (alphaValue (tripleAlphaIndex a r) + delta)).card +
            (yRightNearFavoriteWinnerBases t m (stageNumber r)
              (alphaValue (tripleAlphaIndex a r) + delta)).card := by
        have hnearCard : 0 <
            (nearFavoriteSites yIndex t m (stageNumber r)
              (alphaValue (tripleAlphaIndex a r) + delta)).card :=
          Finset.card_pos.mpr htNear
        omega
      have hwinner :
          (yLeftNearFavoriteWinnerBases t m (stageNumber r)
              (alphaValue (tripleAlphaIndex a r) + delta)).Nonempty ∨
            (yRightNearFavoriteWinnerBases t m (stageNumber r)
              (alphaValue (tripleAlphaIndex a r) + delta)).Nonempty := by
        by_cases hleft : (yLeftNearFavoriteWinnerBases t m (stageNumber r)
            (alphaValue (tripleAlphaIndex a r) + delta)).Nonempty
        · exact Or.inl hleft
        · right
          have hzero : (yLeftNearFavoriteWinnerBases t m (stageNumber r)
              (alphaValue (tripleAlphaIndex a r) + delta)).card = 0 :=
            Finset.card_eq_zero.mpr
              (Finset.not_nonempty_iff_eq_empty.mp hleft)
          exact Finset.card_pos.mp (by omega)
      rcases hwinner with hleft | hright
      · let j : Fin 4 := 0
        refine Set.mem_iUnion.mpr ⟨j, hs.1, ?_⟩
        simp only [canonicalProp49BranchScreen, hi, hy, ↓reduceDIte]
        change reflectPath s ∈
          yPrimeSourceCanonicalProp49BranchScreen m (stageNumber r)
            (alphaValue (tripleAlphaIndex a r) + delta) j
        change t ∈ _ ∩ _
        exact ⟨htFull, hleft⟩
      · let j : Fin 4 := 1
        refine Set.mem_iUnion.mpr ⟨j, hs.1, ?_⟩
        simp only [canonicalProp49BranchScreen, hi, hy, ↓reduceDIte]
        change reflectPath s ∈
          yPrimeSourceCanonicalProp49BranchScreen m (stageNumber r)
            (alphaValue (tripleAlphaIndex a r) + delta) j
        change t ∈ _ ∩ _
        exact ⟨htFull, hright⟩

/-- Strongest source-facing Proposition-4.9 input currently exposed.

For each source branch a natural-valued code records the raw stopped data.
Its fibers automatically form a disjoint partition of path space.  The code
itself need not be measurable: every history-refined fiber used below is
either empty or comes with its own measurable stopped-atom identification. -/
def Prop47StoppedProfileProp49CanonicalCodedFiniteBranchEstimate
    (branchCount localCoeff : ℕ)
    (branchScreen : ℕ → Fin 6 → AlphaTriple → StageIndex →
      Fin branchCount → Set Path)
    (rawCode : ℕ → Fin 6 → AlphaTriple → StageIndex →
      Fin branchCount → Path → ℕ) : Prop :=
  ∀ᶠ m : ℕ in atTop, ∀ i a (r : StageIndex),
    alphaValue (tripleAlphaIndex a r) ≤ kappaTwo →
    let history := prop47History sourceCanonicalProfiles canonicalCStar
      m i a r.1
    let fullScreen := HLOZProp47SourceObjects.lowScaleScreenEvent
      (sourceCanonicalProfiles i) (canonicalCStar i) i m (stageNumber r)
        (alphaValue (tripleAlphaIndex a r) + delta)
    let screen := branchScreen m i a r
    history ∩ fullScreen ⊆ ⋃ j, history ∩ screen j ∧
    ∀ j eta (c : Fin (stageNumber r) → Site),
      let atom := orderedProfileHistoryPathAtom sourceCanonicalProfiles
        canonicalCStar m i a r c
          (rawCodeFiber (rawCode m i a r j) eta)
      atom.Nonempty →
        MeasurableSet atom ∧ RefinedAtomScreenEstimate
          (orderedProfileHistoryPathAtom sourceCanonicalProfiles canonicalCStar
            m i a r c (rawCodeFiber (rawCode m i a r j) eta)) (screen j)
          (sourceProp49ScreenRate m localCoeff
            (alphaValue (tripleAlphaIndex a r)))

/-- Stronger literal coded source interface in which the first screening
stage for all four checkerboard orientations and the unreflected `Y` column
is discharged by the checked stopped laws and the relevant source
identifications.

For a nonempty first-stage checkerboard fibre, the source only identifies
the raw fibre and branch screen with inverse images of one of the four
literal X-east parity/winner atoms and its screen.  The ordered one-site
history and refined narrow-band estimate are transported internally.  A
first-stage `Y` fibre is similarly identified with one of the two literal
terminal phases, together with the deterministic threshold/creation-set
facts recorded by `YStageZeroProp49AtomData`.  At later checkerboard stages
the source may use either the checked full-chronological-complement tower or
the literal unnormalized Proposition-4.9 inequality on the ordered-history
atom.  For the unreflected column pairing, Proposition 4.9 may be
exposed either in its literal local form--the unnormalized screen inequality
on the actual ordered-history atom--or through the deterministic statement
that the checked full chronological complement determines that history on
the coarse atom.  The latter route uses the profile-generic three-factor law
internally.  The reflected `Y'` pairing has the same alternative after the
entire joint law and complement statistic are reflected.  Its fibre condition
is stated against the actual `Y'` history, so no equality of later `Y` and
`Y'` histories is asserted. -/
def Prop47StoppedProfileProp49CanonicalCodedLaterStageEstimateAt
    (m branchCount localCoeff : ℕ)
    (branchScreen : Fin 6 → AlphaTriple → StageIndex →
      Fin branchCount → Set Path)
    (rawCode : Fin 6 → AlphaTriple → StageIndex →
      Fin branchCount → Path → ℕ) : Prop :=
  ∀ i a (r : StageIndex),
    alphaValue (tripleAlphaIndex a r) ≤ kappaTwo →
    let history := prop47History sourceCanonicalProfiles canonicalCStar
      m i a r.1
    let fullScreen := HLOZProp47SourceObjects.lowScaleScreenEvent
      (sourceCanonicalProfiles i) (canonicalCStar i) i m (stageNumber r)
        (alphaValue (tripleAlphaIndex a r) + delta)
    let screen := branchScreen i a r
    history ∩ fullScreen ⊆ ⋃ j, history ∩ screen j ∧
    ∀ j eta (c : Fin (stageNumber r) → Site),
      (orderedProfileHistoryPathAtom sourceCanonicalProfiles canonicalCStar
        m i a r c (rawCodeFiber (rawCode i a r j) eta)).Nonempty →
      (((i.1 < 4 ∧ r = 0) →
          ∃ d : Dir, i = xIndex d ∧
            ∃ eastScreen : Set Path, MeasurableSet eastScreen ∧
              ∃ D : XEastStageZeroProp49AtomData m localCoeff
                  (alphaValue (tripleAlphaIndex a r)) eastScreen,
                rawCodeFiber (rawCode i a r j) eta =
                    orientPath (rotationInverseDir d) ⁻¹' D.atom ∧
                  screen j =
                    orientPath (rotationInverseDir d) ⁻¹' eastScreen) ∧
        ((i = yIndex ∧ r = 0) →
          ∃ yScreen : Set Path,
            ∃ D : YStageZeroProp49AtomData m localCoeff
                (alphaValue (tripleAlphaIndex a r)) yScreen,
              rawCodeFiber (rawCode i a r j) eta = D.atom ∧
                screen j = yScreen) ∧
        ((i = yIndex' ∧ r = 0) →
          ∃ yScreen : Set Path, MeasurableSet yScreen ∧
            ∃ D : YStageZeroProp49AtomData m localCoeff
                (alphaValue (tripleAlphaIndex a r)) yScreen,
              rawCodeFiber (rawCode i a r j) eta =
                  reflectPath ⁻¹' D.atom ∧
                screen j = reflectPath ⁻¹' yScreen) ∧
        ((i.1 < 4 ∧ r ≠ 0) →
          ∃ d : Dir, i = xIndex d ∧
            ∃ eastScreen : Set Path, MeasurableSet eastScreen ∧
              ∃ D : ConcreteStoppedProp49AtomData m (stageNumber r)
                  localCoeff (alphaValue (tripleAlphaIndex a r)) eastScreen,
                rawCodeFiber (rawCode i a r j) eta =
                    orientPath (rotationInverseDir d) ⁻¹' D.atom ∧
                  screen j =
                    orientPath (rotationInverseDir d) ⁻¹' eastScreen ∧
                  (HLOZStoppedFullComplement.ConcreteStoppedProp49AtomData.FullComplementHistoryDetermined
                      D (profiles := sourceCanonicalProfiles)
                        (cStar := canonicalCStar) (i := xIndex east)
                          (a := a) (r := r) (rotateCreationTuple d c) ∨
                    (r = 1 ∧
                      (alphaValue (tripleAlphaIndex a 0) ≤ kappaTwo →
                        HLOZStoppedFullComplement.ConcreteStoppedProp49AtomData.FullComplementStageZeroLowScaleDetermined
                          (r := r) D (profiles := sourceCanonicalProfiles)
                            (cStar := canonicalCStar) (a := a))) ∨
                    RefinedAtomScreenEstimate
                      (orderedProfileHistoryPathAtom sourceCanonicalProfiles
                        canonicalCStar m (xIndex east) a r
                          (rotateCreationTuple d c) D.atom)
                      eastScreen
                      (sourceProp49ScreenRate m localCoeff
                        (alphaValue (tripleAlphaIndex a r))))) ∧
        ((i = yIndex ∧ r ≠ 0) →
          ∃ yScreen : Set Path,
            ∃ D : YLaterStageProp49AtomData m localCoeff
                (alphaValue (tripleAlphaIndex a r)) yScreen a r c,
              rawCodeFiber (rawCode i a r j) eta = D.atom ∧
                screen j = yScreen) ∧
        ((i = yIndex' ∧ r ≠ 0) →
          ∃ yScreen : Set Path,
            ∃ D : YPrimeLaterStageProp49AtomData m localCoeff
                (alphaValue (tripleAlphaIndex a r)) yScreen a r c,
              rawCodeFiber (rawCode i a r j) eta = D.atom ∧
                screen j = reflectPath ⁻¹' yScreen))

/-- Stronger source-facing local interface with the branch screens fixed
canonically.  The source supplies only a stopped-data code and the
nonempty-fibre identifications/estimates.  Neither code measurability nor
branch-screen measurability is a field: the latter follows from the literal
finite winner sets and the former is unnecessary because every used fibre
is identified with a measurable stopped atom.  The full-screen cover is the
deterministic theorem `canonicalProp49BranchScreen_cover`. -/
def Prop47StoppedProfileProp49CanonicalScreensLocalEstimateAt
    (m localCoeff : ℕ)
    (rawCode : Fin 6 → AlphaTriple → StageIndex →
      Fin 4 → Path → ℕ) : Prop :=
  ∀ i a (r : StageIndex),
    alphaValue (tripleAlphaIndex a r) ≤ kappaTwo →
    let screen := canonicalProp49BranchScreen m i a r
    ∀ j eta (c : Fin (stageNumber r) → Site),
      (orderedProfileHistoryPathAtom sourceCanonicalProfiles canonicalCStar
        m i a r c (rawCodeFiber (rawCode i a r j) eta)).Nonempty →
      (((i.1 < 4 ∧ r = 0) →
          ∃ d : Dir, i = xIndex d ∧
            ∃ eastScreen : Set Path,
              ∃ D : XEastStageZeroProp49AtomData m localCoeff
                  (alphaValue (tripleAlphaIndex a r)) eastScreen,
                rawCodeFiber (rawCode i a r j) eta =
                    orientPath (rotationInverseDir d) ⁻¹' D.atom ∧
                  screen j =
                    orientPath (rotationInverseDir d) ⁻¹' eastScreen) ∧
        ((i = yIndex ∧ r = 0) →
          ∃ yScreen : Set Path,
            ∃ D : YStageZeroProp49AtomData m localCoeff
                (alphaValue (tripleAlphaIndex a r)) yScreen,
              rawCodeFiber (rawCode i a r j) eta = D.atom ∧
                screen j = yScreen) ∧
        ((i = yIndex' ∧ r = 0) →
          ∃ yScreen : Set Path,
            ∃ D : YStageZeroProp49AtomData m localCoeff
                (alphaValue (tripleAlphaIndex a r)) yScreen,
              rawCodeFiber (rawCode i a r j) eta =
                  reflectPath ⁻¹' D.atom ∧
                screen j = reflectPath ⁻¹' yScreen) ∧
        ((i.1 < 4 ∧ r ≠ 0) →
          ∃ d : Dir, i = xIndex d ∧
            ∃ eastScreen : Set Path,
              ∃ D : ConcreteStoppedProp49AtomData m (stageNumber r)
                  localCoeff (alphaValue (tripleAlphaIndex a r)) eastScreen,
                rawCodeFiber (rawCode i a r j) eta =
                    orientPath (rotationInverseDir d) ⁻¹' D.atom ∧
                  screen j =
                    orientPath (rotationInverseDir d) ⁻¹' eastScreen ∧
                  (HLOZStoppedFullComplement.ConcreteStoppedProp49AtomData.FullComplementHistoryDetermined
                      D (profiles := sourceCanonicalProfiles)
                        (cStar := canonicalCStar) (i := xIndex east)
                          (a := a) (r := r) (rotateCreationTuple d c) ∨
                    (r = 1 ∧
                      (alphaValue (tripleAlphaIndex a 0) ≤ kappaTwo →
                        HLOZStoppedFullComplement.ConcreteStoppedProp49AtomData.FullComplementStageZeroLowScaleDetermined
                          (r := r) D (profiles := sourceCanonicalProfiles)
                            (cStar := canonicalCStar) (a := a))) ∨
                    RefinedAtomScreenEstimate
                      (orderedProfileHistoryPathAtom sourceCanonicalProfiles
                        canonicalCStar m (xIndex east) a r
                          (rotateCreationTuple d c) D.atom)
                      eastScreen
                      (sourceProp49ScreenRate m localCoeff
                        (alphaValue (tripleAlphaIndex a r))))) ∧
        ((i = yIndex ∧ r ≠ 0) →
          ∃ yScreen : Set Path,
            ∃ D : YLaterStageProp49AtomData m localCoeff
                (alphaValue (tripleAlphaIndex a r)) yScreen a r c,
              rawCodeFiber (rawCode i a r j) eta = D.atom ∧
                screen j = yScreen) ∧
        ((i = yIndex' ∧ r ≠ 0) →
          ∃ yScreen : Set Path,
            ∃ D : YPrimeLaterStageProp49AtomData m localCoeff
                (alphaValue (tripleAlphaIndex a r)) yScreen a r c,
              rawCodeFiber (rawCode i a r j) eta = D.atom ∧
                screen j = reflectPath ⁻¹' yScreen))

/-- The fully canonical local source interface.  Besides fixing the global
branch screens, this also fixes their X-east/Y source representatives.
Consequently callers no longer choose auxiliary screen sets, checkerboard
directions, or prove the six rotation/reflection identities: for `i.1 < 4`
the direction is canonically `⟨i.1, hi⟩`, while the screen identities are
definitional consequences of `canonicalProp49BranchScreen`. -/
def Prop47StoppedProfileProp49CanonicalLiteralLocalEstimateAt
    (m localCoeff : ℕ)
    (rawCode : Fin 6 → AlphaTriple → StageIndex →
      Fin 4 → Path → ℕ) : Prop :=
  ∀ i a (r : StageIndex),
    alphaValue (tripleAlphaIndex a r) ≤ kappaTwo →
    let beta := alphaValue (tripleAlphaIndex a r) + delta
    ∀ j eta (c : Fin (stageNumber r) → Site),
      (orderedProfileHistoryPathAtom sourceCanonicalProfiles canonicalCStar
        m i a r c (rawCodeFiber (rawCode i a r j) eta)).Nonempty →
      (((hcase : i.1 < 4 ∧ r = 0) →
          ∃ D : XEastStageZeroProp49AtomData m localCoeff
              (alphaValue (tripleAlphaIndex a r))
              (xEastCanonicalProp49BranchScreen m (stageNumber r) beta j),
            rawCodeFiber (rawCode i a r j) eta =
              orientPath (rotationInverseDir ⟨i.1, hcase.1⟩) ⁻¹' D.atom) ∧
        ((i = yIndex ∧ r = 0) →
          ∃ D : YStageZeroProp49AtomData m localCoeff
              (alphaValue (tripleAlphaIndex a r))
              (yCanonicalProp49BranchScreen m (stageNumber r) beta j),
            rawCodeFiber (rawCode i a r j) eta = D.atom) ∧
        ((i = yIndex' ∧ r = 0) →
          ∃ D : YStageZeroProp49AtomData m localCoeff
              (alphaValue (tripleAlphaIndex a r))
              (yPrimeSourceCanonicalProp49BranchScreen
                m (stageNumber r) beta j),
            rawCodeFiber (rawCode i a r j) eta =
              reflectPath ⁻¹' D.atom) ∧
        ((hcase : i.1 < 4 ∧ r ≠ 0) →
          ∃ D : ConcreteStoppedProp49AtomData m (stageNumber r)
                localCoeff (alphaValue (tripleAlphaIndex a r))
                (xEastCanonicalProp49BranchScreen
                  m (stageNumber r) beta j),
            rawCodeFiber (rawCode i a r j) eta =
                orientPath (rotationInverseDir ⟨i.1, hcase.1⟩) ⁻¹' D.atom ∧
                (HLOZStoppedFullComplement.ConcreteStoppedProp49AtomData.FullComplementHistoryDetermined
                    D (profiles := sourceCanonicalProfiles)
                      (cStar := canonicalCStar) (i := xIndex east)
                        (a := a) (r := r)
                          (rotateCreationTuple ⟨i.1, hcase.1⟩ c) ∨
                  (r = 1 ∧
                    (alphaValue (tripleAlphaIndex a 0) ≤ kappaTwo →
                      HLOZStoppedFullComplement.ConcreteStoppedProp49AtomData.FullComplementStageZeroLowScaleDetermined
                        (r := r) D (profiles := sourceCanonicalProfiles)
                          (cStar := canonicalCStar) (a := a))) ∨
                  RefinedAtomScreenEstimate
                    (orderedProfileHistoryPathAtom sourceCanonicalProfiles
                      canonicalCStar m (xIndex east) a r
                        (rotateCreationTuple ⟨i.1, hcase.1⟩ c) D.atom)
                    (xEastCanonicalProp49BranchScreen
                      m (stageNumber r) beta j)
                    (sourceProp49ScreenRate m localCoeff
                      (alphaValue (tripleAlphaIndex a r))))) ∧
        ((i = yIndex ∧ r ≠ 0) →
          ∃ D : YLaterStageProp49AtomData m localCoeff
              (alphaValue (tripleAlphaIndex a r))
              (yCanonicalProp49BranchScreen m (stageNumber r) beta j) a r c,
            rawCodeFiber (rawCode i a r j) eta = D.atom) ∧
        ((i = yIndex' ∧ r ≠ 0) →
          ∃ D : YPrimeLaterStageProp49AtomData m localCoeff
              (alphaValue (tripleAlphaIndex a r))
              (yPrimeSourceCanonicalProp49BranchScreen
                m (stageNumber r) beta j) a r c,
            rawCodeFiber (rawCode i a r j) eta = D.atom))

/-- Exactly-one-case form of the canonical literal Proposition-4.9 source.

The six implication fields above are convenient for the generic connector,
but a source fibre belongs to exactly one pairing/stage case.  Moreover a
fibre disjoint from its canonical screen contributes zero to the desired
inequality.  This interface therefore requests the single active package only
when the ordered fibre meets that screen: an X package when `i.1 < 4`, a Y
package when `i = yIndex`, and otherwise the reflected-Y package, split at
stage zero. -/
def Prop47StoppedProfileProp49CanonicalActiveLiteralLocalEstimateAt
    (m localCoeff : ℕ)
    (rawCode : Fin 6 → AlphaTriple → StageIndex →
      Fin 4 → Path → ℕ) : Prop :=
  ∀ i a (r : StageIndex),
    alphaValue (tripleAlphaIndex a r) ≤ kappaTwo →
    let beta := alphaValue (tripleAlphaIndex a r) + delta
    ∀ j eta (c : Fin (stageNumber r) → Site),
      (orderedProfileHistoryPathAtom sourceCanonicalProfiles canonicalCStar
          m i a r c (rawCodeFiber (rawCode i a r j) eta) ∩
        canonicalProp49BranchScreen m i a r j).Nonempty →
      if hx : i.1 < 4 then
        if r = 0 then
          ∃ D : XEastStageZeroProp49AtomData m localCoeff
              (alphaValue (tripleAlphaIndex a r))
              (xEastCanonicalProp49BranchScreen m (stageNumber r) beta j),
            rawCodeFiber (rawCode i a r j) eta =
              orientPath (rotationInverseDir ⟨i.1, hx⟩) ⁻¹' D.atom
        else
          ∃ D : ConcreteStoppedProp49AtomData m (stageNumber r)
                localCoeff (alphaValue (tripleAlphaIndex a r))
                (xEastCanonicalProp49BranchScreen
                  m (stageNumber r) beta j),
            rawCodeFiber (rawCode i a r j) eta =
                orientPath (rotationInverseDir ⟨i.1, hx⟩) ⁻¹' D.atom ∧
              (HLOZStoppedFullComplement.ConcreteStoppedProp49AtomData.FullComplementHistoryDetermined
                    D (profiles := sourceCanonicalProfiles)
                      (cStar := canonicalCStar) (i := xIndex east)
                        (a := a) (r := r)
                          (rotateCreationTuple ⟨i.1, hx⟩ c) ∨
                (r = 1 ∧
                  (alphaValue (tripleAlphaIndex a 0) ≤ kappaTwo →
                    HLOZStoppedFullComplement.ConcreteStoppedProp49AtomData.FullComplementStageZeroLowScaleDetermined
                      (r := r) D (profiles := sourceCanonicalProfiles)
                        (cStar := canonicalCStar) (a := a))) ∨
                RefinedAtomScreenEstimate
                  (orderedProfileHistoryPathAtom sourceCanonicalProfiles
                    canonicalCStar m (xIndex east) a r
                      (rotateCreationTuple ⟨i.1, hx⟩ c) D.atom)
                  (xEastCanonicalProp49BranchScreen
                    m (stageNumber r) beta j)
                  (sourceProp49ScreenRate m localCoeff
                    (alphaValue (tripleAlphaIndex a r))))
      else if i = yIndex then
        if r = 0 then
          ∃ D : YStageZeroProp49AtomData m localCoeff
              (alphaValue (tripleAlphaIndex a r))
              (yCanonicalProp49BranchScreen m (stageNumber r) beta j),
            rawCodeFiber (rawCode i a r j) eta = D.atom
        else
          ∃ D : YLaterStageProp49AtomData m localCoeff
              (alphaValue (tripleAlphaIndex a r))
              (yCanonicalProp49BranchScreen m (stageNumber r) beta j) a r c,
            rawCodeFiber (rawCode i a r j) eta = D.atom
      else if r = 0 then
        ∃ D : YStageZeroProp49AtomData m localCoeff
            (alphaValue (tripleAlphaIndex a r))
            (yPrimeSourceCanonicalProp49BranchScreen
              m (stageNumber r) beta j),
          rawCodeFiber (rawCode i a r j) eta = reflectPath ⁻¹' D.atom
      else
        ∃ D : YPrimeLaterStageProp49AtomData m localCoeff
            (alphaValue (tripleAlphaIndex a r))
            (yPrimeSourceCanonicalProp49BranchScreen
              m (stageNumber r) beta j) a r c,
          rawCodeFiber (rawCode i a r j) eta = D.atom

/-- Forgetting that the source screens were fixed supplies the preceding
canonical-screen interface. -/
theorem prop47StoppedProfileProp49CanonicalScreensLocalEstimateAt_of_literal
    (m localCoeff : ℕ)
    (rawCode : Fin 6 → AlphaTriple → StageIndex → Fin 4 → Path → ℕ)
    (hsource : Prop47StoppedProfileProp49CanonicalLiteralLocalEstimateAt
      m localCoeff rawCode) :
    Prop47StoppedProfileProp49CanonicalScreensLocalEstimateAt
      m localCoeff rawCode := by
  intro i a r halpha
  dsimp only
  intro j eta c hnonempty
  rcases hsource i a r halpha j eta c hnonempty with
    ⟨hxZero, hyZero, hyPrimeZero, hxLater, hyLater, hyPrimeLater⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro hcase
    let d : Dir := ⟨i.1, hcase.1⟩
    have hi : i = xIndex d := by
      apply Fin.ext
      rfl
    rcases hxZero hcase with ⟨D, hatom⟩
    refine ⟨d, hi,
      xEastCanonicalProp49BranchScreen m (stageNumber r)
        (alphaValue (tripleAlphaIndex a r) + delta) j,
      D, hatom, ?_⟩
    exact (congrArg (fun i ↦ canonicalProp49BranchScreen m i a r j) hi).trans
      (canonicalProp49BranchScreen_xIndex m d a r j)
  · intro hcase
    rcases hyZero hcase with ⟨D, hatom⟩
    refine ⟨yCanonicalProp49BranchScreen m (stageNumber r)
      (alphaValue (tripleAlphaIndex a r) + delta) j, D, hatom, ?_⟩
    rw [hcase.1]
    exact canonicalProp49BranchScreen_yIndex m a r j
  · intro hcase
    rcases hyPrimeZero hcase with ⟨D, hatom⟩
    refine ⟨yPrimeSourceCanonicalProp49BranchScreen m (stageNumber r)
      (alphaValue (tripleAlphaIndex a r) + delta) j, D, hatom, ?_⟩
    rw [hcase.1]
    exact canonicalProp49BranchScreen_yIndex' m a r j
  · intro hcase
    let d : Dir := ⟨i.1, hcase.1⟩
    have hi : i = xIndex d := by
      apply Fin.ext
      rfl
    rcases hxLater hcase with ⟨D, hatom, hlocal⟩
    refine ⟨d, hi,
      xEastCanonicalProp49BranchScreen m (stageNumber r)
        (alphaValue (tripleAlphaIndex a r) + delta) j,
      D, hatom, ?_, hlocal⟩
    exact (congrArg (fun i ↦ canonicalProp49BranchScreen m i a r j) hi).trans
      (canonicalProp49BranchScreen_xIndex m d a r j)
  · intro hcase
    rcases hyLater hcase with ⟨D, hatom⟩
    refine ⟨yCanonicalProp49BranchScreen m (stageNumber r)
      (alphaValue (tripleAlphaIndex a r) + delta) j, D, hatom, ?_⟩
    rw [hcase.1]
    exact canonicalProp49BranchScreen_yIndex m a r j
  · intro hcase
    rcases hyPrimeLater hcase with ⟨D, hatom⟩
    refine ⟨yPrimeSourceCanonicalProp49BranchScreen m (stageNumber r)
      (alphaValue (tripleAlphaIndex a r) + delta) j, D, hatom, ?_⟩
    rw [hcase.1]
    exact canonicalProp49BranchScreen_yIndex' m a r j

/-- The deterministic winner/parity cover promotes the local canonical
screen interface to the complete coded later-stage interface. -/
theorem
    prop47StoppedProfileProp49CanonicalCodedLaterStageEstimateAt_of_canonicalScreens
    (m localCoeff : ℕ) (hm : 0 < m)
    (rawCode : Fin 6 → AlphaTriple → StageIndex → Fin 4 → Path → ℕ)
    (hsource : Prop47StoppedProfileProp49CanonicalScreensLocalEstimateAt
      m localCoeff rawCode) :
    Prop47StoppedProfileProp49CanonicalCodedLaterStageEstimateAt
      m 4 localCoeff (canonicalProp49BranchScreen m) rawCode := by
  intro i a r halpha
  refine ⟨canonicalProp49BranchScreen_cover m i a r hm, ?_⟩
  intro j eta c hnonempty
  rcases hsource i a r halpha j eta c hnonempty with
    ⟨hxZero, hyZero, hyPrimeZero, hxLater, hyLater, hyPrimeLater⟩
  refine ⟨?_, hyZero, ?_, ?_, hyLater, hyPrimeLater⟩
  · intro hcase
    rcases hxZero hcase with
      ⟨d, hi, eastScreen, D, hatom, hscreen⟩
    refine ⟨d, hi, eastScreen, ?_, D, hatom, hscreen⟩
    apply measurableSet_of_preimage_orientPath d
    rw [← hscreen]
    exact measurableSet_canonicalProp49BranchScreen m i a r j
  · intro hcase
    rcases hyPrimeZero hcase with
      ⟨yScreen, D, hatom, hscreen⟩
    refine ⟨yScreen, ?_, D, hatom, hscreen⟩
    apply measurableSet_of_preimage_reflectPath
    rw [← hscreen]
    exact measurableSet_canonicalProp49BranchScreen m i a r j
  · intro hcase
    rcases hxLater hcase with
      ⟨d, hi, eastScreen, D, hatom, hscreen, hlocal⟩
    refine ⟨d, hi, eastScreen, ?_, D, hatom, hscreen, hlocal⟩
    apply measurableSet_of_preimage_orientPath d
    rw [← hscreen]
    exact measurableSet_canonicalProp49BranchScreen m i a r j

/-- Eventual form of the literal coded source interface. -/
def Prop47StoppedProfileProp49CanonicalCodedLaterStageEstimate
    (branchCount localCoeff : ℕ)
    (branchScreen : ℕ → Fin 6 → AlphaTriple → StageIndex →
      Fin branchCount → Set Path)
    (rawCode : ℕ → Fin 6 → AlphaTriple → StageIndex →
      Fin branchCount → Path → ℕ) : Prop :=
  ∀ᶠ m : ℕ in atTop,
    Prop47StoppedProfileProp49CanonicalCodedLaterStageEstimateAt
      m branchCount localCoeff (branchScreen m) (rawCode m)

/-- Complete Proposition-4.9 source data at one sufficiently large scale. -/
structure Prop47CanonicalCodedLaterStagePackage
    (m localCoeff : ℕ) where
  branchScreen : Fin 6 → AlphaTriple → StageIndex → Fin 4 → Set Path
  rawCode : Fin 6 → AlphaTriple → StageIndex → Fin 4 → Path → ℕ
  estimate : Prop47StoppedProfileProp49CanonicalCodedLaterStageEstimateAt
    m 4 localCoeff branchScreen rawCode

/-- Reduced per-scale Proposition-4.9 package.  The four branch screens,
their X-east/Y representatives, their measurability, and their global cover
are canonical.  The source supplies one natural-valued stopped code.  Only
when an ordered code fibre meets its canonical screen does it
supply the single package selected by its pairing and stage, rather than six
implication-shaped alternatives. -/
structure Prop47CanonicalScreensCodedLaterStagePackage
    (m localCoeff : ℕ) where
  rawCode : Fin 6 → AlphaTriple → StageIndex → Fin 4 → Path → ℕ
  estimate :
    Prop47StoppedProfileProp49CanonicalActiveLiteralLocalEstimateAt
      m localCoeff rawCode

noncomputable def selectedProp49BranchScreen
    (localCoeff m : ℕ) :
    Fin 6 → AlphaTriple → StageIndex → Fin 4 → Set Path := by
  classical
  exact if h : Nonempty (Prop47CanonicalCodedLaterStagePackage m localCoeff) then
      (Classical.choice h).branchScreen
    else fun _ _ _ _ ↦ ∅

noncomputable def selectedProp49RawCode
    (localCoeff m : ℕ) :
    Fin 6 → AlphaTriple → StageIndex → Fin 4 → Path → ℕ := by
  classical
  exact if h : Nonempty (Prop47CanonicalCodedLaterStagePackage m localCoeff) then
      (Classical.choice h).rawCode
    else fun _ _ _ _ _ ↦ 0

noncomputable def selectedCanonicalProp49RawCode
    (localCoeff m : ℕ) :
    Fin 6 → AlphaTriple → StageIndex → Fin 4 → Path → ℕ := by
  classical
  exact if h : Nonempty
      (Prop47CanonicalScreensCodedLaterStagePackage m localCoeff) then
      (Classical.choice h).rawCode
    else fun _ _ _ _ _ ↦ 0

/-- Eventual per-scale packages canonically supply the total functions used
by the downstream filter statement.  Values outside the eventual set never
enter the proof. -/
theorem prop47StoppedProfileProp49CanonicalCodedLaterStageEstimate_of_packages
    (localCoeff : ℕ)
    (hsource : ∀ᶠ m : ℕ in atTop,
      Nonempty (Prop47CanonicalCodedLaterStagePackage m localCoeff)) :
    Prop47StoppedProfileProp49CanonicalCodedLaterStageEstimate
      4 localCoeff (selectedProp49BranchScreen localCoeff)
        (selectedProp49RawCode localCoeff) := by
  filter_upwards [hsource] with m hm
  let P := Classical.choice hm
  simpa only [selectedProp49BranchScreen, selectedProp49RawCode, hm,
    ↓reduceDIte, P] using P.estimate

/-- Eventual reduced packages directly supply the history-contained
finite-branch estimate.  Only ordered fibres meeting their branch screen are
retained.  Such fibres are measurable by their literal stopped-atom
identification; all other refined atoms are definitionally empty.  Thus no
measurability assumption on the natural-valued raw code is needed. -/
theorem
    prop47StoppedProfileProp49HistoryContainedFiniteBranchEstimate_of_canonicalPackages
    (localCoeff : ℕ)
    (hsource : ∀ᶠ m : ℕ in atTop,
      Nonempty
        (Prop47CanonicalScreensCodedLaterStagePackage m localCoeff)) :
    Prop47StoppedProfileProp49HistoryContainedFiniteBranchEstimate
      sourceCanonicalProfiles canonicalCStar 4 localCoeff
      canonicalProp49BranchScreen
      (fun m i a r j code ↦ canonicalScreenedOrderedHistoryAtom
        (rawCodeFiber
          (selectedCanonicalProp49RawCode localCoeff m i a r j))
        sourceCanonicalProfiles canonicalCStar m i a r
        (canonicalProp49BranchScreen m i a r j) code) := by
  classical
  filter_upwards [hsource, eventually_ge_atTop (1 : ℕ)] with m hm hmOne
  let P := Classical.choice hm
  have hmpos : 0 < m := by omega
  simp only [selectedCanonicalProp49RawCode, hm, ↓reduceDIte]
  intro i a r halpha
  have hactiveLocal (j : Fin 4) (eta : ℕ)
      (c : Fin (stageNumber r) → Site)
      (hscreen :
        (orderedProfileHistoryPathAtom sourceCanonicalProfiles
            canonicalCStar m i a r c
              (rawCodeFiber (P.rawCode i a r j) eta) ∩
          canonicalProp49BranchScreen m i a r j).Nonempty) :
      MeasurableSet
          (orderedProfileHistoryPathAtom sourceCanonicalProfiles
            canonicalCStar m i a r c
              (rawCodeFiber (P.rawCode i a r j) eta)) ∧
        RefinedAtomScreenEstimate
          (orderedProfileHistoryPathAtom sourceCanonicalProfiles
            canonicalCStar m i a r c
              (rawCodeFiber (P.rawCode i a r j) eta))
          (canonicalProp49BranchScreen m i a r j)
          (sourceProp49ScreenRate m localCoeff
            (alphaValue (tripleAlphaIndex a r))) := by
    let atom := orderedProfileHistoryPathAtom sourceCanonicalProfiles
      canonicalCStar m i a r c (rawCodeFiber (P.rawCode i a r j) eta)
    have hnonemptyAtom : atom.Nonempty :=
      hscreen.mono Set.inter_subset_left
    have hs := P.estimate i a r halpha j eta c hscreen
    by_cases hx : i.1 < 4
    · let d : Dir := ⟨i.1, hx⟩
      have hi : i = xIndex d := by
        apply Fin.ext
        rfl
      by_cases hr : r = 0
      · simp only [dif_pos hx, if_pos hr] at hs
        rcases hs with ⟨D, hD⟩
        change rawCodeFiber (P.rawCode i a r j) eta =
          orientPath (rotationInverseDir d) ⁻¹' D.atom at hD
        have hD' : rawCodeFiber (P.rawCode (xIndex d) a r j) eta =
            orientPath (rotationInverseDir d) ⁻¹' D.atom := by
          rw [← hi]
          exact hD
        subst r
        refine ⟨?_, ?_⟩
        · exact measurableSet_orderedSourceHistoryPathAtom
            m i a 0 c _ hmpos (by
              simpa only [hD] using D.measurableSet_atom.preimage
                (measurable_orientPath (rotationInverseDir d)))
        · simpa only [atom, hi, hD',
            canonicalProp49BranchScreen_xIndex, stageNumber] using
              xStageZeroProp49_rotated_screenEstimate (a := a) d D c
                (measurableSet_xEastCanonicalProp49BranchScreen _ _ _ _)
      · simp only [dif_pos hx, if_neg hr] at hs
        rcases hs with ⟨D, hD, hlocalEast⟩
        change rawCodeFiber (P.rawCode i a r j) eta =
          orientPath (rotationInverseDir d) ⁻¹' D.atom at hD
        have hD' : rawCodeFiber (P.rawCode (xIndex d) a r j) eta =
            orientPath (rotationInverseDir d) ⁻¹' D.atom := by
          rw [← hi]
          exact hD
        have hmeas : MeasurableSet atom :=
          measurableSet_orderedSourceHistoryPathAtom
            m i a r c _ hmpos (by
              simpa only [hD] using
                (Erdos1166.HLOZProp49CanonicalRefinement.ConcreteStoppedProp49AtomData.measurableSet_atom
                  D).preimage
                    (measurable_orientPath (rotationInverseDir d)))
        refine ⟨hmeas, ?_⟩
        rcases hlocalEast with hdet | hstageOrEstimate
        · simpa only [atom, hi, hD',
            canonicalProp49BranchScreen_xIndex] using
            xProp49_rotated_fullComplement_screenEstimate d D c
              (measurableSet_xEastCanonicalProp49BranchScreen _ _ _ _)
              hdet
        · rcases hstageOrEstimate with ⟨hrOne, hresidual⟩ | heast
          · subst r
            have hzero :
                HLOZStoppedFullComplement.ConcreteStoppedProp49AtomData.FullComplementStageZeroDetermined
                  D (profiles := sourceCanonicalProfiles)
                    (cStar := canonicalCStar) (a := a)
                      (r := (1 : StageIndex)) :=
              HLOZStoppedFullComplement.ConcreteStoppedProp49AtomData.fullComplementStageZeroDetermined_stageOne_xEast_of_lowScaleResidual
                D hresidual
            have hdet :
                HLOZStoppedFullComplement.ConcreteStoppedProp49AtomData.FullComplementHistoryDetermined
                  D (profiles := sourceCanonicalProfiles)
                    (cStar := canonicalCStar) (i := xIndex east)
                      (a := a) (r := (1 : StageIndex))
                        (rotateCreationTuple d c) :=
              HLOZStoppedFullComplement.ConcreteStoppedProp49AtomData.fullComplementHistoryDetermined_stageOne_xEast_of_stageZero
                D (rotateCreationTuple d c) hzero
            simpa only [atom, hi, hD',
              canonicalProp49BranchScreen_xIndex] using
                xProp49_rotated_fullComplement_screenEstimate d D c
                  (measurableSet_xEastCanonicalProp49BranchScreen _ _ _ _)
                  hdet
          · simpa only [atom, hi, hD',
              canonicalProp49BranchScreen_xIndex] using
                xProp49_rotated_screenEstimate d D c
                  (measurableSet_xEastCanonicalProp49BranchScreen _ _ _ _)
                  heast
    · by_cases hy : i = yIndex
      · by_cases hr : r = 0
        · simp only [dif_neg hx, if_pos hy, if_pos hr] at hs
          rcases hs with ⟨D, hD⟩
          subst i
          subst r
          have hn :
              (orderedProfileHistoryPathAtom sourceCanonicalProfiles
                canonicalCStar m yIndex a 0 c D.atom).Nonempty := by
            simpa only [atom, P, hD, stageNumber] using hnonemptyAtom
          refine ⟨?_, ?_⟩
          · exact measurableSet_orderedSourceHistoryPathAtom
              m yIndex a 0 c _ hmpos (by
                simpa only [hD] using D.measurableSet_atom)
          · simpa only [atom, P, hD,
              canonicalProp49BranchScreen_yIndex, stageNumber] using
                D.screenEstimate c hn
        · simp only [dif_neg hx, if_pos hy, if_neg hr] at hs
          rcases hs with ⟨D, hD⟩
          subst i
          refine ⟨?_, ?_⟩
          · exact measurableSet_orderedSourceHistoryPathAtom
              m yIndex a r c _ hmpos (by
                simpa only [hD] using D.measurableSet_atom)
          · simpa only [atom, P, hD,
              canonicalProp49BranchScreen_yIndex] using
                D.screenEstimate
      · have hy' : i = yIndex' := by
          apply Fin.ext
          change i.1 = 5
          have hi6 : i.1 < 6 := i.2
          have hne4 : i.1 ≠ 4 := by
            intro h4
            apply hy
            apply Fin.ext
            change i.1 = 4
            exact h4
          omega
        by_cases hr : r = 0
        · simp only [dif_neg hx, if_neg hy, if_pos hr] at hs
          rcases hs with ⟨D, hD⟩
          subst i
          subst r
          have hn :
              (orderedProfileHistoryPathAtom sourceCanonicalProfiles
                canonicalCStar m yIndex' a 0 c
                  (reflectPath ⁻¹' D.atom)).Nonempty := by
            simpa only [atom, P, hD, stageNumber] using hnonemptyAtom
          refine ⟨?_, ?_⟩
          · exact measurableSet_orderedSourceHistoryPathAtom
              m yIndex' a 0 c _ hmpos (by
                simpa only [hD] using D.measurableSet_atom.preimage
                  measurable_reflectPath)
          · simpa only [atom, P, hD,
              canonicalProp49BranchScreen_yIndex', stageNumber] using
                yPrimeStageZeroProp49_reflected_screenEstimate D c
                  (measurableSet_yPrimeSourceCanonicalProp49BranchScreen
                    _ _ _ _) hn
        · simp only [dif_neg hx, if_neg hy, if_neg hr] at hs
          rcases hs with ⟨D, hD⟩
          subst i
          refine ⟨?_, ?_⟩
          · exact measurableSet_orderedSourceHistoryPathAtom
              m yIndex' a r c _ hmpos (by
                simpa only [hD] using D.measurableSet_atom)
          · simpa only [atom, P, hD,
              canonicalProp49BranchScreen_yIndex'] using
                D.screenEstimate
  have hcodeLocal (j : Fin 4) (code : ℕ)
      (hscreen :
        (canonicalOrderedHistoryAtom
            (rawCodeFiber (P.rawCode i a r j)) sourceCanonicalProfiles
              canonicalCStar m i a r code ∩
          canonicalProp49BranchScreen m i a r j).Nonempty) :
      MeasurableSet
          (canonicalOrderedHistoryAtom
            (rawCodeFiber (P.rawCode i a r j)) sourceCanonicalProfiles
              canonicalCStar m i a r code) ∧
        RefinedAtomScreenEstimate
          (canonicalOrderedHistoryAtom
            (rawCodeFiber (P.rawCode i a r j)) sourceCanonicalProfiles
              canonicalCStar m i a r code)
          (canonicalProp49BranchScreen m i a r j)
          (sourceProp49ScreenRate m localCoeff
            (alphaValue (tripleAlphaIndex a r))) := by
    generalize hcode : Encodable.decode₂
        (ℕ × (Fin (stageNumber r) → Site)) code = x
    cases x with
    | none => simp [canonicalOrderedHistoryAtom, hcode] at hscreen
    | some x =>
        rcases x with ⟨eta, c⟩
        rw [canonicalOrderedHistoryAtom, hcode] at hscreen ⊢
        exact hactiveLocal j eta c hscreen
  refine ⟨?_, ?_, canonicalProp49BranchScreen_cover m i a r hmpos, ?_, ?_⟩
  · intro j
    exact canonicalScreenedOrderedHistoryAtom_pairwise
      (rawCodeFiber (P.rawCode i a r j)) sourceCanonicalProfiles
        canonicalCStar m i a r (canonicalProp49BranchScreen m i a r j)
          (rawCodeFiber_pairwise _)
  · intro j code
    by_cases hscreen :
        (canonicalOrderedHistoryAtom
            (rawCodeFiber (P.rawCode i a r j)) sourceCanonicalProfiles
              canonicalCStar m i a r code ∩
          canonicalProp49BranchScreen m i a r j).Nonempty
    · rw [canonicalScreenedOrderedHistoryAtom_of_nonempty
        _ _ _ _ _ _ _ _ _ hscreen]
      exact (hcodeLocal j code hscreen).1
    · rw [canonicalScreenedOrderedHistoryAtom_of_not_nonempty
        _ _ _ _ _ _ _ _ _ hscreen]
      exact MeasurableSet.empty
  · intro j s hs
    let eta := P.rawCode i a r j s
    let c : Fin (stageNumber r) → Site :=
      orderedCreationSites m (stageNumber r) s
    let code := Encodable.encode (eta, c)
    have hsraw : s ∈ rawCodeFiber (P.rawCode i a r j) eta := by
      simp only [rawCodeFiber, Set.mem_preimage, Set.mem_singleton_iff, eta]
    have hsordered :
        s ∈ canonicalOrderedHistoryAtom
          (rawCodeFiber (P.rawCode i a r j)) sourceCanonicalProfiles
            canonicalCStar m i a r code := by
      rw [show code = Encodable.encode (eta, c) by rfl,
        canonicalOrderedHistoryAtom_encode]
      exact ⟨hsraw, rfl, hs.1⟩
    have hscreen :
        (canonicalOrderedHistoryAtom
            (rawCodeFiber (P.rawCode i a r j)) sourceCanonicalProfiles
              canonicalCStar m i a r code ∩
          canonicalProp49BranchScreen m i a r j).Nonempty :=
      ⟨s, hsordered, hs.2⟩
    refine Set.mem_iUnion.mpr ⟨code, ?_⟩
    rw [canonicalScreenedOrderedHistoryAtom_of_nonempty
      _ _ _ _ _ _ _ _ _ hscreen]
    exact hsordered
  · intro j code
    refine ⟨canonicalScreenedOrderedHistoryAtom_subset_history
      (rawCodeFiber (P.rawCode i a r j)) sourceCanonicalProfiles
        canonicalCStar m i a r (canonicalProp49BranchScreen m i a r j)
          code, ?_⟩
    by_cases hscreen :
        (canonicalOrderedHistoryAtom
            (rawCodeFiber (P.rawCode i a r j)) sourceCanonicalProfiles
              canonicalCStar m i a r code ∩
          canonicalProp49BranchScreen m i a r j).Nonempty
    · rw [canonicalScreenedOrderedHistoryAtom_of_nonempty
        _ _ _ _ _ _ _ _ _ hscreen]
      exact (hcodeLocal j code hscreen).2
    · rw [canonicalScreenedOrderedHistoryAtom_of_not_nonempty
        _ _ _ _ _ _ _ _ _ hscreen]
      simp only [RefinedAtomScreenEstimate, Set.empty_inter, measure_empty,
        mul_zero, le_refl]

/-- The first-stage checked tower plus the later-stage source estimates
supply the uniform coded interface. -/
theorem prop47StoppedProfileProp49CanonicalCodedFiniteBranchEstimate_of_laterStage
    (branchCount localCoeff : ℕ)
    (branchScreen : ℕ → Fin 6 → AlphaTriple → StageIndex →
      Fin branchCount → Set Path)
    (rawCode : ℕ → Fin 6 → AlphaTriple → StageIndex →
      Fin branchCount → Path → ℕ)
    (hsource : Prop47StoppedProfileProp49CanonicalCodedLaterStageEstimate
      branchCount localCoeff branchScreen rawCode) :
    Prop47StoppedProfileProp49CanonicalCodedFiniteBranchEstimate
      branchCount localCoeff branchScreen rawCode := by
  filter_upwards [hsource, eventually_ge_atTop (1 : ℕ)] with m hm hmOne
  intro i a r halpha
  rcases hm i a r halpha with ⟨hbranchCover, hlocal⟩
  refine ⟨hbranchCover, ?_⟩
  intro j eta c
  dsimp only
  intro hnonempty
  have hmpos : 0 < m := by omega
  rcases hlocal j eta c hnonempty with
    ⟨hzero, hyzero, hyPrimeZero, hxLater, hyLater, hyPrimeLater⟩
  by_cases hr : r = 0
  · by_cases hi : i.1 < 4
    · rcases hzero ⟨hi, hr⟩ with
        ⟨d, hi', eastScreen, hscreen, D, hD, hscreenEq⟩
      subst i
      subst r
      refine ⟨?_, ?_⟩
      · exact measurableSet_orderedSourceHistoryPathAtom
          m (xIndex d) a 0 c _ hmpos (by
            simpa only [hD] using D.measurableSet_atom.preimage
              (measurable_orientPath (rotationInverseDir d)))
      · simpa only [hD, hscreenEq, stageNumber] using
          xStageZeroProp49_rotated_screenEstimate d D c hscreen
    · by_cases hy : i = yIndex
      · rcases hyzero ⟨hy, hr⟩ with
          ⟨yScreen, D, hD, hscreenEq⟩
        subst i
        subst r
        have hn :
            (orderedProfileHistoryPathAtom sourceCanonicalProfiles
              canonicalCStar m yIndex a 0 c D.atom).Nonempty := by
          simpa only [hD, stageNumber] using hnonempty
        refine ⟨?_, ?_⟩
        · exact measurableSet_orderedSourceHistoryPathAtom
            m yIndex a 0 c _ hmpos (by
              simpa only [hD] using D.measurableSet_atom)
        · simpa only [hD, hscreenEq, stageNumber] using
            D.screenEstimate c hn
      · have hy' : i = yIndex' := by
          apply Fin.ext
          change i.1 = 5
          have hi6 : i.1 < 6 := i.2
          have hne4 : i.1 ≠ 4 := by
            intro h4
            apply hy
            apply Fin.ext
            change i.1 = 4
            exact h4
          omega
        rcases hyPrimeZero ⟨hy', hr⟩ with
          ⟨yScreen, hscreen, D, hD, hscreenEq⟩
        subst i
        subst r
        have hn :
            (orderedProfileHistoryPathAtom sourceCanonicalProfiles
              canonicalCStar m yIndex' a 0 c
                (reflectPath ⁻¹' D.atom)).Nonempty := by
          simpa only [hD, stageNumber] using hnonempty
        refine ⟨?_, ?_⟩
        · exact measurableSet_orderedSourceHistoryPathAtom
            m yIndex' a 0 c _ hmpos (by
              simpa only [hD] using D.measurableSet_atom.preimage
                measurable_reflectPath)
        · simpa only [hD, hscreenEq, stageNumber] using
            yPrimeStageZeroProp49_reflected_screenEstimate D c hscreen hn
  · by_cases hi : i.1 < 4
    · rcases hxLater ⟨hi, hr⟩ with
        ⟨d, hi', eastScreen, hscreen, D, hD, hscreenEq, hlocalEast⟩
      subst i
      rcases hlocalEast with hdet | hstageOrEstimate
      · refine ⟨?_, ?_⟩
        · exact measurableSet_orderedSourceHistoryPathAtom
            m (xIndex d) a r c _ hmpos (by
              simpa only [hD] using
                (Erdos1166.HLOZProp49CanonicalRefinement.ConcreteStoppedProp49AtomData.measurableSet_atom
                  D).preimage
                    (measurable_orientPath (rotationInverseDir d)))
        · simpa only [hD, hscreenEq] using
            xProp49_rotated_fullComplement_screenEstimate
              d D c hscreen hdet
      · rcases hstageOrEstimate with ⟨hrOne, hresidual⟩ | heast
        · subst r
          have hzero :
              HLOZStoppedFullComplement.ConcreteStoppedProp49AtomData.FullComplementStageZeroDetermined
                D (profiles := sourceCanonicalProfiles)
                  (cStar := canonicalCStar) (a := a)
                    (r := (1 : StageIndex)) :=
            HLOZStoppedFullComplement.ConcreteStoppedProp49AtomData.fullComplementStageZeroDetermined_stageOne_xEast_of_lowScaleResidual
              D hresidual
          have hdet :
              HLOZStoppedFullComplement.ConcreteStoppedProp49AtomData.FullComplementHistoryDetermined
                D (profiles := sourceCanonicalProfiles)
                  (cStar := canonicalCStar) (i := xIndex east)
                    (a := a) (r := (1 : StageIndex))
                      (rotateCreationTuple d c) :=
            HLOZStoppedFullComplement.ConcreteStoppedProp49AtomData.fullComplementHistoryDetermined_stageOne_xEast_of_stageZero
              D (rotateCreationTuple d c) hzero
          refine ⟨?_, ?_⟩
          · exact measurableSet_orderedSourceHistoryPathAtom
              m (xIndex d) a 1 c _ hmpos (by
                simpa only [hD] using
                  (Erdos1166.HLOZProp49CanonicalRefinement.ConcreteStoppedProp49AtomData.measurableSet_atom
                    D).preimage
                      (measurable_orientPath (rotationInverseDir d)))
          · simpa only [hD, hscreenEq] using
              xProp49_rotated_fullComplement_screenEstimate
                d D c hscreen hdet
        · refine ⟨?_, ?_⟩
          · exact measurableSet_orderedSourceHistoryPathAtom
              m (xIndex d) a r c _ hmpos (by
                simpa only [hD] using
                  (Erdos1166.HLOZProp49CanonicalRefinement.ConcreteStoppedProp49AtomData.measurableSet_atom
                    D).preimage
                      (measurable_orientPath (rotationInverseDir d)))
          · simpa only [hD, hscreenEq] using
              xProp49_rotated_screenEstimate d D c hscreen heast
    · by_cases hy : i = yIndex
      · rcases hyLater ⟨hy, hr⟩ with
          ⟨yScreen, D, hD, hscreenEq⟩
        subst i
        refine ⟨?_, ?_⟩
        · exact measurableSet_orderedSourceHistoryPathAtom
            m yIndex a r c _ hmpos (by
              simpa only [hD] using D.measurableSet_atom)
        · simpa only [hD, hscreenEq] using D.screenEstimate
      · have hy' : i = yIndex' := by
          apply Fin.ext
          change i.1 = 5
          have hi6 : i.1 < 6 := i.2
          have hne4 : i.1 ≠ 4 := by
            intro h4
            apply hy
            apply Fin.ext
            change i.1 = 4
            exact h4
          omega
        rcases hyPrimeLater ⟨hy', hr⟩ with
          ⟨yScreen, D, hD, hscreenEq⟩
        subst i
        refine ⟨?_, ?_⟩
        · exact measurableSet_orderedSourceHistoryPathAtom
            m yIndex' a r c _ hmpos (by
              simpa only [hD] using D.measurableSet_atom)
        · simpa only [hD, hscreenEq] using D.screenEstimate

/-- Direct bridge from the coded source statement to the
history-contained finite-branch connector.

No measurability of the natural-valued code is needed.  A decoded refined
fiber that is used by the proof is measurable by the literal stopped-atom
identification in `hsource`; an unused empty fiber is measurable trivially. -/
theorem
    prop47StoppedProfileProp49HistoryContainedFiniteBranchEstimate_of_coded
    (branchCount localCoeff : ℕ)
    (branchScreen : ℕ → Fin 6 → AlphaTriple → StageIndex →
      Fin branchCount → Set Path)
    (rawCode : ℕ → Fin 6 → AlphaTriple → StageIndex →
      Fin branchCount → Path → ℕ)
    (hsource : Prop47StoppedProfileProp49CanonicalCodedFiniteBranchEstimate
      branchCount localCoeff branchScreen rawCode) :
    Prop47StoppedProfileProp49HistoryContainedFiniteBranchEstimate
      sourceCanonicalProfiles canonicalCStar branchCount localCoeff
      branchScreen
      (fun m i a r j code ↦ canonicalOrderedHistoryAtom
        (rawCodeFiber (rawCode m i a r j)) sourceCanonicalProfiles
          canonicalCStar m i a r code) := by
  classical
  filter_upwards [hsource, eventually_ge_atTop (1 : ℕ)] with m hm hmOne
  intro i a r halpha
  rcases hm i a r halpha with ⟨hbranchCover, hlocal⟩
  refine ⟨?_, ?_, hbranchCover, ?_, ?_⟩
  · intro j
    exact canonicalOrderedHistoryAtom_pairwise
      (rawCodeFiber (rawCode m i a r j)) sourceCanonicalProfiles
        canonicalCStar m i a r (rawCodeFiber_pairwise _)
  · intro j code
    generalize hcode : Encodable.decode₂
        (ℕ × (Fin (stageNumber r) → Site)) code = x
    cases x with
    | none => simp [canonicalOrderedHistoryAtom, hcode]
    | some x =>
        rcases x with ⟨eta, c⟩
        simp only [canonicalOrderedHistoryAtom, hcode]
        let A := orderedProfileHistoryPathAtom sourceCanonicalProfiles
          canonicalCStar m i a r c
            (rawCodeFiber (rawCode m i a r j) eta)
        change MeasurableSet A
        by_cases hA : A.Nonempty
        · exact (hlocal j eta c hA).1
        · have hAempty : A = ∅ := Set.not_nonempty_iff_eq_empty.mp hA
          rw [hAempty]
          exact MeasurableSet.empty
  · intro j
    apply inter_subset_iUnion_canonicalOrderedHistoryAtom
      (rawCodeFiber (rawCode m i a r j)) sourceCanonicalProfiles
        canonicalCStar m i a r (branchScreen m i a r j)
    intro s hs
    rw [iUnion_rawCodeFiber]
    exact Set.mem_univ s
  · intro j code
    refine ⟨canonicalOrderedHistoryAtom_subset_history
      (rawCodeFiber (rawCode m i a r j)) sourceCanonicalProfiles
        canonicalCStar m i a r code, ?_⟩
    generalize hcode : Encodable.decode₂
        (ℕ × (Fin (stageNumber r) → Site)) code = x
    cases x with
    | none => simp [canonicalOrderedHistoryAtom, hcode,
        RefinedAtomScreenEstimate]
    | some x =>
        rcases x with ⟨eta, c⟩
        simp only [canonicalOrderedHistoryAtom, hcode]
        let A := orderedProfileHistoryPathAtom sourceCanonicalProfiles
          canonicalCStar m i a r c
            (rawCodeFiber (rawCode m i a r j) eta)
        change RefinedAtomScreenEstimate A (branchScreen m i a r j)
          (sourceProp49ScreenRate m localCoeff
            (alphaValue (tripleAlphaIndex a r)))
        by_cases hA : A.Nonempty
        · exact (hlocal j eta c hA).2
        · have hAempty : A = ∅ := Set.not_nonempty_iff_eq_empty.mp hA
          rw [hAempty]
          simp [RefinedAtomScreenEstimate]

end Erdos1166.HLOZProp49CanonicalRefinement
