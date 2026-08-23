import ErdosProblems.Erdos1166.Erdos1166HLOZProp47Lemma411412SourceAtoms

/-!
# The four literal X-east branches for Lemmas 4.11--4.12

This file specializes the finite-branch interface of
`Erdos1166HLOZProp47Lemma411412Connector` at the X-east pairing.  The four
branches are the two stopping parities crossed with the honest left/right
winner convention:

* unprimed-even, tie-left;
* unprimed-odd terminal, tie-left;
* primed-odd, strict-right;
* primed-even terminal, strict-right.

Each branch carries literal stopped-source data.  Its product map law and
measurability are derived internally by the constructors in
`Erdos1166HLOZProp47Lemma411412SourceAtoms`; callers supply only the branch
cover, within-branch disjointness, and the event/history estimates in
`Equation447SourceBandBranchRemainingData`.  For each selected coordinate,
Lean canonically filters its history fibre by the current and preceding HLOZ
bands.  Callers supply the literal finite selected-coordinate set and its
cardinality only when the exact count is at most the finite coordinate-space
cardinality; Lean chooses its enumeration and proves injectivity.  Larger
exact counts are proved empty and are totalized by an inactive Dirac
category, so the source interface never asks for an impossible injection.
Callers
supply only the equal-cardinality fact for the two filtered cells.  The pointwise
singleton comparison is derived from the
truncated negative-binomial adjacent-window estimate; the raw set-mass ratio,
conditional product, and conditional one-coordinate ratio are then derived
internally.  The resulting fixed-profile record is threshold-independent at
the type level; only the surrounding branch wrapper retains the canonical
quarter-log-square threshold.  The deterministic `SourceWindowGrowth`
hypothesis used by the
adjacent-window comparison is supplied here from
`eventually_sourceWindowGrowth`; it is not a field of any literal source
atom.  The bound placing every selected stopped profile strictly below `m`
is likewise derived by the four literal winner-source constructors.  No
disjointness between the four branches is assumed.

The conclusion is deliberately restricted to `xIndex east`.  Rotations and
the two column pairings require separate source transports and are not
asserted here.
-/

namespace Erdos1166.HLOZProp47Lemma411412XEastBridge

open Filter Set

open HLOZPairing HLOZProp47Parameters HLOZProp47SourceObjects
open HLOZProp47SourceAssembly
open HLOZProp47Canonical
open HLOZProp47Lemma411412Connector
open HLOZProp47Lemma411412SourceAtoms
open HLOZEquation447
open HLOZBandRatios HLOZLemma412Windows
open HLOZLemma410Prop48Connector HLOZMixedCreationBlocks
open HLOZDecomposition

abbrev Path := ℕ → Site

/-! ## The canonical winner/parity branch cover -/

/-- For the X-east pairing, the distinguished endpoint is exactly the
horizontal chessboard base used by the stopped left/right winner split. -/
theorem distinguishedEndpoint_xEast_eq_horizontalChessBase (x : Site) :
    distinguishedEndpoint (xIndex east) x = horizontalChessBase x := by
  classical
  change (if chessEven x then x else shift x (vec west)) =
    (if chessEven x then x else x + directionStep (1 : Direction))
  by_cases hx : chessEven x
  · simp [hx]
  · simp only [hx, if_false, shift, vec, west, directionStep]
    ext <;> simp

/-- The spatial window is the literal near-favourite set itself. -/
noncomputable def xEastNearFavoriteWindow
    (s : Path) (m k : ℕ) (alpha : ℝ) : Site → Finset Site :=
  fun _ ↦ nearFavoriteSites (xIndex east) s m k alpha

theorem xEast_nearFavorite_candidateSites_eq
    (s : Path) (m k : ℕ) (alpha : ℝ) :
    hlozCandidateSitesAtTime (xEastNearFavoriteWindow s m k alpha) s
      (directCreationTime m k s) 0 =
        nearFavoriteSites (xIndex east) s m k alpha := by
  ext x
  simp [hlozCandidateSitesAtTime, xEastNearFavoriteWindow]

theorem horizontalChessBase_idem (x : Site) :
    horizontalChessBase (horizontalChessBase x) = horizontalChessBase x := by
  rw [horizontalChessBase]
  simp [horizontalChessBase_chessEven]

theorem horizontalChessBase_add_paperE1_of_chessEven
    (x : Site) (hx : chessEven x) :
    horizontalChessBase (x + paperE1) = x := by
  unfold horizontalChessBase
  rw [if_neg (HLOZReconstruction.not_chessEven_add_paperE1 hx)]
  ext <;> simp [directionStep, paperE1]

/-- A left winner in the near-favourite set cannot be a level-`m` creation
winner: the definition of `nearFavoriteSites` excludes the complete
creation domino. -/
theorem xEast_leftCreationWinner_nearFavorite_eq_empty
    (s : Path) (m k : ℕ) (alpha : ℝ) (hm : 0 < m) (hk : 0 < k) :
    hlozLeftCreationWinnerCandidateSitesAtTime
      (xEastNearFavoriteWindow s m k alpha) s
      (directCreationTime m k s) m 0 = ∅ := by
  classical
  apply Finset.not_nonempty_iff_eq_empty.mp
  rintro ⟨x, hx⟩
  have hxWinner := (Finset.mem_filter.mp hx).1
  have hxm := (Finset.mem_filter.mp hx).2
  have hxBase := (Finset.mem_filter.mp hxWinner).1
  rcases Finset.mem_image.mp hxBase with ⟨y, hyCandidate, rfl⟩
  have hyNear : y ∈ nearFavoriteSites (xIndex east) s m k alpha := by
    rw [← xEast_nearFavorite_candidateSites_eq s m k alpha]
    exact hyCandidate
  have hyData := (Finset.mem_filter.mp hyNear).2
  have hkfinite : firstKSitesReachLevel m k s ≠ ⊤ := hyData.1
  have hfree : distinguishedEndpoint (xIndex east) y ∉
      creationDominoEndpoints (xIndex east) s m k := hyData.2.1
  let t := directCreationTime m k s
  have hxVisited : horizontalChessBase y ∈ visitedSites s t := by
    by_contra hxNot
    have hz := localTime_eq_zero_of_not_mem_visitedSites hxNot
    change m ≤ localTime s t (horizontalChessBase y) at hxm
    omega
  have hxLevel : horizontalChessBase y ∈ sitesAtLeastLevel s t m := by
    exact Finset.mem_filter.mpr ⟨hxVisited, hxm⟩
  have hsites := sitesAtLeastLevel_at_threshold_eq_creationSites
    s m k hm hk hkfinite
  dsimp [t, directCreationTime] at hxLevel
  rw [hsites] at hxLevel
  rcases Finset.mem_image.mp hxLevel with ⟨j, hj, hjEq⟩
  apply hfree
  apply Finset.mem_image.mpr
  refine ⟨j, hj, ?_⟩
  rw [hjEq, distinguishedEndpoint_xEast_eq_horizontalChessBase,
    distinguishedEndpoint_xEast_eq_horizontalChessBase,
    horizontalChessBase_idem]

/-- The analogous creation-winner exclusion for the strict-right endpoint. -/
theorem xEast_rightCreationWinner_nearFavorite_eq_empty
    (s : Path) (m k : ℕ) (alpha : ℝ) (hm : 0 < m) (hk : 0 < k) :
    hlozRightCreationWinnerCandidateSitesAtTime
      (xEastNearFavoriteWindow s m k alpha) s
      (directCreationTime m k s) m 0 = ∅ := by
  classical
  apply Finset.not_nonempty_iff_eq_empty.mp
  rintro ⟨x, hx⟩
  have hxWinner := (Finset.mem_filter.mp hx).1
  have hxm := (Finset.mem_filter.mp hx).2
  rcases hlozRightWinnerCandidateSitesAtTime_witness
      (xEastNearFavoriteWindow s m k alpha) s
      (directCreationTime m k s) 0 hxWinner with
    ⟨b, hbCandidateBase, rfl, _hwin, _hmax⟩
  rcases Finset.mem_image.mp hbCandidateBase with
    ⟨y, hyCandidate, hb⟩
  have hyNear : y ∈ nearFavoriteSites (xIndex east) s m k alpha := by
    rw [← xEast_nearFavorite_candidateSites_eq s m k alpha]
    exact hyCandidate
  have hyData := (Finset.mem_filter.mp hyNear).2
  have hkfinite : firstKSitesReachLevel m k s ≠ ⊤ := hyData.1
  have hfree : distinguishedEndpoint (xIndex east) y ∉
      creationDominoEndpoints (xIndex east) s m k := hyData.2.1
  let t := directCreationTime m k s
  have hxVisited : b + paperE1 ∈ visitedSites s t := by
    by_contra hxNot
    have hz := localTime_eq_zero_of_not_mem_visitedSites hxNot
    change m ≤ localTime s t (b + paperE1) at hxm
    omega
  have hxLevel : b + paperE1 ∈ sitesAtLeastLevel s t m := by
    exact Finset.mem_filter.mpr ⟨hxVisited, hxm⟩
  have hsites := sitesAtLeastLevel_at_threshold_eq_creationSites
    s m k hm hk hkfinite
  dsimp [t, directCreationTime] at hxLevel
  rw [hsites] at hxLevel
  rcases Finset.mem_image.mp hxLevel with ⟨j, hj, hjEq⟩
  have hbEven : chessEven b := by
    rw [← hb]
    exact horizontalChessBase_chessEven y
  apply hfree
  apply Finset.mem_image.mpr
  refine ⟨j, hj, ?_⟩
  rw [hjEq, distinguishedEndpoint_xEast_eq_horizontalChessBase,
    distinguishedEndpoint_xEast_eq_horizontalChessBase,
    horizontalChessBase_add_paperE1_of_chessEven b hbEven,
    ← hb]

noncomputable def xEastLeftNearFavoriteWinnerSites
    (s : Path) (m k : ℕ) (alpha : ℝ) : Finset Site :=
  hlozLeftActiveFreeWinnerCandidateSitesAtTime
    (xEastNearFavoriteWindow s m k alpha) s
    (directCreationTime m k s) m 0

noncomputable def xEastRightNearFavoriteWinnerSites
    (s : Path) (m k : ℕ) (alpha : ℝ) : Finset Site :=
  hlozRightActiveFreeWinnerCandidateSitesAtTime
    (xEastNearFavoriteWindow s m k alpha) s
    (directCreationTime m k s) m 0

/-- The near-favourite set is controlled by the two active/free winner
sets.  The factor two is precisely the source inequality (4.40). -/
theorem xEast_nearFavorite_card_le_two_mul_winners
    (s : Path) (m k : ℕ) (alpha : ℝ) (hm : 0 < m) (hk : 0 < k) :
    (nearFavoriteSites (xIndex east) s m k alpha).card ≤
      2 * ((xEastLeftNearFavoriteWinnerSites s m k alpha).card +
        (xEastRightNearFavoriteWinnerSites s m k alpha).card) := by
  let window := xEastNearFavoriteWindow s m k alpha
  let t := directCreationTime m k s
  have hcandidate := hlozCandidateSitesAtTime_card_le_two_mul_winners
    window s t 0
  have hleft := hlozLeftActiveFree_card_add_creation window s t m 0
  have hright := hlozRightActiveFree_card_add_creation window s t m 0
  have hleftEmpty :=
    xEast_leftCreationWinner_nearFavorite_eq_empty s m k alpha hm hk
  have hrightEmpty :=
    xEast_rightCreationWinner_nearFavorite_eq_empty s m k alpha hm hk
  rw [hleftEmpty, Finset.card_empty, add_zero] at hleft
  rw [hrightEmpty, Finset.card_empty, add_zero] at hright
  rw [xEast_nearFavorite_candidateSites_eq s m k alpha] at hcandidate
  simpa only [xEastLeftNearFavoriteWinnerSites,
    xEastRightNearFavoriteWinnerSites, window, t, hleft, hright] using
      hcandidate

def xEastLeftNearFavoriteOverflow
    (m k : ℕ) (alpha rho : ℝ) : Set Path :=
  {s | rho < (xEastLeftNearFavoriteWinnerSites s m k alpha).card}

def xEastRightNearFavoriteOverflow
    (m k : ℕ) (alpha rho : ℝ) : Set Path :=
  {s | rho < (xEastRightNearFavoriteWinnerSites s m k alpha).card}

/-- A log-square overflow forces a quarter-log-square overflow in one of
the two winner classes. -/
theorem xEast_nearFavorite_overflow_subset_winner_overflows
    (m k : ℕ) (alpha : ℝ) (hm : 0 < m) (hk : 0 < k) :
    {s | Real.log m ^ 2 <
        ((nearFavoriteSites (xIndex east) s m k alpha).card : ℝ)} ⊆
      xEastLeftNearFavoriteOverflow m k alpha
          ((1 / 4 : ℝ) * Real.log m ^ 2) ∪
        xEastRightNearFavoriteOverflow m k alpha
          ((1 / 4 : ℝ) * Real.log m ^ 2) := by
  intro s hs
  change Real.log m ^ 2 <
    ((nearFavoriteSites (xIndex east) s m k alpha).card : ℝ) at hs
  have hcard := xEast_nearFavorite_card_le_two_mul_winners
    s m k alpha hm hk
  have hcardReal :
      ((nearFavoriteSites (xIndex east) s m k alpha).card : ℝ) ≤
        2 * (((xEastLeftNearFavoriteWinnerSites s m k alpha).card : ℝ) +
          ((xEastRightNearFavoriteWinnerSites s m k alpha).card : ℝ)) := by
    exact_mod_cast hcard
  by_cases hleft : (1 / 4 : ℝ) * Real.log m ^ 2 <
      ((xEastLeftNearFavoriteWinnerSites s m k alpha).card : ℝ)
  · exact Or.inl hleft
  by_cases hright : (1 / 4 : ℝ) * Real.log m ^ 2 <
      ((xEastRightNearFavoriteWinnerSites s m k alpha).card : ℝ)
  · exact Or.inr hright
  have hleftLe := not_lt.mp hleft
  have hrightLe := not_lt.mp hright
  exfalso
  nlinarith

def xEastEquation447LeftOverflowEvent (m : ℕ) (r : StageIndex) : Set Path :=
  prefixPairingEvent m (xIndex east) (stageNumber r) ∩
    xEastLeftNearFavoriteOverflow m (stageNumber r) kappaOne
      ((1 / 4 : ℝ) * Real.log m ^ 2)

def xEastEquation447RightOverflowEvent (m : ℕ) (r : StageIndex) : Set Path :=
  prefixPairingEvent m (xIndex east) (stageNumber r) ∩
    xEastRightNearFavoriteOverflow m (stageNumber r) kappaOne
      ((1 / 4 : ℝ) * Real.log m ^ 2)

def xEastEquation447UnprimedEvenBranch (m : ℕ) (r : StageIndex) : Set Path :=
  xEastEquation447LeftOverflowEvent m r ∩
    {s | Even (directCreationTime m (stageNumber r) s)}

def xEastEquation447UnprimedOddBranch (m : ℕ) (r : StageIndex) : Set Path :=
  xEastEquation447LeftOverflowEvent m r ∩
    {s | ¬ Even (directCreationTime m (stageNumber r) s)}

def xEastEquation447PrimedOddBranch (m : ℕ) (r : StageIndex) : Set Path :=
  xEastEquation447RightOverflowEvent m r ∩
    {s | ¬ Even (directCreationTime m (stageNumber r) s)}

def xEastEquation447PrimedEvenBranch (m : ℕ) (r : StageIndex) : Set Path :=
  xEastEquation447RightOverflowEvent m r ∩
    {s | Even (directCreationTime m (stageNumber r) s)}

/-- The full X-east cardinality failure is covered by the four canonical
winner/parity branches.  No event cover is source data any longer. -/
theorem lemma411412CardinalityFailureEvent_xEast_subset_canonicalBranches
    (m : ℕ) (r : StageIndex) (hm : 0 < m) :
    lemma411412CardinalityFailureEvent m (xIndex east) r ⊆
      xEastEquation447UnprimedEvenBranch m r ∪
        xEastEquation447UnprimedOddBranch m r ∪
          xEastEquation447PrimedOddBranch m r ∪
            xEastEquation447PrimedEvenBranch m r := by
  intro s hs
  have hk : 0 < stageNumber r := by
    unfold stageNumber
    omega
  have hprefix : s ∈ prefixPairingEvent m (xIndex east) (stageNumber r) :=
    prefixPairingEvent_mono m (xIndex east) (Nat.le_succ _) hs.1
  have hover := xEast_nearFavorite_overflow_subset_winner_overflows
    m (stageNumber r) kappaOne hm hk hs.2
  rcases hover with hleft | hright
  · have hbase : s ∈ xEastEquation447LeftOverflowEvent m r :=
      ⟨hprefix, hleft⟩
    by_cases heven : Even (directCreationTime m (stageNumber r) s)
    · have ha : s ∈ xEastEquation447UnprimedEvenBranch m r :=
        ⟨hbase, heven⟩
      exact Or.inl (Or.inl (Or.inl ha))
    · have hb : s ∈ xEastEquation447UnprimedOddBranch m r :=
        ⟨hbase, heven⟩
      exact Or.inl (Or.inl (Or.inr hb))
  · have hbase : s ∈ xEastEquation447RightOverflowEvent m r :=
      ⟨hprefix, hright⟩
    by_cases heven : Even (directCreationTime m (stageNumber r) s)
    · have hd : s ∈ xEastEquation447PrimedEvenBranch m r :=
        ⟨hbase, heven⟩
      exact Or.inr hd
    · have hc : s ∈ xEastEquation447PrimedOddBranch m r :=
        ⟨hbase, heven⟩
      exact Or.inl (Or.inr hc)

/-- The finite-branch stopped-profile premise restricted to one pairing.
This is the pointwise-in-pairing component of
`Prop47Lemma411412FiniteBranchStoppedProfileInputs`. -/
def Prop47Lemma411412FiniteBranchStoppedProfileInputsAt
    (i : Fin 6) (branchCount cWindow : ℕ)
    (C rhoCoeff : ℝ) : Prop :=
  ∀ᶠ m : ℕ in atTop, ∀ r : StageIndex,
    ∃ branchFailure : Fin branchCount → Set Path,
      ∃ rho : Fin branchCount → ℝ,
      ∃ atoms : (j : Fin branchCount) → ℕ →
          StoppedEquation447BranchAtom cWindow m C
            (branchFailure j) (rho j),
        lemma411412CardinalityFailureEvent m i r ⊆ ⋃ j, branchFailure j ∧
        (∀ j, rhoCoeff * Real.log (m : ℝ) ^ 2 ≤ rho j) ∧
        (∀ j, branchFailure j ⊆ ⋃ eta, (atoms j eta).pathAtom) ∧
        (∀ j eta, (atoms j eta).thetaPathEvent ⊆
          stoppedThetaEvent (sourceCanonicalProfiles i) (canonicalCStar i)
            m (stageNumber r)) ∧
        ∀ j, Pairwise fun eta zeta ↦
          Disjoint (atoms j eta).pathAtom (atoms j zeta).pathAtom

/-- The one-pairing interface is literally a component of the existing
all-six-pairing finite-branch input. -/
theorem finiteBranchStoppedProfileInputsAt_of_all
    (i : Fin 6) (branchCount cWindow : ℕ)
    (C rhoCoeff : ℝ)
    (h : Prop47Lemma411412FiniteBranchStoppedProfileInputs
      branchCount cWindow C rhoCoeff) :
    Prop47Lemma411412FiniteBranchStoppedProfileInputsAt
      i branchCount cWindow C rhoCoeff := by
  filter_upwards [h] with m hm
  exact hm i

/-- Pointwise finite-branch inputs for the six pairings assemble into the
all-pairing interface.  Finiteness of `Fin 6` is essential here: it lets the
six eventual scale bounds be intersected before the pairing is selected. -/
theorem finiteBranchStoppedProfileInputs_of_allAt
    (branchCount cWindow : ℕ) (C rhoCoeff : ℝ)
    (h : ∀ i : Fin 6,
      Prop47Lemma411412FiniteBranchStoppedProfileInputsAt
        i branchCount cWindow C rhoCoeff) :
    Prop47Lemma411412FiniteBranchStoppedProfileInputs
      branchCount cWindow C rhoCoeff := by
  filter_upwards [h 0, h 1, h 2, h 3, h 4, h 5] with
      m h0 h1 h2 h3 h4 h5
  intro i r
  fin_cases i
  · exact h0 r
  · exact h1 r
  · exact h2 r
  · exact h3 r
  · exact h4 r
  · exact h5 r

/-- One-pairing component of the literal deleted-path-witness interface. -/
def Prop47Lemma411412FiniteBranchPathWitnessInputsAt
    (i : Fin 6) (branchCount cWindow : ℕ)
    (c rhoCoeff : ℝ) : Prop :=
  ∀ᶠ m : ℕ in atTop, ∀ r : StageIndex,
    ∃ branchFailure : Fin branchCount → Set Path,
      ∃ rho : Fin branchCount → ℝ,
      ∃ atoms : (j : Fin branchCount) → ℕ →
          StoppedEquation447PathWitnessBranchAtom cWindow m c
            (branchFailure j) (rho j),
        lemma411412CardinalityFailureEvent m i r ⊆ ⋃ j, branchFailure j ∧
        (∀ j, rhoCoeff * Real.log (m : ℝ) ^ 2 ≤ rho j) ∧
        (∀ j, branchFailure j ∩
            HLOZSourceInstantiation.simpleRandomWalkSupport ⊆
          ⋃ eta, (atoms j eta).pathAtom) ∧
        (∀ j eta, (atoms j eta).thetaPathEvent ⊆
          stoppedThetaEvent (sourceCanonicalProfiles i) (canonicalCStar i)
            m (stageNumber r)) ∧
        ∀ j, Pairwise fun eta zeta ↦
          Disjoint (atoms j eta).pathAtom (atoms j zeta).pathAtom

/-- Independently constructed path-witness packages for the six pairings
assemble by a finite intersection of eventual scale bounds. -/
theorem finiteBranchPathWitnessInputs_of_allAt
    (branchCount cWindow : ℕ) (c rhoCoeff : ℝ)
    (h : ∀ i : Fin 6,
      Prop47Lemma411412FiniteBranchPathWitnessInputsAt
        i branchCount cWindow c rhoCoeff) :
    Prop47Lemma411412FiniteBranchPathWitnessInputs
      branchCount cWindow c rhoCoeff := by
  filter_upwards [h 0, h 1, h 2, h 3, h 4, h 5] with
      m h0 h1 h2 h3 h4 h5
  intro i r
  fin_cases i
  · exact h0 r
  · exact h1 r
  · exact h2 r
  · exact h3 r
  · exact h4 r
  · exact h5 r

/-- One-pairing component of the flexible-theta deleted-path-switch
interface. -/
def Prop47Lemma411412FiniteBranchPathWitnessAuxThetaInputsAt
    (thetaTarget : ℕ → Fin 6 → StageIndex → Set Path)
    (i : Fin 6) (branchCount cWindow : ℕ)
    (c rhoCoeff : ℝ) : Prop :=
  ∀ᶠ m : ℕ in atTop, ∀ r : StageIndex,
    ∃ branchFailure : Fin branchCount → Set Path,
      ∃ rho : Fin branchCount → ℝ,
      ∃ atoms : (j : Fin branchCount) → ℕ →
          StoppedEquation447PathWitnessBranchAtom cWindow m c
            (branchFailure j) (rho j),
        lemma411412CardinalityFailureEvent m i r ⊆ ⋃ j, branchFailure j ∧
        (∀ j, rhoCoeff * Real.log (m : ℝ) ^ 2 ≤ rho j) ∧
        (∀ j, branchFailure j ∩
            HLOZSourceInstantiation.simpleRandomWalkSupport ⊆
          ⋃ eta, (atoms j eta).pathAtom) ∧
        (∀ j eta, (atoms j eta).thetaPathEvent ⊆ thetaTarget m i r) ∧
        ∀ j, Pairwise fun eta zeta ↦
          Disjoint (atoms j eta).pathAtom (atoms j zeta).pathAtom

/-- A canonical path-witness input enters the flexible interface when the
chosen auxiliary target is the canonical temporal exception. -/
theorem finiteBranchPathWitnessAuxThetaInputsAt_of_standard
    (thetaTarget : ℕ → Fin 6 → StageIndex → Set Path)
    (i : Fin 6) (branchCount cWindow : ℕ) (c rhoCoeff : ℝ)
    (htheta : ∀ m r, thetaTarget m i r =
      stoppedThetaEvent (sourceCanonicalProfiles i) (canonicalCStar i)
        m (stageNumber r))
    (h : Prop47Lemma411412FiniteBranchPathWitnessInputsAt
      i branchCount cWindow c rhoCoeff) :
    Prop47Lemma411412FiniteBranchPathWitnessAuxThetaInputsAt
      thetaTarget i branchCount cWindow c rhoCoeff := by
  filter_upwards [h] with m hm
  intro r
  rcases hm r with
    ⟨branchFailure, rho, atoms, hcover, hthreshold, hatomCover, hatomTheta,
      hdisjoint⟩
  exact ⟨branchFailure, rho, atoms, hcover, hthreshold, hatomCover,
    fun j eta ↦ (hatomTheta j eta).trans_eq (htheta m r).symm,
    hdisjoint⟩

/-- Pointwise flexible path-witness packages assemble over the six finite
pairing indices. -/
theorem finiteBranchPathWitnessAuxThetaInputs_of_allAt
    (thetaTarget : ℕ → Fin 6 → StageIndex → Set Path)
    (branchCount cWindow : ℕ) (c rhoCoeff : ℝ)
    (h : ∀ i : Fin 6,
      Prop47Lemma411412FiniteBranchPathWitnessAuxThetaInputsAt
        thetaTarget i branchCount cWindow c rhoCoeff) :
    Prop47Lemma411412FiniteBranchPathWitnessAuxThetaInputs
      thetaTarget branchCount cWindow c rhoCoeff := by
  filter_upwards [h 0, h 1, h 2, h 3, h 4, h 5] with
      m h0 h1 h2 h3 h4 h5
  intro i r
  fin_cases i
  · exact h0 r
  · exact h1 r
  · exact h2 r
  · exact h3 r
  · exact h4 r
  · exact h5 r

/-- One-pairing component of the flexible auxiliary-theta interface. -/
def Prop47Lemma411412FiniteBranchAuxThetaInputsAt
    (thetaTarget : ℕ → Fin 6 → StageIndex → Set Path)
    (i : Fin 6) (branchCount cWindow : ℕ)
    (C rhoCoeff : ℝ) : Prop :=
  ∀ᶠ m : ℕ in atTop, ∀ r : StageIndex,
    ∃ branchFailure : Fin branchCount → Set Path,
      ∃ rho : Fin branchCount → ℝ,
      ∃ atoms : (j : Fin branchCount) → ℕ →
          StoppedEquation447BranchAtom cWindow m C
            (branchFailure j) (rho j),
        lemma411412CardinalityFailureEvent m i r ⊆ ⋃ j, branchFailure j ∧
        (∀ j, rhoCoeff * Real.log (m : ℝ) ^ 2 ≤ rho j) ∧
        (∀ j, branchFailure j ⊆ ⋃ eta, (atoms j eta).pathAtom) ∧
        (∀ j eta, (atoms j eta).thetaPathEvent ⊆ thetaTarget m i r) ∧
        ∀ j, Pairwise fun eta zeta ↦
          Disjoint (atoms j eta).pathAtom (atoms j zeta).pathAtom

/-- A standard one-pairing input is a flexible-theta input whenever the
chosen auxiliary target is the canonical temporal `Theta` event. -/
theorem finiteBranchAuxThetaInputsAt_of_standard
    (thetaTarget : ℕ → Fin 6 → StageIndex → Set Path)
    (i : Fin 6) (branchCount cWindow : ℕ) (C rhoCoeff : ℝ)
    (htheta : ∀ m r, thetaTarget m i r =
      stoppedThetaEvent (sourceCanonicalProfiles i) (canonicalCStar i)
        m (stageNumber r))
    (h : Prop47Lemma411412FiniteBranchStoppedProfileInputsAt
      i branchCount cWindow C rhoCoeff) :
    Prop47Lemma411412FiniteBranchAuxThetaInputsAt
      thetaTarget i branchCount cWindow C rhoCoeff := by
  filter_upwards [h] with m hm
  intro r
  rcases hm r with
    ⟨branchFailure, rho, atoms, hcover, hthreshold, hatomCover, hatomTheta,
      hdisjoint⟩
  exact ⟨branchFailure, rho, atoms, hcover, hthreshold, hatomCover,
    fun j eta ↦ (hatomTheta j eta).trans_eq (htheta m r).symm,
    hdisjoint⟩

/-- Pointwise flexible-theta inputs for the six pairings assemble by a
finite intersection of eventual filters. -/
theorem finiteBranchAuxThetaInputs_of_allAt
    (thetaTarget : ℕ → Fin 6 → StageIndex → Set Path)
    (branchCount cWindow : ℕ) (C rhoCoeff : ℝ)
    (h : ∀ i : Fin 6,
      Prop47Lemma411412FiniteBranchAuxThetaInputsAt
        thetaTarget i branchCount cWindow C rhoCoeff) :
    Prop47Lemma411412FiniteBranchAuxThetaInputs
      thetaTarget branchCount cWindow C rhoCoeff := by
  filter_upwards [h 0, h 1, h 2, h 3, h 4, h 5] with
      m h0 h1 h2 h3 h4 h5
  intro i r
  fin_cases i
  · exact h0 r
  · exact h1 r
  · exact h2 r
  · exact h3 r
  · exact h4 r
  · exact h5 r

/-- Literal source data for the four X-east branches at a fixed scale and
creation stage.  The record intentionally has four separate atom families:
their coordinate types are native active-base subtypes and need not agree.
All four use the canonical `rhoCoeff * log(m)^2` threshold, so neither a
branch threshold nor its comparison proof is source data. -/
structure XEastFourBranchSourceData
    (cWindow m : ℕ) (rhoCoeff : ℝ)
    (r : StageIndex) where
  unprimedEvenBranch : Set Path
  unprimedOddBranch : Set Path
  primedOddBranch : Set Path
  primedEvenBranch : Set Path

  unprimedEven : ℕ → UnprimedEvenLeftWinnerSource m
  unprimedOdd : ℕ → UnprimedOddTerminalTieLeftSource m
  primedOdd : ℕ → PrimedOddStrictRightWinnerSource m
  primedEven : ℕ → PrimedEvenTerminalStrictRightSource m

  unprimedEvenRemaining : ∀ eta,
    Equation447SourceBandBranchRemainingData cWindow m
      (rhoCoeff * Real.log (m : ℝ) ^ 2) unprimedEvenBranch
      (stoppedThetaEvent (sourceCanonicalProfiles (xIndex east))
        (canonicalCStar (xIndex east)) m (stageNumber r))
      (unprimedEven eta).pathAtom (unprimedEven eta).profile
      (unprimedEven eta).lazyVector (unprimedEven eta).nextDirection
  unprimedOddRemaining : ∀ eta,
    Equation447SourceBandBranchRemainingData cWindow m
      (rhoCoeff * Real.log (m : ℝ) ^ 2) unprimedOddBranch
      (stoppedThetaEvent (sourceCanonicalProfiles (xIndex east))
        (canonicalCStar (xIndex east)) m (stageNumber r))
      (unprimedOdd eta).pathAtom (unprimedOdd eta).profile
      (unprimedOdd eta).lazyVector (unprimedOdd eta).nextDirection
  primedOddRemaining : ∀ eta,
    Equation447SourceBandBranchRemainingData cWindow m
      (rhoCoeff * Real.log (m : ℝ) ^ 2) primedOddBranch
      (stoppedThetaEvent (sourceCanonicalProfiles (xIndex east))
        (canonicalCStar (xIndex east)) m (stageNumber r))
      (primedOdd eta).pathAtom (primedOdd eta).profile
      (primedOdd eta).lazyVector (primedOdd eta).nextDirection
  primedEvenRemaining : ∀ eta,
    Equation447SourceBandBranchRemainingData cWindow m
      (rhoCoeff * Real.log (m : ℝ) ^ 2) primedEvenBranch
      (stoppedThetaEvent (sourceCanonicalProfiles (xIndex east))
        (canonicalCStar (xIndex east)) m (stageNumber r))
      (primedEven eta).pathAtom (primedEven eta).profile
      (primedEven eta).lazyVector (primedEven eta).nextDirection

  failure_cover : lemma411412CardinalityFailureEvent m (xIndex east) r ⊆
    unprimedEvenBranch ∪ unprimedOddBranch ∪
      primedOddBranch ∪ primedEvenBranch

  unprimedEven_cover : unprimedEvenBranch ⊆
    ⋃ eta, (unprimedEven eta).pathAtom
  unprimedOdd_cover : unprimedOddBranch ⊆
    ⋃ eta, (unprimedOdd eta).pathAtom
  primedOdd_cover : primedOddBranch ⊆
    ⋃ eta, (primedOdd eta).pathAtom
  primedEven_cover : primedEvenBranch ⊆
    ⋃ eta, (primedEven eta).pathAtom

  unprimedEven_disjoint : Pairwise fun eta zeta ↦
    Disjoint (unprimedEven eta).pathAtom (unprimedEven zeta).pathAtom
  unprimedOdd_disjoint : Pairwise fun eta zeta ↦
    Disjoint (unprimedOdd eta).pathAtom (unprimedOdd zeta).pathAtom
  primedOdd_disjoint : Pairwise fun eta zeta ↦
    Disjoint (primedOdd eta).pathAtom (primedOdd zeta).pathAtom
  primedEven_disjoint : Pairwise fun eta zeta ↦
    Disjoint (primedEven eta).pathAtom (primedEven zeta).pathAtom

/-- Literal X-east source data after the deterministic winner/parity split.

Unlike `XEastFourBranchSourceData`, this record has no caller-selected
branch events and no `failure_cover` field.  The four path events are the
canonical quarter-log-square overflow events above; their union covers the
full cardinality failure by
`lemma411412CardinalityFailureEvent_xEast_subset_canonicalBranches`. -/
structure XEastCanonicalFourBranchSourceData
    (cWindow m : ℕ) (r : StageIndex) where
  unprimedEven : ℕ → UnprimedEvenLeftWinnerSource m
  unprimedOdd : ℕ → UnprimedOddTerminalTieLeftSource m
  primedOdd : ℕ → PrimedOddStrictRightWinnerSource m
  primedEven : ℕ → PrimedEvenTerminalStrictRightSource m

  unprimedEvenRemaining : ∀ eta,
    Equation447SourceBandBranchRemainingData cWindow m
      ((1 / 4 : ℝ) * Real.log (m : ℝ) ^ 2)
      (xEastEquation447UnprimedEvenBranch m r)
      (stoppedThetaEvent (sourceCanonicalProfiles (xIndex east))
        (canonicalCStar (xIndex east)) m (stageNumber r))
      (unprimedEven eta).pathAtom (unprimedEven eta).profile
      (unprimedEven eta).lazyVector (unprimedEven eta).nextDirection
  unprimedOddRemaining : ∀ eta,
    Equation447SourceBandBranchRemainingData cWindow m
      ((1 / 4 : ℝ) * Real.log (m : ℝ) ^ 2)
      (xEastEquation447UnprimedOddBranch m r)
      (stoppedThetaEvent (sourceCanonicalProfiles (xIndex east))
        (canonicalCStar (xIndex east)) m (stageNumber r))
      (unprimedOdd eta).pathAtom (unprimedOdd eta).profile
      (unprimedOdd eta).lazyVector (unprimedOdd eta).nextDirection
  primedOddRemaining : ∀ eta,
    Equation447SourceBandBranchRemainingData cWindow m
      ((1 / 4 : ℝ) * Real.log (m : ℝ) ^ 2)
      (xEastEquation447PrimedOddBranch m r)
      (stoppedThetaEvent (sourceCanonicalProfiles (xIndex east))
        (canonicalCStar (xIndex east)) m (stageNumber r))
      (primedOdd eta).pathAtom (primedOdd eta).profile
      (primedOdd eta).lazyVector (primedOdd eta).nextDirection
  primedEvenRemaining : ∀ eta,
    Equation447SourceBandBranchRemainingData cWindow m
      ((1 / 4 : ℝ) * Real.log (m : ℝ) ^ 2)
      (xEastEquation447PrimedEvenBranch m r)
      (stoppedThetaEvent (sourceCanonicalProfiles (xIndex east))
        (canonicalCStar (xIndex east)) m (stageNumber r))
      (primedEven eta).pathAtom (primedEven eta).profile
      (primedEven eta).lazyVector (primedEven eta).nextDirection

  unprimedEven_cover : xEastEquation447UnprimedEvenBranch m r ⊆
    ⋃ eta, (unprimedEven eta).pathAtom
  unprimedOdd_cover : xEastEquation447UnprimedOddBranch m r ⊆
    ⋃ eta, (unprimedOdd eta).pathAtom
  primedOdd_cover : xEastEquation447PrimedOddBranch m r ⊆
    ⋃ eta, (primedOdd eta).pathAtom
  primedEven_cover : xEastEquation447PrimedEvenBranch m r ⊆
    ⋃ eta, (primedEven eta).pathAtom

  unprimedEven_disjoint : Pairwise fun eta zeta ↦
    Disjoint (unprimedEven eta).pathAtom (unprimedEven zeta).pathAtom
  unprimedOdd_disjoint : Pairwise fun eta zeta ↦
    Disjoint (unprimedOdd eta).pathAtom (unprimedOdd zeta).pathAtom
  primedOdd_disjoint : Pairwise fun eta zeta ↦
    Disjoint (primedOdd eta).pathAtom (primedOdd zeta).pathAtom
  primedEven_disjoint : Pairwise fun eta zeta ↦
    Disjoint (primedEven eta).pathAtom (primedEven zeta).pathAtom

namespace XEastCanonicalFourBranchSourceData

variable {cWindow m : ℕ} {r : StageIndex}

/-- Forget the fact that the branch events and their global cover were
constructed by Lean.  This is the precise bridge to the older flexible
four-event record used by the transport layer. -/
noncomputable def toFourBranchSourceData
    (D : XEastCanonicalFourBranchSourceData cWindow m r) :
    XEastFourBranchSourceData cWindow m (1 / 4 : ℝ) r where
  unprimedEvenBranch := xEastEquation447UnprimedEvenBranch m r
  unprimedOddBranch := xEastEquation447UnprimedOddBranch m r
  primedOddBranch := xEastEquation447PrimedOddBranch m r
  primedEvenBranch := xEastEquation447PrimedEvenBranch m r
  unprimedEven := D.unprimedEven
  unprimedOdd := D.unprimedOdd
  primedOdd := D.primedOdd
  primedEven := D.primedEven
  unprimedEvenRemaining := D.unprimedEvenRemaining
  unprimedOddRemaining := D.unprimedOddRemaining
  primedOddRemaining := D.primedOddRemaining
  primedEvenRemaining := D.primedEvenRemaining
  failure_cover :=
    lemma411412CardinalityFailureEvent_xEast_subset_canonicalBranches
      m r (D.unprimedEven 0).m_pos
  unprimedEven_cover := D.unprimedEven_cover
  unprimedOdd_cover := D.unprimedOdd_cover
  primedOdd_cover := D.primedOdd_cover
  primedEven_cover := D.primedEven_cover
  unprimedEven_disjoint := D.unprimedEven_disjoint
  unprimedOdd_disjoint := D.unprimedOdd_disjoint
  primedOdd_disjoint := D.primedOdd_disjoint
  primedEven_disjoint := D.primedEven_disjoint

end XEastCanonicalFourBranchSourceData

namespace XEastFourBranchSourceData

variable {cWindow m : ℕ} {rhoCoeff : ℝ}
    {r : StageIndex}
    (D : XEastFourBranchSourceData
      cWindow m rhoCoeff r)

/-- The four literal branch events, with the order used by the finite union
bound. -/
def branchEvent : Fin 4 → Set Path := ![
  D.unprimedEvenBranch,
  D.unprimedOddBranch,
  D.primedOddBranch,
  D.primedEvenBranch]

/-- Every winner/parity branch uses the canonical threshold retained by the
four-way pigeonhole step. -/
noncomputable def rho
    (_D : XEastFourBranchSourceData cWindow m rhoCoeff r) : Fin 4 → ℝ :=
  fun _ ↦ rhoCoeff * Real.log (m : ℝ) ^ 2

/-- The four checked stopped atoms.  Their map-law fields are filled by the
four source constructors, not by the caller. -/
noncomputable def atoms (growth : SourceWindowGrowth cWindow m)
    (j : Fin 4) (eta : ℕ) :
    StoppedEquation447BranchAtom cWindow m
      (Real.exp (sourceAdjacentComparisonExponent cWindow))
      (D.branchEvent j) (D.rho j) := by
  by_cases h0 : j = 0
  · subst j
    simpa [branchEvent, rho] using
      (D.unprimedEven eta).toStoppedEquation447BranchAtom cWindow
      (Real.exp (sourceAdjacentComparisonExponent cWindow))
        (rhoCoeff * Real.log (m : ℝ) ^ 2) D.unprimedEvenBranch
        ((D.unprimedEvenRemaining eta).toCodedBranchRemainingData
          (D.unprimedEven eta).profile_lt growth |>.toRemainingData)
  by_cases h1 : j = 1
  · subst j
    simpa [branchEvent, rho] using
      (D.unprimedOdd eta).toStoppedEquation447BranchAtom cWindow
      (Real.exp (sourceAdjacentComparisonExponent cWindow))
        (rhoCoeff * Real.log (m : ℝ) ^ 2) D.unprimedOddBranch
        ((D.unprimedOddRemaining eta).toCodedBranchRemainingData
          (D.unprimedOdd eta).profile_lt growth |>.toRemainingData)
  by_cases h2 : j = 2
  · subst j
    simpa [branchEvent, rho] using
      (D.primedOdd eta).toStoppedEquation447BranchAtom cWindow
      (Real.exp (sourceAdjacentComparisonExponent cWindow))
        (rhoCoeff * Real.log (m : ℝ) ^ 2) D.primedOddBranch
        ((D.primedOddRemaining eta).toCodedBranchRemainingData
          (D.primedOdd eta).profile_lt growth |>.toRemainingData)
  have h3 : j = 3 := by
    apply Fin.ext
    omega
  subst j
  simpa [branchEvent, rho] using
      (D.primedEven eta).toStoppedEquation447BranchAtom cWindow
      (Real.exp (sourceAdjacentComparisonExponent cWindow))
        (rhoCoeff * Real.log (m : ℝ) ^ 2) D.primedEvenBranch
        ((D.primedEvenRemaining eta).toCodedBranchRemainingData
          (D.primedEven eta).profile_lt growth |>.toRemainingData)

@[simp] theorem atoms_zero_pathAtom (growth : SourceWindowGrowth cWindow m)
    (eta : ℕ) :
    (D.atoms growth (0 : Fin 4) eta).pathAtom =
      (D.unprimedEven eta).pathAtom := by
  rfl

@[simp] theorem atoms_one_pathAtom (growth : SourceWindowGrowth cWindow m)
    (eta : ℕ) :
    (D.atoms growth (1 : Fin 4) eta).pathAtom =
      (D.unprimedOdd eta).pathAtom := by
  rfl

@[simp] theorem atoms_two_pathAtom (growth : SourceWindowGrowth cWindow m)
    (eta : ℕ) :
    (D.atoms growth (2 : Fin 4) eta).pathAtom =
      (D.primedOdd eta).pathAtom := by
  rfl

@[simp] theorem atoms_three_pathAtom (growth : SourceWindowGrowth cWindow m)
    (eta : ℕ) :
    (D.atoms growth (3 : Fin 4) eta).pathAtom =
      (D.primedEven eta).pathAtom := by
  rfl

theorem failure_subset_iUnion_branchEvent :
    lemma411412CardinalityFailureEvent m (xIndex east) r ⊆
      ⋃ j, D.branchEvent j := by
  intro s hs
  have h : ((s ∈ D.unprimedEvenBranch ∨ s ∈ D.unprimedOddBranch) ∨
      s ∈ D.primedOddBranch) ∨ s ∈ D.primedEvenBranch := by
    simpa only [Set.mem_union] using D.failure_cover hs
  rcases h with ((h | h) | h) | h
  · exact Set.mem_iUnion.mpr ⟨0, h⟩
  · exact Set.mem_iUnion.mpr ⟨1, h⟩
  · exact Set.mem_iUnion.mpr ⟨2, h⟩
  · exact Set.mem_iUnion.mpr ⟨3, h⟩

theorem branch_threshold (j : Fin 4) :
    rhoCoeff * Real.log (m : ℝ) ^ 2 ≤ D.rho j := by
  simp [rho]

theorem branchEvent_subset_iUnion_atoms
    (growth : SourceWindowGrowth cWindow m) (j : Fin 4) :
    D.branchEvent j ⊆ ⋃ eta, (D.atoms growth j eta).pathAtom := by
  fin_cases j
  · simpa [branchEvent] using D.unprimedEven_cover
  · simpa [branchEvent] using D.unprimedOdd_cover
  · simpa [branchEvent] using D.primedOdd_cover
  · simpa [branchEvent] using D.primedEven_cover

theorem atoms_pairwise_disjoint
    (growth : SourceWindowGrowth cWindow m) (j : Fin 4) :
    Pairwise fun eta zeta ↦
      Disjoint (D.atoms growth j eta).pathAtom
        (D.atoms growth j zeta).pathAtom := by
  fin_cases j
  · simpa using D.unprimedEven_disjoint
  · simpa using D.unprimedOdd_disjoint
  · simpa using D.primedOdd_disjoint
  · simpa using D.primedEven_disjoint

theorem atom_theta_subset (growth : SourceWindowGrowth cWindow m)
    (j : Fin 4) (eta : ℕ) :
    (D.atoms growth j eta).thetaPathEvent ⊆
      stoppedThetaEvent (sourceCanonicalProfiles (xIndex east))
        (canonicalCStar (xIndex east)) m (stageNumber r) := by
  fin_cases j
  · exact le_rfl
  · exact le_rfl
  · exact le_rfl
  · exact le_rfl

/-- Package the four literal source families as the exact existential
witness expected by the finite-branch connector at X-east. -/
theorem finiteBranchWitness
    (D : XEastFourBranchSourceData
      cWindow m rhoCoeff r)
    (growth : SourceWindowGrowth cWindow m) :
    ∃ branchFailure : Fin 4 → Set Path,
      ∃ rho : Fin 4 → ℝ,
      ∃ atoms : (j : Fin 4) → ℕ →
          StoppedEquation447BranchAtom cWindow m
            (Real.exp (sourceAdjacentComparisonExponent cWindow))
            (branchFailure j) (rho j),
        lemma411412CardinalityFailureEvent m (xIndex east) r ⊆
            ⋃ j, branchFailure j ∧
        (∀ j, rhoCoeff * Real.log (m : ℝ) ^ 2 ≤ rho j) ∧
        (∀ j, branchFailure j ⊆ ⋃ eta, (atoms j eta).pathAtom) ∧
        (∀ j eta, (atoms j eta).thetaPathEvent ⊆
          stoppedThetaEvent (sourceCanonicalProfiles (xIndex east))
            (canonicalCStar (xIndex east)) m (stageNumber r)) ∧
        ∀ j, Pairwise fun eta zeta ↦
          Disjoint (atoms j eta).pathAtom (atoms j zeta).pathAtom := by
  exact ⟨branchEvent D, rho D, atoms D growth,
    failure_subset_iUnion_branchEvent D, branch_threshold D,
    branchEvent_subset_iUnion_atoms D growth,
    atom_theta_subset D growth, atoms_pairwise_disjoint D growth⟩

end XEastFourBranchSourceData

/-- Eventual literal four-branch source data for the X-east pairing. -/
def Prop47Lemma411412XEastFourBranchSourceInputs
    (cWindow : ℕ) (rhoCoeff : ℝ) : Prop :=
  ∀ᶠ m : ℕ in atTop, ∀ r : StageIndex,
    Nonempty (XEastFourBranchSourceData
      cWindow m rhoCoeff r)

/-- Eventual X-east source data with the winner/parity events and their
global cover fixed canonically.  This is the source-facing interface used by
the final literal closure. -/
def Prop47Lemma411412XEastCanonicalFourBranchSourceInputs
    (cWindow : ℕ) : Prop :=
  ∀ᶠ m : ℕ in atTop, ∀ r : StageIndex,
    Nonempty (XEastCanonicalFourBranchSourceData cWindow m r)

/-- Canonical source inputs discharge the older flexible event package at
the source quarter-log-square coefficient. -/
theorem xEastFourBranchSourceInputs_of_canonical
    (cWindow : ℕ)
    (h : Prop47Lemma411412XEastCanonicalFourBranchSourceInputs cWindow) :
    Prop47Lemma411412XEastFourBranchSourceInputs cWindow (1 / 4 : ℝ) := by
  filter_upwards [h] with m hm
  intro r
  rcases hm r with ⟨D⟩
  exact ⟨D.toFourBranchSourceData⟩

/-- The four literal X-east constructors discharge the stopped map-law and
measurability portions of the finite-branch connector. -/
theorem finiteBranchStoppedProfileInputsAt_xEast_of_source
    (cWindow : ℕ) (rhoCoeff : ℝ)
    (h : Prop47Lemma411412XEastFourBranchSourceInputs
      cWindow rhoCoeff) :
    Prop47Lemma411412FiniteBranchStoppedProfileInputsAt
      (xIndex east) 4 cWindow
        (Real.exp (sourceAdjacentComparisonExponent cWindow)) rhoCoeff := by
  filter_upwards [h, eventually_sourceWindowGrowth cWindow] with m hm growth
  intro r
  rcases hm r with ⟨D⟩
  exact XEastFourBranchSourceData.finiteBranchWitness D growth

/-! ### Literal path-witness base step at X-east -/

/-- Canonical four-way X-east data for the actual deleted-path switch in
(4.47).  The branch events and their global cover are already proved above;
the remaining source fields are the four stopped source atomizations and the
fixed-cardinality bad-path/witness-path switch, including (4.54). -/
structure XEastCanonicalFourBranchPathWitnessSourceData
    (cWindow m : ℕ) (c : ℝ) (r : StageIndex) where
  unprimedEven : ℕ → UnprimedEvenLeftWinnerSource m
  unprimedOdd : ℕ → UnprimedOddTerminalTieLeftSource m
  primedOdd : ℕ → PrimedOddStrictRightWinnerSource m
  primedEven : ℕ → PrimedEvenTerminalStrictRightSource m
  unprimedEvenRemaining : ∀ eta,
    Equation447PathWitnessBranchRemainingData cWindow m c
      ((1 / 4 : ℝ) * Real.log (m : ℝ) ^ 2)
      (xEastEquation447UnprimedEvenBranch m r)
      (unprimedEven eta).pathAtom (unprimedEven eta).profile
      (unprimedEven eta).lazyVector (unprimedEven eta).nextDirection
  unprimedOddRemaining : ∀ eta,
    Equation447PathWitnessBranchRemainingData cWindow m c
      ((1 / 4 : ℝ) * Real.log (m : ℝ) ^ 2)
      (xEastEquation447UnprimedOddBranch m r)
      (unprimedOdd eta).pathAtom (unprimedOdd eta).profile
      (unprimedOdd eta).lazyVector (unprimedOdd eta).nextDirection
  primedOddRemaining : ∀ eta,
    Equation447PathWitnessBranchRemainingData cWindow m c
      ((1 / 4 : ℝ) * Real.log (m : ℝ) ^ 2)
      (xEastEquation447PrimedOddBranch m r)
      (primedOdd eta).pathAtom (primedOdd eta).profile
      (primedOdd eta).lazyVector (primedOdd eta).nextDirection
  primedEvenRemaining : ∀ eta,
    Equation447PathWitnessBranchRemainingData cWindow m c
      ((1 / 4 : ℝ) * Real.log (m : ℝ) ^ 2)
      (xEastEquation447PrimedEvenBranch m r)
      (primedEven eta).pathAtom (primedEven eta).profile
      (primedEven eta).lazyVector (primedEven eta).nextDirection
  unprimedEven_cover : xEastEquation447UnprimedEvenBranch m r ⊆
    ⋃ eta, (unprimedEven eta).pathAtom
  unprimedOdd_cover : xEastEquation447UnprimedOddBranch m r ⊆
    ⋃ eta, (unprimedOdd eta).pathAtom
  primedOdd_cover : xEastEquation447PrimedOddBranch m r ⊆
    ⋃ eta, (primedOdd eta).pathAtom
  primedEven_cover : xEastEquation447PrimedEvenBranch m r ⊆
    ⋃ eta, (primedEven eta).pathAtom
  unprimedEven_theta : ∀ eta,
    (unprimedEvenRemaining eta).thetaPathEvent ⊆
      stoppedThetaEvent (sourceCanonicalProfiles (xIndex east))
        (canonicalCStar (xIndex east)) m (stageNumber r)
  unprimedOdd_theta : ∀ eta,
    (unprimedOddRemaining eta).thetaPathEvent ⊆
      stoppedThetaEvent (sourceCanonicalProfiles (xIndex east))
        (canonicalCStar (xIndex east)) m (stageNumber r)
  primedOdd_theta : ∀ eta,
    (primedOddRemaining eta).thetaPathEvent ⊆
      stoppedThetaEvent (sourceCanonicalProfiles (xIndex east))
        (canonicalCStar (xIndex east)) m (stageNumber r)
  primedEven_theta : ∀ eta,
    (primedEvenRemaining eta).thetaPathEvent ⊆
      stoppedThetaEvent (sourceCanonicalProfiles (xIndex east))
        (canonicalCStar (xIndex east)) m (stageNumber r)
  unprimedEven_disjoint : Pairwise fun eta zeta ↦
    Disjoint (unprimedEven eta).pathAtom (unprimedEven zeta).pathAtom
  unprimedOdd_disjoint : Pairwise fun eta zeta ↦
    Disjoint (unprimedOdd eta).pathAtom (unprimedOdd zeta).pathAtom
  primedOdd_disjoint : Pairwise fun eta zeta ↦
    Disjoint (primedOdd eta).pathAtom (primedOdd zeta).pathAtom
  primedEven_disjoint : Pairwise fun eta zeta ↦
    Disjoint (primedEven eta).pathAtom (primedEven zeta).pathAtom

namespace XEastCanonicalFourBranchPathWitnessSourceData

variable {cWindow m : ℕ} {c : ℝ} {r : StageIndex}
    (D : XEastCanonicalFourBranchPathWitnessSourceData cWindow m c r)

def branchEvent
    (_D : XEastCanonicalFourBranchPathWitnessSourceData cWindow m c r) :
    Fin 4 → Set Path := fun j ↦
  match j.1 with
  | 0 => xEastEquation447UnprimedEvenBranch m r
  | 1 => xEastEquation447UnprimedOddBranch m r
  | 2 => xEastEquation447PrimedOddBranch m r
  | _ => xEastEquation447PrimedEvenBranch m r

noncomputable def rho
    (_D : XEastCanonicalFourBranchPathWitnessSourceData cWindow m c r) :
    Fin 4 → ℝ :=
  fun _ ↦ (1 / 4 : ℝ) * Real.log (m : ℝ) ^ 2

noncomputable def atoms (j : Fin 4) (eta : ℕ) :
    StoppedEquation447PathWitnessBranchAtom cWindow m c
      (D.branchEvent j) (D.rho j) := by
  by_cases h0 : j = 0
  · subst j
    exact (D.unprimedEven eta).toStoppedEquation447PathWitnessBranchAtom
        cWindow c ((1 / 4 : ℝ) * Real.log (m : ℝ) ^ 2)
        (xEastEquation447UnprimedEvenBranch m r)
        (D.unprimedEvenRemaining eta)
  by_cases h1 : j = 1
  · subst j
    exact (D.unprimedOdd eta).toStoppedEquation447PathWitnessBranchAtom
        cWindow c ((1 / 4 : ℝ) * Real.log (m : ℝ) ^ 2)
        (xEastEquation447UnprimedOddBranch m r)
        (D.unprimedOddRemaining eta)
  by_cases h2 : j = 2
  · subst j
    exact (D.primedOdd eta).toStoppedEquation447PathWitnessBranchAtom
        cWindow c ((1 / 4 : ℝ) * Real.log (m : ℝ) ^ 2)
        (xEastEquation447PrimedOddBranch m r)
        (D.primedOddRemaining eta)
  have h3 : j = 3 := by
    apply Fin.ext
    omega
  subst j
  exact (D.primedEven eta).toStoppedEquation447PathWitnessBranchAtom
        cWindow c ((1 / 4 : ℝ) * Real.log (m : ℝ) ^ 2)
        (xEastEquation447PrimedEvenBranch m r)
        (D.primedEvenRemaining eta)

@[simp] theorem atoms_zero_pathAtom (eta : ℕ) :
    (D.atoms (0 : Fin 4) eta).pathAtom = (D.unprimedEven eta).pathAtom := by
  rfl

@[simp] theorem atoms_one_pathAtom (eta : ℕ) :
    (D.atoms (1 : Fin 4) eta).pathAtom = (D.unprimedOdd eta).pathAtom := by
  rfl

@[simp] theorem atoms_two_pathAtom (eta : ℕ) :
    (D.atoms (2 : Fin 4) eta).pathAtom = (D.primedOdd eta).pathAtom := by
  rfl

@[simp] theorem atoms_three_pathAtom (eta : ℕ) :
    (D.atoms (3 : Fin 4) eta).pathAtom = (D.primedEven eta).pathAtom := by
  rfl

@[simp] theorem atoms_zero_thetaPathEvent (eta : ℕ) :
    (D.atoms (0 : Fin 4) eta).thetaPathEvent =
      (D.unprimedEvenRemaining eta).thetaPathEvent := by
  rfl

@[simp] theorem atoms_one_thetaPathEvent (eta : ℕ) :
    (D.atoms (1 : Fin 4) eta).thetaPathEvent =
      (D.unprimedOddRemaining eta).thetaPathEvent := by
  rfl

@[simp] theorem atoms_two_thetaPathEvent (eta : ℕ) :
    (D.atoms (2 : Fin 4) eta).thetaPathEvent =
      (D.primedOddRemaining eta).thetaPathEvent := by
  rfl

@[simp] theorem atoms_three_thetaPathEvent (eta : ℕ) :
    (D.atoms (3 : Fin 4) eta).thetaPathEvent =
      (D.primedEvenRemaining eta).thetaPathEvent := by
  rfl

theorem finiteBranchWitness
    (D : XEastCanonicalFourBranchPathWitnessSourceData cWindow m c r) :
    ∃ branchFailure : Fin 4 → Set Path,
      ∃ rho : Fin 4 → ℝ,
      ∃ atoms : (j : Fin 4) → ℕ →
          StoppedEquation447PathWitnessBranchAtom cWindow m c
            (branchFailure j) (rho j),
        lemma411412CardinalityFailureEvent m (xIndex east) r ⊆
            ⋃ j, branchFailure j ∧
        (∀ j, (1 / 4 : ℝ) * Real.log (m : ℝ) ^ 2 ≤ rho j) ∧
        (∀ j, branchFailure j ⊆ ⋃ eta, (atoms j eta).pathAtom) ∧
        (∀ j eta, (atoms j eta).thetaPathEvent ⊆
          stoppedThetaEvent (sourceCanonicalProfiles (xIndex east))
            (canonicalCStar (xIndex east)) m (stageNumber r)) ∧
        ∀ j, Pairwise fun eta zeta ↦
          Disjoint (atoms j eta).pathAtom (atoms j zeta).pathAtom := by
  refine ⟨D.branchEvent, D.rho, D.atoms, ?_, ?_, ?_, ?_, ?_⟩
  · intro s hs
    have h := lemma411412CardinalityFailureEvent_xEast_subset_canonicalBranches
      m r (D.unprimedEven 0).m_pos hs
    rcases h with ((h | h) | h) | h
    · exact Set.mem_iUnion.mpr ⟨0, h⟩
    · exact Set.mem_iUnion.mpr ⟨1, h⟩
    · exact Set.mem_iUnion.mpr ⟨2, h⟩
    · exact Set.mem_iUnion.mpr ⟨3, h⟩
  · intro j
    simp [rho]
  · intro j
    fin_cases j
    · simpa [branchEvent] using D.unprimedEven_cover
    · simpa [branchEvent] using D.unprimedOdd_cover
    · simpa [branchEvent] using D.primedOdd_cover
    · simpa [branchEvent] using D.primedEven_cover
  · intro j eta
    fin_cases j
    · simpa using D.unprimedEven_theta eta
    · simpa using D.unprimedOdd_theta eta
    · simpa using D.primedOdd_theta eta
    · simpa using D.primedEven_theta eta
  · intro j
    fin_cases j
    · simpa using D.unprimedEven_disjoint
    · simpa using D.unprimedOdd_disjoint
    · simpa using D.primedOdd_disjoint
    · simpa using D.primedEven_disjoint

end XEastCanonicalFourBranchPathWitnessSourceData

def Prop47Lemma411412XEastCanonicalFourBranchPathWitnessSourceInputs
    (cWindow : ℕ) (c : ℝ) : Prop :=
  ∀ᶠ m : ℕ in atTop, ∀ r : StageIndex,
    Nonempty (XEastCanonicalFourBranchPathWitnessSourceData cWindow m c r)

theorem finiteBranchPathWitnessInputsAt_xEast_of_source
    (cWindow : ℕ) (c : ℝ)
    (h : Prop47Lemma411412XEastCanonicalFourBranchPathWitnessSourceInputs
      cWindow c) :
    Prop47Lemma411412FiniteBranchPathWitnessInputsAt
      (xIndex east) 4 cWindow c (1 / 4 : ℝ) := by
  filter_upwards [h] with m hm
  intro r
  rcases hm r with ⟨D⟩
  rcases D.finiteBranchWitness with
    ⟨branchFailure, rho, atoms, hcover, hthreshold, hatomCover,
      hatomTheta, hdisjoint⟩
  refine ⟨branchFailure, rho, atoms, hcover, hthreshold, ?_,
    hatomTheta, hdisjoint⟩
  intro j s hs
  exact hatomCover j hs.1

/-! ### Conditional-categorical source form of the path witness -/

/-- The four canonical X-east branches with the fixed-cardinality switch
expressed by the source's conditional categorical cells and binomial-layer
comparison.  The measure-level changed-path inequality is derived by
`Equation447CategoricalPathWitnessBranchRemainingData.toRemainingData`. -/
structure XEastCanonicalFourBranchCategoricalPathWitnessSourceData
    (cWindow m : ℕ) (c : ℝ) (r : StageIndex) where
  unprimedEven : ℕ → UnprimedEvenLeftWinnerSource m
  unprimedOdd : ℕ → UnprimedOddTerminalTieLeftSource m
  primedOdd : ℕ → PrimedOddStrictRightWinnerSource m
  primedEven : ℕ → PrimedEvenTerminalStrictRightSource m
  unprimedEvenRemaining : ∀ eta,
    Equation447CategoricalPathWitnessBranchRemainingData cWindow m c
      ((1 / 4 : ℝ) * Real.log (m : ℝ) ^ 2)
      (xEastEquation447UnprimedEvenBranch m r)
      (unprimedEven eta).pathAtom (unprimedEven eta).profile
      (unprimedEven eta).lazyVector (unprimedEven eta).nextDirection
  unprimedOddRemaining : ∀ eta,
    Equation447CategoricalPathWitnessBranchRemainingData cWindow m c
      ((1 / 4 : ℝ) * Real.log (m : ℝ) ^ 2)
      (xEastEquation447UnprimedOddBranch m r)
      (unprimedOdd eta).pathAtom (unprimedOdd eta).profile
      (unprimedOdd eta).lazyVector (unprimedOdd eta).nextDirection
  primedOddRemaining : ∀ eta,
    Equation447CategoricalPathWitnessBranchRemainingData cWindow m c
      ((1 / 4 : ℝ) * Real.log (m : ℝ) ^ 2)
      (xEastEquation447PrimedOddBranch m r)
      (primedOdd eta).pathAtom (primedOdd eta).profile
      (primedOdd eta).lazyVector (primedOdd eta).nextDirection
  primedEvenRemaining : ∀ eta,
    Equation447CategoricalPathWitnessBranchRemainingData cWindow m c
      ((1 / 4 : ℝ) * Real.log (m : ℝ) ^ 2)
      (xEastEquation447PrimedEvenBranch m r)
      (primedEven eta).pathAtom (primedEven eta).profile
      (primedEven eta).lazyVector (primedEven eta).nextDirection
  unprimedEven_cover : xEastEquation447UnprimedEvenBranch m r ⊆
    ⋃ eta, (unprimedEven eta).pathAtom
  unprimedOdd_cover : xEastEquation447UnprimedOddBranch m r ⊆
    ⋃ eta, (unprimedOdd eta).pathAtom
  primedOdd_cover : xEastEquation447PrimedOddBranch m r ⊆
    ⋃ eta, (primedOdd eta).pathAtom
  primedEven_cover : xEastEquation447PrimedEvenBranch m r ⊆
    ⋃ eta, (primedEven eta).pathAtom
  unprimedEven_theta : ∀ eta,
    (unprimedEvenRemaining eta).thetaPathEvent ⊆
      stoppedThetaEvent (sourceCanonicalProfiles (xIndex east))
        (canonicalCStar (xIndex east)) m (stageNumber r)
  unprimedOdd_theta : ∀ eta,
    (unprimedOddRemaining eta).thetaPathEvent ⊆
      stoppedThetaEvent (sourceCanonicalProfiles (xIndex east))
        (canonicalCStar (xIndex east)) m (stageNumber r)
  primedOdd_theta : ∀ eta,
    (primedOddRemaining eta).thetaPathEvent ⊆
      stoppedThetaEvent (sourceCanonicalProfiles (xIndex east))
        (canonicalCStar (xIndex east)) m (stageNumber r)
  primedEven_theta : ∀ eta,
    (primedEvenRemaining eta).thetaPathEvent ⊆
      stoppedThetaEvent (sourceCanonicalProfiles (xIndex east))
        (canonicalCStar (xIndex east)) m (stageNumber r)
  unprimedEven_disjoint : Pairwise fun eta zeta ↦
    Disjoint (unprimedEven eta).pathAtom (unprimedEven zeta).pathAtom
  unprimedOdd_disjoint : Pairwise fun eta zeta ↦
    Disjoint (unprimedOdd eta).pathAtom (unprimedOdd zeta).pathAtom
  primedOdd_disjoint : Pairwise fun eta zeta ↦
    Disjoint (primedOdd eta).pathAtom (primedOdd zeta).pathAtom
  primedEven_disjoint : Pairwise fun eta zeta ↦
    Disjoint (primedEven eta).pathAtom (primedEven zeta).pathAtom

namespace XEastCanonicalFourBranchCategoricalPathWitnessSourceData

variable {cWindow m : ℕ} {c : ℝ} {r : StageIndex}

/-- Derive the existing path-witness package branchwise. -/
noncomputable def toPathWitnessSourceData
    (D : XEastCanonicalFourBranchCategoricalPathWitnessSourceData
      cWindow m c r) :
    XEastCanonicalFourBranchPathWitnessSourceData cWindow m c r where
  unprimedEven := D.unprimedEven
  unprimedOdd := D.unprimedOdd
  primedOdd := D.primedOdd
  primedEven := D.primedEven
  unprimedEvenRemaining := fun eta ↦
    (D.unprimedEvenRemaining eta).toRemainingData
  unprimedOddRemaining := fun eta ↦
    (D.unprimedOddRemaining eta).toRemainingData
  primedOddRemaining := fun eta ↦
    (D.primedOddRemaining eta).toRemainingData
  primedEvenRemaining := fun eta ↦
    (D.primedEvenRemaining eta).toRemainingData
  unprimedEven_cover := D.unprimedEven_cover
  unprimedOdd_cover := D.unprimedOdd_cover
  primedOdd_cover := D.primedOdd_cover
  primedEven_cover := D.primedEven_cover
  unprimedEven_theta := D.unprimedEven_theta
  unprimedOdd_theta := D.unprimedOdd_theta
  primedOdd_theta := D.primedOdd_theta
  primedEven_theta := D.primedEven_theta
  unprimedEven_disjoint := D.unprimedEven_disjoint
  unprimedOdd_disjoint := D.unprimedOdd_disjoint
  primedOdd_disjoint := D.primedOdd_disjoint
  primedEven_disjoint := D.primedEven_disjoint

end XEastCanonicalFourBranchCategoricalPathWitnessSourceData

def Prop47Lemma411412XEastCanonicalFourBranchCategoricalPathWitnessSourceInputs
    (cWindow : ℕ) (c : ℝ) : Prop :=
  ∀ᶠ m : ℕ in atTop, ∀ r : StageIndex,
    Nonempty (XEastCanonicalFourBranchCategoricalPathWitnessSourceData
      cWindow m c r)

theorem xEastPathWitnessSourceInputs_of_categorical
    (cWindow : ℕ) (c : ℝ)
    (h :
      Prop47Lemma411412XEastCanonicalFourBranchCategoricalPathWitnessSourceInputs
        cWindow c) :
    Prop47Lemma411412XEastCanonicalFourBranchPathWitnessSourceInputs
      cWindow c := by
  filter_upwards [h] with m hm
  intro r
  rcases hm r with ⟨D⟩
  exact ⟨D.toPathWitnessSourceData⟩

/-! ### Categorical source form with the binomial layer internalized -/

/-- The four canonical X-east branches after the numerical binomial-layer
comparison has been removed from the source assumptions.  A single positive
coordinate ratio determines both the canonical witness cardinality and the
exponential rate. -/
structure XEastCanonicalFourBranchOptimalCategoricalPathWitnessSourceData
    (cWindow m : ℕ) (ratioC : ℝ) (r : StageIndex) where
  unprimedEven : ℕ → UnprimedEvenLeftWinnerSource m
  unprimedOdd : ℕ → UnprimedOddTerminalTieLeftSource m
  primedOdd : ℕ → PrimedOddStrictRightWinnerSource m
  primedEven : ℕ → PrimedEvenTerminalStrictRightSource m
  unprimedEvenRemaining : ∀ eta,
    Equation447OptimalCategoricalPathWitnessBranchRemainingData
      cWindow m ratioC ((1 / 4 : ℝ) * Real.log (m : ℝ) ^ 2)
      (xEastEquation447UnprimedEvenBranch m r)
      (unprimedEven eta).pathAtom (unprimedEven eta).profile
      (unprimedEven eta).lazyVector (unprimedEven eta).nextDirection
  unprimedOddRemaining : ∀ eta,
    Equation447OptimalCategoricalPathWitnessBranchRemainingData
      cWindow m ratioC ((1 / 4 : ℝ) * Real.log (m : ℝ) ^ 2)
      (xEastEquation447UnprimedOddBranch m r)
      (unprimedOdd eta).pathAtom (unprimedOdd eta).profile
      (unprimedOdd eta).lazyVector (unprimedOdd eta).nextDirection
  primedOddRemaining : ∀ eta,
    Equation447OptimalCategoricalPathWitnessBranchRemainingData
      cWindow m ratioC ((1 / 4 : ℝ) * Real.log (m : ℝ) ^ 2)
      (xEastEquation447PrimedOddBranch m r)
      (primedOdd eta).pathAtom (primedOdd eta).profile
      (primedOdd eta).lazyVector (primedOdd eta).nextDirection
  primedEvenRemaining : ∀ eta,
    Equation447OptimalCategoricalPathWitnessBranchRemainingData
      cWindow m ratioC ((1 / 4 : ℝ) * Real.log (m : ℝ) ^ 2)
      (xEastEquation447PrimedEvenBranch m r)
      (primedEven eta).pathAtom (primedEven eta).profile
      (primedEven eta).lazyVector (primedEven eta).nextDirection
  unprimedEven_cover : xEastEquation447UnprimedEvenBranch m r ⊆
    ⋃ eta, (unprimedEven eta).pathAtom
  unprimedOdd_cover : xEastEquation447UnprimedOddBranch m r ⊆
    ⋃ eta, (unprimedOdd eta).pathAtom
  primedOdd_cover : xEastEquation447PrimedOddBranch m r ⊆
    ⋃ eta, (primedOdd eta).pathAtom
  primedEven_cover : xEastEquation447PrimedEvenBranch m r ⊆
    ⋃ eta, (primedEven eta).pathAtom
  unprimedEven_theta : ∀ eta,
    (unprimedEvenRemaining eta).thetaPathEvent ⊆
      stoppedThetaEvent (sourceCanonicalProfiles (xIndex east))
        (canonicalCStar (xIndex east)) m (stageNumber r)
  unprimedOdd_theta : ∀ eta,
    (unprimedOddRemaining eta).thetaPathEvent ⊆
      stoppedThetaEvent (sourceCanonicalProfiles (xIndex east))
        (canonicalCStar (xIndex east)) m (stageNumber r)
  primedOdd_theta : ∀ eta,
    (primedOddRemaining eta).thetaPathEvent ⊆
      stoppedThetaEvent (sourceCanonicalProfiles (xIndex east))
        (canonicalCStar (xIndex east)) m (stageNumber r)
  primedEven_theta : ∀ eta,
    (primedEvenRemaining eta).thetaPathEvent ⊆
      stoppedThetaEvent (sourceCanonicalProfiles (xIndex east))
        (canonicalCStar (xIndex east)) m (stageNumber r)
  unprimedEven_disjoint : Pairwise fun eta zeta ↦
    Disjoint (unprimedEven eta).pathAtom (unprimedEven zeta).pathAtom
  unprimedOdd_disjoint : Pairwise fun eta zeta ↦
    Disjoint (unprimedOdd eta).pathAtom (unprimedOdd zeta).pathAtom
  primedOdd_disjoint : Pairwise fun eta zeta ↦
    Disjoint (primedOdd eta).pathAtom (primedOdd zeta).pathAtom
  primedEven_disjoint : Pairwise fun eta zeta ↦
    Disjoint (primedEven eta).pathAtom (primedEven zeta).pathAtom

/-- Source-faithful variant of the optimal categorical package in which the
inner changed-path disjointness (4.54) is represented by the stopped-length
and monotone level-count certificate.  The outer stopped-source atom families
remain disjoint for the usual fixed-prefix reason. -/
structure XEastCanonicalFourBranchLengthSeparatedOptimalCategoricalPathWitnessSourceData
    (cWindow m : ℕ) (ratioC : ℝ) (r : StageIndex) where
  unprimedEven : ℕ → UnprimedEvenLeftWinnerSource m
  unprimedOdd : ℕ → UnprimedOddTerminalTieLeftSource m
  primedOdd : ℕ → PrimedOddStrictRightWinnerSource m
  primedEven : ℕ → PrimedEvenTerminalStrictRightSource m
  unprimedEvenRemaining : ∀ eta,
    Equation447LengthSeparatedOptimalCategoricalPathWitnessBranchRemainingData
      cWindow m ratioC ((1 / 4 : ℝ) * Real.log (m : ℝ) ^ 2)
      (xEastEquation447UnprimedEvenBranch m r)
      (unprimedEven eta).pathAtom (unprimedEven eta).profile
      (unprimedEven eta).lazyVector (unprimedEven eta).nextDirection
  unprimedOddRemaining : ∀ eta,
    Equation447LengthSeparatedOptimalCategoricalPathWitnessBranchRemainingData
      cWindow m ratioC ((1 / 4 : ℝ) * Real.log (m : ℝ) ^ 2)
      (xEastEquation447UnprimedOddBranch m r)
      (unprimedOdd eta).pathAtom (unprimedOdd eta).profile
      (unprimedOdd eta).lazyVector (unprimedOdd eta).nextDirection
  primedOddRemaining : ∀ eta,
    Equation447LengthSeparatedOptimalCategoricalPathWitnessBranchRemainingData
      cWindow m ratioC ((1 / 4 : ℝ) * Real.log (m : ℝ) ^ 2)
      (xEastEquation447PrimedOddBranch m r)
      (primedOdd eta).pathAtom (primedOdd eta).profile
      (primedOdd eta).lazyVector (primedOdd eta).nextDirection
  primedEvenRemaining : ∀ eta,
    Equation447LengthSeparatedOptimalCategoricalPathWitnessBranchRemainingData
      cWindow m ratioC ((1 / 4 : ℝ) * Real.log (m : ℝ) ^ 2)
      (xEastEquation447PrimedEvenBranch m r)
      (primedEven eta).pathAtom (primedEven eta).profile
      (primedEven eta).lazyVector (primedEven eta).nextDirection
  unprimedEven_cover : xEastEquation447UnprimedEvenBranch m r ⊆
    ⋃ eta, (unprimedEven eta).pathAtom
  unprimedOdd_cover : xEastEquation447UnprimedOddBranch m r ⊆
    ⋃ eta, (unprimedOdd eta).pathAtom
  primedOdd_cover : xEastEquation447PrimedOddBranch m r ⊆
    ⋃ eta, (primedOdd eta).pathAtom
  primedEven_cover : xEastEquation447PrimedEvenBranch m r ⊆
    ⋃ eta, (primedEven eta).pathAtom
  unprimedEven_theta : ∀ eta,
    (unprimedEvenRemaining eta).thetaPathEvent ⊆
      stoppedThetaEvent (sourceCanonicalProfiles (xIndex east))
        (canonicalCStar (xIndex east)) m (stageNumber r)
  unprimedOdd_theta : ∀ eta,
    (unprimedOddRemaining eta).thetaPathEvent ⊆
      stoppedThetaEvent (sourceCanonicalProfiles (xIndex east))
        (canonicalCStar (xIndex east)) m (stageNumber r)
  primedOdd_theta : ∀ eta,
    (primedOddRemaining eta).thetaPathEvent ⊆
      stoppedThetaEvent (sourceCanonicalProfiles (xIndex east))
        (canonicalCStar (xIndex east)) m (stageNumber r)
  primedEven_theta : ∀ eta,
    (primedEvenRemaining eta).thetaPathEvent ⊆
      stoppedThetaEvent (sourceCanonicalProfiles (xIndex east))
        (canonicalCStar (xIndex east)) m (stageNumber r)
  unprimedEven_disjoint : Pairwise fun eta zeta ↦
    Disjoint (unprimedEven eta).pathAtom (unprimedEven zeta).pathAtom
  unprimedOdd_disjoint : Pairwise fun eta zeta ↦
    Disjoint (unprimedOdd eta).pathAtom (unprimedOdd zeta).pathAtom
  primedOdd_disjoint : Pairwise fun eta zeta ↦
    Disjoint (primedOdd eta).pathAtom (primedOdd zeta).pathAtom
  primedEven_disjoint : Pairwise fun eta zeta ↦
    Disjoint (primedEven eta).pathAtom (primedEven zeta).pathAtom

namespace XEastCanonicalFourBranchLengthSeparatedOptimalCategoricalPathWitnessSourceData

variable {cWindow m : ℕ} {ratioC : ℝ} {r : StageIndex}

/-- Derive the legacy optimal categorical package branchwise; (4.54) is
proved by `Equation447PathLengthSeparationData.pairwise_disjoint`. -/
noncomputable def toOptimalCategoricalPathWitnessSourceData
    (D : XEastCanonicalFourBranchLengthSeparatedOptimalCategoricalPathWitnessSourceData
      cWindow m ratioC r) :
    XEastCanonicalFourBranchOptimalCategoricalPathWitnessSourceData
      cWindow m ratioC r where
  unprimedEven := D.unprimedEven
  unprimedOdd := D.unprimedOdd
  primedOdd := D.primedOdd
  primedEven := D.primedEven
  unprimedEvenRemaining := fun eta ↦
    (D.unprimedEvenRemaining eta)
      |>.toOptimalCategoricalPathWitnessBranchRemainingData
  unprimedOddRemaining := fun eta ↦
    (D.unprimedOddRemaining eta)
      |>.toOptimalCategoricalPathWitnessBranchRemainingData
  primedOddRemaining := fun eta ↦
    (D.primedOddRemaining eta)
      |>.toOptimalCategoricalPathWitnessBranchRemainingData
  primedEvenRemaining := fun eta ↦
    (D.primedEvenRemaining eta)
      |>.toOptimalCategoricalPathWitnessBranchRemainingData
  unprimedEven_cover := D.unprimedEven_cover
  unprimedOdd_cover := D.unprimedOdd_cover
  primedOdd_cover := D.primedOdd_cover
  primedEven_cover := D.primedEven_cover
  unprimedEven_theta := D.unprimedEven_theta
  unprimedOdd_theta := D.unprimedOdd_theta
  primedOdd_theta := D.primedOdd_theta
  primedEven_theta := D.primedEven_theta
  unprimedEven_disjoint := D.unprimedEven_disjoint
  unprimedOdd_disjoint := D.unprimedOdd_disjoint
  primedOdd_disjoint := D.primedOdd_disjoint
  primedEven_disjoint := D.primedEven_disjoint

end XEastCanonicalFourBranchLengthSeparatedOptimalCategoricalPathWitnessSourceData

/-- Stronger source-facing X-east package: the two conditional products in
each changed-path branch are derived from literal coordinate rectangles, while
the (4.54) disjointness is still derived from stopped-length separation. -/
structure XEastCanonicalFourBranchLengthSeparatedRectangularOptimalCategoricalPathWitnessSourceData
    (cWindow m : ℕ) (ratioC : ℝ) (r : StageIndex) where
  unprimedEven : ℕ → UnprimedEvenLeftWinnerSource m
  unprimedOdd : ℕ → UnprimedOddTerminalTieLeftSource m
  primedOdd : ℕ → PrimedOddStrictRightWinnerSource m
  primedEven : ℕ → PrimedEvenTerminalStrictRightSource m
  unprimedEvenRemaining : ∀ eta,
    Equation447LengthSeparatedRectangularOptimalCategoricalPathWitnessBranchRemainingData
      cWindow m ratioC ((1 / 4 : ℝ) * Real.log (m : ℝ) ^ 2)
      (xEastEquation447UnprimedEvenBranch m r)
      (stoppedThetaEvent (sourceCanonicalProfiles (xIndex east))
        (canonicalCStar (xIndex east)) m (stageNumber r))
      (unprimedEven eta).pathAtom (unprimedEven eta).profile
      (unprimedEven eta).lazyVector (unprimedEven eta).nextDirection
  unprimedOddRemaining : ∀ eta,
    Equation447LengthSeparatedRectangularOptimalCategoricalPathWitnessBranchRemainingData
      cWindow m ratioC ((1 / 4 : ℝ) * Real.log (m : ℝ) ^ 2)
      (xEastEquation447UnprimedOddBranch m r)
      (stoppedThetaEvent (sourceCanonicalProfiles (xIndex east))
        (canonicalCStar (xIndex east)) m (stageNumber r))
      (unprimedOdd eta).pathAtom (unprimedOdd eta).profile
      (unprimedOdd eta).lazyVector (unprimedOdd eta).nextDirection
  primedOddRemaining : ∀ eta,
    Equation447LengthSeparatedRectangularOptimalCategoricalPathWitnessBranchRemainingData
      cWindow m ratioC ((1 / 4 : ℝ) * Real.log (m : ℝ) ^ 2)
      (xEastEquation447PrimedOddBranch m r)
      (stoppedThetaEvent (sourceCanonicalProfiles (xIndex east))
        (canonicalCStar (xIndex east)) m (stageNumber r))
      (primedOdd eta).pathAtom (primedOdd eta).profile
      (primedOdd eta).lazyVector (primedOdd eta).nextDirection
  primedEvenRemaining : ∀ eta,
    Equation447LengthSeparatedRectangularOptimalCategoricalPathWitnessBranchRemainingData
      cWindow m ratioC ((1 / 4 : ℝ) * Real.log (m : ℝ) ^ 2)
      (xEastEquation447PrimedEvenBranch m r)
      (stoppedThetaEvent (sourceCanonicalProfiles (xIndex east))
        (canonicalCStar (xIndex east)) m (stageNumber r))
      (primedEven eta).pathAtom (primedEven eta).profile
      (primedEven eta).lazyVector (primedEven eta).nextDirection
  unprimedEven_cover : xEastEquation447UnprimedEvenBranch m r ⊆
    ⋃ eta, (unprimedEven eta).pathAtom
  unprimedOdd_cover : xEastEquation447UnprimedOddBranch m r ⊆
    ⋃ eta, (unprimedOdd eta).pathAtom
  primedOdd_cover : xEastEquation447PrimedOddBranch m r ⊆
    ⋃ eta, (primedOdd eta).pathAtom
  primedEven_cover : xEastEquation447PrimedEvenBranch m r ⊆
    ⋃ eta, (primedEven eta).pathAtom
  unprimedEven_disjoint : Pairwise fun eta zeta ↦
    Disjoint (unprimedEven eta).pathAtom (unprimedEven zeta).pathAtom
  unprimedOdd_disjoint : Pairwise fun eta zeta ↦
    Disjoint (unprimedOdd eta).pathAtom (unprimedOdd zeta).pathAtom
  primedOdd_disjoint : Pairwise fun eta zeta ↦
    Disjoint (primedOdd eta).pathAtom (primedOdd zeta).pathAtom
  primedEven_disjoint : Pairwise fun eta zeta ↦
    Disjoint (primedEven eta).pathAtom (primedEven zeta).pathAtom

namespace XEastCanonicalFourBranchLengthSeparatedRectangularOptimalCategoricalPathWitnessSourceData

variable {cWindow m : ℕ} {ratioC : ℝ} {r : StageIndex}

/-- Derive the already-consumed length-separated package branchwise. -/
noncomputable def toLengthSeparatedOptimalCategoricalPathWitnessSourceData
    (D :
      XEastCanonicalFourBranchLengthSeparatedRectangularOptimalCategoricalPathWitnessSourceData
        cWindow m ratioC r) :
    XEastCanonicalFourBranchLengthSeparatedOptimalCategoricalPathWitnessSourceData
      cWindow m ratioC r where
  unprimedEven := D.unprimedEven
  unprimedOdd := D.unprimedOdd
  primedOdd := D.primedOdd
  primedEven := D.primedEven
  unprimedEvenRemaining := fun eta ↦
    (D.unprimedEvenRemaining eta)
      |>.toLengthSeparatedOptimalCategoricalPathWitnessBranchRemainingData
  unprimedOddRemaining := fun eta ↦
    (D.unprimedOddRemaining eta)
      |>.toLengthSeparatedOptimalCategoricalPathWitnessBranchRemainingData
  primedOddRemaining := fun eta ↦
    (D.primedOddRemaining eta)
      |>.toLengthSeparatedOptimalCategoricalPathWitnessBranchRemainingData
  primedEvenRemaining := fun eta ↦
    (D.primedEvenRemaining eta)
      |>.toLengthSeparatedOptimalCategoricalPathWitnessBranchRemainingData
  unprimedEven_cover := D.unprimedEven_cover
  unprimedOdd_cover := D.unprimedOdd_cover
  primedOdd_cover := D.primedOdd_cover
  primedEven_cover := D.primedEven_cover
  unprimedEven_theta := fun _ ↦ Set.Subset.rfl
  unprimedOdd_theta := fun _ ↦ Set.Subset.rfl
  primedOdd_theta := fun _ ↦ Set.Subset.rfl
  primedEven_theta := fun _ ↦ Set.Subset.rfl
  unprimedEven_disjoint := D.unprimedEven_disjoint
  unprimedOdd_disjoint := D.unprimedOdd_disjoint
  primedOdd_disjoint := D.primedOdd_disjoint
  primedEven_disjoint := D.primedEven_disjoint

end XEastCanonicalFourBranchLengthSeparatedRectangularOptimalCategoricalPathWitnessSourceData

/-- Literal source-band rectangles determine the optimal categorical
witness layers for all four X-east parity/winner branches. -/
noncomputable def XEastCanonicalFourBranchSourceData.toOptimalCategoricalPathWitnessSourceData
    {cWindow m : ℕ} {r : StageIndex}
    (D : XEastCanonicalFourBranchSourceData cWindow m r)
    (growth : SourceWindowGrowth cWindow m) :
    XEastCanonicalFourBranchOptimalCategoricalPathWitnessSourceData
      cWindow m (Real.exp (sourceAdjacentComparisonExponent cWindow)) r where
  unprimedEven := D.unprimedEven
  unprimedOdd := D.unprimedOdd
  primedOdd := D.primedOdd
  primedEven := D.primedEven
  unprimedEvenRemaining := fun eta ↦
    (D.unprimedEvenRemaining eta)
      |>.toOptimalCategoricalPathWitnessBranchRemainingData
        (D.unprimedEven eta).profile_lt growth
  unprimedOddRemaining := fun eta ↦
    (D.unprimedOddRemaining eta)
      |>.toOptimalCategoricalPathWitnessBranchRemainingData
        (D.unprimedOdd eta).profile_lt growth
  primedOddRemaining := fun eta ↦
    (D.primedOddRemaining eta)
      |>.toOptimalCategoricalPathWitnessBranchRemainingData
        (D.primedOdd eta).profile_lt growth
  primedEvenRemaining := fun eta ↦
    (D.primedEvenRemaining eta)
      |>.toOptimalCategoricalPathWitnessBranchRemainingData
        (D.primedEven eta).profile_lt growth
  unprimedEven_cover := D.unprimedEven_cover
  unprimedOdd_cover := D.unprimedOdd_cover
  primedOdd_cover := D.primedOdd_cover
  primedEven_cover := D.primedEven_cover
  unprimedEven_theta := fun _ ↦ le_rfl
  unprimedOdd_theta := fun _ ↦ le_rfl
  primedOdd_theta := fun _ ↦ le_rfl
  primedEven_theta := fun _ ↦ le_rfl
  unprimedEven_disjoint := D.unprimedEven_disjoint
  unprimedOdd_disjoint := D.unprimedOdd_disjoint
  primedOdd_disjoint := D.primedOdd_disjoint
  primedEven_disjoint := D.primedEven_disjoint

namespace XEastCanonicalFourBranchOptimalCategoricalPathWitnessSourceData

variable {cWindow m : ℕ} {ratioC : ℝ} {r : StageIndex}

noncomputable def toPathWitnessSourceData
    (D : XEastCanonicalFourBranchOptimalCategoricalPathWitnessSourceData
      cWindow m ratioC r)
    (hC : 0 < ratioC)
    (hbinomial : ∀ q,
      Nat.ceil ((1 / 4 : ℝ) * Real.log (m : ℝ) ^ 2) ≤ q →
      ratioC ^ categoricalOptimalWitnessCount ratioC q ≤
        Real.exp (-categoricalOptimalRate ratioC * (q : ℝ)) *
          Nat.choose q (categoricalOptimalWitnessCount ratioC q)) :
    XEastCanonicalFourBranchPathWitnessSourceData
      cWindow m (categoricalOptimalRate ratioC) r where
  unprimedEven := D.unprimedEven
  unprimedOdd := D.unprimedOdd
  primedOdd := D.primedOdd
  primedEven := D.primedEven
  unprimedEvenRemaining := fun eta ↦
    (D.unprimedEvenRemaining eta).toRemainingData hC hbinomial
  unprimedOddRemaining := fun eta ↦
    (D.unprimedOddRemaining eta).toRemainingData hC hbinomial
  primedOddRemaining := fun eta ↦
    (D.primedOddRemaining eta).toRemainingData hC hbinomial
  primedEvenRemaining := fun eta ↦
    (D.primedEvenRemaining eta).toRemainingData hC hbinomial
  unprimedEven_cover := D.unprimedEven_cover
  unprimedOdd_cover := D.unprimedOdd_cover
  primedOdd_cover := D.primedOdd_cover
  primedEven_cover := D.primedEven_cover
  unprimedEven_theta := D.unprimedEven_theta
  unprimedOdd_theta := D.unprimedOdd_theta
  primedOdd_theta := D.primedOdd_theta
  primedEven_theta := D.primedEven_theta
  unprimedEven_disjoint := D.unprimedEven_disjoint
  unprimedOdd_disjoint := D.unprimedOdd_disjoint
  primedOdd_disjoint := D.primedOdd_disjoint
  primedEven_disjoint := D.primedEven_disjoint

end XEastCanonicalFourBranchOptimalCategoricalPathWitnessSourceData

def Prop47Lemma411412XEastCanonicalFourBranchOptimalCategoricalPathWitnessSourceInputs
    (cWindow : ℕ) (ratioC : ℝ) : Prop :=
  ∀ᶠ m : ℕ in atTop, ∀ r : StageIndex,
    Nonempty (XEastCanonicalFourBranchOptimalCategoricalPathWitnessSourceData
      cWindow m ratioC r)

def Prop47Lemma411412XEastCanonicalFourBranchLengthSeparatedOptimalCategoricalPathWitnessSourceInputs
    (cWindow : ℕ) (ratioC : ℝ) : Prop :=
  ∀ᶠ m : ℕ in atTop, ∀ r : StageIndex,
    Nonempty
      (XEastCanonicalFourBranchLengthSeparatedOptimalCategoricalPathWitnessSourceData
        cWindow m ratioC r)

def Prop47Lemma411412XEastCanonicalFourBranchLengthSeparatedRectangularOptimalCategoricalPathWitnessSourceInputs
    (cWindow : ℕ) (ratioC : ℝ) : Prop :=
  ∀ᶠ m : ℕ in atTop, ∀ r : StageIndex,
    Nonempty
      (XEastCanonicalFourBranchLengthSeparatedRectangularOptimalCategoricalPathWitnessSourceData
        cWindow m ratioC r)

/-- Literal rectangles discharge both branchwise conditional-product
identities before the stopped-length connector is invoked. -/
theorem xEastLengthSeparatedOptimalCategoricalPathWitnessSourceInputs_of_rectangular
    (cWindow : ℕ) (ratioC : ℝ)
    (h :
      Prop47Lemma411412XEastCanonicalFourBranchLengthSeparatedRectangularOptimalCategoricalPathWitnessSourceInputs
        cWindow ratioC) :
    Prop47Lemma411412XEastCanonicalFourBranchLengthSeparatedOptimalCategoricalPathWitnessSourceInputs
      cWindow ratioC := by
  filter_upwards [h] with m hm
  intro r
  rcases hm r with ⟨D⟩
  exact ⟨D.toLengthSeparatedOptimalCategoricalPathWitnessSourceData⟩

/-- The stopped-length version supplies the existing optimal categorical
input without assuming witness disjointness. -/
theorem xEastOptimalCategoricalPathWitnessSourceInputs_of_lengthSeparated
    (cWindow : ℕ) (ratioC : ℝ)
    (h :
      Prop47Lemma411412XEastCanonicalFourBranchLengthSeparatedOptimalCategoricalPathWitnessSourceInputs
        cWindow ratioC) :
    Prop47Lemma411412XEastCanonicalFourBranchOptimalCategoricalPathWitnessSourceInputs
      cWindow ratioC := by
  filter_upwards [h] with m hm
  intro r
  rcases hm r with ⟨D⟩
  exact ⟨D.toOptimalCategoricalPathWitnessSourceData⟩

/-- The existing literal source-band input already contains the optimal
categorical witness data; neither a second conditional-product package nor a
witness-disjointness premise is needed. -/
theorem xEastOptimalCategoricalPathWitnessSourceInputs_of_sourceBand
    (cWindow : ℕ)
    (h : Prop47Lemma411412XEastCanonicalFourBranchSourceInputs cWindow) :
    Prop47Lemma411412XEastCanonicalFourBranchOptimalCategoricalPathWitnessSourceInputs
      cWindow (Real.exp (sourceAdjacentComparisonExponent cWindow)) := by
  filter_upwards [h, eventually_sourceWindowGrowth cWindow] with m hm growth
  intro r
  rcases hm r with ⟨D⟩
  exact ⟨D.toOptimalCategoricalPathWitnessSourceData growth⟩

/-- The maximal weighted binomial layer supplies the path-switch rate
uniformly above the quarter-log-square branch threshold. -/
theorem xEastPathWitnessSourceInputs_of_optimalCategorical
    (cWindow : ℕ) (ratioC : ℝ) (hC : 0 < ratioC)
    (h :
      Prop47Lemma411412XEastCanonicalFourBranchOptimalCategoricalPathWitnessSourceInputs
        cWindow ratioC) :
    Prop47Lemma411412XEastCanonicalFourBranchPathWitnessSourceInputs
      cWindow (categoricalOptimalRate ratioC) := by
  have hbin := eventually_optimal_binomial_layer_above_quarter_log_sq ratioC hC
  filter_upwards [h, hbin] with m hm hbm
  intro r
  rcases hm r with ⟨D⟩
  exact ⟨D.toPathWitnessSourceData hC hbm⟩

/-! ### Pointwise-injective source form of the path switch -/

/-- The four X-east branches with the measure-level switch replaced by the
actual injective path modification and its singleton likelihood ratio. -/
structure XEastCanonicalFourBranchInjectivePathWitnessSourceData
    (cWindow m : ℕ) (c : ℝ) (r : StageIndex) where
  unprimedEven : ℕ → UnprimedEvenLeftWinnerSource m
  unprimedOdd : ℕ → UnprimedOddTerminalTieLeftSource m
  primedOdd : ℕ → PrimedOddStrictRightWinnerSource m
  primedEven : ℕ → PrimedEvenTerminalStrictRightSource m
  unprimedEvenRemaining : ∀ eta,
    Equation447InjectivePathWitnessBranchRemainingData cWindow m c
      ((1 / 4 : ℝ) * Real.log (m : ℝ) ^ 2)
      (xEastEquation447UnprimedEvenBranch m r)
      (unprimedEven eta).pathAtom (unprimedEven eta).profile
      (unprimedEven eta).lazyVector (unprimedEven eta).nextDirection
  unprimedOddRemaining : ∀ eta,
    Equation447InjectivePathWitnessBranchRemainingData cWindow m c
      ((1 / 4 : ℝ) * Real.log (m : ℝ) ^ 2)
      (xEastEquation447UnprimedOddBranch m r)
      (unprimedOdd eta).pathAtom (unprimedOdd eta).profile
      (unprimedOdd eta).lazyVector (unprimedOdd eta).nextDirection
  primedOddRemaining : ∀ eta,
    Equation447InjectivePathWitnessBranchRemainingData cWindow m c
      ((1 / 4 : ℝ) * Real.log (m : ℝ) ^ 2)
      (xEastEquation447PrimedOddBranch m r)
      (primedOdd eta).pathAtom (primedOdd eta).profile
      (primedOdd eta).lazyVector (primedOdd eta).nextDirection
  primedEvenRemaining : ∀ eta,
    Equation447InjectivePathWitnessBranchRemainingData cWindow m c
      ((1 / 4 : ℝ) * Real.log (m : ℝ) ^ 2)
      (xEastEquation447PrimedEvenBranch m r)
      (primedEven eta).pathAtom (primedEven eta).profile
      (primedEven eta).lazyVector (primedEven eta).nextDirection
  unprimedEven_cover : xEastEquation447UnprimedEvenBranch m r ⊆
    ⋃ eta, (unprimedEven eta).pathAtom
  unprimedOdd_cover : xEastEquation447UnprimedOddBranch m r ⊆
    ⋃ eta, (unprimedOdd eta).pathAtom
  primedOdd_cover : xEastEquation447PrimedOddBranch m r ⊆
    ⋃ eta, (primedOdd eta).pathAtom
  primedEven_cover : xEastEquation447PrimedEvenBranch m r ⊆
    ⋃ eta, (primedEven eta).pathAtom
  unprimedEven_theta : ∀ eta,
    (unprimedEvenRemaining eta).thetaPathEvent ⊆
      stoppedThetaEvent (sourceCanonicalProfiles (xIndex east))
        (canonicalCStar (xIndex east)) m (stageNumber r)
  unprimedOdd_theta : ∀ eta,
    (unprimedOddRemaining eta).thetaPathEvent ⊆
      stoppedThetaEvent (sourceCanonicalProfiles (xIndex east))
        (canonicalCStar (xIndex east)) m (stageNumber r)
  primedOdd_theta : ∀ eta,
    (primedOddRemaining eta).thetaPathEvent ⊆
      stoppedThetaEvent (sourceCanonicalProfiles (xIndex east))
        (canonicalCStar (xIndex east)) m (stageNumber r)
  primedEven_theta : ∀ eta,
    (primedEvenRemaining eta).thetaPathEvent ⊆
      stoppedThetaEvent (sourceCanonicalProfiles (xIndex east))
        (canonicalCStar (xIndex east)) m (stageNumber r)
  unprimedEven_disjoint : Pairwise fun eta zeta ↦
    Disjoint (unprimedEven eta).pathAtom (unprimedEven zeta).pathAtom
  unprimedOdd_disjoint : Pairwise fun eta zeta ↦
    Disjoint (unprimedOdd eta).pathAtom (unprimedOdd zeta).pathAtom
  primedOdd_disjoint : Pairwise fun eta zeta ↦
    Disjoint (primedOdd eta).pathAtom (primedOdd zeta).pathAtom
  primedEven_disjoint : Pairwise fun eta zeta ↦
    Disjoint (primedEven eta).pathAtom (primedEven zeta).pathAtom

namespace XEastCanonicalFourBranchInjectivePathWitnessSourceData

variable {cWindow m : ℕ} {c : ℝ} {r : StageIndex}

/-- Sum each pointwise switch and recover the path-witness package consumed
by the existing all-direction connector. -/
noncomputable def toPathWitnessSourceData
    (D : XEastCanonicalFourBranchInjectivePathWitnessSourceData
      cWindow m c r) :
    XEastCanonicalFourBranchPathWitnessSourceData cWindow m c r where
  unprimedEven := D.unprimedEven
  unprimedOdd := D.unprimedOdd
  primedOdd := D.primedOdd
  primedEven := D.primedEven
  unprimedEvenRemaining := fun eta ↦
    (D.unprimedEvenRemaining eta).toRemainingData
  unprimedOddRemaining := fun eta ↦
    (D.unprimedOddRemaining eta).toRemainingData
  primedOddRemaining := fun eta ↦
    (D.primedOddRemaining eta).toRemainingData
  primedEvenRemaining := fun eta ↦
    (D.primedEvenRemaining eta).toRemainingData
  unprimedEven_cover := D.unprimedEven_cover
  unprimedOdd_cover := D.unprimedOdd_cover
  primedOdd_cover := D.primedOdd_cover
  primedEven_cover := D.primedEven_cover
  unprimedEven_theta := D.unprimedEven_theta
  unprimedOdd_theta := D.unprimedOdd_theta
  primedOdd_theta := D.primedOdd_theta
  primedEven_theta := D.primedEven_theta
  unprimedEven_disjoint := D.unprimedEven_disjoint
  unprimedOdd_disjoint := D.unprimedOdd_disjoint
  primedOdd_disjoint := D.primedOdd_disjoint
  primedEven_disjoint := D.primedEven_disjoint

end XEastCanonicalFourBranchInjectivePathWitnessSourceData

def Prop47Lemma411412XEastCanonicalFourBranchInjectivePathWitnessSourceInputs
    (cWindow : ℕ) (c : ℝ) : Prop :=
  ∀ᶠ m : ℕ in atTop, ∀ r : StageIndex,
    Nonempty (XEastCanonicalFourBranchInjectivePathWitnessSourceData
      cWindow m c r)

theorem xEastPathWitnessSourceInputs_of_injective
    (cWindow : ℕ) (c : ℝ)
    (h :
      Prop47Lemma411412XEastCanonicalFourBranchInjectivePathWitnessSourceInputs
        cWindow c) :
    Prop47Lemma411412XEastCanonicalFourBranchPathWitnessSourceInputs
      cWindow c := by
  filter_upwards [h] with m hm
  intro r
  rcases hm r with ⟨D⟩
  exact ⟨D.toPathWitnessSourceData⟩

end Erdos1166.HLOZProp47Lemma411412XEastBridge
