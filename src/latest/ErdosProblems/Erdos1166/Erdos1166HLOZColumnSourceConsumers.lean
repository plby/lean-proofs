/- leanprover/lean4:v4.33.0 -/

import ErdosProblems.Erdos1166.Erdos1166HLOZColumnTerminalRestart
import ErdosProblems.Erdos1166.Erdos1166HLOZColumnFullComplement
import ErdosProblems.Erdos1166.Erdos1166HLOZStoppedHistoryFactorization
import ErdosProblems.Erdos1166.Erdos1166HLOZLemma410Prop48Connector
import ErdosProblems.Erdos1166.Erdos1166HLOZProp47LowStageConnector
import ErdosProblems.Erdos1166.Erdos1166HLOZProp47Lemma411412SourceAtoms
import ErdosProblems.Erdos1166.Erdos1166HLOZProp47Lemma411412XEastBridge

/-!
# Source consumers for the two terminal phases of the `Y` column branch

This file exposes the two separately conditioned terminal phases of the
`Y` branch to the three consumers used in the HLOZ reduction.  These are
*not* the `Y` and `Y'` branches: `Y'` is obtained only after the complete
two-phase `Y` event has been transported by the origin-fixing reflection.
The constructions below remain atom-local: there is no assertion that these
atoms cover a planar failure event and no assertion about the number of
source categories.  For equation (4.47), the remaining one-coordinate
comparison is source-facing only as two equal-cardinality finite cells lying
in adjacent source windows.  The pointwise singleton inequality follows from
Lemma 4.12; summation and both conditioning steps are internal.  Its
deterministic `SourceWindowGrowth` premise is discharged by the eventual
column connectors and is not stored in the forward or backward source
records.  The stopped profile bound is also derived by the literal terminal
winner sources and passed to the finite-cell converter.
-/

namespace Erdos1166.HLOZColumnSourceConsumers

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

open HLOZColumnPairRuns HLOZColumnBlockGrouping HLOZColumnTerminalRestart
  HLOZColumnFullComplement
  HLOZFiniteUnion HLOZBandRatios
  HLOZPairing HLOZPairingProfiles HLOZProp47Prop45YColumns
  HLOZProp47Canonical
  HLOZProp48SourceBands HLOZLemma411 HLOZLemma412Windows HLOZEquation447
  HLOZProp48Truncated HLOZProp49Coordinate
  HLOZLemma410Prop48Connector HLOZProp47LowStageConnector
  HLOZProp47Lemma411412Connector HLOZProp47Lemma411412SourceAtoms
  HLOZProp47Lemma411412XEastBridge
  HLOZProp47SourceObjects HLOZProp47SourceAssembly HLOZProp47Canonical
  HLOZProp47Parameters HLOZLemma411Recursion
  HLOZProp45SourceInterval HLOZProp45SourceMirrors HLOZProp45SourceEndpoints
  HLOZStoppedHistoryFactorization HLOZSourceInstantiation

abbrev Path := ℕ → Site

/-! ## The canonical two-way winner cover -/

/-- Distinguished base of the horizontal `Y` domino containing `x`. -/
noncomputable def yDominoBase (x : Site) : Site :=
  distinguishedEndpoint yIndex x

theorem yDominoBase_eq (x : Site) :
    yDominoBase x = if Even x.1 then x else shift x (vec west) := by
  rfl

/-- Every fibre of the `Y` domino-base map consists of the left endpoint
and, possibly, its eastern partner. -/
theorem yDominoBase_fiber (x b : Site) (h : yDominoBase x = b) :
    x = b ∨ x = shift b (vec east) := by
  rw [yDominoBase_eq] at h
  by_cases hx : Even x.1
  · left
    simpa [hx] using h
  · right
    rw [if_neg hx] at h
    rw [← h]
    simp [shift, vec, east, west]

theorem yDominoBase_fiber_card_le_two (S : Finset Site)
    (b : Site) :
    (S.filter fun x ↦ yDominoBase x = b).card ≤ 2 := by
  classical
  apply (Finset.card_le_card ?_).trans
    (show ({b, shift b (vec east)} : Finset Site).card ≤ 2 by
      calc
        ({b, shift b (vec east)} : Finset Site).card ≤
            ({shift b (vec east)} : Finset Site).card + 1 :=
          Finset.card_insert_le _ _
        _ = 2 := by simp)
  intro x hx
  simp only [Finset.mem_filter] at hx
  rcases yDominoBase_fiber x b hx.2 with rfl | rfl <;> simp

noncomputable def yNearFavoriteDominoBases
    (s : Path) (m k : ℕ) (alpha : ℝ) : Finset Site :=
  (nearFavoriteSites yIndex s m k alpha).image yDominoBase

/-- Tie-left winners among the `Y` dominoes met by the near-favourite set. -/
noncomputable def yLeftNearFavoriteWinnerBases
    (s : Path) (m k : ℕ) (alpha : ℝ) : Finset Site :=
  (yNearFavoriteDominoBases s m k alpha).filter fun b ↦
    localTime s (directCreationTime m k s) (shift b (vec east)) ≤
      localTime s (directCreationTime m k s) b

/-- Strict-right winners among the same `Y` dominoes. -/
noncomputable def yRightNearFavoriteWinnerBases
    (s : Path) (m k : ℕ) (alpha : ℝ) : Finset Site :=
  (yNearFavoriteDominoBases s m k alpha).filter fun b ↦
    localTime s (directCreationTime m k s) b <
      localTime s (directCreationTime m k s) (shift b (vec east))

theorem yNearFavoriteDominoBases_card_eq_winners
    (s : Path) (m k : ℕ) (alpha : ℝ) :
    (yNearFavoriteDominoBases s m k alpha).card =
      (yLeftNearFavoriteWinnerBases s m k alpha).card +
        (yRightNearFavoriteWinnerBases s m k alpha).card := by
  classical
  rw [yLeftNearFavoriteWinnerBases, yRightNearFavoriteWinnerBases]
  simpa only [not_le] using
    (Finset.card_filter_add_card_filter_not
      (s := yNearFavoriteDominoBases s m k alpha)
      (fun b ↦
        localTime s (directCreationTime m k s) (shift b (vec east)) ≤
          localTime s (directCreationTime m k s) b)).symm

/-- The source inequality (4.40) for the even-left column pairing. -/
theorem y_nearFavorite_card_le_two_mul_winners
    (s : Path) (m k : ℕ) (alpha : ℝ) :
    (nearFavoriteSites yIndex s m k alpha).card ≤
      2 * ((yLeftNearFavoriteWinnerBases s m k alpha).card +
        (yRightNearFavoriteWinnerBases s m k alpha).card) := by
  classical
  calc
    (nearFavoriteSites yIndex s m k alpha).card ≤
        2 * (yNearFavoriteDominoBases s m k alpha).card := by
      exact Finset.card_le_mul_card_image
        (nearFavoriteSites yIndex s m k alpha) 2
        (fun b _ ↦ yDominoBase_fiber_card_le_two
          (nearFavoriteSites yIndex s m k alpha) b)
    _ = 2 * ((yLeftNearFavoriteWinnerBases s m k alpha).card +
        (yRightNearFavoriteWinnerBases s m k alpha).card) := by
      rw [yNearFavoriteDominoBases_card_eq_winners]

def yLeftNearFavoriteOverflow
    (m k : ℕ) (alpha rho : ℝ) : Set Path :=
  {s | rho < (yLeftNearFavoriteWinnerBases s m k alpha).card}

def yRightNearFavoriteOverflow
    (m k : ℕ) (alpha rho : ℝ) : Set Path :=
  {s | rho < (yRightNearFavoriteWinnerBases s m k alpha).card}

/-- A full log-square column overflow forces a quarter-log-square winner
overflow on one of the two temporal column phases. -/
theorem y_nearFavorite_overflow_subset_winner_overflows
    (m k : ℕ) (alpha : ℝ) :
    {s | Real.log m ^ 2 <
        ((nearFavoriteSites yIndex s m k alpha).card : ℝ)} ⊆
      yLeftNearFavoriteOverflow m k alpha
          ((1 / 4 : ℝ) * Real.log m ^ 2) ∪
        yRightNearFavoriteOverflow m k alpha
          ((1 / 4 : ℝ) * Real.log m ^ 2) := by
  intro s hs
  change Real.log m ^ 2 <
    ((nearFavoriteSites yIndex s m k alpha).card : ℝ) at hs
  have hcard := y_nearFavorite_card_le_two_mul_winners s m k alpha
  have hcardReal :
      ((nearFavoriteSites yIndex s m k alpha).card : ℝ) ≤
        2 * (((yLeftNearFavoriteWinnerBases s m k alpha).card : ℝ) +
          ((yRightNearFavoriteWinnerBases s m k alpha).card : ℝ)) := by
    exact_mod_cast hcard
  by_cases hleft : (1 / 4 : ℝ) * Real.log m ^ 2 <
      ((yLeftNearFavoriteWinnerBases s m k alpha).card : ℝ)
  · exact Or.inl hleft
  by_cases hright : (1 / 4 : ℝ) * Real.log m ^ 2 <
      ((yRightNearFavoriteWinnerBases s m k alpha).card : ℝ)
  · exact Or.inr hright
  have hleftLe := not_lt.mp hleft
  have hrightLe := not_lt.mp hright
  exfalso
  nlinarith

def yEquation447ForwardBranch (m : ℕ) (r : StageIndex) : Set Path :=
  prefixPairingEvent m yIndex (stageNumber r) ∩
    yLeftNearFavoriteOverflow m (stageNumber r) kappaOne
      ((1 / 4 : ℝ) * Real.log m ^ 2)

def yEquation447BackwardBranch (m : ℕ) (r : StageIndex) : Set Path :=
  prefixPairingEvent m yIndex (stageNumber r) ∩
    yRightNearFavoriteOverflow m (stageNumber r) kappaOne
      ((1 / 4 : ℝ) * Real.log m ^ 2)

/-- The global `Y` cardinality failure is covered by its two canonical
tie-left/strict-right branch events. -/
theorem lemma411412CardinalityFailureEvent_y_subset_canonicalBranches
    (m : ℕ) (r : StageIndex) :
    lemma411412CardinalityFailureEvent m yIndex r ⊆
      yEquation447ForwardBranch m r ∪
        yEquation447BackwardBranch m r := by
  rintro s ⟨hprefix, hover⟩
  have hprefix' : s ∈ prefixPairingEvent m yIndex (stageNumber r) :=
    prefixPairingEvent_mono m yIndex (Nat.le_succ _) hprefix
  rcases y_nearFavorite_overflow_subset_winner_overflows
      m (stageNumber r) kappaOne hover with hleft | hright
  · exact Or.inl ⟨hprefix', hleft⟩
  · exact Or.inr ⟨hprefix', hright⟩

/-! ## The two literal branch-local source atoms -/

/-- One fixed forward (`Y`) column terminal atom with the weak-left winner
split.  The mixed event is the literal block condition; its product law and
profile bound are derived, not supplied. -/
structure ForwardColumnWinnerSource (m : ℕ) where
  k : ℕ
  start : ℕ
  specs : List (Bool × IncrementPair)
  clock : HLOZProp47Prop45YColumns.YPhaseTerminalClockInputs m k start specs
  creationSet : Finset Site
  externalLeft : ColumnRunBase clock.baseAt → ℕ
  externalRight : ColumnRunBase clock.baseAt → ℕ
  candidateBases : Finset (ColumnRunBase clock.baseAt)
  mixed_nonempty :
    (columnMixedBlockSumEvent clock.baseAt m creationSet
      externalLeft externalRight).Nonempty
  left_count : ∀ b,
    Fintype.card (ColumnRunIndex clock.baseAt b) = externalLeft b

namespace ForwardColumnWinnerSource

variable {m : ℕ} (S : ForwardColumnWinnerSource m)

noncomputable def activeBases : Finset (ColumnRunBase S.clock.baseAt) :=
  columnForwardLeftWinnerBases S.clock.baseAt S.externalLeft S.externalRight
    S.candidateBases

abbrev Coord :=
  ColumnActiveFreeBase S.clock.baseAt S.creationSet S.activeBases

def pathAtom : Set Path :=
  forwardTerminalMixedPathAtom S.clock m S.creationSet
    S.externalLeft S.externalRight

noncomputable def profile : S.Coord → ℕ :=
  columnActiveFreeShape S.clock.baseAt S.creationSet S.activeBases

noncomputable def lazyVector : Path → S.Coord → ℕ :=
  forwardTerminalActiveFreeVector S.clock S.creationSet S.activeBases

noncomputable def nextDirection : Path → Direction :=
  forwardTerminalNextDirection S.clock

theorem measurableSet_pathAtom : MeasurableSet S.pathAtom :=
  measurableSet_forwardTerminalMixedPathAtom S.clock m S.creationSet
    S.externalLeft S.externalRight

theorem measurable_lazyVector : Measurable S.lazyVector :=
  measurable_forwardTerminalActiveFreeVector S.clock S.creationSet S.activeBases

theorem measurable_nextDirection : Measurable S.nextDirection :=
  measurable_forwardTerminalNextDirection S.clock

theorem map_law :
    (simpleRandomWalkLaw.restrict S.pathAtom).map
        (fun s ↦ (S.lazyVector s, S.nextDirection s)) =
      simpleRandomWalkLaw S.pathAtom •
        ((sourceTruncatedProfileMeasure m S.profile).prod directionLaw) :=
  forwardTerminalLeftWinner_prod_fresh_truncated_path_map_law
    S.clock m S.creationSet S.externalLeft S.externalRight S.candidateBases
      S.mixed_nonempty S.left_count

theorem profile_lt : ∀ x, S.profile x < m := by
  apply columnActiveFreeShape_lt_of_mixed_nonempty S.clock.baseAt m
    S.creationSet S.activeBases S.externalLeft S.externalRight
    S.mixed_nonempty
  exact columnForwardLeftWinner_cap_eq_shape S.clock.baseAt S.creationSet
    S.externalLeft S.externalRight S.candidateBases S.left_count

end ForwardColumnWinnerSource

/-- The independently conditioned backward terminal phase of the same `Y`
branch, with the strict-right winner split.  Despite the historical word
`primed` in the parser API, this is not the reflected `Y'` branch. -/
structure PrimedColumnWinnerSource (m : ℕ) where
  k : ℕ
  start : ℕ
  specs : List (Bool × IncrementPair)
  clock : HLOZProp47Prop45YColumns.YPrimedPhaseTerminalClockInputs
    m k start specs
  creationSet : Finset Site
  externalLeft : ColumnRunBase clock.baseAt → ℕ
  externalRight : ColumnRunBase clock.baseAt → ℕ
  candidateBases : Finset (ColumnRunBase clock.baseAt)
  mixed_nonempty :
    (columnMixedBlockSumEvent clock.baseAt m creationSet
      externalLeft externalRight).Nonempty
  right_count : ∀ b,
    Fintype.card (ColumnRunIndex clock.baseAt b) = externalRight b

namespace PrimedColumnWinnerSource

variable {m : ℕ} (S : PrimedColumnWinnerSource m)

noncomputable def activeBases : Finset (ColumnRunBase S.clock.baseAt) :=
  columnPrimedStrictRightWinnerBases S.clock.baseAt S.externalLeft
    S.externalRight S.candidateBases

abbrev Coord :=
  ColumnActiveFreeBase S.clock.baseAt S.creationSet S.activeBases

def pathAtom : Set Path :=
  primedTerminalMixedPathAtom S.clock m S.creationSet
    S.externalLeft S.externalRight

noncomputable def profile : S.Coord → ℕ :=
  columnActiveFreeShape S.clock.baseAt S.creationSet S.activeBases

noncomputable def lazyVector : Path → S.Coord → ℕ :=
  primedTerminalActiveFreeVector S.clock S.creationSet S.activeBases

noncomputable def nextDirection : Path → Direction :=
  primedTerminalNextDirection S.clock

theorem measurableSet_pathAtom : MeasurableSet S.pathAtom :=
  measurableSet_primedTerminalMixedPathAtom S.clock m S.creationSet
    S.externalLeft S.externalRight

theorem measurable_lazyVector : Measurable S.lazyVector :=
  measurable_primedTerminalActiveFreeVector S.clock S.creationSet S.activeBases

theorem measurable_nextDirection : Measurable S.nextDirection :=
  measurable_primedTerminalNextDirection S.clock

theorem map_law :
    (simpleRandomWalkLaw.restrict S.pathAtom).map
        (fun s ↦ (S.lazyVector s, S.nextDirection s)) =
      simpleRandomWalkLaw S.pathAtom •
        ((sourceTruncatedProfileMeasure m S.profile).prod directionLaw) :=
  primedTerminalStrictRightWinner_prod_fresh_truncated_path_map_law
    S.clock m S.creationSet S.externalLeft S.externalRight S.candidateBases
      S.mixed_nonempty S.right_count

theorem profile_lt : ∀ x, S.profile x < m := by
  apply columnActiveFreeShape_lt_of_mixed_nonempty S.clock.baseAt m
    S.creationSet S.activeBases S.externalLeft S.externalRight
    S.mixed_nonempty
  exact columnPrimedStrictRightWinner_cap_eq_shape S.clock.baseAt S.creationSet
    S.externalLeft S.externalRight S.candidateBases S.right_count

end PrimedColumnWinnerSource

/-! ### Information-preserving column laws

The ordinary source records above expose the active winner profile and the
fresh direction.  The following strengthened forms retain, independently,
every chronological run coordinate on all complementary bases. -/

theorem ForwardColumnWinnerSource.fullComplement_map_law
    {m : ℕ} (S : ForwardColumnWinnerSource m) :
    (simpleRandomWalkLaw.restrict S.pathAtom).map
        (fun s ↦
          ((S.lazyVector s, S.nextDirection s),
            forwardTerminalFullComplementPath S.clock S.creationSet
              S.activeBases s)) =
      simpleRandomWalkLaw S.pathAtom •
        (((sourceTruncatedProfileMeasure m S.profile).prod directionLaw).prod
          (columnMixedComplementRunMeasure S.clock.baseAt m S.creationSet
            S.activeBases S.externalLeft S.externalRight)) := by
  simpa only [ForwardColumnWinnerSource.pathAtom,
    ForwardColumnWinnerSource.lazyVector,
    ForwardColumnWinnerSource.nextDirection,
    ForwardColumnWinnerSource.profile] using
    forwardTerminalActiveFullComplement_prod_fresh_truncated_path_map_law
      S.clock m S.creationSet S.activeBases S.externalLeft S.externalRight
        S.mixed_nonempty
        (columnForwardLeftWinner_cap_eq_shape S.clock.baseAt S.creationSet
          S.externalLeft S.externalRight S.candidateBases S.left_count)

theorem PrimedColumnWinnerSource.fullComplement_map_law
    {m : ℕ} (S : PrimedColumnWinnerSource m) :
    (simpleRandomWalkLaw.restrict S.pathAtom).map
        (fun s ↦
          ((S.lazyVector s, S.nextDirection s),
            primedTerminalFullComplementPath S.clock S.creationSet
              S.activeBases s)) =
      simpleRandomWalkLaw S.pathAtom •
        (((sourceTruncatedProfileMeasure m S.profile).prod directionLaw).prod
          (columnMixedComplementRunMeasure S.clock.baseAt m S.creationSet
            S.activeBases S.externalLeft S.externalRight)) := by
  simpa only [PrimedColumnWinnerSource.pathAtom,
    PrimedColumnWinnerSource.lazyVector,
    PrimedColumnWinnerSource.nextDirection,
    PrimedColumnWinnerSource.profile] using
    primedTerminalActiveFullComplement_prod_fresh_truncated_path_map_law
      S.clock m S.creationSet S.activeBases S.externalLeft S.externalRight
        S.mixed_nonempty
        (columnPrimedStrictRightWinner_cap_eq_shape S.clock.baseAt S.creationSet
          S.externalLeft S.externalRight S.candidateBases S.right_count)

/-! ## Ordered-history refinements at the adaptive terminal endpoint

The terminal parsers above have their own random endpoint: the first
increment after the completely decoded selective pair list.  The canonical
Proposition-4.7 history is known at `T_m^k`.  Consequently, intersecting a
terminal atom with that history is a legitimate past event only after the
deterministic source reconstruction proves `T_m^k` is no later than the
terminal endpoint.  The structures below retain that exact premise.  They
do not identify the history with a function of the active block sums and do
not assert any active/history independence.
-/

/-- Pulling a path event known at `T_m^k` back to increments and restricting
to `{T_m^k \le n}` gives an event in the iid history through time `n`. -/
theorem measurableSet_pathStoppedEvent_inter_threshold_le_iidHistory
    (m k n : ℕ) (E : Set Path)
    (hE : MeasurableSet[
      (isStoppingTime_firstKSitesReachLevel m k).measurableSpace] E) :
    MeasurableSet[iidHistory (X := Direction) n]
      (simpleRandomWalk ⁻¹' E ∩
        {omega | firstKSitesReachLevel m k
          (simpleRandomWalk omega) ≤ n}) := by
  have hStopped :=
    ((isStoppingTime_firstKSitesReachLevel m k).measurableSet E).mp hE
  have hPath : MeasurableSet[HLOZFoundation.canonicalFiltration n]
      (E ∩ {s | firstKSitesReachLevel m k s ≤ n}) := hStopped.2 n
  have hPre :=
    HLOZFoundation.measurable_simpleRandomWalk_iidHistory_canonicalFiltration
      n hPath
  simpa only [Set.preimage_inter, Set.preimage_ofPred_eq] using hPre

namespace ForwardColumnWinnerSource

variable {m : ℕ} (S : ForwardColumnWinnerSource m)

/-- The complete-pair endpoint attached to the decoded forward terminal
specification. -/
noncomputable def terminalEndTime : (ℕ → Direction) → ℕ :=
  selectiveEncodedEndTime S.clock.encoding

/-- A forward column atom refined by the ordered level-`m` creation sites
and every preceding canonical Proposition-4.7 screen. -/
noncomputable def orderedHistoryRefinedIncrementAtom
    (i : Fin 6) (a : AlphaTriple) (r : StageIndex)
    (c : Fin (stageNumber r) → Site) : Set (ℕ → Direction) :=
  simpleRandomWalk ⁻¹' S.pathAtom ∩
    simpleRandomWalk ⁻¹' orderedCanonicalHistoryEvent m i a r c

/-- On a terminal atom whose endpoint follows `T_m^k`, the full ordered
history refinement is genuinely known at the terminal endpoint, fiber by
fiber. -/
theorem orderedHistoryRefinedIncrementAtom_terminalPast
    (i : Fin 6) (a : AlphaTriple) (r : StageIndex)
    (c : Fin (stageNumber r) → Site) (hm : 0 < m)
    (hbefore : S.orderedHistoryRefinedIncrementAtom i a r c ⊆
      {omega | firstKSitesReachLevel m (stageNumber r)
          (simpleRandomWalk omega) ≤
        (S.terminalEndTime omega : WithTop ℕ)})
    (n : ℕ) :
    MeasurableSet[iidHistory (X := Direction) n]
      (S.orderedHistoryRefinedIncrementAtom i a r c ∩
        {omega | S.terminalEndTime omega = n}) := by
  let B := simpleRandomWalk ⁻¹' S.pathAtom
  let E := orderedCanonicalHistoryEvent m i a r c
  let tau := S.terminalEndTime
  let T := fun omega : ℕ → Direction ↦
    firstKSitesReachLevel m (stageNumber r) (simpleRandomWalk omega)
  have hB : MeasurableSet[iidHistory (X := Direction) n]
      (B ∩ {omega | tau omega = n}) := by
    have hpast := selectiveTerminalRestrictedAtom_past S.clock.encoding
      (fun v ↦ columnBlockSums S.clock.baseAt
        (columnBlockVector S.clock.baseAt v))
      (columnMixedBlockSumEvent S.clock.baseAt m S.creationSet
        S.externalLeft S.externalRight) n
    change MeasurableSet[iidHistory (X := Direction) n]
      (forwardTerminalMixedIncrementAtom S.clock m S.creationSet
          S.externalLeft S.externalRight ∩
        {omega | selectiveEncodedEndTime S.clock.encoding omega = n})
      at hpast
    rw [← forwardTerminalMixedIncrementAtom_preimage
      S.clock m S.creationSet S.externalLeft S.externalRight] at hpast
    simpa only [B, tau, pathAtom, terminalEndTime] using hpast
  have hE : MeasurableSet[iidHistory (X := Direction) n]
      (simpleRandomWalk ⁻¹' E ∩ {omega | T omega ≤ n}) := by
    simpa only [E, T] using
      measurableSet_pathStoppedEvent_inter_threshold_le_iidHistory
        m (stageNumber r) n E
          (measurableSet_orderedCanonicalHistoryEvent_at_threshold
            m i a r c hm)
  have heq : (B ∩ simpleRandomWalk ⁻¹' E) ∩
        {omega | tau omega = n} =
      (B ∩ {omega | tau omega = n}) ∩
        (simpleRandomWalk ⁻¹' E ∩ {omega | T omega ≤ n}) := by
    ext omega
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨⟨hBomega, hEomega⟩, htau⟩
      refine ⟨⟨hBomega, htau⟩, hEomega, ?_⟩
      have hle := hbefore ⟨hBomega, hEomega⟩
      change T omega ≤ (tau omega : WithTop ℕ) at hle
      rw [htau] at hle
      exact hle
    · rintro ⟨⟨hBomega, htau⟩, hEomega, _hle⟩
      exact ⟨⟨hBomega, hEomega⟩, htau⟩
  change MeasurableSet[iidHistory (X := Direction) n]
    ((B ∩ simpleRandomWalk ⁻¹' E) ∩ {omega | tau omega = n})
  rw [heq]
  exact hB.inter hE

/-- Ordinary measurability obtained by summing the terminal-end fibers. -/
theorem measurableSet_orderedHistoryRefinedIncrementAtom
    (i : Fin 6) (a : AlphaTriple) (r : StageIndex)
    (c : Fin (stageNumber r) → Site) (hm : 0 < m)
    (hbefore : S.orderedHistoryRefinedIncrementAtom i a r c ⊆
      {omega | firstKSitesReachLevel m (stageNumber r)
          (simpleRandomWalk omega) ≤
        (S.terminalEndTime omega : WithTop ℕ)}) :
    MeasurableSet (S.orderedHistoryRefinedIncrementAtom i a r c) := by
  exact measurableSet_of_iidHistory_fibers_nat S.terminalEndTime
    (S.orderedHistoryRefinedIncrementAtom i a r c)
    (fun n ↦ S.orderedHistoryRefinedIncrementAtom_terminalPast
      i a r c hm hbefore n)

/-- Path-space form of the forward ordered-history atom. -/
noncomputable def orderedHistoryRefinedPathAtom
    (i : Fin 6) (a : AlphaTriple) (r : StageIndex)
    (c : Fin (stageNumber r) → Site) : Set Path :=
  simpleRandomWalk '' S.orderedHistoryRefinedIncrementAtom i a r c

theorem measurableSet_orderedHistoryRefinedPathAtom
    (i : Fin 6) (a : AlphaTriple) (r : StageIndex)
    (c : Fin (stageNumber r) → Site) (hm : 0 < m)
    (hbefore : S.orderedHistoryRefinedIncrementAtom i a r c ⊆
      {omega | firstKSitesReachLevel m (stageNumber r)
          (simpleRandomWalk omega) ≤
        (S.terminalEndTime omega : WithTop ℕ)}) :
    MeasurableSet (S.orderedHistoryRefinedPathAtom i a r c) := by
  exact measurableEmbedding_simpleRandomWalk.measurableSet_image.2
    (S.measurableSet_orderedHistoryRefinedIncrementAtom
      i a r c hm hbefore)

theorem orderedHistoryRefinedPathAtom_subset_history
    (i : Fin 6) (a : AlphaTriple) (r : StageIndex)
    (c : Fin (stageNumber r) → Site) :
    S.orderedHistoryRefinedPathAtom i a r c ⊆
      prop47History canonicalProfiles canonicalCStar m i a r.1 := by
  rintro s ⟨omega, homega, rfl⟩
  exact homega.2.2

theorem orderedHistoryRefinedPathAtom_subset_sourceAtom
    (i : Fin 6) (a : AlphaTriple) (r : StageIndex)
    (c : Fin (stageNumber r) → Site) :
    S.orderedHistoryRefinedPathAtom i a r c ⊆ S.pathAtom := by
  rintro s ⟨omega, homega, rfl⟩
  exact homega.1

end ForwardColumnWinnerSource

namespace PrimedColumnWinnerSource

variable {m : ℕ} (S : PrimedColumnWinnerSource m)

/-- The complete-pair endpoint for the independently conditioned backward
terminal phase of `Y`.  It is not a reflected `Y'` endpoint. -/
noncomputable def terminalEndTime : (ℕ → Direction) → ℕ :=
  primedEncodedEndTime S.clock.encoding

noncomputable def orderedHistoryRefinedIncrementAtom
    (i : Fin 6) (a : AlphaTriple) (r : StageIndex)
    (c : Fin (stageNumber r) → Site) : Set (ℕ → Direction) :=
  simpleRandomWalk ⁻¹' S.pathAtom ∩
    simpleRandomWalk ⁻¹' orderedCanonicalHistoryEvent m i a r c

theorem orderedHistoryRefinedIncrementAtom_terminalPast
    (i : Fin 6) (a : AlphaTriple) (r : StageIndex)
    (c : Fin (stageNumber r) → Site) (hm : 0 < m)
    (hbefore : S.orderedHistoryRefinedIncrementAtom i a r c ⊆
      {omega | firstKSitesReachLevel m (stageNumber r)
          (simpleRandomWalk omega) ≤
        (S.terminalEndTime omega : WithTop ℕ)})
    (n : ℕ) :
    MeasurableSet[iidHistory (X := Direction) n]
      (S.orderedHistoryRefinedIncrementAtom i a r c ∩
        {omega | S.terminalEndTime omega = n}) := by
  let B := simpleRandomWalk ⁻¹' S.pathAtom
  let E := orderedCanonicalHistoryEvent m i a r c
  let tau := S.terminalEndTime
  let T := fun omega : ℕ → Direction ↦
    firstKSitesReachLevel m (stageNumber r) (simpleRandomWalk omega)
  have hB : MeasurableSet[iidHistory (X := Direction) n]
      (B ∩ {omega | tau omega = n}) := by
    have hpast := primedTerminalRestrictedAtom_past S.clock.encoding
      (fun v ↦ columnBlockSums S.clock.baseAt
        (columnBlockVector S.clock.baseAt v))
      (columnMixedBlockSumEvent S.clock.baseAt m S.creationSet
        S.externalLeft S.externalRight) n
    change MeasurableSet[iidHistory (X := Direction) n]
      (primedTerminalMixedIncrementAtom S.clock m S.creationSet
          S.externalLeft S.externalRight ∩
        {omega | primedEncodedEndTime S.clock.encoding omega = n})
      at hpast
    rw [← primedTerminalMixedIncrementAtom_preimage
      S.clock m S.creationSet S.externalLeft S.externalRight] at hpast
    simpa only [B, tau, pathAtom, terminalEndTime] using hpast
  have hE : MeasurableSet[iidHistory (X := Direction) n]
      (simpleRandomWalk ⁻¹' E ∩ {omega | T omega ≤ n}) := by
    simpa only [E, T] using
      measurableSet_pathStoppedEvent_inter_threshold_le_iidHistory
        m (stageNumber r) n E
          (measurableSet_orderedCanonicalHistoryEvent_at_threshold
            m i a r c hm)
  have heq : (B ∩ simpleRandomWalk ⁻¹' E) ∩
        {omega | tau omega = n} =
      (B ∩ {omega | tau omega = n}) ∩
        (simpleRandomWalk ⁻¹' E ∩ {omega | T omega ≤ n}) := by
    ext omega
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨⟨hBomega, hEomega⟩, htau⟩
      refine ⟨⟨hBomega, htau⟩, hEomega, ?_⟩
      have hle := hbefore ⟨hBomega, hEomega⟩
      change T omega ≤ (tau omega : WithTop ℕ) at hle
      rw [htau] at hle
      exact hle
    · rintro ⟨⟨hBomega, htau⟩, hEomega, _hle⟩
      exact ⟨⟨hBomega, hEomega⟩, htau⟩
  change MeasurableSet[iidHistory (X := Direction) n]
    ((B ∩ simpleRandomWalk ⁻¹' E) ∩ {omega | tau omega = n})
  rw [heq]
  exact hB.inter hE

theorem measurableSet_orderedHistoryRefinedIncrementAtom
    (i : Fin 6) (a : AlphaTriple) (r : StageIndex)
    (c : Fin (stageNumber r) → Site) (hm : 0 < m)
    (hbefore : S.orderedHistoryRefinedIncrementAtom i a r c ⊆
      {omega | firstKSitesReachLevel m (stageNumber r)
          (simpleRandomWalk omega) ≤
        (S.terminalEndTime omega : WithTop ℕ)}) :
    MeasurableSet (S.orderedHistoryRefinedIncrementAtom i a r c) := by
  exact measurableSet_of_iidHistory_fibers_nat S.terminalEndTime
    (S.orderedHistoryRefinedIncrementAtom i a r c)
    (fun n ↦ S.orderedHistoryRefinedIncrementAtom_terminalPast
      i a r c hm hbefore n)

noncomputable def orderedHistoryRefinedPathAtom
    (i : Fin 6) (a : AlphaTriple) (r : StageIndex)
    (c : Fin (stageNumber r) → Site) : Set Path :=
  simpleRandomWalk '' S.orderedHistoryRefinedIncrementAtom i a r c

theorem measurableSet_orderedHistoryRefinedPathAtom
    (i : Fin 6) (a : AlphaTriple) (r : StageIndex)
    (c : Fin (stageNumber r) → Site) (hm : 0 < m)
    (hbefore : S.orderedHistoryRefinedIncrementAtom i a r c ⊆
      {omega | firstKSitesReachLevel m (stageNumber r)
          (simpleRandomWalk omega) ≤
        (S.terminalEndTime omega : WithTop ℕ)}) :
    MeasurableSet (S.orderedHistoryRefinedPathAtom i a r c) := by
  exact measurableEmbedding_simpleRandomWalk.measurableSet_image.2
    (S.measurableSet_orderedHistoryRefinedIncrementAtom
      i a r c hm hbefore)

theorem orderedHistoryRefinedPathAtom_subset_history
    (i : Fin 6) (a : AlphaTriple) (r : StageIndex)
    (c : Fin (stageNumber r) → Site) :
    S.orderedHistoryRefinedPathAtom i a r c ⊆
      prop47History canonicalProfiles canonicalCStar m i a r.1 := by
  rintro s ⟨omega, homega, rfl⟩
  exact homega.2.2

theorem orderedHistoryRefinedPathAtom_subset_sourceAtom
    (i : Fin 6) (a : AlphaTriple) (r : StageIndex)
    (c : Fin (stageNumber r) → Site) :
    S.orderedHistoryRefinedPathAtom i a r c ⊆ S.pathAtom := by
  rintro s ⟨omega, homega, rfl⟩
  exact homega.1

end PrimedColumnWinnerSource

/-- The forward refined path atom is literally the coarse terminal atom
intersected with the ordered canonical history. -/
theorem ForwardColumnWinnerSource.orderedHistoryRefinedPathAtom_eq
    {m : ℕ} (S : ForwardColumnWinnerSource m)
    (i : Fin 6) (a : HLOZProp47Parameters.AlphaTriple) (r : StageIndex)
    (c : Fin (stageNumber r) → Site) :
    S.orderedHistoryRefinedPathAtom i a r c =
      S.pathAtom ∩ orderedCanonicalHistoryEvent m i a r c := by
  ext s
  constructor
  · rintro ⟨omega, ⟨hsource, hhistory⟩, rfl⟩
    exact ⟨hsource, hhistory⟩
  · rintro ⟨hsource, hhistory⟩
    rcases hsource.1 with ⟨omega, _hterminal, rfl⟩
    exact ⟨omega, ⟨hsource, hhistory⟩, rfl⟩

/-- Backward/primed analogue of the exact coarse-atom/history identity. -/
theorem PrimedColumnWinnerSource.orderedHistoryRefinedPathAtom_eq
    {m : ℕ} (S : PrimedColumnWinnerSource m)
    (i : Fin 6) (a : HLOZProp47Parameters.AlphaTriple) (r : StageIndex)
    (c : Fin (stageNumber r) → Site) :
    S.orderedHistoryRefinedPathAtom i a r c =
      S.pathAtom ∩ orderedCanonicalHistoryEvent m i a r c := by
  ext s
  constructor
  · rintro ⟨omega, ⟨hsource, hhistory⟩, rfl⟩
    exact ⟨hsource, hhistory⟩
  · rintro ⟨hsource, hhistory⟩
    rcases hsource.1 with ⟨omega, _hterminal, rfl⟩
    exact ⟨omega, ⟨hsource, hhistory⟩, rfl⟩

/-- Branch-ready forward terminal atom with its ordered source history.
The equality of stage indices records which Proposition-4.7 stage this
terminal parser represents. -/
structure ForwardColumnOrderedHistorySource
    (m : ℕ) (i : Fin 6) (a : AlphaTriple) (r : StageIndex) where
  source : ForwardColumnWinnerSource m
  stage_eq : source.k = stageNumber r
  orderedSites : Fin (stageNumber r) → Site
  m_pos : 0 < m
  threshold_before_terminal :
    source.orderedHistoryRefinedIncrementAtom i a r orderedSites ⊆
    {omega | firstKSitesReachLevel m (stageNumber r)
        (simpleRandomWalk omega) ≤
      (source.terminalEndTime omega : WithTop ℕ)}

namespace ForwardColumnOrderedHistorySource

variable {m : ℕ} {i : Fin 6} {a : AlphaTriple} {r : StageIndex}
    (S : ForwardColumnOrderedHistorySource m i a r)

noncomputable def incrementAtom : Set (ℕ → Direction) :=
  S.source.orderedHistoryRefinedIncrementAtom i a r S.orderedSites

noncomputable def pathAtom : Set Path :=
  S.source.orderedHistoryRefinedPathAtom i a r S.orderedSites

theorem stoppedPast (n : ℕ) :
    MeasurableSet[iidHistory (X := Direction) n]
      (S.incrementAtom ∩
        {omega | S.source.terminalEndTime omega = n}) := by
  exact S.source.orderedHistoryRefinedIncrementAtom_terminalPast
    i a r S.orderedSites S.m_pos S.threshold_before_terminal n

theorem measurableSet_incrementAtom : MeasurableSet S.incrementAtom :=
  S.source.measurableSet_orderedHistoryRefinedIncrementAtom
    i a r S.orderedSites S.m_pos S.threshold_before_terminal

theorem measurableSet_pathAtom : MeasurableSet S.pathAtom :=
  S.source.measurableSet_orderedHistoryRefinedPathAtom
    i a r S.orderedSites S.m_pos S.threshold_before_terminal

theorem pathAtom_subset_history :
    S.pathAtom ⊆
      prop47History canonicalProfiles canonicalCStar m i a r.1 :=
  S.source.orderedHistoryRefinedPathAtom_subset_history
    i a r S.orderedSites

theorem pathAtom_subset_sourceAtom : S.pathAtom ⊆ S.source.pathAtom :=
  S.source.orderedHistoryRefinedPathAtom_subset_sourceAtom
    i a r S.orderedSites

/-- The sole probabilistic Proposition-4.9 obligation on the refined atom.
It is intentionally not inferred from measurability or from the coarse
terminal product law. -/
def ScreenEstimate (screen : Set Path) (rate : ℝ≥0∞) : Prop :=
  RefinedAtomScreenEstimate S.pathAtom screen rate

/-- Proposition-4.9 specialization in the coefficient convention used by
the finite-branch aggregator. -/
def Prop49ScreenEstimate
    (localCoeff : ℕ) (alpha : ℝ) (screen : Set Path) : Prop :=
  S.ScreenEstimate screen (sourceProp49ScreenRate m localCoeff alpha)

theorem history_screen_le
    (screen : Set Path) (rate : ℝ≥0∞)
    (hsource : S.ScreenEstimate screen rate) :
    simpleRandomWalkLaw
        (S.pathAtom ∩
          prop47History canonicalProfiles canonicalCStar m i a r.1 ∩
          screen) ≤
      rate * simpleRandomWalkLaw
        (S.pathAtom ∩
          prop47History canonicalProfiles canonicalCStar m i a r.1) := by
  exact refinedAtom_history_screen_le S.pathAtom
    (prop47History canonicalProfiles canonicalCStar m i a r.1)
    screen rate S.pathAtom_subset_history hsource

theorem prop49_history_screen_le
    (localCoeff : ℕ) (alpha : ℝ) (screen : Set Path)
    (hsource : S.Prop49ScreenEstimate localCoeff alpha screen) :
    simpleRandomWalkLaw
        (S.pathAtom ∩
          prop47History canonicalProfiles canonicalCStar m i a r.1 ∩
          screen) ≤
      sourceProp49ScreenRate m localCoeff alpha *
        simpleRandomWalkLaw
          (S.pathAtom ∩
            prop47History canonicalProfiles canonicalCStar m i a r.1) :=
  S.history_screen_le screen (sourceProp49ScreenRate m localCoeff alpha)
    hsource

end ForwardColumnOrderedHistorySource

/-- Branch-ready backward terminal phase of `Y`, kept distinct from the
reflected `Y'` branch. -/
structure PrimedColumnOrderedHistorySource
    (m : ℕ) (i : Fin 6) (a : AlphaTriple) (r : StageIndex) where
  source : PrimedColumnWinnerSource m
  stage_eq : source.k = stageNumber r
  orderedSites : Fin (stageNumber r) → Site
  m_pos : 0 < m
  threshold_before_terminal :
    source.orderedHistoryRefinedIncrementAtom i a r orderedSites ⊆
    {omega | firstKSitesReachLevel m (stageNumber r)
        (simpleRandomWalk omega) ≤
      (source.terminalEndTime omega : WithTop ℕ)}

namespace PrimedColumnOrderedHistorySource

variable {m : ℕ} {i : Fin 6} {a : AlphaTriple} {r : StageIndex}
    (S : PrimedColumnOrderedHistorySource m i a r)

noncomputable def incrementAtom : Set (ℕ → Direction) :=
  S.source.orderedHistoryRefinedIncrementAtom i a r S.orderedSites

noncomputable def pathAtom : Set Path :=
  S.source.orderedHistoryRefinedPathAtom i a r S.orderedSites

theorem stoppedPast (n : ℕ) :
    MeasurableSet[iidHistory (X := Direction) n]
      (S.incrementAtom ∩
        {omega | S.source.terminalEndTime omega = n}) := by
  exact S.source.orderedHistoryRefinedIncrementAtom_terminalPast
    i a r S.orderedSites S.m_pos S.threshold_before_terminal n

theorem measurableSet_incrementAtom : MeasurableSet S.incrementAtom :=
  S.source.measurableSet_orderedHistoryRefinedIncrementAtom
    i a r S.orderedSites S.m_pos S.threshold_before_terminal

theorem measurableSet_pathAtom : MeasurableSet S.pathAtom :=
  S.source.measurableSet_orderedHistoryRefinedPathAtom
    i a r S.orderedSites S.m_pos S.threshold_before_terminal

theorem pathAtom_subset_history :
    S.pathAtom ⊆
      prop47History canonicalProfiles canonicalCStar m i a r.1 :=
  S.source.orderedHistoryRefinedPathAtom_subset_history
    i a r S.orderedSites

theorem pathAtom_subset_sourceAtom : S.pathAtom ⊆ S.source.pathAtom :=
  S.source.orderedHistoryRefinedPathAtom_subset_sourceAtom
    i a r S.orderedSites

def ScreenEstimate (screen : Set Path) (rate : ℝ≥0∞) : Prop :=
  RefinedAtomScreenEstimate S.pathAtom screen rate

def Prop49ScreenEstimate
    (localCoeff : ℕ) (alpha : ℝ) (screen : Set Path) : Prop :=
  S.ScreenEstimate screen (sourceProp49ScreenRate m localCoeff alpha)

theorem history_screen_le
    (screen : Set Path) (rate : ℝ≥0∞)
    (hsource : S.ScreenEstimate screen rate) :
    simpleRandomWalkLaw
        (S.pathAtom ∩
          prop47History canonicalProfiles canonicalCStar m i a r.1 ∩
          screen) ≤
      rate * simpleRandomWalkLaw
        (S.pathAtom ∩
          prop47History canonicalProfiles canonicalCStar m i a r.1) := by
  exact refinedAtom_history_screen_le S.pathAtom
    (prop47History canonicalProfiles canonicalCStar m i a r.1)
    screen rate S.pathAtom_subset_history hsource

theorem prop49_history_screen_le
    (localCoeff : ℕ) (alpha : ℝ) (screen : Set Path)
    (hsource : S.Prop49ScreenEstimate localCoeff alpha screen) :
    simpleRandomWalkLaw
        (S.pathAtom ∩
          prop47History canonicalProfiles canonicalCStar m i a r.1 ∩
          screen) ≤
      sourceProp49ScreenRate m localCoeff alpha *
        simpleRandomWalkLaw
          (S.pathAtom ∩
            prop47History canonicalProfiles canonicalCStar m i a r.1) :=
  S.history_screen_le screen (sourceProp49ScreenRate m localCoeff alpha)
    hsource

end PrimedColumnOrderedHistorySource

/-- Countable forward-phase atom family in exactly the shape needed by one
branch of `Prop47StoppedProfileProp49RefinedFiniteBranchEstimate`.  The
uniform tail is the explicit `screen_estimate` field. -/
structure ForwardColumnOrderedHistoryProp49Branch
    (m : ℕ) (i : Fin 6) (a : AlphaTriple) (r : StageIndex)
    (localCoeff : ℕ) (alpha : ℝ) (screen : Set Path) where
  atoms : ℕ → ForwardColumnOrderedHistorySource m i a r
  pairwise_disjoint : Pairwise fun n l ↦
    Disjoint (atoms n).pathAtom (atoms l).pathAtom
  cover :
    prop47History canonicalProfiles canonicalCStar m i a r.1 ∩ screen ⊆
      ⋃ n, (atoms n).pathAtom
  screen_estimate : ∀ n,
    (atoms n).Prop49ScreenEstimate localCoeff alpha screen

namespace ForwardColumnOrderedHistoryProp49Branch

variable {m : ℕ} {i : Fin 6} {a : AlphaTriple} {r : StageIndex}
    {localCoeff : ℕ} {alpha : ℝ} {screen : Set Path}
    (B : ForwardColumnOrderedHistoryProp49Branch
      m i a r localCoeff alpha screen)

theorem measurable_atom (n : ℕ) : MeasurableSet (B.atoms n).pathAtom :=
  (B.atoms n).measurableSet_pathAtom

theorem local_history_screen_le (n : ℕ) :
    simpleRandomWalkLaw
        ((B.atoms n).pathAtom ∩
          prop47History canonicalProfiles canonicalCStar m i a r.1 ∩
          screen) ≤
      sourceProp49ScreenRate m localCoeff alpha *
        simpleRandomWalkLaw
          ((B.atoms n).pathAtom ∩
            prop47History canonicalProfiles canonicalCStar m i a r.1) :=
  (B.atoms n).prop49_history_screen_le localCoeff alpha screen
    (B.screen_estimate n)

end ForwardColumnOrderedHistoryProp49Branch

/-- Independently conditioned backward terminal phase, with the same exact
branch interface and no reflection applied to it. -/
structure PrimedColumnOrderedHistoryProp49Branch
    (m : ℕ) (i : Fin 6) (a : AlphaTriple) (r : StageIndex)
    (localCoeff : ℕ) (alpha : ℝ) (screen : Set Path) where
  atoms : ℕ → PrimedColumnOrderedHistorySource m i a r
  pairwise_disjoint : Pairwise fun n l ↦
    Disjoint (atoms n).pathAtom (atoms l).pathAtom
  cover :
    prop47History canonicalProfiles canonicalCStar m i a r.1 ∩ screen ⊆
      ⋃ n, (atoms n).pathAtom
  screen_estimate : ∀ n,
    (atoms n).Prop49ScreenEstimate localCoeff alpha screen

namespace PrimedColumnOrderedHistoryProp49Branch

variable {m : ℕ} {i : Fin 6} {a : AlphaTriple} {r : StageIndex}
    {localCoeff : ℕ} {alpha : ℝ} {screen : Set Path}
    (B : PrimedColumnOrderedHistoryProp49Branch
      m i a r localCoeff alpha screen)

theorem measurable_atom (n : ℕ) : MeasurableSet (B.atoms n).pathAtom :=
  (B.atoms n).measurableSet_pathAtom

theorem local_history_screen_le (n : ℕ) :
    simpleRandomWalkLaw
        ((B.atoms n).pathAtom ∩
          prop47History canonicalProfiles canonicalCStar m i a r.1 ∩
          screen) ≤
      sourceProp49ScreenRate m localCoeff alpha *
        simpleRandomWalkLaw
          ((B.atoms n).pathAtom ∩
            prop47History canonicalProfiles canonicalCStar m i a r.1) :=
  (B.atoms n).prop49_history_screen_le localCoeff alpha screen
    (B.screen_estimate n)

end PrimedColumnOrderedHistoryProp49Branch

/-! ## Lemmas 4.11--4.12 equation-(4.47) constructors -/

/-- Reflection invariance for any measurable path event under the simple
random-walk law. -/
theorem simpleRandomWalkLaw_reflectPath_preimage
    (E : Set Path) (hE : MeasurableSet E) :
    simpleRandomWalkLaw (HLOZPairingProfiles.reflectPath ⁻¹' E) =
      simpleRandomWalkLaw E := by
  calc
    simpleRandomWalkLaw (HLOZPairingProfiles.reflectPath ⁻¹' E) =
        (simpleRandomWalkLaw.map HLOZPairingProfiles.reflectPath) E := by
      rw [Measure.map_apply
        HLOZProp47Prop45YColumns.measurable_reflectPath hE]
    _ = simpleRandomWalkLaw E := by
      rw [HLOZProp47Prop45YColumns.simpleRandomWalkLaw_map_reflectPath]

/-- Restriction and observation commute with reflection.  This is the
measure-theoretic engine for transporting an entire equation-(4.47) branch
atom, rather than reflecting one conditional phase by fiat. -/
theorem simpleRandomWalkLaw_restrict_reflectPath_preimage_map_comp
    {beta : Type*} [MeasurableSpace beta]
    (E : Set Path) (hE : MeasurableSet E)
    (f : Path → beta) (hf : Measurable f) :
    (simpleRandomWalkLaw.restrict
        (HLOZPairingProfiles.reflectPath ⁻¹' E)).map
        (f ∘ HLOZPairingProfiles.reflectPath) =
      (simpleRandomWalkLaw.restrict E).map f := by
  ext B hB
  let R := HLOZPairingProfiles.reflectPath
  have hR : Measurable R :=
    HLOZProp47Prop45YColumns.measurable_reflectPath
  rw [Measure.map_apply (hf.comp hR) hB, Measure.map_apply hf hB,
    Measure.restrict_apply (hB.preimage (hf.comp hR)),
    Measure.restrict_apply (hB.preimage hf)]
  have hset : (f ∘ R) ⁻¹' B ∩ R ⁻¹' E =
      R ⁻¹' (f ⁻¹' B ∩ E) := by
    ext s
    rfl
  rw [hset]
  exact simpleRandomWalkLaw_reflectPath_preimage _
    ((hB.preimage hf).inter hE)

/-- Transport a branch-local stopped-profile atom through the origin-fixing
reflection.  The coordinate/profile/category data and `rho` are unchanged;
only path events and path statistics are precomposed with reflection. -/
noncomputable def reflectStoppedEquation447BranchAtom
    {cWindow m : ℕ} {ratioC rho : ℝ}
    {failure : Set Path}
    (A : StoppedEquation447BranchAtom cWindow m ratioC
      failure rho) :
    StoppedEquation447BranchAtom cWindow m ratioC
      (HLOZPairingProfiles.reflectPath ⁻¹' failure) rho where
  Coord := A.Coord
  coordFintype := A.coordFintype
  pathAtom := HLOZPairingProfiles.reflectPath ⁻¹' A.pathAtom
  measurableSet_pathAtom := A.measurableSet_pathAtom.preimage
    HLOZProp47Prop45YColumns.measurable_reflectPath
  profile := A.profile
  profile_lt := A.profile_lt
  lazyVector := A.lazyVector ∘ HLOZPairingProfiles.reflectPath
  measurable_lazyVector := A.measurable_lazyVector.comp
    HLOZProp47Prop45YColumns.measurable_reflectPath
  nextDirection := A.nextDirection ∘ HLOZPairingProfiles.reflectPath
  measurable_nextDirection := A.measurable_nextDirection.comp
    HLOZProp47Prop45YColumns.measurable_reflectPath
  forcedDirection := A.forcedDirection
  D := A.D
  badAtom := A.badAtom
  historyAtom := A.historyAtom
  category := A.category
  categoryLaw := A.categoryLaw
  categoryLaw_probability := A.categoryLaw_probability
  map_law := by
    change (simpleRandomWalkLaw.restrict
        (HLOZPairingProfiles.reflectPath ⁻¹' A.pathAtom)).map
        ((fun s ↦ (A.lazyVector s, A.nextDirection s)) ∘
          HLOZPairingProfiles.reflectPath) = _
    rw [simpleRandomWalkLaw_restrict_reflectPath_preimage_map_comp
      A.pathAtom A.measurableSet_pathAtom
      (fun s ↦ (A.lazyVector s, A.nextDirection s))
      (A.measurable_lazyVector.prodMk A.measurable_nextDirection), A.map_law,
      simpleRandomWalkLaw_reflectPath_preimage A.pathAtom
        A.measurableSet_pathAtom]
  failure_subset := by
    intro s hs
    exact A.failure_subset ⟨hs.1, hs.2⟩
  thetaPathEvent := HLOZPairingProfiles.reflectPath ⁻¹' A.thetaPathEvent
  theta_preimage_subset := by
    intro s hs
    exact A.theta_preimage_subset ⟨hs.1, hs.2⟩
  equation447_cover := A.equation447_cover
  bad_subset_history_allUpper := A.bad_subset_history_allUpper
  conditional_category_product := A.conditional_category_product
  category_mass_ratio := A.category_mass_ratio
  history_disjoint := A.history_disjoint
  history_measurable := A.history_measurable

/-- Reflection transport for the literal deleted-path switch.  The bad and
witness cells are profile-space objects, so the full (4.54) mechanism is
preserved verbatim while path events are pulled back. -/
noncomputable def reflectStoppedEquation447PathWitnessBranchAtom
    {cWindow m : ℕ} {c rho : ℝ}
    {failure : Set Path}
    (A : StoppedEquation447PathWitnessBranchAtom cWindow m c
      failure rho) :
    StoppedEquation447PathWitnessBranchAtom cWindow m c
      (HLOZPairingProfiles.reflectPath ⁻¹' failure) rho where
  Coord := A.Coord
  coordFintype := A.coordFintype
  Path := A.Path
  pathCountable := A.pathCountable
  pathAtom := HLOZPairingProfiles.reflectPath ⁻¹' A.pathAtom
  measurableSet_pathAtom := A.measurableSet_pathAtom.preimage
    HLOZProp47Prop45YColumns.measurable_reflectPath
  profile := A.profile
  profile_lt := A.profile_lt
  lazyVector := A.lazyVector ∘ HLOZPairingProfiles.reflectPath
  measurable_lazyVector := A.measurable_lazyVector.comp
    HLOZProp47Prop45YColumns.measurable_reflectPath
  nextDirection := A.nextDirection ∘ HLOZPairingProfiles.reflectPath
  measurable_nextDirection := A.measurable_nextDirection.comp
    HLOZProp47Prop45YColumns.measurable_reflectPath
  forcedDirection := A.forcedDirection
  D := A.D
  badAtom := A.badAtom
  witnessAtom := A.witnessAtom
  map_law := by
    change (simpleRandomWalkLaw.restrict
        (HLOZPairingProfiles.reflectPath ⁻¹' A.pathAtom)).map
        ((fun s ↦ (A.lazyVector s, A.nextDirection s)) ∘
          HLOZPairingProfiles.reflectPath) = _
    rw [simpleRandomWalkLaw_restrict_reflectPath_preimage_map_comp
      A.pathAtom A.measurableSet_pathAtom
      (fun s ↦ (A.lazyVector s, A.nextDirection s))
      (A.measurable_lazyVector.prodMk A.measurable_nextDirection), A.map_law,
      simpleRandomWalkLaw_reflectPath_preimage A.pathAtom
        A.measurableSet_pathAtom]
  failure_subset := by
    intro s hs
    exact A.failure_subset ⟨hs.1, hs.2⟩
  thetaPathEvent := HLOZPairingProfiles.reflectPath ⁻¹' A.thetaPathEvent
  theta_preimage_subset := by
    intro s hs
    exact A.theta_preimage_subset ⟨hs.1, hs.2⟩
  equation447_cover := A.equation447_cover
  path_switch := A.path_switch
  witness_disjoint := A.witness_disjoint
  witness_measurable := A.witness_measurable

@[simp] theorem reflectSite_reflectSite (x : Site) :
    reflectSite (reflectSite x) = x := by
  rcases x with ⟨x₁, x₂⟩
  simp [reflectSite]

@[simp] theorem reflectPath_reflectPath (s : Path) :
    reflectPath (reflectPath s) = s := by
  funext n
  exact reflectSite_reflectSite (s n)

/-- Distinguished endpoints do not themselves reflect pointwise from the
even-left column tiling to the odd-left tiling.  The reflected domino's
distinguished endpoint is one step west of the reflected old endpoint. -/
def reflectYDistinguishedEndpoint (x : Site) : Site :=
  shift (reflectSite x) (vec west)

theorem reflectYDistinguishedEndpoint_injective :
    Function.Injective reflectYDistinguishedEndpoint := by
  rintro ⟨x₁, x₂⟩ ⟨y₁, y₂⟩ h
  simp [reflectYDistinguishedEndpoint, reflectSite, shift, vec, west] at h ⊢
  omega

theorem distinguishedEndpoint_y_reflect (x : Site) :
    distinguishedEndpoint yIndex' (reflectSite x) =
      reflectYDistinguishedEndpoint (distinguishedEndpoint yIndex x) := by
  rcases x with ⟨x₁, x₂⟩
  by_cases hx : Even x₁
  · have hxeven : Even (-x₁) := by simpa using hx
    have hxnotodd : ¬ Odd (-x₁) := Int.not_odd_iff_even.mpr hxeven
    ext <;>
      simp [distinguishedEndpoint, yIndex, yIndex',
        reflectYDistinguishedEndpoint, reflectSite, shift, vec, west,
        hx, hxnotodd]
  · have hxodd : Odd x₁ := Int.not_even_iff_odd.mp hx
    have hxodd' : Odd (-x₁) := by simpa using hxodd
    ext <;>
      simp [distinguishedEndpoint, yIndex, yIndex',
        reflectYDistinguishedEndpoint, reflectSite, shift, vec, west,
        hx, hxodd']

theorem creationDominoEndpoints_y_reflect
    (s : Path) (m k : ℕ) :
    creationDominoEndpoints yIndex' (reflectPath s) m k =
      (creationDominoEndpoints yIndex s m k).image
        reflectYDistinguishedEndpoint := by
  unfold creationDominoEndpoints
  rw [Finset.image_image]
  apply Finset.image_congr
  intro j hj
  change distinguishedEndpoint yIndex'
      (levelCreationSite (reflectPath s) m j) =
    reflectYDistinguishedEndpoint
      (distinguishedEndpoint yIndex (levelCreationSite s m j))
  rw [levelCreationSite_reflectPath, distinguishedEndpoint_y_reflect]

theorem nearFavoriteSites_y_reflect
    (s : Path) (m k : ℕ) (alpha : ℝ) :
    nearFavoriteSites yIndex' (reflectPath s) m k alpha =
      (nearFavoriteSites yIndex s m k alpha).image reflectSite := by
  classical
  unfold nearFavoriteSites
  rw [visitedSites_reflectPath, directCreationTime_reflectPath,
    firstKSitesReachLevel_reflectPath, creationDominoEndpoints_y_reflect]
  ext y
  simp only [Finset.mem_filter, Finset.mem_image]
  constructor
  · rintro ⟨⟨x, hxVisited, rfl⟩, hfinite, houtside, hlower, hupper⟩
    refine ⟨x, ⟨hxVisited, hfinite, ?_, ?_, ?_⟩, rfl⟩
    · intro hcreated
      apply houtside
      rw [distinguishedEndpoint_y_reflect]
      exact ⟨distinguishedEndpoint yIndex x, hcreated, rfl⟩
    · simpa only [localTime_reflectPath] using hlower
    · simpa only [localTime_reflectPath] using hupper
  · rintro ⟨x, ⟨hxVisited, hfinite, houtside, hlower, hupper⟩, rfl⟩
    refine ⟨⟨x, hxVisited, rfl⟩, hfinite, ?_, ?_, ?_⟩
    · intro hcreated
      rcases hcreated with ⟨z, hz, hEq⟩
      apply houtside
      have hEq' : distinguishedEndpoint yIndex x = z := by
        apply reflectYDistinguishedEndpoint_injective
        rw [distinguishedEndpoint_y_reflect] at hEq
        exact hEq.symm
      exact hEq' ▸ hz
    · simpa only [localTime_reflectPath] using hlower
    · simpa only [localTime_reflectPath] using hupper

theorem nearFavoriteSites_y_reflect_card
    (s : Path) (m k : ℕ) (alpha : ℝ) :
    (nearFavoriteSites yIndex' (reflectPath s) m k alpha).card =
      (nearFavoriteSites yIndex s m k alpha).card := by
  rw [nearFavoriteSites_y_reflect]
  exact Finset.card_image_of_injective _ reflectSite_injective

theorem lemma411412CardinalityFailureEvent_y_reflect_iff
    (s : Path) (m : ℕ) (r : StageIndex) :
    reflectPath s ∈ lemma411412CardinalityFailureEvent m yIndex' r ↔
      s ∈ lemma411412CardinalityFailureEvent m yIndex r := by
  constructor
  · rintro ⟨hprefix, hcard⟩
    refine ⟨(prefixPairingEvent_y_reflect_iff s m _).mp hprefix, ?_⟩
    change Real.log (m : ℝ) ^ 2 <
      (nearFavoriteSites yIndex' (reflectPath s) m (stageNumber r)
        kappaOne).card at hcard
    change Real.log (m : ℝ) ^ 2 <
      (nearFavoriteSites yIndex s m (stageNumber r) kappaOne).card
    rwa [nearFavoriteSites_y_reflect_card] at hcard
  · rintro ⟨hprefix, hcard⟩
    refine ⟨(prefixPairingEvent_y_reflect_iff s m _).mpr hprefix, ?_⟩
    change Real.log (m : ℝ) ^ 2 <
      (nearFavoriteSites yIndex s m (stageNumber r) kappaOne).card at hcard
    change Real.log (m : ℝ) ^ 2 <
      (nearFavoriteSites yIndex' (reflectPath s) m (stageNumber r)
        kappaOne).card
    rwa [nearFavoriteSites_y_reflect_card]

/-- The `Y'` cardinality failure is exactly the reflection pullback of the
already assembled `Y` failure. -/
theorem lemma411412CardinalityFailureEvent_yPrime_preimage
    (m : ℕ) (r : StageIndex) :
    reflectPath ⁻¹' lemma411412CardinalityFailureEvent m yIndex r =
      lemma411412CardinalityFailureEvent m yIndex' r := by
  ext s
  simpa using
    (lemma411412CardinalityFailureEvent_y_reflect_iff
      (reflectPath s) m r).symm

noncomputable def ForwardColumnWinnerSource.toStoppedEquation447BranchAtom
    {m : ℕ} (S : ForwardColumnWinnerSource m)
    (cWindow : ℕ) (ratioC rho : ℝ)
    (branchEvent : Set Path)
    (R : Equation447BranchRemainingData cWindow m ratioC
      rho branchEvent S.pathAtom S.profile S.lazyVector S.nextDirection) :
    StoppedEquation447BranchAtom cWindow m ratioC
      branchEvent rho where
  Coord := S.Coord
  coordFintype := inferInstance
  pathAtom := S.pathAtom
  measurableSet_pathAtom := S.measurableSet_pathAtom
  profile := S.profile
  profile_lt := S.profile_lt
  lazyVector := S.lazyVector
  measurable_lazyVector := S.measurable_lazyVector
  nextDirection := S.nextDirection
  measurable_nextDirection := S.measurable_nextDirection
  forcedDirection := R.forcedDirection
  D := R.D
  badAtom := R.badAtom
  historyAtom := R.historyAtom
  category := R.category
  categoryLaw := R.categoryLaw
  categoryLaw_probability := R.categoryLaw_probability
  map_law := S.map_law
  failure_subset := R.failure_subset
  thetaPathEvent := R.thetaPathEvent
  theta_preimage_subset := R.theta_preimage_subset
  equation447_cover := R.equation447_cover
  bad_subset_history_allUpper := R.bad_subset_history_allUpper
  conditional_category_product := R.conditional_category_product
  category_mass_ratio := R.category_mass_ratio
  history_disjoint := R.history_disjoint
  history_measurable := R.history_measurable

noncomputable def PrimedColumnWinnerSource.toStoppedEquation447BranchAtom
    {m : ℕ} (S : PrimedColumnWinnerSource m)
    (cWindow : ℕ) (ratioC rho : ℝ)
    (branchEvent : Set Path)
    (R : Equation447BranchRemainingData cWindow m ratioC
      rho branchEvent S.pathAtom S.profile S.lazyVector S.nextDirection) :
    StoppedEquation447BranchAtom cWindow m ratioC
      branchEvent rho where
  Coord := S.Coord
  coordFintype := inferInstance
  pathAtom := S.pathAtom
  measurableSet_pathAtom := S.measurableSet_pathAtom
  profile := S.profile
  profile_lt := S.profile_lt
  lazyVector := S.lazyVector
  measurable_lazyVector := S.measurable_lazyVector
  nextDirection := S.nextDirection
  measurable_nextDirection := S.measurable_nextDirection
  forcedDirection := R.forcedDirection
  D := R.D
  badAtom := R.badAtom
  historyAtom := R.historyAtom
  category := R.category
  categoryLaw := R.categoryLaw
  categoryLaw_probability := R.categoryLaw_probability
  map_law := S.map_law
  failure_subset := R.failure_subset
  thetaPathEvent := R.thetaPathEvent
  theta_preimage_subset := R.theta_preimage_subset
  equation447_cover := R.equation447_cover
  bad_subset_history_allUpper := R.bad_subset_history_allUpper
  conditional_category_product := R.conditional_category_product
  category_mass_ratio := R.category_mass_ratio
  history_disjoint := R.history_disjoint
  history_measurable := R.history_measurable

/-- Literal deleted-path-switch atom for the forward column phase.  Its
stopped product map law and profile bound come from the terminal restart
theorem, not from the caller. -/
noncomputable def ForwardColumnWinnerSource.toStoppedEquation447PathWitnessBranchAtom
    {m : ℕ} (S : ForwardColumnWinnerSource m)
    (cWindow : ℕ) (c rho : ℝ) (branchEvent : Set Path)
    (R : Equation447PathWitnessBranchRemainingData cWindow m c rho
      branchEvent S.pathAtom S.profile S.lazyVector S.nextDirection) :
    StoppedEquation447PathWitnessBranchAtom cWindow m c branchEvent rho :=
  R.toStoppedEquation447PathWitnessBranchAtom S.measurableSet_pathAtom
    S.profile_lt S.measurable_lazyVector S.measurable_nextDirection S.map_law

/-- Literal deleted-path-switch atom for the independently conditioned
backward column phase. -/
noncomputable def PrimedColumnWinnerSource.toStoppedEquation447PathWitnessBranchAtom
    {m : ℕ} (S : PrimedColumnWinnerSource m)
    (cWindow : ℕ) (c rho : ℝ) (branchEvent : Set Path)
    (R : Equation447PathWitnessBranchRemainingData cWindow m c rho
      branchEvent S.pathAtom S.profile S.lazyVector S.nextDirection) :
    StoppedEquation447PathWitnessBranchAtom cWindow m c branchEvent rho :=
  R.toStoppedEquation447PathWitnessBranchAtom S.measurableSet_pathAtom
    S.profile_lt S.measurable_lazyVector S.measurable_nextDirection S.map_law

/-- One countable, disjoint forward-phase branch for the equation-(4.47)
consumer.  The cover is only of `branchEvent`; in particular this record
does not assert that one column phase covers a full cardinality failure. -/
structure ForwardColumnEquation447Branch
    (cWindow m : ℕ) (rho : ℝ)
    (branchEvent thetaPathEvent : Set Path) where
  source : ℕ → ForwardColumnWinnerSource m
  remaining : ∀ n, Equation447SourceBandBranchRemainingData cWindow m
    rho branchEvent thetaPathEvent (source n).pathAtom (source n).profile
      (source n).lazyVector (source n).nextDirection
  cover : branchEvent ⊆ ⋃ n, (source n).pathAtom
  pairwise_disjoint : Pairwise fun n l ↦
    Disjoint (source n).pathAtom (source l).pathAtom

namespace ForwardColumnEquation447Branch

noncomputable def atom
    {cWindow m : ℕ} {rho : ℝ}
    {branchEvent thetaPathEvent : Set Path}
    (B : ForwardColumnEquation447Branch cWindow m rho
      branchEvent thetaPathEvent)
    (growth : SourceWindowGrowth cWindow m) (n : ℕ) :
    StoppedEquation447BranchAtom cWindow m
      (Real.exp (sourceAdjacentComparisonExponent cWindow))
      branchEvent rho :=
  (B.source n).toStoppedEquation447BranchAtom cWindow
    (Real.exp (sourceAdjacentComparisonExponent cWindow))
    rho branchEvent
      ((B.remaining n).toCodedBranchRemainingData
        (B.source n).profile_lt growth |>.toRemainingData)

theorem cover_atoms
    {cWindow m : ℕ} {rho : ℝ}
    {branchEvent thetaPathEvent : Set Path}
    (B : ForwardColumnEquation447Branch cWindow m rho
      branchEvent thetaPathEvent)
    (growth : SourceWindowGrowth cWindow m) :
    branchEvent ⊆ ⋃ n, (B.atom growth n).pathAtom := by
  simpa only [atom,
    ForwardColumnWinnerSource.toStoppedEquation447BranchAtom]
    using B.cover

theorem pairwise_disjoint_atoms
    {cWindow m : ℕ} {rho : ℝ}
    {branchEvent thetaPathEvent : Set Path}
    (B : ForwardColumnEquation447Branch cWindow m rho
      branchEvent thetaPathEvent)
    (growth : SourceWindowGrowth cWindow m) :
    Pairwise fun n l ↦
      Disjoint (B.atom growth n).pathAtom (B.atom growth l).pathAtom := by
  simpa only [atom,
    ForwardColumnWinnerSource.toStoppedEquation447BranchAtom]
    using B.pairwise_disjoint

end ForwardColumnEquation447Branch

/-- The independently conditioned backward terminal phase as one local
equation-(4.47) branch. -/
structure PrimedColumnEquation447Branch
    (cWindow m : ℕ) (rho : ℝ)
    (branchEvent thetaPathEvent : Set Path) where
  source : ℕ → PrimedColumnWinnerSource m
  remaining : ∀ n, Equation447SourceBandBranchRemainingData cWindow m
    rho branchEvent thetaPathEvent (source n).pathAtom (source n).profile
      (source n).lazyVector (source n).nextDirection
  cover : branchEvent ⊆ ⋃ n, (source n).pathAtom
  pairwise_disjoint : Pairwise fun n l ↦
    Disjoint (source n).pathAtom (source l).pathAtom

namespace PrimedColumnEquation447Branch

noncomputable def atom
    {cWindow m : ℕ} {rho : ℝ}
    {branchEvent thetaPathEvent : Set Path}
    (B : PrimedColumnEquation447Branch cWindow m rho
      branchEvent thetaPathEvent)
    (growth : SourceWindowGrowth cWindow m) (n : ℕ) :
    StoppedEquation447BranchAtom cWindow m
      (Real.exp (sourceAdjacentComparisonExponent cWindow))
      branchEvent rho :=
  (B.source n).toStoppedEquation447BranchAtom cWindow
    (Real.exp (sourceAdjacentComparisonExponent cWindow))
    rho branchEvent
      ((B.remaining n).toCodedBranchRemainingData
        (B.source n).profile_lt growth |>.toRemainingData)

theorem cover_atoms
    {cWindow m : ℕ} {rho : ℝ}
    {branchEvent thetaPathEvent : Set Path}
    (B : PrimedColumnEquation447Branch cWindow m rho
      branchEvent thetaPathEvent)
    (growth : SourceWindowGrowth cWindow m) :
    branchEvent ⊆ ⋃ n, (B.atom growth n).pathAtom := by
  simpa only [atom,
    PrimedColumnWinnerSource.toStoppedEquation447BranchAtom]
    using B.cover

theorem pairwise_disjoint_atoms
    {cWindow m : ℕ} {rho : ℝ}
    {branchEvent thetaPathEvent : Set Path}
    (B : PrimedColumnEquation447Branch cWindow m rho
      branchEvent thetaPathEvent)
    (growth : SourceWindowGrowth cWindow m) :
    Pairwise fun n l ↦
      Disjoint (B.atom growth n).pathAtom (B.atom growth l).pathAtom := by
  simpa only [atom,
    PrimedColumnWinnerSource.toStoppedEquation447BranchAtom]
    using B.pairwise_disjoint

end PrimedColumnEquation447Branch

/-! ### Literal deleted-path witnesses for the two column phases -/

structure ForwardColumnEquation447PathWitnessBranch
    (cWindow m : ℕ) (c rho : ℝ)
    (branchEvent thetaTarget : Set Path) where
  source : ℕ → ForwardColumnWinnerSource m
  remaining : ∀ n,
    Equation447PathWitnessBranchRemainingData cWindow m c rho
      branchEvent (source n).pathAtom (source n).profile
        (source n).lazyVector (source n).nextDirection
  cover : branchEvent ⊆ ⋃ n, (source n).pathAtom
  theta_subset : ∀ n, (remaining n).thetaPathEvent ⊆ thetaTarget
  pairwise_disjoint : Pairwise fun n l ↦
    Disjoint (source n).pathAtom (source l).pathAtom

namespace ForwardColumnEquation447PathWitnessBranch

noncomputable def atom
    {cWindow m : ℕ} {c rho : ℝ}
    {branchEvent thetaTarget : Set Path}
    (B : ForwardColumnEquation447PathWitnessBranch
      cWindow m c rho branchEvent thetaTarget) (n : ℕ) :
    StoppedEquation447PathWitnessBranchAtom cWindow m c branchEvent rho :=
  (B.source n).toStoppedEquation447PathWitnessBranchAtom
    cWindow c rho branchEvent (B.remaining n)

@[simp] theorem atom_pathAtom
    {cWindow m : ℕ} {c rho : ℝ}
    {branchEvent thetaTarget : Set Path}
    (B : ForwardColumnEquation447PathWitnessBranch
      cWindow m c rho branchEvent thetaTarget) (n : ℕ) :
    (B.atom n).pathAtom = (B.source n).pathAtom := by
  rfl

@[simp] theorem atom_thetaPathEvent
    {cWindow m : ℕ} {c rho : ℝ}
    {branchEvent thetaTarget : Set Path}
    (B : ForwardColumnEquation447PathWitnessBranch
      cWindow m c rho branchEvent thetaTarget) (n : ℕ) :
    (B.atom n).thetaPathEvent = (B.remaining n).thetaPathEvent := by
  rfl

theorem cover_atoms
    {cWindow m : ℕ} {c rho : ℝ}
    {branchEvent thetaTarget : Set Path}
    (B : ForwardColumnEquation447PathWitnessBranch
      cWindow m c rho branchEvent thetaTarget) :
    branchEvent ⊆ ⋃ n, (B.atom n).pathAtom := by
  simpa using B.cover

theorem pairwise_disjoint_atoms
    {cWindow m : ℕ} {c rho : ℝ}
    {branchEvent thetaTarget : Set Path}
    (B : ForwardColumnEquation447PathWitnessBranch
      cWindow m c rho branchEvent thetaTarget) :
    Pairwise fun n l ↦ Disjoint (B.atom n).pathAtom (B.atom l).pathAtom := by
  simpa using B.pairwise_disjoint

end ForwardColumnEquation447PathWitnessBranch

structure PrimedColumnEquation447PathWitnessBranch
    (cWindow m : ℕ) (c rho : ℝ)
    (branchEvent thetaTarget : Set Path) where
  source : ℕ → PrimedColumnWinnerSource m
  remaining : ∀ n,
    Equation447PathWitnessBranchRemainingData cWindow m c rho
      branchEvent (source n).pathAtom (source n).profile
        (source n).lazyVector (source n).nextDirection
  cover : branchEvent ⊆ ⋃ n, (source n).pathAtom
  theta_subset : ∀ n, (remaining n).thetaPathEvent ⊆ thetaTarget
  pairwise_disjoint : Pairwise fun n l ↦
    Disjoint (source n).pathAtom (source l).pathAtom

namespace PrimedColumnEquation447PathWitnessBranch

noncomputable def atom
    {cWindow m : ℕ} {c rho : ℝ}
    {branchEvent thetaTarget : Set Path}
    (B : PrimedColumnEquation447PathWitnessBranch
      cWindow m c rho branchEvent thetaTarget) (n : ℕ) :
    StoppedEquation447PathWitnessBranchAtom cWindow m c branchEvent rho :=
  (B.source n).toStoppedEquation447PathWitnessBranchAtom
    cWindow c rho branchEvent (B.remaining n)

@[simp] theorem atom_pathAtom
    {cWindow m : ℕ} {c rho : ℝ}
    {branchEvent thetaTarget : Set Path}
    (B : PrimedColumnEquation447PathWitnessBranch
      cWindow m c rho branchEvent thetaTarget) (n : ℕ) :
    (B.atom n).pathAtom = (B.source n).pathAtom := by
  rfl

@[simp] theorem atom_thetaPathEvent
    {cWindow m : ℕ} {c rho : ℝ}
    {branchEvent thetaTarget : Set Path}
    (B : PrimedColumnEquation447PathWitnessBranch
      cWindow m c rho branchEvent thetaTarget) (n : ℕ) :
    (B.atom n).thetaPathEvent = (B.remaining n).thetaPathEvent := by
  rfl

theorem cover_atoms
    {cWindow m : ℕ} {c rho : ℝ}
    {branchEvent thetaTarget : Set Path}
    (B : PrimedColumnEquation447PathWitnessBranch
      cWindow m c rho branchEvent thetaTarget) :
    branchEvent ⊆ ⋃ n, (B.atom n).pathAtom := by
  simpa using B.cover

theorem pairwise_disjoint_atoms
    {cWindow m : ℕ} {c rho : ℝ}
    {branchEvent thetaTarget : Set Path}
    (B : PrimedColumnEquation447PathWitnessBranch
      cWindow m c rho branchEvent thetaTarget) :
    Pairwise fun n l ↦ Disjoint (B.atom n).pathAtom (B.atom l).pathAtom := by
  simpa using B.pairwise_disjoint

end PrimedColumnEquation447PathWitnessBranch

/-- Forward column data with the fixed-cardinality changed-path estimate
reduced to conditional categorical products and the binomial layer. -/
structure ForwardColumnEquation447CategoricalPathWitnessBranch
    (cWindow m : ℕ) (c rho : ℝ)
    (branchEvent thetaTarget : Set Path) where
  source : ℕ → ForwardColumnWinnerSource m
  remaining : ∀ n,
    Equation447CategoricalPathWitnessBranchRemainingData cWindow m c rho
      branchEvent (source n).pathAtom (source n).profile
        (source n).lazyVector (source n).nextDirection
  cover : branchEvent ⊆ ⋃ n, (source n).pathAtom
  theta_subset : ∀ n, (remaining n).thetaPathEvent ⊆ thetaTarget
  pairwise_disjoint : Pairwise fun n l ↦
    Disjoint (source n).pathAtom (source l).pathAtom

namespace ForwardColumnEquation447CategoricalPathWitnessBranch

noncomputable def toPathWitnessBranch
    {cWindow m : ℕ} {c rho : ℝ}
    {branchEvent thetaTarget : Set Path}
    (B : ForwardColumnEquation447CategoricalPathWitnessBranch
      cWindow m c rho branchEvent thetaTarget) :
    ForwardColumnEquation447PathWitnessBranch
      cWindow m c rho branchEvent thetaTarget where
  source := B.source
  remaining := fun n ↦ (B.remaining n).toRemainingData
  cover := B.cover
  theta_subset := B.theta_subset
  pairwise_disjoint := B.pairwise_disjoint

end ForwardColumnEquation447CategoricalPathWitnessBranch

/-- Backward/primed column counterpart of the conditional-categorical
changed-path source data. -/
structure PrimedColumnEquation447CategoricalPathWitnessBranch
    (cWindow m : ℕ) (c rho : ℝ)
    (branchEvent thetaTarget : Set Path) where
  source : ℕ → PrimedColumnWinnerSource m
  remaining : ∀ n,
    Equation447CategoricalPathWitnessBranchRemainingData cWindow m c rho
      branchEvent (source n).pathAtom (source n).profile
        (source n).lazyVector (source n).nextDirection
  cover : branchEvent ⊆ ⋃ n, (source n).pathAtom
  theta_subset : ∀ n, (remaining n).thetaPathEvent ⊆ thetaTarget
  pairwise_disjoint : Pairwise fun n l ↦
    Disjoint (source n).pathAtom (source l).pathAtom

namespace PrimedColumnEquation447CategoricalPathWitnessBranch

noncomputable def toPathWitnessBranch
    {cWindow m : ℕ} {c rho : ℝ}
    {branchEvent thetaTarget : Set Path}
    (B : PrimedColumnEquation447CategoricalPathWitnessBranch
      cWindow m c rho branchEvent thetaTarget) :
    PrimedColumnEquation447PathWitnessBranch
      cWindow m c rho branchEvent thetaTarget where
  source := B.source
  remaining := fun n ↦ (B.remaining n).toRemainingData
  cover := B.cover
  theta_subset := B.theta_subset
  pairwise_disjoint := B.pairwise_disjoint

end PrimedColumnEquation447CategoricalPathWitnessBranch

/-! ### Column categorical source data with the binomial layer internalized -/

/-- Forward column categorical data whose witness cardinality is the
canonical maximum weighted binomial layer. -/
structure ForwardColumnEquation447OptimalCategoricalPathWitnessBranch
    (cWindow m : ℕ) (ratioC rho : ℝ)
    (branchEvent thetaTarget : Set Path) where
  source : ℕ → ForwardColumnWinnerSource m
  remaining : ∀ n,
    Equation447OptimalCategoricalPathWitnessBranchRemainingData
      cWindow m ratioC rho
      branchEvent (source n).pathAtom (source n).profile
        (source n).lazyVector (source n).nextDirection
  cover : branchEvent ⊆ ⋃ n, (source n).pathAtom
  theta_subset : ∀ n, (remaining n).thetaPathEvent ⊆ thetaTarget
  pairwise_disjoint : Pairwise fun n l ↦
    Disjoint (source n).pathAtom (source l).pathAtom

namespace ForwardColumnEquation447OptimalCategoricalPathWitnessBranch

noncomputable def toPathWitnessBranch
    {cWindow m : ℕ} {ratioC rho : ℝ}
    {branchEvent thetaTarget : Set Path}
    (B : ForwardColumnEquation447OptimalCategoricalPathWitnessBranch
      cWindow m ratioC rho branchEvent thetaTarget)
    (hC : 0 < ratioC)
    (hbinomial : ∀ q, Nat.ceil rho ≤ q →
      ratioC ^ categoricalOptimalWitnessCount ratioC q ≤
        Real.exp (-categoricalOptimalRate ratioC * (q : ℝ)) *
          Nat.choose q (categoricalOptimalWitnessCount ratioC q)) :
    ForwardColumnEquation447PathWitnessBranch
      cWindow m (categoricalOptimalRate ratioC) rho
        branchEvent thetaTarget where
  source := B.source
  remaining := fun n ↦ (B.remaining n).toRemainingData hC hbinomial
  cover := B.cover
  theta_subset := B.theta_subset
  pairwise_disjoint := B.pairwise_disjoint

end ForwardColumnEquation447OptimalCategoricalPathWitnessBranch

/-- Backward/primed column counterpart with the numerical binomial layer
proved internally. -/
structure PrimedColumnEquation447OptimalCategoricalPathWitnessBranch
    (cWindow m : ℕ) (ratioC rho : ℝ)
    (branchEvent thetaTarget : Set Path) where
  source : ℕ → PrimedColumnWinnerSource m
  remaining : ∀ n,
    Equation447OptimalCategoricalPathWitnessBranchRemainingData
      cWindow m ratioC rho
      branchEvent (source n).pathAtom (source n).profile
        (source n).lazyVector (source n).nextDirection
  cover : branchEvent ⊆ ⋃ n, (source n).pathAtom
  theta_subset : ∀ n, (remaining n).thetaPathEvent ⊆ thetaTarget
  pairwise_disjoint : Pairwise fun n l ↦
    Disjoint (source n).pathAtom (source l).pathAtom

namespace PrimedColumnEquation447OptimalCategoricalPathWitnessBranch

noncomputable def toPathWitnessBranch
    {cWindow m : ℕ} {ratioC rho : ℝ}
    {branchEvent thetaTarget : Set Path}
    (B : PrimedColumnEquation447OptimalCategoricalPathWitnessBranch
      cWindow m ratioC rho branchEvent thetaTarget)
    (hC : 0 < ratioC)
    (hbinomial : ∀ q, Nat.ceil rho ≤ q →
      ratioC ^ categoricalOptimalWitnessCount ratioC q ≤
        Real.exp (-categoricalOptimalRate ratioC * (q : ℝ)) *
          Nat.choose q (categoricalOptimalWitnessCount ratioC q)) :
    PrimedColumnEquation447PathWitnessBranch
      cWindow m (categoricalOptimalRate ratioC) rho
        branchEvent thetaTarget where
  source := B.source
  remaining := fun n ↦ (B.remaining n).toRemainingData hC hbinomial
  cover := B.cover
  theta_subset := B.theta_subset
  pairwise_disjoint := B.pairwise_disjoint

end PrimedColumnEquation447OptimalCategoricalPathWitnessBranch

/-- Forward column optimal-categorical data in the source-faithful form
where disjointness of the changed-path witnesses follows from their stopped
horizons and level-count separation. -/
structure ForwardColumnEquation447LengthSeparatedOptimalCategoricalPathWitnessBranch
    (cWindow m : ℕ) (ratioC rho : ℝ)
    (branchEvent thetaTarget : Set Path) where
  source : ℕ → ForwardColumnWinnerSource m
  remaining : ∀ n,
    Equation447LengthSeparatedOptimalCategoricalPathWitnessBranchRemainingData
      cWindow m ratioC rho
      branchEvent (source n).pathAtom (source n).profile
        (source n).lazyVector (source n).nextDirection
  cover : branchEvent ⊆ ⋃ n, (source n).pathAtom
  theta_subset : ∀ n, (remaining n).thetaPathEvent ⊆ thetaTarget
  pairwise_disjoint : Pairwise fun n l ↦
    Disjoint (source n).pathAtom (source l).pathAtom

namespace ForwardColumnEquation447LengthSeparatedOptimalCategoricalPathWitnessBranch

noncomputable def toOptimalCategoricalPathWitnessBranch
    {cWindow m : ℕ} {ratioC rho : ℝ}
    {branchEvent thetaTarget : Set Path}
    (B : ForwardColumnEquation447LengthSeparatedOptimalCategoricalPathWitnessBranch
      cWindow m ratioC rho branchEvent thetaTarget) :
    ForwardColumnEquation447OptimalCategoricalPathWitnessBranch
      cWindow m ratioC rho branchEvent thetaTarget where
  source := B.source
  remaining := fun n ↦
    (B.remaining n).toOptimalCategoricalPathWitnessBranchRemainingData
  cover := B.cover
  theta_subset := B.theta_subset
  pairwise_disjoint := B.pairwise_disjoint

end ForwardColumnEquation447LengthSeparatedOptimalCategoricalPathWitnessBranch

/-- Backward/primed counterpart of the stopped-length categorical branch. -/
structure PrimedColumnEquation447LengthSeparatedOptimalCategoricalPathWitnessBranch
    (cWindow m : ℕ) (ratioC rho : ℝ)
    (branchEvent thetaTarget : Set Path) where
  source : ℕ → PrimedColumnWinnerSource m
  remaining : ∀ n,
    Equation447LengthSeparatedOptimalCategoricalPathWitnessBranchRemainingData
      cWindow m ratioC rho
      branchEvent (source n).pathAtom (source n).profile
        (source n).lazyVector (source n).nextDirection
  cover : branchEvent ⊆ ⋃ n, (source n).pathAtom
  theta_subset : ∀ n, (remaining n).thetaPathEvent ⊆ thetaTarget
  pairwise_disjoint : Pairwise fun n l ↦
    Disjoint (source n).pathAtom (source l).pathAtom

namespace PrimedColumnEquation447LengthSeparatedOptimalCategoricalPathWitnessBranch

noncomputable def toOptimalCategoricalPathWitnessBranch
    {cWindow m : ℕ} {ratioC rho : ℝ}
    {branchEvent thetaTarget : Set Path}
    (B : PrimedColumnEquation447LengthSeparatedOptimalCategoricalPathWitnessBranch
      cWindow m ratioC rho branchEvent thetaTarget) :
    PrimedColumnEquation447OptimalCategoricalPathWitnessBranch
      cWindow m ratioC rho branchEvent thetaTarget where
  source := B.source
  remaining := fun n ↦
    (B.remaining n).toOptimalCategoricalPathWitnessBranchRemainingData
  cover := B.cover
  theta_subset := B.theta_subset
  pairwise_disjoint := B.pairwise_disjoint

end PrimedColumnEquation447LengthSeparatedOptimalCategoricalPathWitnessBranch

/-- Forward column branch with both conditional products derived from literal
coordinate rectangles and (4.54) derived from stopped-length separation. -/
structure ForwardColumnEquation447LengthSeparatedRectangularOptimalCategoricalPathWitnessBranch
    (cWindow m : ℕ) (ratioC rho : ℝ)
    (branchEvent thetaTarget : Set Path) where
  source : ℕ → ForwardColumnWinnerSource m
  remaining : ∀ n,
    Equation447LengthSeparatedRectangularOptimalCategoricalPathWitnessBranchRemainingData
      cWindow m ratioC rho
      branchEvent thetaTarget (source n).pathAtom (source n).profile
        (source n).lazyVector (source n).nextDirection
  cover : branchEvent ⊆ ⋃ n, (source n).pathAtom
  pairwise_disjoint : Pairwise fun n l ↦
    Disjoint (source n).pathAtom (source l).pathAtom

namespace ForwardColumnEquation447LengthSeparatedRectangularOptimalCategoricalPathWitnessBranch

noncomputable def toLengthSeparatedOptimalCategoricalPathWitnessBranch
    {cWindow m : ℕ} {ratioC rho : ℝ}
    {branchEvent thetaTarget : Set Path}
    (B :
      ForwardColumnEquation447LengthSeparatedRectangularOptimalCategoricalPathWitnessBranch
        cWindow m ratioC rho branchEvent thetaTarget) :
    ForwardColumnEquation447LengthSeparatedOptimalCategoricalPathWitnessBranch
      cWindow m ratioC rho branchEvent thetaTarget where
  source := B.source
  remaining := fun n ↦
    (B.remaining n)
      |>.toLengthSeparatedOptimalCategoricalPathWitnessBranchRemainingData
  cover := B.cover
  theta_subset := fun _ ↦ Set.Subset.rfl
  pairwise_disjoint := B.pairwise_disjoint

end ForwardColumnEquation447LengthSeparatedRectangularOptimalCategoricalPathWitnessBranch

/-- Backward/primed rectangular counterpart. -/
structure PrimedColumnEquation447LengthSeparatedRectangularOptimalCategoricalPathWitnessBranch
    (cWindow m : ℕ) (ratioC rho : ℝ)
    (branchEvent thetaTarget : Set Path) where
  source : ℕ → PrimedColumnWinnerSource m
  remaining : ∀ n,
    Equation447LengthSeparatedRectangularOptimalCategoricalPathWitnessBranchRemainingData
      cWindow m ratioC rho
      branchEvent thetaTarget (source n).pathAtom (source n).profile
        (source n).lazyVector (source n).nextDirection
  cover : branchEvent ⊆ ⋃ n, (source n).pathAtom
  pairwise_disjoint : Pairwise fun n l ↦
    Disjoint (source n).pathAtom (source l).pathAtom

namespace PrimedColumnEquation447LengthSeparatedRectangularOptimalCategoricalPathWitnessBranch

noncomputable def toLengthSeparatedOptimalCategoricalPathWitnessBranch
    {cWindow m : ℕ} {ratioC rho : ℝ}
    {branchEvent thetaTarget : Set Path}
    (B :
      PrimedColumnEquation447LengthSeparatedRectangularOptimalCategoricalPathWitnessBranch
        cWindow m ratioC rho branchEvent thetaTarget) :
    PrimedColumnEquation447LengthSeparatedOptimalCategoricalPathWitnessBranch
      cWindow m ratioC rho branchEvent thetaTarget where
  source := B.source
  remaining := fun n ↦
    (B.remaining n)
      |>.toLengthSeparatedOptimalCategoricalPathWitnessBranchRemainingData
  cover := B.cover
  theta_subset := fun _ ↦ Set.Subset.rfl
  pairwise_disjoint := B.pairwise_disjoint

end PrimedColumnEquation447LengthSeparatedRectangularOptimalCategoricalPathWitnessBranch

/-- Literal forward column source-band data determines its optimal
categorical witness branch. -/
noncomputable def ForwardColumnEquation447Branch.toOptimalCategoricalPathWitnessBranch
    {cWindow m : ℕ} {rho : ℝ}
    {branchEvent thetaPathEvent : Set Path}
    (B : ForwardColumnEquation447Branch cWindow m rho
      branchEvent thetaPathEvent)
    (growth : SourceWindowGrowth cWindow m) :
    ForwardColumnEquation447OptimalCategoricalPathWitnessBranch
      cWindow m (Real.exp (sourceAdjacentComparisonExponent cWindow)) rho
      branchEvent thetaPathEvent where
  source := B.source
  remaining := fun n ↦
    (B.remaining n).toOptimalCategoricalPathWitnessBranchRemainingData
      (B.source n).profile_lt growth
  cover := B.cover
  theta_subset := fun _ ↦ le_rfl
  pairwise_disjoint := B.pairwise_disjoint

/-- Literal backward column source-band data determines its optimal
categorical witness branch. -/
noncomputable def PrimedColumnEquation447Branch.toOptimalCategoricalPathWitnessBranch
    {cWindow m : ℕ} {rho : ℝ}
    {branchEvent thetaPathEvent : Set Path}
    (B : PrimedColumnEquation447Branch cWindow m rho
      branchEvent thetaPathEvent)
    (growth : SourceWindowGrowth cWindow m) :
    PrimedColumnEquation447OptimalCategoricalPathWitnessBranch
      cWindow m (Real.exp (sourceAdjacentComparisonExponent cWindow)) rho
      branchEvent thetaPathEvent where
  source := B.source
  remaining := fun n ↦
    (B.remaining n).toOptimalCategoricalPathWitnessBranchRemainingData
      (B.source n).profile_lt growth
  cover := B.cover
  theta_subset := fun _ ↦ le_rfl
  pairwise_disjoint := B.pairwise_disjoint

/-- Forward column path-witness data with an explicit injective switch on
each count/history atom. -/
structure ForwardColumnEquation447InjectivePathWitnessBranch
    (cWindow m : ℕ) (c rho : ℝ)
    (branchEvent thetaTarget : Set Path) where
  source : ℕ → ForwardColumnWinnerSource m
  remaining : ∀ n,
    Equation447InjectivePathWitnessBranchRemainingData cWindow m c rho
      branchEvent (source n).pathAtom (source n).profile
        (source n).lazyVector (source n).nextDirection
  cover : branchEvent ⊆ ⋃ n, (source n).pathAtom
  theta_subset : ∀ n, (remaining n).thetaPathEvent ⊆ thetaTarget
  pairwise_disjoint : Pairwise fun n l ↦
    Disjoint (source n).pathAtom (source l).pathAtom

namespace ForwardColumnEquation447InjectivePathWitnessBranch

noncomputable def toPathWitnessBranch
    {cWindow m : ℕ} {c rho : ℝ}
    {branchEvent thetaTarget : Set Path}
    (B : ForwardColumnEquation447InjectivePathWitnessBranch
      cWindow m c rho branchEvent thetaTarget) :
    ForwardColumnEquation447PathWitnessBranch
      cWindow m c rho branchEvent thetaTarget where
  source := B.source
  remaining := fun n ↦ (B.remaining n).toRemainingData
  cover := B.cover
  theta_subset := B.theta_subset
  pairwise_disjoint := B.pairwise_disjoint

end ForwardColumnEquation447InjectivePathWitnessBranch

/-- Backward/primed column path-witness data with an explicit injective
switch on each count/history atom. -/
structure PrimedColumnEquation447InjectivePathWitnessBranch
    (cWindow m : ℕ) (c rho : ℝ)
    (branchEvent thetaTarget : Set Path) where
  source : ℕ → PrimedColumnWinnerSource m
  remaining : ∀ n,
    Equation447InjectivePathWitnessBranchRemainingData cWindow m c rho
      branchEvent (source n).pathAtom (source n).profile
        (source n).lazyVector (source n).nextDirection
  cover : branchEvent ⊆ ⋃ n, (source n).pathAtom
  theta_subset : ∀ n, (remaining n).thetaPathEvent ⊆ thetaTarget
  pairwise_disjoint : Pairwise fun n l ↦
    Disjoint (source n).pathAtom (source l).pathAtom

namespace PrimedColumnEquation447InjectivePathWitnessBranch

noncomputable def toPathWitnessBranch
    {cWindow m : ℕ} {c rho : ℝ}
    {branchEvent thetaTarget : Set Path}
    (B : PrimedColumnEquation447InjectivePathWitnessBranch
      cWindow m c rho branchEvent thetaTarget) :
    PrimedColumnEquation447PathWitnessBranch
      cWindow m c rho branchEvent thetaTarget where
  source := B.source
  remaining := fun n ↦ (B.remaining n).toRemainingData
  cover := B.cover
  theta_subset := B.theta_subset
  pairwise_disjoint := B.pairwise_disjoint

end PrimedColumnEquation447InjectivePathWitnessBranch

/-! ### The two literal `Y` branches and their reflected `Y'` transport -/

/-- The profile exception naturally transported with the stopped
Equation-(4.47) atoms.  It is the canonical temporal `Theta` event at the
four checkerboard pairings and at `Y`; at `Y'` it is the reflection of the
literal temporal `Y` exception.  No false set inclusion between the latter
and the unreflected temporal `Y'` exception is asserted. -/
def sourceEquation447ThetaTarget
    (m : ℕ) (i : Fin 6) (r : StageIndex) : Set Path :=
  if i = yIndex' then
    reflectPath ⁻¹' stoppedThetaEvent
      (sourceCanonicalProfiles yIndex) (canonicalCStar yIndex)
        m (stageNumber r)
  else
    stoppedThetaEvent (sourceCanonicalProfiles i) (canonicalCStar i)
      m (stageNumber r)

@[simp] theorem sourceEquation447ThetaTarget_y (m : ℕ) (r : StageIndex) :
    sourceEquation447ThetaTarget m yIndex r =
      stoppedThetaEvent (sourceCanonicalProfiles yIndex)
        (canonicalCStar yIndex) m (stageNumber r) := by
  simp [sourceEquation447ThetaTarget, yIndex, yIndex']

@[simp] theorem sourceEquation447ThetaTarget_yPrime
    (m : ℕ) (r : StageIndex) :
    sourceEquation447ThetaTarget m yIndex' r =
      reflectPath ⁻¹' stoppedThetaEvent
        (sourceCanonicalProfiles yIndex) (canonicalCStar yIndex)
          m (stageNumber r) := by
  simp [sourceEquation447ThetaTarget]

/-- Fixed-scale source data for the complete two-phase `Y` column branch.
The forward and backward phases remain separate branch-specific stopped
atomizations; only their union is required to cover the `Y` cardinality
failure.  Both phases use the canonical `rhoCoeff * log(m)^2` threshold;
there is no caller-chosen phase threshold or lower-bound premise. -/
structure YTwoPhaseEquation447SourceData
    (cWindow m : ℕ) (rhoCoeff : ℝ)
    (r : StageIndex) where
  forwardBranch : Set Path
  backwardBranch : Set Path
  forward : ForwardColumnEquation447Branch cWindow m
      (rhoCoeff * Real.log (m : ℝ) ^ 2)
      forwardBranch
      (stoppedThetaEvent (sourceCanonicalProfiles yIndex)
        (canonicalCStar yIndex) m (stageNumber r))
  backward : PrimedColumnEquation447Branch cWindow m
      (rhoCoeff * Real.log (m : ℝ) ^ 2)
      backwardBranch
      (stoppedThetaEvent (sourceCanonicalProfiles yIndex)
        (canonicalCStar yIndex) m (stageNumber r))
  failure_cover : lemma411412CardinalityFailureEvent m yIndex r ⊆
    forwardBranch ∪ backwardBranch

/-- Source-facing two-phase `Y` data on the canonical winner events.
Neither the phase sets nor their union cover are caller-supplied. -/
structure YCanonicalTwoPhaseEquation447SourceData
    (cWindow m : ℕ) (r : StageIndex) where
  forward : ForwardColumnEquation447Branch cWindow m
      ((1 / 4 : ℝ) * Real.log (m : ℝ) ^ 2)
      (yEquation447ForwardBranch m r)
      (stoppedThetaEvent (sourceCanonicalProfiles yIndex)
        (canonicalCStar yIndex) m (stageNumber r))
  backward : PrimedColumnEquation447Branch cWindow m
      ((1 / 4 : ℝ) * Real.log (m : ℝ) ^ 2)
      (yEquation447BackwardBranch m r)
      (stoppedThetaEvent (sourceCanonicalProfiles yIndex)
        (canonicalCStar yIndex) m (stageNumber r))

namespace YCanonicalTwoPhaseEquation447SourceData

variable {cWindow m : ℕ} {r : StageIndex}

/-- Forget the checked canonical phase choice to enter the flexible
two-event transport record. -/
noncomputable def toTwoPhaseSourceData
    (D : YCanonicalTwoPhaseEquation447SourceData cWindow m r) :
    YTwoPhaseEquation447SourceData cWindow m (1 / 4 : ℝ) r where
  forwardBranch := yEquation447ForwardBranch m r
  backwardBranch := yEquation447BackwardBranch m r
  forward := D.forward
  backward := D.backward
  failure_cover :=
    lemma411412CardinalityFailureEvent_y_subset_canonicalBranches m r

end YCanonicalTwoPhaseEquation447SourceData

namespace YTwoPhaseEquation447SourceData

variable {cWindow m : ℕ} {rhoCoeff : ℝ}
    {r : StageIndex}
    (D : YTwoPhaseEquation447SourceData
      cWindow m rhoCoeff r)

def branchEvent : Fin 2 → Set Path := ![
  D.forwardBranch,
  D.backwardBranch]

noncomputable def rho
    (_D : YTwoPhaseEquation447SourceData cWindow m rhoCoeff r) : Fin 2 → ℝ :=
  fun _ ↦ rhoCoeff * Real.log (m : ℝ) ^ 2

noncomputable def atoms (growth : SourceWindowGrowth cWindow m)
    (j : Fin 2) (eta : ℕ) :
    StoppedEquation447BranchAtom cWindow m
      (Real.exp (sourceAdjacentComparisonExponent cWindow))
      (D.branchEvent j) (D.rho j) := by
  by_cases h0 : j = 0
  · subst j
    exact D.forward.atom growth eta
  · have h1 : j = 1 := Fin.ext (by omega)
    subst j
    exact D.backward.atom growth eta

theorem failure_subset_iUnion_branchEvent :
    lemma411412CardinalityFailureEvent m yIndex r ⊆
      ⋃ j, D.branchEvent j := by
  intro s hs
  rcases D.failure_cover hs with hs | hs
  · exact Set.mem_iUnion.mpr ⟨0, hs⟩
  · exact Set.mem_iUnion.mpr ⟨1, hs⟩

theorem branch_threshold (j : Fin 2) :
    rhoCoeff * Real.log (m : ℝ) ^ 2 ≤ D.rho j := by
  simp [rho]

theorem branchEvent_subset_iUnion_atoms
    (growth : SourceWindowGrowth cWindow m) (j : Fin 2) :
    D.branchEvent j ⊆ ⋃ eta, (D.atoms growth j eta).pathAtom := by
  fin_cases j
  · simpa [branchEvent, atoms] using D.forward.cover_atoms growth
  · simpa [branchEvent, atoms] using D.backward.cover_atoms growth

theorem atoms_pairwise_disjoint (growth : SourceWindowGrowth cWindow m)
    (j : Fin 2) :
    Pairwise fun eta zeta ↦
      Disjoint (D.atoms growth j eta).pathAtom
        (D.atoms growth j zeta).pathAtom := by
  fin_cases j
  · simpa [atoms] using D.forward.pairwise_disjoint_atoms growth
  · simpa [atoms] using D.backward.pairwise_disjoint_atoms growth

theorem atom_theta_subset (growth : SourceWindowGrowth cWindow m)
    (j : Fin 2) (eta : ℕ) :
    (D.atoms growth j eta).thetaPathEvent ⊆
      stoppedThetaEvent (sourceCanonicalProfiles yIndex)
        (canonicalCStar yIndex) m (stageNumber r) := by
  fin_cases j
  · exact le_rfl
  · exact le_rfl

theorem reflected_atom_theta_subset_aux
    (growth : SourceWindowGrowth cWindow m) (j : Fin 2) (eta : ℕ) :
    reflectPath ⁻¹' (D.atoms growth j eta).thetaPathEvent ⊆
      sourceEquation447ThetaTarget m yIndex' r := by
  rw [sourceEquation447ThetaTarget_yPrime]
  fin_cases j
  · exact Set.preimage_mono le_rfl
  · exact Set.preimage_mono le_rfl

include D in
/-- The exact finite-branch existential required at the `Y` pairing. -/
theorem finiteBranchWitness (growth : SourceWindowGrowth cWindow m) :
    ∃ branchFailure : Fin 2 → Set Path,
      ∃ rho : Fin 2 → ℝ,
      ∃ atoms : (j : Fin 2) → ℕ →
          StoppedEquation447BranchAtom cWindow m
            (Real.exp (sourceAdjacentComparisonExponent cWindow))
            (branchFailure j) (rho j),
        lemma411412CardinalityFailureEvent m yIndex r ⊆
            ⋃ j, branchFailure j ∧
        (∀ j, rhoCoeff * Real.log (m : ℝ) ^ 2 ≤ rho j) ∧
        (∀ j, branchFailure j ⊆ ⋃ eta, (atoms j eta).pathAtom) ∧
        (∀ j eta, (atoms j eta).thetaPathEvent ⊆
          stoppedThetaEvent (sourceCanonicalProfiles yIndex)
            (canonicalCStar yIndex) m (stageNumber r)) ∧
        ∀ j, Pairwise fun eta zeta ↦
          Disjoint (atoms j eta).pathAtom (atoms j zeta).pathAtom := by
  exact ⟨branchEvent D, rho D, atoms D growth,
    failure_subset_iUnion_branchEvent D, branch_threshold D,
    branchEvent_subset_iUnion_atoms D growth, atom_theta_subset D growth,
    atoms_pairwise_disjoint D growth⟩

end YTwoPhaseEquation447SourceData

/-- Eventual two-phase stopped source data for the unreflected `Y` pairing. -/
def Prop47Lemma411412YTwoPhaseSourceInputs
    (cWindow : ℕ) (rhoCoeff : ℝ) : Prop :=
  ∀ᶠ m : ℕ in Filter.atTop, ∀ r : StageIndex,
    Nonempty (YTwoPhaseEquation447SourceData
      cWindow m rhoCoeff r)

/-- Eventual literal column data after fixing both phase events
canonically. -/
def Prop47Lemma411412YCanonicalTwoPhaseSourceInputs
    (cWindow : ℕ) : Prop :=
  ∀ᶠ m : ℕ in Filter.atTop, ∀ r : StageIndex,
    Nonempty (YCanonicalTwoPhaseEquation447SourceData cWindow m r)

theorem yTwoPhaseSourceInputs_of_canonical
    (cWindow : ℕ)
    (h : Prop47Lemma411412YCanonicalTwoPhaseSourceInputs cWindow) :
    Prop47Lemma411412YTwoPhaseSourceInputs cWindow (1 / 4 : ℝ) := by
  filter_upwards [h] with m hm
  intro r
  rcases hm r with ⟨D⟩
  exact ⟨D.toTwoPhaseSourceData⟩

theorem finiteBranchStoppedProfileInputsAt_y_of_source
    (cWindow : ℕ) (rhoCoeff : ℝ)
    (h : Prop47Lemma411412YTwoPhaseSourceInputs
      cWindow rhoCoeff) :
    Prop47Lemma411412FiniteBranchStoppedProfileInputsAt
      yIndex 2 cWindow
        (Real.exp (sourceAdjacentComparisonExponent cWindow)) rhoCoeff := by
  filter_upwards [h, eventually_sourceWindowGrowth cWindow] with m hm growth
  intro r
  rcases hm r with ⟨D⟩
  exact YTwoPhaseEquation447SourceData.finiteBranchWitness D growth

/-! ### Source-faithful deleted-path witnesses for `Y` and `Y'` -/

/-- The two canonical column phases with the literal changed-path witness
from (4.47)--(4.54). -/
structure YCanonicalTwoPhaseEquation447PathWitnessSourceData
    (cWindow m : ℕ) (c : ℝ) (r : StageIndex) where
  forward : ForwardColumnEquation447PathWitnessBranch cWindow m c
    ((1 / 4 : ℝ) * Real.log (m : ℝ) ^ 2)
    (yEquation447ForwardBranch m r)
    (stoppedThetaEvent (sourceCanonicalProfiles yIndex)
      (canonicalCStar yIndex) m (stageNumber r))
  backward : PrimedColumnEquation447PathWitnessBranch cWindow m c
    ((1 / 4 : ℝ) * Real.log (m : ℝ) ^ 2)
    (yEquation447BackwardBranch m r)
    (stoppedThetaEvent (sourceCanonicalProfiles yIndex)
      (canonicalCStar yIndex) m (stageNumber r))

namespace YCanonicalTwoPhaseEquation447PathWitnessSourceData

variable {cWindow m : ℕ} {c : ℝ} {r : StageIndex}
    (D : YCanonicalTwoPhaseEquation447PathWitnessSourceData
      cWindow m c r)

def branchEvent
    (_D : YCanonicalTwoPhaseEquation447PathWitnessSourceData
      cWindow m c r) : Fin 2 → Set Path := fun j ↦
  match j.1 with
  | 0 => yEquation447ForwardBranch m r
  | _ => yEquation447BackwardBranch m r

noncomputable def rho
    (_D : YCanonicalTwoPhaseEquation447PathWitnessSourceData
      cWindow m c r) : Fin 2 → ℝ :=
  fun _ ↦ (1 / 4 : ℝ) * Real.log (m : ℝ) ^ 2

noncomputable def atoms (j : Fin 2) (eta : ℕ) :
    StoppedEquation447PathWitnessBranchAtom cWindow m c
      (D.branchEvent j) (D.rho j) := by
  by_cases h0 : j = 0
  · subst j
    exact D.forward.atom eta
  · have h1 : j = 1 := Fin.ext (by omega)
    subst j
    exact D.backward.atom eta

@[simp] theorem atoms_zero_pathAtom (eta : ℕ) :
    (D.atoms (0 : Fin 2) eta).pathAtom =
      (D.forward.source eta).pathAtom := by
  rfl

@[simp] theorem atoms_one_pathAtom (eta : ℕ) :
    (D.atoms (1 : Fin 2) eta).pathAtom =
      (D.backward.source eta).pathAtom := by
  rfl

@[simp] theorem atoms_zero_thetaPathEvent (eta : ℕ) :
    (D.atoms (0 : Fin 2) eta).thetaPathEvent =
      (D.forward.remaining eta).thetaPathEvent := by
  rfl

@[simp] theorem atoms_one_thetaPathEvent (eta : ℕ) :
    (D.atoms (1 : Fin 2) eta).thetaPathEvent =
      (D.backward.remaining eta).thetaPathEvent := by
  rfl

theorem finiteBranchWitness
    (D : YCanonicalTwoPhaseEquation447PathWitnessSourceData
      cWindow m c r) :
    ∃ branchFailure : Fin 2 → Set Path,
      ∃ rho : Fin 2 → ℝ,
      ∃ atoms : (j : Fin 2) → ℕ →
          StoppedEquation447PathWitnessBranchAtom cWindow m c
            (branchFailure j) (rho j),
        lemma411412CardinalityFailureEvent m yIndex r ⊆
            ⋃ j, branchFailure j ∧
        (∀ j, (1 / 4 : ℝ) * Real.log (m : ℝ) ^ 2 ≤ rho j) ∧
        (∀ j, branchFailure j ⊆ ⋃ eta, (atoms j eta).pathAtom) ∧
        (∀ j eta, (atoms j eta).thetaPathEvent ⊆
          stoppedThetaEvent (sourceCanonicalProfiles yIndex)
            (canonicalCStar yIndex) m (stageNumber r)) ∧
        ∀ j, Pairwise fun eta zeta ↦
          Disjoint (atoms j eta).pathAtom (atoms j zeta).pathAtom := by
  refine ⟨D.branchEvent, D.rho, D.atoms, ?_, ?_, ?_, ?_, ?_⟩
  · intro s hs
    rcases lemma411412CardinalityFailureEvent_y_subset_canonicalBranches
        m r hs with h | h
    · exact Set.mem_iUnion.mpr ⟨0, h⟩
    · exact Set.mem_iUnion.mpr ⟨1, h⟩
  · intro j
    simp [rho]
  · intro j
    fin_cases j
    · simpa [branchEvent] using D.forward.cover_atoms
    · simpa [branchEvent] using D.backward.cover_atoms
  · intro j eta
    fin_cases j
    · simpa using D.forward.theta_subset eta
    · simpa using D.backward.theta_subset eta
  · intro j
    fin_cases j
    · simpa using D.forward.pairwise_disjoint_atoms
    · simpa using D.backward.pairwise_disjoint_atoms

end YCanonicalTwoPhaseEquation447PathWitnessSourceData

/-- The two canonical column phases with the fixed-cardinality switch
expressed by conditional categorical products and the source's binomial
layer estimate. -/
structure YCanonicalTwoPhaseEquation447CategoricalPathWitnessSourceData
    (cWindow m : ℕ) (c : ℝ) (r : StageIndex) where
  forward : ForwardColumnEquation447CategoricalPathWitnessBranch cWindow m c
    ((1 / 4 : ℝ) * Real.log (m : ℝ) ^ 2)
    (yEquation447ForwardBranch m r)
    (stoppedThetaEvent (sourceCanonicalProfiles yIndex)
      (canonicalCStar yIndex) m (stageNumber r))
  backward : PrimedColumnEquation447CategoricalPathWitnessBranch cWindow m c
    ((1 / 4 : ℝ) * Real.log (m : ℝ) ^ 2)
    (yEquation447BackwardBranch m r)
    (stoppedThetaEvent (sourceCanonicalProfiles yIndex)
      (canonicalCStar yIndex) m (stageNumber r))

namespace YCanonicalTwoPhaseEquation447CategoricalPathWitnessSourceData

variable {cWindow m : ℕ} {c : ℝ} {r : StageIndex}

noncomputable def toPathWitnessSourceData
    (D : YCanonicalTwoPhaseEquation447CategoricalPathWitnessSourceData
      cWindow m c r) :
    YCanonicalTwoPhaseEquation447PathWitnessSourceData cWindow m c r where
  forward := D.forward.toPathWitnessBranch
  backward := D.backward.toPathWitnessBranch

end YCanonicalTwoPhaseEquation447CategoricalPathWitnessSourceData

/-- The two canonical column phases after the binomial-layer inequality has
been internalized.  The source retains only a positive common coordinate
ratio together with its categorical history/witness data. -/
structure YCanonicalTwoPhaseEquation447OptimalCategoricalPathWitnessSourceData
    (cWindow m : ℕ) (ratioC : ℝ) (r : StageIndex) where
  forward : ForwardColumnEquation447OptimalCategoricalPathWitnessBranch
    cWindow m ratioC
    ((1 / 4 : ℝ) * Real.log (m : ℝ) ^ 2)
    (yEquation447ForwardBranch m r)
    (stoppedThetaEvent (sourceCanonicalProfiles yIndex)
      (canonicalCStar yIndex) m (stageNumber r))
  backward : PrimedColumnEquation447OptimalCategoricalPathWitnessBranch
    cWindow m ratioC
    ((1 / 4 : ℝ) * Real.log (m : ℝ) ^ 2)
    (yEquation447BackwardBranch m r)
    (stoppedThetaEvent (sourceCanonicalProfiles yIndex)
      (canonicalCStar yIndex) m (stageNumber r))

/-- The two column phases with Equation-(4.54) represented by stopped-path
length and level-count separation, rather than by an assumed set-level
disjointness statement. -/
structure YCanonicalTwoPhaseEquation447LengthSeparatedOptimalCategoricalPathWitnessSourceData
    (cWindow m : ℕ) (ratioC : ℝ) (r : StageIndex) where
  forward :
    ForwardColumnEquation447LengthSeparatedOptimalCategoricalPathWitnessBranch
      cWindow m ratioC
      ((1 / 4 : ℝ) * Real.log (m : ℝ) ^ 2)
      (yEquation447ForwardBranch m r)
      (stoppedThetaEvent (sourceCanonicalProfiles yIndex)
        (canonicalCStar yIndex) m (stageNumber r))
  backward :
    PrimedColumnEquation447LengthSeparatedOptimalCategoricalPathWitnessBranch
      cWindow m ratioC
      ((1 / 4 : ℝ) * Real.log (m : ℝ) ^ 2)
      (yEquation447BackwardBranch m r)
      (stoppedThetaEvent (sourceCanonicalProfiles yIndex)
        (canonicalCStar yIndex) m (stageNumber r))

namespace YCanonicalTwoPhaseEquation447LengthSeparatedOptimalCategoricalPathWitnessSourceData

variable {cWindow m : ℕ} {ratioC : ℝ} {r : StageIndex}

noncomputable def toOptimalCategoricalPathWitnessSourceData
    (D :
      YCanonicalTwoPhaseEquation447LengthSeparatedOptimalCategoricalPathWitnessSourceData
        cWindow m ratioC r) :
    YCanonicalTwoPhaseEquation447OptimalCategoricalPathWitnessSourceData
      cWindow m ratioC r where
  forward := D.forward.toOptimalCategoricalPathWitnessBranch
  backward := D.backward.toOptimalCategoricalPathWitnessBranch

end YCanonicalTwoPhaseEquation447LengthSeparatedOptimalCategoricalPathWitnessSourceData

/-- Canonical two-phase column input in the strict rectangular form. -/
structure YCanonicalTwoPhaseEquation447LengthSeparatedRectangularOptimalCategoricalPathWitnessSourceData
    (cWindow m : ℕ) (ratioC : ℝ) (r : StageIndex) where
  forward :
    ForwardColumnEquation447LengthSeparatedRectangularOptimalCategoricalPathWitnessBranch
      cWindow m ratioC
      ((1 / 4 : ℝ) * Real.log (m : ℝ) ^ 2)
      (yEquation447ForwardBranch m r)
      (stoppedThetaEvent (sourceCanonicalProfiles yIndex)
        (canonicalCStar yIndex) m (stageNumber r))
  backward :
    PrimedColumnEquation447LengthSeparatedRectangularOptimalCategoricalPathWitnessBranch
      cWindow m ratioC
      ((1 / 4 : ℝ) * Real.log (m : ℝ) ^ 2)
      (yEquation447BackwardBranch m r)
      (stoppedThetaEvent (sourceCanonicalProfiles yIndex)
        (canonicalCStar yIndex) m (stageNumber r))

namespace YCanonicalTwoPhaseEquation447LengthSeparatedRectangularOptimalCategoricalPathWitnessSourceData

variable {cWindow m : ℕ} {ratioC : ℝ} {r : StageIndex}

noncomputable def toLengthSeparatedOptimalCategoricalPathWitnessSourceData
    (D :
      YCanonicalTwoPhaseEquation447LengthSeparatedRectangularOptimalCategoricalPathWitnessSourceData
        cWindow m ratioC r) :
    YCanonicalTwoPhaseEquation447LengthSeparatedOptimalCategoricalPathWitnessSourceData
      cWindow m ratioC r where
  forward := D.forward.toLengthSeparatedOptimalCategoricalPathWitnessBranch
  backward := D.backward.toLengthSeparatedOptimalCategoricalPathWitnessBranch

end YCanonicalTwoPhaseEquation447LengthSeparatedRectangularOptimalCategoricalPathWitnessSourceData

/-- The two literal source-band column phases already determine their
canonical optimal categorical witness layers. -/
noncomputable def YCanonicalTwoPhaseEquation447SourceData.toOptimalCategoricalPathWitnessSourceData
    {cWindow m : ℕ} {r : StageIndex}
    (D : YCanonicalTwoPhaseEquation447SourceData cWindow m r)
    (growth : SourceWindowGrowth cWindow m) :
    YCanonicalTwoPhaseEquation447OptimalCategoricalPathWitnessSourceData
      cWindow m (Real.exp (sourceAdjacentComparisonExponent cWindow)) r where
  forward := D.forward.toOptimalCategoricalPathWitnessBranch growth
  backward := D.backward.toOptimalCategoricalPathWitnessBranch growth

namespace YCanonicalTwoPhaseEquation447OptimalCategoricalPathWitnessSourceData

variable {cWindow m : ℕ} {ratioC : ℝ} {r : StageIndex}

noncomputable def toPathWitnessSourceData
    (D : YCanonicalTwoPhaseEquation447OptimalCategoricalPathWitnessSourceData
      cWindow m ratioC r)
    (hC : 0 < ratioC)
    (hbinomial : ∀ q,
      Nat.ceil ((1 / 4 : ℝ) * Real.log (m : ℝ) ^ 2) ≤ q →
      ratioC ^ categoricalOptimalWitnessCount ratioC q ≤
        Real.exp (-categoricalOptimalRate ratioC * (q : ℝ)) *
          Nat.choose q (categoricalOptimalWitnessCount ratioC q)) :
    YCanonicalTwoPhaseEquation447PathWitnessSourceData
      cWindow m (categoricalOptimalRate ratioC) r where
  forward := D.forward.toPathWitnessBranch hC hbinomial
  backward := D.backward.toPathWitnessBranch hC hbinomial

end YCanonicalTwoPhaseEquation447OptimalCategoricalPathWitnessSourceData

/-- The two canonical column phases with explicit injective changed-path
maps and pointwise likelihood comparisons. -/
structure YCanonicalTwoPhaseEquation447InjectivePathWitnessSourceData
    (cWindow m : ℕ) (c : ℝ) (r : StageIndex) where
  forward : ForwardColumnEquation447InjectivePathWitnessBranch cWindow m c
    ((1 / 4 : ℝ) * Real.log (m : ℝ) ^ 2)
    (yEquation447ForwardBranch m r)
    (stoppedThetaEvent (sourceCanonicalProfiles yIndex)
      (canonicalCStar yIndex) m (stageNumber r))
  backward : PrimedColumnEquation447InjectivePathWitnessBranch cWindow m c
    ((1 / 4 : ℝ) * Real.log (m : ℝ) ^ 2)
    (yEquation447BackwardBranch m r)
    (stoppedThetaEvent (sourceCanonicalProfiles yIndex)
      (canonicalCStar yIndex) m (stageNumber r))

namespace YCanonicalTwoPhaseEquation447InjectivePathWitnessSourceData

variable {cWindow m : ℕ} {c : ℝ} {r : StageIndex}

noncomputable def toPathWitnessSourceData
    (D : YCanonicalTwoPhaseEquation447InjectivePathWitnessSourceData
      cWindow m c r) :
    YCanonicalTwoPhaseEquation447PathWitnessSourceData cWindow m c r where
  forward := D.forward.toPathWitnessBranch
  backward := D.backward.toPathWitnessBranch

end YCanonicalTwoPhaseEquation447InjectivePathWitnessSourceData

def Prop47Lemma411412YCanonicalTwoPhasePathWitnessSourceInputs
    (cWindow : ℕ) (c : ℝ) : Prop :=
  ∀ᶠ m : ℕ in Filter.atTop, ∀ r : StageIndex,
    Nonempty (YCanonicalTwoPhaseEquation447PathWitnessSourceData
      cWindow m c r)

def Prop47Lemma411412YCanonicalTwoPhaseCategoricalPathWitnessSourceInputs
    (cWindow : ℕ) (c : ℝ) : Prop :=
  ∀ᶠ m : ℕ in Filter.atTop, ∀ r : StageIndex,
    Nonempty (YCanonicalTwoPhaseEquation447CategoricalPathWitnessSourceData
      cWindow m c r)

def Prop47Lemma411412YCanonicalTwoPhaseOptimalCategoricalPathWitnessSourceInputs
    (cWindow : ℕ) (ratioC : ℝ) : Prop :=
  ∀ᶠ m : ℕ in Filter.atTop, ∀ r : StageIndex,
    Nonempty (YCanonicalTwoPhaseEquation447OptimalCategoricalPathWitnessSourceData
      cWindow m ratioC r)

def Prop47Lemma411412YCanonicalTwoPhaseLengthSeparatedOptimalCategoricalPathWitnessSourceInputs
    (cWindow : ℕ) (ratioC : ℝ) : Prop :=
  ∀ᶠ m : ℕ in Filter.atTop, ∀ r : StageIndex,
    Nonempty
      (YCanonicalTwoPhaseEquation447LengthSeparatedOptimalCategoricalPathWitnessSourceData
        cWindow m ratioC r)

def Prop47Lemma411412YCanonicalTwoPhaseLengthSeparatedRectangularOptimalCategoricalPathWitnessSourceInputs
    (cWindow : ℕ) (ratioC : ℝ) : Prop :=
  ∀ᶠ m : ℕ in Filter.atTop, ∀ r : StageIndex,
    Nonempty
      (YCanonicalTwoPhaseEquation447LengthSeparatedRectangularOptimalCategoricalPathWitnessSourceData
        cWindow m ratioC r)

/-- Rectangular column histories derive the two product identities before
entering the stopped-length source connector. -/
theorem yLengthSeparatedOptimalCategoricalPathWitnessSourceInputs_of_rectangular
    (cWindow : ℕ) (ratioC : ℝ)
    (h :
      Prop47Lemma411412YCanonicalTwoPhaseLengthSeparatedRectangularOptimalCategoricalPathWitnessSourceInputs
        cWindow ratioC) :
    Prop47Lemma411412YCanonicalTwoPhaseLengthSeparatedOptimalCategoricalPathWitnessSourceInputs
      cWindow ratioC := by
  filter_upwards [h] with m hm
  intro r
  rcases hm r with ⟨D⟩
  exact ⟨D.toLengthSeparatedOptimalCategoricalPathWitnessSourceData⟩

/-- The stopped-length column package derives Equation-(4.54), and hence the
existing optimal categorical input, internally. -/
theorem yOptimalCategoricalPathWitnessSourceInputs_of_lengthSeparated
    (cWindow : ℕ) (ratioC : ℝ)
    (h :
      Prop47Lemma411412YCanonicalTwoPhaseLengthSeparatedOptimalCategoricalPathWitnessSourceInputs
        cWindow ratioC) :
    Prop47Lemma411412YCanonicalTwoPhaseOptimalCategoricalPathWitnessSourceInputs
      cWindow ratioC := by
  filter_upwards [h] with m hm
  intro r
  rcases hm r with ⟨D⟩
  exact ⟨D.toOptimalCategoricalPathWitnessSourceData⟩

/-- The existing canonical column source input supplies the optimal witness
package internally. -/
theorem yOptimalCategoricalPathWitnessSourceInputs_of_sourceBand
    (cWindow : ℕ)
    (h : Prop47Lemma411412YCanonicalTwoPhaseSourceInputs cWindow) :
    Prop47Lemma411412YCanonicalTwoPhaseOptimalCategoricalPathWitnessSourceInputs
      cWindow (Real.exp (sourceAdjacentComparisonExponent cWindow)) := by
  filter_upwards [h, eventually_sourceWindowGrowth cWindow] with m hm growth
  intro r
  rcases hm r with ⟨D⟩
  exact ⟨D.toOptimalCategoricalPathWitnessSourceData growth⟩

def Prop47Lemma411412YCanonicalTwoPhaseInjectivePathWitnessSourceInputs
    (cWindow : ℕ) (c : ℝ) : Prop :=
  ∀ᶠ m : ℕ in Filter.atTop, ∀ r : StageIndex,
    Nonempty (YCanonicalTwoPhaseEquation447InjectivePathWitnessSourceData
      cWindow m c r)

theorem yPathWitnessSourceInputs_of_injective
    (cWindow : ℕ) (c : ℝ)
    (h :
      Prop47Lemma411412YCanonicalTwoPhaseInjectivePathWitnessSourceInputs
        cWindow c) :
    Prop47Lemma411412YCanonicalTwoPhasePathWitnessSourceInputs
      cWindow c := by
  filter_upwards [h] with m hm
  intro r
  rcases hm r with ⟨D⟩
  exact ⟨D.toPathWitnessSourceData⟩

theorem yPathWitnessSourceInputs_of_categorical
    (cWindow : ℕ) (c : ℝ)
    (h :
      Prop47Lemma411412YCanonicalTwoPhaseCategoricalPathWitnessSourceInputs
        cWindow c) :
    Prop47Lemma411412YCanonicalTwoPhasePathWitnessSourceInputs
      cWindow c := by
  filter_upwards [h] with m hm
  intro r
  rcases hm r with ⟨D⟩
  exact ⟨D.toPathWitnessSourceData⟩

/-- The maximal weighted binomial layer supplies the common column
path-switch rate uniformly above the quarter-log-square threshold. -/
theorem yPathWitnessSourceInputs_of_optimalCategorical
    (cWindow : ℕ) (ratioC : ℝ) (hC : 0 < ratioC)
    (h :
      Prop47Lemma411412YCanonicalTwoPhaseOptimalCategoricalPathWitnessSourceInputs
        cWindow ratioC) :
    Prop47Lemma411412YCanonicalTwoPhasePathWitnessSourceInputs
      cWindow (categoricalOptimalRate ratioC) := by
  have hbin := eventually_optimal_binomial_layer_above_quarter_log_sq ratioC hC
  filter_upwards [h, hbin] with m hm hbm
  intro r
  rcases hm r with ⟨D⟩
  exact ⟨D.toPathWitnessSourceData hC hbm⟩

theorem finiteBranchPathWitnessInputsAt_y_of_source
    (cWindow : ℕ) (c : ℝ)
    (h : Prop47Lemma411412YCanonicalTwoPhasePathWitnessSourceInputs
      cWindow c) :
    Prop47Lemma411412FiniteBranchPathWitnessInputsAt
      yIndex 2 cWindow c (1 / 4 : ℝ) := by
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

/-- Reflection transports the reunited two-phase deleted-path witness to
`Y'`, retaining the reflected temporal exception as an auxiliary target. -/
theorem finiteBranchPathWitnessAuxThetaInputsAt_yPrime_of_source
    (cWindow : ℕ) (c : ℝ)
    (h : Prop47Lemma411412YCanonicalTwoPhasePathWitnessSourceInputs
      cWindow c) :
    Prop47Lemma411412FiniteBranchPathWitnessAuxThetaInputsAt
      sourceEquation447ThetaTarget yIndex' 2 cWindow c (1 / 4 : ℝ) := by
  filter_upwards [h] with m hm
  intro r
  rcases hm r with ⟨D⟩
  rcases D.finiteBranchWitness with
    ⟨branchFailure, rho, atoms, hcover, hthreshold, hatomCover, htheta,
      hdisjoint⟩
  let reflectedFailure : Fin 2 → Set Path :=
    fun j ↦ reflectPath ⁻¹' branchFailure j
  let reflectedAtoms : (j : Fin 2) → ℕ →
      StoppedEquation447PathWitnessBranchAtom cWindow m c
        (reflectedFailure j) (rho j) :=
    fun j eta ↦ reflectStoppedEquation447PathWitnessBranchAtom
      (atoms j eta)
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
    rcases Set.mem_iUnion.mp (hatomCover j hs.1) with ⟨eta, heta⟩
    exact Set.mem_iUnion.mpr ⟨eta, heta⟩
  · intro j eta
    rw [sourceEquation447ThetaTarget_yPrime]
    exact Set.preimage_mono (htheta j eta)
  · intro j eta zeta hne
    rw [Set.disjoint_left]
    intro s hsEta hsZeta
    exact Set.disjoint_left.1 (hdisjoint j hne) hsEta hsZeta

/-- Reflection transports the complete two-phase atomization to `Y'`.  Its
profile exception is the reflected temporal `Y` exception, recorded by the
flexible auxiliary-theta interface rather than forced into the unrelated
unreflected temporal `Y'` event. -/
theorem finiteBranchAuxThetaInputsAt_yPrime_of_source
    (cWindow : ℕ) (rhoCoeff : ℝ)
    (h : Prop47Lemma411412YTwoPhaseSourceInputs
      cWindow rhoCoeff) :
    Prop47Lemma411412FiniteBranchAuxThetaInputsAt
      sourceEquation447ThetaTarget yIndex' 2 cWindow
        (Real.exp (sourceAdjacentComparisonExponent cWindow)) rhoCoeff := by
  filter_upwards [h, eventually_sourceWindowGrowth cWindow] with m hm growth
  intro r
  rcases hm r with ⟨D⟩
  let reflectedFailure : Fin 2 → Set Path :=
    fun j ↦ reflectPath ⁻¹' D.branchEvent j
  let reflectedAtoms : (j : Fin 2) → ℕ →
      StoppedEquation447BranchAtom cWindow m
        (Real.exp (sourceAdjacentComparisonExponent cWindow))
        (reflectedFailure j) (D.rho j) :=
    fun j eta ↦ reflectStoppedEquation447BranchAtom (D.atoms growth j eta)
  refine ⟨reflectedFailure, D.rho, reflectedAtoms, ?_, D.branch_threshold,
    ?_, ?_, ?_⟩
  · intro s hs
    have hsource : reflectPath s ∈
        lemma411412CardinalityFailureEvent m yIndex r := by
      change s ∈ reflectPath ⁻¹'
        lemma411412CardinalityFailureEvent m yIndex r
      rw [lemma411412CardinalityFailureEvent_yPrime_preimage]
      exact hs
    rcases Set.mem_iUnion.mp
        (D.failure_subset_iUnion_branchEvent hsource) with ⟨j, hj⟩
    exact Set.mem_iUnion.mpr ⟨j, hj⟩
  · intro j s hs
    rcases Set.mem_iUnion.mp
        (D.branchEvent_subset_iUnion_atoms growth j hs) with ⟨eta, heta⟩
    exact Set.mem_iUnion.mpr ⟨eta, heta⟩
  · intro j eta
    exact D.reflected_atom_theta_subset_aux growth j eta
  · intro j eta zeta hne
    rw [Set.disjoint_left]
    intro s hsEta hsZeta
    exact Set.disjoint_left.1 (D.atoms_pairwise_disjoint growth j hne)
      hsEta hsZeta

theorem hlozDirectAvoidanceEvent_reflect_iff_eq447
    (s : Path) (m j : ℕ) :
    s ∈ hlozDirectAvoidanceEvent m j ↔
      reflectPath s ∈ hlozDirectAvoidanceEvent m j := by
  simp only [hlozDirectAvoidanceEvent, Set.mem_ofPred_eq,
    firstKSitesReachLevel_reflectPath, levelCreationSite_reflectPath,
    reflectPath]
  constructor
  · intro h n hn hn' i hi hi' hEq
    exact h n hn hn' i hi hi' (reflectSite_injective hEq)
  · intro h n hn hn' i hi hi' hEq
    exact h n hn hn' i hi hi' (congrArg reflectSite hEq)

theorem siteDistance_reflectSite_eq447 (x y : Site) :
    siteDistance (reflectSite x) (reflectSite y) = siteDistance x y := by
  have hsquared :
      siteSquaredDistance (reflectSite x) (reflectSite y) =
        siteSquaredDistance x y := by
    rcases x with ⟨x₁, x₂⟩
    rcases y with ⟨y₁, y₂⟩
    simp only [siteSquaredDistance, reflectSite]
    rw [show -x₁ - -y₁ = -(x₁ - y₁) by ring, Int.natAbs_neg]
  unfold siteDistance
  rw [hsquared]

theorem distanceBinEvent_reflect_iff_eq447
    (s : Path) (m k : ℕ) (alpha : ℝ) :
    s ∈ distanceBinEvent m k alpha ↔
      reflectPath s ∈ distanceBinEvent m k alpha := by
  simp only [distanceBinEvent, Set.mem_ofPred_eq,
    firstKSitesReachLevel_reflectPath, levelCreationSite_reflectPath,
    siteDistance_reflectSite_eq447]

/-- At `Y'`, the auxiliary stopped-atom exception is exactly the reflection
preimage of the literal temporal `Y` Proposition-4.5 event, including its
prefix, avoidance, and distance-bin factors. -/
theorem lemma411412AuxThetaEvent_yPrime_eq_preimage_prop45_y
    (m : ℕ) (r : StageIndex) (alpha : ℝ) :
    lemma411412AuxThetaEvent sourceEquation447ThetaTarget
        m yIndex' r alpha =
      reflectPath ⁻¹' prop45FailureEvent
        sourceCanonicalProfiles canonicalCStar m yIndex r alpha := by
  ext s
  simp only [lemma411412AuxThetaEvent, sourceEquation447ThetaTarget_yPrime,
    prop45FailureEvent, Set.mem_inter_iff, Set.mem_preimage]
  constructor
  · rintro ⟨⟨⟨hprefix, havoid⟩, hdist⟩, htheta⟩
    refine ⟨⟨⟨?_, ?_⟩, ?_⟩, htheta⟩
    · have hleft : reflectPath (reflectPath s) ∈
          prefixPairingEvent m yIndex' (stageNumber r + 1) := by
        simpa using hprefix
      exact (prefixPairingEvent_y_reflect_iff
        (reflectPath s) m (stageNumber r + 1)).mp hleft
    · exact (hlozDirectAvoidanceEvent_reflect_iff_eq447 s m _).mp havoid
    · exact (distanceBinEvent_reflect_iff_eq447 s m _ alpha).mp hdist
  · rintro ⟨⟨⟨hprefix, havoid⟩, hdist⟩, htheta⟩
    refine ⟨⟨⟨?_, ?_⟩, ?_⟩, htheta⟩
    · have hleft := (prefixPairingEvent_y_reflect_iff
        (reflectPath s) m (stageNumber r + 1)).mpr hprefix
      rw [reflectPath_reflectPath] at hleft
      have hidx : (⟨5, by omega⟩ : Fin 6) = yIndex' := Fin.ext rfl
      rw [← hidx]
      exact hleft
    · exact (hlozDirectAvoidanceEvent_reflect_iff_eq447 s m _).mpr havoid
    · exact (distanceBinEvent_reflect_iff_eq447 s m _ alpha).mpr hdist

theorem simpleRandomWalkLaw_lemma411412AuxThetaEvent_yPrime_eq_prop45_y
    (m : ℕ) (r : StageIndex) (alpha : ℝ) :
    simpleRandomWalkLaw
        (lemma411412AuxThetaEvent sourceEquation447ThetaTarget
          m yIndex' r alpha) =
      simpleRandomWalkLaw
        (prop45FailureEvent sourceCanonicalProfiles canonicalCStar
          m yIndex r alpha) := by
  rw [lemma411412AuxThetaEvent_yPrime_eq_preimage_prop45_y]
  apply simpleRandomWalkLaw_reflectPath_preimage
  exact (((measurableSet_prefixPairingEvent m yIndex
      (stageNumber r + 1)).inter
    (measurableSet_hlozDirectAvoidanceEvent m (stageNumber r + 1))).inter
    (measurableSet_distanceBinEvent m (stageNumber r) alpha)).inter
    (measurableSet_stoppedThetaEvent (sourceCanonicalProfiles yIndex)
      (canonicalCStar yIndex) m (stageNumber r))

/-- The flexible Equation-(4.47) profile exception costs no new source
estimate.  At five pairings it is the canonical Proposition-4.5 event; at
`Y'` reflection identifies its law with the already bounded `Y` event. -/
theorem sourceEquation447AuxThetaEstimate_of_prop45
    (thetaCoeff : ℕ)
    (h : Prop47Prop45Estimate
      sourceCanonicalProfiles canonicalCStar thetaCoeff) :
    Prop47Lemma411412AuxThetaEstimate
      sourceEquation447ThetaTarget thetaCoeff := by
  filter_upwards [h] with m hm
  intro i r a ha
  by_cases hi : i = yIndex'
  · subst i
    rw [simpleRandomWalkLaw_lemma411412AuxThetaEvent_yPrime_eq_prop45_y]
    exact hm yIndex r a ha
  · simpa [lemma411412AuxThetaEvent, sourceEquation447ThetaTarget, hi,
      prop45FailureEvent] using hm i r a ha

/-! ## Proposition 4.9 atom inputs -/

noncomputable def ForwardColumnWinnerSource.toProp49Input
    {m : ℕ} (S : ForwardColumnWinnerSource m)
    (A : ℕ) (alpha : ℝ) (screen : Set Path)
    (candidate : Finset S.Coord) (narrowBand : S.Coord → Set ℕ)
    (hband : ∀ x ∈ candidate, MeasurableSet (narrowBand x))
    (hcard : (candidate.card : ℝ) ≤ Real.log ((m : ℝ) + 1) ^ 2)
    (hcoordinate : ∀ x ∈ candidate,
      sourceTruncatedNegBinMeasure m (S.profile x) (narrowBand x) ≤
        sourceProp49CoordinateRate m A alpha)
    (hinclusion :
      S.pathAtom ∩ screen ⊆ S.pathAtom ∩
        (fun s ↦ (S.lazyVector s, S.nextDirection s)) ⁻¹'
          (anyCoordinateInBand candidate narrowBand ×ˢ Set.univ)) :
    @StoppedTruncatedProp49AtomInput S.Coord inferInstance
      m S.k A alpha screen where
  atom := S.pathAtom
  measurable_atom := S.measurableSet_pathAtom
  lazyVector := S.lazyVector
  nextDirection := S.nextDirection
  profile := S.profile
  profile_lt := S.profile_lt
  measurable_joint := S.measurable_lazyVector.prodMk S.measurable_nextDirection
  map_law := S.map_law
  candidate := candidate
  narrowBand := narrowBand
  narrowBand_measurable := hband
  candidate_card := hcard
  coordinate_bound := hcoordinate
  screen_subset := hinclusion

noncomputable def PrimedColumnWinnerSource.toProp49Input
    {m : ℕ} (S : PrimedColumnWinnerSource m)
    (A : ℕ) (alpha : ℝ) (screen : Set Path)
    (candidate : Finset S.Coord) (narrowBand : S.Coord → Set ℕ)
    (hband : ∀ x ∈ candidate, MeasurableSet (narrowBand x))
    (hcard : (candidate.card : ℝ) ≤ Real.log ((m : ℝ) + 1) ^ 2)
    (hcoordinate : ∀ x ∈ candidate,
      sourceTruncatedNegBinMeasure m (S.profile x) (narrowBand x) ≤
        sourceProp49CoordinateRate m A alpha)
    (hinclusion :
      S.pathAtom ∩ screen ⊆ S.pathAtom ∩
        (fun s ↦ (S.lazyVector s, S.nextDirection s)) ⁻¹'
          (anyCoordinateInBand candidate narrowBand ×ˢ Set.univ)) :
    @StoppedTruncatedProp49AtomInput S.Coord inferInstance
      m S.k A alpha screen where
  atom := S.pathAtom
  measurable_atom := S.measurableSet_pathAtom
  lazyVector := S.lazyVector
  nextDirection := S.nextDirection
  profile := S.profile
  profile_lt := S.profile_lt
  measurable_joint := S.measurable_lazyVector.prodMk S.measurable_nextDirection
  map_law := S.map_law
  candidate := candidate
  narrowBand := narrowBand
  narrowBand_measurable := hband
  candidate_card := hcard
  coordinate_bound := hcoordinate
  screen_subset := hinclusion

/-- Refined source data for a forward column atom.  The preceding sequential
history is intentionally absent: a caller that needs it must separately
supply `StoppedTruncatedProp49HistoryFactorization`. -/
structure ForwardColumnProp49AtomData
    (m A : ℕ) (alpha : ℝ) (screen : Set Path) where
  source : ForwardColumnWinnerSource m
  candidate : Finset source.Coord
  candidate_card :
    (candidate.card : ℝ) ≤ Real.log ((m : ℝ) + 1) ^ 2
  comparisonCoeff : ℕ
  windowGrowth : HLOZLemma412Windows.SourceWindowGrowth comparisonCoeff m
  profile_window : ∀ x ∈ candidate,
    HLOZLemma412Windows.InEquation458ExternalWindow comparisonCoeff m
      (source.profile x)
  alpha_nonneg : 0 ≤ alpha + HLOZProp47Parameters.delta
  alpha_lt : alpha + HLOZProp47Parameters.delta <
    HLOZProp47Parameters.kappaOne
  coefficient :
    8 * Real.exp (HLOZLemma412Windows.sourceComparisonExponent
      comparisonCoeff) ≤ A
  screen_subset :
    source.pathAtom ∩ screen ⊆ source.pathAtom ∩
      (fun s ↦ (source.lazyVector s, source.nextDirection s)) ⁻¹'
        (anyCoordinateInBand candidate (fun x ↦ sourceProp49NarrowBand m
          (source.profile x) alpha) ×ˢ Set.univ)

noncomputable def ForwardColumnProp49AtomData.toInput
    {m A : ℕ} {alpha : ℝ} {screen : Set Path}
    (D : ForwardColumnProp49AtomData m A alpha screen) :
    @StoppedTruncatedProp49AtomInput D.source.Coord inferInstance
      m D.source.k A alpha screen :=
  D.source.toProp49Input A alpha screen D.candidate
    (fun x ↦ sourceProp49NarrowBand m (D.source.profile x) alpha)
    (fun _ _ ↦ measurableSet_sourceProp49NarrowBand _ _ _)
    D.candidate_card (fun x hx ↦ by
      rw [sourceProp49CoordinateRate]
      exact sourceTruncatedNegBinMeasure_sourceProp49NarrowBand_le
        D.comparisonCoeff m (D.source.profile x) A alpha D.windowGrowth
          (D.profile_window x hx) D.alpha_nonneg D.alpha_lt D.coefficient)
    D.screen_subset

structure PrimedColumnProp49AtomData
    (m A : ℕ) (alpha : ℝ) (screen : Set Path) where
  source : PrimedColumnWinnerSource m
  candidate : Finset source.Coord
  candidate_card :
    (candidate.card : ℝ) ≤ Real.log ((m : ℝ) + 1) ^ 2
  comparisonCoeff : ℕ
  windowGrowth : HLOZLemma412Windows.SourceWindowGrowth comparisonCoeff m
  profile_window : ∀ x ∈ candidate,
    HLOZLemma412Windows.InEquation458ExternalWindow comparisonCoeff m
      (source.profile x)
  alpha_nonneg : 0 ≤ alpha + HLOZProp47Parameters.delta
  alpha_lt : alpha + HLOZProp47Parameters.delta <
    HLOZProp47Parameters.kappaOne
  coefficient :
    8 * Real.exp (HLOZLemma412Windows.sourceComparisonExponent
      comparisonCoeff) ≤ A
  screen_subset :
    source.pathAtom ∩ screen ⊆ source.pathAtom ∩
      (fun s ↦ (source.lazyVector s, source.nextDirection s)) ⁻¹'
        (anyCoordinateInBand candidate (fun x ↦ sourceProp49NarrowBand m
          (source.profile x) alpha) ×ˢ Set.univ)

noncomputable def PrimedColumnProp49AtomData.toInput
    {m A : ℕ} {alpha : ℝ} {screen : Set Path}
    (D : PrimedColumnProp49AtomData m A alpha screen) :
    @StoppedTruncatedProp49AtomInput D.source.Coord inferInstance
      m D.source.k A alpha screen :=
  D.source.toProp49Input A alpha screen D.candidate
    (fun x ↦ sourceProp49NarrowBand m (D.source.profile x) alpha)
    (fun _ _ ↦ measurableSet_sourceProp49NarrowBand _ _ _)
    D.candidate_card (fun x hx ↦ by
      rw [sourceProp49CoordinateRate]
      exact sourceTruncatedNegBinMeasure_sourceProp49NarrowBand_le
        D.comparisonCoeff m (D.source.profile x) A alpha D.windowGrowth
          (D.profile_window x hx) D.alpha_nonneg D.alpha_lt D.coefficient)
    D.screen_subset

/-! ### Proposition 4.9 from full-complement fiber determination -/

/-- Profile-generic forward terminal form of the full-complement tower.

The stopped product law is independent of the profile family used to
describe the preceding history.  Consequently the same checked law applies
to the literal temporal-parity source profiles, not only to the auxiliary
endpoint-adapted column profiles. -/
theorem ForwardColumnProp49AtomData.fullComplement_orderedProfileHistory_screenEstimate_of_fiberwise
    {m A : ℕ} {alpha : ℝ} {screen : Set Path}
    (profiles : Fin 6 → ExternalProfilePair) (cStar : Fin 6 → ℝ)
    {i : Fin 6} {a : HLOZProp47Parameters.AlphaTriple} {r : StageIndex}
    (D : ForwardColumnProp49AtomData m A alpha screen)
    (c : Fin (stageNumber r) → Site)
    (hdet : EventDeterminedByOn D.source.pathAtom
      (orderedProfileHistoryEvent profiles cStar m i a r c)
      (forwardTerminalFullComplementPath D.source.clock D.source.creationSet
        D.source.activeBases)) :
    RefinedAtomScreenEstimate
      (orderedProfileHistoryPathAtom profiles cStar m i a r c
        D.source.pathAtom) screen
      (sourceProp49ScreenRate m A alpha) := by
  let complementLaw := columnMixedComplementRunMeasure
    D.source.clock.baseAt m D.source.creationSet D.source.activeBases
      D.source.externalLeft D.source.externalRight
  let z := forwardTerminalFullComplementPath D.source.clock
    D.source.creationSet D.source.activeBases
  apply refinedAtomScreenEstimate_of_joint_complement_determined
    D.toInput complementLaw z
  · exact measurable_forwardTerminalFullComplementPath D.source.clock
      D.source.creationSet D.source.activeBases
  · exact MeasurableSet.of_discrete
  · exact hdet
  · simpa only [ForwardColumnProp49AtomData.toInput,
      ForwardColumnWinnerSource.toProp49Input,
      ForwardColumnWinnerSource.pathAtom,
      ForwardColumnWinnerSource.lazyVector,
      ForwardColumnWinnerSource.nextDirection,
      ForwardColumnWinnerSource.profile, complementLaw, z] using
      D.source.fullComplement_map_law

/-- Profile-generic backward/primed terminal form. -/
theorem PrimedColumnProp49AtomData.fullComplement_orderedProfileHistory_screenEstimate_of_fiberwise
    {m A : ℕ} {alpha : ℝ} {screen : Set Path}
    (profiles : Fin 6 → ExternalProfilePair) (cStar : Fin 6 → ℝ)
    {i : Fin 6} {a : HLOZProp47Parameters.AlphaTriple} {r : StageIndex}
    (D : PrimedColumnProp49AtomData m A alpha screen)
    (c : Fin (stageNumber r) → Site)
    (hdet : EventDeterminedByOn D.source.pathAtom
      (orderedProfileHistoryEvent profiles cStar m i a r c)
      (primedTerminalFullComplementPath D.source.clock D.source.creationSet
        D.source.activeBases)) :
    RefinedAtomScreenEstimate
      (orderedProfileHistoryPathAtom profiles cStar m i a r c
        D.source.pathAtom) screen
      (sourceProp49ScreenRate m A alpha) := by
  let complementLaw := columnMixedComplementRunMeasure
    D.source.clock.baseAt m D.source.creationSet D.source.activeBases
      D.source.externalLeft D.source.externalRight
  let z := primedTerminalFullComplementPath D.source.clock
    D.source.creationSet D.source.activeBases
  apply refinedAtomScreenEstimate_of_joint_complement_determined
    D.toInput complementLaw z
  · exact measurable_primedTerminalFullComplementPath D.source.clock
      D.source.creationSet D.source.activeBases
  · exact MeasurableSet.of_discrete
  · exact hdet
  · simpa only [PrimedColumnProp49AtomData.toInput,
      PrimedColumnWinnerSource.toProp49Input,
      PrimedColumnWinnerSource.pathAtom,
      PrimedColumnWinnerSource.lazyVector,
      PrimedColumnWinnerSource.nextDirection,
      PrimedColumnWinnerSource.profile, complementLaw, z] using
      D.source.fullComplement_map_law

/-- The forward column tower with the deterministic history condition split
into its source components.  Ordered creation sites, the initial pairing
event and each earlier stage may be reconstructed independently. -/
theorem ForwardColumnProp49AtomData.fullComplement_orderedProfileHistory_screenEstimate_of_stages
    {m A : ℕ} {alpha : ℝ} {screen : Set Path}
    (profiles : Fin 6 → ExternalProfilePair) (cStar : Fin 6 → ℝ)
    {i : Fin 6} {a : HLOZProp47Parameters.AlphaTriple} {r : StageIndex}
    (D : ForwardColumnProp49AtomData m A alpha screen)
    (c : Fin (stageNumber r) → Site)
    (hordered : EventDeterminedByOn D.source.pathAtom
      (orderedCreationSitesEvent m (stageNumber r) c)
      (forwardTerminalFullComplementPath D.source.clock
        D.source.creationSet D.source.activeBases))
    (hbase : EventDeterminedByOn D.source.pathAtom
      (prefixPairingEvent m i 1)
      (forwardTerminalFullComplementPath D.source.clock
        D.source.creationSet D.source.activeBases))
    (hstage : ∀ (j : Fin 3), j.1 < r.1 →
      EventDeterminedByOn D.source.pathAtom
        (prop47StageEvent profiles cStar i m j
          (alphaValue (tripleAlphaIndex a j)))
        (forwardTerminalFullComplementPath D.source.clock
          D.source.creationSet D.source.activeBases)) :
    RefinedAtomScreenEstimate
      (orderedProfileHistoryPathAtom profiles cStar m i a r c
        D.source.pathAtom)
      screen (sourceProp49ScreenRate m A alpha) := by
  apply D.fullComplement_orderedProfileHistory_screenEstimate_of_fiberwise
    profiles cStar c
  exact eventDeterminedByOn_orderedProfileHistoryEvent_of_stages
    D.source.pathAtom
      (forwardTerminalFullComplementPath D.source.clock
        D.source.creationSet D.source.activeBases)
      profiles cStar m i a r c hordered hbase hstage

/-- Backward/primed counterpart of the componentwise history tower. -/
theorem PrimedColumnProp49AtomData.fullComplement_orderedProfileHistory_screenEstimate_of_stages
    {m A : ℕ} {alpha : ℝ} {screen : Set Path}
    (profiles : Fin 6 → ExternalProfilePair) (cStar : Fin 6 → ℝ)
    {i : Fin 6} {a : HLOZProp47Parameters.AlphaTriple} {r : StageIndex}
    (D : PrimedColumnProp49AtomData m A alpha screen)
    (c : Fin (stageNumber r) → Site)
    (hordered : EventDeterminedByOn D.source.pathAtom
      (orderedCreationSitesEvent m (stageNumber r) c)
      (primedTerminalFullComplementPath D.source.clock
        D.source.creationSet D.source.activeBases))
    (hbase : EventDeterminedByOn D.source.pathAtom
      (prefixPairingEvent m i 1)
      (primedTerminalFullComplementPath D.source.clock
        D.source.creationSet D.source.activeBases))
    (hstage : ∀ (j : Fin 3), j.1 < r.1 →
      EventDeterminedByOn D.source.pathAtom
        (prop47StageEvent profiles cStar i m j
          (alphaValue (tripleAlphaIndex a j)))
        (primedTerminalFullComplementPath D.source.clock
          D.source.creationSet D.source.activeBases)) :
    RefinedAtomScreenEstimate
      (orderedProfileHistoryPathAtom profiles cStar m i a r c
        D.source.pathAtom)
      screen (sourceProp49ScreenRate m A alpha) := by
  apply D.fullComplement_orderedProfileHistory_screenEstimate_of_fiberwise
    profiles cStar c
  exact eventDeterminedByOn_orderedProfileHistoryEvent_of_stages
    D.source.pathAtom
      (primedTerminalFullComplementPath D.source.clock
        D.source.creationSet D.source.activeBases)
      profiles cStar m i a r c hordered hbase hstage

/-- For a forward terminal atom, the checked three-factor product law turns
fiberwise determination of the ordered history by the complete chronological
complement into the exact refined Proposition-4.9 screen estimate. -/
theorem ForwardColumnProp49AtomData.fullComplement_orderedHistory_screenEstimate_of_fiberwise
    {m A : ℕ} {alpha : ℝ} {screen : Set Path}
    {i : Fin 6} {a : HLOZProp47Parameters.AlphaTriple} {r : StageIndex}
    (D : ForwardColumnProp49AtomData m A alpha screen)
    (c : Fin (stageNumber r) → Site)
    (hdet : EventDeterminedByOn D.source.pathAtom
      (orderedCanonicalHistoryEvent m i a r c)
      (forwardTerminalFullComplementPath D.source.clock D.source.creationSet
        D.source.activeBases)) :
    RefinedAtomScreenEstimate
      (D.source.orderedHistoryRefinedPathAtom i a r c) screen
      (sourceProp49ScreenRate m A alpha) := by
  rw [D.source.orderedHistoryRefinedPathAtom_eq]
  exact D.fullComplement_orderedProfileHistory_screenEstimate_of_fiberwise
    canonicalProfiles canonicalCStar c hdet

/-- Backward/primed terminal counterpart. -/
theorem PrimedColumnProp49AtomData.fullComplement_orderedHistory_screenEstimate_of_fiberwise
    {m A : ℕ} {alpha : ℝ} {screen : Set Path}
    {i : Fin 6} {a : HLOZProp47Parameters.AlphaTriple} {r : StageIndex}
    (D : PrimedColumnProp49AtomData m A alpha screen)
    (c : Fin (stageNumber r) → Site)
    (hdet : EventDeterminedByOn D.source.pathAtom
      (orderedCanonicalHistoryEvent m i a r c)
      (primedTerminalFullComplementPath D.source.clock D.source.creationSet
        D.source.activeBases)) :
    RefinedAtomScreenEstimate
      (D.source.orderedHistoryRefinedPathAtom i a r c) screen
      (sourceProp49ScreenRate m A alpha) := by
  rw [D.source.orderedHistoryRefinedPathAtom_eq]
  exact D.fullComplement_orderedProfileHistory_screenEstimate_of_fiberwise
    canonicalProfiles canonicalCStar c hdet

/-- A forward ordered-history atom whose Proposition-4.9 estimate is derived
from the full-complement law.  The only additional condition is the literal
fiberwise determination of the ordered history on the coarse source atom. -/
structure ForwardColumnFullComplementOrderedHistoryAtomData
    (m A : ℕ) (alpha : ℝ) (screen : Set Path)
    (i : Fin 6) (a : HLOZProp47Parameters.AlphaTriple)
    (r : StageIndex) where
  data : ForwardColumnProp49AtomData m A alpha screen
  stage_eq : data.source.k = stageNumber r
  orderedSites : Fin (stageNumber r) → Site
  m_pos : 0 < m
  threshold_before_terminal :
    data.source.orderedHistoryRefinedIncrementAtom i a r orderedSites ⊆
    {omega | firstKSitesReachLevel m (stageNumber r)
        (simpleRandomWalk omega) ≤
      (data.source.terminalEndTime omega : WithTop ℕ)}
  history_determined : EventDeterminedByOn data.source.pathAtom
    (orderedCanonicalHistoryEvent m i a r orderedSites)
    (forwardTerminalFullComplementPath data.source.clock
      data.source.creationSet data.source.activeBases)

namespace ForwardColumnFullComplementOrderedHistoryAtomData

variable {m A : ℕ} {alpha : ℝ} {screen : Set Path}
    {i : Fin 6} {a : HLOZProp47Parameters.AlphaTriple}
    {r : StageIndex}

noncomputable def toOrderedHistorySource
    (D : ForwardColumnFullComplementOrderedHistoryAtomData
      m A alpha screen i a r) :
    ForwardColumnOrderedHistorySource m i a r where
  source := D.data.source
  stage_eq := D.stage_eq
  orderedSites := D.orderedSites
  m_pos := D.m_pos
  threshold_before_terminal := D.threshold_before_terminal

theorem prop49ScreenEstimate
    (D : ForwardColumnFullComplementOrderedHistoryAtomData
      m A alpha screen i a r) :
    D.toOrderedHistorySource.Prop49ScreenEstimate A alpha screen := by
  exact D.data.fullComplement_orderedHistory_screenEstimate_of_fiberwise
    D.orderedSites D.history_determined

end ForwardColumnFullComplementOrderedHistoryAtomData

/-- Backward/primed form of the information-preserving ordered-history atom. -/
structure PrimedColumnFullComplementOrderedHistoryAtomData
    (m A : ℕ) (alpha : ℝ) (screen : Set Path)
    (i : Fin 6) (a : HLOZProp47Parameters.AlphaTriple)
    (r : StageIndex) where
  data : PrimedColumnProp49AtomData m A alpha screen
  stage_eq : data.source.k = stageNumber r
  orderedSites : Fin (stageNumber r) → Site
  m_pos : 0 < m
  threshold_before_terminal :
    data.source.orderedHistoryRefinedIncrementAtom i a r orderedSites ⊆
    {omega | firstKSitesReachLevel m (stageNumber r)
        (simpleRandomWalk omega) ≤
      (data.source.terminalEndTime omega : WithTop ℕ)}
  history_determined : EventDeterminedByOn data.source.pathAtom
    (orderedCanonicalHistoryEvent m i a r orderedSites)
    (primedTerminalFullComplementPath data.source.clock
      data.source.creationSet data.source.activeBases)

namespace PrimedColumnFullComplementOrderedHistoryAtomData

variable {m A : ℕ} {alpha : ℝ} {screen : Set Path}
    {i : Fin 6} {a : HLOZProp47Parameters.AlphaTriple}
    {r : StageIndex}

noncomputable def toOrderedHistorySource
    (D : PrimedColumnFullComplementOrderedHistoryAtomData
      m A alpha screen i a r) :
    PrimedColumnOrderedHistorySource m i a r where
  source := D.data.source
  stage_eq := D.stage_eq
  orderedSites := D.orderedSites
  m_pos := D.m_pos
  threshold_before_terminal := D.threshold_before_terminal

theorem prop49ScreenEstimate
    (D : PrimedColumnFullComplementOrderedHistoryAtomData
      m A alpha screen i a r) :
    D.toOrderedHistorySource.Prop49ScreenEstimate A alpha screen := by
  exact D.data.fullComplement_orderedHistory_screenEstimate_of_fiberwise
    D.orderedSites D.history_determined

end PrimedColumnFullComplementOrderedHistoryAtomData

/-- Countable forward phase with all atom-local Proposition-4.9 estimates
derived from complement fiber determination. -/
structure ForwardColumnFullComplementOrderedHistoryProp49Branch
    (m : ℕ) (i : Fin 6) (a : HLOZProp47Parameters.AlphaTriple)
    (r : StageIndex) (localCoeff : ℕ) (alpha : ℝ)
    (screen : Set Path) where
  atoms : ℕ → ForwardColumnFullComplementOrderedHistoryAtomData
    m localCoeff alpha screen i a r
  pairwise_disjoint : Pairwise fun n l ↦
    Disjoint (atoms n).toOrderedHistorySource.pathAtom
      (atoms l).toOrderedHistorySource.pathAtom
  cover :
    prop47History canonicalProfiles canonicalCStar m i a r.1 ∩ screen ⊆
      ⋃ n, (atoms n).toOrderedHistorySource.pathAtom

namespace ForwardColumnFullComplementOrderedHistoryProp49Branch

noncomputable def toOrderedHistoryProp49Branch
    {m : ℕ} {i : Fin 6} {a : HLOZProp47Parameters.AlphaTriple}
    {r : StageIndex} {localCoeff : ℕ} {alpha : ℝ}
    {screen : Set Path}
    (B : ForwardColumnFullComplementOrderedHistoryProp49Branch
      m i a r localCoeff alpha screen) :
    ForwardColumnOrderedHistoryProp49Branch
      m i a r localCoeff alpha screen where
  atoms := fun n ↦ (B.atoms n).toOrderedHistorySource
  pairwise_disjoint := B.pairwise_disjoint
  cover := B.cover
  screen_estimate := fun n ↦ (B.atoms n).prop49ScreenEstimate

end ForwardColumnFullComplementOrderedHistoryProp49Branch

/-- Backward/primed complement-determined phase. -/
structure PrimedColumnFullComplementOrderedHistoryProp49Branch
    (m : ℕ) (i : Fin 6) (a : HLOZProp47Parameters.AlphaTriple)
    (r : StageIndex) (localCoeff : ℕ) (alpha : ℝ)
    (screen : Set Path) where
  atoms : ℕ → PrimedColumnFullComplementOrderedHistoryAtomData
    m localCoeff alpha screen i a r
  pairwise_disjoint : Pairwise fun n l ↦
    Disjoint (atoms n).toOrderedHistorySource.pathAtom
      (atoms l).toOrderedHistorySource.pathAtom
  cover :
    prop47History canonicalProfiles canonicalCStar m i a r.1 ∩ screen ⊆
      ⋃ n, (atoms n).toOrderedHistorySource.pathAtom

namespace PrimedColumnFullComplementOrderedHistoryProp49Branch

noncomputable def toOrderedHistoryProp49Branch
    {m : ℕ} {i : Fin 6} {a : HLOZProp47Parameters.AlphaTriple}
    {r : StageIndex} {localCoeff : ℕ} {alpha : ℝ}
    {screen : Set Path}
    (B : PrimedColumnFullComplementOrderedHistoryProp49Branch
      m i a r localCoeff alpha screen) :
    PrimedColumnOrderedHistoryProp49Branch
      m i a r localCoeff alpha screen where
  atoms := fun n ↦ (B.atoms n).toOrderedHistorySource
  pairwise_disjoint := B.pairwise_disjoint
  cover := B.cover
  screen_estimate := fun n ↦ (B.atoms n).prop49ScreenEstimate

end PrimedColumnFullComplementOrderedHistoryProp49Branch

theorem ForwardColumnProp49AtomData.conditional_screen_le
    {m A : ℕ} {alpha : ℝ} {screen : Set Path}
    (D : ForwardColumnProp49AtomData m A alpha screen) :
    simpleRandomWalkLaw[|D.source.pathAtom]
        (D.source.pathAtom ∩ screen) ≤ sourceProp49ScreenRate m A alpha :=
  D.toInput.conditional_screen_le

theorem PrimedColumnProp49AtomData.conditional_screen_le
    {m A : ℕ} {alpha : ℝ} {screen : Set Path}
    (D : PrimedColumnProp49AtomData m A alpha screen) :
    simpleRandomWalkLaw[|D.source.pathAtom]
        (D.source.pathAtom ∩ screen) ≤ sourceProp49ScreenRate m A alpha :=
  D.toInput.conditional_screen_le

/-- The history-intersected estimate is exposed only after the exact
active/complement factorization is supplied. -/
theorem ForwardColumnProp49AtomData.history_screen_le
    {m A : ℕ} {alpha : ℝ} {screen history : Set Path}
    (D : ForwardColumnProp49AtomData m A alpha screen)
    (F : StoppedTruncatedProp49HistoryFactorization D.toInput history) :
    simpleRandomWalkLaw (D.source.pathAtom ∩ history ∩ screen) ≤
      sourceProp49ScreenRate m A alpha *
        simpleRandomWalkLaw (D.source.pathAtom ∩ history) :=
  F.history_screen_le D.toInput

theorem PrimedColumnProp49AtomData.history_screen_le
    {m A : ℕ} {alpha : ℝ} {screen history : Set Path}
    (D : PrimedColumnProp49AtomData m A alpha screen)
    (F : StoppedTruncatedProp49HistoryFactorization D.toInput history) :
    simpleRandomWalkLaw (D.source.pathAtom ∩ history ∩ screen) ≤
      sourceProp49ScreenRate m A alpha *
        simpleRandomWalkLaw (D.source.pathAtom ∩ history) :=
  F.history_screen_le D.toInput

/-- Honest sequential-history input for one forward column atom.  The
history-intersected inequality is kept as the exact unresolved source
estimate; no independence of the coarse stopped atom and prior history is
asserted. -/
structure ForwardColumnProp49HistoryAtomData
    (m A : ℕ) (alpha : ℝ) (screen history : Set Path) where
  data : ForwardColumnProp49AtomData m A alpha screen
  history_screen_bound :
    simpleRandomWalkLaw
        (data.source.pathAtom ∩ history ∩ screen) ≤
      sourceProp49ScreenRate m A alpha *
        simpleRandomWalkLaw (data.source.pathAtom ∩ history)

/-- Honest sequential-history input for one backward terminal phase atom of
`Y`. -/
structure PrimedColumnProp49HistoryAtomData
    (m A : ℕ) (alpha : ℝ) (screen history : Set Path) where
  data : PrimedColumnProp49AtomData m A alpha screen
  history_screen_bound :
    simpleRandomWalkLaw
        (data.source.pathAtom ∩ history ∩ screen) ≤
      sourceProp49ScreenRate m A alpha *
        simpleRandomWalkLaw (data.source.pathAtom ∩ history)

/-- A branch-local forward-phase atomization for the sequential Proposition
4.9 estimate.  It covers only the supplied history branch. -/
structure ForwardColumnProp49HistoryBranch
    (m A : ℕ) (alpha : ℝ) (screen history : Set Path) where
  atoms : ℕ → ForwardColumnProp49HistoryAtomData m A alpha screen history
  history_measurable : MeasurableSet history
  cover : history ⊆ ⋃ n, (atoms n).data.source.pathAtom
  pairwise_disjoint : Pairwise fun n l ↦
    Disjoint (atoms n).data.source.pathAtom (atoms l).data.source.pathAtom

/-- A branch-local backward-phase atomization for the same consumer. -/
structure PrimedColumnProp49HistoryBranch
    (m A : ℕ) (alpha : ℝ) (screen history : Set Path) where
  atoms : ℕ → PrimedColumnProp49HistoryAtomData m A alpha screen history
  history_measurable : MeasurableSet history
  cover : history ⊆ ⋃ n, (atoms n).data.source.pathAtom
  pairwise_disjoint : Pairwise fun n l ↦
    Disjoint (atoms n).data.source.pathAtom (atoms l).data.source.pathAtom

theorem ForwardColumnProp49HistoryBranch.measure_history_screen_le
    {m A : ℕ} {alpha : ℝ} {screen history : Set Path}
    (B : ForwardColumnProp49HistoryBranch m A alpha screen history) :
    simpleRandomWalkLaw (history ∩ screen) ≤
      sourceProp49ScreenRate m A alpha * simpleRandomWalkLaw history := by
  exact measure_history_inter_le_mul_of_countable_atomwise
    simpleRandomWalkLaw history screen
      (fun n ↦ (B.atoms n).data.source.pathAtom)
      (sourceProp49ScreenRate m A alpha) B.pairwise_disjoint
      (fun n ↦ (B.atoms n).data.source.measurableSet_pathAtom)
      B.history_measurable B.cover
      (fun n ↦ (B.atoms n).history_screen_bound)

theorem PrimedColumnProp49HistoryBranch.measure_history_screen_le
    {m A : ℕ} {alpha : ℝ} {screen history : Set Path}
    (B : PrimedColumnProp49HistoryBranch m A alpha screen history) :
    simpleRandomWalkLaw (history ∩ screen) ≤
      sourceProp49ScreenRate m A alpha * simpleRandomWalkLaw history := by
  exact measure_history_inter_le_mul_of_countable_atomwise
    simpleRandomWalkLaw history screen
      (fun n ↦ (B.atoms n).data.source.pathAtom)
      (sourceProp49ScreenRate m A alpha) B.pairwise_disjoint
      (fun n ↦ (B.atoms n).data.source.measurableSet_pathAtom)
      B.history_measurable B.cover
      (fun n ↦ (B.atoms n).history_screen_bound)

/-! ## Lemma 4.10 / Proposition 4.8 on the two `Y` terminal phases -/

/-- Probability transport common to the two literal column terminal phases.
The only probabilistic premise is the fixed-profile Proposition 4.8 bound;
the stopped product law is passed separately and is instantiated below by
the terminal restart theorems. -/
private theorem columnTerminalProfileEvent_local_bound
    {ι : Type*} [Fintype ι]
    {cWindow m : ℕ} {alpha : ℝ}
    {failure atom : Set Path}
    (profile : ι → ℕ)
    (lazyVector : Path → ι → ℕ)
    (nextDirection : Path → Direction)
    (hmeasurableLazy : Measurable lazyVector)
    (hmeasurableNext : Measurable nextDirection)
    (hmap : (simpleRandomWalkLaw.restrict atom).map
        (fun s ↦ (lazyVector s, nextDirection s)) =
      simpleRandomWalkLaw atom •
        ((sourceTruncatedProfileMeasure m profile).prod directionLaw))
    (hsubset : failure ∩ atom ⊆ lazyVector ⁻¹'
      sourceProfileQEvent m (sourceAlphaIntervalCount m alpha) profile
        (geometricThreshold (Real.log (m : ℝ) ^ 2)
          (sourceLemma411GrowthFactor cWindow)
          (sourceAlphaIntervalCount m alpha)))
    (tail : ℝ≥0∞)
    (hProp48 :
      sourceTruncatedProfileMeasure m profile
        (sourceProfileQEvent m (sourceAlphaIntervalCount m alpha) profile
          (geometricThreshold (Real.log (m : ℝ) ^ 2)
            (sourceLemma411GrowthFactor cWindow)
            (sourceAlphaIntervalCount m alpha))) ≤ tail) :
    simpleRandomWalkLaw (failure ∩ atom) ≤
      tail * simpleRandomWalkLaw atom := by
  let Q : Set (ι → ℕ) :=
    sourceProfileQEvent m (sourceAlphaIntervalCount m alpha) profile
      (geometricThreshold (Real.log (m : ℝ) ^ 2)
        (sourceLemma411GrowthFactor cWindow)
        (sourceAlphaIntervalCount m alpha))
  let B : Set ((ι → ℕ) × Direction) :=
    Q ×ˢ (Set.univ : Set Direction)
  have hB : MeasurableSet B := MeasurableSet.of_discrete
  have hmeasurable : Measurable (fun s ↦ (lazyVector s, nextDirection s)) :=
    hmeasurableLazy.prodMk hmeasurableNext
  have hprod :
      (sourceTruncatedProfileMeasure m profile).prod directionLaw B =
        sourceTruncatedProfileMeasure m profile Q := by
    dsimp [B]
    rw [Measure.prod_prod, measure_univ, mul_one]
  have hrestricted :
      simpleRandomWalkLaw
          (atom ∩ (fun s ↦ (lazyVector s, nextDirection s)) ⁻¹' B) =
        simpleRandomWalkLaw atom *
          sourceTruncatedProfileMeasure m profile Q := by
    have hmeasure := congrArg
      (fun mu : Measure ((ι → ℕ) × Direction) ↦ mu B) hmap
    rw [Measure.map_apply hmeasurable hB,
      Measure.restrict_apply (hB.preimage hmeasurable),
      Measure.smul_apply, smul_eq_mul, hprod] at hmeasure
    simpa only [Set.inter_comm] using hmeasure
  have hfailure : failure ∩ atom ⊆
      atom ∩ (fun s ↦ (lazyVector s, nextDirection s)) ⁻¹' B := by
    intro s hs
    refine ⟨hs.2, ?_⟩
    exact ⟨hsubset hs, trivial⟩
  calc
    simpleRandomWalkLaw (failure ∩ atom) ≤
        simpleRandomWalkLaw
          (atom ∩ (fun s ↦ (lazyVector s, nextDirection s)) ⁻¹' B) :=
      measure_mono hfailure
    _ = simpleRandomWalkLaw atom *
        sourceTruncatedProfileMeasure m profile Q := hrestricted
    _ ≤ simpleRandomWalkLaw atom * tail := by gcongr
    _ = tail * simpleRandomWalkLaw atom := mul_comm _ _

namespace ForwardColumnWinnerSource

/-- The forward terminal source atom and the coded equation-(4.47) data
give the complete theta-free Proposition-4.8 bound.  No fixed-profile
probability bound is a caller premise. -/
theorem prop48_good_band_local_bound
    {m : ℕ} (S : ForwardColumnWinnerSource m)
    (cWindow : ℕ) {C cBase alpha : ℝ}
    {failure thetaPath : Set Path}
    (R : Equation447CodedProfileData cWindow m C S.profile)
    (G : SourceProp48NumericalAt cWindow m cBase 1 1)
    (hC : 0 < C)
    (halpha : kappaOne ≤ alpha) (hAlpha : alpha ≤ (4 : ℝ) / 5)
    (hfailure : failure ∩ S.pathAtom ⊆
      (fun s ↦ (S.lazyVector s, S.nextDirection s)) ⁻¹'
        (((sourceProfileQEvent m (sourceAlphaIntervalCount m alpha) S.profile
            (geometricThreshold (Real.log (m : ℝ) ^ 2)
              (sourceLemma411GrowthFactor cWindow)
              (sourceAlphaIntervalCount m alpha)) ∩ R.D)) ×ˢ
          (Set.univ : Set Direction)))
    (htheta : (failure ∩ S.pathAtom) ∩
      (fun s ↦ (S.lazyVector s, S.nextDirection s)) ⁻¹'
        (sourceProfileThetaUpTo cWindow m
            (sourceAlphaIntervalCount m alpha) S.profile ×ˢ
          (Set.univ : Set Direction)) ⊆ thetaPath)
    (hbaseAbsorb :
      let d := Real.log ((C + 1) / C)
      let K := (1 - Real.exp (-d))⁻¹
      4 * (Real.exp (-d *
          (Nat.ceil (Real.log (m : ℝ) ^ 2) : ℝ)) * K) ≤
        Real.exp (-(cBase * Real.log (m : ℝ) ^ 2)))
    (tail : ℝ≥0∞)
    (hshift : ENNReal.ofReal (Real.exp (-(min cBase
      (imbalanceRate
        (Real.exp (sourceAdjacentComparisonExponent cWindow))) / 2) *
          Real.log (m : ℝ) ^ 2)) ≤ tail) :
    simpleRandomWalkLaw ((failure \ thetaPath) ∩ S.pathAtom) ≤
      tail * simpleRandomWalkLaw S.pathAtom := by
  let sourceInst : Fintype S.Coord := inferInstance
  letI : Fintype S.Coord := sourceInst
  let A := S.toStoppedEquation447BranchAtom cWindow C
    (Real.log (m : ℝ) ^ 2) ∅
      (R.toRemainingData S.pathAtom S.lazyVector S.nextDirection)
  have hgood :=
    stoppedEquation447BranchAtom_prop48_good_band_bound_at_ennreal
      A G hC halpha hAlpha hbaseAbsorb tail hshift
  have hcoordFintype : A.coordFintype = sourceInst := Subsingleton.elim _ _
  rw [hcoordFintype] at hgood
  have hgoodS :
      sourceTruncatedProfileMeasure m S.profile
        ((sourceProfileQEvent m (sourceAlphaIntervalCount m alpha) S.profile
            (geometricThreshold (Real.log (m : ℝ) ^ 2)
              (sourceLemma411GrowthFactor cWindow)
              (sourceAlphaIntervalCount m alpha)) ∩ R.D) \
          sourceProfileThetaUpTo cWindow m
            (sourceAlphaIntervalCount m alpha) S.profile) ≤ tail := by
    change sourceTruncatedProfileMeasure m S.profile
      ((sourceProfileQEvent m (sourceAlphaIntervalCount m alpha) S.profile
          (geometricThreshold (Real.log (m : ℝ) ^ 2)
            (sourceLemma411GrowthFactor cWindow)
            (sourceAlphaIntervalCount m alpha)) ∩ R.D) \
        sourceProfileThetaUpTo cWindow m
          (sourceAlphaIntervalCount m alpha) S.profile) ≤ tail at hgood
    exact hgood
  apply stoppedProfileGoodEvent_local_bound S.profile S.pathAtom failure
    thetaPath (fun s ↦ (S.lazyVector s, S.nextDirection s))
    (sourceProfileQEvent m (sourceAlphaIntervalCount m alpha) S.profile
        (geometricThreshold (Real.log (m : ℝ) ^ 2)
          (sourceLemma411GrowthFactor cWindow)
          (sourceAlphaIntervalCount m alpha)) ∩ R.D)
    (sourceProfileThetaUpTo cWindow m
      (sourceAlphaIntervalCount m alpha) S.profile)
    (S.measurable_lazyVector.prodMk S.measurable_nextDirection)
    S.map_law hfailure htheta tail hgoodS

end ForwardColumnWinnerSource

namespace PrimedColumnWinnerSource

/-- Backward-terminal counterpart of the forward theta-free good-band
bound. -/
theorem prop48_good_band_local_bound
    {m : ℕ} (S : PrimedColumnWinnerSource m)
    (cWindow : ℕ) {C cBase alpha : ℝ}
    {failure thetaPath : Set Path}
    (R : Equation447CodedProfileData cWindow m C S.profile)
    (G : SourceProp48NumericalAt cWindow m cBase 1 1)
    (hC : 0 < C)
    (halpha : kappaOne ≤ alpha) (hAlpha : alpha ≤ (4 : ℝ) / 5)
    (hfailure : failure ∩ S.pathAtom ⊆
      (fun s ↦ (S.lazyVector s, S.nextDirection s)) ⁻¹'
        (((sourceProfileQEvent m (sourceAlphaIntervalCount m alpha) S.profile
            (geometricThreshold (Real.log (m : ℝ) ^ 2)
              (sourceLemma411GrowthFactor cWindow)
              (sourceAlphaIntervalCount m alpha)) ∩ R.D)) ×ˢ
          (Set.univ : Set Direction)))
    (htheta : (failure ∩ S.pathAtom) ∩
      (fun s ↦ (S.lazyVector s, S.nextDirection s)) ⁻¹'
        (sourceProfileThetaUpTo cWindow m
            (sourceAlphaIntervalCount m alpha) S.profile ×ˢ
          (Set.univ : Set Direction)) ⊆ thetaPath)
    (hbaseAbsorb :
      let d := Real.log ((C + 1) / C)
      let K := (1 - Real.exp (-d))⁻¹
      4 * (Real.exp (-d *
          (Nat.ceil (Real.log (m : ℝ) ^ 2) : ℝ)) * K) ≤
        Real.exp (-(cBase * Real.log (m : ℝ) ^ 2)))
    (tail : ℝ≥0∞)
    (hshift : ENNReal.ofReal (Real.exp (-(min cBase
      (imbalanceRate
        (Real.exp (sourceAdjacentComparisonExponent cWindow))) / 2) *
          Real.log (m : ℝ) ^ 2)) ≤ tail) :
    simpleRandomWalkLaw ((failure \ thetaPath) ∩ S.pathAtom) ≤
      tail * simpleRandomWalkLaw S.pathAtom := by
  let sourceInst : Fintype S.Coord := inferInstance
  letI : Fintype S.Coord := sourceInst
  let A := S.toStoppedEquation447BranchAtom cWindow C
    (Real.log (m : ℝ) ^ 2) ∅
      (R.toRemainingData S.pathAtom S.lazyVector S.nextDirection)
  have hgood :=
    stoppedEquation447BranchAtom_prop48_good_band_bound_at_ennreal
      A G hC halpha hAlpha hbaseAbsorb tail hshift
  have hcoordFintype : A.coordFintype = sourceInst := Subsingleton.elim _ _
  rw [hcoordFintype] at hgood
  have hgoodS :
      sourceTruncatedProfileMeasure m S.profile
        ((sourceProfileQEvent m (sourceAlphaIntervalCount m alpha) S.profile
            (geometricThreshold (Real.log (m : ℝ) ^ 2)
              (sourceLemma411GrowthFactor cWindow)
              (sourceAlphaIntervalCount m alpha)) ∩ R.D) \
          sourceProfileThetaUpTo cWindow m
            (sourceAlphaIntervalCount m alpha) S.profile) ≤ tail := by
    change sourceTruncatedProfileMeasure m S.profile
      ((sourceProfileQEvent m (sourceAlphaIntervalCount m alpha) S.profile
          (geometricThreshold (Real.log (m : ℝ) ^ 2)
            (sourceLemma411GrowthFactor cWindow)
            (sourceAlphaIntervalCount m alpha)) ∩ R.D) \
        sourceProfileThetaUpTo cWindow m
          (sourceAlphaIntervalCount m alpha) S.profile) ≤ tail at hgood
    exact hgood
  apply stoppedProfileGoodEvent_local_bound S.profile S.pathAtom failure
    thetaPath (fun s ↦ (S.lazyVector s, S.nextDirection s))
    (sourceProfileQEvent m (sourceAlphaIntervalCount m alpha) S.profile
        (geometricThreshold (Real.log (m : ℝ) ^ 2)
          (sourceLemma411GrowthFactor cWindow)
          (sourceAlphaIntervalCount m alpha)) ∩ R.D)
    (sourceProfileThetaUpTo cWindow m
      (sourceAlphaIntervalCount m alpha) S.profile)
    (S.measurable_lazyVector.prodMk S.measurable_nextDirection)
    S.map_law hfailure htheta tail hgoodS

end PrimedColumnWinnerSource

/-- One forward terminal atom in the theta-free good-band decomposition. -/
structure ForwardColumnGoodBandAtomData
    (cWindow m : ℕ) (C alpha : ℝ)
    (failure thetaPath : Set Path) where
  source : ForwardColumnWinnerSource m
  remaining : Equation447CodedProfileData cWindow m C source.profile
  failure_subset : failure ∩ source.pathAtom ⊆
    (fun s ↦ (source.lazyVector s, source.nextDirection s)) ⁻¹'
      (((sourceProfileQEvent m (sourceAlphaIntervalCount m alpha)
          source.profile
          (geometricThreshold (Real.log (m : ℝ) ^ 2)
            (sourceLemma411GrowthFactor cWindow)
            (sourceAlphaIntervalCount m alpha)) ∩ remaining.D)) ×ˢ
        (Set.univ : Set Direction))
  theta_subset : (failure ∩ source.pathAtom) ∩
    (fun s ↦ (source.lazyVector s, source.nextDirection s)) ⁻¹'
      (sourceProfileThetaUpTo cWindow m
          (sourceAlphaIntervalCount m alpha) source.profile ×ˢ
        (Set.univ : Set Direction)) ⊆ thetaPath

/-- Reuse the forward column's branch equation-(4.47) law in its
Proposition-4.8 atom.  The source must still identify the particular
candidate-band and global-Theta events. -/
noncomputable def ForwardColumnGoodBandAtomData.ofBranchRemaining
    {cWindow m : ℕ} {C alpha rho : ℝ}
    {failure thetaPath branchFailure branchTheta : Set Path}
    (source : ForwardColumnWinnerSource m)
    (R : Equation447CodedBranchRemainingData cWindow m C rho
      branchFailure branchTheta source.pathAtom source.profile
      source.lazyVector source.nextDirection)
    (hfailure : failure ∩ source.pathAtom ⊆
      (fun s ↦ (source.lazyVector s, source.nextDirection s)) ⁻¹'
        (((sourceProfileQEvent m (sourceAlphaIntervalCount m alpha)
            source.profile
            (geometricThreshold (Real.log (m : ℝ) ^ 2)
              (sourceLemma411GrowthFactor cWindow)
              (sourceAlphaIntervalCount m alpha)) ∩ R.D)) ×ˢ
          (Set.univ : Set Direction)))
    (htheta : (failure ∩ source.pathAtom) ∩
      (fun s ↦ (source.lazyVector s, source.nextDirection s)) ⁻¹'
        (sourceProfileThetaUpTo cWindow m
            (sourceAlphaIntervalCount m alpha) source.profile ×ˢ
          (Set.univ : Set Direction)) ⊆ thetaPath) :
    ForwardColumnGoodBandAtomData cWindow m C alpha failure thetaPath where
  source := source
  remaining := R.toProfileData
  failure_subset := hfailure
  theta_subset := htheta

structure ForwardColumnGoodBandDecomposition
    (cWindow m : ℕ) (C alpha : ℝ)
    (failure thetaPath : Set Path) where
  atoms : ℕ → ForwardColumnGoodBandAtomData cWindow m C alpha
    failure thetaPath
  cover : failure ⊆ ⋃ n, (atoms n).source.pathAtom
  pairwise_disjoint : Pairwise fun n l ↦
    Disjoint (atoms n).source.pathAtom (atoms l).source.pathAtom

theorem measure_diff_le_of_forwardColumnGoodBandDecomposition
    {cWindow m : ℕ} {C cBase alpha : ℝ}
    {failure thetaPath : Set Path}
    (D : ForwardColumnGoodBandDecomposition cWindow m C alpha
      failure thetaPath)
    (G : SourceProp48NumericalAt cWindow m cBase 1 1)
    (hC : 0 < C)
    (halpha : kappaOne ≤ alpha) (hAlpha : alpha ≤ (4 : ℝ) / 5)
    (hbaseAbsorb :
      let d := Real.log ((C + 1) / C)
      let K := (1 - Real.exp (-d))⁻¹
      4 * (Real.exp (-d *
          (Nat.ceil (Real.log (m : ℝ) ^ 2) : ℝ)) * K) ≤
        Real.exp (-(cBase * Real.log (m : ℝ) ^ 2)))
    (tail : ℝ≥0∞)
    (hshift : ENNReal.ofReal (Real.exp (-(min cBase
      (imbalanceRate
        (Real.exp (sourceAdjacentComparisonExponent cWindow))) / 2) *
          Real.log (m : ℝ) ^ 2)) ≤ tail) :
    simpleRandomWalkLaw (failure \ thetaPath) ≤ tail := by
  apply measure_diff_le_of_disjoint_stopped_atoms
    (fun n ↦ (D.atoms n).source.pathAtom) tail D.cover D.pairwise_disjoint
  · intro n
    exact (D.atoms n).source.measurableSet_pathAtom
  · intro n
    exact (D.atoms n).source.prop48_good_band_local_bound cWindow
      (D.atoms n).remaining G hC halpha hAlpha
      (D.atoms n).failure_subset (D.atoms n).theta_subset hbaseAbsorb
      tail hshift

/-- Backward-terminal theta-free good-band atom. -/
structure PrimedColumnGoodBandAtomData
    (cWindow m : ℕ) (C alpha : ℝ)
    (failure thetaPath : Set Path) where
  source : PrimedColumnWinnerSource m
  remaining : Equation447CodedProfileData cWindow m C source.profile
  failure_subset : failure ∩ source.pathAtom ⊆
    (fun s ↦ (source.lazyVector s, source.nextDirection s)) ⁻¹'
      (((sourceProfileQEvent m (sourceAlphaIntervalCount m alpha)
          source.profile
          (geometricThreshold (Real.log (m : ℝ) ^ 2)
            (sourceLemma411GrowthFactor cWindow)
            (sourceAlphaIntervalCount m alpha)) ∩ remaining.D)) ×ˢ
        (Set.univ : Set Direction))
  theta_subset : (failure ∩ source.pathAtom) ∩
    (fun s ↦ (source.lazyVector s, source.nextDirection s)) ⁻¹'
      (sourceProfileThetaUpTo cWindow m
          (sourceAlphaIntervalCount m alpha) source.profile ×ˢ
        (Set.univ : Set Direction)) ⊆ thetaPath

/-- Reuse the backward column's branch equation-(4.47) law in its
Proposition-4.8 atom. -/
noncomputable def PrimedColumnGoodBandAtomData.ofBranchRemaining
    {cWindow m : ℕ} {C alpha rho : ℝ}
    {failure thetaPath branchFailure branchTheta : Set Path}
    (source : PrimedColumnWinnerSource m)
    (R : Equation447CodedBranchRemainingData cWindow m C rho
      branchFailure branchTheta source.pathAtom source.profile
      source.lazyVector source.nextDirection)
    (hfailure : failure ∩ source.pathAtom ⊆
      (fun s ↦ (source.lazyVector s, source.nextDirection s)) ⁻¹'
        (((sourceProfileQEvent m (sourceAlphaIntervalCount m alpha)
            source.profile
            (geometricThreshold (Real.log (m : ℝ) ^ 2)
              (sourceLemma411GrowthFactor cWindow)
              (sourceAlphaIntervalCount m alpha)) ∩ R.D)) ×ˢ
          (Set.univ : Set Direction)))
    (htheta : (failure ∩ source.pathAtom) ∩
      (fun s ↦ (source.lazyVector s, source.nextDirection s)) ⁻¹'
        (sourceProfileThetaUpTo cWindow m
            (sourceAlphaIntervalCount m alpha) source.profile ×ˢ
          (Set.univ : Set Direction)) ⊆ thetaPath) :
    PrimedColumnGoodBandAtomData cWindow m C alpha failure thetaPath where
  source := source
  remaining := R.toProfileData
  failure_subset := hfailure
  theta_subset := htheta

structure PrimedColumnGoodBandDecomposition
    (cWindow m : ℕ) (C alpha : ℝ)
    (failure thetaPath : Set Path) where
  atoms : ℕ → PrimedColumnGoodBandAtomData cWindow m C alpha
    failure thetaPath
  cover : failure ⊆ ⋃ n, (atoms n).source.pathAtom
  pairwise_disjoint : Pairwise fun n l ↦
    Disjoint (atoms n).source.pathAtom (atoms l).source.pathAtom

theorem measure_diff_le_of_primedColumnGoodBandDecomposition
    {cWindow m : ℕ} {C cBase alpha : ℝ}
    {failure thetaPath : Set Path}
    (D : PrimedColumnGoodBandDecomposition cWindow m C alpha
      failure thetaPath)
    (G : SourceProp48NumericalAt cWindow m cBase 1 1)
    (hC : 0 < C)
    (halpha : kappaOne ≤ alpha) (hAlpha : alpha ≤ (4 : ℝ) / 5)
    (hbaseAbsorb :
      let d := Real.log ((C + 1) / C)
      let K := (1 - Real.exp (-d))⁻¹
      4 * (Real.exp (-d *
          (Nat.ceil (Real.log (m : ℝ) ^ 2) : ℝ)) * K) ≤
        Real.exp (-(cBase * Real.log (m : ℝ) ^ 2)))
    (tail : ℝ≥0∞)
    (hshift : ENNReal.ofReal (Real.exp (-(min cBase
      (imbalanceRate
        (Real.exp (sourceAdjacentComparisonExponent cWindow))) / 2) *
          Real.log (m : ℝ) ^ 2)) ≤ tail) :
    simpleRandomWalkLaw (failure \ thetaPath) ≤ tail := by
  apply measure_diff_le_of_disjoint_stopped_atoms
    (fun n ↦ (D.atoms n).source.pathAtom) tail D.cover D.pairwise_disjoint
  · intro n
    exact (D.atoms n).source.measurableSet_pathAtom
  · intro n
    exact (D.atoms n).source.prop48_good_band_local_bound cWindow
      (D.atoms n).remaining G hC halpha hAlpha
      (D.atoms n).failure_subset (D.atoms n).theta_subset hbaseAbsorb
      tail hshift

/-! ## Source-banded Proposition-4.8 atoms

Unlike the legacy theta-free records above, these inputs do not remove one
global Proposition-4.5 event.  Each stopped terminal atom instead carries the
literal arbitrary-endpoint Proposition-4.5 input for every recursive profile
interval.  The checked stopped product law then pays the good profile part and
the interval inputs pay the exceptional profile bands. -/

private theorem ForwardColumnWinnerSource.prop48_good_profile_bound
    {cWindow m : ℕ} (S : ForwardColumnWinnerSource m)
    {C cBase alpha : ℝ}
    (R : Equation447CodedProfileData cWindow m C S.profile)
    (G : SourceProp48NumericalAt cWindow m cBase 1 1)
    (hC : 0 < C) (halpha : kappaOne ≤ alpha)
    (hAlpha : alpha ≤ (4 : ℝ) / 5)
    (hbaseAbsorb :
      let d := Real.log ((C + 1) / C)
      let K := (1 - Real.exp (-d))⁻¹
      4 * (Real.exp (-d *
          (Nat.ceil (Real.log (m : ℝ) ^ 2) : ℝ)) * K) ≤
        Real.exp (-(cBase * Real.log (m : ℝ) ^ 2)))
    (tail : ℝ≥0∞)
    (hshift : ENNReal.ofReal (Real.exp (-(min cBase
      (imbalanceRate
        (Real.exp (sourceAdjacentComparisonExponent cWindow))) / 2) *
          Real.log (m : ℝ) ^ 2)) ≤ tail) :
    sourceTruncatedProfileMeasure m S.profile
      ((sourceProfileQEvent m (sourceAlphaIntervalCount m alpha) S.profile
          (geometricThreshold (Real.log (m : ℝ) ^ 2)
            (sourceLemma411GrowthFactor cWindow)
            (sourceAlphaIntervalCount m alpha)) ∩ R.D) \
        sourceProfileThetaUpTo cWindow m
          (sourceAlphaIntervalCount m alpha) S.profile) ≤ tail := by
  let sourceInst : Fintype S.Coord := inferInstance
  letI : Fintype S.Coord := sourceInst
  let A := S.toStoppedEquation447BranchAtom cWindow C
    (Real.log (m : ℝ) ^ 2) ∅
      (R.toRemainingData S.pathAtom S.lazyVector S.nextDirection)
  have hgood := stoppedEquation447BranchAtom_prop48_good_band_bound_at_ennreal
    A G hC halpha hAlpha hbaseAbsorb tail hshift
  have hcoordFintype : A.coordFintype = sourceInst := Subsingleton.elim _ _
  rw [hcoordFintype] at hgood
  change sourceTruncatedProfileMeasure m S.profile
    ((sourceProfileQEvent m (sourceAlphaIntervalCount m alpha) S.profile
        (geometricThreshold (Real.log (m : ℝ) ^ 2)
          (sourceLemma411GrowthFactor cWindow)
          (sourceAlphaIntervalCount m alpha)) ∩ R.D) \
      sourceProfileThetaUpTo cWindow m
        (sourceAlphaIntervalCount m alpha) S.profile) ≤ tail at hgood
  exact hgood

private theorem PrimedColumnWinnerSource.prop48_good_profile_bound
    {cWindow m : ℕ} (S : PrimedColumnWinnerSource m)
    {C cBase alpha : ℝ}
    (R : Equation447CodedProfileData cWindow m C S.profile)
    (G : SourceProp48NumericalAt cWindow m cBase 1 1)
    (hC : 0 < C) (halpha : kappaOne ≤ alpha)
    (hAlpha : alpha ≤ (4 : ℝ) / 5)
    (hbaseAbsorb :
      let d := Real.log ((C + 1) / C)
      let K := (1 - Real.exp (-d))⁻¹
      4 * (Real.exp (-d *
          (Nat.ceil (Real.log (m : ℝ) ^ 2) : ℝ)) * K) ≤
        Real.exp (-(cBase * Real.log (m : ℝ) ^ 2)))
    (tail : ℝ≥0∞)
    (hshift : ENNReal.ofReal (Real.exp (-(min cBase
      (imbalanceRate
        (Real.exp (sourceAdjacentComparisonExponent cWindow))) / 2) *
          Real.log (m : ℝ) ^ 2)) ≤ tail) :
    sourceTruncatedProfileMeasure m S.profile
      ((sourceProfileQEvent m (sourceAlphaIntervalCount m alpha) S.profile
          (geometricThreshold (Real.log (m : ℝ) ^ 2)
            (sourceLemma411GrowthFactor cWindow)
            (sourceAlphaIntervalCount m alpha)) ∩ R.D) \
        sourceProfileThetaUpTo cWindow m
          (sourceAlphaIntervalCount m alpha) S.profile) ≤ tail := by
  let sourceInst : Fintype S.Coord := inferInstance
  letI : Fintype S.Coord := sourceInst
  let A := S.toStoppedEquation447BranchAtom cWindow C
    (Real.log (m : ℝ) ^ 2) ∅
      (R.toRemainingData S.pathAtom S.lazyVector S.nextDirection)
  have hgood := stoppedEquation447BranchAtom_prop48_good_band_bound_at_ennreal
    A G hC halpha hAlpha hbaseAbsorb tail hshift
  have hcoordFintype : A.coordFintype = sourceInst := Subsingleton.elim _ _
  rw [hcoordFintype] at hgood
  change sourceTruncatedProfileMeasure m S.profile
    ((sourceProfileQEvent m (sourceAlphaIntervalCount m alpha) S.profile
        (geometricThreshold (Real.log (m : ℝ) ^ 2)
          (sourceLemma411GrowthFactor cWindow)
          (sourceAlphaIntervalCount m alpha)) ∩ R.D) \
      sourceProfileThetaUpTo cWindow m
        (sourceAlphaIntervalCount m alpha) S.profile) ≤ tail at hgood
  exact hgood

structure ForwardColumnSourceBandedGoodBandAtomData
    (cWindow m : ℕ) (C alpha : ℝ) (failure : Set Path) where
  source : ForwardColumnWinnerSource m
  remaining : Equation447CodedProfileData cWindow m C source.profile
  failure_subset : failure ∩ source.pathAtom ⊆
    (fun s ↦ (source.lazyVector s, source.nextDirection s)) ⁻¹'
      (((sourceProfileQEvent m (sourceAlphaIntervalCount m alpha)
          source.profile
          (geometricThreshold (Real.log (m : ℝ) ^ 2)
            (sourceLemma411GrowthFactor cWindow)
            (sourceAlphaIntervalCount m alpha)) ∩ remaining.D)) ×ˢ
        (Set.univ : Set Direction))
  bands : StoppedProfileBandedThetaInputs cWindow m source.k alpha
    source.profile source.pathAtom failure
      (fun s ↦ (source.lazyVector s, source.nextDirection s))

structure PrimedColumnSourceBandedGoodBandAtomData
    (cWindow m : ℕ) (C alpha : ℝ) (failure : Set Path) where
  source : PrimedColumnWinnerSource m
  remaining : Equation447CodedProfileData cWindow m C source.profile
  failure_subset : failure ∩ source.pathAtom ⊆
    (fun s ↦ (source.lazyVector s, source.nextDirection s)) ⁻¹'
      (((sourceProfileQEvent m (sourceAlphaIntervalCount m alpha)
          source.profile
          (geometricThreshold (Real.log (m : ℝ) ^ 2)
            (sourceLemma411GrowthFactor cWindow)
            (sourceAlphaIntervalCount m alpha)) ∩ remaining.D)) ×ˢ
        (Set.univ : Set Direction))
  bands : StoppedProfileBandedThetaInputs cWindow m source.k alpha
    source.profile source.pathAtom failure
      (fun s ↦ (source.lazyVector s, source.nextDirection s))

theorem ForwardColumnSourceBandedGoodBandAtomData.local_bound
    {cWindow m : ℕ} {C cBase alpha : ℝ} {failure : Set Path}
    (D : ForwardColumnSourceBandedGoodBandAtomData
      cWindow m C alpha failure)
    (G : SourceProp48NumericalAt cWindow m cBase 1 1)
    (hC : 0 < C) (halpha : kappaOne ≤ alpha)
    (hAlpha : alpha ≤ (4 : ℝ) / 5)
    (hscales : ∀ l : Fin (sourceAlphaIntervalCount m alpha),
      SourceIntervalScale m (sourceIntervalLower m (l.1 + 1)) ∧
        SourceUpperScale m (sourceThetaIntervalUpper m (l.1 + 1)))
    (hbaseAbsorb :
      let d := Real.log ((C + 1) / C)
      let K := (1 - Real.exp (-d))⁻¹
      4 * (Real.exp (-d *
          (Nat.ceil (Real.log (m : ℝ) ^ 2) : ℝ)) * K) ≤
        Real.exp (-(cBase * Real.log (m : ℝ) ^ 2)))
    (tail : ℝ≥0∞)
    (hshift : ENNReal.ofReal (Real.exp (-(min cBase
      (imbalanceRate
        (Real.exp (sourceAdjacentComparisonExponent cWindow))) / 2) *
          Real.log (m : ℝ) ^ 2)) ≤ tail) :
    simpleRandomWalkLaw (failure ∩ D.source.pathAtom) ≤
      (tail + (sourceAlphaIntervalCount m alpha : ℝ≥0∞) *
        sourceProp45FourBranchError m) *
          simpleRandomWalkLaw D.source.pathAtom := by
  apply stoppedProfileEvent_local_bound_of_source_banded_theta
    D.source.profile D.source.pathAtom failure
    (fun s ↦ (D.source.lazyVector s, D.source.nextDirection s))
    (sourceProfileQEvent m (sourceAlphaIntervalCount m alpha) D.source.profile
      (geometricThreshold (Real.log (m : ℝ) ^ 2)
        (sourceLemma411GrowthFactor cWindow)
        (sourceAlphaIntervalCount m alpha)) ∩ D.remaining.D)
    D.bands hscales
    (D.source.measurable_lazyVector.prodMk D.source.measurable_nextDirection)
    D.source.map_law D.failure_subset tail
  exact D.source.prop48_good_profile_bound D.remaining G hC halpha hAlpha
    hbaseAbsorb tail hshift

theorem PrimedColumnSourceBandedGoodBandAtomData.local_bound
    {cWindow m : ℕ} {C cBase alpha : ℝ} {failure : Set Path}
    (D : PrimedColumnSourceBandedGoodBandAtomData
      cWindow m C alpha failure)
    (G : SourceProp48NumericalAt cWindow m cBase 1 1)
    (hC : 0 < C) (halpha : kappaOne ≤ alpha)
    (hAlpha : alpha ≤ (4 : ℝ) / 5)
    (hscales : ∀ l : Fin (sourceAlphaIntervalCount m alpha),
      SourceIntervalScale m (sourceIntervalLower m (l.1 + 1)) ∧
        SourceUpperScale m (sourceThetaIntervalUpper m (l.1 + 1)))
    (hbaseAbsorb :
      let d := Real.log ((C + 1) / C)
      let K := (1 - Real.exp (-d))⁻¹
      4 * (Real.exp (-d *
          (Nat.ceil (Real.log (m : ℝ) ^ 2) : ℝ)) * K) ≤
        Real.exp (-(cBase * Real.log (m : ℝ) ^ 2)))
    (tail : ℝ≥0∞)
    (hshift : ENNReal.ofReal (Real.exp (-(min cBase
      (imbalanceRate
        (Real.exp (sourceAdjacentComparisonExponent cWindow))) / 2) *
          Real.log (m : ℝ) ^ 2)) ≤ tail) :
    simpleRandomWalkLaw (failure ∩ D.source.pathAtom) ≤
      (tail + (sourceAlphaIntervalCount m alpha : ℝ≥0∞) *
        sourceProp45FourBranchError m) *
          simpleRandomWalkLaw D.source.pathAtom := by
  apply stoppedProfileEvent_local_bound_of_source_banded_theta
    D.source.profile D.source.pathAtom failure
    (fun s ↦ (D.source.lazyVector s, D.source.nextDirection s))
    (sourceProfileQEvent m (sourceAlphaIntervalCount m alpha) D.source.profile
      (geometricThreshold (Real.log (m : ℝ) ^ 2)
        (sourceLemma411GrowthFactor cWindow)
        (sourceAlphaIntervalCount m alpha)) ∩ D.remaining.D)
    D.bands hscales
    (D.source.measurable_lazyVector.prodMk D.source.measurable_nextDirection)
    D.source.map_law D.failure_subset tail
  exact D.source.prop48_good_profile_bound D.remaining G hC halpha hAlpha
    hbaseAbsorb tail hshift

structure ForwardColumnSourceBandedGoodBandDecomposition
    (cWindow m : ℕ) (C alpha : ℝ) (target : Set Path) where
  atoms : ℕ → ForwardColumnSourceBandedGoodBandAtomData
    cWindow m C alpha target
  cover : target ⊆ ⋃ n, (atoms n).source.pathAtom
  pairwise_disjoint : Pairwise fun n l ↦
    Disjoint (atoms n).source.pathAtom (atoms l).source.pathAtom

structure PrimedColumnSourceBandedGoodBandDecomposition
    (cWindow m : ℕ) (C alpha : ℝ) (target : Set Path) where
  atoms : ℕ → PrimedColumnSourceBandedGoodBandAtomData
    cWindow m C alpha target
  cover : target ⊆ ⋃ n, (atoms n).source.pathAtom
  pairwise_disjoint : Pairwise fun n l ↦
    Disjoint (atoms n).source.pathAtom (atoms l).source.pathAtom

private theorem measure_le_of_disjoint_column_source_banded_atoms
    {failure : Set Path}
    (atom : ℕ → Set Path) (tail : ℝ≥0∞)
    (cover : failure ⊆ ⋃ n, atom n)
    (pairwise_disjoint : Pairwise fun n l ↦ Disjoint (atom n) (atom l))
    (measurable_atom : ∀ n, MeasurableSet (atom n))
    (local_bound : ∀ n, simpleRandomWalkLaw (failure ∩ atom n) ≤
      tail * simpleRandomWalkLaw (atom n)) :
    simpleRandomWalkLaw failure ≤ tail := by
  apply fixed_cardinality_of_disjoint_path_witnesses simpleRandomWalkLaw
    failure (fun n ↦ failure ∩ atom n) atom tail
  · intro omega homega
    rcases Set.mem_iUnion.mp (cover homega) with ⟨n, hn⟩
    exact Set.mem_iUnion.mpr ⟨n, homega, hn⟩
  · exact local_bound
  · exact pairwise_disjoint
  · exact measurable_atom

theorem ForwardColumnSourceBandedGoodBandDecomposition.measure_le
    {cWindow m : ℕ} {C cBase alpha : ℝ} {target : Set Path}
    (D : ForwardColumnSourceBandedGoodBandDecomposition
      cWindow m C alpha target)
    (G : SourceProp48NumericalAt cWindow m cBase 1 1)
    (hC : 0 < C) (halpha : kappaOne ≤ alpha)
    (hAlpha : alpha ≤ (4 : ℝ) / 5)
    (hscales : ∀ l : Fin (sourceAlphaIntervalCount m alpha),
      SourceIntervalScale m (sourceIntervalLower m (l.1 + 1)) ∧
        SourceUpperScale m (sourceThetaIntervalUpper m (l.1 + 1)))
    (hbaseAbsorb :
      let d := Real.log ((C + 1) / C)
      let K := (1 - Real.exp (-d))⁻¹
      4 * (Real.exp (-d *
          (Nat.ceil (Real.log (m : ℝ) ^ 2) : ℝ)) * K) ≤
        Real.exp (-(cBase * Real.log (m : ℝ) ^ 2)))
    (tail : ℝ≥0∞)
    (hshift : ENNReal.ofReal (Real.exp (-(min cBase
      (imbalanceRate
        (Real.exp (sourceAdjacentComparisonExponent cWindow))) / 2) *
          Real.log (m : ℝ) ^ 2)) ≤ tail) :
    simpleRandomWalkLaw target ≤
      tail + (sourceAlphaIntervalCount m alpha : ℝ≥0∞) *
        sourceProp45FourBranchError m := by
  apply measure_le_of_disjoint_column_source_banded_atoms
    (fun n ↦ (D.atoms n).source.pathAtom)
    (tail + (sourceAlphaIntervalCount m alpha : ℝ≥0∞) *
      sourceProp45FourBranchError m)
    D.cover D.pairwise_disjoint
  · intro n
    exact (D.atoms n).source.measurableSet_pathAtom
  · intro n
    exact (D.atoms n).local_bound G hC halpha hAlpha hscales
      hbaseAbsorb tail hshift

theorem PrimedColumnSourceBandedGoodBandDecomposition.measure_le
    {cWindow m : ℕ} {C cBase alpha : ℝ} {target : Set Path}
    (D : PrimedColumnSourceBandedGoodBandDecomposition
      cWindow m C alpha target)
    (G : SourceProp48NumericalAt cWindow m cBase 1 1)
    (hC : 0 < C) (halpha : kappaOne ≤ alpha)
    (hAlpha : alpha ≤ (4 : ℝ) / 5)
    (hscales : ∀ l : Fin (sourceAlphaIntervalCount m alpha),
      SourceIntervalScale m (sourceIntervalLower m (l.1 + 1)) ∧
        SourceUpperScale m (sourceThetaIntervalUpper m (l.1 + 1)))
    (hbaseAbsorb :
      let d := Real.log ((C + 1) / C)
      let K := (1 - Real.exp (-d))⁻¹
      4 * (Real.exp (-d *
          (Nat.ceil (Real.log (m : ℝ) ^ 2) : ℝ)) * K) ≤
        Real.exp (-(cBase * Real.log (m : ℝ) ^ 2)))
    (tail : ℝ≥0∞)
    (hshift : ENNReal.ofReal (Real.exp (-(min cBase
      (imbalanceRate
        (Real.exp (sourceAdjacentComparisonExponent cWindow))) / 2) *
          Real.log (m : ℝ) ^ 2)) ≤ tail) :
    simpleRandomWalkLaw target ≤
      tail + (sourceAlphaIntervalCount m alpha : ℝ≥0∞) *
        sourceProp45FourBranchError m := by
  apply measure_le_of_disjoint_column_source_banded_atoms
    (fun n ↦ (D.atoms n).source.pathAtom)
    (tail + (sourceAlphaIntervalCount m alpha : ℝ≥0∞) *
      sourceProp45FourBranchError m)
    D.cover D.pairwise_disjoint
  · intro n
    exact (D.atoms n).source.measurableSet_pathAtom
  · intro n
    exact (D.atoms n).local_bound G hC halpha hAlpha hscales
      hbaseAbsorb tail hshift

/-- Proposition-4.8 evidence on one forward terminal phase atom.  The
`base_bound` and `theta_bound` fields are retained as branch-local analytic
evidence for the Lemma-4.10 consumer; neither is silently promoted to a
global estimate. -/
structure ForwardColumnProp48Evidence
    (cWindow m : ℕ) (alpha cBase cTheta thetaPower : ℝ)
    (failure : Set Path) where
  source : ForwardColumnWinnerSource m
  failure_subset : failure ∩ source.pathAtom ⊆ source.lazyVector ⁻¹'
    sourceProfileQEvent m (sourceAlphaIntervalCount m alpha) source.profile
      (geometricThreshold (Real.log (m : ℝ) ^ 2)
        (sourceLemma411GrowthFactor cWindow)
        (sourceAlphaIntervalCount m alpha))
  base_bound :
    (sourceTruncatedProfileMeasure m source.profile).real
      (sourceProfileQEvent m 1 source.profile (Real.log (m : ℝ) ^ 2)) ≤
        Real.exp (-cBase * Real.log (m : ℝ) ^ 2)
  theta_bound : ∀ l, 2 ≤ l → l ≤ sourceAlphaIntervalCount m alpha →
    (sourceTruncatedProfileMeasure m source.profile).real
      (sourceProfileThetaBad cWindow m l source.profile) ≤
        Real.exp (-cTheta * (m : ℝ) ^ thetaPower)

/-- Proposition-4.8 evidence on one backward terminal phase atom of the same
`Y` branch. -/
structure PrimedColumnProp48Evidence
    (cWindow m : ℕ) (alpha cBase cTheta thetaPower : ℝ)
    (failure : Set Path) where
  source : PrimedColumnWinnerSource m
  failure_subset : failure ∩ source.pathAtom ⊆ source.lazyVector ⁻¹'
    sourceProfileQEvent m (sourceAlphaIntervalCount m alpha) source.profile
      (geometricThreshold (Real.log (m : ℝ) ^ 2)
        (sourceLemma411GrowthFactor cWindow)
        (sourceAlphaIntervalCount m alpha))
  base_bound :
    (sourceTruncatedProfileMeasure m source.profile).real
      (sourceProfileQEvent m 1 source.profile (Real.log (m : ℝ) ^ 2)) ≤
        Real.exp (-cBase * Real.log (m : ℝ) ^ 2)
  theta_bound : ∀ l, 2 ≤ l → l ≤ sourceAlphaIntervalCount m alpha →
    (sourceTruncatedProfileMeasure m source.profile).real
      (sourceProfileThetaBad cWindow m l source.profile) ≤
        Real.exp (-cTheta * (m : ℝ) ^ thetaPower)

theorem ForwardColumnProp48Evidence.local_bound
    {cWindow m : ℕ} {alpha cBase cTheta thetaPower : ℝ}
    {failure : Set Path}
    (E : ForwardColumnProp48Evidence cWindow m alpha cBase cTheta
      thetaPower failure)
    (tail : ℝ≥0∞)
    (hProp48 :
      sourceTruncatedProfileMeasure m E.source.profile
        (sourceProfileQEvent m (sourceAlphaIntervalCount m alpha)
          E.source.profile
          (geometricThreshold (Real.log (m : ℝ) ^ 2)
            (sourceLemma411GrowthFactor cWindow)
            (sourceAlphaIntervalCount m alpha))) ≤ tail) :
    simpleRandomWalkLaw (failure ∩ E.source.pathAtom) ≤
      tail * simpleRandomWalkLaw E.source.pathAtom := by
  exact columnTerminalProfileEvent_local_bound E.source.profile
    E.source.lazyVector E.source.nextDirection E.source.measurable_lazyVector
    E.source.measurable_nextDirection E.source.map_law E.failure_subset tail
    hProp48

theorem PrimedColumnProp48Evidence.local_bound
    {cWindow m : ℕ} {alpha cBase cTheta thetaPower : ℝ}
    {failure : Set Path}
    (E : PrimedColumnProp48Evidence cWindow m alpha cBase cTheta
      thetaPower failure)
    (tail : ℝ≥0∞)
    (hProp48 :
      sourceTruncatedProfileMeasure m E.source.profile
        (sourceProfileQEvent m (sourceAlphaIntervalCount m alpha)
          E.source.profile
          (geometricThreshold (Real.log (m : ℝ) ^ 2)
            (sourceLemma411GrowthFactor cWindow)
            (sourceAlphaIntervalCount m alpha))) ≤ tail) :
    simpleRandomWalkLaw (failure ∩ E.source.pathAtom) ≤
      tail * simpleRandomWalkLaw E.source.pathAtom := by
  exact columnTerminalProfileEvent_local_bound E.source.profile
    E.source.lazyVector E.source.nextDirection E.source.measurable_lazyVector
    E.source.measurable_nextDirection E.source.map_law E.failure_subset tail
    hProp48

/-- A disjoint, branch-local decomposition of the forward terminal phase.
It deliberately makes no claim about the other phase, `Y'`, or the planar
failure event. -/
structure ForwardColumnStoppedCandidateDecomposition
    (cWindow m : ℕ) (alpha cBase cTheta thetaPower : ℝ)
    (failure : Set Path) where
  atoms : ℕ → ForwardColumnProp48Evidence cWindow m alpha cBase cTheta
    thetaPower failure
  cover : failure ⊆ ⋃ n, (atoms n).source.pathAtom
  pairwise_disjoint : Pairwise fun n l ↦
    Disjoint (atoms n).source.pathAtom (atoms l).source.pathAtom

/-- The analogous branch-local decomposition of the backward terminal phase
of `Y`. -/
structure PrimedColumnStoppedCandidateDecomposition
    (cWindow m : ℕ) (alpha cBase cTheta thetaPower : ℝ)
    (failure : Set Path) where
  atoms : ℕ → PrimedColumnProp48Evidence cWindow m alpha cBase cTheta
    thetaPower failure
  cover : failure ⊆ ⋃ n, (atoms n).source.pathAtom
  pairwise_disjoint : Pairwise fun n l ↦
    Disjoint (atoms n).source.pathAtom (atoms l).source.pathAtom

theorem measure_failure_le_of_forwardColumnStoppedCandidateDecomposition
    {cWindow m : ℕ} {alpha cBase cTheta thetaPower : ℝ}
    {failure : Set Path}
    (D : ForwardColumnStoppedCandidateDecomposition cWindow m alpha cBase
      cTheta thetaPower failure)
    (tail : ℝ≥0∞)
    (hProp48 : ∀ n,
      sourceTruncatedProfileMeasure m (D.atoms n).source.profile
        (sourceProfileQEvent m (sourceAlphaIntervalCount m alpha)
          (D.atoms n).source.profile
          (geometricThreshold (Real.log (m : ℝ) ^ 2)
            (sourceLemma411GrowthFactor cWindow)
            (sourceAlphaIntervalCount m alpha))) ≤ tail) :
    simpleRandomWalkLaw failure ≤ tail := by
  apply fixed_cardinality_of_disjoint_path_witnesses simpleRandomWalkLaw
    failure (fun n ↦ failure ∩ (D.atoms n).source.pathAtom)
      (fun n ↦ (D.atoms n).source.pathAtom) tail
  · intro s hs
    rcases Set.mem_iUnion.mp (D.cover hs) with ⟨n, hn⟩
    exact Set.mem_iUnion.mpr ⟨n, hs, hn⟩
  · intro n
    exact (D.atoms n).local_bound tail (hProp48 n)
  · exact D.pairwise_disjoint
  · intro n
    exact (D.atoms n).source.measurableSet_pathAtom

theorem measure_failure_le_of_primedColumnStoppedCandidateDecomposition
    {cWindow m : ℕ} {alpha cBase cTheta thetaPower : ℝ}
    {failure : Set Path}
    (D : PrimedColumnStoppedCandidateDecomposition cWindow m alpha cBase
      cTheta thetaPower failure)
    (tail : ℝ≥0∞)
    (hProp48 : ∀ n,
      sourceTruncatedProfileMeasure m (D.atoms n).source.profile
        (sourceProfileQEvent m (sourceAlphaIntervalCount m alpha)
          (D.atoms n).source.profile
          (geometricThreshold (Real.log (m : ℝ) ^ 2)
            (sourceLemma411GrowthFactor cWindow)
            (sourceAlphaIntervalCount m alpha))) ≤ tail) :
    simpleRandomWalkLaw failure ≤ tail := by
  apply fixed_cardinality_of_disjoint_path_witnesses simpleRandomWalkLaw
    failure (fun n ↦ failure ∩ (D.atoms n).source.pathAtom)
      (fun n ↦ (D.atoms n).source.pathAtom) tail
  · intro s hs
    rcases Set.mem_iUnion.mp (D.cover hs) with ⟨n, hn⟩
    exact Set.mem_iUnion.mpr ⟨n, hs, hn⟩
  · intro n
    exact (D.atoms n).local_bound tail (hProp48 n)
  · exact D.pairwise_disjoint
  · intro n
    exact (D.atoms n).source.measurableSet_pathAtom

/-! ## Reflection only after the two phases have been assembled -/

/-- The complete `Y` branch obtained by adjoining its two independently
conditioned terminal phases. -/
def yTwoPhaseBranchEvent (forwardPhase backwardPhase : Set Path) : Set Path :=
  forwardPhase ∪ backwardPhase

/-- The source-faithful `Y'` branch is the preimage of the assembled `Y`
branch under reflection in the vertical axis.  Reflection is deliberately
not applied to either conditional phase in isolation. -/
def reflectedYPrimeBranchEvent
    (forwardPhase backwardPhase : Set Path) : Set Path :=
  HLOZPairingProfiles.reflectPath ⁻¹'
    yTwoPhaseBranchEvent forwardPhase backwardPhase

theorem measurableSet_yTwoPhaseBranchEvent
    {forwardPhase backwardPhase : Set Path}
    (hf : MeasurableSet forwardPhase) (hb : MeasurableSet backwardPhase) :
    MeasurableSet (yTwoPhaseBranchEvent forwardPhase backwardPhase) :=
  hf.union hb

theorem simpleRandomWalkLaw_reflectedYPrimeBranchEvent_eq
    {forwardPhase backwardPhase : Set Path}
    (hf : MeasurableSet forwardPhase) (hb : MeasurableSet backwardPhase) :
    simpleRandomWalkLaw
        (reflectedYPrimeBranchEvent forwardPhase backwardPhase) =
      simpleRandomWalkLaw
        (yTwoPhaseBranchEvent forwardPhase backwardPhase) := by
  let E := yTwoPhaseBranchEvent forwardPhase backwardPhase
  have hE : MeasurableSet E := measurableSet_yTwoPhaseBranchEvent hf hb
  calc
    simpleRandomWalkLaw
        (reflectedYPrimeBranchEvent forwardPhase backwardPhase) =
      (simpleRandomWalkLaw.map
        HLOZPairingProfiles.reflectPath) E := by
        rw [Measure.map_apply
          HLOZProp47Prop45YColumns.measurable_reflectPath hE]
        rfl
    _ = simpleRandomWalkLaw E := by
      rw [HLOZProp47Prop45YColumns.simpleRandomWalkLaw_map_reflectPath]

theorem reflectedYPrimeBranchEvent_measure_le_of_yTwoPhase
    {forwardPhase backwardPhase : Set Path} {R : ℝ≥0∞}
    (hf : MeasurableSet forwardPhase) (hb : MeasurableSet backwardPhase)
    (hY : simpleRandomWalkLaw
      (yTwoPhaseBranchEvent forwardPhase backwardPhase) ≤ R) :
    simpleRandomWalkLaw
      (reflectedYPrimeBranchEvent forwardPhase backwardPhase) ≤ R := by
  rw [simpleRandomWalkLaw_reflectedYPrimeBranchEvent_eq hf hb]
  exact hY

/-- Assemble the two ordered-history terminal phases before doing anything
with the reflected tiling.  In particular the backward parser phase is
still part of `Y`, not itself the `Y'` event. -/
noncomputable def yOrderedHistoryTwoPhaseBranchEvent
    {m : ℕ} {i : Fin 6} {a : AlphaTriple} {r : StageIndex}
    (forward : ForwardColumnOrderedHistorySource m i a r)
    (backward : PrimedColumnOrderedHistorySource m i a r) : Set Path :=
  yTwoPhaseBranchEvent forward.pathAtom backward.pathAtom

/-- Only the already assembled two-phase `Y` event is transported to the
origin-reflected `Y'` branch. -/
noncomputable def reflectedYPrimeOrderedHistoryBranchEvent
    {m : ℕ} {i : Fin 6} {a : AlphaTriple} {r : StageIndex}
    (forward : ForwardColumnOrderedHistorySource m i a r)
    (backward : PrimedColumnOrderedHistorySource m i a r) : Set Path :=
  reflectedYPrimeBranchEvent forward.pathAtom backward.pathAtom

theorem measurableSet_yOrderedHistoryTwoPhaseBranchEvent
    {m : ℕ} {i : Fin 6} {a : AlphaTriple} {r : StageIndex}
    (forward : ForwardColumnOrderedHistorySource m i a r)
    (backward : PrimedColumnOrderedHistorySource m i a r) :
    MeasurableSet
      (yOrderedHistoryTwoPhaseBranchEvent forward backward) :=
  measurableSet_yTwoPhaseBranchEvent forward.measurableSet_pathAtom
    backward.measurableSet_pathAtom

theorem simpleRandomWalkLaw_reflectedYPrimeOrderedHistoryBranchEvent_eq
    {m : ℕ} {i : Fin 6} {a : AlphaTriple} {r : StageIndex}
    (forward : ForwardColumnOrderedHistorySource m i a r)
    (backward : PrimedColumnOrderedHistorySource m i a r) :
    simpleRandomWalkLaw
        (reflectedYPrimeOrderedHistoryBranchEvent forward backward) =
      simpleRandomWalkLaw
        (yOrderedHistoryTwoPhaseBranchEvent forward backward) := by
  exact simpleRandomWalkLaw_reflectedYPrimeBranchEvent_eq
    forward.measurableSet_pathAtom backward.measurableSet_pathAtom

end Erdos1166.HLOZColumnSourceConsumers
