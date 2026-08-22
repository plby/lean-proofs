/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.HLOZSourceOrientedThetaBalance
import ErdosProblems.Erdos1165.TilingOrientedRetainedDominoEndpoint
import ErdosProblems.Erdos1165.TilingOrientedRetainedSourceLocalTime
import ErdosProblems.Erdos1165.TilingOrientedShellSupportSelector

/-!
# Retained-creation slots for the oriented Theta screen

The site enumeration in Proposition 4.5 must be fixed by the retained word
at the rank-`k` creation clock.  Enumerating the larger Proposition 4.4 set
at a deterministic *physical* cutoff is unsuitable for the stopped product:
changing one pre-creation insertion total changes how far the endpoint chain
has run by that cutoff.  The creation set below is fixed by the deleted
creation word.  On the on-time event it embeds into the deterministic-cutoff
set, so the Proposition 4.4 cardinal budget is unchanged.

The low-external family is likewise enumerated by all compatible represented
bases of the creation word, rather than by physical-time sites.  This is the
trace-local finite carrier used by the one-away-coordinate product split.
-/

open Set

namespace Erdos1165.HLOZSourceOrientedThetaCreationSlots

open ExternalProposition44 HLOZGapEstimate HLOZPathEvents
open HLOZShellZeroReplacementWindows HLOZSourceOrientedExternalLocalTime
open HLOZSourceOrientedThetaBalance HLOZThetaSourceBalance
open LazyDecomposition TilingOrientedRetainedSourceLocalTime
open PathInsertion PreStoppingFiber
open TilingOrientedShellZeroSourcePartition
open TilingOrientedRetainedCoordinateSupport
open TilingOrientedRetainedDominoEndpoint
open TilingOrientedShellSupportSelector
open SpatialInsertionFiber TilingShellZeroSourcePartition
open TilingLazyDecomposition TilingSpatialInsertionFiber
open TilingExternalPhaseSplit
open VariableStoppedTracePartition

noncomputable section

attribute [local instance] Classical.propDecidable

abbrev DominoTiling := Tilings.Tiling

/-- Compatible bases represented by one oriented retained creation word. -/
def orientedThetaCodeBases (t : DominoTiling) (o : Orientation)
    (z : OrientedTilingTypedExternalWordCode t) : Finset Point :=
  (tilingExternalDominoBases t z.start z.retained).filter
    (OrientationCompatible o)

/-- Retained multiplicity of a represented base, totalized by zero away from
the represented set. -/
def orientedThetaCodeExternalCount (t : DominoTiling)
    (z : OrientedTilingTypedExternalWordCode t) (b : Point) : ℕ :=
  if hb : b ∈ tilingExternalDominoBases t z.start z.retained then
    Fintype.card (TilingCoordinatesAt t z.start z.retained ⟨b, hb⟩)
  else 0

/-- The high-external Proposition 4.4 support, evaluated on the retained
creation word rather than at the deterministic physical cutoff. -/
def orientedThetaCodeCandidateSites44 (t : DominoTiling) (o : Orientation)
    (m : ℕ) (z : OrientedTilingTypedExternalWordCode t) : Finset Point :=
  (orientedThetaCodeBases t o z).filter fun b ↦
    hlozThickLevel44 m ≤ orientedThetaCodeExternalCount t z b

/-- High-count represented dominoes, normalized to the physical endpoint in
the checkerboard class selected by `o`.  Unlike `orientedThetaCodeCandidateSites44`,
this family also handles represented canonical bases of the opposite parity. -/
def orientedThetaCodeEndpointCandidateSites44
    (t : DominoTiling) (o : Orientation) (m : ℕ)
    (z : OrientedTilingTypedExternalWordCode t) : Finset Point :=
  ((tilingExternalDominoBases t z.start z.retained).filter fun b ↦
      hlozThickLevel44 m ≤ orientedThetaCodeExternalCount t z b).image
    (orientedDominoEndpoint t o)

/-- Path form of the retained creation-word base set. -/
def orientedThetaCreationBases (t : DominoTiling) (o : Orientation)
    (m k : ℕ) (s : WalkPath) : Finset Point :=
  orientedThetaCodeBases t o
    (fixedOrientedTypedExternalWordCode t o (creationTimeNat m k s) s)

/-- Path form of the retained creation-word high candidate set. -/
def orientedThetaCreationCandidateSites44 (t : DominoTiling)
    (o : Orientation) (m k : ℕ) (s : WalkPath) : Finset Point :=
  orientedThetaCodeCandidateSites44 t o m
    (fixedOrientedTypedExternalWordCode t o (creationTimeNat m k s) s)

/-- Path form of the endpoint-normalized high candidate family. -/
def orientedThetaCreationEndpointCandidateSites44 (t : DominoTiling)
    (o : Orientation) (m k : ℕ) (s : WalkPath) : Finset Point :=
  orientedThetaCodeEndpointCandidateSites44 t o m
    (fixedOrientedTypedExternalWordCode t o (creationTimeNat m k s) s)

lemma mem_orientedThetaCodeBases_iff
    {t : DominoTiling} {o : Orientation}
    {z : OrientedTilingTypedExternalWordCode t} {b : Point} :
    b ∈ orientedThetaCodeBases t o z ↔
      b ∈ tilingExternalDominoBases t z.start z.retained ∧
        OrientationCompatible o b := by
  simp [orientedThetaCodeBases]

lemma mem_orientedThetaCodeCandidateSites44_iff
    {t : DominoTiling} {o : Orientation} {m : ℕ}
    {z : OrientedTilingTypedExternalWordCode t} {b : Point} :
    b ∈ orientedThetaCodeCandidateSites44 t o m z ↔
      ∃ hb : b ∈ tilingExternalDominoBases t z.start z.retained,
        OrientationCompatible o b ∧
          hlozThickLevel44 m ≤
            Fintype.card (TilingCoordinatesAt t z.start z.retained ⟨b, hb⟩) := by
  classical
  unfold orientedThetaCodeCandidateSites44
  rw [Finset.mem_filter]
  constructor
  · rintro ⟨hb, hthick⟩
    rw [mem_orientedThetaCodeBases_iff] at hb
    refine ⟨hb.1, hb.2, ?_⟩
    simpa [orientedThetaCodeExternalCount, hb.1] using hthick
  · rintro ⟨hb, hcompat, hthick⟩
    refine ⟨mem_orientedThetaCodeBases_iff.mpr ⟨hb, hcompat⟩, ?_⟩
    simpa [orientedThetaCodeExternalCount, hb] using hthick

private theorem orientedThetaCodeExternalCount_fixed_eq_endpointSource
    (t : DominoTiling) (o : Orientation) (s : WalkPath) (n : ℕ)
    (hvalid : s ∈ validStepWalk) (hn : 0 < n) (b : Point)
    (hb : b ∈ tilingExternalDominoBases t
      (fixedOrientedTypedExternalWordCode t o n s).start
      (fixedOrientedTypedExternalWordCode t o n s).retained) :
    orientedThetaCodeExternalCount t
        (fixedOrientedTypedExternalWordCode t o n s) b =
      tilingSourceExternalBaseLocalTime t o s n
        (orientedDominoEndpoint t o b) := by
  rw [orientedThetaCodeExternalCount, dif_pos hb]
  unfold validStepWalk at hvalid
  change trajectory (stepsOfWalk s) = s at hvalid
  generalize homega : stepsOfWalk s = omega at hvalid
  subst s
  rw [card_tilingCoordinatesAt_eq_orientedEndpointLocalTime t
    (fixedOrientedTypedExternalWordCode t o n
      (trajectory omega)).start
    (orientationCompatible_fixedOrientedTypedExternalWordCode_start
      t o n (trajectory omega) hn)
    (fixedOrientedTypedExternalWordCode t o n
      (trajectory omega)).retained ⟨b, hb⟩]
  have hphase := phasedExternalVertexPath_eq_orientedRawEndpointPath
    t o omega n hn
  unfold TilingExternalPhaseSplit.phasedExternalVertexPath at hphase
  exact congrArg
    (fun p : List Point ↦ listLocalTime p (orientedDominoEndpoint t o b))
    ((fixedOrientedTypedExternalWordCode_endpointPath t o omega n hn).trans
      hphase.symm)

/-- On a valid positive-time creation prefix, the retained-code candidate
definition is exactly the source endpoint-chain thick-site definition. -/
theorem mem_orientedThetaCreationCandidateSites44_iff
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    {s : WalkPath} {b : Point}
    (hvalid : s ∈ (validStepWalk : Set WalkPath))
    (hcreation : 0 < creationTimeNat m k s) :
    b ∈ orientedThetaCreationCandidateSites44 t o m k s ↔
      b ∈ orientedThetaCreationBases t o m k s ∧
        hlozThickLevel44 m ≤
          tilingSourceExternalBaseLocalTime t o s
            (creationTimeNat m k s) b := by
  classical
  let z := fixedOrientedTypedExternalWordCode t o
    (creationTimeNat m k s) s
  change b ∈ orientedThetaCodeCandidateSites44 t o m z ↔
    b ∈ orientedThetaCodeBases t o z ∧ _
  rw [mem_orientedThetaCodeCandidateSites44_iff]
  constructor
  · rintro ⟨hb, hcompat, hthick⟩
    refine ⟨mem_orientedThetaCodeBases_iff.mpr ⟨hb, hcompat⟩, ?_⟩
    rw [← card_tilingCoordinatesAt_fixedOrientedTypedExternalWordCode_eq_source
      t o s (creationTimeNat m k s) hvalid hcreation ⟨b, hb⟩ hcompat]
    exact hthick
  · rintro ⟨hbcode, hthick⟩
    rw [mem_orientedThetaCodeBases_iff] at hbcode
    refine ⟨hbcode.1, hbcode.2, ?_⟩
    rw [card_tilingCoordinatesAt_fixedOrientedTypedExternalWordCode_eq_source
      t o s (creationTimeNat m k s) hvalid hcreation ⟨b, hbcode.1⟩ hbcode.2]
    exact hthick

private theorem creationTimeNat_pos
    {m k : ℕ} {s : WalkPath} (hm : 1 < m) (hk : 0 < k)
    (hreach : ReachesThreshold s m k) :
    0 < creationTimeNat m k s := by
  have hcreation : ThresholdCreation s m k (creationTimeNat m k s) := by
    simpa only [creationTimeNat, hreach, dif_pos] using
      thresholdCreation_natFind hreach
  by_contra hn
  have hzero : creationTimeNat m k s = 0 := Nat.eq_zero_of_not_pos hn
  have hsite := position_mem_thresholdSites_of_creation hk hcreation
  have hlevel := (mem_thresholdSites s _ m _).mp hsite |>.2
  have hlocal : localTime s 0 (s 0) = 1 := by
    simp [localTime, localTimePrefix, pathPrefix]
  rw [hzero, hlocal] at hlevel
  omega

/-- Every high restricted-Theta base is one of the retained creation-word
high candidates. -/
theorem orientedRestrictedThetaHighAtCreation_subset_creationCandidates44
    {t : DominoTiling} {o : Orientation}
    {m k w externalLow externalHigh : ℕ} {s : WalkPath}
    (hm : 1 < m) (hk : 0 < k)
    (hvalid : s ∈ (validStepWalk : Set WalkPath))
    (hreach : ReachesThreshold s m k) :
    orientedRestrictedThetaHighAtCreation t o m k w externalLow externalHigh s ⊆
      orientedThetaCreationCandidateSites44 t o m k s := by
  intro b hb
  have hcreation := creationTimeNat_pos hm hk hreach
  rw [orientedRestrictedThetaHighAtCreation, Finset.mem_filter] at hb
  have hbtheta := hb.1
  rw [orientedTilingThetaAtCreation, orientedTilingThetaBases,
    Finset.mem_filter, mem_orientedTilingVTwoBases_iff] at hbtheta
  have hcompat : OrientationCompatible o b := hbtheta.1.2
  have hzero : 0 ∉ shellZeroSourceTotalWindow m w ∪
      shellZeroReplacementTotalWindow m w := by
    simp [mem_shellZeroSourceTotalWindow,
      mem_shellZeroReplacementTotalWindow]
  have hrepresented :=
    orientedTilingVTwoBases_subset_fixedExternalDominoBases t o
      (shellZeroSourceTotalWindow m w ∪
        shellZeroReplacementTotalWindow m w) s
      (creationTimeNat m k s) hvalid hzero
      (mem_orientedTilingVTwoBases_iff t o _ s _ b |>.2
        ⟨hbtheta.1.1, hcompat⟩)
  rw [mem_orientedThetaCreationCandidateSites44_iff hvalid hcreation]
  refine ⟨mem_orientedThetaCodeBases_iff.mpr ⟨hrepresented, hcompat⟩, hb.2⟩

/-- Creation-word candidates embed into the deterministic-cutoff
Proposition 4.4 family on the on-time event. -/
theorem orientedThetaCreationCandidateSites44_subset_cutoffCandidates44
    {t : DominoTiling} {o : Orientation} {m k : ℕ} {s : WalkPath}
    (hvalid : s ∈ (validStepWalk : Set WalkPath))
    (hcreation : 0 < creationTimeNat m k s)
    (hclock : creationTimeNat m k s ≤ hlozCutoff44 m) :
    orientedThetaCreationCandidateSites44 t o m k s ⊆
      orientedThetaCandidateSites44 t o m s := by
  intro b hb
  rw [mem_orientedThetaCreationCandidateSites44_iff hvalid hcreation] at hb
  have hbcode := hb.1
  unfold orientedThetaCreationBases at hbcode
  rw [mem_orientedThetaCodeBases_iff] at hbcode
  apply mem_tilingSourceExternalCandidateSites_of_thick
    (Nat.succ_pos _) hbcode.2
  · exact hb.2.trans
      (tilingSourceExternalBaseLocalTime_mono_of_valid t o s b hclock hvalid)
  · simp

/-- Off the existing Proposition 4.4 overflow, the retained creation-word
high family has the same finite budget. -/
theorem orientedThetaCreationCandidateSites44_card_le
    {t : DominoTiling} {o : Orientation} {m k : ℕ} {s : WalkPath}
    (hvalid : s ∈ (validStepWalk : Set WalkPath))
    (hcreation : 0 < creationTimeNat m k s)
    (hclock : creationTimeNat m k s ≤ hlozCutoff44 m)
    (hoverflow : s ∉ orientedThetaCandidateOverflow44 t o m) :
    (orientedThetaCreationCandidateSites44 t o m k s).card ≤
      hlozSiteBudget44 m := by
  exact (Finset.card_le_card
      (orientedThetaCreationCandidateSites44_subset_cutoffCandidates44
        hvalid hcreation hclock)).trans
    (tilingSourceExternalCandidateSites_card_le_of_not_overflow hoverflow)

/-- Endpoint-normalized creation-word candidates embed into the same
deterministic-cutoff Proposition 4.4 family. -/
theorem orientedThetaCreationEndpointCandidateSites44_subset_cutoffCandidates44
    {t : DominoTiling} {o : Orientation} {m k : ℕ} {s : WalkPath}
    (hvalid : s ∈ (validStepWalk : Set WalkPath))
    (hcreation : 0 < creationTimeNat m k s)
    (hclock : creationTimeNat m k s ≤ hlozCutoff44 m) :
    orientedThetaCreationEndpointCandidateSites44 t o m k s ⊆
      orientedThetaCandidateSites44 t o m s := by
  classical
  intro x hx
  unfold orientedThetaCreationEndpointCandidateSites44 at hx
  unfold orientedThetaCodeEndpointCandidateSites44 at hx
  rw [Finset.mem_image] at hx
  rcases hx with ⟨b, hb, rfl⟩
  rw [Finset.mem_filter] at hb
  have hcount := orientedThetaCodeExternalCount_fixed_eq_endpointSource
    t o s (creationTimeNat m k s) hvalid hcreation b hb.1
  apply mem_tilingSourceExternalCandidateSites_of_thick
    (Nat.succ_pos _) (orientedDominoEndpoint_compatible t o b)
  · exact (hcount ▸ hb.2).trans
      (tilingSourceExternalBaseLocalTime_mono_of_valid t o s
        (orientedDominoEndpoint t o b) hclock hvalid)
  · simp

/-- Off Proposition 4.4 overflow, the endpoint-normalized high family has
the same cardinal budget. -/
theorem orientedThetaCreationEndpointCandidateSites44_card_le
    {t : DominoTiling} {o : Orientation} {m k : ℕ} {s : WalkPath}
    (hvalid : s ∈ (validStepWalk : Set WalkPath))
    (hcreation : 0 < creationTimeNat m k s)
    (hclock : creationTimeNat m k s ≤ hlozCutoff44 m)
    (hoverflow : s ∉ orientedThetaCandidateOverflow44 t o m) :
    (orientedThetaCreationEndpointCandidateSites44 t o m k s).card ≤
      hlozSiteBudget44 m := by
  exact (Finset.card_le_card
      (orientedThetaCreationEndpointCandidateSites44_subset_cutoffCandidates44
        hvalid hcreation hclock)).trans
    (tilingSourceExternalCandidateSites_card_le_of_not_overflow hoverflow)

/-- Every low restricted-Theta base is represented by the retained creation
word and has the prescribed temporal orientation. -/
theorem orientedRestrictedThetaLowAtCreation_subset_creationBases
    {t : DominoTiling} {o : Orientation}
    {m k w externalLow externalHigh : ℕ} {s : WalkPath}
    (hvalid : s ∈ (validStepWalk : Set WalkPath)) :
    orientedRestrictedThetaLowAtCreation t o m k w externalLow externalHigh s ⊆
      orientedThetaCreationBases t o m k s := by
  intro b hb
  rw [orientedRestrictedThetaLowAtCreation, Finset.mem_filter] at hb
  have hbtheta := hb.1
  rw [orientedTilingThetaAtCreation, orientedTilingThetaBases,
    Finset.mem_filter, mem_orientedTilingVTwoBases_iff] at hbtheta
  have hzero : 0 ∉ shellZeroSourceTotalWindow m w ∪
      shellZeroReplacementTotalWindow m w := by
    simp [mem_shellZeroSourceTotalWindow,
      mem_shellZeroReplacementTotalWindow]
  have hrepresented :=
    orientedTilingVTwoBases_subset_fixedExternalDominoBases t o
      (shellZeroSourceTotalWindow m w ∪
        shellZeroReplacementTotalWindow m w) s
      (creationTimeNat m k s) hvalid hzero
      (mem_orientedTilingVTwoBases_iff t o _ s _ b |>.2
        ⟨hbtheta.1.1, hbtheta.1.2⟩)
  exact mem_orientedThetaCodeBases_iff.mpr ⟨hrepresented, hbtheta.1.2⟩

private theorem deleteTilingBlocks_length_le (t : DominoTiling) (x : Point) :
    ∀ bs : List PathInsertion.Block,
      (deleteTilingBlocks t x bs).length ≤ bs.length := by
  intro bs
  induction bs generalizing x with
  | nil => rfl
  | cons a as ih =>
      simp only [deleteTilingBlocks]
      split
      · exact (ih x).trans (Nat.le_succ _)
      · simp only [List.length_cons]
        exact Nat.succ_le_succ (ih (blockEnd x a))

/-- The low slot family is bounded by the physical creation clock, hence by
the same `cutoff+1` budget used in the source numerical estimate. -/
theorem orientedThetaCreationBases_card_le_cutoff_add_one
    {t : DominoTiling} {o : Orientation} {m k : ℕ} {s : WalkPath}
    (hclock : creationTimeNat m k s ≤ hlozCutoff44 m) :
    (orientedThetaCreationBases t o m k s).card ≤ hlozCutoff44 m + 1 := by
  let z := fixedOrientedTypedExternalWordCode t o
    (creationTimeNat m k s) s
  calc
    (orientedThetaCreationBases t o m k s).card ≤
        (tilingExternalDominoBases t z.start z.retained).card := by
      exact Finset.card_le_card (Finset.filter_subset _ _)
    _ ≤ z.retainedCount + 1 := by
      unfold tilingExternalDominoBases
      calc
        (Finset.univ.image (fun j : Fin (z.retainedCount + 1) ↦
            tilingBase t (rawExternalBase z.start z.retained.1 j))).card ≤
            (Finset.univ : Finset (Fin (z.retainedCount + 1))).card :=
          Finset.card_image_le
        _ = z.retainedCount + 1 := by simp
    _ ≤ creationTimeNat m k s + 1 := by
      have hretained : z.retainedCount ≤ creationTimeNat m k s := by
        unfold z fixedOrientedTypedExternalWordCode
        dsimp only
        refine (deleteTilingBlocks_length_le t _ _).trans ?_
        calc
          (pairDirectionList
              (orientedIncrementPrefixList o (creationTimeNat m k s) s)).length ≤
              (orientedIncrementPrefixList o
                (creationTimeNat m k s) s).length := by
            rw [pairDirectionList_length]
            omega
          _ ≤ creationTimeNat m k s := by
            cases o <;> simp [orientedIncrementPrefixList,
              incrementPrefixList]
      omega
    _ ≤ hlozCutoff44 m + 1 := by omega

/-! ## Trace-local slot events and the physical cover -/

/-- One high-external slot selected from the retained creation word. -/
def orientedThetaCreationHighSlotBad (t : DominoTiling) (o : Orientation)
    (m k w externalLow externalHigh : ℕ)
    (slot : Fin (hlozSiteBudget44 m)) : Set WalkPath :=
  {s | s ∈ validStepWalk ∧ ReachesThreshold s m k ∧
    creationTimeNat m k s ≤ hlozCutoff44 m ∧
    ∃ b, finsetSlot
        (orientedThetaCreationCandidateSites44 t o m k s) slot = some b ∧
      b ∈ orientedRestrictedThetaHighAtCreation t o m k w externalLow
        externalHigh s}

/-- One low-external slot selected from all compatible represented bases of
the retained creation word. -/
def orientedThetaCreationLowSlotBad (t : DominoTiling) (o : Orientation)
    (m k w externalLow externalHigh : ℕ)
    (slot : Fin (hlozCutoff44 m + 1)) : Set WalkPath :=
  {s | s ∈ validStepWalk ∧ ReachesThreshold s m k ∧
    creationTimeNat m k s ≤ hlozCutoff44 m ∧
    ∃ b, finsetSlot (orientedThetaCreationBases t o m k s) slot = some b ∧
      b ∈ orientedRestrictedThetaLowAtCreation t o m k w externalLow
        externalHigh s}

def someOrientedThetaCreationHighSlotBad (t : DominoTiling)
    (o : Orientation) (m k w externalLow externalHigh : ℕ) : Set WalkPath :=
  Screening.someCandidateBad
    (Finset.univ : Finset (Fin (hlozSiteBudget44 m)))
    (orientedThetaCreationHighSlotBad t o m k w externalLow externalHigh)

def someOrientedThetaCreationLowSlotBad (t : DominoTiling)
    (o : Orientation) (m k w externalLow externalHigh : ℕ) : Set WalkPath :=
  Screening.someCandidateBad
    (Finset.univ : Finset (Fin (hlozCutoff44 m + 1)))
    (orientedThetaCreationLowSlotBad t o m k w externalLow externalHigh)

/-- Source-correct retained-slot payment for one restricted oriented Theta
screen.  The Proposition 4.4 overflow is still evaluated at the larger
deterministic cutoff; only the finite slot selectors are evaluated at the
creation retained word. -/
def orientedRestrictedThetaCreationPaidEvent (t : DominoTiling)
    (o : Orientation) (m k w externalLow externalHigh : ℕ) : Set WalkPath :=
  validStepWalkᶜ ∪ (orientedThetaCandidateOverflow44 t o m ∪
    (someOrientedThetaCreationHighSlotBad t o m k w externalLow externalHigh ∪
      someOrientedThetaCreationLowSlotBad t o m k w externalLow externalHigh))

/-- The physical restricted-Theta failure is covered by the retained-word
slot family, without a cutoff-prefix selector. -/
theorem restrictedTheta_onTime_subset_creationPaid
    (t : DominoTiling) (o : Orientation)
    (m k w externalLow externalHigh : ℕ)
    (hm : 1 < m) (hk : 0 < k) :
    {s | ReachesThreshold s m k ∧
      creationTimeNat m k s ≤ hlozCutoff44 m ∧
      orientedTilingThetaAtCreation t o m k w externalLow externalHigh s ≠ ∅} ⊆
      orientedRestrictedThetaCreationPaidEvent t o m k w externalLow
        externalHigh := by
  intro s hs
  rcases hs with ⟨hreach, hclock, htheta⟩
  by_cases hvalid : s ∈ validStepWalk
  · rw [orientedTilingThetaAtCreation_eq_high_union_low] at htheta
    have hcreation := creationTimeNat_pos hm hk hreach
    by_cases hhigh :
        (orientedRestrictedThetaHighAtCreation t o m k w externalLow
          externalHigh s).Nonempty
    · by_cases hoverflow : s ∈ orientedThetaCandidateOverflow44 t o m
      · right; left; exact hoverflow
      · right; right; left
        obtain ⟨b, hb⟩ := hhigh
        have hbcand :=
          orientedRestrictedThetaHighAtCreation_subset_creationCandidates44
            hm hk hvalid hreach hb
        obtain ⟨j, hjlt, hj⟩ := exists_finsetSlot_eq_some hbcand
        have hjbudget : j < hlozSiteBudget44 m :=
          hjlt.trans_le (orientedThetaCreationCandidateSites44_card_le
            hvalid hcreation hclock hoverflow)
        exact ⟨⟨j, hjbudget⟩, Finset.mem_univ _,
          hvalid, hreach, hclock, b, by simpa using hj, hb⟩
    · right; right; right
      have hlow :
          (orientedRestrictedThetaLowAtCreation t o m k w externalLow
            externalHigh s).Nonempty := by
        obtain ⟨b, hb⟩ := Finset.nonempty_iff_ne_empty.mpr htheta
        rw [Finset.mem_union] at hb
        rcases hb with hb | hb
        · exact (hhigh ⟨b, hb⟩).elim
        · exact ⟨b, hb⟩
      obtain ⟨b, hb⟩ := hlow
      have hbbase :=
        orientedRestrictedThetaLowAtCreation_subset_creationBases hvalid hb
      obtain ⟨j, hjlt, hj⟩ := exists_finsetSlot_eq_some hbbase
      have hjcut : j < hlozCutoff44 m + 1 :=
        hjlt.trans_le (orientedThetaCreationBases_card_le_cutoff_add_one hclock)
      exact ⟨⟨j, hjcut⟩, Finset.mem_univ _,
        hvalid, hreach, hclock, b, by simpa using hj, hb⟩
  · left; exact hvalid

end

end Erdos1165.HLOZSourceOrientedThetaCreationSlots
