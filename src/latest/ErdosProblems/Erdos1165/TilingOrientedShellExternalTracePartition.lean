/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.TilingOrientedShellZeroSourcePartition

/-!
# Endpoint-oriented shell-zero partition by external retained words

The fixed-central replacement changes some `I₁` local times into `I₀`
local times.  Its current favorite-site data therefore cannot equal the
source favorite-site data.  The common cross-clock carrier is only the full
endpoint-oriented external word: physical initial prefix, statefully retained
word, and boundary tail.

This file partitions both exact source and fixed-central replacement events
by that carrier.  `V₂`, `Theta`, and the exact source/replacement counts stay
in the path event, not in the trace code.  Replacement atoms are pairwise
disjoint by the genuine path-dependent creation clock.
-/

open Set

namespace Erdos1165.TilingOrientedShellExternalTracePartition

open HLOZPathEvents HLOZShellZeroReplacementWindows
open LazyDecomposition
open TilingOrientedShellZeroSourcePartition
open TilingShellZeroSourcePartition
open VariableStoppedTracePartition

noncomputable section

abbrev DominoTiling := Tilings.Tiling

/-- Exact oriented source atom indexed only by its physical prefixed external
word.  Favorite data and all source screens remain unfixed. -/
def orientedShellZeroExactSourceExternalTraceAtom
    (t : DominoTiling) (o : Orientation)
    (m k w low externalLow externalHigh total : ℕ)
    (z : OrientedTilingTypedExternalWordCode t) : Set WalkPath :=
  orientedShellZeroExactSourceEvent t o m k w low externalLow externalHigh
      total ∩
    {s | fixedOrientedTypedExternalWordCode t o (creationTimeNat m k s) s = z}

/-- Valid-walk support of one exact external source atom. -/
def orientedValidShellZeroExactSourceExternalTraceAtom
    (t : DominoTiling) (o : Orientation)
    (m k w low externalLow externalHigh total : ℕ)
    (z : OrientedTilingTypedExternalWordCode t) : Set WalkPath :=
  orientedShellZeroExactSourceExternalTraceAtom t o m k w low externalLow
    externalHigh total z ∩ validStepWalk

theorem iUnion_orientedShellZeroExactSourceExternalTraceAtom
    (t : DominoTiling) (o : Orientation)
    (m k w low externalLow externalHigh total : ℕ) :
    (⋃ z : OrientedTilingTypedExternalWordCode t,
      orientedShellZeroExactSourceExternalTraceAtom t o m k w low externalLow
        externalHigh total z) =
      orientedShellZeroExactSourceEvent t o m k w low externalLow externalHigh
        total := by
  ext s
  simp only [Set.mem_iUnion,
    orientedShellZeroExactSourceExternalTraceAtom, Set.mem_inter_iff,
    Set.mem_ofPred_eq]
  constructor
  · rintro ⟨z, hs, _⟩
    exact hs
  · intro hs
    exact ⟨fixedOrientedTypedExternalWordCode t o
      (creationTimeNat m k s) s, hs, rfl⟩

theorem iUnion_orientedValidShellZeroExactSourceExternalTraceAtom
    (t : DominoTiling) (o : Orientation)
    (m k w low externalLow externalHigh total : ℕ) :
    (⋃ z : OrientedTilingTypedExternalWordCode t,
      orientedValidShellZeroExactSourceExternalTraceAtom t o m k w low
        externalLow externalHigh total z) =
      orientedShellZeroExactSourceEvent t o m k w low externalLow externalHigh
        total ∩ validStepWalk := by
  simp only [orientedValidShellZeroExactSourceExternalTraceAtom]
  rw [← iUnion_inter]
  congr 1
  exact iUnion_orientedShellZeroExactSourceExternalTraceAtom
    t o m k w low externalLow externalHigh total

theorem pairwise_disjoint_orientedShellZeroExactSourceExternalTraceAtom
    (t : DominoTiling) (o : Orientation)
    (m k w low externalLow externalHigh total : ℕ) :
    Pairwise fun z z' ↦ Disjoint
      (orientedShellZeroExactSourceExternalTraceAtom t o m k w low
        externalLow externalHigh total z)
      (orientedShellZeroExactSourceExternalTraceAtom t o m k w low
        externalLow externalHigh total z') := by
  intro z z' hne
  rw [Set.disjoint_left]
  intro s hs hs'
  apply hne
  exact hs.2.symm.trans hs'.2

/-- Fixed-central replacement event before choosing its external trace. -/
def orientedShellZeroFixedCentralReplacementEvent
    (t : DominoTiling) (o : Orientation)
    (m k w low externalLow externalHigh total central : ℕ) : Set WalkPath :=
  let rank := replacementCreationRank k total central
  {s | ReachesThreshold s m rank ∧
    let n := creationTimeNat m rank s
    tilingDtildeEtaAt t m k w low s n ∧
      orientedTilingThetaBases t o m w externalLow externalHigh s n = ∅ ∧
      (orientedTilingVTwoBases t o
        (shellZeroSourceTotalWindow m w) s n).card = central ∧
      (orientedTilingVTwoBases t o
        (shellZeroReplacementTotalWindow m w) s n).card = total - central}

/-- Replacement atom with no current-favorite equality.  The complete
physical external word is evaluated at the raised-rank creation clock. -/
def orientedShellZeroReplacementExternalTraceAtom
    (t : DominoTiling) (o : Orientation)
    (m k w low externalLow externalHigh total central : ℕ)
    (z : OrientedTilingTypedExternalWordCode t) : Set WalkPath :=
  orientedShellZeroFixedCentralReplacementEvent t o m k w low externalLow
      externalHigh total central ∩
    {s | fixedOrientedTypedExternalWordCode t o
      (creationTimeNat m (replacementCreationRank k total central) s) s = z}

/-- Valid-walk support of one replacement external atom. -/
def orientedValidShellZeroReplacementExternalTraceAtom
    (t : DominoTiling) (o : Orientation)
    (m k w low externalLow externalHigh total central : ℕ)
    (z : OrientedTilingTypedExternalWordCode t) : Set WalkPath :=
  orientedShellZeroReplacementExternalTraceAtom t o m k w low externalLow
    externalHigh total central z ∩ validStepWalk

theorem iUnion_orientedShellZeroReplacementExternalTraceAtom
    (t : DominoTiling) (o : Orientation)
    (m k w low externalLow externalHigh total central : ℕ) :
    (⋃ z : OrientedTilingTypedExternalWordCode t,
      orientedShellZeroReplacementExternalTraceAtom t o m k w low externalLow
        externalHigh total central z) =
      orientedShellZeroFixedCentralReplacementEvent t o m k w low externalLow
        externalHigh total central := by
  ext s
  simp only [Set.mem_iUnion,
    orientedShellZeroReplacementExternalTraceAtom, Set.mem_inter_iff,
    Set.mem_ofPred_eq]
  constructor
  · rintro ⟨z, hs, _⟩
    exact hs
  · intro hs
    exact ⟨fixedOrientedTypedExternalWordCode t o
      (creationTimeNat m (replacementCreationRank k total central) s) s,
      hs, rfl⟩

theorem iUnion_orientedValidShellZeroReplacementExternalTraceAtom
    (t : DominoTiling) (o : Orientation)
    (m k w low externalLow externalHigh total central : ℕ) :
    (⋃ z : OrientedTilingTypedExternalWordCode t,
      orientedValidShellZeroReplacementExternalTraceAtom t o m k w low
        externalLow externalHigh total central z) =
      orientedShellZeroFixedCentralReplacementEvent t o m k w low externalLow
        externalHigh total central ∩ validStepWalk := by
  simp only [orientedValidShellZeroReplacementExternalTraceAtom]
  rw [← iUnion_inter]
  congr 1
  exact iUnion_orientedShellZeroReplacementExternalTraceAtom
    t o m k w low externalLow externalHigh total central

theorem orientedShellZeroReplacementExternalTraceAtom_creation
    {t : DominoTiling} {o : Orientation}
    {m k w low externalLow externalHigh total central : ℕ}
    {z : OrientedTilingTypedExternalWordCode t} {s : WalkPath}
    (hs : s ∈ orientedShellZeroReplacementExternalTraceAtom t o m k w low
      externalLow externalHigh total central z) :
    ThresholdCreation s m (replacementCreationRank k total central)
      (creationTimeNat m (replacementCreationRank k total central) s) := by
  have hreach : ReachesThreshold s m
      (replacementCreationRank k total central) := hs.1.1
  simpa only [creationTimeNat, hreach, dif_pos] using
    (thresholdCreation_natFind hreach)

theorem orientedShellZeroReplacementExternalTraceAtom_trace
    {t : DominoTiling} {o : Orientation}
    {m k w low externalLow externalHigh total central : ℕ}
    {z : OrientedTilingTypedExternalWordCode t} {s : WalkPath}
    (hs : s ∈ orientedShellZeroReplacementExternalTraceAtom t o m k w low
      externalLow externalHigh total central z) :
    fixedOrientedTypedExternalWordCode t o
        (creationTimeNat m (replacementCreationRank k total central) s) s =
      z := hs.2

/-- Variable-clock jump certificate for the corrected external-word-only
replacement atoms. -/
def orientedShellZeroExternalVariableClockJump
    (t : DominoTiling) (o : Orientation)
    (m k w low externalLow externalHigh total central : ℕ)
    (hm : 1 < m)
    (hrank : 0 < replacementCreationRank k total central) :
    VariableClockThresholdJumpReplacementFamily
      (orientedShellZeroReplacementExternalTraceAtom t o m k w low
        externalLow externalHigh total central) where
  clock := fun _ s ↦
    creationTimeNat m (replacementCreationRank k total central) s
  traceAt := fun s n ↦ fixedOrientedTypedExternalWordCode t o n s
  thresholdCount := fun s n ↦ thresholdCount s n m
  monotone_thresholdCount := fun s ↦ thresholdCount_mono_time s m
  rank := replacementCreationRank k total central - 1
  trace_eq := fun _ _ hs ↦
    orientedShellZeroReplacementExternalTraceAtom_trace hs
  count_before := fun _ _ hs ↦
    thresholdCount_pred_eq_of_creation hm hrank
      (orientedShellZeroReplacementExternalTraceAtom_creation hs)
  count_at := by
    intro z s hs
    have hcreation :=
      orientedShellZeroReplacementExternalTraceAtom_creation hs
    have hcount := thresholdCount_eq_of_creation hrank hcreation
    simpa only [Nat.sub_add_cancel hrank] using hcount

theorem pairwise_disjoint_orientedShellZeroReplacementExternalTraceAtom
    (t : DominoTiling) (o : Orientation)
    (m k w low externalLow externalHigh total central : ℕ)
    (hm : 1 < m)
    (hrank : 0 < replacementCreationRank k total central) :
    Pairwise fun z z' ↦ Disjoint
      (orientedShellZeroReplacementExternalTraceAtom t o m k w low
        externalLow externalHigh total central z)
      (orientedShellZeroReplacementExternalTraceAtom t o m k w low
        externalLow externalHigh total central z') :=
  pairwise_disjoint_of_variableClockThresholdJump
    (orientedShellZeroExternalVariableClockJump t o m k w low externalLow
      externalHigh total central hm hrank)

end

end Erdos1165.TilingOrientedShellExternalTracePartition
