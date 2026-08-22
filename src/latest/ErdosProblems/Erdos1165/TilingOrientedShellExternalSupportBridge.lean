/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.TilingOrientedShellExternalTracePartition
import ErdosProblems.Erdos1165.TilingOrientedExternalAllCreationStoppedCoordinate

/-!
# Support-refined external shell atoms

The cross-clock trace carrier is the oriented physical external word.  The
finite away carrier additionally fixes a support set `S`, but that set is a
separate atom index rather than part of the trace code.  This file refines
the corrected external source/replacement atoms by `S` and embeds their
valid-walk versions into the frozen external all-creation family.
-/

open Set

namespace Erdos1165.TilingOrientedShellExternalSupportBridge

open HLOZProposition48Candidates HLOZShellZeroReplacementWindows
open LazyDecomposition
open TilingOrientedExternalAllCreationStoppedCoordinate
open TilingOrientedShellExternalTracePartition
open TilingOrientedShellZeroSourcePartition
open TilingShellZeroSourcePartition
open VariableStoppedTracePartition

noncomputable section

abbrev DominoTiling := Tilings.Tiling

/-- Source-clock support selector, kept separate from the external trace. -/
def externalShellSourceSupportAt
    (t : DominoTiling) (o : Orientation) (m : ℕ) :
    WalkPath → ℕ → Finset Point :=
  fun s n ↦ orientedTilingVTwoBases t o
    (shellZeroSourceTotalWindow m (shellWidth48 m)) s n

/-- Raised-clock support selector.  The same static set is interpreted as
the union of retained `I₁` and artificial `I₀` bases. -/
def externalShellReplacementSupportAt
    (t : DominoTiling) (o : Orientation) (m : ℕ) :
    WalkPath → ℕ → Finset Point :=
  fun s n ↦ orientedTilingVTwoBases t o
    (shellZeroSourceTotalWindow m (shellWidth48 m) ∪
      shellZeroReplacementTotalWindow m (shellWidth48 m)) s n

/-- Exact source external atom with its away support fixed separately. -/
def orientedShellZeroExactSourceExternalSupportAtom
    (t : DominoTiling) (o : Orientation)
    (m k low externalLow externalHigh total : ℕ)
    (z : OrientedTilingTypedExternalWordCode t) (S : Finset Point) :
    Set WalkPath :=
  orientedShellZeroExactSourceExternalTraceAtom t o m k (shellWidth48 m) low
      externalLow externalHigh total z ∩
    {s | externalShellSourceSupportAt t o m s (creationTimeNat m k s) = S}

def orientedValidShellZeroExactSourceExternalSupportAtom
    (t : DominoTiling) (o : Orientation)
    (m k low externalLow externalHigh total : ℕ)
    (z : OrientedTilingTypedExternalWordCode t) (S : Finset Point) :
    Set WalkPath :=
  orientedShellZeroExactSourceExternalSupportAtom t o m k low externalLow
    externalHigh total z S ∩ validStepWalk

/-- Fixed-central replacement atom with the union-window support fixed to
the same separate static set. -/
def orientedShellZeroReplacementExternalSupportAtom
    (t : DominoTiling) (o : Orientation)
    (m k low externalLow externalHigh total central : ℕ)
    (z : OrientedTilingTypedExternalWordCode t) (S : Finset Point) :
    Set WalkPath :=
  orientedShellZeroReplacementExternalTraceAtom t o m k (shellWidth48 m) low
      externalLow externalHigh total central z ∩
    {s | externalShellReplacementSupportAt t o m s
      (creationTimeNat m (replacementCreationRank k total central) s) = S}

def orientedValidShellZeroReplacementExternalSupportAtom
    (t : DominoTiling) (o : Orientation)
    (m k low externalLow externalHigh total central : ℕ)
    (z : OrientedTilingTypedExternalWordCode t) (S : Finset Point) :
    Set WalkPath :=
  orientedShellZeroReplacementExternalSupportAtom t o m k low externalLow
    externalHigh total central z S ∩ validStepWalk

theorem iUnion_orientedShellZeroExactSourceExternalSupportAtom
    (t : DominoTiling) (o : Orientation)
    (m k low externalLow externalHigh total : ℕ)
    (z : OrientedTilingTypedExternalWordCode t) :
    (⋃ S : Finset Point,
      orientedShellZeroExactSourceExternalSupportAtom t o m k low externalLow
        externalHigh total z S) =
      orientedShellZeroExactSourceExternalTraceAtom t o m k (shellWidth48 m)
        low externalLow externalHigh total z := by
  ext s
  simp only [Set.mem_iUnion,
    orientedShellZeroExactSourceExternalSupportAtom, Set.mem_inter_iff,
    Set.mem_ofPred_eq]
  constructor
  · rintro ⟨S, hs, _⟩
    exact hs
  · intro hs
    exact ⟨externalShellSourceSupportAt t o m s
      (creationTimeNat m k s), hs, rfl⟩

theorem iUnion_orientedShellZeroReplacementExternalSupportAtom
    (t : DominoTiling) (o : Orientation)
    (m k low externalLow externalHigh total central : ℕ)
    (z : OrientedTilingTypedExternalWordCode t) :
    (⋃ S : Finset Point,
      orientedShellZeroReplacementExternalSupportAtom t o m k low externalLow
        externalHigh total central z S) =
      orientedShellZeroReplacementExternalTraceAtom t o m k (shellWidth48 m)
        low externalLow externalHigh total central z := by
  ext s
  simp only [Set.mem_iUnion,
    orientedShellZeroReplacementExternalSupportAtom, Set.mem_inter_iff,
    Set.mem_ofPred_eq]
  constructor
  · rintro ⟨S, hs, _⟩
    exact hs
  · intro hs
    exact ⟨externalShellReplacementSupportAt t o m s
      (creationTimeNat m (replacementCreationRank k total central) s), hs, rfl⟩

theorem validSourceExternalSupportAtom_subset_allCreation
    (t : DominoTiling) (o : Orientation)
    (m k low externalLow externalHigh total : ℕ)
    (z : OrientedTilingTypedExternalWordCode t) (S : Finset Point) :
    orientedValidShellZeroExactSourceExternalSupportAtom t o m k low
        externalLow externalHigh total z S ⊆
      orientedExternalAllCreationSupportTraceAtom t o m k
        (externalShellSourceSupportAt t o m) z S := by
  rw [orientedExternalAllCreationSupportTraceAtom_eq]
  intro s hs
  exact ⟨hs.2, hs.1.1.1.1, hs.1.1.2, hs.1.2⟩

theorem validReplacementExternalSupportAtom_subset_allCreation
    (t : DominoTiling) (o : Orientation)
    (m k low externalLow externalHigh total central : ℕ)
    (z : OrientedTilingTypedExternalWordCode t) (S : Finset Point) :
    orientedValidShellZeroReplacementExternalSupportAtom t o m k low
        externalLow externalHigh total central z S ⊆
      orientedExternalAllCreationSupportTraceAtom t o m
        (replacementCreationRank k total central)
        (externalShellReplacementSupportAt t o m) z S := by
  rw [orientedExternalAllCreationSupportTraceAtom_eq]
  intro s hs
  exact ⟨hs.2, hs.1.1.1.1, hs.1.1.2, hs.1.2⟩

/-- Nonempty source shell atoms, now indexed by the honest external word and
the separate fixed away support. -/
abbrev SupportedSourceIndex
    (t : DominoTiling) (o : Orientation)
    (m k low externalLow externalHigh total : ℕ) :=
  {eta : OrientedTilingTypedExternalWordCode t × Finset Point //
    (orientedValidShellZeroExactSourceExternalSupportAtom t o m k low
      externalLow externalHigh total eta.1 eta.2).Nonempty}

abbrev SupportedReplacementIndex
    (t : DominoTiling) (o : Orientation)
    (m k low externalLow externalHigh total central : ℕ) :=
  {eta : OrientedTilingTypedExternalWordCode t × Finset Point //
    (orientedValidShellZeroReplacementExternalSupportAtom t o m k low
      externalLow externalHigh total central eta.1 eta.2).Nonempty}

noncomputable def sourceAllCreationSupportedIndex
    (t : DominoTiling) (o : Orientation)
    (m k low externalLow externalHigh total : ℕ)
    (eta : SupportedSourceIndex t o m k low externalLow externalHigh total) :
    SupportedIndex t o m k (externalShellSourceSupportAt t o m) :=
  ⟨eta.1, eta.2.mono (validSourceExternalSupportAtom_subset_allCreation
    t o m k low externalLow externalHigh total eta.1.1 eta.1.2)⟩

noncomputable def replacementAllCreationSupportedIndex
    (t : DominoTiling) (o : Orientation)
    (m k low externalLow externalHigh total central : ℕ)
    (eta : SupportedReplacementIndex t o m k low externalLow externalHigh
      total central) :
    SupportedIndex t o m (replacementCreationRank k total central)
      (externalShellReplacementSupportAt t o m) :=
  ⟨eta.1, eta.2.mono (validReplacementExternalSupportAtom_subset_allCreation
    t o m k low externalLow externalHigh total central eta.1.1 eta.1.2)⟩

end

end Erdos1165.TilingOrientedShellExternalSupportBridge
