/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.TilingOrientedAllCreationStoppedCoordinate
import ErdosProblems.Erdos1165.TilingShellZeroFactoredCapScreen

/-!
# Shell-zero atoms as supported all-creation atoms

The common prefixed coordinate fibre fixes only the oriented retained/favorite
trace and a finite support set.  This file identifies the two shell-zero
clocks with that reusable layer.  The source support is `V₂(I₁)`; at the
replacement clock the same stored finite set is `V₂(I₀ ∪ I₁)`.
-/

open Set

namespace Erdos1165.TilingShellZeroAllCreationTraceBridge

open HLOZShellZeroCentralCount HLOZShellZeroReplacementWindows
open HLOZProposition48Candidates
open LazyDecomposition
open TilingOrientedAllCreationStoppedCoordinate
open TilingOrientedShellZeroSourcePartition
open TilingShellZeroFactoredCapScreen
open TilingShellZeroSourcePartition
open VariableStoppedTracePartition

noncomputable section

abbrev DominoTiling := Tilings.Tiling

/-- Forget only the shell support field, retaining the complete physical
prefix, stateful retained word, boundary tail, and favorite data. -/
def eraseOrientedShellTrace {t : DominoTiling}
    (z : OrientedTypedFavoriteTilingTraceCode t) :
    OrientedAllCreationTraceCode t where
  external := z.external
  favorite := z.favorite

@[simp] theorem eraseOrientedShellTrace_fixed
    (t : DominoTiling) (o : Orientation) (window : Finset ℕ)
    (n : ℕ) (s : WalkPath) :
    eraseOrientedShellTrace
        (fixedOrientedTypedFavoriteTraceCode t o window n s) =
      fixedOrientedAllCreationTraceCode t o n s := rfl

@[simp] theorem eraseOrientedShellTrace_creation
    (t : DominoTiling) (o : Orientation) (m k w : ℕ) (s : WalkPath) :
    eraseOrientedShellTrace (orientedTypedCreationTraceCode t o m k w s) =
      fixedOrientedAllCreationTraceCode t o (creationTimeNat m k s) s := rfl

/-- Support selector used by the genuine source clock. -/
def orientedShellZeroSourceSupportAt
    (t : DominoTiling) (o : Orientation) (m : ℕ) :
    WalkPath → ℕ → Finset Point :=
  fun s n ↦ orientedTilingVTwoBases t o
    (shellZeroSourceTotalWindow m (shellWidth48 m)) s n

/-- Support selector used by the fixed-central replacement clock. -/
def orientedShellZeroReplacementSupportAt
    (t : DominoTiling) (o : Orientation) (m : ℕ) :
    WalkPath → ℕ → Finset Point :=
  fun s n ↦ orientedTilingVTwoBases t o
    (shellZeroSourceTotalWindow m (shellWidth48 m) ∪
      shellZeroReplacementTotalWindow m (shellWidth48 m)) s n

/-- A valid exact source trace atom is literally the corresponding supported
all-creation atom after forgetting the redundant stored support field. -/
theorem validExactSourceTraceAtom_subset_allCreationSupportTraceAtom
    {t : DominoTiling} {o : Orientation}
    {m k low externalLow externalHigh total : ℕ}
    {z : OrientedTypedFavoriteTilingTraceCode t} :
    orientedValidShellZeroExactSourceTraceAtom t o m k (shellWidth48 m) low
        externalLow externalHigh total z ⊆
      orientedAllCreationSupportTraceAtom t o m k
        (orientedShellZeroSourceSupportAt t o m)
        (eraseOrientedShellTrace z) z.supportBases := by
  intro s hs
  rcases hs with ⟨⟨hsource, htrace⟩, hvalid⟩
  refine ⟨⟨hvalid, hsource.1, ?_⟩, ?_⟩
  · simpa only [eraseOrientedShellTrace_creation] using
      congrArg eraseOrientedShellTrace htrace
  · have hsupport := congrArg
        (fun q : OrientedTypedFavoriteTilingTraceCode t ↦ q.supportBases)
        htrace
    change orientedTilingVTwoBases t o
      (shellZeroSourceTotalWindow m (shellWidth48 m)) s
        (creationTimeNat m k s) = z.supportBases
    simpa only [orientedTypedCreationTraceCode,
      fixedOrientedTypedFavoriteTraceCode,
      orientedShellZeroSourceSupportAt] using hsupport

/-- The canonical supported all-creation index underlying one nonempty
literal exact-source trace.  This is the index used to obtain the physical
prefixed carrier before imposing either shell screen. -/
noncomputable def sourceAllCreationSupportedAtomIndex
    (t : DominoTiling) (o : Orientation)
    (m k low externalLow externalHigh total : ℕ)
    (eta : LiteralShellZeroSupportedTraceIndex t o m k low externalLow
      externalHigh total) :
    OrientedAllCreationSupportedAtomIndex t o m k
      (orientedShellZeroSourceSupportAt t o m) := by
  refine ⟨(eraseOrientedShellTrace eta.1, eta.1.supportBases), ?_⟩
  rcases eta.2 with ⟨s, hs⟩
  exact ⟨s, validExactSourceTraceAtom_subset_allCreationSupportTraceAtom hs⟩

@[simp] theorem sourceAllCreationSupportedAtomIndex_trace
    (t : DominoTiling) (o : Orientation)
    (m k low externalLow externalHigh total : ℕ)
    (eta : LiteralShellZeroSupportedTraceIndex t o m k low externalLow
      externalHigh total) :
    (sourceAllCreationSupportedAtomIndex t o m k low externalLow
      externalHigh total eta).1.1 = eraseOrientedShellTrace eta.1 := rfl

@[simp] theorem sourceAllCreationSupportedAtomIndex_support
    (t : DominoTiling) (o : Orientation)
    (m k low externalLow externalHigh total : ℕ)
    (eta : LiteralShellZeroSupportedTraceIndex t o m k low externalLow
      externalHigh total) :
    (sourceAllCreationSupportedAtomIndex t o m k low externalLow
      externalHigh total eta).1.2 = eta.1.supportBases := rfl

/-- A valid replacement atom has the same erased trace and stored support,
now interpreted as the union-window support at the raised creation rank. -/
theorem validReplacementTraceAtom_subset_allCreationSupportTraceAtom
    {t : DominoTiling} {o : Orientation}
    {m k low externalLow externalHigh total central : ℕ}
    {z : OrientedTypedFavoriteTilingTraceCode t} :
    orientedValidShellZeroReplacementTraceAtom t o m k (shellWidth48 m) low
        externalLow externalHigh total central z ⊆
      orientedAllCreationSupportTraceAtom t o m
        (replacementCreationRank k total central)
        (orientedShellZeroReplacementSupportAt t o m)
        (eraseOrientedShellTrace z) z.supportBases := by
  intro s hs
  rcases hs with ⟨hreplacement, hvalid⟩
  let rank := replacementCreationRank k total central
  have htrace := orientedShellZeroReplacementTraceAtom_trace hreplacement
  refine ⟨⟨hvalid, hreplacement.1, ?_⟩, ?_⟩
  · simpa only [eraseOrientedShellTrace_fixed] using
      congrArg eraseOrientedShellTrace htrace
  · have hsupport := congrArg
        (fun q : OrientedTypedFavoriteTilingTraceCode t ↦ q.supportBases)
        htrace
    change orientedTilingVTwoBases t o
      (shellZeroSourceTotalWindow m (shellWidth48 m) ∪
        shellZeroReplacementTotalWindow m (shellWidth48 m)) s
        (creationTimeNat m (replacementCreationRank k total central) s) =
      z.supportBases
    simpa only [orientedShellZeroReplacementSupportAt,
      fixedOrientedTypedFavoriteTraceCode] using hsupport

/-- Nonempty valid replacement traces, indexed only on their genuine
support.  No obligation is imposed for a raw replacement atom that is empty. -/
abbrev LiteralShellZeroSupportedReplacementTraceIndex
    (t : DominoTiling) (o : Orientation)
    (m k low externalLow externalHigh total central : ℕ) :=
  {z : OrientedTypedFavoriteTilingTraceCode t //
    (orientedValidShellZeroReplacementTraceAtom t o m k (shellWidth48 m) low
      externalLow externalHigh total central z).Nonempty}

/-- The supported all-creation index underlying a nonempty literal
replacement trace at its raised creation rank. -/
noncomputable def replacementAllCreationSupportedAtomIndex
    (t : DominoTiling) (o : Orientation)
    (m k low externalLow externalHigh total central : ℕ)
    (eta : LiteralShellZeroSupportedReplacementTraceIndex t o m k low
      externalLow externalHigh total central) :
    OrientedAllCreationSupportedAtomIndex t o m
      (replacementCreationRank k total central)
      (orientedShellZeroReplacementSupportAt t o m) := by
  refine ⟨(eraseOrientedShellTrace eta.1, eta.1.supportBases), ?_⟩
  rcases eta.2 with ⟨s, hs⟩
  exact ⟨s, validReplacementTraceAtom_subset_allCreationSupportTraceAtom hs⟩

end

end Erdos1165.TilingShellZeroAllCreationTraceBridge
