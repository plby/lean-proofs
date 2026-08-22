/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.TilingOrientedExternalStaticDStoppedCoordinate
import ErdosProblems.Erdos1165.TilingShellZeroExternalStoppedCoordinateSpec

/-!
# Shell-zero external atoms as coarse static-D creation fibres

The corrected shell-zero carrier fixes only the physical oriented external
word.  This file forgets the shell screens and embeds every nonempty source or
raised-rank replacement atom into the corresponding coarse external creation
fibre.  No favorite data or pathwise `V₂` support is identified across the two
clocks.
-/

open Set

namespace Erdos1165.TilingShellZeroExternalStaticDBridge

open HLOZPathEvents HLOZProposition48Candidates HLOZShellZeroReplacementWindows
open LazyDecomposition
open TilingOrientedExternalStaticDStoppedCoordinate
open TilingOrientedShellExternalTracePartition
open TilingOrientedShellZeroSourcePartition
open TilingShellZeroExternalStoppedCoordinateSpec
open TilingShellZeroSourcePartition
open VariableStoppedTracePartition

noncomputable section

abbrev DominoTiling := Tilings.Tiling

theorem validExactSourceExternalTraceAtom_subset_coarse
    (t : DominoTiling) (o : Orientation)
    (m k w low externalLow externalHigh total : ℕ)
    (z : OrientedTilingTypedExternalWordCode t) :
    orientedValidShellZeroExactSourceExternalTraceAtom t o m k w low
        externalLow externalHigh total z ⊆
      orientedExternalOnlyCreationTraceAtom t o m k z := by
  rintro s ⟨⟨hsource, htrace⟩, hvalid⟩
  exact ⟨hvalid, hsource.1, htrace⟩

/-- A supported exact shell source gives an honest coarse physical-prefix
fibre at the source creation rank. -/
noncomputable def sourceCoarseSupportedIndex
    {t : DominoTiling} {o : Orientation}
    {m k low externalLow externalHigh total : ℕ}
    (eta : SupportedSourceExternalTraceIndex t o m k low externalLow
      externalHigh total) :
    TilingOrientedExternalStaticDStoppedCoordinate.SupportedIndex
      t o m k := by
  refine ⟨eta.1, ?_⟩
  rcases eta.2 with ⟨s, hs⟩
  exact ⟨s, validExactSourceExternalTraceAtom_subset_coarse
    t o m k (shellWidth48 m) low externalLow externalHigh total eta.1 hs⟩

/-- Supported external words for the honest raised-rank replacement atom. -/
abbrev SupportedReplacementExternalTraceIndex
    (t : DominoTiling) (o : Orientation)
    (m k w low externalLow externalHigh total central : ℕ) :=
  {z : OrientedTilingTypedExternalWordCode t //
    (orientedValidShellZeroReplacementExternalTraceAtom t o m k w low
      externalLow externalHigh total central z).Nonempty}

theorem validReplacementExternalTraceAtom_subset_coarse
    (t : DominoTiling) (o : Orientation)
    (m k w low externalLow externalHigh total central : ℕ)
    (z : OrientedTilingTypedExternalWordCode t) :
    orientedValidShellZeroReplacementExternalTraceAtom t o m k w low
        externalLow externalHigh total central z ⊆
      orientedExternalOnlyCreationTraceAtom t o m
        (replacementCreationRank k total central) z := by
  rintro s ⟨⟨hreplacement, htrace⟩, hvalid⟩
  exact ⟨hvalid, hreplacement.1, htrace⟩

/-- A supported replacement word gives an honest coarse physical-prefix
fibre at the raised creation rank. -/
noncomputable def replacementCoarseSupportedIndex
    {t : DominoTiling} {o : Orientation}
    {m k w low externalLow externalHigh total central : ℕ}
    (eta : SupportedReplacementExternalTraceIndex t o m k w low externalLow
      externalHigh total central) :
    TilingOrientedExternalStaticDStoppedCoordinate.SupportedIndex
      t o m (replacementCreationRank k total central) := by
  refine ⟨eta.1, ?_⟩
  rcases eta.2 with ⟨s, hs⟩
  exact ⟨s, validReplacementExternalTraceAtom_subset_coarse
    t o m k w low externalLow externalHigh total central eta.1 hs⟩

end

end Erdos1165.TilingShellZeroExternalStaticDBridge
