/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.TilingShellZeroExternalStaticDBridge
import ErdosProblems.Erdos1165.TilingShellZeroExternalStaticSupportData

/-!
# Static-support shell atoms as coarse accepted-creation fibres

This module only forgets the shell screen.  It preserves the explicit
`(z,S)` index and uses `D = externalBases \ S` as the common static split.
-/

open Set

namespace Erdos1165.TilingShellZeroStaticSupportCoarseBridge

open LazyDecomposition TilingOrientedExternalStaticDStoppedCoordinate
open TilingOrientedShellZeroSourcePartition
open TilingOrientedSupportAwayCoordinates
open TilingShellZeroExternalStaticDBridge
open TilingShellZeroExternalStaticSupportData
open TilingShellZeroExternalStaticSupportPartition
open TilingSpatialInsertionFiber

noncomputable section

abbrev DominoTiling := Tilings.Tiling

/-- The common static distinguished set complementary to the moved support. -/
def staticDistinguished
    {t : DominoTiling} (z : OrientedTilingTypedExternalWordCode t)
    (S : Finset Point) : Finset Point :=
  supportComplementDistinguished t z.start z.retained S

theorem staticDistinguished_subset
    {t : DominoTiling} (z : OrientedTilingTypedExternalWordCode t)
    (S : Finset Point) :
    staticDistinguished z S ⊆
      tilingExternalDominoBases t z.start z.retained := by
  intro b hb
  exact (Finset.mem_sdiff.mp hb).1

/-- Forget a supported `(z,S)` source atom to the coarse external-word
creation fibre at rank `k`. -/
noncomputable def sourceCoarseIndex
    {t : DominoTiling} {o : Orientation}
    {m k w low externalLow externalHigh total : ℕ}
    (eta : SupportedSourceStaticSupportIndex t o m k w low externalLow
      externalHigh total) :
    TilingOrientedExternalStaticDStoppedCoordinate.SupportedIndex t o m k := by
  refine ⟨eta.1.1, ?_⟩
  rcases eta.2 with ⟨s, hs⟩
  exact ⟨s, validExactSourceExternalTraceAtom_subset_coarse
    t o m k w low externalLow externalHigh total eta.1.1 hs.1⟩

/-- A nonempty replacement `(z,S)` atom gives the corresponding coarse
external-word fibre at the raised rank. -/
noncomputable def replacementCoarseIndex
    {t : DominoTiling} {o : Orientation}
    {m k w low externalLow externalHigh total central : ℕ}
    {z : OrientedTilingTypedExternalWordCode t} {S : Finset Point}
    (hreplacement :
      (orientedValidShellZeroReplacementStaticSupportAtom t o m k w low
        externalLow externalHigh total central z S).Nonempty) :
    TilingOrientedExternalStaticDStoppedCoordinate.SupportedIndex t o m
      (TilingShellZeroSourcePartition.replacementCreationRank
        k total central) := by
  refine ⟨z, ?_⟩
  rcases hreplacement with ⟨s, hs⟩
  exact ⟨s, validReplacementExternalTraceAtom_subset_coarse
    t o m k w low externalLow externalHigh total central z hs.1⟩

end

end Erdos1165.TilingShellZeroStaticSupportCoarseBridge
