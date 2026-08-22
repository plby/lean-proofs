/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.TilingOrientedPrefixedBoundarySourceLocalTime
import ErdosProblems.Erdos1165.TilingShellZeroExternalStaticSupportData

/-!
# Uniform facts carried by a supported static shell source

These facts are extracted once from nonemptiness of a literal `(z,S)` source
atom.  They are independent of the later capped insertion vector.
-/

namespace Erdos1165.TilingShellZeroSupportedSourceStaticFacts

open HLOZPathEvents HLOZSourceOrientedThetaAcceptedCreationPath
open LazyDecomposition
open PathInsertion PreStoppingFiber SpatialInsertionFiber StoppedInsertion
open VariableStoppedFiber
open TilingCappedMarginalization
open TilingOrientedAllRepresentedExternalFiber
open TilingOrientedPrefixedBoundarySourceLocalTime
open TilingOrientedShellZeroSourcePartition
open TilingPrefixedFavoriteTraceSupport TilingPrefixedInsertedLocalTime
open TilingPrefixedStoppedProductDisintegration
open TilingShellZeroExternalStaticSupportData
open TilingShellZeroExternalStaticSupportPartition
open TilingSpatialInsertionFiber
open VariableStoppedTracePartition

noncomputable section

abbrev DominoTiling := Tilings.Tiling

/-- Forget the shell predicates but retain the nonempty oriented external
creation atom. -/
noncomputable def toAllRepresentedIndex
    {t : DominoTiling} {o : Orientation}
    {m k w low externalLow externalHigh total : ℕ}
    (eta : SupportedSourceStaticSupportIndex t o m k w low externalLow
      externalHigh total) :
    TilingOrientedAllRepresentedExternalFiber.SupportedIndex t o m k := by
  refine ⟨eta.1.1, ?_⟩
  rcases eta.2 with ⟨s, hs⟩
  exact ⟨s, hs.1.2, hs.1.1.1.1, hs.1.1.2⟩

/-- Every member of the static source support belongs to the selected
endpoint orientation. -/
theorem orientationCompatible_of_mem_staticSupport
    {t : DominoTiling} {o : Orientation}
    {m k w low externalLow externalHigh total : ℕ}
    (eta : SupportedSourceStaticSupportIndex t o m k w low externalLow
      externalHigh total) :
    ∀ b ∈ eta.1.2, OrientationCompatible o b := by
  rcases eta.2 with ⟨s, hs⟩
  intro b hb
  have hsupport := hs.2
  change sourceStaticSupport t o m k w s = eta.1.2 at hsupport
  have hb' : b ∈ sourceStaticSupport t o m k w s := by
    rw [hsupport]
    exact hb
  exact (mem_orientedTilingVTwoBases_iff t o
    (HLOZShellZeroReplacementWindows.shellZeroSourceTotalWindow m w)
      s (creationTimeNat m k s) b).mp hb' |>.2

/-- The static support has the advertised exact source count. -/
theorem card_staticSupport
    {t : DominoTiling} {o : Orientation}
    {m k w low externalLow externalHigh total : ℕ}
    (eta : SupportedSourceStaticSupportIndex t o m k w low externalLow
      externalHigh total) : eta.1.2.card = total := by
  rcases eta.2 with ⟨s, hs⟩
  have hcard := hs.1.1.1.2.2.2
  have hsupport := hs.2
  change sourceStaticSupport t o m k w s = eta.1.2 at hsupport
  change (sourceStaticSupport t o m k w s).card = total at hcard
  simpa only [hsupport] using hcard

/-- Every capped reconstruction of a supported source external word has
exactly that external word. -/
theorem fixedCode_prefixedInsertion
    {t : DominoTiling} {o : Orientation}
    {m k w low externalLow externalHigh total : ℕ}
    (eta : SupportedSourceStaticSupportIndex t o m k w low externalLow
      externalHigh total) (hm : 1 < m) (hk : 0 < k)
    (q : Fin (eta.1.1.retainedCount + 1) → ℕ) :
    let v := prefixedTilingInsertionPrefixList eta.1.1.initial.1 t
      eta.1.1.start eta.1.1.retained q eta.1.1.tail.1
    fixedOrientedTypedExternalWordCode t o v.length
        (trajectory (extendPrefix (directionVectorOfList v))) = eta.1.1 := by
  exact HLOZSourceOrientedThetaAcceptedCreationPath.fixedCode_prefixedInsertion
    (toAllRepresentedIndex eta) hm hk q

/-- Prefix-correct fixed boundary local time is the retained-coordinate
multiplicity at every represented support base. -/
theorem boundaryLocalTime_eq_coordinateCard
    {t : DominoTiling} {o : Orientation}
    {m k w low externalLow externalHigh total : ℕ}
    (eta : SupportedSourceStaticSupportIndex t o m k w low externalLow
      externalHigh total) (hm : 1 < m) (hk : 0 < k)
    (q : Fin (eta.1.1.retainedCount + 1) → ℕ)
    (b : TilingExternalDomino t eta.1.1.start eta.1.1.retained)
    (hb : b.1 ∈ eta.1.2) :
    prefixedTilingFixedBoundaryLocalTime eta.1.1.initial.1 eta.1.1.start
        eta.1.1.retained
        (prefixedTilingInsertionTerminal eta.1.1.initial t eta.1.1.start
          eta.1.1.retained q eta.1.1.tail) b.1 =
      Fintype.card (TilingCoordinatesAt t eta.1.1.start
        eta.1.1.retained b) := by
  exact prefixedBoundaryLocalTime_eq_coordinateCard
    (toAllRepresentedIndex eta) hm hk q b
      (orientationCompatible_of_mem_staticSupport eta b.1 hb)

end

end Erdos1165.TilingShellZeroSupportedSourceStaticFacts
