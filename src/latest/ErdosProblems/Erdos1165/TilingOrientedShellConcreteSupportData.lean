/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.TilingOrientedShellSupportSelector
import ErdosProblems.Erdos1165.TilingOrientedRetainedSourceLocalTime

/-!
# Concrete geometric data on an oriented exact source trace

An exact source trace fixes the oriented `V₂(I₁)` support.  The support is
the away-coordinate carrier, its cardinality is the exact source count, and
Theta-goodness puts every retained endpoint multiplicity in the external
window.  The concrete all-creation cap normalization then covers both shell
windows from logical cap zero onward.
-/

open Set

namespace Erdos1165.TilingOrientedShellConcreteSupportData

open HLOZProposition48Candidates HLOZShellZeroReplacementWindows
open HLOZSourceOrientedExternalLocalTime
open LazyDecomposition
open SpatialInsertionFiber
open TilingCappedMarginalization TilingLazyDecomposition
open TilingSpatialInsertionFiber
open TilingOrientedRetainedSourceLocalTime
open TilingOrientedShellZeroSourcePartition
open TilingOrientedShellSupportSelector
open TilingOrientedSupportAwayCoordinates
open TilingShellZeroFactoredCapScreen
open TilingShellZeroSourcePartition
open VariableStoppedTracePartition

noncomputable section

abbrev DominoTiling := Tilings.Tiling

private theorem mem_orientedTilingVTwoBases_union_of_mem_left
    (t : DominoTiling) (o : Orientation) (left right : Finset ℕ)
    (s : WalkPath) (n : ℕ) (b : Point)
    (hb : b ∈ orientedTilingVTwoBases t o left s n) :
    b ∈ orientedTilingVTwoBases t o (left ∪ right) s n := by
  classical
  rw [mem_orientedTilingVTwoBases_iff] at hb ⊢
  refine ⟨?_, hb.2⟩
  unfold tilingVTwoBases at hb ⊢
  rw [Finset.mem_filter] at hb ⊢
  refine ⟨hb.1.1, hb.1.2.1, ?_⟩
  exact Finset.mem_union_left _ hb.1.2.2

/-- Literal cap/support data obtained from a nonempty exact source trace.
No probability estimate and no eventual arithmetic enter this construction. -/
noncomputable def literalShellZeroSourceCoordinateSupportData
    (t : DominoTiling) (o : Orientation)
    (m k low externalLow externalHigh total : ℕ)
    (eta : LiteralShellZeroSupportedTraceIndex t o m k low externalLow
      externalHigh total) (cap : ℕ)
    (hn : ∀ s ∈ orientedValidShellZeroExactSourceTraceAtom t o m k
      (shellWidth48 m) low externalLow externalHigh total eta.1,
      0 < creationTimeNat m k s) :
    LiteralShellZeroCoordinateSupportData
      (cap := max eta.1.external.retainedCount (m + shellWidth48 m) + cap)
      (m := m) (externalLow := externalLow)
      (externalHigh := externalHigh) (total := total)
      t eta.1.external.start eta.1.external.retained
      (supportComplementDistinguished t eta.1.external.start
        eta.1.external.retained eta.1.supportBases)
      (fun _ ↦ max eta.1.external.retainedCount
        (m + shellWidth48 m) + 1) := by
  classical
  rcases eta with ⟨z, hz⟩
  rcases hz with ⟨s, hs⟩
  have hsource := hs.1.1
  have htrace := hs.1.2
  have hvalid := hs.2
  let n := creationTimeNat m k s
  change ReachesThreshold s m k ∧
      tilingDEtaAt t m k (shellWidth48 m) low s n ∧
      orientedTilingThetaBases t o m (shellWidth48 m) externalLow
        externalHigh s n = ∅ ∧
      (orientedTilingVTwoBases t o
        (shellZeroSourceTotalWindow m (shellWidth48 m)) s n).card = total
    at hsource
  have htrace' : fixedOrientedTypedFavoriteTraceCode t o
      (shellZeroSourceTotalWindow m (shellWidth48 m)) n s = z := htrace
  have hn' : 0 < n := by simpa only [n] using hn s hs
  subst z
  let code := fixedOrientedTypedExternalWordCode t o n s
  let S := orientedTilingVTwoBases t o
    (shellZeroSourceTotalWindow m (shellWidth48 m)) s n
  have hzero : 0 ∉ shellZeroSourceTotalWindow m (shellWidth48 m) := by
    simp only [mem_shellZeroSourceTotalWindow]
    omega
  have hrepresented : S ⊆
      tilingExternalDominoBases t code.start code.retained := by
    exact orientedTilingVTwoBases_subset_fixedExternalDominoBases
      t o (shellZeroSourceTotalWindow m (shellWidth48 m)) s n hvalid hzero
  dsimp only [orientedTypedCreationTraceCode,
    fixedOrientedTypedFavoriteTraceCode] at ⊢
  refine {
    card := ?_
    externalWindow := ?_
    sourceUpper := ?_
    replacementUpper := ?_
    sourceCap := ?_
    replacementCap := ?_ }
  · simpa only [code, S, n] using
      (card_supportAwayDomino t code.start code.retained S hrepresented).trans
        hsource.2.2.2
  · intro b
    change externalLow ≤ Fintype.card
        (TilingCoordinatesAt t code.start code.retained b.1) ∧
      Fintype.card (TilingCoordinatesAt t code.start code.retained b.1) <
        externalHigh
    have hbS : b.1.1 ∈ S :=
      (away_mem_support_iff t code.start code.retained S b.1).1 b.2
    have hbcompat : OrientationCompatible o b.1.1 :=
      (mem_orientedTilingVTwoBases_iff t o _ s n b.1.1).mp hbS |>.2
    have hbUnion : b.1.1 ∈ orientedTilingVTwoBases t o
        (shellZeroSourceTotalWindow m (shellWidth48 m) ∪
          shellZeroReplacementTotalWindow m (shellWidth48 m)) s n :=
      mem_orientedTilingVTwoBases_union_of_mem_left t o _ _ s n b.1.1 hbS
    have hwindow : externalLow ≤
          tilingSourceExternalBaseLocalTime t o s n b.1.1 ∧
        tilingSourceExternalBaseLocalTime t o s n b.1.1 < externalHigh := by
      by_contra hbad
      have hmem : b.1.1 ∈ orientedTilingThetaBases t o m
          (shellWidth48 m) externalLow externalHigh s n := by
        exact Finset.mem_filter.mpr ⟨hbUnion, hbad⟩
      rw [hsource.2.2.1] at hmem
      simp at hmem
    rw [card_tilingCoordinatesAt_fixedOrientedTypedExternalWordCode_eq_source
      t o s n hvalid hn' b.1 hbcompat]
    exact hwindow
  · intro b v hv
    simp only [mem_shellZeroSourceFailureWindow] at hv
    omega
  · intro b v hv
    simp only [mem_shellZeroReplacementFailureWindow] at hv
    omega
  · intro b v hv
    simp only [mem_shellZeroSourceFailureWindow] at hv
    omega
  · intro b v hv
    simp only [mem_shellZeroReplacementFailureWindow] at hv
    omega

end

end Erdos1165.TilingOrientedShellConcreteSupportData
