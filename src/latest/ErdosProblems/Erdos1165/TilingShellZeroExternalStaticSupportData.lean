/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.TilingOrientedRetainedSourceLocalTime
import ErdosProblems.Erdos1165.TilingOrientedShellSupportSelector
import ErdosProblems.Erdos1165.TilingOrientedSupportAwayCoordinates
import ErdosProblems.Erdos1165.TilingShellZeroExternalStaticSupportPartition
import ErdosProblems.Erdos1165.TilingShellZeroFactoredCapScreen

/-!
# Literal window data on an external word and static moved support

This is the external-word counterpart of the older full-favorite support
constructor.  Its static carrier is exactly the source `V₂(I₁)` set.  The
replacement clock may split that same set into `I₁` and `I₀`; it is never
required to have the same current-favorite trace or the same `V₂(I₁)` set.
-/

open Set

namespace Erdos1165.TilingShellZeroExternalStaticSupportData

open HLOZProposition48Candidates HLOZShellZeroReplacementWindows
open HLOZSourceOrientedExternalLocalTime
open LazyDecomposition SpatialInsertionFiber
open TilingCappedMarginalization TilingOrientedRetainedSourceLocalTime
open TilingOrientedShellZeroSourcePartition
open TilingOrientedShellSupportSelector
open TilingOrientedSupportAwayCoordinates
open TilingShellZeroExternalStaticSupportPartition
open TilingShellZeroFactoredCapScreen TilingShellZeroSourcePartition
open TilingSpatialInsertionFiber VariableStoppedTracePartition

noncomputable section

abbrev DominoTiling := Tilings.Tiling

theorem creationTimeNat_pos_of_mem_sourceStaticSupportAtom
    {t : DominoTiling} {o : Orientation}
    {m k w low externalLow externalHigh total : ℕ}
    {z : OrientedTilingTypedExternalWordCode t} {S : Finset Point}
    {s : WalkPath}
    (hm : 1 < m)
    (hs : s ∈ orientedValidShellZeroExactSourceStaticSupportAtom
      t o m k w low externalLow externalHigh total z S) :
    0 < creationTimeNat m k s := by
  by_contra hn
  have hzero : creationTimeNat m k s = 0 := by omega
  have hendpoint := hs.1.1.1.2.1.2
  rw [hzero] at hendpoint
  simp [localTime, localTimePrefix, pathPrefix] at hendpoint
  omega

/-- The static source support is represented in the retained external word. -/
theorem sourceStaticSupport_subset_externalDominoBases
    {t : DominoTiling} {o : Orientation}
    {m k w low externalLow externalHigh total : ℕ}
    (eta : SupportedSourceStaticSupportIndex t o m k w low externalLow
      externalHigh total) :
    eta.1.2 ⊆ tilingExternalDominoBases t eta.1.1.start
      eta.1.1.retained := by
  rcases eta.2 with ⟨s, hs⟩
  have hvalid := hs.1.2
  have htrace := hs.1.1.2
  have hsupport := hs.2
  change fixedOrientedTypedExternalWordCode t o (creationTimeNat m k s) s =
      eta.1.1 at htrace
  change sourceStaticSupport t o m k w s = eta.1.2 at hsupport
  have hzero : 0 ∉ shellZeroSourceTotalWindow m w := by
    simp only [mem_shellZeroSourceTotalWindow]
    omega
  have hrepresented :=
    orientedTilingVTwoBases_subset_fixedExternalDominoBases
      t o (shellZeroSourceTotalWindow m w) s (creationTimeNat m k s)
        hvalid hzero
  rw [← hsupport, ← htrace]
  exact hrepresented

/-- Literal cap and retained-count window data on the static moved support.
No probability or asymptotic arithmetic is used. -/
noncomputable def coordinateSupportData
    (t : DominoTiling) (o : Orientation)
    (m k w low externalLow externalHigh total cap : ℕ)
    (eta : SupportedSourceStaticSupportIndex t o m k w low externalLow
      externalHigh total)
    (hm : 1 < m) :
    LiteralShellZeroCoordinateSupportData
      (cap := max eta.1.1.retainedCount (m + shellWidth48 m) + cap)
      (m := m) (externalLow := externalLow)
      (externalHigh := externalHigh) (total := total)
      t eta.1.1.start eta.1.1.retained
      (supportComplementDistinguished t eta.1.1.start eta.1.1.retained
        eta.1.2)
      (fun _ ↦ max eta.1.1.retainedCount (m + shellWidth48 m) + 1) := by
  classical
  rcases eta with ⟨⟨z, S⟩, heta⟩
  rcases heta with ⟨s, hs⟩
  have hsource := hs.1.1.1
  have htrace := hs.1.1.2
  have hvalid := hs.1.2
  have hsupport := hs.2
  change fixedOrientedTypedExternalWordCode t o (creationTimeNat m k s) s = z
    at htrace
  change sourceStaticSupport t o m k w s = S at hsupport
  let n := creationTimeNat m k s
  have hn' : 0 < n := by
    simpa only [n] using
      creationTimeNat_pos_of_mem_sourceStaticSupportAtom hm hs
  have hzero : 0 ∉ shellZeroSourceTotalWindow m w := by
    simp only [mem_shellZeroSourceTotalWindow]
    omega
  have hrepresentedSource : sourceStaticSupport t o m k w s ⊆
      tilingExternalDominoBases t
        (fixedOrientedTypedExternalWordCode t o n s).start
        (fixedOrientedTypedExternalWordCode t o n s).retained := by
    exact orientedTilingVTwoBases_subset_fixedExternalDominoBases
      t o (shellZeroSourceTotalWindow m w) s n hvalid hzero
  subst z
  subst S
  refine {
    card := ?_
    externalWindow := ?_
    sourceUpper := ?_
    replacementUpper := ?_
    sourceCap := ?_
    replacementCap := ?_ }
  · rw [card_supportAwayDomino t
      (fixedOrientedTypedExternalWordCode t o n s).start
      (fixedOrientedTypedExternalWordCode t o n s).retained
      (sourceStaticSupport t o m k w s) hrepresentedSource]
    exact hsource.2.2.2
  · intro b
    change externalLow ≤ Fintype.card
        (TilingCoordinatesAt t
          (fixedOrientedTypedExternalWordCode t o n s).start
          (fixedOrientedTypedExternalWordCode t o n s).retained b.1) ∧
      Fintype.card
        (TilingCoordinatesAt t
          (fixedOrientedTypedExternalWordCode t o n s).start
          (fixedOrientedTypedExternalWordCode t o n s).retained b.1) <
        externalHigh
    have hbS : b.1.1 ∈ sourceStaticSupport t o m k w s :=
      (away_mem_support_iff t
        (fixedOrientedTypedExternalWordCode t o n s).start
        (fixedOrientedTypedExternalWordCode t o n s).retained
        (sourceStaticSupport t o m k w s) b.1).1 b.2
    change b.1.1 ∈ orientedTilingVTwoBases t o
      (shellZeroSourceTotalWindow m w) s n at hbS
    have hbcompat : OrientationCompatible o b.1.1 :=
      (mem_orientedTilingVTwoBases_iff t o _ s n b.1.1).mp hbS |>.2
    have hbUnion : b.1.1 ∈ orientedTilingVTwoBases t o
        (shellZeroSourceTotalWindow m w ∪
          shellZeroReplacementTotalWindow m w) s n := by
      rw [mem_orientedTilingVTwoBases_iff] at hbS ⊢
      refine ⟨?_, hbS.2⟩
      unfold tilingVTwoBases at hbS ⊢
      rw [Finset.mem_filter] at hbS ⊢
      exact ⟨hbS.1.1, hbS.1.2.1,
        Finset.mem_union_left _ hbS.1.2.2⟩
    have hwindow : externalLow ≤
          tilingSourceExternalBaseLocalTime t o s n b.1.1 ∧
        tilingSourceExternalBaseLocalTime t o s n b.1.1 < externalHigh := by
      by_contra hbad
      have hmem : b.1.1 ∈ orientedTilingThetaBases t o m w
          externalLow externalHigh s n :=
        Finset.mem_filter.mpr ⟨hbUnion, hbad⟩
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

end Erdos1165.TilingShellZeroExternalStaticSupportData
