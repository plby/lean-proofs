/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.TilingShellZeroStaticReplacementPathRecovery

/-!
# Static-support recovery at an honest replacement clock

The actual-increment coordinate screen reconstructs the replacement values
on the static moved set.  Outside that set the two endpoint local times are
unchanged.  This module proves that the replacement `V₂(I₁) ∪ V₂(I₀)`
support is therefore exactly the original static source support.
-/

namespace Erdos1165.TilingShellZeroStaticReplacementSupportRecovery

open HLOZShellZeroReplacementWindows HLOZSourceOrientedExternalLocalTime
open LazyDecomposition
open SpatialInsertionFiber
open TilingOrientedRetainedSourceLocalTime
open TilingLazyDecomposition TilingOrientedShellZeroSourcePartition
open TilingShellZeroSourcePartition TilingSpatialInsertionFiber

noncomputable section

abbrev DominoTiling := Tilings.Tiling

private theorem mem_visitedTilingBases_of_vTwoAt
    {t : DominoTiling} {window : Finset ℕ} {s : WalkPath} {n : ℕ}
    {b : Point} (hbBase : IsTilingBase t b)
    (hpositive : ∀ j ∈ window, 0 < j)
    (hVTwo : tilingVTwoAt t window s n b) :
    b ∈ visitedTilingBases t s n := by
  rw [visitedTilingBases, Finset.mem_image]
  refine ⟨b, (mem_visitedSites_iff_localTime_pos s n b).2 ?_, ?_⟩
  · exact hpositive _ hVTwo.2
  · simp only [tilingBase, if_pos hbBase]

private theorem mem_orientedVTwo_of_vTwoAt
    {t : DominoTiling} {o : Orientation} {window : Finset ℕ}
    {s : WalkPath} {n : ℕ} {b : Point}
    (hbBase : IsTilingBase t b) (hbCompat : OrientationCompatible o b)
    (hpositive : ∀ j ∈ window, 0 < j)
    (hVTwo : tilingVTwoAt t window s n b) :
    b ∈ orientedTilingVTwoBases t o window s n := by
  classical
  rw [mem_orientedTilingVTwoBases_iff]
  refine ⟨?_, hbCompat⟩
  change b ∈ (visitedTilingBases t s n).filter
    (tilingVTwoAt t window s n)
  exact Finset.mem_filter.mpr
    ⟨mem_visitedTilingBases_of_vTwoAt hbBase hpositive hVTwo, hVTwo⟩

/-- The honest replacement support is the same static moved set, even
though its members are split between `I₁` and `I₀`. -/
theorem orientedReplacementSupport_eq_staticSupport
    {t : DominoTiling} {o : Orientation} {m k w low : ℕ}
    {sSource sReplacement : WalkPath} {nSource nReplacement : ℕ}
    (S : Finset Point) (hlow : low < m)
    (hsourceD : tilingDEtaAt t m k w low sSource nSource)
    (hsourceSupport : orientedTilingVTwoBases t o
      (shellZeroSourceTotalWindow m w) sSource nSource = S)
    (hreplacementS : ∀ b ∈ S,
      tilingVTwoAt t (shellZeroSourceTotalWindow m w)
          sReplacement nReplacement b ∨
        tilingVTwoAt t (shellZeroReplacementTotalWindow m w)
          sReplacement nReplacement b)
    (hbaseOutside : ∀ b, IsTilingBase t b → b ∉ S →
      localTime sReplacement nReplacement b = localTime sSource nSource b)
    (hpartnerOutside : ∀ b, IsTilingBase t b → b ∉ S →
      localTime sReplacement nReplacement (tilingPartner t b) =
        localTime sSource nSource (tilingPartner t b)) :
    orientedTilingVTwoBases t o (shellZeroSourceTotalWindow m w)
          sReplacement nReplacement ∪
        orientedTilingVTwoBases t o (shellZeroReplacementTotalWindow m w)
          sReplacement nReplacement = S := by
  classical
  apply Finset.Subset.antisymm
  · intro b hb
    rcases Finset.mem_union.mp hb with hb | hb
    · have hbInfo := (mem_orientedTilingVTwoBases_iff t o
          (shellZeroSourceTotalWindow m w) sReplacement nReplacement b).mp hb
      have hbRaw := hbInfo.1
      change b ∈ (visitedTilingBases t sReplacement nReplacement).filter
        (tilingVTwoAt t (shellZeroSourceTotalWindow m w)
          sReplacement nReplacement) at hbRaw
      have hbBase := HLOZThetaSourceBalance.isTilingBase_of_mem_visitedTilingBases
        (Finset.mem_filter.mp hbRaw).1
      by_contra hbNot
      have hbeq := hbaseOutside b hbBase hbNot
      have hpeq := hpartnerOutside b hbBase hbNot
      have hV := (Finset.mem_filter.mp hbRaw).2
      have hSourceV : tilingVTwoAt t (shellZeroSourceTotalWindow m w)
          sSource nSource b := by
        unfold tilingVTwoAt at hV ⊢
        rw [← hbeq, ← hpeq]
        exact hV
      have hbSource : b ∈ orientedTilingVTwoBases t o
          (shellZeroSourceTotalWindow m w) sSource nSource :=
        mem_orientedVTwo_of_vTwoAt hbBase hbInfo.2
          (by intro j hj; have := (mem_shellZeroSourceTotalWindow.mp hj).1; omega)
          hSourceV
      exact hbNot (hsourceSupport ▸ hbSource)
    · have hbInfo := (mem_orientedTilingVTwoBases_iff t o
          (shellZeroReplacementTotalWindow m w) sReplacement nReplacement b).mp hb
      have hbRaw := hbInfo.1
      change b ∈ (visitedTilingBases t sReplacement nReplacement).filter
        (tilingVTwoAt t (shellZeroReplacementTotalWindow m w)
          sReplacement nReplacement) at hbRaw
      have hbBase := HLOZThetaSourceBalance.isTilingBase_of_mem_visitedTilingBases
        (Finset.mem_filter.mp hbRaw).1
      by_contra hbNot
      have hbeq := hbaseOutside b hbBase hbNot
      have hV := (Finset.mem_filter.mp hbRaw).2
      have hgt : m < localTime sReplacement nReplacement b := by
        have := (mem_shellZeroReplacementTotalWindow.mp hV.2).1
        omega
      rw [hbeq] at hgt
      rcases hsourceD.2.1 b hbBase with hOne | hTwo | hThree
      · unfold tilingVOneAt at hOne
        omega
      · have hlt := (mem_shellZeroSourceTotalWindow.mp hTwo.2).2
        omega
      · unfold tilingVThreeAt at hThree
        rcases hThree with hbase | hpartner <;> omega
  · intro b hbS
    have hbSource : b ∈ orientedTilingVTwoBases t o
        (shellZeroSourceTotalWindow m w) sSource nSource := by
      rw [hsourceSupport]
      exact hbS
    have hbCompat := (mem_orientedTilingVTwoBases_iff t o
      (shellZeroSourceTotalWindow m w) sSource nSource b).mp hbSource |>.2
    have hbRaw := (mem_orientedTilingVTwoBases_iff t o
      (shellZeroSourceTotalWindow m w) sSource nSource b).mp hbSource |>.1
    change b ∈ (visitedTilingBases t sSource nSource).filter
      (tilingVTwoAt t (shellZeroSourceTotalWindow m w) sSource nSource) at hbRaw
    have hbBase := HLOZThetaSourceBalance.isTilingBase_of_mem_visitedTilingBases
      (Finset.mem_filter.mp hbRaw).1
    rcases hreplacementS b hbS with hV | hV
    · exact Finset.mem_union_left _
        (mem_orientedVTwo_of_vTwoAt hbBase hbCompat
          (by intro j hj; have := (mem_shellZeroSourceTotalWindow.mp hj).1; omega)
          hV)
    · exact Finset.mem_union_right _
        (mem_orientedVTwo_of_vTwoAt hbBase hbCompat
          (by intro j hj; have := (mem_shellZeroReplacementTotalWindow.mp hj).1; omega)
          hV)

/-- Once the honest replacement support is identified with `S`, the
oriented `Theta` screen is exactly the external-window condition on `S`. -/
theorem orientedTilingThetaBases_eq_empty_of_staticSupport
    {t : DominoTiling} {o : Orientation}
    {m w externalLow externalHigh : ℕ} {s : WalkPath} {n : ℕ}
    (S : Finset Point)
    (hsupport : orientedTilingVTwoBases t o
        (shellZeroSourceTotalWindow m w) s n ∪
      orientedTilingVTwoBases t o
        (shellZeroReplacementTotalWindow m w) s n = S)
    (hwindow : ∀ b ∈ S,
      externalLow ≤ tilingSourceExternalBaseLocalTime t o s n b ∧
        tilingSourceExternalBaseLocalTime t o s n b < externalHigh) :
    orientedTilingThetaBases t o m w externalLow externalHigh s n = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro b hb
  rw [orientedTilingThetaBases, Finset.mem_filter] at hb
  have hbUnion : b ∈ orientedTilingVTwoBases t o
        (shellZeroSourceTotalWindow m w) s n ∪
      orientedTilingVTwoBases t o
        (shellZeroReplacementTotalWindow m w) s n := by
    have hbRaw := (mem_orientedTilingVTwoBases_iff t o
      (shellZeroSourceTotalWindow m w ∪ shellZeroReplacementTotalWindow m w)
      s n b).mp hb.1
    have hbRawMem := hbRaw.1
    change b ∈ (visitedTilingBases t s n).filter
        (tilingVTwoAt t
          (shellZeroSourceTotalWindow m w ∪ shellZeroReplacementTotalWindow m w)
          s n) at hbRawMem
    have hmem := Finset.mem_filter.mp hbRawMem
    rcases Finset.mem_union.mp hmem.2.2 with hsrc | hrep
    · refine Finset.mem_union_left _ ?_
      rw [mem_orientedTilingVTwoBases_iff]
      refine ⟨?_, hbRaw.2⟩
      change b ∈ (visitedTilingBases t s n).filter
        (tilingVTwoAt t (shellZeroSourceTotalWindow m w) s n)
      exact Finset.mem_filter.mpr
        ⟨hmem.1, hmem.2.1, hsrc⟩
    · refine Finset.mem_union_right _ ?_
      rw [mem_orientedTilingVTwoBases_iff]
      refine ⟨?_, hbRaw.2⟩
      change b ∈ (visitedTilingBases t s n).filter
        (tilingVTwoAt t (shellZeroReplacementTotalWindow m w) s n)
      exact Finset.mem_filter.mpr
        ⟨hmem.1, hmem.2.1, hrep⟩
  exact hb.2 (hwindow b (hsupport ▸ hbUnion))

/-- A fixed oriented external word transports the literal retained-coordinate
window to the endpoint-chain external local time on every represented member
of the static support. -/
theorem sourceExternalWindow_of_fixedCode
    {t : DominoTiling} {o : Orientation} {n : ℕ} {s : WalkPath}
    {z : OrientedTilingTypedExternalWordCode t} {S : Finset Point}
    {externalLow externalHigh : ℕ}
    (hvalid : s ∈ VariableStoppedTracePartition.validStepWalk)
    (hn : 0 < n)
    (hcode : fixedOrientedTypedExternalWordCode t o n s = z)
    (hrepresented : S ⊆ tilingExternalDominoBases t z.start z.retained)
    (hcompat : ∀ b ∈ S, OrientationCompatible o b)
    (hcardWindow : ∀ b : TilingExternalDomino t z.start z.retained,
      b.1 ∈ S → externalLow ≤ Fintype.card
          (TilingCoordinatesAt t z.start z.retained b) ∧
        Fintype.card (TilingCoordinatesAt t z.start z.retained b) <
          externalHigh) :
    ∀ b ∈ S,
      externalLow ≤ tilingSourceExternalBaseLocalTime t o s n b ∧
        tilingSourceExternalBaseLocalTime t o s n b < externalHigh := by
  subst z
  intro b hb
  let bext : TilingExternalDomino t
      (fixedOrientedTypedExternalWordCode t o n s).start
      (fixedOrientedTypedExternalWordCode t o n s).retained :=
    ⟨b, hrepresented hb⟩
  rw [← card_tilingCoordinatesAt_fixedOrientedTypedExternalWordCode_eq_source
    t o s n hvalid hn bext (hcompat b hb)]
  exact hcardWindow bext hb

end

end Erdos1165.TilingShellZeroStaticReplacementSupportRecovery
