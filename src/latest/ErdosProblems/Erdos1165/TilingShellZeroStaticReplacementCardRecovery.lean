/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.TilingShellZeroStaticReplacementSupportRecovery
import ErdosProblems.Erdos1165.TilingShellZeroStaticSupportCoordinateIff

/-!
# Exact replacement cardinalities from a fixed actual-increment screen

The subset `A` in the finite product screen is literally the replacement
path's `V₂(I₁)` set after reindexing by the static support equivalence.
Consequently its complement is the `V₂(I₀)` set, with no guessed rank.
-/

namespace Erdos1165.TilingShellZeroStaticReplacementCardRecovery

open FiniteDominoProductLaw HLOZShellZeroEndpointIncrementPartition
open HLOZShellZeroReplacementWindows LazyDecomposition
open PathInsertion PreStoppingFiber PreStoppingSpatialLaw
open SpatialInsertionFiber StoppedInsertion VariableStoppedFiber
open TilingCappedMarginalization TilingLazyDecomposition
open TilingInsertedLocalTime
open TilingOrientedShellZeroSourcePartition TilingOrientedSupportAwayCoordinates
open TilingPrefixedFavoriteTraceSupport TilingPrefixedInsertedLocalTime
open TilingPrefixedStoppedProductDisintegration
open TilingShellZeroEndpointIncrementScreen
open TilingShellZeroStaticSupportCoordinateIff
open TilingShellZeroStaticSupportLocalTimeTransport
open TilingShellZeroSourcePartition TilingSpatialInsertionFiber

noncomputable section

abbrev DominoTiling := Tilings.Tiling

/-- The actual-increment product screen has exactly the advertised literal
`I₁` and `I₀` cardinalities on the replacement path. -/
theorem card_orientedVTwo_source_and_replacement_of_incrementScreen
    (initial : BoundaryTail) {i cap m w central total : ℕ}
    (t : DominoTiling) (o : Orientation) (x : Point)
    (r : TilingRetainedWord t x i) (tail : BoundaryTail)
    (S : Finset Point)
    (hSrepresented : S ⊆ tilingExternalDominoBases t x r)
    (upper : TilingAwayDomino t x r
      (tilingExternalDominoBases t x r \ S) → ℕ)
    (q : TilingCappedCoordinates i cap) (ell : TruncatedTotals upper)
    (delta : ℕ)
    (hstart : trajectory
      (extendPrefix (directionVectorOfList initial.1)) initial.1.length = x)
    (hbase : ∀ b : TilingAwayDomino t x r
        (tilingExternalDominoBases t x r \ S),
      prefixedTilingFixedBoundaryLocalTime initial.1 x r
          (prefixedTilingInsertionTerminal initial t x r
            (fun j ↦ (q j : ℕ)) tail) b.1.1 =
        Fintype.card (TilingCoordinatesAt t x r b.1))
    (hdominance : ∀ b : TilingAwayDomino t x r
        (tilingExternalDominoBases t x r \ S),
      prefixedTilingFixedBoundaryLocalTime initial.1 x r
          (prefixedTilingInsertionTerminal initial t x r
            (fun j ↦ (q j : ℕ)) tail) (tilingPartner t b.1.1) ≤
        prefixedTilingFixedBoundaryLocalTime initial.1 x r
          (prefixedTilingInsertionTerminal initial t x r
            (fun j ↦ (q j : ℕ)) tail) b.1.1)
    (htranslate : ∀ b : TilingAwayDomino t x r
        (tilingExternalDominoBases t x r \ S),
      Fintype.card (TilingCoordinatesAt t x r b.1) ≤ m - w + 1)
    (htotal : ∀ b,
      tilingDominoTotal t x r (fun j ↦ (q j : ℕ)) b.1 = (ell b : ℕ))
    (hscreen : prefixedShellZeroReplacementScreenAtIncrement
      (cap := cap) (m := m) (w := w) initial.1 t x r
        (prefixedTilingInsertionTerminal initial t x r
          (fun j ↦ (q j : ℕ)) tail)
        (tilingExternalDominoBases t x r \ S) upper central delta ell)
    (hsupport :
      let v := prefixedTilingInsertionPrefixList initial.1 t x r
        (fun j ↦ (q j : ℕ)) tail.1
      let s := trajectory (extendPrefix (directionVectorOfList v))
      orientedTilingVTwoBases t o (shellZeroSourceTotalWindow m w) s v.length ∪
        orientedTilingVTwoBases t o
          (shellZeroReplacementTotalWindow m w) s v.length = S)
    (hcompat : ∀ b ∈ S, OrientationCompatible o b)
    (hcard : S.card = total) :
    let v := prefixedTilingInsertionPrefixList initial.1 t x r
      (fun j ↦ (q j : ℕ)) tail.1
    let s := trajectory (extendPrefix (directionVectorOfList v))
    (orientedTilingVTwoBases t o
        (shellZeroSourceTotalWindow m w) s v.length).card = central ∧
      (orientedTilingVTwoBases t o
        (shellZeroReplacementTotalWindow m w) s v.length).card =
          total - central := by
  classical
  let D := tilingExternalDominoBases t x r \ S
  let v := prefixedTilingInsertionPrefixList initial.1 t x r
    (fun j ↦ (q j : ℕ)) tail.1
  let s := trajectory (extendPrefix (directionVectorOfList v))
  let sourceSet := orientedTilingVTwoBases t o
    (shellZeroSourceTotalWindow m w) s v.length
  let replacementSet := orientedTilingVTwoBases t o
    (shellZeroReplacementTotalWindow m w) s v.length
  rcases hscreen.1 with ⟨A, hA, hclass⟩
  have hAcard : A.card = central := (Finset.mem_powersetCard.mp hA).2
  have hsourceSet : sourceSet = A.image (fun b ↦ b.1.1) := by
    ext b
    constructor
    · intro hb
      have hbS : b ∈ S := by
        have : b ∈ sourceSet ∪ replacementSet := Finset.mem_union_left _ hb
        exact hsupport ▸ this
      let c := supportAwayChosen t x r S hSrepresented b hbS
      refine Finset.mem_image.mpr ⟨c, ?_, rfl⟩
      by_contra hc
      have hrepCoord := (hclass c).2 hc
      have hrepV := tilingVTwoAt_replacement_of_prefixedReplacementCoordinate
        initial t x r tail D upper q ell hstart c
          (by simpa only [D] using hbase c)
          (by simpa only [D] using hdominance c) hrepCoord (htotal c)
      have hbRaw := (mem_orientedTilingVTwoBases_iff t o
        (shellZeroSourceTotalWindow m w) s v.length b).mp hb |>.1
      change b ∈ (visitedTilingBases t s v.length).filter
        (tilingVTwoAt t (shellZeroSourceTotalWindow m w) s v.length) at hbRaw
      have hsrcV := (Finset.mem_filter.mp hbRaw).2
      exact (Finset.disjoint_left.mp (shellZeroTotalWindows_disjoint m w)
        hsrcV.2 hrepV.2)
    · intro hb
      rcases Finset.mem_image.mp hb with ⟨c, hcA, rfl⟩
      have hcS : c.1.1 ∈ S := by
        exact (away_mem_support_iff t x r S c.1).1 c.2
      have hsrcV := tilingVTwoAt_source_of_prefixedSourceCoordinate
        initial t x r tail D upper q ell hstart c
          (by simpa only [D] using hbase c)
          (by simpa only [D] using hdominance c)
          (by simpa only [D] using htranslate c) ((hclass c).1 hcA) (htotal c)
      rw [mem_orientedTilingVTwoBases_iff]
      refine ⟨?_, hcompat c.1.1 hcS⟩
      change c.1.1 ∈ (visitedTilingBases t s v.length).filter
        (tilingVTwoAt t (shellZeroSourceTotalWindow m w) s v.length)
      refine Finset.mem_filter.mpr ⟨?_, hsrcV⟩
      rw [visitedTilingBases, Finset.mem_image]
      refine ⟨c.1.1, (mem_visitedSites_iff_localTime_pos s v.length c.1.1).2
        ?_, ?_⟩
      · have hlo := (mem_shellZeroSourceTotalWindow.mp hsrcV.2).1
        exact (Nat.zero_lt_succ (m - w)).trans_le hlo
      · exact tilingExternalDomino_isBase t x r c.1
  have himageCard : (A.image (fun b ↦ b.1.1)).card = A.card := by
    rw [Finset.card_image_iff]
    intro a _ b _ hab
    apply Subtype.ext
    apply Subtype.ext
    exact hab
  have hsourceCard : sourceSet.card = central := by
    rw [hsourceSet, himageCard, hAcard]
  have hdisjoint : Disjoint sourceSet replacementSet := by
    rw [Finset.disjoint_left]
    intro b hbSource hbReplacement
    have hsRaw := (mem_orientedTilingVTwoBases_iff t o
      (shellZeroSourceTotalWindow m w) s v.length b).mp hbSource |>.1
    have hrRaw := (mem_orientedTilingVTwoBases_iff t o
      (shellZeroReplacementTotalWindow m w) s v.length b).mp hbReplacement |>.1
    change b ∈ (visitedTilingBases t s v.length).filter
      (tilingVTwoAt t (shellZeroSourceTotalWindow m w) s v.length) at hsRaw
    change b ∈ (visitedTilingBases t s v.length).filter
      (tilingVTwoAt t (shellZeroReplacementTotalWindow m w) s v.length) at hrRaw
    exact Finset.disjoint_left.mp (shellZeroTotalWindows_disjoint m w)
      (Finset.mem_filter.mp hsRaw).2.2 (Finset.mem_filter.mp hrRaw).2.2
  refine ⟨hsourceCard, ?_⟩
  have hunionCard : sourceSet.card + replacementSet.card = total := by
    rw [← Finset.card_union_of_disjoint hdisjoint, hsupport, hcard]
  rw [hsourceCard] at hunionCard
  change replacementSet.card = total - central
  omega

end

end Erdos1165.TilingShellZeroStaticReplacementCardRecovery
