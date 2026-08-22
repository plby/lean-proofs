/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.TilingCappedMarginalization
import ErdosProblems.Erdos1165.TilingTraceDataFixing

/-!
# Distinguished-coordinate factorization for all-six tiling fibres

The finite endpoint conditions on distinguished favorite dominoes depend
only on the distinguished projection of the capped insertion vector.  This
module states that dependence as an exact equivalence in the coordinate
language consumed by `TilingFactoredStoppedCoordinateData`.
-/

namespace Erdos1165.TilingDistinguishedProjectionFactorization

open TilingLazyDecomposition TilingSpatialInsertionFiber
open TilingInsertedLocalTime TilingStoppedAcceptanceFactorization
open TilingCappedMarginalization

noncomputable section

abbrev DominoTiling := Tilings.Tiling

/-- The finite terminal endpoint predicate expressed solely in the
distinguished grouped coordinates. -/
def TilingDistinguishedEndpointSelection {i cap : ℕ}
    (t : DominoTiling) (x : Point) (r : TilingRetainedWord t x i)
    (terminal : Option Point) (level : ℕ) (D : Finset Point)
    (d : TilingDistinguishedCoordinates (cap := cap) t x r D) : Prop :=
  ∀ b : TilingDistinguishedDomino t x r D,
    tilingFixedBoundaryLocalTime x r terminal b.1.1 +
        ∑ k, (d b k : ℕ) < level ∧
      tilingFixedBoundaryLocalTime x r terminal
          (tilingPartner t b.1.1) +
        ∑ k, (d b k : ℕ) < level

/-- The distinguished projection evaluates to the original insertion
coordinate at every coordinate belonging to a distinguished domino. -/
theorem splitTilingCoordinatesEquiv_distinguished_apply
    {i cap : ℕ} (t : DominoTiling) (x : Point)
    (r : TilingRetainedWord t x i) (D : Finset Point)
    (q : TilingCappedCoordinates i cap)
    (b : TilingDistinguishedDomino t x r D)
    (k : TilingCoordinatesAt t x r b.1) :
    (splitTilingCoordinatesEquiv t x r D q).1 b k = q k.1 :=
  TilingCappedMarginalization.splitTilingCoordinatesEquiv_distinguished_apply
    t x r D q b k

/-- Exact identification of literal distinguished endpoint inequalities with
a predicate on the distinguished coordinate projection alone. -/
theorem tilingPrefixDistinguishedEndpointsBelowLevel_iff_selection
    {i cap : ℕ} (t : DominoTiling) (x : Point)
    (r : TilingRetainedWord t x i) (terminal : Option Point)
    (level : ℕ) (D : Finset Point) (q : TilingCappedCoordinates i cap) :
    TilingPrefixDistinguishedEndpointsBelowLevel t x r terminal level D
        (fun k ↦ (q k : ℕ)) ↔
      TilingDistinguishedEndpointSelection t x r terminal level D
        (splitTilingCoordinatesEquiv t x r D q).1 := by
  constructor
  · intro h b
    have hend := h b.1 b.2
    rw [tilingInsertedPrefix_localTime_at_dominoPoint t x r
        (fun k ↦ (q k : ℕ)) terminal b.1 b.1.1
        (tilingExternalDomino_isBase t x r b.1),
      tilingInsertedPrefix_localTime_at_dominoPoint t x r
        (fun k ↦ (q k : ℕ)) terminal b.1
        (tilingPartner t b.1.1)
        ((tilingBase_partner t b.1.1).trans
          (tilingExternalDomino_isBase t x r b.1))] at hend
    simpa only [tilingDominoTotal,
      splitTilingCoordinatesEquiv_distinguished_apply] using hend
  · intro h b hb
    have hend := h ⟨b, hb⟩
    rw [tilingInsertedPrefix_localTime_at_dominoPoint t x r
        (fun k ↦ (q k : ℕ)) terminal b b.1
        (tilingExternalDomino_isBase t x r b),
      tilingInsertedPrefix_localTime_at_dominoPoint t x r
        (fun k ↦ (q k : ℕ)) terminal b (tilingPartner t b.1)
        ((tilingBase_partner t b.1).trans
          (tilingExternalDomino_isBase t x r b))]
    simpa only [tilingDominoTotal,
      splitTilingCoordinatesEquiv_distinguished_apply] using hend

/-- Consequently, two capped vectors with the same distinguished projection
satisfy exactly the same distinguished endpoint condition. -/
theorem tilingPrefixDistinguishedEndpointsBelowLevel_congr
    {i cap : ℕ} (t : DominoTiling) (x : Point)
    (r : TilingRetainedWord t x i) (terminal : Option Point)
    (level : ℕ) (D : Finset Point) (q q' : TilingCappedCoordinates i cap)
    (hprojection :
      (splitTilingCoordinatesEquiv t x r D q).1 =
        (splitTilingCoordinatesEquiv t x r D q').1) :
    TilingPrefixDistinguishedEndpointsBelowLevel t x r terminal level D
        (fun k ↦ (q k : ℕ)) ↔
      TilingPrefixDistinguishedEndpointsBelowLevel t x r terminal level D
        (fun k ↦ (q' k : ℕ)) := by
  rw [tilingPrefixDistinguishedEndpointsBelowLevel_iff_selection,
    tilingPrefixDistinguishedEndpointsBelowLevel_iff_selection,
    hprojection]

end

end Erdos1165.TilingDistinguishedProjectionFactorization
