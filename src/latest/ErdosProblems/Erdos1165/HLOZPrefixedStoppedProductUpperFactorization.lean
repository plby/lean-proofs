/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.TilingPrefixedStoppedProductDisintegration

/-!
# One-sided stopped-product factorization

For upper bounds, a stopped predicate only needs to imply a distinguished /
away factorization.  The reverse implication used by the exact product
identity is unnecessary and can fail after the away coordinates are
enlarged.  This lemma records the corresponding one-sided mass estimate.
-/

open scoped BigOperators

namespace Erdos1165.HLOZPrefixedStoppedProductUpperFactorization

open FiniteDominoProductLaw
open LazyDecomposition PreStoppingFiber SpatialInsertionFiber StoppedInsertion
open TilingCappedMarginalization
open TilingPrefixedStoppedProductDisintegration
open TilingSpatialInsertionFiber
open VariableStoppedProductDisintegration

noncomputable section

abbrev DominoTiling := Tilings.Tiling

theorem prefixedTilingStoppedAcceptedGeometricMass_le_screenMass_mul_distinguishedBase
    {τ : StepPath → ℕ} {initial : List Direction} {i cap : ℕ}
    {t : DominoTiling} {x : Point} {r : TilingRetainedWord t x i}
    {tail : List Direction}
    (screened : TilingCappedCoordinates i cap → Prop)
    [DecidablePred screened]
    (D : Finset Point)
    (selected : TilingDistinguishedCoordinates (cap := cap) t x r D → Prop)
    [DecidablePred selected]
    (upper : TilingAwayDomino t x r D → ℕ)
    (screen : TruncatedTotals upper → Prop)
    [DecidablePred screen]
    (hforward : ∀ q,
      screened q ∧ PrefixedTilingStoppingAccepted τ initial t x r
          (fun k ↦ (q k : ℕ)) tail →
        selected ((splitTilingCoordinatesEquiv t x r D q).1) ∧
          TilingAwayTotalsScreen t x r D upper screen
            (splitTilingCoordinatesEquiv t x r D q).2)
    (htotal : (∑ ell : TruncatedTotals upper,
      jointMass (tilingAwayPointMass (cap := cap) t x r D) upper ell) ≠ 0) :
    prefixedTilingStoppedAcceptedGeometricMass
        τ initial t x r cap tail screened ≤
      screenMass (tilingAwayPointMass (cap := cap) t x r D) upper screen *
        ∑ ell : TruncatedTotals upper,
          distinguishedAwayMass
            (tilingAwayPointMass (cap := cap) t x r D) upper
            (fun d ↦ if selected d then
              tilingDistinguishedAssignmentMass t x r D d else 0) ell := by
  classical
  rw [prefixedTilingStoppedAcceptedGeometricMass_eq_indicatorSum]
  calc
    (∑ q : TilingCappedCoordinates i cap,
        if screened q ∧ PrefixedTilingStoppingAccepted τ initial t x r
            (fun k ↦ (q k : ℕ)) tail then
          gapVectorMass (fun k ↦ (q k : ℕ)) else 0) ≤
      ∑ q : TilingCappedCoordinates i cap,
        if selected ((splitTilingCoordinatesEquiv t x r D q).1) ∧
            TilingAwayTotalsScreen t x r D upper screen
              (splitTilingCoordinatesEquiv t x r D q).2 then
          gapVectorMass (fun k ↦ (q k : ℕ)) else 0 := by
      apply Finset.sum_le_sum
      intro q _hq
      by_cases hs : screened q ∧
          PrefixedTilingStoppingAccepted τ initial t x r
            (fun k ↦ (q k : ℕ)) tail
      · rw [if_pos hs, if_pos (hforward q hs)]
      · rw [if_neg hs]
        split
        · exact gapVectorMass_nonneg _
        · exact le_rfl
    _ = ∑ ell : TruncatedTotals upper,
        if screen ell then
          distinguishedAwayMass
            (tilingAwayPointMass (cap := cap) t x r D) upper
            (fun d ↦ if selected d then
              tilingDistinguishedAssignmentMass t x r D d else 0) ell
        else 0 :=
      tilingCappedScreenedMass_factorization t x r D selected upper screen
    _ = screenMass (tilingAwayPointMass (cap := cap) t x r D) upper screen *
        ∑ ell : TruncatedTotals upper,
          distinguishedAwayMass
            (tilingAwayPointMass (cap := cap) t x r D) upper
            (fun d ↦ if selected d then
              tilingDistinguishedAssignmentMass t x r D d else 0) ell :=
      (screenMass_mul_distinguishedBase
        (tilingAwayPointMass (cap := cap) t x r D) upper screen
        (fun d ↦ if selected d then
          tilingDistinguishedAssignmentMass t x r D d else 0) htotal).symm

end

end Erdos1165.HLOZPrefixedStoppedProductUpperFactorization
