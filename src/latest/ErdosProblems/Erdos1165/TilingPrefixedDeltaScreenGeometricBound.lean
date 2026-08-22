/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.TilingPrefixedCrossClockSelectorComparison

/-!
# One-sided source and delta-indexed replacement product bound

For the shell-zero source, exact source membership only implies the pure
`I₁` screen; the converse need not hold.  At every fixed actual endpoint
increment, however, the replacement predicate has an exact factorization.
This module proves that this one-sided source implication is sufficient.
-/

open scoped BigOperators ENNReal

namespace Erdos1165.TilingPrefixedDeltaScreenGeometricBound

open FiniteDominoProductLaw
open SpatialInsertionFiber
open TilingCappedMarginalization TilingConditionalCappedMarginalization
open TilingPrefixedCrossClockSelectorComparison
open TilingPrefixedConditionalCappedMarginalization
open TilingPrefixedStoppedProductDisintegration
open TilingSpatialInsertionFiber

noncomputable section

abbrev DominoTiling := Tilings.Tiling

private theorem sourceMass_le_screenMass_mul_selector
    (sourceTau : StepPath → ℕ) (initial : List Direction) {i cap : ℕ}
    (t : DominoTiling) (x : Point) (r : TilingRetainedWord t x i)
    (tail : List Direction)
    (sourcePredicate : TilingCappedCoordinates i cap → Prop)
    (D : Finset Point)
    (selected : TilingDistinguishedCoordinates (cap := cap) t x r D → Prop)
    [DecidablePred selected]
    (upper : TilingAwayDomino t x r D → ℕ)
    (sourceScreen : TruncatedTotals upper → Prop)
    [DecidablePred sourceScreen]
    (hforward : ∀ q,
      sourcePredicate q ∧ PrefixedTilingStoppingAccepted sourceTau initial
          t x r (fun j ↦ (q j : ℕ)) tail →
        selected ((splitTilingCoordinatesEquiv t x r D q).1) ∧
          TilingAwayTotalsScreen t x r D upper sourceScreen
            ((splitTilingCoordinatesEquiv t x r D q).2))
    (htotal : (∑ ell : TruncatedTotals upper,
      jointMass (tilingAwayPointMass (cap := cap) t x r D) upper ell) ≠ 0) :
    prefixedTilingStoppedAcceptedGeometricMass sourceTau initial t x r cap tail
        sourcePredicate ≤
      screenMass (tilingAwayPointMass (cap := cap) t x r D) upper
          sourceScreen *
        prefixedTilingDistinguishedSelectorMass t x r D upper selected := by
  classical
  rw [prefixedTilingStoppedAcceptedGeometricMass_eq_indicatorSum]
  calc
    (∑ q : TilingCappedCoordinates i cap,
        if sourcePredicate q ∧
            PrefixedTilingStoppingAccepted sourceTau initial t x r
              (fun j ↦ (q j : ℕ)) tail then
          gapVectorMass (fun j ↦ (q j : ℕ)) else 0) ≤
        ∑ q : TilingCappedCoordinates i cap,
          if selected ((splitTilingCoordinatesEquiv t x r D q).1) ∧
              TilingAwayTotalsScreen t x r D upper sourceScreen
                ((splitTilingCoordinatesEquiv t x r D q).2) then
            gapVectorMass (fun j ↦ (q j : ℕ)) else 0 := by
      apply Finset.sum_le_sum
      intro q _
      by_cases hq : sourcePredicate q ∧
          PrefixedTilingStoppingAccepted sourceTau initial t x r
            (fun j ↦ (q j : ℕ)) tail
      · rw [if_pos hq, if_pos (hforward q hq)]
      · rw [if_neg hq]
        split_ifs
        · exact VariableStoppedProductDisintegration.gapVectorMass_nonneg _
        · exact le_rfl
    _ = ∑ ell : TruncatedTotals upper,
        if sourceScreen ell then
          distinguishedAwayMass
            (tilingAwayPointMass (cap := cap) t x r D) upper
            (fun d ↦ if selected d then
              tilingDistinguishedAssignmentMass t x r D d else 0) ell
        else 0 :=
      tilingCappedScreenedMass_factorization
        t x r D selected upper sourceScreen
    _ = screenMass (tilingAwayPointMass (cap := cap) t x r D) upper
          sourceScreen *
        prefixedTilingDistinguishedSelectorMass t x r D upper selected := by
      unfold prefixedTilingDistinguishedSelectorMass
      exact (screenMass_mul_distinguishedBase
        (tilingAwayPointMass (cap := cap) t x r D) upper sourceScreen
        (fun d ↦ if selected d then
          tilingDistinguishedAssignmentMass t x r D d else 0) htotal).symm

/-- A common distinguished selector, a one-sided source screen, and exact
factorizations of the fixed-increment replacement pieces give the desired
finite sum bound. -/
theorem prefixedTilingStoppedAcceptedGeometricMass_le_delta_sum
    {Delta : Type*} [Fintype Delta]
    (sourceTau : StepPath → ℕ) (replacementTau : Delta → StepPath → ℕ)
    (initial : List Direction) {i cap : ℕ}
    (t : DominoTiling) (x : Point) (r : TilingRetainedWord t x i)
    (tail : List Direction)
    (sourcePredicate : TilingCappedCoordinates i cap → Prop)
    (replacementPredicate : Delta → TilingCappedCoordinates i cap → Prop)
    (D : Finset Point)
    (selected : TilingDistinguishedCoordinates (cap := cap) t x r D → Prop)
    [DecidablePred selected]
    (upper : TilingAwayDomino t x r D → ℕ)
    (sourceScreen : TruncatedTotals upper → Prop)
    [DecidablePred sourceScreen]
    (replacementScreen : Delta → TruncatedTotals upper → Prop)
    [replacementScreenDec : ∀ delta, DecidablePred (replacementScreen delta)]
    (sourceForward : ∀ q,
      sourcePredicate q ∧ PrefixedTilingStoppingAccepted sourceTau initial
          t x r (fun j ↦ (q j : ℕ)) tail →
        selected ((splitTilingCoordinatesEquiv t x r D q).1) ∧
          TilingAwayTotalsScreen t x r D upper sourceScreen
            ((splitTilingCoordinatesEquiv t x r D q).2))
    (replacementFactorization : ∀ delta q,
      replacementPredicate delta q ∧
          PrefixedTilingStoppingAccepted (replacementTau delta) initial
            t x r (fun j ↦ (q j : ℕ)) tail ↔
        selected ((splitTilingCoordinatesEquiv t x r D q).1) ∧
          TilingAwayTotalsScreen t x r D upper (replacementScreen delta)
            ((splitTilingCoordinatesEquiv t x r D q).2))
    (htotal : (∑ ell : TruncatedTotals upper,
      jointMass (tilingAwayPointMass (cap := cap) t x r D) upper ell) ≠ 0)
    (ratio : ℝ)
    (hscreen : screenMass
        (tilingAwayPointMass (cap := cap) t x r D) upper sourceScreen ≤
      ratio * ∑ delta, screenMass
        (tilingAwayPointMass (cap := cap) t x r D) upper
          (replacementScreen delta)) :
    prefixedTilingStoppedAcceptedGeometricMass sourceTau initial t x r cap tail
        sourcePredicate ≤
      ratio * ∑ delta,
        prefixedTilingStoppedAcceptedGeometricMass (replacementTau delta)
          initial t x r cap tail (replacementPredicate delta) := by
  classical
  let common := prefixedTilingDistinguishedSelectorMass
    t x r D upper selected
  have hcommon : 0 ≤ common :=
    prefixedTilingDistinguishedSelectorMass_nonneg t x r D upper selected
  have hsource := sourceMass_le_screenMass_mul_selector sourceTau initial
    t x r tail sourcePredicate D selected upper sourceScreen sourceForward htotal
  have hreplacement : ∀ delta,
      prefixedTilingStoppedAcceptedGeometricMass (replacementTau delta)
          initial t x r cap tail (replacementPredicate delta) =
        screenMass (tilingAwayPointMass (cap := cap) t x r D) upper
            (replacementScreen delta) * common := by
    intro delta
    simpa only [common, prefixedTilingDistinguishedSelectorMass] using
      prefixedTilingStoppedAcceptedGeometricMass_eq_screenMass_mul_distinguishedBase
        (replacementTau delta) initial t x r tail
        (replacementPredicate delta) D selected upper
        (replacementScreen delta) (replacementFactorization delta) htotal
  calc
    _ ≤ screenMass (tilingAwayPointMass (cap := cap) t x r D) upper
          sourceScreen * common := hsource
    _ ≤ (ratio * ∑ delta, screenMass
          (tilingAwayPointMass (cap := cap) t x r D) upper
            (replacementScreen delta)) * common :=
      mul_le_mul_of_nonneg_right hscreen hcommon
    _ = ratio * ∑ delta,
        prefixedTilingStoppedAcceptedGeometricMass (replacementTau delta)
          initial t x r cap tail (replacementPredicate delta) := by
      simp_rw [hreplacement]
      rw [← Finset.sum_mul]
      ring

/-- `ENNReal` form used directly by the delta-indexed stopped-coordinate
specification. -/
theorem ofReal_prefixedTilingStoppedAcceptedGeometricMass_le_delta_tsum
    {Delta : Type*} [Fintype Delta]
    (sourceTau : StepPath → ℕ) (replacementTau : Delta → StepPath → ℕ)
    (initial : List Direction) {i cap : ℕ}
    (t : DominoTiling) (x : Point) (r : TilingRetainedWord t x i)
    (tail : List Direction)
    (sourcePredicate : TilingCappedCoordinates i cap → Prop)
    (replacementPredicate : Delta → TilingCappedCoordinates i cap → Prop)
    (D : Finset Point)
    (selected : TilingDistinguishedCoordinates (cap := cap) t x r D → Prop)
    [DecidablePred selected]
    (upper : TilingAwayDomino t x r D → ℕ)
    (sourceScreen : TruncatedTotals upper → Prop)
    [DecidablePred sourceScreen]
    (replacementScreen : Delta → TruncatedTotals upper → Prop)
    [replacementScreenDec : ∀ delta, DecidablePred (replacementScreen delta)]
    (sourceForward : ∀ q,
      sourcePredicate q ∧ PrefixedTilingStoppingAccepted sourceTau initial
          t x r (fun j ↦ (q j : ℕ)) tail →
        selected ((splitTilingCoordinatesEquiv t x r D q).1) ∧
          TilingAwayTotalsScreen t x r D upper sourceScreen
            ((splitTilingCoordinatesEquiv t x r D q).2))
    (replacementFactorization : ∀ delta q,
      replacementPredicate delta q ∧
          PrefixedTilingStoppingAccepted (replacementTau delta) initial
            t x r (fun j ↦ (q j : ℕ)) tail ↔
        selected ((splitTilingCoordinatesEquiv t x r D q).1) ∧
          TilingAwayTotalsScreen t x r D upper (replacementScreen delta)
            ((splitTilingCoordinatesEquiv t x r D q).2))
    (htotal : (∑ ell : TruncatedTotals upper,
      jointMass (tilingAwayPointMass (cap := cap) t x r D) upper ell) ≠ 0)
    (ratio : ℝ) (hratio : 0 ≤ ratio)
    (hscreen : screenMass
        (tilingAwayPointMass (cap := cap) t x r D) upper sourceScreen ≤
      ratio * ∑ delta, screenMass
        (tilingAwayPointMass (cap := cap) t x r D) upper
          (replacementScreen delta)) :
    ENNReal.ofReal (prefixedTilingStoppedAcceptedGeometricMass sourceTau
        initial t x r cap tail sourcePredicate) ≤
      ENNReal.ofReal ratio * ∑' delta,
        ENNReal.ofReal (prefixedTilingStoppedAcceptedGeometricMass
          (replacementTau delta) initial t x r cap tail
            (replacementPredicate delta)) := by
  have hreal := prefixedTilingStoppedAcceptedGeometricMass_le_delta_sum
    sourceTau replacementTau initial t x r tail sourcePredicate
      replacementPredicate D selected upper sourceScreen replacementScreen
      sourceForward replacementFactorization htotal ratio hscreen
  calc
    _ ≤ ENNReal.ofReal (ratio * ∑ delta,
        prefixedTilingStoppedAcceptedGeometricMass (replacementTau delta)
          initial t x r cap tail (replacementPredicate delta)) :=
      ENNReal.ofReal_le_ofReal hreal
    _ = _ := by
      rw [ENNReal.ofReal_mul hratio, tsum_fintype,
        ← ENNReal.ofReal_sum_of_nonneg]
      intro delta _
      exact prefixedTilingStoppedAcceptedGeometricMass_nonneg
        (replacementTau delta) initial t x r cap tail
          (replacementPredicate delta)

end

end Erdos1165.TilingPrefixedDeltaScreenGeometricBound
