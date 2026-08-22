/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.TilingPrefixedConditionalCappedMarginalization

/-!
# Cross-clock comparison with different distinguished selectors

Two stopped clocks on the same retained carrier need not use definitionally
equal distinguished-coordinate selectors.  The finite-product comparison
only needs the replacement distinguished contribution to be at most the
source contribution.  This file isolates that weakest deterministic seam.

A pointwise inclusion of replacement selectors into source selectors implies
the required mass inequality.  Thus a later trace-invariance theorem may prove
an inclusion (or equality), without changing the frozen stopped-fibre APIs.
-/

open Set

namespace Erdos1165.TilingPrefixedCrossClockSelectorComparison

open FiniteDominoProductLaw PathInsertion
open TilingCappedMarginalization
open TilingPrefixedConditionalCappedMarginalization
open TilingPrefixedStoppedProductDisintegration
open TilingSpatialInsertionFiber

noncomputable section

abbrev DominoTiling := Tilings.Tiling

/-- The distinguished-coordinate contribution belonging to one selector on
a fixed retained carrier.  It is independent of the stopped clock and of the
away-coordinate screen. -/
noncomputable def prefixedTilingDistinguishedSelectorMass
    {i cap : ℕ} (t : DominoTiling) (x : Point)
    (r : TilingRetainedWord t x i) (D : Finset Point)
    (upper : TilingAwayDomino t x r D → ℕ)
    (selected : TilingDistinguishedCoordinates (cap := cap) t x r D → Prop)
    [DecidablePred selected] :
    ℝ := by
  classical
  exact ∑ ell : TruncatedTotals upper,
    distinguishedAwayMass
      (tilingAwayPointMass (cap := cap) t x r D) upper
      (fun d ↦ if selected d then
        tilingDistinguishedAssignmentMass t x r D d else 0) ell

theorem prefixedTilingDistinguishedSelectorMass_nonneg
    {i cap : ℕ} (t : DominoTiling) (x : Point)
    (r : TilingRetainedWord t x i) (D : Finset Point)
    (upper : TilingAwayDomino t x r D → ℕ)
    (selected : TilingDistinguishedCoordinates (cap := cap) t x r D → Prop)
    [DecidablePred selected] :
    0 ≤ prefixedTilingDistinguishedSelectorMass t x r D upper selected := by
  classical
  unfold prefixedTilingDistinguishedSelectorMass distinguishedAwayMass
  apply Finset.sum_nonneg
  intro ell _
  apply Finset.sum_nonneg
  intro d _
  apply mul_nonneg
  · unfold jointMass tilingAwayPointMass
    exact Finset.prod_nonneg fun b _ ↦
      tilingAwayExactTotalMass_nonneg t x r D b (ell b)
  ·
    by_cases hd : selected d
    · simp only [hd, if_true]
      unfold tilingDistinguishedAssignmentMass
      exact Finset.prod_nonneg fun b _ ↦
        Finset.prod_nonneg fun j _ ↦ geometricGapMass_nonneg (d b j : ℕ)
    · simp [hd]

/-- Pointwise inclusion of distinguished selectors gives the exact common
mass comparison required by a cross-clock product estimate. -/
theorem prefixedTilingDistinguishedSelectorMass_mono
    {i cap : ℕ} (t : DominoTiling) (x : Point)
    (r : TilingRetainedWord t x i) (D : Finset Point)
    (upper : TilingAwayDomino t x r D → ℕ)
    (sourceSelected replacementSelected :
      TilingDistinguishedCoordinates (cap := cap) t x r D → Prop)
    [DecidablePred sourceSelected] [DecidablePred replacementSelected]
    (hselected : ∀ d, replacementSelected d → sourceSelected d) :
    prefixedTilingDistinguishedSelectorMass t x r D upper replacementSelected ≤
      prefixedTilingDistinguishedSelectorMass t x r D upper sourceSelected := by
  classical
  unfold prefixedTilingDistinguishedSelectorMass distinguishedAwayMass
  apply Finset.sum_le_sum
  intro ell _
  apply Finset.sum_le_sum
  intro d _
  apply mul_le_mul_of_nonneg_left
  ·
    by_cases hr : replacementSelected d
    · have hs : sourceSelected d := hselected d hr
      simp only [hr, hs, if_true]
      exact le_rfl
    · simp only [hr, if_false]
      by_cases hs : sourceSelected d
      · simp only [hs, if_true]
        unfold tilingDistinguishedAssignmentMass
        exact Finset.prod_nonneg fun b _ ↦
          Finset.prod_nonneg fun j _ ↦ geometricGapMass_nonneg (d b j : ℕ)
      · simp [hs]
  · unfold jointMass tilingAwayPointMass
    exact Finset.prod_nonneg fun b _ ↦
      tilingAwayExactTotalMass_nonneg t x r D b (ell b)

/-- Cross-clock comparison after separate literal factorizations.  Equality
of the two selectors is stronger than necessary: an inequality between their
distinguished masses suffices. -/
theorem prefixedTilingStoppedAcceptedGeometricMass_le_of_crossClock
    (sourceTau replacementTau : StepPath → ℕ)
    (initial : List Direction) {i cap : ℕ}
    (t : DominoTiling) (x : Point) (r : TilingRetainedWord t x i)
    (tail : List Direction)
    (sourcePredicate replacementPredicate :
      TilingCappedCoordinates i cap → Prop)
    [DecidablePred sourcePredicate] [DecidablePred replacementPredicate]
    (D : Finset Point)
    (sourceSelected replacementSelected :
      TilingDistinguishedCoordinates (cap := cap) t x r D → Prop)
    [DecidablePred sourceSelected] [DecidablePred replacementSelected]
    (upper : TilingAwayDomino t x r D → ℕ)
    (sourceScreen replacementScreen : TruncatedTotals upper → Prop)
    [DecidablePred sourceScreen] [DecidablePred replacementScreen]
    (sourceFactorization : ∀ q,
      sourcePredicate q ∧ PrefixedTilingStoppingAccepted sourceTau initial
          t x r (fun j ↦ (q j : ℕ)) tail ↔
        sourceSelected ((splitTilingCoordinatesEquiv t x r D q).1) ∧
          TilingAwayTotalsScreen t x r D upper sourceScreen
            ((splitTilingCoordinatesEquiv t x r D q).2))
    (replacementFactorization : ∀ q,
      replacementPredicate q ∧
          PrefixedTilingStoppingAccepted replacementTau initial t x r
            (fun j ↦ (q j : ℕ)) tail ↔
        replacementSelected ((splitTilingCoordinatesEquiv t x r D q).1) ∧
          TilingAwayTotalsScreen t x r D upper replacementScreen
            ((splitTilingCoordinatesEquiv t x r D q).2))
    (htotal : (∑ ell : TruncatedTotals upper,
      jointMass (tilingAwayPointMass (cap := cap) t x r D) upper ell) ≠ 0)
    (ratio : ℝ) (hratio : 0 ≤ ratio)
    (hscreen : screenMass (tilingAwayPointMass (cap := cap) t x r D) upper
        replacementScreen ≤
      ratio * screenMass (tilingAwayPointMass (cap := cap) t x r D) upper
        sourceScreen)
    (hselector :
      prefixedTilingDistinguishedSelectorMass t x r D upper
          replacementSelected ≤
        prefixedTilingDistinguishedSelectorMass t x r D upper
          sourceSelected) :
    prefixedTilingStoppedAcceptedGeometricMass replacementTau initial t x r
        cap tail replacementPredicate ≤
      ratio * prefixedTilingStoppedAcceptedGeometricMass sourceTau initial t x r
        cap tail sourcePredicate := by
  classical
  rw [prefixedTilingStoppedAcceptedGeometricMass_eq_screenMass_mul_distinguishedBase
      replacementTau initial t x r tail replacementPredicate D
      replacementSelected upper replacementScreen replacementFactorization
      htotal,
    prefixedTilingStoppedAcceptedGeometricMass_eq_screenMass_mul_distinguishedBase
      sourceTau initial t x r tail sourcePredicate D sourceSelected upper
      sourceScreen sourceFactorization htotal]
  unfold prefixedTilingDistinguishedSelectorMass at hselector
  set replacementCommon : ℝ := ∑ ell : TruncatedTotals upper,
    distinguishedAwayMass
      (tilingAwayPointMass (cap := cap) t x r D) upper
      (fun d ↦ if replacementSelected d then
        tilingDistinguishedAssignmentMass t x r D d else 0) ell with
      hreplacementCommonDef
  set sourceCommon : ℝ := ∑ ell : TruncatedTotals upper,
    distinguishedAwayMass
      (tilingAwayPointMass (cap := cap) t x r D) upper
      (fun d ↦ if sourceSelected d then
        tilingDistinguishedAssignmentMass t x r D d else 0) ell with
      hsourceCommonDef
  have hreplacementCommon : 0 ≤ replacementCommon := by
    have h := prefixedTilingDistinguishedSelectorMass_nonneg
      t x r D upper replacementSelected
    unfold prefixedTilingDistinguishedSelectorMass at h
    simpa only [← hreplacementCommonDef] using h
  have hsourceScreen : 0 ≤ screenMass
      (tilingAwayPointMass (cap := cap) t x r D) upper sourceScreen := by
    unfold screenMass
    apply Finset.sum_nonneg
    intro ell _
    by_cases hell : sourceScreen ell
    · simp only [hell, if_true]
      unfold normalizedJointMass
      apply div_nonneg
      · unfold jointMass tilingAwayPointMass
        exact Finset.prod_nonneg fun b _ ↦
          tilingAwayExactTotalMass_nonneg t x r D b (ell b)
      · apply Finset.sum_nonneg
        intro z _
        unfold jointMass tilingAwayPointMass
        exact Finset.prod_nonneg fun b _ ↦
          tilingAwayExactTotalMass_nonneg t x r D b (z b)
    · simp [hell]
  change screenMass (tilingAwayPointMass (cap := cap) t x r D) upper
        replacementScreen * replacementCommon ≤
    ratio * (screenMass (tilingAwayPointMass (cap := cap) t x r D) upper
        sourceScreen * sourceCommon)
  calc
    _ ≤ (ratio * screenMass (tilingAwayPointMass (cap := cap) t x r D)
          upper sourceScreen) * replacementCommon :=
      mul_le_mul_of_nonneg_right hscreen hreplacementCommon
    _ ≤ (ratio * screenMass (tilingAwayPointMass (cap := cap) t x r D)
          upper sourceScreen) * sourceCommon := by
      apply mul_le_mul_of_nonneg_left hselector
      exact mul_nonneg hratio hsourceScreen
    _ = _ := by ring

end

end Erdos1165.TilingPrefixedCrossClockSelectorComparison
