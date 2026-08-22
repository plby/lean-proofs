/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.TilingShellZeroExternalStoppedCoordinateSpec

/-!
# Swapped cross-clock shell-zero comparison

The generic cross-clock theorem is phrased as
`formalReplacementMass ≤ ratio * formalSourceMass`.  HLOZ needs
`actualSourceMass ≤ ratio * actualReplacementMass`, so this adapter invokes
it with the formal roles swapped.  This makes the direction of the static
selector injection explicit and auditable.
-/

open Set
open scoped BigOperators

namespace Erdos1165.TilingShellZeroExternalCrossClockBound

open FiniteDominoProductLaw HeterogeneousProductTail
open HLOZProposition48Candidates
open HLOZShellZeroCentralCount HLOZShellZeroCentralTail
open HLOZShellZeroExternalWindow HLOZShellZeroReplacementWindows
open TilingCappedMarginalization
open TilingPrefixedCrossClockSelectorComparison
open TilingShellZeroExternalStoppedCoordinateSpec
open TilingShellZeroFactoredCapScreen
open TilingShellZeroSourcePartition
open TilingSpatialInsertionFiber
open TilingPrefixedStoppedProductDisintegration

noncomputable section

abbrev DominoTiling := Tilings.Tiling

private theorem exactSourceSubsetVector_fintype_iff
    {Coordinate : Type*} (I J : Fintype Coordinate)
    [DecidableEq Coordinate] {State : Coordinate → Type*}
    (source replacement : ∀ c, State c → Prop) (central : ℕ)
    (ell : ∀ c, State c) :
    @exactSourceSubsetVector Coordinate I inferInstance State
        source replacement central ell ↔
      @exactSourceSubsetVector Coordinate J inferInstance State
        source replacement central ell := by
  unfold exactSourceSubsetVector
  have huniv : @Finset.univ Coordinate I = @Finset.univ Coordinate J := by
    ext c
    simp
  rw [huniv]

private theorem sourceScreenMass_eq
    {t : DominoTiling} {o : LazyDecomposition.Orientation}
    {m k low externalLow externalHigh total : ℕ}
    {z : TilingOrientedShellZeroSourcePartition.OrientedTilingTypedExternalWordCode t}
    (data : LiteralShellZeroExternalStoppedCoordinateSpec t o m k low
      externalLow externalHigh total z) (cap : ℕ) :
    @screenMass
        (TilingAwayDomino t z.start z.retained data.distinguished)
        (instFintypeTilingAwayDomino t z.start z.retained data.distinguished)
        (fun a b ↦ Subtype.instDecidableEq a b)
        (tilingAwayPointMass (cap := data.coordinateCap cap) t z.start
          z.retained data.distinguished)
        (data.upper cap)
        (allSourceVector fun b v ↦ tilingShellZeroSourceCoordinate
          (cap := data.coordinateCap cap) (m := m) (w := shellWidth48 m)
          t z.start z.retained data.distinguished (data.upper cap) b v)
        (instDecidablePredAllSourceVector _) =
      tilingShellZeroAllSourceProductMass
        (cap := data.coordinateCap cap) (m := m) t z.start z.retained
          data.distinguished (data.upper cap) := by
  classical
  let source := fun b v ↦ tilingShellZeroSourceCoordinate
    (cap := data.coordinateCap cap) (m := m) (w := shellWidth48 m)
    t z.start z.retained data.distinguished (data.upper cap) b v
  rw [@screenMass_eq_product
    (TilingAwayDomino t z.start z.retained data.distinguished)
    (instFintypeTilingAwayDomino t z.start z.retained data.distinguished)
    (fun a b ↦ Subtype.instDecidableEq a b)
    (tilingAwayPointMass (cap := data.coordinateCap cap) t z.start
      z.retained data.distinguished) (data.upper cap) (allSourceVector source)
    (instDecidablePredAllSourceVector source)]
  let weight := fun b (v : Fin (data.upper cap b)) ↦
    coordinateMass
      (tilingAwayPointMass (cap := data.coordinateCap cap) t z.start
      z.retained data.distinguished)
      (data.upper cap) b (v : ℕ)
  have hsum := @sum_allSourceVector_eq_product
    (TilingAwayDomino t z.start z.retained data.distinguished)
    (instFintypeTilingAwayDomino t z.start z.retained data.distinguished)
    (fun a b ↦ Subtype.instDecidableEq a b)
    (fun b ↦ Fin (data.upper cap b)) (fun b ↦ Fin.fintype (data.upper cap b))
    weight source (fun _ ↦ Classical.decPred _)
  unfold productPointMass at hsum
  refine hsum.trans ?_
  unfold tilingShellZeroAllSourceProductMass
  congr 1
  funext b
  unfold tilingShellZeroSourceCoordinateMass
  apply Finset.sum_congr rfl
  intro v _
  by_cases hv : (v : ℕ) ∈ shellZeroSourceFailureWindow m (shellWidth48 m)
      (Fintype.card (TilingCoordinatesAt t z.start z.retained b.1))
  · have hs : source b v := by
      simpa only [source, tilingShellZeroSourceCoordinate] using hv
    rw [if_pos hs]
    rw [if_pos hv]
    rfl
  · have hs : ¬ source b v := by
      simpa only [source, tilingShellZeroSourceCoordinate] using hv
    rw [if_neg hs]
    rw [if_neg hv]

private theorem replacementScreenMass_eq
    {t : DominoTiling} {o : LazyDecomposition.Orientation}
    {m k low externalLow externalHigh total : ℕ}
    {z : TilingOrientedShellZeroSourcePartition.OrientedTilingTypedExternalWordCode t}
    (data : LiteralShellZeroExternalStoppedCoordinateSpec t o m k low
      externalLow externalHigh total z)
    (hexternal : ShellZeroExternalWindowArithmeticAt m externalLow externalHigh)
    (cap : ℕ) :
    @screenMass
        (TilingAwayDomino t z.start z.retained data.distinguished)
        (instFintypeTilingAwayDomino t z.start z.retained data.distinguished)
        (fun a b ↦ Subtype.instDecidableEq a b)
        (tilingAwayPointMass (cap := data.coordinateCap cap) t z.start
          z.retained data.distinguished)
        (data.upper cap)
        (exactSourceSubsetVector
          (fun b v ↦ tilingShellZeroSourceCoordinate
            (cap := data.coordinateCap cap) (m := m) (w := shellWidth48 m)
            t z.start z.retained data.distinguished (data.upper cap) b v)
          (fun b v ↦ tilingShellZeroReplacementCoordinate
            (cap := data.coordinateCap cap) (m := m) (w := shellWidth48 m)
            t z.start z.retained data.distinguished (data.upper cap) b v)
          (centralReplacementUpperCount shellZeroLocalRatioConstant total))
        (instDecidablePredExactSourceSubsetVector _ _ _) =
      tilingShellZeroCentralReplacementProductMass
        (cap := data.coordinateCap cap) (m := m) t z.start z.retained
          data.distinguished (data.upper cap)
            (centralReplacementUpperCount shellZeroLocalRatioConstant total) := by
  classical
  let source := fun b v ↦ tilingShellZeroSourceCoordinate
    (cap := data.coordinateCap cap) (m := m) (w := shellWidth48 m)
    t z.start z.retained data.distinguished (data.upper cap) b v
  let replacement := fun b v ↦ tilingShellZeroReplacementCoordinate
    (cap := data.coordinateCap cap) (m := m) (w := shellWidth48 m)
    t z.start z.retained data.distinguished (data.upper cap) b v
  let replacementScreen := exactSourceSubsetVector source replacement
    (centralReplacementUpperCount shellZeroLocalRatioConstant total)
  let namedReplacementScreen := @exactSourceSubsetVector
    (TilingAwayDomino t z.start z.retained data.distinguished)
    (instFintypeTilingAwayDomino t z.start z.retained data.distinguished)
    (fun a b ↦ Subtype.instDecidableEq a b)
    (fun b ↦ Fin (data.upper cap b)) source replacement
    (centralReplacementUpperCount shellZeroLocalRatioConstant total)
  have hscreenProduct := @screenMass_eq_product
    (TilingAwayDomino t z.start z.retained data.distinguished)
    (instFintypeTilingAwayDomino t z.start z.retained data.distinguished)
    (fun a b ↦ Subtype.instDecidableEq a b)
    (tilingAwayPointMass (cap := data.coordinateCap cap) t z.start
      z.retained data.distinguished) (data.upper cap)
    replacementScreen (Classical.decPred replacementScreen)
  let weight := fun b (v : Fin (data.upper cap b)) ↦
    coordinateMass
      (tilingAwayPointMass (cap := data.coordinateCap cap) t z.start
      z.retained data.distinguished)
      (data.upper cap) b (v : ℕ)
  have hscreens : replacementScreen = namedReplacementScreen := by
    funext ell
    apply propext
    exact exactSourceSubsetVector_fintype_iff
      (Subtype.fintype fun b : TilingExternalDomino t z.start z.retained ↦
        b.1 ∉ data.distinguished)
      (instFintypeTilingAwayDomino t z.start z.retained data.distinguished)
      source replacement
      (centralReplacementUpperCount shellZeroLocalRatioConstant total) ell
  have hsum := @sum_exactSourceSubsetVector_eq_exactUpperCountProductMass
    (TilingAwayDomino t z.start z.retained data.distinguished)
    (instFintypeTilingAwayDomino t z.start z.retained data.distinguished)
    (fun a b ↦ Subtype.instDecidableEq a b)
    (fun b ↦ Fin (data.upper cap b)) (fun b ↦ Fin.fintype (data.upper cap b))
    weight source replacement (fun _ ↦ Classical.decPred _)
    (fun _ ↦ Classical.decPred _)
    (tilingShellZeroCoordinate_disjoint t z.start z.retained
      data.distinguished (data.upper cap)
        ((data.coordinateSupport cap).toWindowData hexternal).translate)
    (centralReplacementUpperCount shellZeroLocalRatioConstant total)
  unfold productPointMass at hsum
  have hproduct : _ = tilingShellZeroCentralReplacementProductMass
      (cap := data.coordinateCap cap) (m := m) t z.start z.retained
        data.distinguished (data.upper cap)
          (centralReplacementUpperCount shellZeroLocalRatioConstant total) :=
    hsum.trans (by
      unfold tilingShellZeroCentralReplacementProductMass
      congr 1
      · funext b
        unfold tilingShellZeroSourceCoordinateMass
        apply Finset.sum_congr rfl
        intro v _
        by_cases hv : (v : ℕ) ∈ shellZeroSourceFailureWindow m
            (shellWidth48 m)
            (Fintype.card (TilingCoordinatesAt t z.start z.retained b.1))
        · have hs : source b v := by
            simpa only [source, tilingShellZeroSourceCoordinate] using hv
          rw [if_pos hs]
          rw [if_pos hv]
          rfl
        · have hs : ¬ source b v := by
            simpa only [source, tilingShellZeroSourceCoordinate] using hv
          rw [if_neg hs]
          rw [if_neg hv]
      · funext b
        unfold tilingShellZeroReplacementCoordinateMass
        apply Finset.sum_congr rfl
        intro v _
        by_cases hv : (v : ℕ) ∈ shellZeroReplacementFailureWindow m
            (shellWidth48 m)
            (Fintype.card (TilingCoordinatesAt t z.start z.retained b.1))
        · have hr : replacement b v := by
            simpa only [replacement, tilingShellZeroReplacementCoordinate]
              using hv
          rw [if_pos hr]
          rw [if_pos hv]
          rfl
        · have hr : ¬ replacement b v := by
            simpa only [replacement, tilingShellZeroReplacementCoordinate]
              using hv
          rw [if_neg hr]
          rw [if_neg hv])
  rw [hscreens] at hscreenProduct
  have hlocal : @screenMass
      (TilingAwayDomino t z.start z.retained data.distinguished)
      (instFintypeTilingAwayDomino t z.start z.retained data.distinguished)
      (fun a b ↦ Subtype.instDecidableEq a b)
      (tilingAwayPointMass (cap := data.coordinateCap cap) t z.start
        z.retained data.distinguished) (data.upper cap) replacementScreen
      (Classical.decPred replacementScreen) =
        tilingShellZeroCentralReplacementProductMass
          (cap := data.coordinateCap cap) (m := m) t z.start z.retained
            data.distinguished (data.upper cap)
              (centralReplacementUpperCount shellZeroLocalRatioConstant total) := by
    rw [hscreens]
    exact hscreenProduct.trans hproduct
  simpa only [replacementScreen, source, replacement] using hlocal

/-- Actual source stopped mass is bounded by the central ratio times actual
replacement stopped mass.  The generic theorem is deliberately called with
the semantic roles swapped. -/
theorem LiteralShellZeroExternalStoppedCoordinateSpec.coordinate_bound
    {t : DominoTiling} {o : LazyDecomposition.Orientation}
    {m k low externalLow externalHigh total : ℕ}
    {z : TilingOrientedShellZeroSourcePartition.OrientedTilingTypedExternalWordCode t}
    (data : LiteralShellZeroExternalStoppedCoordinateSpec t o m k low
      externalLow externalHigh total z)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (hexternal : ShellZeroExternalWindowArithmeticAt m externalLow externalHigh)
    (cap : ℕ) :
    prefixedTilingStoppedAcceptedGeometricMass (data.sourceStoppingTime cap)
        z.initial.1 t z.start z.retained (data.coordinateCap cap) z.tail.1
          (data.sourcePredicate cap) ≤
      centralReplacementRatio shellZeroLocalRatioConstant total *
        prefixedTilingStoppedAcceptedGeometricMass
          (data.replacementStoppingTime cap) z.initial.1 t z.start z.retained
          (data.coordinateCap cap) z.tail.1
            (data.replacementPredicate cap) := by
  classical
  let source := fun b v ↦ tilingShellZeroSourceCoordinate
    (cap := data.coordinateCap cap) (m := m) (w := shellWidth48 m)
    t z.start z.retained data.distinguished (data.upper cap) b v
  let replacement := fun b v ↦ tilingShellZeroReplacementCoordinate
    (cap := data.coordinateCap cap) (m := m) (w := shellWidth48 m)
    t z.start z.retained data.distinguished (data.upper cap) b v
  let sourceScreen := allSourceVector source
  let replacementScreen := exactSourceSubsetVector source replacement
    (centralReplacementUpperCount shellZeroLocalRatioConstant total)
  have hproduct := tilingAllSourceProductMass_le_centralReplacement
    t z.start z.retained data.distinguished (data.upper cap) harithmetic
      ((data.coordinateSupport cap).toWindowData hexternal)
  have hscreen : @screenMass
      (TilingAwayDomino t z.start z.retained data.distinguished)
      (instFintypeTilingAwayDomino t z.start z.retained data.distinguished)
      (fun a b ↦ Subtype.instDecidableEq a b)
      (tilingAwayPointMass (cap := data.coordinateCap cap) t z.start
        z.retained data.distinguished) (data.upper cap) sourceScreen
      (instDecidablePredAllSourceVector source) ≤
    centralReplacementRatio shellZeroLocalRatioConstant total *
      @screenMass
        (TilingAwayDomino t z.start z.retained data.distinguished)
        (instFintypeTilingAwayDomino t z.start z.retained data.distinguished)
        (fun a b ↦ Subtype.instDecidableEq a b)
        (tilingAwayPointMass (cap := data.coordinateCap cap) t z.start
          z.retained data.distinguished) (data.upper cap)
          replacementScreen
          (Classical.decPred replacementScreen) := by
    dsimp only [sourceScreen, replacementScreen]
    rw [sourceScreenMass_eq data cap,
      replacementScreenMass_eq data hexternal cap]
    exact hproduct
  have hselector := prefixedTilingDistinguishedSelectorMass_mono
    t z.start z.retained data.distinguished (data.upper cap)
      (data.replacementSelected cap) (data.sourceSelected cap)
      (data.source_selected_subset cap)
  exact prefixedTilingStoppedAcceptedGeometricMass_le_of_crossClock
    (data.replacementStoppingTime cap) (data.sourceStoppingTime cap)
    z.initial.1 t z.start z.retained z.tail.1
    (data.replacementPredicate cap) (data.sourcePredicate cap)
    data.distinguished (data.replacementSelected cap)
    (data.sourceSelected cap) (data.upper cap) replacementScreen sourceScreen
    (data.replacement_factorization cap) (data.source_factorization cap)
    (tilingAwayPointMass_normalization_ne_zero_of_upper_pos
      t z.start z.retained data.distinguished (data.upper cap)
        (data.upper_pos cap))
    (centralReplacementRatio shellZeroLocalRatioConstant total)
    (centralReplacementRatio_nonneg shellZeroLocalRatioConstant_pos.le total)
    hscreen hselector

end

end Erdos1165.TilingShellZeroExternalCrossClockBound
