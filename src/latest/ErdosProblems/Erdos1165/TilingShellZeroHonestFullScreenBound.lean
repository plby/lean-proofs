/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.TilingOrientedExternalStaticDAcceptedCreation
import ErdosProblems.Erdos1165.TilingShellZeroScreenedExternalStoppedCoordinateSpec

/-!
# Honest full-screen fixed-central comparison

The source full screen is contained in the pure all-`I₁` screen.  If every
pure fixed-central replacement vector is accepted by the replacement clock,
then its full screen equals the pure replacement screen.  The existing
fixed-central finite-product comparison therefore applies without a path
probability premise.
-/

open Set
open scoped BigOperators

namespace Erdos1165.TilingShellZeroHonestFullScreenBound

open FiniteDominoProductLaw HeterogeneousProductTail
open HLOZProposition48Candidates
open HLOZShellZeroCentralCount HLOZShellZeroCentralTail
open HLOZShellZeroExternalWindow HLOZShellZeroReplacementWindows
open TilingCappedMarginalization TilingConditionalCappedMarginalization
open TilingPrefixedHonestAcceptedCreationCrossClock
open TilingShellZeroFactoredCapScreen TilingShellZeroSourcePartition
open TilingSpatialInsertionFiber

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

private theorem pureSourceScreenMass_eq
    {i cap m : ℕ} (t : DominoTiling) (x : Point)
    (r : TilingRetainedWord t x i) (D : Finset Point)
    (upper : TilingAwayDomino t x r D → ℕ) :
    @screenMass (TilingAwayDomino t x r D)
        (instFintypeTilingAwayDomino t x r D)
        (fun a b ↦ Subtype.instDecidableEq a b)
        (tilingAwayPointMass (cap := cap) t x r D) upper
        (allSourceVector fun b v ↦ tilingShellZeroSourceCoordinate
          (cap := cap) (m := m) (w := shellWidth48 m) t x r D upper b v)
        (instDecidablePredAllSourceVector _) =
      tilingShellZeroAllSourceProductMass (cap := cap) (m := m)
        t x r D upper := by
  classical
  let source := fun b v ↦ tilingShellZeroSourceCoordinate
    (cap := cap) (m := m) (w := shellWidth48 m) t x r D upper b v
  rw [@screenMass_eq_product (TilingAwayDomino t x r D)
    (instFintypeTilingAwayDomino t x r D)
    (fun a b ↦ Subtype.instDecidableEq a b)
    (tilingAwayPointMass (cap := cap) t x r D) upper
    (allSourceVector source) (instDecidablePredAllSourceVector source)]
  let weight := fun b (v : Fin (upper b)) ↦
    coordinateMass (tilingAwayPointMass (cap := cap) t x r D) upper b (v : ℕ)
  have hsum := @sum_allSourceVector_eq_product
    (TilingAwayDomino t x r D) (instFintypeTilingAwayDomino t x r D)
    (fun a b ↦ Subtype.instDecidableEq a b)
    (fun b ↦ Fin (upper b)) (fun b ↦ Fin.fintype (upper b))
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
      (Fintype.card (TilingCoordinatesAt t x r b.1))
  · have hs : source b v := by
      simpa only [source, tilingShellZeroSourceCoordinate] using hv
    rw [if_pos hs, if_pos hv]
  · have hs : ¬ source b v := by
      simpa only [source, tilingShellZeroSourceCoordinate] using hv
    rw [if_neg hs, if_neg hv]

private theorem pureReplacementScreenMass_eq
    {i cap m total externalLow externalHigh : ℕ}
    (t : DominoTiling) (x : Point)
    (r : TilingRetainedWord t x i) (D : Finset Point)
    (upper : TilingAwayDomino t x r D → ℕ)
    (hexternal : ShellZeroExternalWindowArithmeticAt m externalLow externalHigh)
    (support : LiteralShellZeroCoordinateSupportData
      (cap := cap) (m := m) (externalLow := externalLow)
      (externalHigh := externalHigh) (total := total) t x r D upper) :
    @screenMass (TilingAwayDomino t x r D)
        (instFintypeTilingAwayDomino t x r D)
        (fun a b ↦ Subtype.instDecidableEq a b)
        (tilingAwayPointMass (cap := cap) t x r D) upper
        (exactSourceSubsetVector
          (fun b v ↦ tilingShellZeroSourceCoordinate
            (cap := cap) (m := m) (w := shellWidth48 m) t x r D upper b v)
          (fun b v ↦ tilingShellZeroReplacementCoordinate
            (cap := cap) (m := m) (w := shellWidth48 m) t x r D upper b v)
          (centralReplacementUpperCount shellZeroLocalRatioConstant total))
        (instDecidablePredExactSourceSubsetVector _ _ _) =
      tilingShellZeroCentralReplacementProductMass (cap := cap) (m := m)
        t x r D upper
          (centralReplacementUpperCount shellZeroLocalRatioConstant total) := by
  classical
  let source := fun b v ↦ tilingShellZeroSourceCoordinate
    (cap := cap) (m := m) (w := shellWidth48 m) t x r D upper b v
  let replacement := fun b v ↦ tilingShellZeroReplacementCoordinate
    (cap := cap) (m := m) (w := shellWidth48 m) t x r D upper b v
  let replacementScreen := exactSourceSubsetVector source replacement
    (centralReplacementUpperCount shellZeroLocalRatioConstant total)
  let namedReplacementScreen := @exactSourceSubsetVector
    (TilingAwayDomino t x r D) (instFintypeTilingAwayDomino t x r D)
    (fun a b ↦ Subtype.instDecidableEq a b) (fun b ↦ Fin (upper b))
    source replacement
    (centralReplacementUpperCount shellZeroLocalRatioConstant total)
  have hscreenProduct := @screenMass_eq_product
    (TilingAwayDomino t x r D) (instFintypeTilingAwayDomino t x r D)
    (fun a b ↦ Subtype.instDecidableEq a b)
    (tilingAwayPointMass (cap := cap) t x r D) upper replacementScreen
    (Classical.decPred replacementScreen)
  let weight := fun b (v : Fin (upper b)) ↦
    coordinateMass (tilingAwayPointMass (cap := cap) t x r D) upper b (v : ℕ)
  have hscreens : replacementScreen = namedReplacementScreen := by
    funext ell
    apply propext
    simpa only [replacementScreen, namedReplacementScreen] using
      (exactSourceSubsetVector_fintype_iff
        (Subtype.fintype fun b : TilingExternalDomino t x r ↦ b.1 ∉ D)
        (instFintypeTilingAwayDomino t x r D) source replacement
        (centralReplacementUpperCount shellZeroLocalRatioConstant total) ell)
  have hsum := @sum_exactSourceSubsetVector_eq_exactUpperCountProductMass
    (TilingAwayDomino t x r D) (instFintypeTilingAwayDomino t x r D)
    (fun a b ↦ Subtype.instDecidableEq a b)
    (fun b ↦ Fin (upper b)) (fun b ↦ Fin.fintype (upper b))
    weight source replacement (fun _ ↦ Classical.decPred _)
    (fun _ ↦ Classical.decPred _)
    (tilingShellZeroCoordinate_disjoint t x r D upper
      (support.toWindowData hexternal).translate)
    (centralReplacementUpperCount shellZeroLocalRatioConstant total)
  unfold productPointMass at hsum
  have hproduct : _ = tilingShellZeroCentralReplacementProductMass
      (cap := cap) (m := m) t x r D upper
        (centralReplacementUpperCount shellZeroLocalRatioConstant total) :=
    hsum.trans (by
      unfold tilingShellZeroCentralReplacementProductMass
      congr 1
      · funext b
        unfold tilingShellZeroSourceCoordinateMass
        apply Finset.sum_congr rfl
        intro v _
        by_cases hv : (v : ℕ) ∈ shellZeroSourceFailureWindow m
            (shellWidth48 m) (Fintype.card (TilingCoordinatesAt t x r b.1))
        · have hs : source b v := by
            simpa only [source, tilingShellZeroSourceCoordinate] using hv
          rw [if_pos hs, if_pos hv]
        · have hs : ¬ source b v := by
            simpa only [source, tilingShellZeroSourceCoordinate] using hv
          rw [if_neg hs, if_neg hv]
      · funext b
        unfold tilingShellZeroReplacementCoordinateMass
        apply Finset.sum_congr rfl
        intro v _
        by_cases hv : (v : ℕ) ∈ shellZeroReplacementFailureWindow m
            (shellWidth48 m) (Fintype.card (TilingCoordinatesAt t x r b.1))
        · have hr : replacement b v := by
            simpa only [replacement, tilingShellZeroReplacementCoordinate]
              using hv
          rw [if_pos hr, if_pos hv]
        · have hr : ¬ replacement b v := by
            simpa only [replacement, tilingShellZeroReplacementCoordinate]
              using hv
          rw [if_neg hr, if_neg hv])
  rw [hscreens] at hscreenProduct
  have hlocal : @screenMass (TilingAwayDomino t x r D)
      (instFintypeTilingAwayDomino t x r D)
      (fun a b ↦ Subtype.instDecidableEq a b)
      (tilingAwayPointMass (cap := cap) t x r D) upper replacementScreen
      (Classical.decPred replacementScreen) =
        tilingShellZeroCentralReplacementProductMass (cap := cap) (m := m)
          t x r D upper
            (centralReplacementUpperCount shellZeroLocalRatioConstant total) := by
    rw [hscreens]
    exact hscreenProduct.trans hproduct
  simpa only [replacementScreen, source, replacement] using hlocal

/-- Dropping source accepted-creation and using replacement acceptance on the
entire pure central screen reduces the full-screen comparison to the existing
HLOZ fixed-central product inequality. -/
theorem fullScreen_le_centralReplacement_of_replacement_accepts
    {initial tail : List Direction}
    {i cap m total externalLow externalHigh : ℕ}
    (t : DominoTiling) (x : Point) (r : TilingRetainedWord t x i)
    (D : Finset Point) (upper : TilingAwayDomino t x r D → ℕ)
    (source replacement : AcceptedCreationClockData
      (cap := cap) initial t x r tail D upper)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (hexternal : ShellZeroExternalWindowArithmeticAt m externalLow externalHigh)
    (support : LiteralShellZeroCoordinateSupportData
      (cap := cap) (m := m) (externalLow := externalLow)
      (externalHigh := externalHigh) (total := total) t x r D upper)
    (hreplacement : ∀ ell,
      exactSourceSubsetVector
        (fun b v ↦ tilingShellZeroSourceCoordinate
          (cap := cap) (m := m) (w := shellWidth48 m) t x r D upper b v)
        (fun b v ↦ tilingShellZeroReplacementCoordinate
          (cap := cap) (m := m) (w := shellWidth48 m) t x r D upper b v)
        (centralReplacementUpperCount shellZeroLocalRatioConstant total) ell →
      replacement.baseAccepts ell) :
    @screenMass (TilingAwayDomino t x r D)
        (instFintypeTilingAwayDomino t x r D)
        (fun a b ↦ Subtype.instDecidableEq a b)
        (tilingAwayPointMass (cap := cap) t x r D) upper
        (source.fullScreen (allSourceVector fun b v ↦
          tilingShellZeroSourceCoordinate (cap := cap) (m := m)
            (w := shellWidth48 m) t x r D upper b v))
        (Classical.decPred _) ≤
      centralReplacementRatio shellZeroLocalRatioConstant total *
        @screenMass (TilingAwayDomino t x r D)
          (instFintypeTilingAwayDomino t x r D)
          (fun a b ↦ Subtype.instDecidableEq a b)
          (tilingAwayPointMass (cap := cap) t x r D) upper
          (replacement.fullScreen (exactSourceSubsetVector
            (fun b v ↦ tilingShellZeroSourceCoordinate
              (cap := cap) (m := m) (w := shellWidth48 m)
                t x r D upper b v)
            (fun b v ↦ tilingShellZeroReplacementCoordinate
              (cap := cap) (m := m) (w := shellWidth48 m)
                t x r D upper b v)
            (centralReplacementUpperCount shellZeroLocalRatioConstant total)))
          (Classical.decPred _) := by
  classical
  let sourcePure := allSourceVector fun b v ↦ tilingShellZeroSourceCoordinate
    (cap := cap) (m := m) (w := shellWidth48 m) t x r D upper b v
  let replacementPure := exactSourceSubsetVector
    (fun b v ↦ tilingShellZeroSourceCoordinate
      (cap := cap) (m := m) (w := shellWidth48 m) t x r D upper b v)
    (fun b v ↦ tilingShellZeroReplacementCoordinate
      (cap := cap) (m := m) (w := shellWidth48 m) t x r D upper b v)
    (centralReplacementUpperCount shellZeroLocalRatioConstant total)
  have hsource : screenMass (tilingAwayPointMass (cap := cap) t x r D) upper
      (source.fullScreen sourcePure) ≤
      screenMass (tilingAwayPointMass (cap := cap) t x r D) upper
        sourcePure := by
    apply screenMass_mono_of_pointMass_nonneg
    · intro b v
      exact tilingAwayExactTotalMass_nonneg t x r D b v
    · intro ell hell
      exact hell.2
  have hreplacementEq : replacement.fullScreen replacementPure =
      replacementPure := by
    funext ell
    apply propext
    constructor
    · exact fun h ↦ h.2
    · intro h
      exact ⟨hreplacement ell h, h⟩
  have hpure : screenMass (tilingAwayPointMass (cap := cap) t x r D) upper
      sourcePure ≤
      centralReplacementRatio shellZeroLocalRatioConstant total *
        screenMass (tilingAwayPointMass (cap := cap) t x r D) upper
          replacementPure := by
    rw [pureSourceScreenMass_eq t x r D upper,
      pureReplacementScreenMass_eq t x r D upper hexternal support]
    exact tilingAllSourceProductMass_le_centralReplacement
      t x r D upper harithmetic (support.toWindowData hexternal)
  simpa only [sourcePure, replacementPure, hreplacementEq] using
    hsource.trans hpure

end

end Erdos1165.TilingShellZeroHonestFullScreenBound
