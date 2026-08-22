/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.TilingShellZeroDeltaReplacementSound

/-!
# Finite-product mass bound partitioned by actual endpoint increment

This module exposes the product identities that were previously private to
single-clock adapters.  The exact-central replacement screen is partitioned
by its actual endpoint increment, so the source product is bounded by the
central ratio times the finite sum of fixed-delta screen masses.
-/

open scoped BigOperators

namespace Erdos1165.TilingShellZeroDeltaScreenMassBound

open FiniteDominoProductLaw HeterogeneousProductTail
open HLOZProposition48Candidates HLOZShellZeroCentralCount
open HLOZShellZeroReplacementWindows
open LazyDecomposition TilingLazyDecomposition
open TilingCappedMarginalization
open TilingPrefixedInsertedLocalTime
open TilingShellZeroActualDeltaPartition
open TilingShellZeroEndpointIncrementScreen
open TilingShellZeroFactoredCapScreen
open TilingShellZeroSourcePartition TilingSpatialInsertionFiber

noncomputable section

abbrev DominoTiling := Tilings.Tiling

private lemma ite_eq_ite_of_iff {α : Type*} {p q : Prop}
    [Decidable p] [Decidable q] {a b c d : α} (hpq : p ↔ q)
    (hac : a = c) (hbd : b = d) :
    (if p then a else b) = if q then c else d := by
  by_cases hp : p
  · rw [if_pos hp, if_pos (hpq.mp hp), hac]
  · rw [if_neg hp, if_neg (fun hq ↦ hp (hpq.mpr hq)), hbd]

/-- The literal all-source screen mass is the named all-source coordinate
product. -/
theorem screenMass_allSourceVector_eq_product
    {i cap m : ℕ} (t : DominoTiling) (x : Point)
    (r : TilingRetainedWord t x i) (D : Finset Point)
    (upper : TilingAwayDomino t x r D → ℕ) :
    @screenMass (TilingAwayDomino t x r D) inferInstance inferInstance
        (tilingAwayPointMass (cap := cap) t x r D) upper
        (allSourceVector fun b v ↦ tilingShellZeroSourceCoordinate
          (cap := cap) (m := m) (w := shellWidth48 m)
          t x r D upper b v)
        (Classical.decPred _) =
      tilingShellZeroAllSourceProductMass (cap := cap) (m := m)
        t x r D upper := by
  classical
  let source := fun b v ↦ tilingShellZeroSourceCoordinate
    (cap := cap) (m := m) (w := shellWidth48 m) t x r D upper b v
  rw [@screenMass_eq_product (TilingAwayDomino t x r D) inferInstance
    inferInstance (tilingAwayPointMass (cap := cap) t x r D) upper
    (allSourceVector source) (Classical.decPred _)]
  let weight := fun b (v : Fin (upper b)) ↦
    coordinateMass (tilingAwayPointMass (cap := cap) t x r D)
      upper b (v : ℕ)
  have hsum := @sum_allSourceVector_eq_product
    (TilingAwayDomino t x r D) inferInstance inferInstance
    (fun b ↦ Fin (upper b)) (fun b ↦ Fin.fintype (upper b)) weight source
    (fun _ ↦ Classical.decPred _)
  unfold productPointMass at hsum
  refine hsum.trans ?_
  unfold tilingShellZeroAllSourceProductMass
  congr 1
  funext b
  unfold tilingShellZeroSourceCoordinateMass
  apply Finset.sum_congr rfl
  intro v _
  exact ite_eq_ite_of_iff (by rfl) rfl rfl

/-- The exact-central source/replacement screen mass is the named central
replacement product. -/
theorem screenMass_exactSourceSubsetVector_eq_product
    {i cap m central : ℕ} (t : DominoTiling) (x : Point)
    (r : TilingRetainedWord t x i) (D : Finset Point)
    (upper : TilingAwayDomino t x r D → ℕ)
    (htranslate : ∀ b : TilingAwayDomino t x r D,
      Fintype.card (TilingCoordinatesAt t x r b.1) ≤ m - shellWidth48 m + 1) :
    @screenMass (TilingAwayDomino t x r D) inferInstance inferInstance
        (tilingAwayPointMass (cap := cap) t x r D) upper
        (exactSourceSubsetVector
          (fun b v ↦ tilingShellZeroSourceCoordinate
            (cap := cap) (m := m) (w := shellWidth48 m)
            t x r D upper b v)
          (fun b v ↦ tilingShellZeroReplacementCoordinate
            (cap := cap) (m := m) (w := shellWidth48 m)
            t x r D upper b v) central)
        (Classical.decPred _) =
      tilingShellZeroCentralReplacementProductMass
        (cap := cap) (m := m) t x r D upper central := by
  classical
  let source := fun b v ↦ tilingShellZeroSourceCoordinate
    (cap := cap) (m := m) (w := shellWidth48 m) t x r D upper b v
  let replacement := fun b v ↦ tilingShellZeroReplacementCoordinate
    (cap := cap) (m := m) (w := shellWidth48 m) t x r D upper b v
  rw [@screenMass_eq_product (TilingAwayDomino t x r D) inferInstance
    inferInstance (tilingAwayPointMass (cap := cap) t x r D) upper
    (exactSourceSubsetVector source replacement central) (Classical.decPred _)]
  let weight := fun b (v : Fin (upper b)) ↦
    coordinateMass (tilingAwayPointMass (cap := cap) t x r D)
      upper b (v : ℕ)
  have hsum := @sum_exactSourceSubsetVector_eq_exactUpperCountProductMass
    (TilingAwayDomino t x r D) inferInstance inferInstance
    (fun b ↦ Fin (upper b)) (fun b ↦ Fin.fintype (upper b))
    weight source replacement (fun _ ↦ Classical.decPred _)
    (fun _ ↦ Classical.decPred _)
    (tilingShellZeroCoordinate_disjoint t x r D upper htranslate) central
  unfold productPointMass at hsum
  refine hsum.trans ?_
  unfold tilingShellZeroCentralReplacementProductMass
  congr 1
  · funext b
    unfold tilingShellZeroSourceCoordinateMass
    apply Finset.sum_congr rfl
    intro v _
    exact ite_eq_ite_of_iff (by rfl) rfl rfl
  · funext b
    unfold tilingShellZeroReplacementCoordinateMass
    apply Finset.sum_congr rfl
    intro v _
    exact ite_eq_ite_of_iff (by rfl) rfl rfl

/-- Source product mass is controlled by the finite sum of honest
fixed-increment replacement screens. -/
theorem screenMass_source_le_ratio_mul_sum_actualDelta
    {i cap m total : ℕ} (t : DominoTiling) (x : Point)
    (r : TilingRetainedWord t x i) (D : Finset Point)
    (upper : TilingAwayDomino t x r D → ℕ)
    (initial : List Direction) (terminal : Option Point)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (data : TilingShellZeroCoordinateWindowData
      (cap := cap) (m := m) (total := total) t x r D upper)
    (hbase : ∀ b : TilingAwayDomino t x r D,
      prefixedTilingFixedBoundaryLocalTime initial x r terminal b.1.1 =
        Fintype.card (TilingCoordinatesAt t x r b.1))
    (hdominance : ∀ b : TilingAwayDomino t x r D,
      prefixedTilingFixedBoundaryLocalTime initial x r terminal
          (tilingPartner t b.1.1) ≤
        prefixedTilingFixedBoundaryLocalTime initial x r terminal b.1.1) :
    @screenMass (TilingAwayDomino t x r D) inferInstance inferInstance
        (tilingAwayPointMass (cap := cap) t x r D) upper
        (allSourceVector fun b v ↦ tilingShellZeroSourceCoordinate
          (cap := cap) (m := m) (w := shellWidth48 m)
          t x r D upper b v)
        (Classical.decPred _) ≤
      centralReplacementRatio shellZeroLocalRatioConstant total *
        ∑ delta : ReplacementEndpointIncrement total
            (centralReplacementUpperCount shellZeroLocalRatioConstant total),
          @screenMass (TilingAwayDomino t x r D) inferInstance inferInstance
            (tilingAwayPointMass (cap := cap) t x r D) upper
            (prefixedShellZeroReplacementScreenAtIncrement
              (cap := cap) (m := m) (w := shellWidth48 m)
              initial t x r terminal D upper
              (centralReplacementUpperCount shellZeroLocalRatioConstant total)
              delta)
            (Classical.decPred _) := by
  classical
  have hcard := data.card
  subst total
  let total := Fintype.card (TilingAwayDomino t x r D)
  rw [screenMass_allSourceVector_eq_product]
  have hsum := sum_screenMass_prefixedShellZeroReplacementScreenAtIncrement_eq
    (cap := cap) (m := m) (w := shellWidth48 m)
    initial t x r terminal D upper
    (centralReplacementUpperCount shellZeroLocalRatioConstant total)
    hbase hdominance
  have hcentral := screenMass_exactSourceSubsetVector_eq_product
    (cap := cap)
    (central := centralReplacementUpperCount shellZeroLocalRatioConstant total)
    t x r D upper data.translate
  have hproduct := tilingAllSourceProductMass_le_centralReplacement
    t x r D upper harithmetic data
  calc
    _ ≤ centralReplacementRatio shellZeroLocalRatioConstant total *
        tilingShellZeroCentralReplacementProductMass
          (cap := cap) (m := m) t x r D upper
            (centralReplacementUpperCount shellZeroLocalRatioConstant total) :=
      hproduct
    _ = centralReplacementRatio shellZeroLocalRatioConstant total *
        @screenMass (TilingAwayDomino t x r D) inferInstance inferInstance
          (tilingAwayPointMass (cap := cap) t x r D) upper
          (exactSourceSubsetVector
            (fun b v ↦ tilingShellZeroSourceCoordinate
              (cap := cap) (m := m) (w := shellWidth48 m)
              t x r D upper b v)
            (fun b v ↦ tilingShellZeroReplacementCoordinate
              (cap := cap) (m := m) (w := shellWidth48 m)
              t x r D upper b v)
            (centralReplacementUpperCount shellZeroLocalRatioConstant total))
          (Classical.decPred _) := congrArg _ hcentral.symm
    _ = centralReplacementRatio shellZeroLocalRatioConstant total *
        ∑ delta : ReplacementEndpointIncrement total
            (centralReplacementUpperCount shellZeroLocalRatioConstant total),
          @screenMass (TilingAwayDomino t x r D) inferInstance inferInstance
            (tilingAwayPointMass (cap := cap) t x r D) upper
            (prefixedShellZeroReplacementScreenAtIncrement
              (cap := cap) (m := m) (w := shellWidth48 m)
              initial t x r terminal D upper
              (centralReplacementUpperCount shellZeroLocalRatioConstant total)
              delta)
            (Classical.decPred _) := by
      congr 1
      exact hsum.symm

end

end Erdos1165.TilingShellZeroDeltaScreenMassBound
