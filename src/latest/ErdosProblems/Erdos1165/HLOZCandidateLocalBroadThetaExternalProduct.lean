/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.HLOZCandidateLocalBroadThetaProduct
import ErdosProblems.Erdos1165.HLOZSourceOrientedThetaExternalProduct

/-!
# Broad source-Theta product on external-word creation fibres

This is the external-word analogue of the broad one-coordinate estimate used
by the candidate-local product branch.  It deliberately stops before any
path-space or stopped-history identification: the output is the normalized
finite-product mass of the literal one-sided source-window screen.
-/

open scoped BigOperators

namespace Erdos1165.HLOZCandidateLocalBroadThetaExternalProduct

open ExternalProposition44 FiniteDominoProductLaw
open HLOZCandidateLocalBroadThetaProduct HLOZFiniteProductCoordinateUnion
open HLOZNegativeBinomialTruncation HLOZSourceOrientedThetaBalance
open HLOZSourceOrientedThetaExternalProduct HLOZSourceOrientedThetaProduct
open ScreeningInstantiation TilingCappedMarginalization
open TilingOrientedAllCreationConcreteFamily
open TilingOrientedExternalAllCreationStoppedCoordinate
open TilingOrientedShellZeroSourcePartition
open TilingOrientedSupportAwayCoordinates TilingSpatialInsertionFiber

noncomputable section

abbrev DominoTiling := Tilings.Tiling

/-- The literal broad source-window union on one external fibre. -/
def externalBroadSourceThetaAccepts
    {t : DominoTiling} {o : LazyDecomposition.Orientation} {m k : ℕ}
    {supportAt : WalkPath → ℕ → Finset Point} {S : Finset Point}
    {z : OrientedTilingTypedExternalWordCode t}
    (data : Spec t o m k supportAt S z)
    (width externalThreshold cap : ℕ)
    (ell : TruncatedTotals (data.upper cap)) : Bool :=
  decide (∃ b, broadSourceThetaCoordinateBad m width externalThreshold
    (Fintype.card (TilingCoordinatesAt t z.start z.retained b.1)) (ell b))

noncomputable def externalBroadSourceThetaScreenMass
    {t : DominoTiling} {o : LazyDecomposition.Orientation} {m k : ℕ}
    {supportAt : WalkPath → ℕ → Finset Point} {S : Finset Point}
    {z : OrientedTilingTypedExternalWordCode t}
    (data : Spec t o m k supportAt S z)
    (width externalThreshold cap : ℕ) : ℝ :=
  @screenMass
    (TilingAwayDomino t z.start z.retained
      (supportComplementDistinguished t z.start z.retained S))
    (instFintypeTilingAwayDomino t z.start z.retained
      (supportComplementDistinguished t z.start z.retained S))
    (fun a b ↦ Subtype.instDecidableEq a b)
    (tilingAwayPointMass (cap := data.coordinateCap cap) t z.start z.retained
      (supportComplementDistinguished t z.start z.retained S))
    (data.upper cap)
    (fun ell ↦ externalBroadSourceThetaAccepts data width externalThreshold
      cap ell = true)
    (fun ell ↦ instDecidableEqBool
      (externalBroadSourceThetaAccepts data width externalThreshold cap ell)
      true)

/-- Exact deterministic inputs for the broad external-fibre product. -/
structure ExternalBroadSourceThetaProductArithmetic
    {t : DominoTiling} {o : LazyDecomposition.Orientation} {m k : ℕ}
    {supportAt : WalkPath → ℕ → Finset Point} {S : Finset Point}
    {z : OrientedTilingTypedExternalWordCode t}
    (data : Spec t o m k supportAt S z)
    (width externalThreshold cap : ℕ) : Prop where
  level_pos : 0 < m
  width_bound : (width : ℝ) ≤ (m : ℝ) / 10
  capacity : HLOZCandidateLocalLazyCap.sourceCandidateLazyCap48 m +
    externalThreshold + width ≤ m + 1
  margin : (16 / 15 : ℝ) *
      HLOZShellZeroExternalWindow.shellZeroExternalLow48 m +
    geometricDeviation m ≤ (m : ℝ) + 1
  geometric : geometricDeviation m ≤ (m + width : ℕ)
  theta : thetaLowDeviation m ≤ (m + width : ℕ)
  thick_nonneg : 0 ≤ hlozThickThresholdReal44 m
  low_dom : (width : ℝ) + thetaLowDeviation m ≤
    (16 / 15 : ℝ) * (m : ℝ) ^ (4 / 5 : ℝ)
  upper_le_cap : ∀ b, data.upper cap b ≤ data.coordinateCap cap + 1
  mean : ∀ b, 2 * Fintype.card
    (TilingCoordinatesAt t z.start z.retained b.1) ≤ 15 * data.upper cap b
  window_upper : ∀
    (b : TilingAwayDomino t z.start z.retained
      (supportComplementDistinguished t z.start z.retained S)) v,
    v ∈ HLOZShellZeroReplacementWindows.shellZeroSourceFailureWindow
        m width (Fintype.card
          (TilingCoordinatesAt t z.start z.retained b.1)) →
    v < data.upper cap b
  window_cap : ∀
    (b : TilingAwayDomino t z.start z.retained
      (supportComplementDistinguished t z.start z.retained S)) v,
    v ∈ HLOZShellZeroReplacementWindows.shellZeroSourceFailureWindow
        m width (Fintype.card
          (TilingCoordinatesAt t z.start z.retained b.1)) →
    v ≤ data.coordinateCap cap

lemma externalBroadSourceTheta_bad_mass_le
    {t : DominoTiling} {o : LazyDecomposition.Orientation} {m k : ℕ}
    {supportAt : WalkPath → ℕ → Finset Point} {S : Finset Point}
    {z : OrientedTilingTypedExternalWordCode t}
    (data : Spec t o m k supportAt S z)
    (width externalThreshold cap : ℕ)
    (arith : ExternalBroadSourceThetaProductArithmetic data width
      externalThreshold cap)
    (b) :
    (∑ v : Fin (data.upper cap b),
      if broadSourceThetaCoordinateBad m width externalThreshold
          (Fintype.card (TilingCoordinatesAt t z.start z.retained b.1)) v then
        tilingAwayPointMass (cap := data.coordinateCap cap) t z.start z.retained
          (supportComplementDistinguished t z.start z.retained S) b v
      else 0) ≤ externalThetaCost data cap b := by
  exact sum_broadSourceThetaCoordinateBad_tilingAwayPointMass_le
    t z.start z.retained
    (supportComplementDistinguished t z.start z.retained S) b
    arith.level_pos arith.width_bound arith.capacity arith.margin arith.geometric
    arith.theta arith.thick_nonneg arith.low_dom (arith.window_upper b)
    (arith.window_cap b)

/-- Literal normalized finite-product estimate for the broad source screen. -/
theorem externalBroadSourceThetaScreenMass_le
    {t : DominoTiling} {o : LazyDecomposition.Orientation} {m k : ℕ}
    {supportAt : WalkPath → ℕ → Finset Point} {S : Finset Point}
    {z : OrientedTilingTypedExternalWordCode t}
    (data : Spec t o m k supportAt S z)
    (width externalThreshold cap : ℕ)
    (arith : ExternalBroadSourceThetaProductArithmetic data width
      externalThreshold cap) :
    externalBroadSourceThetaScreenMass data width externalThreshold cap ≤
      2 * ∑ b : TilingAwayDomino t z.start z.retained
        (supportComplementDistinguished t z.start z.retained S),
          externalThetaCost data cap b := by
  classical
  let pointMass := tilingAwayPointMass (cap := data.coordinateCap cap) t
    z.start z.retained
      (supportComplementDistinguished t z.start z.retained S)
  let upper := data.upper cap
  let bad := fun b (v : Fin (upper b)) ↦
    broadSourceThetaCoordinateBad m width externalThreshold
      (Fintype.card (TilingCoordinatesAt t z.start z.retained b.1)) v
  let cost := fun b : TilingAwayDomino t z.start z.retained
      (supportComplementDistinguished t z.start z.retained S) ↦
    thetaCoordinateCost m
      (Fintype.card (TilingCoordinatesAt t z.start z.retained b.1))
  have hpoint : ∀ b v, 0 ≤ pointMass b v :=
    externalTheta_pointMass_nonneg data cap
  have hsum : ∀ b, (∑ v : Fin (upper b),
      coordinateMass pointMass upper b v) = 1 :=
    externalTheta_coordinate_sum_eq_one data cap
  have hden : ∀ b, (1 / 2 : ℝ) ≤ ∑ v : Fin (upper b), pointMass b v := by
    intro b
    exact half_le_sum_tilingAwayPointMass t z.start z.retained
      (supportComplementDistinguished t z.start z.retained S) b
      (data.upper cap b) (data.upper_pos cap b) (arith.upper_le_cap b)
      (card_tilingCoordinatesAt_pos t z.start z.retained b.1) (arith.mean b)
  have hbad : ∀ b, (∑ v : Fin (upper b),
      if bad b v then pointMass b v else 0) ≤ cost b := by
    exact externalBroadSourceTheta_bad_mass_le data width externalThreshold
      cap arith
  have haccepts : ∀ ell, externalBroadSourceThetaAccepts data width
      externalThreshold cap ell = true ↔ ∃ b, bad b (ell b) := by
    intro ell
    simp [externalBroadSourceThetaAccepts, bad, upper]
  have hmain := @screenMass_bool_iff_exists_coordinate_le_two_mul_sum
    (TilingAwayDomino t z.start z.retained
      (supportComplementDistinguished t z.start z.retained S))
    (instFintypeTilingAwayDomino t z.start z.retained
      (supportComplementDistinguished t z.start z.retained S))
    (fun a b ↦ Subtype.instDecidableEq a b)
    pointMass upper bad (fun _ ↦ Classical.decPred _)
    (externalBroadSourceThetaAccepts data width externalThreshold cap)
    haccepts cost hpoint hsum hden hbad
  let explicitUniv : Finset
      (TilingAwayDomino t z.start z.retained
        (supportComplementDistinguished t z.start z.retained S)) :=
    @Finset.univ
      (TilingAwayDomino t z.start z.retained
        (supportComplementDistinguished t z.start z.retained S))
      (instFintypeTilingAwayDomino t z.start z.retained
        (supportComplementDistinguished t z.start z.retained S))
  unfold externalBroadSourceThetaScreenMass
  calc
    @screenMass
        (TilingAwayDomino t z.start z.retained
          (supportComplementDistinguished t z.start z.retained S))
        (instFintypeTilingAwayDomino t z.start z.retained
          (supportComplementDistinguished t z.start z.retained S))
        (fun a b ↦ Subtype.instDecidableEq a b)
        pointMass upper
        (fun ell ↦ externalBroadSourceThetaAccepts data width
          externalThreshold cap ell = true)
        (fun ell ↦ instDecidableEqBool
          (externalBroadSourceThetaAccepts data width externalThreshold cap ell)
          true) ≤
      2 * ∑ b ∈ explicitUniv, cost b := hmain
    _ = 2 * ∑ b, externalThetaCost data cap b := by
      congr 1
      have huniv : explicitUniv =
          (Finset.univ : Finset (TilingAwayDomino t z.start z.retained
            (supportComplementDistinguished t z.start z.retained S))) := by
        ext b
        simp [explicitUniv]
      rw [huniv]
      rfl

/-- The broad screen inherits the same high/low coordinate split as the
narrow source screen. -/
theorem externalBroadSourceThetaScreenMass_le_two_scale
    {t : DominoTiling} {o : LazyDecomposition.Orientation} {m k : ℕ}
    {supportAt : WalkPath → ℕ → Finset Point} {S : Finset Point}
    {z : OrientedTilingTypedExternalWordCode t}
    (data : Spec t o m k supportAt S z)
    (width externalThreshold cap : ℕ)
    (arith : ExternalBroadSourceThetaProductArithmetic data width
      externalThreshold cap) :
    externalBroadSourceThetaScreenMass data width externalThreshold cap ≤
      2 * (((externalThetaHighCoordinates data cap).card : ℝ) *
          Real.exp (-17 * balanceRateScale m) +
        (S.card : ℝ) * Real.exp (-17 * thetaLowRateScale m)) := by
  exact (externalBroadSourceThetaScreenMass_le data width externalThreshold
    cap arith).trans
      (mul_le_mul_of_nonneg_left (sum_externalThetaCost_le data cap)
        (by norm_num))

end

end Erdos1165.HLOZCandidateLocalBroadThetaExternalProduct
