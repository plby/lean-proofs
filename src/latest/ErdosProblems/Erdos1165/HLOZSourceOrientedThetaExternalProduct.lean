/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.HLOZSourceOrientedThetaProduct
import ErdosProblems.Erdos1165.TilingOrientedExternalAllCreationStoppedCoordinate

/-!
# Absolute Theta product on external-word creation fibres

Proposition 4.5 is an absolute estimate after fixing the oriented retained
external word.  It is not a conditional estimate inside a current-favorite
atom.  This file therefore repeats the finite-product screen on the coarser
external-word/support coordinate data.  The screen is the unconditional
Boolean union that some away coordinate lies in the Theta failure window;
there is no broad-screen denominator.

The path-space application may further coarsen over the exact support.  The
quantitative statement here only uses the literal retained word, the chosen
away carrier, and the normalized negative-binomial point masses.
-/

open scoped BigOperators

namespace Erdos1165.HLOZSourceOrientedThetaExternalProduct

open ExternalProposition44 FiniteDominoProductLaw
open HLOZAllSixExactCoordinateProductClosure HLOZNegativeBinomialTruncation
open HLOZFiniteProductCoordinateUnion
open HLOZSourceOrientedThetaBalance
open HLOZSourceOrientedThetaProduct
open HLOZShellZeroExternalWindow
open TilingCappedMarginalization TilingSpatialInsertionFiber
open TilingOrientedAllCreationConcreteFamily
open TilingOrientedExternalAllCreationStoppedCoordinate
open TilingOrientedShellZeroSourcePartition
open TilingOrientedSupportAwayCoordinates
open ScreeningInstantiation

noncomputable section

abbrev DominoTiling := Tilings.Tiling

/-- The absolute external-word Theta screen. -/
def externalThetaAccepts
    {t : DominoTiling} {o : LazyDecomposition.Orientation} {m k : ℕ}
    {supportAt : WalkPath → ℕ → Finset Point} {S : Finset Point}
    {z : OrientedTilingTypedExternalWordCode t}
    (data : Spec t o m k supportAt S z)
    (w externalLow externalHigh cap : ℕ)
    (ell : TruncatedTotals (data.upper cap)) : Bool :=
  decide (∃ b, thetaCoordinateBad m w externalLow externalHigh
    (Fintype.card (TilingCoordinatesAt t z.start z.retained b.1)) (ell b))

noncomputable def externalThetaScreenMass
    {t : DominoTiling} {o : LazyDecomposition.Orientation} {m k : ℕ}
    {supportAt : WalkPath → ℕ → Finset Point} {S : Finset Point}
    {z : OrientedTilingTypedExternalWordCode t}
    (data : Spec t o m k supportAt S z)
    (w externalLow externalHigh cap : ℕ) : ℝ :=
  @screenMass
    (TilingAwayDomino t z.start z.retained
      (supportComplementDistinguished t z.start z.retained S))
    (instFintypeTilingAwayDomino t z.start z.retained
      (supportComplementDistinguished t z.start z.retained S))
    (fun a b ↦ Subtype.instDecidableEq a b)
    (tilingAwayPointMass (cap := data.coordinateCap cap) t z.start z.retained
      (supportComplementDistinguished t z.start z.retained S))
    (data.upper cap)
    (fun ell ↦ externalThetaAccepts data w externalLow externalHigh cap ell = true)
    (fun ell ↦ instDecidableEqBool
      (externalThetaAccepts data w externalLow externalHigh cap ell) true)

def externalThetaCost
    {t : DominoTiling} {o : LazyDecomposition.Orientation} {m k : ℕ}
    {supportAt : WalkPath → ℕ → Finset Point} {S : Finset Point}
    {z : OrientedTilingTypedExternalWordCode t}
    (_data : Spec t o m k supportAt S z) (_cap : ℕ)
    (b : TilingAwayDomino t z.start z.retained
      (supportComplementDistinguished t z.start z.retained S)) : ℝ :=
  thetaCoordinateCost m
    (Fintype.card (TilingCoordinatesAt t z.start z.retained b.1))

/-- The exact deterministic support conditions for an absolute external-word
Theta product. -/
structure ExternalThetaProductArithmetic
    {t : DominoTiling} {o : LazyDecomposition.Orientation} {m k : ℕ}
    {supportAt : WalkPath → ℕ → Finset Point} {S : Finset Point}
    {z : OrientedTilingTypedExternalWordCode t}
    (data : Spec t o m k supportAt S z)
    (w externalLow externalHigh cap : ℕ) : Prop where
  level_pos : 0 < m
  width : (w : ℝ) ≤ (m : ℝ) / 10
  width_eq : w = HLOZProposition48Candidates.shellWidth48 m
  externalLow_eq : externalLow = shellZeroExternalLow48 m
  externalHigh_eq : externalHigh = shellZeroExternalHigh48 m
  geometric : geometricDeviation m ≤ m + w
  theta : thetaLowDeviation m ≤ m + w
  thick_nonneg : 0 ≤ hlozThickThresholdReal44 m
  low_dom : (w : ℝ) + thetaLowDeviation m ≤
    (16 / 15 : ℝ) * (m : ℝ) ^ (4 / 5 : ℝ)
  upper_le_cap : ∀ b, data.upper cap b ≤ data.coordinateCap cap + 1
  mean : ∀ b, 2 * Fintype.card
    (TilingCoordinatesAt t z.start z.retained b.1) ≤ 15 * data.upper cap b
  window_upper : ∀
    (b : TilingAwayDomino t z.start z.retained
      (supportComplementDistinguished t z.start z.retained S)) v,
    v ∈ thetaFailureWindow m w
      (Fintype.card (TilingCoordinatesAt t z.start z.retained b.1)) →
    v < data.upper cap b
  window_cap : ∀
    (b : TilingAwayDomino t z.start z.retained
      (supportComplementDistinguished t z.start z.retained S)) v,
    v ∈ thetaFailureWindow m w
      (Fintype.card (TilingCoordinatesAt t z.start z.retained b.1)) →
    v ≤ data.coordinateCap cap

lemma externalTheta_pointMass_nonneg
    {t : DominoTiling} {o : LazyDecomposition.Orientation} {m k : ℕ}
    {supportAt : WalkPath → ℕ → Finset Point} {S : Finset Point}
    {z : OrientedTilingTypedExternalWordCode t}
    (data : Spec t o m k supportAt S z) (cap : ℕ) (b) (v : ℕ) :
    0 ≤ tilingAwayPointMass (cap := data.coordinateCap cap) t z.start
      z.retained (supportComplementDistinguished t z.start z.retained S) b v :=
  tilingAwayExactTotalMass_nonneg t z.start z.retained
    (supportComplementDistinguished t z.start z.retained S) b v

lemma externalTheta_coordinate_sum_eq_one
    {t : DominoTiling} {o : LazyDecomposition.Orientation} {m k : ℕ}
    {supportAt : WalkPath → ℕ → Finset Point} {S : Finset Point}
    {z : OrientedTilingTypedExternalWordCode t}
    (data : Spec t o m k supportAt S z) (cap : ℕ) (b) :
    (∑ v : Fin (data.upper cap b), coordinateMass
      (tilingAwayPointMass (cap := data.coordinateCap cap) t z.start
        z.retained (supportComplementDistinguished t z.start z.retained S))
      (data.upper cap) b v) = 1 := by
  exact sum_coordinateMass_eq_one_of_zero_pos _ _
    (externalTheta_pointMass_nonneg data cap) (data.upper_pos cap)
    (fun c ↦ tilingAwayExactTotalMass_zero_pos t z.start z.retained
      (supportComplementDistinguished t z.start z.retained S) c) b

lemma externalTheta_denominator
    {t : DominoTiling} {o : LazyDecomposition.Orientation} {m k : ℕ}
    {supportAt : WalkPath → ℕ → Finset Point} {S : Finset Point}
    {z : OrientedTilingTypedExternalWordCode t}
    (data : Spec t o m k supportAt S z) (w externalLow externalHigh cap : ℕ)
    (arith : ExternalThetaProductArithmetic data w externalLow externalHigh cap)
    (b) :
    (1 / 2 : ℝ) ≤ ∑ v : Fin (data.upper cap b),
      tilingAwayPointMass (cap := data.coordinateCap cap) t z.start z.retained
        (supportComplementDistinguished t z.start z.retained S) b v := by
  exact half_le_sum_tilingAwayPointMass t z.start z.retained
    (supportComplementDistinguished t z.start z.retained S) b
    (data.upper cap b) (data.upper_pos cap b) (arith.upper_le_cap b)
    (card_tilingCoordinatesAt_pos t z.start z.retained b.1) (arith.mean b)

lemma externalTheta_bad_mass_le
    {t : DominoTiling} {o : LazyDecomposition.Orientation} {m k : ℕ}
    {supportAt : WalkPath → ℕ → Finset Point} {S : Finset Point}
    {z : OrientedTilingTypedExternalWordCode t}
    (data : Spec t o m k supportAt S z) (w externalLow externalHigh cap : ℕ)
    (arith : ExternalThetaProductArithmetic data w externalLow externalHigh cap)
    (b) :
    (∑ v : Fin (data.upper cap b),
      if thetaCoordinateBad m w externalLow externalHigh
          (Fintype.card (TilingCoordinatesAt t z.start z.retained b.1)) v then
        tilingAwayPointMass (cap := data.coordinateCap cap) t z.start z.retained
          (supportComplementDistinguished t z.start z.retained S) b v
      else 0) ≤ externalThetaCost data cap b := by
  classical
  exact sum_thetaCoordinateBad_tilingAwayPointMass_le t z.start z.retained
    (supportComplementDistinguished t z.start z.retained S) b
    arith.level_pos arith.width arith.width_eq arith.externalLow_eq
    arith.externalHigh_eq arith.geometric arith.theta arith.thick_nonneg
    arith.low_dom (arith.window_upper b) (arith.window_cap b)

/-- Literal unconditional finite-product bound on one external-word/support
fibre. -/
theorem externalThetaScreenMass_le
    {t : DominoTiling} {o : LazyDecomposition.Orientation} {m k : ℕ}
    {supportAt : WalkPath → ℕ → Finset Point} {S : Finset Point}
    {z : OrientedTilingTypedExternalWordCode t}
    (data : Spec t o m k supportAt S z)
    (w externalLow externalHigh cap : ℕ)
    (arith : ExternalThetaProductArithmetic data w externalLow
      externalHigh cap) :
    externalThetaScreenMass data w externalLow externalHigh cap ≤
      2 * ∑ b : TilingAwayDomino t z.start z.retained
        (supportComplementDistinguished t z.start z.retained S),
          externalThetaCost data cap b := by
  classical
  let pointMass := tilingAwayPointMass (cap := data.coordinateCap cap) t
    z.start z.retained
      (supportComplementDistinguished t z.start z.retained S)
  let upper := data.upper cap
  let bad := fun b (v : Fin (upper b)) ↦
    thetaCoordinateBad m w externalLow externalHigh
      (Fintype.card (TilingCoordinatesAt t z.start z.retained b.1)) v
  let cost := fun b : TilingAwayDomino t z.start z.retained
      (supportComplementDistinguished t z.start z.retained S) ↦
    thetaCoordinateCost m
      (Fintype.card (TilingCoordinatesAt t z.start z.retained b.1))
  have hpoint : ∀ b v, 0 ≤ pointMass b v :=
    externalTheta_pointMass_nonneg data cap
  have hsum : ∀ b, (∑ v : Fin (upper b),
      coordinateMass pointMass upper b v) = 1 := by
    exact externalTheta_coordinate_sum_eq_one data cap
  have hden : ∀ b, (1 / 2 : ℝ) ≤
      ∑ v : Fin (upper b), pointMass b v := by
    exact externalTheta_denominator data w externalLow externalHigh cap arith
  have hbad : ∀ b, (∑ v : Fin (upper b),
      if bad b v then pointMass b v else 0) ≤ cost b := by
    exact externalTheta_bad_mass_le data w externalLow externalHigh cap arith
  have haccepts : ∀ ell, externalThetaAccepts data w externalLow
      externalHigh cap ell = true ↔ ∃ b, bad b (ell b) := by
    intro ell
    simp [externalThetaAccepts, bad, upper]
  have hmain := @screenMass_bool_iff_exists_coordinate_le_two_mul_sum
    (TilingAwayDomino t z.start z.retained
      (supportComplementDistinguished t z.start z.retained S))
    (instFintypeTilingAwayDomino t z.start z.retained
      (supportComplementDistinguished t z.start z.retained S))
    (fun a b ↦ Subtype.instDecidableEq a b)
    pointMass upper bad (fun _ ↦ Classical.decPred _)
    (externalThetaAccepts data w externalLow externalHigh cap) haccepts cost
    hpoint hsum hden hbad
  let explicitUniv : Finset
      (TilingAwayDomino t z.start z.retained
        (supportComplementDistinguished t z.start z.retained S)) :=
    @Finset.univ
      (TilingAwayDomino t z.start z.retained
        (supportComplementDistinguished t z.start z.retained S))
      (instFintypeTilingAwayDomino t z.start z.retained
        (supportComplementDistinguished t z.start z.retained S))
  unfold externalThetaScreenMass
  calc
    @screenMass
        (TilingAwayDomino t z.start z.retained
          (supportComplementDistinguished t z.start z.retained S))
        (instFintypeTilingAwayDomino t z.start z.retained
          (supportComplementDistinguished t z.start z.retained S))
        (fun a b ↦ Subtype.instDecidableEq a b)
        pointMass upper
        (fun ell ↦ externalThetaAccepts data w externalLow externalHigh
          cap ell = true)
        (fun ell ↦ instDecidableEqBool
          (externalThetaAccepts data w externalLow externalHigh cap ell) true) ≤
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

/-- Large-retained-multiplicity coordinates of an external fibre. -/
def externalThetaHighCoordinates
    {t : DominoTiling} {o : LazyDecomposition.Orientation} {m k : ℕ}
    {supportAt : WalkPath → ℕ → Finset Point} {S : Finset Point}
    {z : OrientedTilingTypedExternalWordCode t}
    (_data : Spec t o m k supportAt S z) (_cap : ℕ) :
    Finset (TilingAwayDomino t z.start z.retained
      (supportComplementDistinguished t z.start z.retained S)) :=
  Finset.univ.filter fun b ↦ hlozThickLevel44 m ≤
    Fintype.card (TilingCoordinatesAt t z.start z.retained b.1)

lemma sum_externalThetaCost_le
    {t : DominoTiling} {o : LazyDecomposition.Orientation} {m k : ℕ}
    {supportAt : WalkPath → ℕ → Finset Point} {S : Finset Point}
    {z : OrientedTilingTypedExternalWordCode t}
    (data : Spec t o m k supportAt S z) (cap : ℕ) :
    (∑ b : TilingAwayDomino t z.start z.retained
        (supportComplementDistinguished t z.start z.retained S),
      externalThetaCost data cap b) ≤
      ((externalThetaHighCoordinates data cap).card : ℝ) *
          Real.exp (-17 * balanceRateScale m) +
        (S.card : ℝ) * Real.exp (-17 * thetaLowRateScale m) := by
  classical
  let highCost := Real.exp (-17 * balanceRateScale m)
  let lowCost := Real.exp (-17 * thetaLowRateScale m)
  calc
    (∑ b : TilingAwayDomino t z.start z.retained
        (supportComplementDistinguished t z.start z.retained S),
      externalThetaCost data cap b) ≤
      ∑ b : TilingAwayDomino t z.start z.retained
        (supportComplementDistinguished t z.start z.retained S),
        ((if hlozThickLevel44 m ≤ Fintype.card
            (TilingCoordinatesAt t z.start z.retained b.1)
          then highCost else 0) + lowCost) := by
      apply Finset.sum_le_sum
      intro b _
      unfold externalThetaCost thetaCoordinateCost highCost lowCost
      split
      · exact le_add_of_nonneg_right (Real.exp_pos _).le
      · simp only [zero_add, le_refl]
    _ = ((externalThetaHighCoordinates data cap).card : ℝ) * highCost +
        (S.card : ℝ) * lowCost := by
      rw [Finset.sum_add_distrib]
      congr 1
      · rw [show (∑ b : TilingAwayDomino t z.start z.retained
          (supportComplementDistinguished t z.start z.retained S),
          if hlozThickLevel44 m ≤ Fintype.card
              (TilingCoordinatesAt t z.start z.retained b.1)
            then highCost else 0) =
          ((externalThetaHighCoordinates data cap).card : ℝ) * highCost by
          rw [← Finset.sum_filter]
          simp only [Finset.sum_const, nsmul_eq_mul,
            externalThetaHighCoordinates]]
      · simp only [Finset.sum_const, nsmul_eq_mul]
        let explicitUniv : Finset
            (TilingAwayDomino t z.start z.retained
              (supportComplementDistinguished t z.start z.retained S)) :=
          @Finset.univ
            (TilingAwayDomino t z.start z.retained
              (supportComplementDistinguished t z.start z.retained S))
            (instFintypeTilingAwayDomino t z.start z.retained
              (supportComplementDistinguished t z.start z.retained S))
        have huniv : explicitUniv =
            (Finset.univ : Finset (TilingAwayDomino t z.start z.retained
              (supportComplementDistinguished t z.start z.retained S))) := by
          ext b
          simp [explicitUniv]
        have hcard : (Finset.univ : Finset
            (TilingAwayDomino t z.start z.retained
              (supportComplementDistinguished t z.start z.retained S))).card =
            S.card := by
          rw [← huniv]
          simpa only [explicitUniv, Finset.card_univ] using
            card_supportAwayDomino t z.start z.retained S
              data.support_represented
        rw [hcard]
    _ = _ := rfl

/-- Concrete external-fibre normalization and the source-scale coordinate
cost. -/
theorem externalConcreteFiber_theta_le_of_scale
    {t : DominoTiling} {o : LazyDecomposition.Orientation} {m k : ℕ}
    {supportAt : WalkPath → ℕ → Finset Point}
    (supportData : OrientedAllCreationSupportSelectorData t o m k supportAt)
    (eta : SupportedIndex t o m k supportAt)
    (cap : ℕ) (scale : OrientedThetaScaleArithmetic m) :
    let data := concreteFiber o m k supportAt supportData eta
    externalThetaScreenMass data
        (HLOZProposition48Candidates.shellWidth48 m)
        (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m) cap ≤
      2 * (((externalThetaHighCoordinates data cap).card : ℝ) *
          Real.exp (-17 * balanceRateScale m) +
        (eta.1.2.card : ℝ) * Real.exp (-17 * thetaLowRateScale m)) := by
  let data := concreteFiber o m k supportAt supportData eta
  have harith : ExternalThetaProductArithmetic data
      (HLOZProposition48Candidates.shellWidth48 m)
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m) cap := by
    refine
      { level_pos := scale.level_pos
        width := scale.width
        width_eq := rfl
        externalLow_eq := rfl
        externalHigh_eq := rfl
        geometric := scale.geometric
        theta := scale.theta
        thick_nonneg := scale.thick_nonneg
        low_dom := scale.low_dom
        upper_le_cap := ?_
        mean := ?_
        window_upper := ?_
        window_cap := ?_ }
    · intro b
      dsimp only [data, concreteFiber]
      omega
    · intro b
      have hcard := card_tilingCoordinatesAt_le_retainedCount_succ t
        eta.1.1.start eta.1.1.retained b.1
      dsimp only [data, concreteFiber] at hcard ⊢
      omega
    · intro b v hv
      have hv' := lazy_le_total_upper_of_mem_thetaFailureWindow hv
      dsimp only [data, concreteFiber]
      omega
    · intro b v hv
      have hv' := lazy_le_total_upper_of_mem_thetaFailureWindow hv
      dsimp only [data, concreteFiber]
      omega
  exact (externalThetaScreenMass_le data
    (HLOZProposition48Candidates.shellWidth48 m)
    (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m) cap harith).trans
      (mul_le_mul_of_nonneg_left (sum_externalThetaCost_le data cap)
        (by norm_num))

end

end Erdos1165.HLOZSourceOrientedThetaExternalProduct
