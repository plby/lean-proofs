/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.HLOZAllCreationCofinalConditionalSharpWindow
import ErdosProblems.Erdos1165.HLOZConditionalTruncatedRandomTotalProductBound
import ErdosProblems.Erdos1165.HLOZPositiveInterfacePhysicalWindows

/-!
# Cofinal conditional products for physical deficit-shell interfaces

The former positive-interface tail used negative-binomial windows centred at
the mean of each retained coordinate.  Those windows do not classify the
physical deficit shells.  This module gives the parallel finite-product
interface for the exact physical windows

`(m - (i + v)) / width = shell + 1` and
`(m - (i + v)) / width = shell`.

Both windows are intersected with the honest same-rank accepted-creation
window before their coordinate masses are compared.  Thus the saturation of
natural subtraction at shell zero is harmless: inadmissible values never
enter the conditional screen.
-/

open MeasureTheory Set
open scoped ENNReal

namespace Erdos1165.HLOZAllCreationCofinalPhysicalInterface

open CappedCoordinateMassCertificate FiniteDominoProductLaw
open HLOZAllCreationCofinalConditionalSharpWindow
open HLOZAllSixExactCoordinateProductClosure
open HLOZConditionalTruncatedRandomTotalProductBound
open HLOZPathEvents HLOZPositiveInterfacePhysicalWindows
open HLOZProposition48Candidates
open HLOZSharpProductNumerics
open LazyDecomposition ScreeningInstantiation
open TilingCappedMarginalization TilingConditionalCappedMarginalization
open TilingOrientedAllCreationConcreteFamily
open TilingOrientedAllCreationStoppedCoordinate
open TilingOrientedSupportAwayCoordinates
open TilingSpatialInsertionFiber
open VariableStoppedTracePartition

noncomputable section

abbrev DominoTiling := Tilings.Tiling

/-- Literal conditional product data for two adjacent *physical* deficit
shells on one accepted all-creation stopped fibre.  All path reconstruction
is contained in `refinement`; the only analytic field is the explicit
one-coordinate comparison after intersecting with the accepted base window.
-/
structure OrientedAllCreationConditionalPhysicalInterfaceTailData
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    {supportAt : WalkPath → ℕ → Finset Point} {S : Finset Point}
    {z : OrientedAllCreationTraceCode t}
    (fiber : OrientedAllCreationPrefixedStoppedCoordinateSpec
      t o m k supportAt S z)
    (piece next : Set WalkPath) (threshold : ℕ → ℕ)
    (width shell bound : ℕ) where
  refinement : OrientedAllCreationConditionalRefinementData
    fiber piece next 1
  capStart : ℕ
  baseWindow : ∀ cap,
    TilingAwayDomino t (fiber.start cap) (fiber.retained cap)
      (fiber.distinguished cap) → Finset ℕ
  baseAccepts_iff : ∀ cap ell,
    refinement.baseAccepts cap ell = true ↔
      ∀ b, (ell b : ℕ) ∈ baseWindow cap b
  screenedAccepts_iff : ∀ cap ell,
    refinement.screenedAccepts cap ell = true ↔
      (∀ b, (ell b : ℕ) ∈ baseWindow cap b) ∧
        allCreationRandomTotalThresholdedUpperTail fiber cap
          (fun b (v : Fin (fiber.upper cap b)) ↦
            (v : ℕ) ∈ physicalDeficitFailureWindow m width
              (Fintype.card (TilingCoordinatesAt t (fiber.start cap)
                (fiber.retained cap) b.1)) (shell + 1))
          (fun b (v : Fin (fiber.upper cap b)) ↦
            (v : ℕ) ∈ physicalDeficitFailureWindow m width
              (Fintype.card (TilingCoordinatesAt t (fiber.start cap)
                (fiber.retained cap) b.1)) shell)
          threshold shellGrowth48 shell bound ell
  baseLocalPos : ∀ cap, capStart ≤ cap → ∀ b,
    0 < ∑ v : Fin (fiber.upper cap b),
      if (v : ℕ) ∈ baseWindow cap b then
        coordinateMass
          (tilingAwayPointMass (cap := fiber.coordinateCap cap) t
            (fiber.start cap) (fiber.retained cap)
            (fiber.distinguished cap))
          (fiber.upper cap) b v else 0
  window_ratio_inter_base : ∀ cap, capStart ≤ cap →
    ∀ (b : TilingAwayDomino t (fiber.start cap) (fiber.retained cap)
      (fiber.distinguished cap)),
    (∑ v : Fin (fiber.upper cap b),
      if (v : ℕ) ∈ physicalDeficitFailureWindow m width
            (Fintype.card (TilingCoordinatesAt t (fiber.start cap)
              (fiber.retained cap) b.1)) (shell + 1) ∧
          (v : ℕ) ∈ baseWindow cap b then
        coordinateMass
          (tilingAwayPointMass (cap := fiber.coordinateCap cap) t
            (fiber.start cap) (fiber.retained cap)
            (fiber.distinguished cap))
          (fiber.upper cap) b v else 0) ≤
      (4 / 3 : ℝ) *
        ∑ v : Fin (fiber.upper cap b),
          if (v : ℕ) ∈ physicalDeficitFailureWindow m width
                (Fintype.card (TilingCoordinatesAt t (fiber.start cap)
                  (fiber.retained cap) b.1)) shell ∧
              (v : ℕ) ∈ baseWindow cap b then
            coordinateMass
              (tilingAwayPointMass (cap := fiber.coordinateCap cap) t
                (fiber.start cap) (fiber.retained cap)
                (fiber.distinguished cap))
              (fiber.upper cap) b v else 0

namespace OrientedAllCreationConditionalPhysicalInterfaceTailData

/-- The exact physical adjacent-shell product has the same aggregate
`sharpInterfaceCost` once the checked local `4/3` comparison is available.
-/
theorem cofinal_product_bound_at_cap
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    {supportAt : WalkPath → ℕ → Finset Point} {S : Finset Point}
    {z : OrientedAllCreationTraceCode t}
    {fiber : OrientedAllCreationPrefixedStoppedCoordinateSpec
      t o m k supportAt S z}
    {piece next : Set WalkPath} {threshold : ℕ → ℕ}
    {width shell bound : ℕ}
    (data : OrientedAllCreationConditionalPhysicalInterfaceTailData
      fiber piece next threshold width shell bound) (cap : ℕ)
    (hcap : data.capStart ≤ cap) :
    allCreationBoolConditionalScreenMass fiber
        data.refinement.baseAccepts data.refinement.screenedAccepts cap ≤
      (ENNReal.ofReal (sharpInterfaceCost threshold shell)).toReal := by
  classical
  let upperWindow := fun
      (b : TilingAwayDomino t (fiber.start cap) (fiber.retained cap)
        (fiber.distinguished cap))
      (v : Fin (fiber.upper cap b)) ↦
    (v : ℕ) ∈ physicalDeficitFailureWindow m width
      (Fintype.card (TilingCoordinatesAt t (fiber.start cap)
        (fiber.retained cap) b.1)) (shell + 1)
  let lowerWindow := fun
      (b : TilingAwayDomino t (fiber.start cap) (fiber.retained cap)
        (fiber.distinguished cap))
      (v : Fin (fiber.upper cap b)) ↦
    (v : ℕ) ∈ physicalDeficitFailureWindow m width
      (Fintype.card (TilingCoordinatesAt t (fiber.start cap)
        (fiber.retained cap) b.1)) shell
  let baseWindow := fun
      (b : TilingAwayDomino t (fiber.start cap) (fiber.retained cap)
        (fiber.distinguished cap))
      (v : Fin (fiber.upper cap b)) ↦
    (v : ℕ) ∈ data.baseWindow cap b
  let pointMass := tilingAwayPointMass
    (cap := fiber.coordinateCap cap) t (fiber.start cap)
      (fiber.retained cap) (fiber.distinguished cap)
  rw [ENNReal.toReal_ofReal (sharpInterfaceCost_nonneg threshold shell)]
  unfold allCreationBoolConditionalScreenMass
  apply @conditionalScreenMass_randomTotalThresholdedUpperTail_inter_base_le_of_iff
    (TilingAwayDomino t (fiber.start cap) (fiber.retained cap)
      (fiber.distinguished cap))
    (instFintypeTilingAwayDomino t (fiber.start cap) (fiber.retained cap)
      (fiber.distinguished cap))
    (fun a b ↦ Subtype.instDecidableEq a b)
    pointMass (fiber.upper cap)
    baseWindow upperWindow lowerWindow inferInstance inferInstance
      inferInstance threshold shellGrowth48 shell bound
    (fun ell ↦ data.refinement.baseAccepts cap ell = true)
    (fun ell ↦ data.refinement.screenedAccepts cap ell = true)
    (fun ell ↦ instDecidableEqBool
      (data.refinement.baseAccepts cap ell) true)
    (fun ell ↦ instDecidableEqBool
      (data.refinement.screenedAccepts cap ell) true)
    (C := (4 / 3 : ℝ))
    (K := sharpInterfaceCost threshold shell)
  · intro ell
    exact data.baseAccepts_iff cap ell
  · intro ell
    simpa only [allCreationRandomTotalThresholdedUpperTail] using
      data.screenedAccepts_iff cap ell
  · intro b v
    exact coordinateMass_nonneg_of_pointMass_nonneg _ _
      (fun b' ell ↦ tilingAwayExactTotalMass_nonneg t
        (fiber.start cap) (fiber.retained cap)
        (fiber.distinguished cap) b' ell) b v
  · exact fun b ↦ data.baseLocalPos cap hcap b
  · intro b v hv
    exact Finset.disjoint_left.mp
      (physicalAdjacentFailureWindows_disjoint
        (m := m) (width := width)
        (i := Fintype.card (TilingCoordinatesAt t
          (fiber.start cap) (fiber.retained cap) b.1))
        (shell := shell)) hv.1 hv.2
  · norm_num
  · exact sharpInterfaceCost_nonneg threshold shell
  · exact fun b ↦ data.window_ratio_inter_base cap hcap b
  · exact fun total _ ↦
      thresholdedProductEnvelope_le_sharpInterfaceCost
        (4 / 3) (by norm_num) four_thirds_le_positiveInterfaceRatioConstant
          threshold shell total

/-- Forget the physical-window implementation after deriving its cofinal
conditional product estimate. -/
noncomputable def toCofinalData
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    {supportAt : WalkPath → ℕ → Finset Point} {S : Finset Point}
    {z : OrientedAllCreationTraceCode t}
    {fiber : OrientedAllCreationPrefixedStoppedCoordinateSpec
      t o m k supportAt S z}
    {piece next : Set WalkPath} {threshold : ℕ → ℕ}
    {width shell bound : ℕ}
    (data : OrientedAllCreationConditionalPhysicalInterfaceTailData
      fiber piece next threshold width shell bound) :
    OrientedAllCreationCofinalConditionalSharpWindowData fiber piece next
      (ENNReal.ofReal (sharpInterfaceCost threshold shell)) where
  refinement := data.refinement
  capStart := data.capStart
  cofinal_product_bound := fun cap hcap ↦
    data.cofinal_product_bound_at_cap cap hcap

end OrientedAllCreationConditionalPhysicalInterfaceTailData

end

end Erdos1165.HLOZAllCreationCofinalPhysicalInterface
