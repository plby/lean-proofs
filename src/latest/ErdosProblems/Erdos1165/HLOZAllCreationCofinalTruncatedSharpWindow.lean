/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.HLOZAllCreationCofinalConditionalSharpWindow
import ErdosProblems.Erdos1165.HLOZConditionalTruncatedRandomTotalProductBound

/-!
# Cofinal conditional sharp tails with accepted-window truncation

The canonical adjacent failure windows need not lie wholly inside the
same-rank accepted creation window.  This corrected cofinal constructor uses
their intersections with the coordinatewise base window.  It retains the
same path-facing interface and sharp global cost.
-/

open MeasureTheory Set
open scoped ENNReal

namespace Erdos1165.HLOZAllCreationCofinalTruncatedSharpWindow

open FiniteDominoProductLaw
open HLOZAllCreationCofinalConditionalSharpWindow
open HLOZAllCreationCofinalConditionalSharpWindow.OrientedAllCreationConditionalSharpTailData
open HLOZConditionalTruncatedRandomTotalProductBound
open HLOZPathEvents HLOZSharpProductNumerics
open HLOZProposition48Candidates
open HLOZSharpWindowProductClosure
open LazyDecomposition ScreeningInstantiation
open TilingCappedMarginalization TilingConditionalCappedMarginalization
open TilingOrientedAllCreationConcreteFamily
open TilingOrientedAllCreationStoppedCoordinate
open TilingOrientedSupportAwayCoordinates
open TilingSpatialInsertionFiber
open VariableStoppedTracePartition

noncomputable section

abbrev DominoTiling := Tilings.Tiling

/-- Literal conditional sharp-tail data after intersecting both canonical
windows with the honest coordinatewise creation window. -/
structure OrientedAllCreationConditionalTruncatedSharpTailData
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    {supportAt : WalkPath → ℕ → Finset Point} {S : Finset Point}
    {z : OrientedAllCreationTraceCode t}
    (fiber : OrientedAllCreationPrefixedStoppedCoordinateSpec
      t o m k supportAt S z)
    (piece next : Set WalkPath) (threshold : ℕ → ℕ)
    (shell bound : ℕ) where
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
            (v : ℕ) ∈ activeUpperFailureWindow m
              (Fintype.card (TilingCoordinatesAt t (fiber.start cap)
                (fiber.retained cap) b.1)))
          (fun b (v : Fin (fiber.upper cap b)) ↦
            (v : ℕ) ∈ activeLowerFailureWindow m
              (Fintype.card (TilingCoordinatesAt t (fiber.start cap)
                (fiber.retained cap) b.1)))
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
      if (v : ℕ) ∈ activeUpperFailureWindow m
          (Fintype.card (TilingCoordinatesAt t (fiber.start cap)
            (fiber.retained cap) b.1)) ∧
          (v : ℕ) ∈ baseWindow cap b then
        coordinateMass
          (tilingAwayPointMass (cap := fiber.coordinateCap cap) t
            (fiber.start cap) (fiber.retained cap)
            (fiber.distinguished cap))
          (fiber.upper cap) b v else 0) ≤
      (4 / 3 : ℝ) *
        ∑ v : Fin (fiber.upper cap b),
          if (v : ℕ) ∈ activeLowerFailureWindow m
              (Fintype.card (TilingCoordinatesAt t (fiber.start cap)
                (fiber.retained cap) b.1)) ∧
              (v : ℕ) ∈ baseWindow cap b then
            coordinateMass
              (tilingAwayPointMass (cap := fiber.coordinateCap cap) t
                (fiber.start cap) (fiber.retained cap)
                (fiber.distinguished cap))
              (fiber.upper cap) b v else 0

namespace OrientedAllCreationConditionalTruncatedSharpTailData

/-- Construct the corrected cofinal sharp bound at one cap. -/
theorem cofinal_product_bound_at_cap
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    {supportAt : WalkPath → ℕ → Finset Point} {S : Finset Point}
    {z : OrientedAllCreationTraceCode t}
    {fiber : OrientedAllCreationPrefixedStoppedCoordinateSpec
      t o m k supportAt S z}
    {piece next : Set WalkPath} {threshold : ℕ → ℕ}
    {shell bound : ℕ}
    (data : OrientedAllCreationConditionalTruncatedSharpTailData
      fiber piece next threshold shell bound) (cap : ℕ)
    (hcap : data.capStart ≤ cap) :
    allCreationBoolConditionalScreenMass fiber
        data.refinement.baseAccepts data.refinement.screenedAccepts cap ≤
      (ENNReal.ofReal (sharpInterfaceCost threshold shell)).toReal := by
  classical
  let upperWindow := fun
      (b : TilingAwayDomino t (fiber.start cap) (fiber.retained cap)
        (fiber.distinguished cap))
      (v : Fin (fiber.upper cap b)) ↦
    (v : ℕ) ∈ activeUpperFailureWindow m
      (Fintype.card (TilingCoordinatesAt t (fiber.start cap)
        (fiber.retained cap) b.1))
  let lowerWindow := fun
      (b : TilingAwayDomino t (fiber.start cap) (fiber.retained cap)
        (fiber.distinguished cap))
      (v : Fin (fiber.upper cap b)) ↦
    (v : ℕ) ∈ activeLowerFailureWindow m
      (Fintype.card (TilingCoordinatesAt t (fiber.start cap)
        (fiber.retained cap) b.1))
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
  · exact allCreationCoordinateMass_nonneg cap
  · exact fun b ↦ data.baseLocalPos cap hcap b
  · intro b v hv
    exact activeFailureWindows_disjoint m
        (Fintype.card (TilingCoordinatesAt t (fiber.start cap)
          (fiber.retained cap) b.1)) (fiber.upper cap b) v hv
  · norm_num
  · exact sharpInterfaceCost_nonneg threshold shell
  · exact fun b ↦ data.window_ratio_inter_base cap hcap b
  · exact fun total _ ↦
      thresholdedProductEnvelope_le_sharpInterfaceCost
        (4 / 3) (by norm_num) four_thirds_le_positiveInterfaceRatioConstant
          threshold shell total

/-- Forget the truncated-window implementation after deriving its sharp
cofinal product estimate. -/
noncomputable def toCofinalData
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    {supportAt : WalkPath → ℕ → Finset Point} {S : Finset Point}
    {z : OrientedAllCreationTraceCode t}
    {fiber : OrientedAllCreationPrefixedStoppedCoordinateSpec
      t o m k supportAt S z}
    {piece next : Set WalkPath} {threshold : ℕ → ℕ}
    {shell bound : ℕ}
    (data : OrientedAllCreationConditionalTruncatedSharpTailData
      fiber piece next threshold shell bound) :
    OrientedAllCreationCofinalConditionalSharpWindowData fiber piece next
      (ENNReal.ofReal (sharpInterfaceCost threshold shell)) where
  refinement := data.refinement
  capStart := data.capStart
  cofinal_product_bound := fun cap hcap ↦
    data.cofinal_product_bound_at_cap cap hcap

end OrientedAllCreationConditionalTruncatedSharpTailData

end

end Erdos1165.HLOZAllCreationCofinalTruncatedSharpWindow
