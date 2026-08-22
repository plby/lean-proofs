/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.HLOZAllCreationCofinalConditionalSharpWindow
import ErdosProblems.Erdos1165.HLOZPrefixedAllCreationCanonicalRefinement

/-!
# Prefix-correct aggregate sharp tails on all-creation atoms

This module is separate from the one-coordinate Proposition 4.9 screen.
Given a prefix-correct conditional refinement whose numerator is the
aggregate random-total tail, it derives broad coordinate positivity and the
local `4/3` comparison from the literal negative-binomial coordinate law.
-/

open MeasureTheory Set
open scoped ENNReal BigOperators

namespace Erdos1165.HLOZPrefixedAllCreationAggregateSharpTail

open FiniteDominoProductLaw
open HLOZAllCreationCofinalConditionalSharpWindow
open HLOZAllCreationCofinalConditionalSharpWindow.OrientedAllCreationConditionalSharpTailData
open HLOZAllSixExactCoordinateProductClosure
open HLOZProposition48Candidates
open HLOZSharpProductNumerics HLOZSharpWindowProductClosure
open LazyDecomposition ScreeningInstantiation SmallWindow
open TilingAwayNegativeBinomial TilingCappedMarginalization
open TilingConditionalCappedMarginalization
open TilingOrientedAllCreationStoppedCoordinate
open TilingOrientedSupportAwayCoordinates
open Erdos1165.TilingOrientedShellZeroSourcePartition
open TilingSpatialInsertionFiber VariableStoppedTracePartition

noncomputable section

abbrev DominoTiling := Tilings.Tiling

/-- Exact local data for the conditional aggregate interface.  The base and
screened identities are semantic equalities; the remaining fields are
deterministic one-coordinate containment and truncation facts. -/
structure CofinalLocalWindowData
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
  active : ∀ cap, capStart ≤ cap → ∀
      (b : TilingAwayDomino t (fiber.start cap) (fiber.retained cap)
        (fiber.distinguished cap)),
    m / 2 ≤ Fintype.card (TilingCoordinatesAt t (fiber.start cap)
      (fiber.retained cap) b.1)
  upper_mem_base : ∀ cap, capStart ≤ cap → ∀ b
      (v : Fin (fiber.upper cap b)),
    (v : ℕ) ∈ activeUpperFailureWindow m
        (Fintype.card (TilingCoordinatesAt t (fiber.start cap)
          (fiber.retained cap) b.1)) →
      (v : ℕ) ∈ baseWindow cap b
  lower_mem_base : ∀ cap, capStart ≤ cap → ∀ b
      (v : Fin (fiber.upper cap b)),
    (v : ℕ) ∈ activeLowerFailureWindow m
        (Fintype.card (TilingCoordinatesAt t (fiber.start cap)
          (fiber.retained cap) b.1)) →
      (v : ℕ) ∈ baseWindow cap b
  upper_lt_truncation : ∀ cap, capStart ≤ cap → ∀
      (b : TilingAwayDomino t (fiber.start cap) (fiber.retained cap)
        (fiber.distinguished cap)) v,
    v ∈ activeUpperFailureWindow m
        (Fintype.card (TilingCoordinatesAt t (fiber.start cap)
          (fiber.retained cap) b.1)) → v < fiber.upper cap b
  lower_lt_truncation : ∀ cap, capStart ≤ cap → ∀
      (b : TilingAwayDomino t (fiber.start cap) (fiber.retained cap)
        (fiber.distinguished cap)) v,
    v ∈ activeLowerFailureWindow m
        (Fintype.card (TilingCoordinatesAt t (fiber.start cap)
          (fiber.retained cap) b.1)) → v < fiber.upper cap b
  upper_le_cap : ∀ cap, capStart ≤ cap → ∀
      (b : TilingAwayDomino t (fiber.start cap) (fiber.retained cap)
        (fiber.distinguished cap)) v,
    v ∈ activeUpperFailureWindow m
        (Fintype.card (TilingCoordinatesAt t (fiber.start cap)
          (fiber.retained cap) b.1)) → v ≤ fiber.coordinateCap cap
  lower_le_cap : ∀ cap, capStart ≤ cap → ∀
      (b : TilingAwayDomino t (fiber.start cap) (fiber.retained cap)
        (fiber.distinguished cap)) v,
    v ∈ activeLowerFailureWindow m
        (Fintype.card (TilingCoordinatesAt t (fiber.start cap)
          (fiber.retained cap) b.1)) → v ≤ fiber.coordinateCap cap

namespace CofinalLocalWindowData

variable
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    {supportAt : WalkPath → ℕ → Finset Point} {S : Finset Point}
    {z : OrientedAllCreationTraceCode t}
    {fiber : OrientedAllCreationPrefixedStoppedCoordinateSpec
      t o m k supportAt S z}
    {piece next : Set WalkPath} {threshold : ℕ → ℕ}
    {shell bound : ℕ}

/-- The active lower window has positive normalized coordinate mass. -/
theorem lowerCoordinateMass_pos
    (harith : SharpWindowArithmeticAt m)
    (data : CofinalLocalWindowData fiber piece next threshold shell bound)
    (cap : ℕ) (hcap : data.capStart ≤ cap)
    (b : TilingAwayDomino t (fiber.start cap) (fiber.retained cap)
      (fiber.distinguished cap)) :
    0 < ∑ v : Fin (fiber.upper cap b),
      if (v : ℕ) ∈ activeLowerFailureWindow m
          (Fintype.card (TilingCoordinatesAt t (fiber.start cap)
            (fiber.retained cap) b.1)) then
        coordinateMass
          (tilingAwayPointMass (cap := fiber.coordinateCap cap) t
            (fiber.start cap) (fiber.retained cap)
          (fiber.distinguished cap))
          (fiber.upper cap) b v else 0 := by
  let i := Fintype.card (TilingCoordinatesAt t (fiber.start cap)
    (fiber.retained cap) b.1)
  have hi : m / 2 ≤ i := data.active cap hcap b
  have hiPos : 0 < i := (harith.2 i hi).1
  have hwindowPos : 0 < windowMass i (activeLowerFailureWindow m i) := by
    rw [activeLowerFailureWindow_eq_of_active hi]
    exact windowMass_pos hiPos (lowerFailureWindow_nonempty harith.1)
  have hdenPos : 0 < ∑ j : Fin (fiber.upper cap b),
      tilingAwayPointMass (cap := fiber.coordinateCap cap) t
        (fiber.start cap) (fiber.retained cap)
        (fiber.distinguished cap) b j := by
    let v0 : Fin (fiber.upper cap b) := ⟨0, fiber.upper_pos cap b⟩
    have hv0 : 0 < tilingAwayPointMass (cap := fiber.coordinateCap cap) t
        (fiber.start cap) (fiber.retained cap)
        (fiber.distinguished cap) b v0 := by
      simpa only [v0, tilingAwayPointMass] using
        tilingAwayExactTotalMass_zero_pos (cap := fiber.coordinateCap cap)
          t (fiber.start cap) (fiber.retained cap)
          (fiber.distinguished cap) b
    exact hv0.trans_le (Finset.single_le_sum
      (s := Finset.univ)
      (f := fun j : Fin (fiber.upper cap b) ↦
        tilingAwayPointMass (cap := fiber.coordinateCap cap) t
          (fiber.start cap) (fiber.retained cap)
          (fiber.distinguished cap) b j)
      (fun j _ ↦ tilingAwayExactTotalMass_nonneg t
        (fiber.start cap) (fiber.retained cap)
        (fiber.distinguished cap) b j)
      (Finset.mem_univ v0))
  have heq := sum_tilingAway_coordinateMass_window t (fiber.start cap)
    (fiber.retained cap) (fiber.distinguished cap) (fiber.upper cap) b
    (activeLowerFailureWindow m i)
    (data.lower_lt_truncation cap hcap b)
    (data.lower_le_cap cap hcap b) hiPos
  exact heq.symm ▸ div_pos hwindowPos hdenPos

/-- Positivity of the honest broad coordinate normalizer follows from the
contained active lower window. -/
theorem baseLocalPos
    (harith : SharpWindowArithmeticAt m)
    (data : CofinalLocalWindowData fiber piece next threshold shell bound)
    (cap : ℕ) (hcap : data.capStart ≤ cap)
    (b : TilingAwayDomino t (fiber.start cap) (fiber.retained cap)
      (fiber.distinguished cap)) :
    0 < ∑ v : Fin (fiber.upper cap b),
      if (v : ℕ) ∈ data.baseWindow cap b then
        coordinateMass
          (tilingAwayPointMass (cap := fiber.coordinateCap cap) t
            (fiber.start cap) (fiber.retained cap)
            (fiber.distinguished cap))
          (fiber.upper cap) b v else 0 := by
  apply (data.lowerCoordinateMass_pos harith cap hcap b).trans_le
  apply Finset.sum_le_sum
  intro v _hv
  by_cases hlower : (v : ℕ) ∈ activeLowerFailureWindow m
      (Fintype.card (TilingCoordinatesAt t (fiber.start cap)
        (fiber.retained cap) b.1))
  · rw [if_pos hlower, if_pos (data.lower_mem_base cap hcap b v hlower)]
  · rw [if_neg hlower]
    split
    · exact allCreationCoordinateMass_nonneg cap b v
    · exact le_rfl

/-- The literal capped negative-binomial law inherits the checked local
`4/3` adjacent-window comparison. -/
theorem window_ratio
    (harith : SharpWindowArithmeticAt m)
    (data : CofinalLocalWindowData fiber piece next threshold shell bound)
    (cap : ℕ) (hcap : data.capStart ≤ cap)
    (b : TilingAwayDomino t (fiber.start cap) (fiber.retained cap)
      (fiber.distinguished cap)) :
    (∑ v : Fin (fiber.upper cap b),
      if (v : ℕ) ∈ activeUpperFailureWindow m
          (Fintype.card (TilingCoordinatesAt t (fiber.start cap)
            (fiber.retained cap) b.1)) then
        coordinateMass
          (tilingAwayPointMass (cap := fiber.coordinateCap cap) t
            (fiber.start cap) (fiber.retained cap)
            (fiber.distinguished cap))
          (fiber.upper cap) b v else 0) ≤
      (4 / 3 : ℝ) *
        ∑ v : Fin (fiber.upper cap b),
          if (v : ℕ) ∈ activeLowerFailureWindow m
              (Fintype.card (TilingCoordinatesAt t (fiber.start cap)
                (fiber.retained cap) b.1)) then
            coordinateMass
              (tilingAwayPointMass (cap := fiber.coordinateCap cap) t
                (fiber.start cap) (fiber.retained cap)
                (fiber.distinguished cap))
              (fiber.upper cap) b v else 0 := by
  let i := Fintype.card (TilingCoordinatesAt t (fiber.start cap)
    (fiber.retained cap) b.1)
  have hi : m / 2 ≤ i := data.active cap hcap b
  have hiFacts := harith.2 i hi
  change
    (∑ v : Fin (fiber.upper cap b),
      if (v : ℕ) ∈ activeUpperFailureWindow m i then
        coordinateMass
          (tilingAwayPointMass (cap := fiber.coordinateCap cap) t
            (fiber.start cap) (fiber.retained cap)
            (fiber.distinguished cap))
          (fiber.upper cap) b v else 0) ≤
      (4 / 3 : ℝ) * ∑ v : Fin (fiber.upper cap b),
        if (v : ℕ) ∈ activeLowerFailureWindow m i then
          coordinateMass
            (tilingAwayPointMass (cap := fiber.coordinateCap cap) t
              (fiber.start cap) (fiber.retained cap)
              (fiber.distinguished cap))
            (fiber.upper cap) b v else 0
  rw [activeUpperFailureWindow_eq_of_active hi,
    activeLowerFailureWindow_eq_of_active hi]
  refine (tilingAway_coordinateMass_window_ratio_of_localCLT t
    (fiber.start cap) (fiber.retained cap) (fiber.distinguished cap)
    (fiber.upper cap) b
    (upperFailureWindow i (HLOZProposition48Candidates.shellWidth48 m))
    (lowerFailureWindow i (HLOZProposition48Candidates.shellWidth48 m))
    (fun v hv ↦ data.upper_lt_truncation cap hcap b v (by
      rw [activeUpperFailureWindow_eq_of_active hi]
      exact hv))
    (fun v hv ↦ data.lower_lt_truncation cap hcap b v (by
      rw [activeLowerFailureWindow_eq_of_active hi]
      exact hv))
    (fun v hv ↦ data.upper_le_cap cap hcap b v (by
      rw [activeUpperFailureWindow_eq_of_active hi]
      exact hv))
    (fun v hv ↦ data.lower_le_cap cap hcap b v (by
      rw [activeLowerFailureWindow_eq_of_active hi]
      exact hv))
    hiFacts.1 (adjacentWindowRadius_nonneg _)
    (adjacentWindowSeparation_nonneg _) hiFacts.2.1
    (lowerFailureWindow_nonempty harith.1) (by simp)
    (fun _ hv ↦ upperFailureWindow_deviation_le hv)
    (fun _ hv ↦ lowerFailureWindow_deviation_le hv)
    (fun _ hu _ hl ↦ adjacentFailureWindow_deviation_sub_le hu hl)).trans ?_
  apply mul_le_mul_of_nonneg_right hiFacts.2.2
  exact Finset.sum_nonneg fun v _ ↦ by
    split
    · exact allCreationCoordinateMass_nonneg cap b v
    · exact le_rfl

/-- Smallest cofinal aggregate constructor.  The aggregate product estimate
is subsequently derived by `toCofinalData`; it is not a premise here. -/
noncomputable def toConditionalSharpTailData
    (harith : SharpWindowArithmeticAt m)
    (data : CofinalLocalWindowData fiber piece next threshold shell bound) :
    OrientedAllCreationConditionalSharpTailData fiber piece next
      threshold shell bound where
  refinement := data.refinement
  capStart := data.capStart
  baseWindow := data.baseWindow
  baseAccepts_iff := data.baseAccepts_iff
  screenedAccepts_iff := data.screenedAccepts_iff
  baseLocalPos := fun cap hcap b ↦ data.baseLocalPos harith cap hcap b
  upper_mem_base := data.upper_mem_base
  lower_mem_base := data.lower_mem_base
  window_ratio := fun cap hcap b ↦ data.window_ratio harith cap hcap b

/-- Direct cofinal certificate obtained without a product-bound premise. -/
noncomputable def toCofinalData
    (harith : SharpWindowArithmeticAt m)
    (data : CofinalLocalWindowData fiber piece next threshold shell bound) :
    OrientedAllCreationCofinalConditionalSharpWindowData fiber piece next
      (ENNReal.ofReal (sharpInterfaceCost threshold shell)) :=
  (data.toConditionalSharpTailData harith).toCofinalData

end CofinalLocalWindowData

end

end Erdos1165.HLOZPrefixedAllCreationAggregateSharpTail
