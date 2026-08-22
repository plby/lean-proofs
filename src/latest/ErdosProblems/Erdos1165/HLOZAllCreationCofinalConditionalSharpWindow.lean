/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors.
-/

import ErdosProblems.Erdos1165.HLOZCofinalSharpWindowProductClosure
import ErdosProblems.Erdos1165.HLOZConditionalRandomTotalProductBound
import ErdosProblems.Erdos1165.HLOZAllSixExactCoordinateProductClosure
import ErdosProblems.Erdos1165.TilingOrientedAllCreationConcreteFamily

/-!
# Cofinal conditional sharp windows on physical-prefix creation fibres

The reusable all-creation fibre has a physical initial prefix and an affine
actual-coordinate cap.  Moreover, genuine creation acceptance is a
nontrivial broad away-total condition.  It therefore cannot be coerced into
the old origin-start, unconditional `TilingFactoredStoppedCoordinateData`.

This module supplies the source-correct interface.  Exact prefixed
broad/screened factorization gives a finite-cap conditional product law.  Its
automatic bound by one constructs the raw capped certificate at every cap;
the sharp conditional estimate is required only on a cofinal range.  Cap
removal then gives the same atomwise transition bound as the legacy sharp
interface without asserting anything at cap zero.
-/

open MeasureTheory Set
open scoped ENNReal

namespace Erdos1165.HLOZAllCreationCofinalConditionalSharpWindow

open CappedCoordinateMassCertificate FiniteDominoProductLaw
open HLOZAllSixBandProductClosure HLOZSharpWindowProductClosure
open HLOZAllSixExactCoordinateProductClosure
open HLOZCofinalSharpWindowProductClosure HLOZPathEvents HLOZSpatialAdapter
open HLOZConditionalRandomTotalProductBound
open HLOZSharpProductNumerics HLOZProposition48Candidates
open LazyDecomposition PreStoppingConditionalLaw
open ScreeningInstantiation TilingCappedMarginalization
open TilingConditionalCappedMarginalization
open TilingOrientedAllCreationConcreteFamily
open TilingOrientedAllCreationStoppedCoordinate
open TilingOrientedSupportAwayCoordinates
open Erdos1165.TilingOrientedShellZeroSourcePartition
open TilingPrefixedConditionalCappedMarginalization
open TilingSpatialInsertionFiber
open VariableStoppedTracePartition

noncomputable section

abbrev DominoTiling := Tilings.Tiling

/-- Aggregate sharp-tail predicate with the same explicit away-domino
`Fintype` instance used by `allCreationBoolConditionalScreenMass`.  Fixing
this instance prevents elaboration from choosing a propositionally equal but
definitionally different subtype enumeration. -/
def allCreationRandomTotalThresholdedUpperTail
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    {supportAt : WalkPath → ℕ → Finset Point} {S : Finset Point}
    {z : OrientedAllCreationTraceCode t}
    (fiber : OrientedAllCreationPrefixedStoppedCoordinateSpec
      t o m k supportAt S z) (cap : ℕ)
    (upperWindow lowerWindow : ∀
      b : TilingAwayDomino t (fiber.start cap) (fiber.retained cap)
        (fiber.distinguished cap), Fin (fiber.upper cap b) → Prop)
    [∀ b, DecidablePred (upperWindow b)]
    [∀ b, DecidablePred (lowerWindow b)]
    (threshold : ℕ → ℕ) (G shell bound : ℕ)
    (ell : TruncatedTotals (fiber.upper cap)) : Prop :=
  @randomTotalThresholdedUpperTail
    (TilingAwayDomino t (fiber.start cap) (fiber.retained cap)
      (fiber.distinguished cap))
    (instFintypeTilingAwayDomino t (fiber.start cap) (fiber.retained cap)
      (fiber.distinguished cap))
    (fun b ↦ Fin (fiber.upper cap b)) upperWindow lowerWindow inferInstance
      inferInstance threshold G shell bound ell

/-! ## Literal conditional sharp tail -/

/-- Deterministic coordinate data for the conditional positive-shell tail
on one physical-prefix all-creation atom.

The exact stopped-coordinate refinement carries recovery, monotonicity and
coverage.  This record adds only coordinatewise identities and the checked
one-coordinate ratio.  In particular, it has no product-bound or event-
probability field. -/
structure OrientedAllCreationConditionalSharpTailData
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
  upper_mem_base : ∀ cap, capStart ≤ cap → ∀ b (v : Fin (fiber.upper cap b)),
    (v : ℕ) ∈ activeUpperFailureWindow m
        (Fintype.card (TilingCoordinatesAt t (fiber.start cap)
          (fiber.retained cap) b.1)) →
      (v : ℕ) ∈ baseWindow cap b
  lower_mem_base : ∀ cap, capStart ≤ cap → ∀ b (v : Fin (fiber.upper cap b)),
    (v : ℕ) ∈ activeLowerFailureWindow m
        (Fintype.card (TilingCoordinatesAt t (fiber.start cap)
          (fiber.retained cap) b.1)) →
      (v : ℕ) ∈ baseWindow cap b
  window_ratio : ∀ cap, capStart ≤ cap →
    ∀ (b : TilingAwayDomino t (fiber.start cap) (fiber.retained cap)
      (fiber.distinguished cap)),
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
              (fiber.upper cap) b v else 0

/-- One honest prefixed conditional screen with a sharp bound required only
above a logical cap start.

`refinement` contains the two direct coordinate identities.  Its harmless
finite-cap cost is one.  `cofinal_product_bound` is the sole remaining sharp
coordinate inequality; importantly, it is conditional on the honest broad
creation screen rather than an away-independent fictitious base. -/
structure OrientedAllCreationCofinalConditionalSharpWindowData
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    {supportAt : WalkPath → ℕ → Finset Point} {S : Finset Point}
    {z : OrientedAllCreationTraceCode t}
    (fiber : OrientedAllCreationPrefixedStoppedCoordinateSpec
      t o m k supportAt S z)
    (piece next : Set WalkPath) (cost : ℝ≥0∞) where
  refinement : OrientedAllCreationConditionalRefinementData
    fiber piece next 1
  capStart : ℕ
  cofinal_product_bound : ∀ cap, capStart ≤ cap →
    allCreationBoolConditionalScreenMass fiber
      refinement.baseAccepts refinement.screenedAccepts cap ≤ cost.toReal

namespace OrientedAllCreationConditionalSharpTailData

/-- The exact away-coordinate masses on an all-creation fibre are
nonnegative. -/
theorem allCreationCoordinateMass_nonneg
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    {supportAt : WalkPath → ℕ → Finset Point} {S : Finset Point}
    {z : OrientedAllCreationTraceCode t}
    {fiber : OrientedAllCreationPrefixedStoppedCoordinateSpec
      t o m k supportAt S z}
    (cap : ℕ) : ∀ b (v : Fin (fiber.upper cap b)),
      0 ≤ coordinateMass
        (tilingAwayPointMass (cap := fiber.coordinateCap cap) t
          (fiber.start cap) (fiber.retained cap) (fiber.distinguished cap))
        (fiber.upper cap) b v := by
  intro b v
  exact coordinateMass_nonneg_of_pointMass_nonneg _ _
    (fun b' ell ↦ tilingAwayExactTotalMass_nonneg t
      (fiber.start cap) (fiber.retained cap)
      (fiber.distinguished cap) b' ell) b v

/-- The active upper and lower sharp windows are disjoint. -/
theorem activeFailureWindows_disjoint (m i upper : ℕ) (v : Fin upper) :
    ¬ ((v : ℕ) ∈ activeUpperFailureWindow m i ∧
      (v : ℕ) ∈ activeLowerFailureWindow m i) := by
  intro hv
  by_cases hi : m / 2 ≤ i
  · rw [activeUpperFailureWindow_eq_of_active hi,
      activeLowerFailureWindow_eq_of_active hi] at hv
    rw [upperFailureWindow, Finset.mem_Ico] at hv
    rw [lowerFailureWindow, Finset.mem_Ico] at hv
    omega
  · rw [activeUpperFailureWindow_eq_empty_of_inactive hi] at hv
    simp at hv

/-- Construct the cofinal sharp bound at one cap from deterministic recovery
and local coordinate comparisons. -/
theorem cofinal_product_bound_at_cap
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    {supportAt : WalkPath → ℕ → Finset Point} {S : Finset Point}
    {z : OrientedAllCreationTraceCode t}
    {fiber : OrientedAllCreationPrefixedStoppedCoordinateSpec
      t o m k supportAt S z}
    {piece next : Set WalkPath} {threshold : ℕ → ℕ}
    {shell bound : ℕ}
    (data : OrientedAllCreationConditionalSharpTailData
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
  have hdisjoint : ∀ b v, ¬ (upperWindow b v ∧ lowerWindow b v) := by
    intro b v
    exact activeFailureWindows_disjoint m
      (Fintype.card (TilingCoordinatesAt t (fiber.start cap)
        (fiber.retained cap) b.1)) (fiber.upper cap b) v
  rw [ENNReal.toReal_ofReal (sharpInterfaceCost_nonneg threshold shell)]
  unfold allCreationBoolConditionalScreenMass
  apply @conditionalScreenMass_randomTotalThresholdedUpperTail_le_of_iff
    (TilingAwayDomino t (fiber.start cap) (fiber.retained cap)
      (fiber.distinguished cap))
    (instFintypeTilingAwayDomino t (fiber.start cap) (fiber.retained cap)
      (fiber.distinguished cap))
    (fun a b ↦ Subtype.instDecidableEq a b)
    pointMass (fiber.upper cap) baseWindow upperWindow lowerWindow
    inferInstance inferInstance inferInstance threshold shellGrowth48 shell bound
    (fun ell ↦ data.refinement.baseAccepts cap ell = true)
    (fun ell ↦ data.refinement.screenedAccepts cap ell = true)
    (fun ell ↦ instDecidableEqBool (data.refinement.baseAccepts cap ell) true)
    (fun ell ↦ instDecidableEqBool
      (data.refinement.screenedAccepts cap ell) true)
    (C := (4 / 3 : ℝ)) (K := sharpInterfaceCost threshold shell)
  · intro ell
    exact data.baseAccepts_iff cap ell
  · intro ell
    simpa only [allCreationRandomTotalThresholdedUpperTail] using
      data.screenedAccepts_iff cap ell
  · exact allCreationCoordinateMass_nonneg cap
  · exact fun b ↦ data.baseLocalPos cap hcap b
  · exact fun b v hv ↦ data.upper_mem_base cap hcap b v hv
  · exact fun b v hv ↦ data.lower_mem_base cap hcap b v hv
  · exact hdisjoint
  · norm_num
  · exact sharpInterfaceCost_nonneg threshold shell
  · exact fun b ↦ data.window_ratio cap hcap b
  · exact fun total _ ↦
      thresholdedProductEnvelope_le_sharpInterfaceCost
        (4 / 3) (by norm_num) four_thirds_le_positiveInterfaceRatioConstant
          threshold shell total

/-- Construct the cofinal sharp certificate from deterministic recovery and
local coordinate comparisons.  The aggregate product estimate is derived by
normalizing each broad coordinate window and applying the random-total tail
bound to that restricted product. -/
theorem cofinal_product_bound_of_tailData
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    {supportAt : WalkPath → ℕ → Finset Point} {S : Finset Point}
    {z : OrientedAllCreationTraceCode t}
    {fiber : OrientedAllCreationPrefixedStoppedCoordinateSpec
      t o m k supportAt S z}
    {piece next : Set WalkPath} {threshold : ℕ → ℕ}
    {shell bound : ℕ}
    (data : OrientedAllCreationConditionalSharpTailData
      fiber piece next threshold shell bound) : ∀ cap, data.capStart ≤ cap →
    allCreationBoolConditionalScreenMass fiber
        data.refinement.baseAccepts data.refinement.screenedAccepts cap ≤
      (ENNReal.ofReal (sharpInterfaceCost threshold shell)).toReal := by
  intro cap _hcap
  exact cofinal_product_bound_at_cap data cap _hcap

/-- Package the derived cofinal product bound with the exact conditional
refinement. -/
noncomputable def toCofinalData
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    {supportAt : WalkPath → ℕ → Finset Point} {S : Finset Point}
    {z : OrientedAllCreationTraceCode t}
    {fiber : OrientedAllCreationPrefixedStoppedCoordinateSpec
      t o m k supportAt S z}
    {piece next : Set WalkPath} {threshold : ℕ → ℕ}
    {shell bound : ℕ}
    (data : OrientedAllCreationConditionalSharpTailData
      fiber piece next threshold shell bound) :
    OrientedAllCreationCofinalConditionalSharpWindowData fiber piece next
      (ENNReal.ofReal (sharpInterfaceCost threshold shell)) where
  refinement := data.refinement
  capStart := data.capStart
  cofinal_product_bound := cofinal_product_bound_of_tailData data

end OrientedAllCreationConditionalSharpTailData

namespace OrientedAllCreationCofinalConditionalSharpWindowData

/-- The exact prefixed finite-cap law, with the sharp estimate delayed to
the cofinal wrapper. -/
noncomputable def rawCertificate
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    {supportAt : WalkPath → ℕ → Finset Point} {S : Finset Point}
    {z : OrientedAllCreationTraceCode t}
    {fiber : OrientedAllCreationPrefixedStoppedCoordinateSpec
      t o m k supportAt S z}
    {piece next : Set WalkPath} {cost : ℝ≥0∞}
    (data : OrientedAllCreationCofinalConditionalSharpWindowData
      fiber piece next cost) :
    CappedProductScreenCertificate (fun _ : Unit ↦ piece) next 1 :=
  cappedProductScreenCertificateOfCoordinateMassSpec
    (coordinateMassSpecOfAllCreation fiber data.refinement)

/-- Package the preceding law with the large-cap sharp estimate. -/
noncomputable def cofinalCertificate
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    {supportAt : WalkPath → ℕ → Finset Point} {S : Finset Point}
    {z : OrientedAllCreationTraceCode t}
    {fiber : OrientedAllCreationPrefixedStoppedCoordinateSpec
      t o m k supportAt S z}
    {piece next : Set WalkPath} {cost : ℝ≥0∞}
    (data : OrientedAllCreationCofinalConditionalSharpWindowData
      fiber piece next cost) :
    CofinalCappedProductScreenCertificate (fun _ : Unit ↦ piece) next cost where
  raw := data.rawCertificate
  capStart := fun _ ↦ data.capStart
  product_bound := by
    intro _ cap hcap
    change allCreationBoolConditionalScreenMass fiber
      data.refinement.baseAccepts data.refinement.screenedAccepts cap ≤
        cost.toReal
    exact data.cofinal_product_bound cap hcap

/-- Cofinal cap removal on one exact all-creation atom. -/
theorem atomwiseRestrictedRealScreen
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    {supportAt : WalkPath → ℕ → Finset Point} {S : Finset Point}
    {z : OrientedAllCreationTraceCode t}
    {fiber : OrientedAllCreationPrefixedStoppedCoordinateSpec
      t o m k supportAt S z}
    {piece next : Set WalkPath} {cost : ℝ≥0∞}
    (data : OrientedAllCreationCofinalConditionalSharpWindowData
      fiber piece next cost) (hcost : cost ≠ ∞) :
    AtomwiseRestrictedRealScreen (fun _ : Unit ↦ piece) next cost :=
  atomwiseRestrictedRealScreen_of_cofinalCappedProductCertificate
    (fun _ : Unit ↦ piece) next cost hcost data.cofinalCertificate

/-- The relative transition estimate on one exact supported creation atom. -/
theorem measure_inter_next_le
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    {supportAt : WalkPath → ℕ → Finset Point} {S : Finset Point}
    {z : OrientedAllCreationTraceCode t}
    {fiber : OrientedAllCreationPrefixedStoppedCoordinateSpec
      t o m k supportAt S z}
    {piece next : Set WalkPath} {cost : ℝ≥0∞}
    (data : OrientedAllCreationCofinalConditionalSharpWindowData
      fiber piece next cost)
    (hnext : MeasurableSet next) (hcost : cost ≠ ∞) :
    simpleRandomWalk (piece ∩ next) ≤ cost * simpleRandomWalk piece := by
  have hlocal := pathTransitionDomination_of_atomwiseRestrictedRealScreen
    (fun _ : Unit ↦ piece) hnext hcost (data.atomwiseRestrictedRealScreen hcost)
  exact hlocal ()

end OrientedAllCreationCofinalConditionalSharpWindowData

/-! ## Countable supported-atom interface -/

/-- A whole positive-shell interface over the exact oriented all-creation
partition.  Every atom uses the same conditional sharp cost, but may have a
different physical prefix, cap schedule, and honest broad creation screen. -/
structure OrientedAllCreationCofinalSharpWindowInterfaceProductData
    (t : DominoTiling) (o : Orientation) (m k : ℕ)
    (next : Set WalkPath) (threshold : ℕ → ℕ) (shell bound : ℕ) where
  supportAt : WalkPath → ℕ → Finset Point
  supportData : OrientedAllCreationSupportSelectorData t o m k supportAt
  next_measurable : MeasurableSet next
  next_subset_stage_valid : next ⊆ thresholdReachStage m k ∩ validStepWalk
  tail : ∀ eta : OrientedAllCreationSupportedAtomIndex t o m k supportAt,
    OrientedAllCreationCofinalConditionalSharpWindowData
      ((orientedAllCreationConcreteFamily
        t o m k supportAt supportData).fiber eta)
      (orientedAllCreationSupportTraceAtom t o m k supportAt
        eta.1.1 eta.1.2)
      next (ENNReal.ofReal (sharpInterfaceCost threshold shell))

namespace OrientedAllCreationCofinalSharpWindowInterfaceProductData

/-- Build the whole countable positive-interface screen from literal
conditional sharp-tail data on every supported all-creation atom.  The
cofinal product bound is derived atomwise by `toCofinalData`; callers cannot
insert an event-probability or abstract product-bound premise here. -/
noncomputable def ofConditionalSharpTailData
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    {next : Set WalkPath} {threshold : ℕ → ℕ} {shell bound : ℕ}
    (supportAt : WalkPath → ℕ → Finset Point)
    (supportData : OrientedAllCreationSupportSelectorData t o m k supportAt)
    (next_measurable : MeasurableSet next)
    (next_subset_stage_valid : next ⊆ thresholdReachStage m k ∩ validStepWalk)
    (tail : ∀ eta : OrientedAllCreationSupportedAtomIndex
        t o m k supportAt,
      OrientedAllCreationConditionalSharpTailData
        ((orientedAllCreationConcreteFamily
          t o m k supportAt supportData).fiber eta)
        (orientedAllCreationSupportTraceAtom t o m k supportAt
          eta.1.1 eta.1.2)
        next threshold shell bound) :
    OrientedAllCreationCofinalSharpWindowInterfaceProductData
      t o m k next threshold shell bound where
  supportAt := supportAt
  supportData := supportData
  next_measurable := next_measurable
  next_subset_stage_valid := next_subset_stage_valid
  tail := fun eta ↦ (tail eta).toCofinalData

abbrev piece
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    {next : Set WalkPath} {threshold : ℕ → ℕ} {shell bound : ℕ}
    (data : OrientedAllCreationCofinalSharpWindowInterfaceProductData
      t o m k next threshold shell bound)
    (eta : OrientedAllCreationSupportedAtomIndex
      t o m k data.supportAt) : Set WalkPath :=
  orientedAllCreationSupportTraceAtom t o m k data.supportAt
    eta.1.1 eta.1.2

/-- Countable summation of the cofinal conditional atomwise bounds. -/
theorem measure_next_le
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    {next : Set WalkPath} {threshold : ℕ → ℕ} {shell bound : ℕ}
    (data : OrientedAllCreationCofinalSharpWindowInterfaceProductData
      t o m k next threshold shell bound) :
    simpleRandomWalk next ≤
      ENNReal.ofReal (sharpInterfaceCost threshold shell) := by
  let cost : ℝ≥0∞ := ENNReal.ofReal (sharpInterfaceCost threshold shell)
  have hlocal : PathTransitionDomination data.piece next cost := by
    intro eta
    exact (data.tail eta).measure_inter_next_le data.next_measurable
      ENNReal.ofReal_ne_top
  calc
    simpleRandomWalk next ≤
        cost * simpleRandomWalk (thresholdReachStage m k ∩ validStepWalk) :=
      measure_next_le_of_atomwiseTransition data.piece
        (fun eta ↦
          (orientedAllCreationConcreteFamily t o m k data.supportAt
            data.supportData).fiber eta |>.atom_measurable)
        (fun eta eta' hne ↦
          (pairwise_disjoint_orientedAllCreationSupportTraceAtom
            t o m k data.supportAt (by
              intro heq
              apply hne
              exact Subtype.ext heq)).mono le_rfl le_rfl)
        (iUnion_supported_orientedAllCreationSupportTraceAtom
          t o m k data.supportAt)
        data.next_subset_stage_valid hlocal
    _ ≤ cost * 1 := by
      gcongr
      simpa using measure_mono (μ := simpleRandomWalk)
        (subset_univ (thresholdReachStage m k ∩ validStepWalk))
    _ = ENNReal.ofReal (sharpInterfaceCost threshold shell) := mul_one _

/-- Real-valued form consumed by a band interface law. -/
theorem simpleRandomWalk_real_next_le
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    {next : Set WalkPath} {threshold : ℕ → ℕ} {shell bound : ℕ}
    (data : OrientedAllCreationCofinalSharpWindowInterfaceProductData
      t o m k next threshold shell bound) :
    simpleRandomWalk.real next ≤ sharpInterfaceCost threshold shell := by
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top data.measure_next_le
  simpa only [Measure.real, ENNReal.toReal_ofReal
    (sharpInterfaceCost_nonneg threshold shell)] using hreal

end OrientedAllCreationCofinalSharpWindowInterfaceProductData

end

end Erdos1165.HLOZAllCreationCofinalConditionalSharpWindow
