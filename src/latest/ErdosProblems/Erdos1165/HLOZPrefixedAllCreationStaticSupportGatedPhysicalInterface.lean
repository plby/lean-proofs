/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.HLOZPrefixedAllCreationStaticSupportPhysicalInterface

/-!
# Coordinate-gated physical positive-interface products

A physical adjacent-shell ratio is valid only at coordinates satisfying the
deterministic fit, rising-mode, and endpoint-boundary conditions.  Requiring
those conditions on every coordinate of every exact atom is too strong.
This module gates both physical shell predicates by a coordinate eligibility
proposition.  Eligible coordinates use the checked `4/3` comparison;
ineligible coordinates have empty upper and lower predicates, so their local
ratio is `0 ≤ (4/3) * 0`.  Paths whose upper-shell witness is ineligible are
therefore absent from this screen and can be paid by a separate balance
remainder.
-/

open MeasureTheory Set
open scoped ENNReal

namespace Erdos1165.HLOZPrefixedAllCreationStaticSupportAggregateRefinement

open CappedCoordinateMassCertificate FiniteDominoProductLaw
open HLOZAllCreationCanonicalRefinement
open HLOZAllCreationCofinalConditionalSharpWindow
open HLOZAllCreationCofinalPhysicalInterface
open HLOZAllSixExactCoordinateProductClosure
open HLOZConditionalTruncatedRandomTotalProductBound
open HLOZPositiveInterfacePhysicalWindows
open HLOZProposition48Candidates
open HLOZPrefixedAllCreationStaticSupportAggregateRefinement
open HLOZPrefixedAllCreationStaticSupportAggregateRefinement.StaticSupportRecoveryCertificate
open HLOZSharpProductNumerics
open LazyDecomposition ScreeningInstantiation
open TilingCappedMarginalization TilingConditionalCappedMarginalization
open TilingOrientedAllCreationConcreteFamily
open TilingOrientedAllCreationStoppedCoordinate
open TilingOrientedSupportAwayCoordinates
open TilingPrefixedStoppedProductDisintegration
open TilingSpatialInsertionFiber VariableStoppedTracePartition

noncomputable section

namespace StaticSupportRecoveryCertificate

abbrev DominoTiling := Tilings.Tiling

attribute [local instance] Classical.propDecidable

variable
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    {supportAt : WalkPath → ℕ → Finset Point}
    {supportData : OrientedAllCreationSupportSelectorData t o m k supportAt}
    {eta : OrientedAllCreationSupportedAtomIndex t o m k supportAt}

/-- Public name for the concrete stopped fibre underlying a gated physical
screen.  Keeping this alias public lets pathwise reconstruction theorems state
their coordinate predicates directly against `ConcreteFiber supportData eta`.
-/
abbrev gatedFiber
    (_cert : StaticSupportRecoveryCertificate supportData eta) :=
  HLOZPrefixedAllCreationStaticSupportAggregateRefinement.ConcreteFiber
    supportData eta

/-- Physical upper-window predicate restricted to eligible coordinates. -/
def gatedPhysicalUpper
    (cert : StaticSupportRecoveryCertificate supportData eta)
    (eligible : ∀ cap, TilingAwayDomino t (cert.gatedFiber.start cap)
      (cert.gatedFiber.retained cap) (cert.gatedFiber.distinguished cap) → Prop)
    (width shell cap : ℕ)
    (b : TilingAwayDomino t (cert.gatedFiber.start cap)
      (cert.gatedFiber.retained cap) (cert.gatedFiber.distinguished cap))
    (v : Fin (cert.gatedFiber.upper cap b)) : Prop :=
  eligible cap b ∧
    (v : ℕ) ∈ physicalDeficitFailureWindow m width
      (Fintype.card (TilingCoordinatesAt t (cert.gatedFiber.start cap)
        (cert.gatedFiber.retained cap) b.1)) (shell + 1)

/-- Physical lower-window predicate restricted by the same eligibility gate. -/
def gatedPhysicalLower
    (cert : StaticSupportRecoveryCertificate supportData eta)
    (eligible : ∀ cap, TilingAwayDomino t (cert.gatedFiber.start cap)
      (cert.gatedFiber.retained cap) (cert.gatedFiber.distinguished cap) → Prop)
    (width shell cap : ℕ)
    (b : TilingAwayDomino t (cert.gatedFiber.start cap)
      (cert.gatedFiber.retained cap) (cert.gatedFiber.distinguished cap))
    (v : Fin (cert.gatedFiber.upper cap b)) : Prop :=
  eligible cap b ∧
    (v : ℕ) ∈ physicalDeficitFailureWindow m width
      (Fintype.card (TilingCoordinatesAt t (cert.gatedFiber.start cap)
        (cert.gatedFiber.retained cap) b.1)) shell

/-- Accepted broad screen together with the coordinate-gated random-total
physical adjacent-shell tail. -/
def gatedPhysicalScreenedProp
    (cert : StaticSupportRecoveryCertificate supportData eta)
    (eligible : ∀ cap, TilingAwayDomino t (cert.gatedFiber.start cap)
      (cert.gatedFiber.retained cap) (cert.gatedFiber.distinguished cap) → Prop)
    (threshold : ℕ → ℕ) (width shell bound cap : ℕ)
    (ell : TruncatedTotals (cert.gatedFiber.upper cap)) : Prop :=
  cert.baseProp cap ell ∧
    allCreationRandomTotalThresholdedUpperTail cert.gatedFiber cap
      (cert.gatedPhysicalUpper eligible width shell cap)
      (cert.gatedPhysicalLower eligible width shell cap)
      threshold shellGrowth48 shell bound ell

noncomputable def gatedPhysicalScreenedAccepts
    (cert : StaticSupportRecoveryCertificate supportData eta)
    (eligible : ∀ cap, TilingAwayDomino t (cert.gatedFiber.start cap)
      (cert.gatedFiber.retained cap) (cert.gatedFiber.distinguished cap) → Prop)
    (threshold : ℕ → ℕ) (width shell bound cap : ℕ) :
    TruncatedTotals (cert.gatedFiber.upper cap) → Bool := fun ell ↦
  decide (cert.gatedPhysicalScreenedProp eligible threshold width shell bound
    cap ell)

private noncomputable def gatedPhysicalBasePredicate
    (cert : StaticSupportRecoveryCertificate supportData eta) (cap : ℕ)
    (q : TilingCappedCoordinates eta.1.1.external.retainedCount
      (cert.gatedFiber.coordinateCap cap)) : Prop :=
  cert.gatedFiber.atomPredicate cap q ∧
    TilingAwayTotalsScreen t (cert.gatedFiber.start cap)
      (cert.gatedFiber.retained cap) (cert.gatedFiber.distinguished cap)
      (cert.gatedFiber.upper cap) (fun ell ↦ cert.baseAccepts cap ell = true)
      ((splitTilingCoordinatesEquiv t (cert.gatedFiber.start cap)
        (cert.gatedFiber.retained cap) (cert.gatedFiber.distinguished cap) q).2)

/-- Path-coordinate predicate for the gated physical screen. -/
noncomputable def gatedPhysicalScreenedPredicate
    (cert : StaticSupportRecoveryCertificate supportData eta)
    (eligible : ∀ cap, TilingAwayDomino t (cert.gatedFiber.start cap)
      (cert.gatedFiber.retained cap) (cert.gatedFiber.distinguished cap) → Prop)
    (threshold : ℕ → ℕ) (width shell bound cap : ℕ)
    (q : TilingCappedCoordinates eta.1.1.external.retainedCount
      (cert.gatedFiber.coordinateCap cap)) : Prop :=
  cert.gatedFiber.atomPredicate cap q ∧
    TilingAwayTotalsScreen t (cert.gatedFiber.start cap)
      (cert.gatedFiber.retained cap) (cert.gatedFiber.distinguished cap)
      (cert.gatedFiber.upper cap)
      (fun ell ↦ cert.gatedPhysicalScreenedAccepts eligible threshold width
        shell bound cap ell = true)
      ((splitTilingCoordinatesEquiv t (cert.gatedFiber.start cap)
        (cert.gatedFiber.retained cap) (cert.gatedFiber.distinguished cap) q).2)

private theorem gatedPhysicalScreenedScreen_base
    (cert : StaticSupportRecoveryCertificate supportData eta)
    (eligible : ∀ cap, TilingAwayDomino t (cert.gatedFiber.start cap)
      (cert.gatedFiber.retained cap) (cert.gatedFiber.distinguished cap) → Prop)
    (threshold : ℕ → ℕ) (width shell bound cap : ℕ)
    (a : TilingAwayCoordinates (cap := cert.gatedFiber.coordinateCap cap)
      t (cert.gatedFiber.start cap) (cert.gatedFiber.retained cap)
        (cert.gatedFiber.distinguished cap))
    (h : TilingAwayTotalsScreen t (cert.gatedFiber.start cap)
      (cert.gatedFiber.retained cap) (cert.gatedFiber.distinguished cap)
      (cert.gatedFiber.upper cap)
      (fun ell ↦ cert.gatedPhysicalScreenedAccepts eligible threshold width
        shell bound cap ell = true) a) :
    TilingAwayTotalsScreen t (cert.gatedFiber.start cap)
      (cert.gatedFiber.retained cap) (cert.gatedFiber.distinguished cap)
      (cert.gatedFiber.upper cap) (fun ell ↦ cert.baseAccepts cap ell = true)
      a := by
  rcases h with ⟨ell, hell, htotal⟩
  refine ⟨ell, ?_, htotal⟩
  have hprop := @of_decide_eq_true
    (cert.gatedPhysicalScreenedProp eligible threshold width shell bound cap ell)
      (Classical.propDecidable _) hell
  exact show cert.baseAccepts cap ell = true by
    simpa only [StaticSupportRecoveryCertificate.baseAccepts,
      decide_eq_true_eq] using hprop.1

private theorem gatedPhysicalBase_factorization
    (cert : StaticSupportRecoveryCertificate supportData eta) (cap : ℕ)
    (q : TilingCappedCoordinates eta.1.1.external.retainedCount
      (cert.gatedFiber.coordinateCap cap)) :
    cert.gatedPhysicalBasePredicate cap q ∧
        PrefixedTilingStoppingAccepted (cert.gatedFiber.stoppingTime cap)
          (cert.gatedFiber.initial cap) t (cert.gatedFiber.start cap)
          (cert.gatedFiber.retained cap) (fun j ↦ (q j : ℕ))
          (cert.gatedFiber.tail cap) ↔
      cert.gatedFiber.selected cap
          ((splitTilingCoordinatesEquiv t (cert.gatedFiber.start cap)
            (cert.gatedFiber.retained cap)
            (cert.gatedFiber.distinguished cap) q).1) ∧
        TilingAwayTotalsScreen t (cert.gatedFiber.start cap)
          (cert.gatedFiber.retained cap) (cert.gatedFiber.distinguished cap)
          (cert.gatedFiber.upper cap)
          (fun ell ↦ cert.baseAccepts cap ell = true)
          ((splitTilingCoordinatesEquiv t (cert.gatedFiber.start cap)
            (cert.gatedFiber.retained cap)
            (cert.gatedFiber.distinguished cap) q).2) := by
  apply allCreationScreenedPredicate_factorization_of_reconstructed
    supportData eta cap (fun ell ↦ cert.baseAccepts cap ell = true) (q := q)
  intro q'
  dsimp only
  intro hselected hscreen
  apply cert.recover cap q' hselected
  rcases hscreen with ⟨ell, hell, htotal⟩
  refine ⟨ell, ?_, htotal⟩
  exact @of_decide_eq_true (cert.baseProp cap ell)
    (Classical.propDecidable _) hell

private theorem gatedPhysicalScreened_factorization
    (cert : StaticSupportRecoveryCertificate supportData eta)
    (eligible : ∀ cap, TilingAwayDomino t (cert.gatedFiber.start cap)
      (cert.gatedFiber.retained cap) (cert.gatedFiber.distinguished cap) → Prop)
    (threshold : ℕ → ℕ) (width shell bound cap : ℕ)
    (q : TilingCappedCoordinates eta.1.1.external.retainedCount
      (cert.gatedFiber.coordinateCap cap)) :
    cert.gatedPhysicalScreenedPredicate eligible threshold width shell bound cap q ∧
        PrefixedTilingStoppingAccepted (cert.gatedFiber.stoppingTime cap)
          (cert.gatedFiber.initial cap) t (cert.gatedFiber.start cap)
          (cert.gatedFiber.retained cap) (fun j ↦ (q j : ℕ))
          (cert.gatedFiber.tail cap) ↔
      cert.gatedFiber.selected cap
          ((splitTilingCoordinatesEquiv t (cert.gatedFiber.start cap)
            (cert.gatedFiber.retained cap)
            (cert.gatedFiber.distinguished cap) q).1) ∧
        TilingAwayTotalsScreen t (cert.gatedFiber.start cap)
          (cert.gatedFiber.retained cap) (cert.gatedFiber.distinguished cap)
          (cert.gatedFiber.upper cap)
          (fun ell ↦ cert.gatedPhysicalScreenedAccepts eligible threshold
            width shell bound cap ell = true)
          ((splitTilingCoordinatesEquiv t (cert.gatedFiber.start cap)
            (cert.gatedFiber.retained cap)
            (cert.gatedFiber.distinguished cap) q).2) := by
  apply allCreationScreenedPredicate_factorization_of_reconstructed
    supportData eta cap
      (fun ell ↦ cert.gatedPhysicalScreenedAccepts eligible threshold width
        shell bound cap ell = true) (q := q)
  intro q'
  dsimp only
  intro hselected hscreen
  have hbase := cert.gatedPhysicalScreenedScreen_base eligible threshold width
    shell bound cap _ hscreen
  rcases hbase with ⟨ell, hell, htotal⟩
  apply cert.recover cap q' hselected
  refine ⟨ell, ?_, htotal⟩
  exact @of_decide_eq_true (cert.baseProp cap ell)
    (Classical.propDecidable _) hell

private theorem gatedScreenMass_bool_coordinate_windows_pos
    {Domino : Type*} [Fintype Domino] [DecidableEq Domino]
    (pointMass : Domino → ℕ → ℝ) (upper : Domino → ℕ)
    (accepts : TruncatedTotals upper → Bool)
    (window : Domino → Finset ℕ)
    (hiff : ∀ ell, accepts ell = true ↔
      ∀ b, (ell b : ℕ) ∈ window b)
    (hlocal : ∀ b, 0 < ∑ v : Fin (upper b),
      if (v : ℕ) ∈ window b then
        coordinateMass pointMass upper b v else 0) :
    0 < @screenMass Domino inferInstance inferInstance pointMass upper
      (fun ell ↦ accepts ell = true)
      (fun ell ↦ instDecidableEqBool (accepts ell) true) := by
  classical
  have hbroad : 0 < screenMass pointMass upper
      (fun ell ↦ ∀ b, (ell b : ℕ) ∈ window b) := by
    rw [screenMass_all_coordinate_windows_eq_prod]
    exact Finset.prod_pos fun b _ ↦ hlocal b
  apply hbroad.trans_eq
  unfold screenMass
  apply Finset.sum_congr rfl
  intro ell _hell
  exact if_congr (hiff ell).symm rfl rfl

private theorem gatedPhysicalBaseMass_pos
    (cert : StaticSupportRecoveryCertificate supportData eta)
    (baseLocalPos : ∀ cap
      (b : TilingAwayDomino t (cert.gatedFiber.start cap)
        (cert.gatedFiber.retained cap) (cert.gatedFiber.distinguished cap)),
      0 < ∑ v : Fin (cert.gatedFiber.upper cap b),
        if (v : ℕ) ∈ cert.baseWindow cap b then
          coordinateMass
            (tilingAwayPointMass (cap := cert.gatedFiber.coordinateCap cap) t
              (cert.gatedFiber.start cap) (cert.gatedFiber.retained cap)
              (cert.gatedFiber.distinguished cap))
            (cert.gatedFiber.upper cap) b v else 0) :
    ∀ cap, 0 < allCreationBoolScreenMass cert.gatedFiber
      cert.baseAccepts cap := by
  intro cap
  unfold allCreationBoolScreenMass
  exact @gatedScreenMass_bool_coordinate_windows_pos
    (TilingAwayDomino t (cert.gatedFiber.start cap)
      (cert.gatedFiber.retained cap) (cert.gatedFiber.distinguished cap))
    (instFintypeTilingAwayDomino t (cert.gatedFiber.start cap)
      (cert.gatedFiber.retained cap) (cert.gatedFiber.distinguished cap))
    (fun a b ↦ Subtype.instDecidableEq a b)
    (tilingAwayPointMass (cap := cert.gatedFiber.coordinateCap cap) t
      (cert.gatedFiber.start cap) (cert.gatedFiber.retained cap)
      (cert.gatedFiber.distinguished cap))
    (cert.gatedFiber.upper cap) (cert.baseAccepts cap)
    (cert.baseWindow cap)
    (fun ell ↦ by
      change cert.baseAccepts cap ell = true ↔ cert.baseProp cap ell
      simp only [StaticSupportRecoveryCertificate.baseAccepts,
        decide_eq_true_eq])
    (baseLocalPos cap)

/-- Exact stopped-coordinate refinement for the coordinate-gated physical
screen. -/
noncomputable def gatedPhysicalRefinement
    (cert : StaticSupportRecoveryCertificate supportData eta)
    (eligible : ∀ cap, TilingAwayDomino t (cert.gatedFiber.start cap)
      (cert.gatedFiber.retained cap) (cert.gatedFiber.distinguished cap) → Prop)
    (piece next : Set WalkPath) (threshold : ℕ → ℕ)
    (width shell bound : ℕ)
    (atom_subset_piece : orientedAllCreationSupportTraceAtom
      t o m k supportAt eta.1.1 eta.1.2 ⊆ piece)
    (baseLocalPos : ∀ cap
      (b : TilingAwayDomino t (cert.gatedFiber.start cap)
        (cert.gatedFiber.retained cap) (cert.gatedFiber.distinguished cap)),
      0 < ∑ v : Fin (cert.gatedFiber.upper cap b),
        if (v : ℕ) ∈ cert.baseWindow cap b then
          coordinateMass
            (tilingAwayPointMass (cap := cert.gatedFiber.coordinateCap cap) t
              (cert.gatedFiber.start cap) (cert.gatedFiber.retained cap)
              (cert.gatedFiber.distinguished cap))
            (cert.gatedFiber.upper cap) b v else 0)
    (monotone_screened : Monotone fun cap ↦
      walkLift (prefixedTilingPreStoppingFiberEvent
        (cert.gatedFiber.stoppingTime cap) (cert.gatedFiber.initial cap) t
        (cert.gatedFiber.start cap) (cert.gatedFiber.retained cap)
        (cert.gatedFiber.coordinateCap cap) (cert.gatedFiber.tail cap)
        (cert.gatedPhysicalScreenedPredicate eligible threshold width shell
          bound cap)))
    (transition_covered : piece ∩ next ⊆ ⋃ cap,
      walkLift (prefixedTilingPreStoppingFiberEvent
        (cert.gatedFiber.stoppingTime cap) (cert.gatedFiber.initial cap) t
        (cert.gatedFiber.start cap) (cert.gatedFiber.retained cap)
        (cert.gatedFiber.coordinateCap cap) (cert.gatedFiber.tail cap)
        (cert.gatedPhysicalScreenedPredicate eligible threshold width shell
          bound cap))) :
    OrientedAllCreationConditionalRefinementData cert.gatedFiber piece next 1 where
  basePredicate := cert.gatedPhysicalBasePredicate
  screenedPredicate := cert.gatedPhysicalScreenedPredicate eligible threshold
    width shell bound
  base_subset_atom := fun _cap _q hq ↦ hq.1
  screened_subset_basePredicate := by
    intro cap q hq
    exact ⟨hq.1, cert.gatedPhysicalScreenedScreen_base eligible threshold
      width shell bound cap _ hq.2⟩
  baseAccepts := cert.baseAccepts
  screenedAccepts := cert.gatedPhysicalScreenedAccepts eligible threshold
    width shell bound
  screened_subset_base := by
    intro cap ell hell
    have hprop := @of_decide_eq_true
      (cert.gatedPhysicalScreenedProp eligible threshold width shell bound
        cap ell) (Classical.propDecidable _) hell
    simpa only [StaticSupportRecoveryCertificate.baseAccepts,
      decide_eq_true_eq] using hprop.1
  base_factorization := by
    intro cap q
    simpa only [OrientedAllCreationPrefixedStoppedCoordinateSpec.retainedCount]
      using cert.gatedPhysicalBase_factorization cap q
  screened_factorization := by
    intro cap q
    simpa only [OrientedAllCreationPrefixedStoppedCoordinateSpec.retainedCount]
      using cert.gatedPhysicalScreened_factorization eligible threshold width
        shell bound cap q
  base_mass_pos := cert.gatedPhysicalBaseMass_pos baseLocalPos
  base_subset_piece := by
    intro cap s hs
    apply atom_subset_piece
    apply cert.gatedFiber.atom_sound cap
    exact ⟨hs.1, prefixedTilingPreStoppingFiberEvent_mono
      (cert.gatedFiber.stoppingTime cap) (cert.gatedFiber.initial cap) t
      (cert.gatedFiber.start cap) (cert.gatedFiber.retained cap)
      (cert.gatedFiber.tail cap) (fun _q hq ↦ hq.1) hs.2⟩
  monotone_screened := monotone_screened
  transition_covered := transition_covered
  product_bound := by
    intro cap
    rw [ENNReal.toReal_one]
    apply @conditionalScreenMass_le_one_of_subset
      (TilingAwayDomino t (cert.gatedFiber.start cap)
        (cert.gatedFiber.retained cap) (cert.gatedFiber.distinguished cap))
      (instFintypeTilingAwayDomino t (cert.gatedFiber.start cap)
        (cert.gatedFiber.retained cap) (cert.gatedFiber.distinguished cap))
      (fun a b ↦ Subtype.instDecidableEq a b)
      (tilingAwayPointMass (cap := cert.gatedFiber.coordinateCap cap) t
        (cert.gatedFiber.start cap) (cert.gatedFiber.retained cap)
        (cert.gatedFiber.distinguished cap))
      (cert.gatedFiber.upper cap)
      (fun ell ↦ cert.baseAccepts cap ell = true)
      (fun ell ↦ cert.gatedPhysicalScreenedAccepts eligible threshold width
        shell bound cap ell = true)
      (fun ell ↦ instDecidableEqBool (cert.baseAccepts cap ell) true)
      (fun ell ↦ instDecidableEqBool
        (cert.gatedPhysicalScreenedAccepts eligible threshold width shell bound
          cap ell) true)
    · intro b v
      exact tilingAwayExactTotalMass_nonneg t
        (cert.gatedFiber.start cap) (cert.gatedFiber.retained cap)
        (cert.gatedFiber.distinguished cap) b v
    · intro ell hell
      have hprop := @of_decide_eq_true
        (cert.gatedPhysicalScreenedProp eligible threshold width shell bound
          cap ell) (Classical.propDecidable _) hell
      simpa only [StaticSupportRecoveryCertificate.baseAccepts,
        decide_eq_true_eq] using hprop.1
    · exact cert.gatedPhysicalBaseMass_pos baseLocalPos cap

/-- Add the checked local ratio on eligible coordinates.  Ineligible
coordinates contribute zero to both physical windows, so the same sharp
cofinal product bound follows without a global balance hypothesis. -/
noncomputable def gatedPhysicalCofinalData
    (cert : StaticSupportRecoveryCertificate supportData eta)
    (eligible : ∀ cap, TilingAwayDomino t (cert.gatedFiber.start cap)
      (cert.gatedFiber.retained cap) (cert.gatedFiber.distinguished cap) → Prop)
    (piece next : Set WalkPath) (threshold : ℕ → ℕ)
    (width shell bound : ℕ)
    (atom_subset_piece : orientedAllCreationSupportTraceAtom
      t o m k supportAt eta.1.1 eta.1.2 ⊆ piece)
    (baseLocalPos : ∀ cap
      (b : TilingAwayDomino t (cert.gatedFiber.start cap)
        (cert.gatedFiber.retained cap) (cert.gatedFiber.distinguished cap)),
      0 < ∑ v : Fin (cert.gatedFiber.upper cap b),
        if (v : ℕ) ∈ cert.baseWindow cap b then
          coordinateMass
            (tilingAwayPointMass (cap := cert.gatedFiber.coordinateCap cap) t
              (cert.gatedFiber.start cap) (cert.gatedFiber.retained cap)
              (cert.gatedFiber.distinguished cap))
            (cert.gatedFiber.upper cap) b v else 0)
    (monotone_screened : Monotone fun cap ↦
      walkLift (prefixedTilingPreStoppingFiberEvent
        (cert.gatedFiber.stoppingTime cap) (cert.gatedFiber.initial cap) t
        (cert.gatedFiber.start cap) (cert.gatedFiber.retained cap)
        (cert.gatedFiber.coordinateCap cap) (cert.gatedFiber.tail cap)
        (cert.gatedPhysicalScreenedPredicate eligible threshold width shell
          bound cap)))
    (transition_covered : piece ∩ next ⊆ ⋃ cap,
      walkLift (prefixedTilingPreStoppingFiberEvent
        (cert.gatedFiber.stoppingTime cap) (cert.gatedFiber.initial cap) t
        (cert.gatedFiber.start cap) (cert.gatedFiber.retained cap)
        (cert.gatedFiber.coordinateCap cap) (cert.gatedFiber.tail cap)
        (cert.gatedPhysicalScreenedPredicate eligible threshold width shell
          bound cap)))
    (capStart : ℕ)
    (window_ratio_inter_base : ∀ cap, capStart ≤ cap →
      ∀ (b : TilingAwayDomino t (cert.gatedFiber.start cap)
        (cert.gatedFiber.retained cap) (cert.gatedFiber.distinguished cap)),
      eligible cap b →
      (∑ v : Fin (cert.gatedFiber.upper cap b),
        if (v : ℕ) ∈ physicalDeficitFailureWindow m width
              (Fintype.card (TilingCoordinatesAt t
                (cert.gatedFiber.start cap) (cert.gatedFiber.retained cap)
                b.1)) (shell + 1) ∧
            (v : ℕ) ∈ cert.baseWindow cap b then
          coordinateMass
            (tilingAwayPointMass (cap := cert.gatedFiber.coordinateCap cap) t
              (cert.gatedFiber.start cap) (cert.gatedFiber.retained cap)
              (cert.gatedFiber.distinguished cap))
            (cert.gatedFiber.upper cap) b v else 0) ≤
        (4 / 3 : ℝ) *
          ∑ v : Fin (cert.gatedFiber.upper cap b),
            if (v : ℕ) ∈ physicalDeficitFailureWindow m width
                  (Fintype.card (TilingCoordinatesAt t
                    (cert.gatedFiber.start cap) (cert.gatedFiber.retained cap)
                    b.1)) shell ∧
                (v : ℕ) ∈ cert.baseWindow cap b then
              coordinateMass
                (tilingAwayPointMass
                  (cap := cert.gatedFiber.coordinateCap cap) t
                  (cert.gatedFiber.start cap) (cert.gatedFiber.retained cap)
                  (cert.gatedFiber.distinguished cap))
                (cert.gatedFiber.upper cap) b v else 0) :
    OrientedAllCreationCofinalConditionalSharpWindowData cert.gatedFiber
      piece next (ENNReal.ofReal (sharpInterfaceCost threshold shell)) where
  refinement := cert.gatedPhysicalRefinement eligible piece next threshold
    width shell bound atom_subset_piece baseLocalPos monotone_screened
      transition_covered
  capStart := capStart
  cofinal_product_bound := by
    intro cap hcap
    classical
    rw [ENNReal.toReal_ofReal (sharpInterfaceCost_nonneg threshold shell)]
    unfold allCreationBoolConditionalScreenMass
    apply @conditionalScreenMass_randomTotalThresholdedUpperTail_inter_base_le_of_iff
      (TilingAwayDomino t (cert.gatedFiber.start cap)
        (cert.gatedFiber.retained cap) (cert.gatedFiber.distinguished cap))
      (instFintypeTilingAwayDomino t (cert.gatedFiber.start cap)
        (cert.gatedFiber.retained cap) (cert.gatedFiber.distinguished cap))
      (fun a b ↦ Subtype.instDecidableEq a b)
      (tilingAwayPointMass (cap := cert.gatedFiber.coordinateCap cap) t
        (cert.gatedFiber.start cap) (cert.gatedFiber.retained cap)
        (cert.gatedFiber.distinguished cap))
      (cert.gatedFiber.upper cap)
      (fun b v ↦ (v : ℕ) ∈ cert.baseWindow cap b)
      (cert.gatedPhysicalUpper eligible width shell cap)
      (cert.gatedPhysicalLower eligible width shell cap)
      inferInstance inferInstance inferInstance threshold shellGrowth48 shell bound
      (fun ell ↦ cert.baseAccepts cap ell = true)
      (fun ell ↦ cert.gatedPhysicalScreenedAccepts eligible threshold width
        shell bound cap ell = true)
      (fun ell ↦ instDecidableEqBool (cert.baseAccepts cap ell) true)
      (fun ell ↦ instDecidableEqBool
        (cert.gatedPhysicalScreenedAccepts eligible threshold width shell bound
          cap ell) true)
      (C := (4 / 3 : ℝ))
      (K := sharpInterfaceCost threshold shell)
      (fun ell ↦ by
        change cert.baseAccepts cap ell = true ↔ cert.baseProp cap ell
        simp only [StaticSupportRecoveryCertificate.baseAccepts,
          decide_eq_true_eq])
      (fun ell ↦ by
        change cert.gatedPhysicalScreenedAccepts eligible threshold width shell
            bound cap ell = true ↔
          cert.gatedPhysicalScreenedProp eligible threshold width shell bound
            cap ell
        simp only [gatedPhysicalScreenedAccepts, decide_eq_true_eq])
      (fun b v ↦ coordinateMass_nonneg_of_pointMass_nonneg _ _
        (fun b' ell ↦ tilingAwayExactTotalMass_nonneg t
          (cert.gatedFiber.start cap) (cert.gatedFiber.retained cap)
          (cert.gatedFiber.distinguished cap) b' ell) b v)
      (baseLocalPos cap)
      (fun b v hv ↦ Finset.disjoint_left.mp
        (physicalAdjacentFailureWindows_disjoint
          (m := m) (width := width)
          (i := Fintype.card (TilingCoordinatesAt t
            (cert.gatedFiber.start cap) (cert.gatedFiber.retained cap) b.1))
          (shell := shell)) hv.1.2 hv.2.2)
      (by norm_num) (sharpInterfaceCost_nonneg threshold shell)
      (fun b ↦ by
        by_cases hb : eligible cap b
        · simp only [gatedPhysicalUpper, gatedPhysicalLower, hb, true_and]
          exact window_ratio_inter_base cap hcap b hb
        · simp only [gatedPhysicalUpper, gatedPhysicalLower, hb,
            false_and, if_false, Finset.sum_const_zero, mul_zero, le_refl])
      (fun total _ ↦
        thresholdedProductEnvelope_le_sharpInterfaceCost
          (4 / 3) (by norm_num) four_thirds_le_positiveInterfaceRatioConstant
            threshold shell total)

end StaticSupportRecoveryCertificate

end

end Erdos1165.HLOZPrefixedAllCreationStaticSupportAggregateRefinement
