/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.HLOZAllCreationCofinalPhysicalInterface
import ErdosProblems.Erdos1165.HLOZPrefixedAllCreationStaticSupportAggregateRefinement

/-!
# Static-support recovery for physical deficit-shell windows

This is the physical-window analogue of the legacy static-support aggregate
refinement.  The broad accepted-creation screen and its recovery certificate
are reused verbatim.  Only the narrow Boolean screen is changed: its upper
and lower coordinate predicates are the exact physical deficit shells.
-/

open MeasureTheory Set
open scoped ENNReal

namespace Erdos1165.HLOZPrefixedAllCreationStaticSupportAggregateRefinement

open CappedCoordinateMassCertificate FiniteDominoProductLaw
open HLOZAllCreationCofinalConditionalSharpWindow
open HLOZAllCreationCofinalPhysicalInterface
open HLOZAllSixExactCoordinateProductClosure
open HLOZPositiveInterfacePhysicalWindows
open HLOZProposition48Candidates
open HLOZPrefixedAllCreationStaticSupportAggregateRefinement
open LazyDecomposition
open TilingCappedMarginalization
open TilingConditionalCappedMarginalization
open TilingOrientedAllCreationConcreteFamily
open TilingOrientedAllCreationStoppedCoordinate
open TilingOrientedSupportAwayCoordinates
open TilingPrefixedStoppedProductDisintegration
open TilingSpatialInsertionFiber
open VariableStoppedTracePartition

noncomputable section

namespace StaticSupportRecoveryCertificate

attribute [local instance] Classical.propDecidable

variable
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    {supportAt : WalkPath → ℕ → Finset Point}
    {supportData : OrientedAllCreationSupportSelectorData t o m k supportAt}
    {eta : OrientedAllCreationSupportedAtomIndex t o m k supportAt}

/-- The concrete stopped-coordinate fibre used by the physical interface screen.

This is public so downstream path-recovery theorems can state the recovered
random-total tail on definitionally the same fibre as `physicalScreenedProp`.
-/
abbrev physicalFiber
    (_cert : StaticSupportRecoveryCertificate supportData eta) :=
  ConcreteFiber supportData eta

/-- The exact accepted physical adjacent-shell predicate on away totals. -/
def physicalScreenedProp
    (cert : StaticSupportRecoveryCertificate supportData eta)
    (threshold : ℕ → ℕ) (width shell bound cap : ℕ)
    (ell : TruncatedTotals (cert.physicalFiber.upper cap)) : Prop :=
  cert.baseProp cap ell ∧
    allCreationRandomTotalThresholdedUpperTail cert.physicalFiber cap
      (fun b (v : Fin (cert.physicalFiber.upper cap b)) ↦
        (v : ℕ) ∈ physicalDeficitFailureWindow m width
          (Fintype.card (TilingCoordinatesAt t
            (cert.physicalFiber.start cap)
            (cert.physicalFiber.retained cap) b.1)) (shell + 1))
      (fun b (v : Fin (cert.physicalFiber.upper cap b)) ↦
        (v : ℕ) ∈ physicalDeficitFailureWindow m width
          (Fintype.card (TilingCoordinatesAt t
            (cert.physicalFiber.start cap)
            (cert.physicalFiber.retained cap) b.1)) shell)
      threshold shellGrowth48 shell bound ell

noncomputable def physicalScreenedAccepts
    (cert : StaticSupportRecoveryCertificate supportData eta)
    (threshold : ℕ → ℕ) (width shell bound cap : ℕ) :
    TruncatedTotals (cert.physicalFiber.upper cap) → Bool := fun ell ↦
  decide (cert.physicalScreenedProp threshold width shell bound cap ell)

/-- Boolean membership in the physical screen is exactly its propositional
form.  Keeping this characterization at the definition site prevents
downstream path-recovery proofs from unfolding the dependent concrete fibre.
-/
@[simp] theorem physicalScreenedAccepts_eq_true_iff
    (cert : StaticSupportRecoveryCertificate supportData eta)
    (threshold : ℕ → ℕ) (width shell bound cap : ℕ)
    (ell : TruncatedTotals (cert.physicalFiber.upper cap)) :
    cert.physicalScreenedAccepts threshold width shell bound cap ell = true ↔
      cert.physicalScreenedProp threshold width shell bound cap ell := by
  simp only [physicalScreenedAccepts, decide_eq_true_eq]

private noncomputable def physicalBasePredicate
    (cert : StaticSupportRecoveryCertificate supportData eta) (cap : ℕ)
    (q : TilingCappedCoordinates eta.1.1.external.retainedCount
      (cert.physicalFiber.coordinateCap cap)) : Prop :=
  cert.physicalFiber.atomPredicate cap q ∧
    TilingAwayTotalsScreen t (cert.physicalFiber.start cap)
      (cert.physicalFiber.retained cap) (cert.physicalFiber.distinguished cap)
      (cert.physicalFiber.upper cap)
      (fun ell ↦ cert.baseAccepts cap ell = true)
      ((splitTilingCoordinatesEquiv t (cert.physicalFiber.start cap)
        (cert.physicalFiber.retained cap)
        (cert.physicalFiber.distinguished cap) q).2)

/-- Public path-coordinate predicate for the physical narrow screen. -/
noncomputable def physicalScreenedPredicate
    (cert : StaticSupportRecoveryCertificate supportData eta)
    (threshold : ℕ → ℕ) (width shell bound cap : ℕ)
    (q : TilingCappedCoordinates eta.1.1.external.retainedCount
      (cert.physicalFiber.coordinateCap cap)) : Prop :=
  cert.physicalFiber.atomPredicate cap q ∧
    TilingAwayTotalsScreen t (cert.physicalFiber.start cap)
      (cert.physicalFiber.retained cap) (cert.physicalFiber.distinguished cap)
      (cert.physicalFiber.upper cap)
      (fun ell ↦ cert.physicalScreenedAccepts threshold width shell bound
        cap ell = true)
      ((splitTilingCoordinatesEquiv t (cert.physicalFiber.start cap)
        (cert.physicalFiber.retained cap)
        (cert.physicalFiber.distinguished cap) q).2)

private theorem physicalScreenedScreen_base
    (cert : StaticSupportRecoveryCertificate supportData eta)
    (threshold : ℕ → ℕ) (width shell bound cap : ℕ)
    (a : TilingAwayCoordinates (cap := cert.physicalFiber.coordinateCap cap)
      t (cert.physicalFiber.start cap) (cert.physicalFiber.retained cap)
        (cert.physicalFiber.distinguished cap))
    (h : TilingAwayTotalsScreen t (cert.physicalFiber.start cap)
      (cert.physicalFiber.retained cap) (cert.physicalFiber.distinguished cap)
      (cert.physicalFiber.upper cap)
      (fun ell ↦ cert.physicalScreenedAccepts threshold width shell bound
        cap ell = true) a) :
    TilingAwayTotalsScreen t (cert.physicalFiber.start cap)
      (cert.physicalFiber.retained cap) (cert.physicalFiber.distinguished cap)
      (cert.physicalFiber.upper cap)
      (fun ell ↦ cert.baseAccepts cap ell = true) a := by
  rcases h with ⟨ell, hell, htotal⟩
  refine ⟨ell, ?_, htotal⟩
  have hprop : cert.physicalScreenedProp threshold width shell bound cap ell := by
    simpa only [physicalScreenedAccepts, decide_eq_true_eq] using hell
  simpa only [StaticSupportRecoveryCertificate.baseAccepts,
    decide_eq_true_eq] using hprop.1

private theorem physicalBase_factorization
    (cert : StaticSupportRecoveryCertificate supportData eta) (cap : ℕ)
    (q : TilingCappedCoordinates eta.1.1.external.retainedCount
      (cert.physicalFiber.coordinateCap cap)) :
    cert.physicalBasePredicate cap q ∧
        PrefixedTilingStoppingAccepted (cert.physicalFiber.stoppingTime cap)
          (cert.physicalFiber.initial cap) t (cert.physicalFiber.start cap)
          (cert.physicalFiber.retained cap) (fun j ↦ (q j : ℕ))
          (cert.physicalFiber.tail cap) ↔
      cert.physicalFiber.selected cap
          ((splitTilingCoordinatesEquiv t (cert.physicalFiber.start cap)
            (cert.physicalFiber.retained cap)
            (cert.physicalFiber.distinguished cap) q).1) ∧
        TilingAwayTotalsScreen t (cert.physicalFiber.start cap)
          (cert.physicalFiber.retained cap) (cert.physicalFiber.distinguished cap)
          (cert.physicalFiber.upper cap)
          (fun ell ↦ cert.baseAccepts cap ell = true)
          ((splitTilingCoordinatesEquiv t (cert.physicalFiber.start cap)
            (cert.physicalFiber.retained cap)
            (cert.physicalFiber.distinguished cap) q).2) := by
  apply
    HLOZAllCreationCanonicalRefinement.allCreationScreenedPredicate_factorization_of_reconstructed
      supportData eta cap (fun ell ↦ cert.baseAccepts cap ell = true)
      (q := q)
  intro q'
  dsimp only
  intro hselected hscreen
  apply cert.recover cap q' hselected
  rcases hscreen with ⟨ell, hell, htotal⟩
  refine ⟨ell, ?_, htotal⟩
  exact @of_decide_eq_true (cert.baseProp cap ell)
    (Classical.propDecidable _) hell

private theorem physicalScreened_factorization
    (cert : StaticSupportRecoveryCertificate supportData eta)
    (threshold : ℕ → ℕ) (width shell bound cap : ℕ)
    (q : TilingCappedCoordinates eta.1.1.external.retainedCount
      (cert.physicalFiber.coordinateCap cap)) :
    cert.physicalScreenedPredicate threshold width shell bound cap q ∧
        PrefixedTilingStoppingAccepted (cert.physicalFiber.stoppingTime cap)
          (cert.physicalFiber.initial cap) t (cert.physicalFiber.start cap)
          (cert.physicalFiber.retained cap) (fun j ↦ (q j : ℕ))
          (cert.physicalFiber.tail cap) ↔
      cert.physicalFiber.selected cap
          ((splitTilingCoordinatesEquiv t (cert.physicalFiber.start cap)
            (cert.physicalFiber.retained cap)
            (cert.physicalFiber.distinguished cap) q).1) ∧
        TilingAwayTotalsScreen t (cert.physicalFiber.start cap)
          (cert.physicalFiber.retained cap) (cert.physicalFiber.distinguished cap)
          (cert.physicalFiber.upper cap)
          (fun ell ↦ cert.physicalScreenedAccepts threshold width shell bound
            cap ell = true)
          ((splitTilingCoordinatesEquiv t (cert.physicalFiber.start cap)
            (cert.physicalFiber.retained cap)
            (cert.physicalFiber.distinguished cap) q).2) := by
  apply
    HLOZAllCreationCanonicalRefinement.allCreationScreenedPredicate_factorization_of_reconstructed
      supportData eta cap
      (fun ell ↦ cert.physicalScreenedAccepts threshold width shell bound
        cap ell = true) (q := q)
  intro q'
  dsimp only
  intro hselected hscreened
  have hbase := cert.physicalScreenedScreen_base threshold width shell bound
    cap _ hscreened
  rcases hbase with ⟨ell, hell, htotal⟩
  apply cert.recover cap q' hselected
  refine ⟨ell, ?_, htotal⟩
  exact @of_decide_eq_true (cert.baseProp cap ell)
    (Classical.propDecidable _) hell

private theorem screenMass_bool_coordinate_windows_pos
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

private theorem screenMass_base_pos
    (cert : StaticSupportRecoveryCertificate supportData eta)
    (baseLocalPos : ∀ cap
      (b : TilingAwayDomino t (cert.physicalFiber.start cap)
        (cert.physicalFiber.retained cap)
        (cert.physicalFiber.distinguished cap)),
      0 < ∑ v : Fin (cert.physicalFiber.upper cap b),
        if (v : ℕ) ∈ cert.baseWindow cap b then
          coordinateMass
            (tilingAwayPointMass (cap := cert.physicalFiber.coordinateCap cap) t
              (cert.physicalFiber.start cap)
              (cert.physicalFiber.retained cap)
              (cert.physicalFiber.distinguished cap))
            (cert.physicalFiber.upper cap) b v else 0) :
    ∀ cap, 0 < allCreationBoolScreenMass cert.physicalFiber
      cert.baseAccepts cap := by
  intro cap
  unfold allCreationBoolScreenMass
  exact @screenMass_bool_coordinate_windows_pos
    (TilingAwayDomino t (cert.physicalFiber.start cap)
      (cert.physicalFiber.retained cap)
      (cert.physicalFiber.distinguished cap))
    (instFintypeTilingAwayDomino t (cert.physicalFiber.start cap)
      (cert.physicalFiber.retained cap)
      (cert.physicalFiber.distinguished cap))
    (fun a b ↦ Subtype.instDecidableEq a b)
    (tilingAwayPointMass (cap := cert.physicalFiber.coordinateCap cap) t
      (cert.physicalFiber.start cap) (cert.physicalFiber.retained cap)
      (cert.physicalFiber.distinguished cap))
    (cert.physicalFiber.upper cap) (cert.baseAccepts cap)
    (cert.baseWindow cap)
    (fun ell ↦ by
      change cert.baseAccepts cap ell = true ↔ cert.baseProp cap ell
      simp only [StaticSupportRecoveryCertificate.baseAccepts,
        decide_eq_true_eq])
    (baseLocalPos cap)

/-- Construct an exact physical-window refinement on one static-support
atom.  The cap monotonicity and path-event cover are deliberately kept as
deterministic inputs; the product bound is derived internally from screen
inclusion and is never a probability premise. -/
noncomputable def physicalRefinement
    (cert : StaticSupportRecoveryCertificate supportData eta)
    (piece next : Set WalkPath) (threshold : ℕ → ℕ)
    (width shell bound : ℕ)
    (atom_subset_piece : orientedAllCreationSupportTraceAtom
      t o m k supportAt eta.1.1 eta.1.2 ⊆ piece)
    (baseLocalPos : ∀ cap
      (b : TilingAwayDomino t (cert.physicalFiber.start cap)
        (cert.physicalFiber.retained cap)
        (cert.physicalFiber.distinguished cap)),
      0 < ∑ v : Fin (cert.physicalFiber.upper cap b),
        if (v : ℕ) ∈ cert.baseWindow cap b then
          coordinateMass
            (tilingAwayPointMass (cap := cert.physicalFiber.coordinateCap cap) t
              (cert.physicalFiber.start cap)
              (cert.physicalFiber.retained cap)
              (cert.physicalFiber.distinguished cap))
            (cert.physicalFiber.upper cap) b v else 0)
    (monotone_screened : Monotone fun cap ↦
      walkLift (prefixedTilingPreStoppingFiberEvent
        (cert.physicalFiber.stoppingTime cap)
        (cert.physicalFiber.initial cap) t (cert.physicalFiber.start cap)
        (cert.physicalFiber.retained cap)
        (cert.physicalFiber.coordinateCap cap) (cert.physicalFiber.tail cap)
        (cert.physicalScreenedPredicate threshold width shell bound cap)))
    (transition_covered : piece ∩ next ⊆ ⋃ cap,
      walkLift (prefixedTilingPreStoppingFiberEvent
        (cert.physicalFiber.stoppingTime cap)
        (cert.physicalFiber.initial cap) t (cert.physicalFiber.start cap)
        (cert.physicalFiber.retained cap)
        (cert.physicalFiber.coordinateCap cap) (cert.physicalFiber.tail cap)
        (cert.physicalScreenedPredicate threshold width shell bound cap))) :
    OrientedAllCreationConditionalRefinementData cert.physicalFiber piece next
      1 where
  basePredicate := cert.physicalBasePredicate
  screenedPredicate := cert.physicalScreenedPredicate threshold width shell bound
  base_subset_atom := fun _cap _q hq ↦ hq.1
  screened_subset_basePredicate := by
    intro cap q hq
    exact ⟨hq.1, cert.physicalScreenedScreen_base threshold width shell bound
      cap _ hq.2⟩
  baseAccepts := cert.baseAccepts
  screenedAccepts := cert.physicalScreenedAccepts threshold width shell bound
  screened_subset_base := by
    intro cap ell hell
    have hprop : cert.physicalScreenedProp threshold width shell bound cap ell := by
      simpa only [physicalScreenedAccepts, decide_eq_true_eq] using hell
    simpa only [StaticSupportRecoveryCertificate.baseAccepts,
      decide_eq_true_eq] using hprop.1
  base_factorization := by
    intro cap q
    simpa only [OrientedAllCreationPrefixedStoppedCoordinateSpec.retainedCount]
      using cert.physicalBase_factorization cap q
  screened_factorization := by
    intro cap q
    simpa only [OrientedAllCreationPrefixedStoppedCoordinateSpec.retainedCount]
      using cert.physicalScreened_factorization threshold width shell bound cap q
  base_mass_pos := cert.screenMass_base_pos baseLocalPos
  base_subset_piece := by
    intro cap s hs
    apply atom_subset_piece
    apply cert.physicalFiber.atom_sound cap
    exact ⟨hs.1, prefixedTilingPreStoppingFiberEvent_mono
      (cert.physicalFiber.stoppingTime cap) (cert.physicalFiber.initial cap) t
      (cert.physicalFiber.start cap) (cert.physicalFiber.retained cap)
      (cert.physicalFiber.tail cap) (fun _q hq ↦ hq.1) hs.2⟩
  monotone_screened := monotone_screened
  transition_covered := transition_covered
  product_bound := by
    intro cap
    rw [ENNReal.toReal_one]
    apply @conditionalScreenMass_le_one_of_subset
      (TilingAwayDomino t (cert.physicalFiber.start cap)
        (cert.physicalFiber.retained cap)
        (cert.physicalFiber.distinguished cap))
      (instFintypeTilingAwayDomino t (cert.physicalFiber.start cap)
        (cert.physicalFiber.retained cap)
        (cert.physicalFiber.distinguished cap))
      (fun a b ↦ Subtype.instDecidableEq a b)
      (tilingAwayPointMass (cap := cert.physicalFiber.coordinateCap cap) t
        (cert.physicalFiber.start cap) (cert.physicalFiber.retained cap)
        (cert.physicalFiber.distinguished cap))
      (cert.physicalFiber.upper cap)
      (fun ell ↦ cert.baseAccepts cap ell = true)
      (fun ell ↦ cert.physicalScreenedAccepts threshold width shell bound
        cap ell = true)
      (fun ell ↦ instDecidableEqBool (cert.baseAccepts cap ell) true)
      (fun ell ↦ instDecidableEqBool
        (cert.physicalScreenedAccepts threshold width shell bound cap ell) true)
    · intro b v
      exact tilingAwayExactTotalMass_nonneg t
        (cert.physicalFiber.start cap) (cert.physicalFiber.retained cap)
        (cert.physicalFiber.distinguished cap) b v
    · intro ell hell
      have hprop : cert.physicalScreenedProp threshold width shell bound cap ell := by
        simpa only [physicalScreenedAccepts, decide_eq_true_eq] using hell
      simpa only [StaticSupportRecoveryCertificate.baseAccepts,
        decide_eq_true_eq] using hprop.1
    · exact cert.screenMass_base_pos baseLocalPos cap

/-- Add the checked physical one-coordinate comparison to the exact
refinement and obtain the cofinal physical-interface tail. -/
noncomputable def physicalInterfaceTailData
    (cert : StaticSupportRecoveryCertificate supportData eta)
    (piece next : Set WalkPath) (threshold : ℕ → ℕ)
    (width shell bound : ℕ)
    (atom_subset_piece : orientedAllCreationSupportTraceAtom
      t o m k supportAt eta.1.1 eta.1.2 ⊆ piece)
    (baseLocalPos : ∀ cap
      (b : TilingAwayDomino t (cert.physicalFiber.start cap)
        (cert.physicalFiber.retained cap)
        (cert.physicalFiber.distinguished cap)),
      0 < ∑ v : Fin (cert.physicalFiber.upper cap b),
        if (v : ℕ) ∈ cert.baseWindow cap b then
          coordinateMass
            (tilingAwayPointMass (cap := cert.physicalFiber.coordinateCap cap) t
              (cert.physicalFiber.start cap)
              (cert.physicalFiber.retained cap)
              (cert.physicalFiber.distinguished cap))
            (cert.physicalFiber.upper cap) b v else 0)
    (monotone_screened : Monotone fun cap ↦
      walkLift (prefixedTilingPreStoppingFiberEvent
        (cert.physicalFiber.stoppingTime cap)
        (cert.physicalFiber.initial cap) t (cert.physicalFiber.start cap)
        (cert.physicalFiber.retained cap)
        (cert.physicalFiber.coordinateCap cap) (cert.physicalFiber.tail cap)
        (cert.physicalScreenedPredicate threshold width shell bound cap)))
    (transition_covered : piece ∩ next ⊆ ⋃ cap,
      walkLift (prefixedTilingPreStoppingFiberEvent
        (cert.physicalFiber.stoppingTime cap)
        (cert.physicalFiber.initial cap) t (cert.physicalFiber.start cap)
        (cert.physicalFiber.retained cap)
        (cert.physicalFiber.coordinateCap cap) (cert.physicalFiber.tail cap)
        (cert.physicalScreenedPredicate threshold width shell bound cap)))
    (capStart : ℕ)
    (window_ratio_inter_base : ∀ cap, capStart ≤ cap →
      ∀ (b : TilingAwayDomino t (cert.physicalFiber.start cap)
        (cert.physicalFiber.retained cap)
        (cert.physicalFiber.distinguished cap)),
      (∑ v : Fin (cert.physicalFiber.upper cap b),
        if (v : ℕ) ∈ physicalDeficitFailureWindow m width
              (Fintype.card (TilingCoordinatesAt t
                (cert.physicalFiber.start cap)
                (cert.physicalFiber.retained cap) b.1)) (shell + 1) ∧
            (v : ℕ) ∈ cert.baseWindow cap b then
          coordinateMass
            (tilingAwayPointMass (cap := cert.physicalFiber.coordinateCap cap) t
              (cert.physicalFiber.start cap)
              (cert.physicalFiber.retained cap)
              (cert.physicalFiber.distinguished cap))
            (cert.physicalFiber.upper cap) b v else 0) ≤
        (4 / 3 : ℝ) *
          ∑ v : Fin (cert.physicalFiber.upper cap b),
            if (v : ℕ) ∈ physicalDeficitFailureWindow m width
                  (Fintype.card (TilingCoordinatesAt t
                    (cert.physicalFiber.start cap)
                    (cert.physicalFiber.retained cap) b.1)) shell ∧
                (v : ℕ) ∈ cert.baseWindow cap b then
              coordinateMass
                (tilingAwayPointMass
                  (cap := cert.physicalFiber.coordinateCap cap) t
                  (cert.physicalFiber.start cap)
                  (cert.physicalFiber.retained cap)
                  (cert.physicalFiber.distinguished cap))
                (cert.physicalFiber.upper cap) b v else 0) :
    OrientedAllCreationConditionalPhysicalInterfaceTailData
      cert.physicalFiber piece next threshold width shell bound where
  refinement := cert.physicalRefinement piece next threshold width shell bound
    atom_subset_piece baseLocalPos monotone_screened transition_covered
  capStart := capStart
  baseWindow := cert.baseWindow
  baseAccepts_iff := by
    intro cap ell
    change cert.baseAccepts cap ell = true ↔ cert.baseProp cap ell
    simp only [StaticSupportRecoveryCertificate.baseAccepts,
      decide_eq_true_eq]
  screenedAccepts_iff := by
    intro cap ell
    change cert.physicalScreenedAccepts threshold width shell bound cap ell =
      true ↔ cert.physicalScreenedProp threshold width shell bound cap ell
    simp only [physicalScreenedAccepts, decide_eq_true_eq]
  baseLocalPos := fun cap _hcap b ↦ baseLocalPos cap b
  window_ratio_inter_base := window_ratio_inter_base

end StaticSupportRecoveryCertificate

end

end Erdos1165.HLOZPrefixedAllCreationStaticSupportAggregateRefinement
