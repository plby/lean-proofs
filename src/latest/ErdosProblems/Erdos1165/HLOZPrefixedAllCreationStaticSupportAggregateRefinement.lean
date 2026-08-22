/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.HLOZPrefixedAllCreationAggregateSharpTail

/-!
# Aggregate refinement on an exact `(external word, static support)` atom

The chosen-candidate recovery certificate used for Proposition 4.9 cannot
serve as the denominator of the positive-interface product: choosing an away
domino forces the static support to be nonempty.  Exact static-support atoms,
however, may have empty support.

This file gives the aggregate screen its own prefix-correct recovery
certificate.  Its broad acceptor is a coordinatewise window on the exact
`(z,S)` carrier and contains no chosen point.  Thus it applies uniformly to
empty and nonempty supports.  From the one pathwise recovery implication it
derives both stopped-fibre factorizations, broad-product positivity, and the
finite-cap conditional cost-one refinement.  The cofinal sharp product bound
is then supplied by the existing aggregate random-total theorem.
-/

open MeasureTheory Set
open scoped ENNReal

namespace Erdos1165.HLOZPrefixedAllCreationStaticSupportAggregateRefinement

open FiniteDominoProductLaw
open HLOZAllCreationCofinalConditionalSharpWindow
open HLOZPrefixedAllCreationAggregateSharpTail
open HLOZProposition48Candidates
open LazyDecomposition TilingCappedMarginalization
open TilingConditionalCappedMarginalization
open TilingOrientedAllCreationConcreteFamily
open TilingOrientedAllCreationStoppedCoordinate
open TilingOrientedSupportAwayCoordinates
open TilingPrefixedStoppedProductDisintegration
open TilingSpatialInsertionFiber VariableStoppedTracePartition

noncomputable section

abbrev DominoTiling := Tilings.Tiling

attribute [local instance] Classical.propDecidable

abbrev ConcreteFiber
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    {supportAt : WalkPath → ℕ → Finset Point}
    (supportData : OrientedAllCreationSupportSelectorData t o m k supportAt)
    (eta : OrientedAllCreationSupportedAtomIndex t o m k supportAt) :=
  (orientedAllCreationConcreteFamily
    t o m k supportAt supportData).fiber eta

/-- The exact pathwise recovery needed by an aggregate positive-interface
screen.  Unlike the candidate recovery certificate, this record never
chooses an away domino and therefore remains meaningful when `eta.1.2 = ∅`.

The broad denominator is explicitly coordinatewise.  This is exactly the
form required by the conditional random-total product theorem; it is not an
assumed event probability or product estimate. -/
structure StaticSupportRecoveryCertificate
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    {supportAt : WalkPath → ℕ → Finset Point}
    (supportData : OrientedAllCreationSupportSelectorData t o m k supportAt)
    (eta : OrientedAllCreationSupportedAtomIndex t o m k supportAt) where
  baseWindow : ∀ cap,
    TilingAwayDomino t ((ConcreteFiber supportData eta).start cap)
      ((ConcreteFiber supportData eta).retained cap)
      ((ConcreteFiber supportData eta).distinguished cap) → Finset ℕ
  recover : ∀ cap
    (q : TilingCappedCoordinates eta.1.1.external.retainedCount
      ((ConcreteFiber supportData eta).coordinateCap cap)),
    let fiber := ConcreteFiber supportData eta
    fiber.selected cap
        ((splitTilingCoordinatesEquiv t (fiber.start cap)
          (fiber.retained cap) (fiber.distinguished cap) q).1) →
      TilingAwayTotalsScreen t (fiber.start cap) (fiber.retained cap)
          (fiber.distinguished cap) (fiber.upper cap)
          (fun ell ↦ ∀ b, (ell b : ℕ) ∈ baseWindow cap b)
          ((splitTilingCoordinatesEquiv t (fiber.start cap)
            (fiber.retained cap) (fiber.distinguished cap) q).2) →
        fiber.atomPredicate cap q ∧
          PrefixedTilingStoppingAccepted (fiber.stoppingTime cap)
            (fiber.initial cap) t (fiber.start cap) (fiber.retained cap)
            (fun j ↦ (q j : ℕ)) (fiber.tail cap)

namespace StaticSupportRecoveryCertificate

variable
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    {supportAt : WalkPath → ℕ → Finset Point}
    {supportData : OrientedAllCreationSupportSelectorData t o m k supportAt}
    {eta : OrientedAllCreationSupportedAtomIndex t o m k supportAt}

private abbrev fiber
    (_cert : StaticSupportRecoveryCertificate supportData eta) :=
  ConcreteFiber supportData eta

def baseProp
    (cert : StaticSupportRecoveryCertificate supportData eta) (cap : ℕ)
    (ell : TruncatedTotals (cert.fiber.upper cap)) : Prop :=
  ∀ b, (ell b : ℕ) ∈ cert.baseWindow cap b

noncomputable def baseAccepts
    (cert : StaticSupportRecoveryCertificate supportData eta) (cap : ℕ) :
    TruncatedTotals (cert.fiber.upper cap) → Bool := fun ell ↦
  decide (cert.baseProp cap ell)

def screenedProp
    (cert : StaticSupportRecoveryCertificate supportData eta)
    (threshold : ℕ → ℕ) (shell bound cap : ℕ)
    (ell : TruncatedTotals (cert.fiber.upper cap)) : Prop :=
  cert.baseProp cap ell ∧
    allCreationRandomTotalThresholdedUpperTail cert.fiber cap
      (fun b (v : Fin (cert.fiber.upper cap b)) ↦
        (v : ℕ) ∈ HLOZSharpWindowProductClosure.activeUpperFailureWindow m
          (Fintype.card (TilingCoordinatesAt t
            (cert.fiber.start cap) (cert.fiber.retained cap) b.1)))
      (fun b (v : Fin (cert.fiber.upper cap b)) ↦
        (v : ℕ) ∈ HLOZSharpWindowProductClosure.activeLowerFailureWindow m
          (Fintype.card (TilingCoordinatesAt t
            (cert.fiber.start cap) (cert.fiber.retained cap) b.1)))
      threshold shellGrowth48 shell bound ell

noncomputable def screenedAccepts
    (cert : StaticSupportRecoveryCertificate supportData eta)
    (threshold : ℕ → ℕ) (shell bound cap : ℕ) :
    TruncatedTotals (cert.fiber.upper cap) → Bool := fun ell ↦
  decide (cert.screenedProp threshold shell bound cap ell)

private noncomputable def basePredicate
    (cert : StaticSupportRecoveryCertificate supportData eta) (cap : ℕ)
    (q : TilingCappedCoordinates eta.1.1.external.retainedCount
      (cert.fiber.coordinateCap cap)) : Prop :=
  cert.fiber.atomPredicate cap q ∧
    TilingAwayTotalsScreen t (cert.fiber.start cap)
      (cert.fiber.retained cap) (cert.fiber.distinguished cap)
      (cert.fiber.upper cap) (fun ell ↦ cert.baseAccepts cap ell = true)
      ((splitTilingCoordinatesEquiv t (cert.fiber.start cap)
        (cert.fiber.retained cap) (cert.fiber.distinguished cap) q).2)

private noncomputable def screenedPredicate
    (cert : StaticSupportRecoveryCertificate supportData eta)
    (threshold : ℕ → ℕ) (shell bound cap : ℕ)
    (q : TilingCappedCoordinates eta.1.1.external.retainedCount
      (cert.fiber.coordinateCap cap)) : Prop :=
  cert.fiber.atomPredicate cap q ∧
    TilingAwayTotalsScreen t (cert.fiber.start cap)
      (cert.fiber.retained cap) (cert.fiber.distinguished cap)
      (cert.fiber.upper cap)
      (fun ell ↦ cert.screenedAccepts threshold shell bound cap ell = true)
      ((splitTilingCoordinatesEquiv t (cert.fiber.start cap)
        (cert.fiber.retained cap) (cert.fiber.distinguished cap) q).2)

private theorem screenedScreen_base
    (cert : StaticSupportRecoveryCertificate supportData eta)
    (threshold : ℕ → ℕ) (shell bound cap : ℕ)
    (a : TilingAwayCoordinates (cap := cert.fiber.coordinateCap cap)
      t (cert.fiber.start cap) (cert.fiber.retained cap)
        (cert.fiber.distinguished cap))
    (h : TilingAwayTotalsScreen t (cert.fiber.start cap)
      (cert.fiber.retained cap) (cert.fiber.distinguished cap)
      (cert.fiber.upper cap)
      (fun ell ↦ cert.screenedAccepts threshold shell bound cap ell = true) a) :
    TilingAwayTotalsScreen t (cert.fiber.start cap)
      (cert.fiber.retained cap) (cert.fiber.distinguished cap)
      (cert.fiber.upper cap) (fun ell ↦ cert.baseAccepts cap ell = true) a := by
  rcases h with ⟨ell, hell, htotal⟩
  refine ⟨ell, ?_, htotal⟩
  have hprop : cert.screenedProp threshold shell bound cap ell := by
    simpa only [screenedAccepts, decide_eq_true_eq] using hell
  simpa only [baseAccepts, decide_eq_true_eq] using hprop.1

private theorem base_factorization
    (cert : StaticSupportRecoveryCertificate supportData eta) (cap : ℕ)
    (q : TilingCappedCoordinates eta.1.1.external.retainedCount
      (cert.fiber.coordinateCap cap)) :
    cert.basePredicate cap q ∧
        PrefixedTilingStoppingAccepted (cert.fiber.stoppingTime cap)
          (cert.fiber.initial cap) t (cert.fiber.start cap)
          (cert.fiber.retained cap) (fun j ↦ (q j : ℕ))
          (cert.fiber.tail cap) ↔
      cert.fiber.selected cap
          ((splitTilingCoordinatesEquiv t (cert.fiber.start cap)
            (cert.fiber.retained cap) (cert.fiber.distinguished cap) q).1) ∧
        TilingAwayTotalsScreen t (cert.fiber.start cap)
          (cert.fiber.retained cap) (cert.fiber.distinguished cap)
          (cert.fiber.upper cap) (fun ell ↦ cert.baseAccepts cap ell = true)
          ((splitTilingCoordinatesEquiv t (cert.fiber.start cap)
            (cert.fiber.retained cap) (cert.fiber.distinguished cap) q).2) := by
  apply
    HLOZAllCreationCanonicalRefinement.allCreationScreenedPredicate_factorization_of_reconstructed
    supportData eta cap (fun ell ↦ cert.baseAccepts cap ell = true) (q := q)
  intro q'
  dsimp only
  intro hselected hscreen
  apply cert.recover cap q' hselected
  rcases hscreen with ⟨ell, hell, htotal⟩
  refine ⟨ell, ?_, htotal⟩
  exact @of_decide_eq_true (cert.baseProp cap ell)
    (Classical.propDecidable _) hell

private theorem screened_factorization
    (cert : StaticSupportRecoveryCertificate supportData eta)
    (threshold : ℕ → ℕ) (shell bound cap : ℕ)
    (q : TilingCappedCoordinates eta.1.1.external.retainedCount
      (cert.fiber.coordinateCap cap)) :
    cert.screenedPredicate threshold shell bound cap q ∧
        PrefixedTilingStoppingAccepted (cert.fiber.stoppingTime cap)
          (cert.fiber.initial cap) t (cert.fiber.start cap)
          (cert.fiber.retained cap) (fun j ↦ (q j : ℕ))
          (cert.fiber.tail cap) ↔
      cert.fiber.selected cap
          ((splitTilingCoordinatesEquiv t (cert.fiber.start cap)
            (cert.fiber.retained cap) (cert.fiber.distinguished cap) q).1) ∧
        TilingAwayTotalsScreen t (cert.fiber.start cap)
          (cert.fiber.retained cap) (cert.fiber.distinguished cap)
          (cert.fiber.upper cap)
          (fun ell ↦ cert.screenedAccepts threshold shell bound cap ell = true)
          ((splitTilingCoordinatesEquiv t (cert.fiber.start cap)
            (cert.fiber.retained cap) (cert.fiber.distinguished cap) q).2) := by
  apply
    HLOZAllCreationCanonicalRefinement.allCreationScreenedPredicate_factorization_of_reconstructed
    supportData eta cap
      (fun ell ↦ cert.screenedAccepts threshold shell bound cap ell = true)
      (q := q)
  intro q'
  dsimp only
  intro hselected hscreened
  have hbase := cert.screenedScreen_base threshold shell bound cap _ hscreened
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
      (b : TilingAwayDomino t (cert.fiber.start cap)
        (cert.fiber.retained cap) (cert.fiber.distinguished cap)),
      0 < ∑ v : Fin (cert.fiber.upper cap b),
        if (v : ℕ) ∈ cert.baseWindow cap b then
          coordinateMass
            (tilingAwayPointMass (cap := cert.fiber.coordinateCap cap) t
              (cert.fiber.start cap) (cert.fiber.retained cap)
              (cert.fiber.distinguished cap))
            (cert.fiber.upper cap) b v else 0) :
    ∀ cap, 0 < allCreationBoolScreenMass cert.fiber cert.baseAccepts cap := by
  intro cap
  unfold allCreationBoolScreenMass
  exact @screenMass_bool_coordinate_windows_pos
    (TilingAwayDomino t (cert.fiber.start cap) (cert.fiber.retained cap)
      (cert.fiber.distinguished cap))
    (instFintypeTilingAwayDomino t (cert.fiber.start cap)
      (cert.fiber.retained cap) (cert.fiber.distinguished cap))
    (fun a b ↦ Subtype.instDecidableEq a b)
    (tilingAwayPointMass (cap := cert.fiber.coordinateCap cap) t
      (cert.fiber.start cap) (cert.fiber.retained cap)
      (cert.fiber.distinguished cap))
    (cert.fiber.upper cap) (cert.baseAccepts cap)
    (cert.baseWindow cap)
    (fun ell ↦ by
      change cert.baseAccepts cap ell = true ↔ cert.baseProp cap ell
      simp only [baseAccepts, decide_eq_true_eq])
    (baseLocalPos cap)

/-- The prefix-correct finite-cap aggregate refinement on one exact
`(z,S)` atom.  Its cost-one bound is derived from screen inclusion. -/
noncomputable def refinement
    (cert : StaticSupportRecoveryCertificate supportData eta)
    (piece next : Set WalkPath) (threshold : ℕ → ℕ)
    (shell bound : ℕ)
    (atom_subset_piece : orientedAllCreationSupportTraceAtom
      t o m k supportAt eta.1.1 eta.1.2 ⊆ piece)
    (baseLocalPos : ∀ cap
      (b : TilingAwayDomino t (cert.fiber.start cap)
        (cert.fiber.retained cap) (cert.fiber.distinguished cap)),
      0 < ∑ v : Fin (cert.fiber.upper cap b),
        if (v : ℕ) ∈ cert.baseWindow cap b then
          coordinateMass
            (tilingAwayPointMass (cap := cert.fiber.coordinateCap cap) t
              (cert.fiber.start cap) (cert.fiber.retained cap)
              (cert.fiber.distinguished cap))
            (cert.fiber.upper cap) b v else 0)
    (monotone_screened : Monotone fun cap ↦
      walkLift (prefixedTilingPreStoppingFiberEvent
        (cert.fiber.stoppingTime cap) (cert.fiber.initial cap) t
        (cert.fiber.start cap) (cert.fiber.retained cap)
        (cert.fiber.coordinateCap cap) (cert.fiber.tail cap)
        (cert.screenedPredicate threshold shell bound cap)))
    (transition_covered : piece ∩ next ⊆ ⋃ cap,
      walkLift (prefixedTilingPreStoppingFiberEvent
        (cert.fiber.stoppingTime cap) (cert.fiber.initial cap) t
        (cert.fiber.start cap) (cert.fiber.retained cap)
        (cert.fiber.coordinateCap cap) (cert.fiber.tail cap)
        (cert.screenedPredicate threshold shell bound cap))) :
    OrientedAllCreationConditionalRefinementData cert.fiber piece next 1 where
  basePredicate := cert.basePredicate
  screenedPredicate := cert.screenedPredicate threshold shell bound
  base_subset_atom := fun _cap _q hq ↦ hq.1
  screened_subset_basePredicate := by
    intro cap q hq
    exact ⟨hq.1, cert.screenedScreen_base threshold shell bound cap _ hq.2⟩
  baseAccepts := cert.baseAccepts
  screenedAccepts := cert.screenedAccepts threshold shell bound
  screened_subset_base := by
    intro cap ell hell
    have hprop : cert.screenedProp threshold shell bound cap ell := by
      simpa only [screenedAccepts, decide_eq_true_eq] using hell
    simpa only [baseAccepts, decide_eq_true_eq] using hprop.1
  base_factorization := by
    intro cap q
    simpa only [OrientedAllCreationPrefixedStoppedCoordinateSpec.retainedCount]
      using cert.base_factorization cap q
  screened_factorization := by
    intro cap q
    simpa only [OrientedAllCreationPrefixedStoppedCoordinateSpec.retainedCount]
      using cert.screened_factorization threshold shell bound cap q
  base_mass_pos := cert.screenMass_base_pos baseLocalPos
  base_subset_piece := by
    intro cap s hs
    apply atom_subset_piece
    apply cert.fiber.atom_sound cap
    exact ⟨hs.1, prefixedTilingPreStoppingFiberEvent_mono
      (cert.fiber.stoppingTime cap) (cert.fiber.initial cap) t
      (cert.fiber.start cap) (cert.fiber.retained cap)
      (cert.fiber.tail cap) (fun _q hq ↦ hq.1) hs.2⟩
  monotone_screened := monotone_screened
  transition_covered := transition_covered
  product_bound := by
    intro cap
    rw [ENNReal.toReal_one]
    apply @conditionalScreenMass_le_one_of_subset
      (TilingAwayDomino t (cert.fiber.start cap) (cert.fiber.retained cap)
        (cert.fiber.distinguished cap))
      (instFintypeTilingAwayDomino t (cert.fiber.start cap)
        (cert.fiber.retained cap) (cert.fiber.distinguished cap))
      (fun a b ↦ Subtype.instDecidableEq a b)
      (tilingAwayPointMass (cap := cert.fiber.coordinateCap cap) t
        (cert.fiber.start cap) (cert.fiber.retained cap)
        (cert.fiber.distinguished cap))
      (cert.fiber.upper cap)
      (fun ell ↦ cert.baseAccepts cap ell = true)
      (fun ell ↦ cert.screenedAccepts threshold shell bound cap ell = true)
      (fun ell ↦ instDecidableEqBool (cert.baseAccepts cap ell) true)
      (fun ell ↦ instDecidableEqBool
        (cert.screenedAccepts threshold shell bound cap ell) true)
    · intro b v
      exact tilingAwayExactTotalMass_nonneg t
        (cert.fiber.start cap) (cert.fiber.retained cap)
        (cert.fiber.distinguished cap) b v
    · intro ell hell
      have hprop : cert.screenedProp threshold shell bound cap ell := by
        simpa only [screenedAccepts, decide_eq_true_eq] using hell
      simpa only [baseAccepts, decide_eq_true_eq] using hprop.1
    · exact cert.screenMass_base_pos baseLocalPos cap

/-- Package the exact `(z,S)` recovery and deterministic sharp-window facts
as the aggregate local tail consumed by `CofinalLocalWindowData.toCofinalData`.
No candidate or nonempty-support hypothesis occurs in this constructor. -/
noncomputable def cofinalLocalWindowData
    (cert : StaticSupportRecoveryCertificate supportData eta)
    (piece next : Set WalkPath) (threshold : ℕ → ℕ)
    (shell bound : ℕ)
    (atom_subset_piece : orientedAllCreationSupportTraceAtom
      t o m k supportAt eta.1.1 eta.1.2 ⊆ piece)
    (baseLocalPos : ∀ cap
      (b : TilingAwayDomino t (cert.fiber.start cap)
        (cert.fiber.retained cap) (cert.fiber.distinguished cap)),
      0 < ∑ v : Fin (cert.fiber.upper cap b),
        if (v : ℕ) ∈ cert.baseWindow cap b then
          coordinateMass
            (tilingAwayPointMass (cap := cert.fiber.coordinateCap cap) t
              (cert.fiber.start cap) (cert.fiber.retained cap)
              (cert.fiber.distinguished cap))
            (cert.fiber.upper cap) b v else 0)
    (monotone_screened : Monotone fun cap ↦
      walkLift (prefixedTilingPreStoppingFiberEvent
        (cert.fiber.stoppingTime cap) (cert.fiber.initial cap) t
        (cert.fiber.start cap) (cert.fiber.retained cap)
        (cert.fiber.coordinateCap cap) (cert.fiber.tail cap)
        (cert.screenedPredicate threshold shell bound cap)))
    (transition_covered : piece ∩ next ⊆ ⋃ cap,
      walkLift (prefixedTilingPreStoppingFiberEvent
        (cert.fiber.stoppingTime cap) (cert.fiber.initial cap) t
        (cert.fiber.start cap) (cert.fiber.retained cap)
        (cert.fiber.coordinateCap cap) (cert.fiber.tail cap)
        (cert.screenedPredicate threshold shell bound cap)))
    (capStart : ℕ)
    (active : ∀ cap, capStart ≤ cap → ∀
      (b : TilingAwayDomino t (cert.fiber.start cap)
        (cert.fiber.retained cap) (cert.fiber.distinguished cap)),
      m / 2 ≤ Fintype.card (TilingCoordinatesAt t
        (cert.fiber.start cap) (cert.fiber.retained cap) b.1))
    (upper_mem_base : ∀ cap, capStart ≤ cap → ∀ b
      (v : Fin (cert.fiber.upper cap b)),
      (v : ℕ) ∈ HLOZSharpWindowProductClosure.activeUpperFailureWindow m
          (Fintype.card (TilingCoordinatesAt t (cert.fiber.start cap)
            (cert.fiber.retained cap) b.1)) →
        (v : ℕ) ∈ cert.baseWindow cap b)
    (lower_mem_base : ∀ cap, capStart ≤ cap → ∀ b
      (v : Fin (cert.fiber.upper cap b)),
      (v : ℕ) ∈ HLOZSharpWindowProductClosure.activeLowerFailureWindow m
          (Fintype.card (TilingCoordinatesAt t (cert.fiber.start cap)
            (cert.fiber.retained cap) b.1)) →
        (v : ℕ) ∈ cert.baseWindow cap b)
    (upper_lt_truncation : ∀ cap, capStart ≤ cap → ∀
      (b : TilingAwayDomino t (cert.fiber.start cap)
        (cert.fiber.retained cap) (cert.fiber.distinguished cap)) v,
      v ∈ HLOZSharpWindowProductClosure.activeUpperFailureWindow m
          (Fintype.card (TilingCoordinatesAt t (cert.fiber.start cap)
            (cert.fiber.retained cap) b.1)) → v < cert.fiber.upper cap b)
    (lower_lt_truncation : ∀ cap, capStart ≤ cap → ∀
      (b : TilingAwayDomino t (cert.fiber.start cap)
        (cert.fiber.retained cap) (cert.fiber.distinguished cap)) v,
      v ∈ HLOZSharpWindowProductClosure.activeLowerFailureWindow m
          (Fintype.card (TilingCoordinatesAt t (cert.fiber.start cap)
            (cert.fiber.retained cap) b.1)) → v < cert.fiber.upper cap b)
    (upper_le_cap : ∀ cap, capStart ≤ cap → ∀
      (b : TilingAwayDomino t (cert.fiber.start cap)
        (cert.fiber.retained cap) (cert.fiber.distinguished cap)) v,
      v ∈ HLOZSharpWindowProductClosure.activeUpperFailureWindow m
          (Fintype.card (TilingCoordinatesAt t (cert.fiber.start cap)
            (cert.fiber.retained cap) b.1)) → v ≤ cert.fiber.coordinateCap cap)
    (lower_le_cap : ∀ cap, capStart ≤ cap → ∀
      (b : TilingAwayDomino t (cert.fiber.start cap)
        (cert.fiber.retained cap) (cert.fiber.distinguished cap)) v,
      v ∈ HLOZSharpWindowProductClosure.activeLowerFailureWindow m
          (Fintype.card (TilingCoordinatesAt t (cert.fiber.start cap)
            (cert.fiber.retained cap) b.1)) → v ≤ cert.fiber.coordinateCap cap) :
    CofinalLocalWindowData cert.fiber piece next threshold shell bound where
  refinement := cert.refinement piece next threshold shell bound
    atom_subset_piece baseLocalPos monotone_screened transition_covered
  capStart := capStart
  baseWindow := cert.baseWindow
  baseAccepts_iff := by
    intro cap ell
    change cert.baseAccepts cap ell = true ↔ cert.baseProp cap ell
    simp only [baseAccepts, decide_eq_true_eq]
  screenedAccepts_iff := by
    intro cap ell
    change cert.screenedAccepts threshold shell bound cap ell = true ↔
      cert.screenedProp threshold shell bound cap ell
    simp only [screenedAccepts, decide_eq_true_eq]
  active := active
  upper_mem_base := upper_mem_base
  lower_mem_base := lower_mem_base
  upper_lt_truncation := upper_lt_truncation
  lower_lt_truncation := lower_lt_truncation
  upper_le_cap := upper_le_cap
  lower_le_cap := lower_le_cap

end StaticSupportRecoveryCertificate

end

end Erdos1165.HLOZPrefixedAllCreationStaticSupportAggregateRefinement
