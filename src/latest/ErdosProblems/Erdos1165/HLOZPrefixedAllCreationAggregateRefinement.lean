/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.HLOZPrefixedAllCreationAggregateSharpTail

/-!
# Prefix-correct aggregate refinement on an all-creation atom

The prefix-correct canonical recovery certificate already supplies the
honest broad accepted-creation denominator.  Here its one-coordinate narrow
screen is replaced by the aggregate random-total upper tail used by the
positive-shell interface.  The harmless finite-cap cost one is derived from
screen inclusion and broad positivity.
-/

open MeasureTheory Set
open scoped ENNReal

namespace Erdos1165.HLOZPrefixedAllCreationAggregateRefinement

open FiniteDominoProductLaw
open HLOZAllCreationCanonicalRefinement
open HLOZAllCreationCofinalConditionalSharpWindow
open HLOZAllSixExactCoordinateProductClosure
open HLOZProposition48Candidates
open HLOZSharpProductNumerics HLOZSharpWindowProductClosure
open HLOZPrefixedAllCreationCanonicalDominantWindows
open HLOZPrefixedAllCreationCanonicalRefinement
open HLOZPrefixedAllCreationAggregateSharpTail
open LazyDecomposition ScreeningInstantiation SmallWindow
open TilingAwayNegativeBinomial
open TilingCappedMarginalization
open TilingConditionalCappedMarginalization
open TilingOrientedAllCreationConcreteFamily
open TilingOrientedAllCreationStoppedCoordinate
open TilingOrientedSupportAwayCoordinates
open TilingPrefixedStoppedProductDisintegration
open TilingSpatialInsertionFiber VariableStoppedTracePartition

noncomputable section

abbrev DominoTiling := Tilings.Tiling

abbrev CanonicalRecoveryCertificate
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    {supportAt : WalkPath → ℕ → Finset Point}
    (supportData : OrientedAllCreationSupportSelectorData t o m k supportAt)
    (eta : OrientedAllCreationSupportedAtomIndex t o m k supportAt)
    (candidate : Point) :=
  HLOZPrefixedAllCreationCanonicalRefinement.RecoveryCertificate
    supportData eta candidate

abbrev ConcreteFiber
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    {supportAt : WalkPath → ℕ → Finset Point}
    (supportData : OrientedAllCreationSupportSelectorData t o m k supportAt)
    (eta : OrientedAllCreationSupportedAtomIndex t o m k supportAt) :=
  HLOZPrefixedAllCreationCanonicalRefinement.ConcreteFiber supportData eta

/-! ## Exact aggregate acceptor -/

def aggregateScreenedProp
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    {supportAt : WalkPath → ℕ → Finset Point}
    {supportData : OrientedAllCreationSupportSelectorData t o m k supportAt}
    {eta : OrientedAllCreationSupportedAtomIndex t o m k supportAt}
    {candidate : Point}
    (cert : CanonicalRecoveryCertificate supportData eta candidate)
    (threshold : ℕ → ℕ) (shell bound cap : ℕ)
    (ell : TruncatedTotals ((ConcreteFiber supportData eta).upper cap)) : Prop :=
  (cert.parameters cap).toSpec.acceptedBaseProp ell ∧
    allCreationRandomTotalThresholdedUpperTail
      (ConcreteFiber supportData eta) cap
      (fun b (v : Fin ((ConcreteFiber supportData eta).upper cap b)) ↦
        (v : ℕ) ∈ HLOZSharpWindowProductClosure.activeUpperFailureWindow m
          (Fintype.card (TilingCoordinatesAt t
            ((ConcreteFiber supportData eta).start cap)
            ((ConcreteFiber supportData eta).retained cap) b.1)))
      (fun b (v : Fin ((ConcreteFiber supportData eta).upper cap b)) ↦
        (v : ℕ) ∈ HLOZSharpWindowProductClosure.activeLowerFailureWindow m
          (Fintype.card (TilingCoordinatesAt t
            ((ConcreteFiber supportData eta).start cap)
            ((ConcreteFiber supportData eta).retained cap) b.1)))
      threshold shellGrowth48 shell bound ell

noncomputable def aggregateScreenedAccepts
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    {supportAt : WalkPath → ℕ → Finset Point}
    {supportData : OrientedAllCreationSupportSelectorData t o m k supportAt}
    {eta : OrientedAllCreationSupportedAtomIndex t o m k supportAt}
    {candidate : Point}
    (cert : CanonicalRecoveryCertificate supportData eta candidate)
    (threshold : ℕ → ℕ) (shell bound cap : ℕ) :
    TruncatedTotals ((ConcreteFiber supportData eta).upper cap) → Bool := by
  classical
  exact fun ell ↦ decide
    (aggregateScreenedProp cert threshold shell bound cap ell)

namespace CanonicalRecoveryCertificate

variable
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    {supportAt : WalkPath → ℕ → Finset Point}
    {supportData : OrientedAllCreationSupportSelectorData t o m k supportAt}
    {eta : OrientedAllCreationSupportedAtomIndex t o m k supportAt}
    {candidate : Point}

private abbrev fiber
    (_cert : CanonicalRecoveryCertificate supportData eta candidate) :=
  ConcreteFiber supportData eta

/-- A candidate-style recovery certificate necessarily has a nonempty
static support: its parameters choose one away domino.  This records the
reason it cannot by itself cover empty `(z,S)` atoms in the aggregate
positive-interface partition. -/
theorem support_nonempty
    (cert : CanonicalRecoveryCertificate supportData eta candidate) :
    eta.1.2.Nonempty := by
  let b := (cert.parameters 0).chosen
  refine ⟨b.1.1, ?_⟩
  exact (away_mem_support_iff t (cert.fiber.start 0)
    (cert.fiber.retained 0) eta.1.2 b.1).1 b.2

private noncomputable def basePredicate
    (cert : CanonicalRecoveryCertificate supportData eta candidate) (cap : ℕ)
    (q : TilingCappedCoordinates eta.1.1.external.retainedCount
      (cert.fiber.coordinateCap cap)) : Prop :=
  cert.fiber.atomPredicate cap q ∧
    TilingAwayTotalsScreen t (cert.fiber.start cap)
      (cert.fiber.retained cap) (cert.fiber.distinguished cap)
      (cert.fiber.upper cap)
      (fun ell ↦ (cert.parameters cap).toSpec.acceptedBaseAccepts ell = true)
      ((splitTilingCoordinatesEquiv t (cert.fiber.start cap)
        (cert.fiber.retained cap) (cert.fiber.distinguished cap) q).2)

private noncomputable def screenedPredicate
    (cert : CanonicalRecoveryCertificate supportData eta candidate)
    (threshold : ℕ → ℕ) (shell bound cap : ℕ)
    (q : TilingCappedCoordinates eta.1.1.external.retainedCount
      (cert.fiber.coordinateCap cap)) : Prop :=
  cert.fiber.atomPredicate cap q ∧
    TilingAwayTotalsScreen t (cert.fiber.start cap)
      (cert.fiber.retained cap) (cert.fiber.distinguished cap)
      (cert.fiber.upper cap)
      (fun ell ↦ aggregateScreenedAccepts cert threshold shell bound cap ell = true)
      ((splitTilingCoordinatesEquiv t (cert.fiber.start cap)
        (cert.fiber.retained cap) (cert.fiber.distinguished cap) q).2)

private theorem screenedScreen_base
    (cert : CanonicalRecoveryCertificate supportData eta candidate)
    (threshold : ℕ → ℕ) (shell bound cap : ℕ)
    (a : TilingAwayCoordinates (cap := cert.fiber.coordinateCap cap)
      t (cert.fiber.start cap) (cert.fiber.retained cap)
        (cert.fiber.distinguished cap))
    (h : TilingAwayTotalsScreen t (cert.fiber.start cap)
      (cert.fiber.retained cap) (cert.fiber.distinguished cap)
      (cert.fiber.upper cap)
      (fun ell ↦ aggregateScreenedAccepts cert threshold shell bound cap ell = true)
      a) :
    TilingAwayTotalsScreen t (cert.fiber.start cap)
      (cert.fiber.retained cap) (cert.fiber.distinguished cap)
      (cert.fiber.upper cap)
      (fun ell ↦ (cert.parameters cap).toSpec.acceptedBaseAccepts ell = true)
      a := by
  rcases h with ⟨ell, hell, htotal⟩
  refine ⟨ell, ?_, htotal⟩
  have hprop : aggregateScreenedProp cert threshold shell bound cap ell := by
    simpa only [aggregateScreenedAccepts, decide_eq_true_eq] using hell
  simpa only [PrefixedCanonicalDominantCandidateWindowSpec.acceptedBaseAccepts,
    decide_eq_true_eq] using hprop.1

private theorem base_factorization
    (cert : CanonicalRecoveryCertificate supportData eta candidate) (cap : ℕ)
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
          (cert.fiber.upper cap)
          (fun ell ↦
            (cert.parameters cap).toSpec.acceptedBaseAccepts ell = true)
          ((splitTilingCoordinatesEquiv t (cert.fiber.start cap)
            (cert.fiber.retained cap) (cert.fiber.distinguished cap) q).2) := by
  exact allCreationScreenedPredicate_factorization_of_reconstructed
    supportData eta cap
    (fun ell ↦ (cert.parameters cap).toSpec.acceptedBaseAccepts ell = true)
    (cert.recover cap) q

private theorem screened_factorization
    (cert : CanonicalRecoveryCertificate supportData eta candidate)
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
          (fun ell ↦ aggregateScreenedAccepts cert threshold shell bound cap ell = true)
          ((splitTilingCoordinatesEquiv t (cert.fiber.start cap)
            (cert.fiber.retained cap) (cert.fiber.distinguished cap) q).2) := by
  apply allCreationScreenedPredicate_factorization_of_reconstructed
    supportData eta cap
    (fun ell ↦ aggregateScreenedAccepts cert threshold shell bound cap ell = true)
    (q := q)
  intro q'
  dsimp only
  intro hselected hscreened
  exact cert.recover cap q' hselected
    (cert.screenedScreen_base threshold shell bound cap _ hscreened)

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

/-- The broad stopped-creation denominator is positive as soon as its exact
coordinatewise presentation has positive mass in every coordinate.  This is
an identity in the literal finite product, not a path-space probability
premise. -/
theorem acceptedBaseScreenMass_pos_of_coordinate_windows
    (cert : CanonicalRecoveryCertificate supportData eta candidate)
    (baseWindow : ∀ cap,
      TilingAwayDomino t (cert.fiber.start cap) (cert.fiber.retained cap)
        (cert.fiber.distinguished cap) → Finset ℕ)
    (baseAccepts_iff : ∀ cap ell,
      (cert.parameters cap).toSpec.acceptedBaseAccepts ell = true ↔
        ∀ b, (ell b : ℕ) ∈ baseWindow cap b)
    (baseLocalPos : ∀ cap
      (b : TilingAwayDomino t (cert.fiber.start cap)
        (cert.fiber.retained cap) (cert.fiber.distinguished cap)),
      0 < ∑ v : Fin (cert.fiber.upper cap b),
        if (v : ℕ) ∈ baseWindow cap b then
          coordinateMass
            (tilingAwayPointMass (cap := cert.fiber.coordinateCap cap) t
              (cert.fiber.start cap) (cert.fiber.retained cap)
              (cert.fiber.distinguished cap))
            (cert.fiber.upper cap) b v else 0) :
    ∀ cap, 0 < allCreationBoolScreenMass cert.fiber
      (fun cap ↦ (cert.parameters cap).toSpec.acceptedBaseAccepts) cap := by
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
    (cert.fiber.upper cap)
    ((cert.parameters cap).toSpec.acceptedBaseAccepts)
    (baseWindow cap) (baseAccepts_iff cap) (baseLocalPos cap)

/-- Literal positivity of one broad coordinate window, derived from the
contained active lower sharp window and the exact capped negative-binomial
law.  This is the all-cap input needed by the stopped refinement; the sharp
ratio itself remains cofinal. -/
theorem acceptedBaseCoordinateMass_pos_of_lowerWindow
    (cert : CanonicalRecoveryCertificate supportData eta candidate)
    (harith : SharpWindowArithmeticAt m)
    (baseWindow : ∀ cap,
      TilingAwayDomino t (cert.fiber.start cap) (cert.fiber.retained cap)
        (cert.fiber.distinguished cap) → Finset ℕ)
    (cap : ℕ)
    (b : TilingAwayDomino t (cert.fiber.start cap)
      (cert.fiber.retained cap) (cert.fiber.distinguished cap))
    (active : m / 2 ≤ Fintype.card (TilingCoordinatesAt t
      (cert.fiber.start cap) (cert.fiber.retained cap) b.1))
    (lower_mem_base : ∀ (v : Fin (cert.fiber.upper cap b)),
      (v : ℕ) ∈ activeLowerFailureWindow m
          (Fintype.card (TilingCoordinatesAt t (cert.fiber.start cap)
            (cert.fiber.retained cap) b.1)) →
        (v : ℕ) ∈ baseWindow cap b)
    (lower_lt_truncation : ∀ v,
      v ∈ activeLowerFailureWindow m
          (Fintype.card (TilingCoordinatesAt t (cert.fiber.start cap)
            (cert.fiber.retained cap) b.1)) →
        v < cert.fiber.upper cap b)
    (lower_le_cap : ∀ v,
      v ∈ activeLowerFailureWindow m
          (Fintype.card (TilingCoordinatesAt t (cert.fiber.start cap)
            (cert.fiber.retained cap) b.1)) →
        v ≤ cert.fiber.coordinateCap cap) :
    0 < ∑ v : Fin (cert.fiber.upper cap b),
      if (v : ℕ) ∈ baseWindow cap b then
        coordinateMass
          (tilingAwayPointMass (cap := cert.fiber.coordinateCap cap) t
            (cert.fiber.start cap) (cert.fiber.retained cap)
            (cert.fiber.distinguished cap))
          (cert.fiber.upper cap) b v else 0 := by
  let i := Fintype.card (TilingCoordinatesAt t (cert.fiber.start cap)
    (cert.fiber.retained cap) b.1)
  have hiPos : 0 < i := (harith.2 i active).1
  have hwindowPos : 0 < windowMass i (activeLowerFailureWindow m i) := by
    rw [activeLowerFailureWindow_eq_of_active active]
    exact windowMass_pos hiPos (lowerFailureWindow_nonempty harith.1)
  have hdenPos : 0 < ∑ j : Fin (cert.fiber.upper cap b),
      tilingAwayPointMass (cap := cert.fiber.coordinateCap cap) t
        (cert.fiber.start cap) (cert.fiber.retained cap)
        (cert.fiber.distinguished cap) b j := by
    let v0 : Fin (cert.fiber.upper cap b) :=
      ⟨0, cert.fiber.upper_pos cap b⟩
    have hv0 : 0 < tilingAwayPointMass
        (cap := cert.fiber.coordinateCap cap) t
        (cert.fiber.start cap) (cert.fiber.retained cap)
        (cert.fiber.distinguished cap) b v0 := by
      simpa only [v0, tilingAwayPointMass] using
        tilingAwayExactTotalMass_zero_pos
          (cap := cert.fiber.coordinateCap cap) t
          (cert.fiber.start cap) (cert.fiber.retained cap)
          (cert.fiber.distinguished cap) b
    exact hv0.trans_le (Finset.single_le_sum
      (s := Finset.univ)
      (f := fun j : Fin (cert.fiber.upper cap b) ↦
        tilingAwayPointMass (cap := cert.fiber.coordinateCap cap) t
          (cert.fiber.start cap) (cert.fiber.retained cap)
          (cert.fiber.distinguished cap) b j)
      (fun j _ ↦ tilingAwayExactTotalMass_nonneg t
        (cert.fiber.start cap) (cert.fiber.retained cap)
        (cert.fiber.distinguished cap) b j)
      (Finset.mem_univ v0))
  have heq := sum_tilingAway_coordinateMass_window t
    (cert.fiber.start cap) (cert.fiber.retained cap)
    (cert.fiber.distinguished cap) (cert.fiber.upper cap) b
    (activeLowerFailureWindow m i) lower_lt_truncation lower_le_cap hiPos
  have hlower : 0 < ∑ v : Fin (cert.fiber.upper cap b),
      if (v : ℕ) ∈ activeLowerFailureWindow m i then
        coordinateMass
          (tilingAwayPointMass (cap := cert.fiber.coordinateCap cap) t
            (cert.fiber.start cap) (cert.fiber.retained cap)
            (cert.fiber.distinguished cap))
          (cert.fiber.upper cap) b v else 0 :=
    heq.symm ▸ div_pos hwindowPos hdenPos
  apply hlower.trans_le
  apply Finset.sum_le_sum
  intro v _hv
  by_cases hlowerMem : (v : ℕ) ∈ activeLowerFailureWindow m i
  · rw [if_pos hlowerMem, if_pos (lower_mem_base v hlowerMem)]
  · rw [if_neg hlowerMem]
    split
    · exact OrientedAllCreationConditionalSharpTailData.allCreationCoordinateMass_nonneg
        cap b v
    · exact le_rfl

/-- Prefix-correct aggregate refinement.  Broad positivity, monotonicity and
coverage are deterministic fibre facts; the unit product bound is derived. -/
noncomputable def aggregateRefinement
    (cert : CanonicalRecoveryCertificate supportData eta candidate)
    (piece next : Set WalkPath) (threshold : ℕ → ℕ)
    (shell bound : ℕ)
    (atom_subset_piece : orientedAllCreationSupportTraceAtom
      t o m k supportAt eta.1.1 eta.1.2 ⊆ piece)
    (base_mass_pos : ∀ cap, 0 < allCreationBoolScreenMass cert.fiber
      (fun cap ↦ (cert.parameters cap).toSpec.acceptedBaseAccepts) cap)
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
  baseAccepts := fun cap ↦ (cert.parameters cap).toSpec.acceptedBaseAccepts
  screenedAccepts := fun cap ↦
    aggregateScreenedAccepts cert threshold shell bound cap
  screened_subset_base := by
    intro cap ell hell
    have hprop : aggregateScreenedProp cert threshold shell bound cap ell := by
      simpa only [aggregateScreenedAccepts, decide_eq_true_eq] using hell
    simpa only [PrefixedCanonicalDominantCandidateWindowSpec.acceptedBaseAccepts,
      decide_eq_true_eq] using hprop.1
  base_factorization := cert.base_factorization
  screened_factorization := cert.screened_factorization threshold shell bound
  base_mass_pos := base_mass_pos
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
        (fun ell ↦
          (cert.parameters cap).toSpec.acceptedBaseAccepts ell = true)
        (fun ell ↦
          aggregateScreenedAccepts cert threshold shell bound cap ell = true)
      (fun ell ↦ instDecidableEqBool
        ((cert.parameters cap).toSpec.acceptedBaseAccepts ell) true)
      (fun ell ↦ instDecidableEqBool
        (aggregateScreenedAccepts cert threshold shell bound cap ell) true)
    · intro b v
      exact tilingAwayExactTotalMass_nonneg t
        (cert.fiber.start cap) (cert.fiber.retained cap)
        (cert.fiber.distinguished cap) b v
    · intro ell hell
      have hprop : aggregateScreenedProp cert threshold shell bound cap ell := by
        simpa only [aggregateScreenedAccepts, decide_eq_true_eq] using hell
      simpa only [PrefixedCanonicalDominantCandidateWindowSpec.acceptedBaseAccepts,
        decide_eq_true_eq] using hprop.1
    · exact base_mass_pos cap

/-- Prefix-correct aggregate refinement with broad positivity derived
coordinate by coordinate.  The caller supplies only the literal broad-window
identity and its local positive masses; no normalized product probability or
transition estimate is an input. -/
noncomputable def aggregateRefinementOfCoordinateWindows
    (cert : CanonicalRecoveryCertificate supportData eta candidate)
    (piece next : Set WalkPath) (threshold : ℕ → ℕ)
    (shell bound : ℕ)
    (atom_subset_piece : orientedAllCreationSupportTraceAtom
      t o m k supportAt eta.1.1 eta.1.2 ⊆ piece)
    (baseWindow : ∀ cap,
      TilingAwayDomino t (cert.fiber.start cap) (cert.fiber.retained cap)
        (cert.fiber.distinguished cap) → Finset ℕ)
    (baseAccepts_iff : ∀ cap ell,
      (cert.parameters cap).toSpec.acceptedBaseAccepts ell = true ↔
        ∀ b, (ell b : ℕ) ∈ baseWindow cap b)
    (baseLocalPos : ∀ cap
      (b : TilingAwayDomino t (cert.fiber.start cap)
        (cert.fiber.retained cap) (cert.fiber.distinguished cap)),
      0 < ∑ v : Fin (cert.fiber.upper cap b),
        if (v : ℕ) ∈ baseWindow cap b then
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
    OrientedAllCreationConditionalRefinementData cert.fiber piece next 1 :=
  cert.aggregateRefinement piece next threshold shell bound atom_subset_piece
    (cert.acceptedBaseScreenMass_pos_of_coordinate_windows
      baseWindow baseAccepts_iff baseLocalPos)
    monotone_screened transition_covered

/-- Smallest aggregate refinement constructor based directly on the literal
sharp windows.  Positivity of the broad finite product is reconstructed from
the active lower window in every coordinate, so even the local positive-mass
facts are not exposed as inputs. -/
noncomputable def aggregateRefinementOfSharpWindows
    (cert : CanonicalRecoveryCertificate supportData eta candidate)
    (harith : SharpWindowArithmeticAt m)
    (piece next : Set WalkPath) (threshold : ℕ → ℕ)
    (shell bound : ℕ)
    (atom_subset_piece : orientedAllCreationSupportTraceAtom
      t o m k supportAt eta.1.1 eta.1.2 ⊆ piece)
    (baseWindow : ∀ cap,
      TilingAwayDomino t (cert.fiber.start cap) (cert.fiber.retained cap)
        (cert.fiber.distinguished cap) → Finset ℕ)
    (baseAccepts_iff : ∀ cap ell,
      (cert.parameters cap).toSpec.acceptedBaseAccepts ell = true ↔
        ∀ b, (ell b : ℕ) ∈ baseWindow cap b)
    (active : ∀ cap
      (b : TilingAwayDomino t (cert.fiber.start cap)
        (cert.fiber.retained cap) (cert.fiber.distinguished cap)),
      m / 2 ≤ Fintype.card (TilingCoordinatesAt t
        (cert.fiber.start cap) (cert.fiber.retained cap) b.1))
    (lower_mem_base : ∀ cap
      (b : TilingAwayDomino t (cert.fiber.start cap)
        (cert.fiber.retained cap) (cert.fiber.distinguished cap))
      (v : Fin (cert.fiber.upper cap b)),
      (v : ℕ) ∈ activeLowerFailureWindow m
          (Fintype.card (TilingCoordinatesAt t (cert.fiber.start cap)
            (cert.fiber.retained cap) b.1)) →
        (v : ℕ) ∈ baseWindow cap b)
    (lower_lt_truncation : ∀ cap
      (b : TilingAwayDomino t (cert.fiber.start cap)
        (cert.fiber.retained cap) (cert.fiber.distinguished cap)) v,
      v ∈ activeLowerFailureWindow m
          (Fintype.card (TilingCoordinatesAt t (cert.fiber.start cap)
            (cert.fiber.retained cap) b.1)) →
        v < cert.fiber.upper cap b)
    (lower_le_cap : ∀ cap
      (b : TilingAwayDomino t (cert.fiber.start cap)
        (cert.fiber.retained cap) (cert.fiber.distinguished cap)) v,
      v ∈ activeLowerFailureWindow m
          (Fintype.card (TilingCoordinatesAt t (cert.fiber.start cap)
            (cert.fiber.retained cap) b.1)) →
        v ≤ cert.fiber.coordinateCap cap)
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
    OrientedAllCreationConditionalRefinementData cert.fiber piece next 1 :=
  cert.aggregateRefinementOfCoordinateWindows piece next threshold shell bound
    atom_subset_piece baseWindow baseAccepts_iff
    (fun cap b ↦ cert.acceptedBaseCoordinateMass_pos_of_lowerWindow harith
      baseWindow cap b (active cap b) (lower_mem_base cap b)
      (lower_lt_truncation cap b) (lower_le_cap cap b))
    monotone_screened transition_covered

end CanonicalRecoveryCertificate

end

end Erdos1165.HLOZPrefixedAllCreationAggregateRefinement
