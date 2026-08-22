/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.TilingOrientedExternalStaticDStoppedCoordinate
import ErdosProblems.Erdos1165.TilingPrefixedHonestAcceptedCreationCrossClock

/-!
# Honest accepted-creation screens on a static external split

An external retained-word atom does not by itself make stopping acceptance
independent of the away coordinates.  The base screen in this file therefore
records the complete accepted-creation condition.  Its forward and recovery
fields are deterministic statements on reconstructed coordinates.  Once
they are supplied, both the base factorization and every narrower
Theta/shell screen are consequences, rather than additional factorization
premises.
-/

open Set

namespace Erdos1165.TilingOrientedExternalStaticDAcceptedCreation

open FiniteDominoProductLaw LazyDecomposition
open TilingCappedMarginalization TilingConditionalCappedMarginalization
open TilingOrientedExternalAllCreationStoppedCoordinate
open TilingOrientedExternalStaticDStoppedCoordinate
open TilingPrefixedHonestAcceptedCreationCrossClock
open TilingPrefixedStoppedProductDisintegration
open TilingSpatialInsertionFiber

noncomputable section

abbrev DominoTiling := Tilings.Tiling

/-- Complete deterministic accepted-creation data on one coarse external
atom and one static distinguished carrier.  `baseAccepts` is intentionally
not `True`: it must include every away-coordinate condition needed to
preserve the creation clock. -/
structure StaticDAcceptedCreationData
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    (eta : SupportedIndex t o m k) (D : Finset Point)
    (hD : D ⊆ tilingExternalDominoBases t eta.1.start eta.1.retained) where
  upper : ∀ _cap, TilingAwayDomino t eta.1.start eta.1.retained D → ℕ
  upper_pos : ∀ cap b, 0 < upper cap b
  baseAccepts : ∀ cap, TruncatedTotals (upper cap) → Prop
  forward : ∀ cap
    (q : TilingCappedCoordinates eta.1.retainedCount
      ((coarseFiber eta).coordinateCap cap)),
    (coarseFiber eta).atomPredicate cap q ∧
        PrefixedTilingStoppingAccepted ((coarseFiber eta).stoppingTime cap)
          eta.1.initial.1 t eta.1.start eta.1.retained
          (fun j ↦ (q j : ℕ)) eta.1.tail.1 →
      TilingAwayTotalsScreen t eta.1.start eta.1.retained D (upper cap)
        (baseAccepts cap)
        ((splitTilingCoordinatesEquiv t eta.1.start eta.1.retained D q).2)
  recover : ∀ cap
    (q : TilingCappedCoordinates eta.1.retainedCount
      ((coarseFiber eta).coordinateCap cap)),
    staticSelected eta D hD cap
        ((splitTilingCoordinatesEquiv t eta.1.start eta.1.retained D q).1) →
      TilingAwayTotalsScreen t eta.1.start eta.1.retained D (upper cap)
          (baseAccepts cap)
          ((splitTilingCoordinatesEquiv t eta.1.start eta.1.retained D q).2) →
        (coarseFiber eta).atomPredicate cap q ∧
          PrefixedTilingStoppingAccepted ((coarseFiber eta).stoppingTime cap)
            eta.1.initial.1 t eta.1.start eta.1.retained
            (fun j ↦ (q j : ℕ)) eta.1.tail.1

namespace StaticDAcceptedCreationData

variable
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    {eta : SupportedIndex t o m k} {D : Finset Point}
    {hD : D ⊆ tilingExternalDominoBases t eta.1.start eta.1.retained}

/-- The complete accepted-creation factorization. -/
theorem base_factorization
    (data : StaticDAcceptedCreationData eta D hD) (cap : ℕ)
    (q : TilingCappedCoordinates eta.1.retainedCount
      ((coarseFiber eta).coordinateCap cap)) :
    (coarseFiber eta).atomPredicate cap q ∧
        PrefixedTilingStoppingAccepted ((coarseFiber eta).stoppingTime cap)
          eta.1.initial.1 t eta.1.start eta.1.retained
          (fun j ↦ (q j : ℕ)) eta.1.tail.1 ↔
      staticSelected eta D hD cap
          ((splitTilingCoordinatesEquiv t eta.1.start eta.1.retained D q).1) ∧
        TilingAwayTotalsScreen t eta.1.start eta.1.retained D
          (data.upper cap) (data.baseAccepts cap)
          ((splitTilingCoordinatesEquiv t eta.1.start eta.1.retained D q).2) := by
  constructor
  · intro hq
    refine ⟨?_, data.forward cap q hq⟩
    refine ⟨(splitTilingCoordinatesEquiv t eta.1.start eta.1.retained D q).2,
      ?_⟩
    rw [Equiv.symm_apply_apply]
    exact hq
  · rintro ⟨hselected, hscreen⟩
    exact data.recover cap q hselected hscreen

/-- A narrower accepted-coordinate predicate.  Its base atom is unchanged;
the full creation screen remains present through `screened ⊆ baseAccepts`. -/
def screenedPredicate
    (data : StaticDAcceptedCreationData eta D hD) (cap : ℕ)
    (screened : TruncatedTotals (data.upper cap) → Prop)
    (q : TilingCappedCoordinates eta.1.retainedCount
      ((coarseFiber eta).coordinateCap cap)) : Prop :=
  (coarseFiber eta).atomPredicate cap q ∧
    TilingAwayTotalsScreen t eta.1.start eta.1.retained D (data.upper cap)
      screened
      ((splitTilingCoordinatesEquiv t eta.1.start eta.1.retained D q).2)

/-- Every narrower screen has an exact stopped factorization.  This is the
form consumed by absolute Theta and by the source/replacement shell clocks. -/
theorem screened_factorization
    (data : StaticDAcceptedCreationData eta D hD) (cap : ℕ)
    (screened : TruncatedTotals (data.upper cap) → Prop)
    (hsub : ∀ ell, screened ell → data.baseAccepts cap ell)
    (q : TilingCappedCoordinates eta.1.retainedCount
      ((coarseFiber eta).coordinateCap cap)) :
    data.screenedPredicate cap screened q ∧
        PrefixedTilingStoppingAccepted ((coarseFiber eta).stoppingTime cap)
          eta.1.initial.1 t eta.1.start eta.1.retained
          (fun j ↦ (q j : ℕ)) eta.1.tail.1 ↔
      staticSelected eta D hD cap
          ((splitTilingCoordinatesEquiv t eta.1.start eta.1.retained D q).1) ∧
        TilingAwayTotalsScreen t eta.1.start eta.1.retained D
          (data.upper cap) screened
          ((splitTilingCoordinatesEquiv t eta.1.start eta.1.retained D q).2) := by
  apply coarseExternalScreenedPredicate_factorization eta D hD cap
    (data.upper cap) screened
  intro q' hselected hscreened
  apply data.recover cap q' hselected
  rcases hscreened with ⟨ell, hell, htotal⟩
  exact ⟨ell, hsub ell hell, htotal⟩

/-- The common specialization used when a consumer defines its screened
acceptor as the complete creation screen conjoined with an exceptional
coordinate predicate. -/
theorem and_screen_factorization
    (data : StaticDAcceptedCreationData eta D hD) (cap : ℕ)
    (exceptional : TruncatedTotals (data.upper cap) → Prop)
    (q : TilingCappedCoordinates eta.1.retainedCount
      ((coarseFiber eta).coordinateCap cap)) :
    data.screenedPredicate cap
          (fun ell ↦ data.baseAccepts cap ell ∧ exceptional ell) q ∧
        PrefixedTilingStoppingAccepted ((coarseFiber eta).stoppingTime cap)
          eta.1.initial.1 t eta.1.start eta.1.retained
          (fun j ↦ (q j : ℕ)) eta.1.tail.1 ↔
      staticSelected eta D hD cap
          ((splitTilingCoordinatesEquiv t eta.1.start eta.1.retained D q).1) ∧
        TilingAwayTotalsScreen t eta.1.start eta.1.retained D
          (data.upper cap)
          (fun ell ↦ data.baseAccepts cap ell ∧ exceptional ell)
          ((splitTilingCoordinatesEquiv t eta.1.start eta.1.retained D q).2) :=
  data.screened_factorization cap _ (fun _ h ↦ h.1) q

/-- Forget the external-atom construction and expose the accepted clock to
the generic honest cross-clock comparison. -/
noncomputable def toClock
    (data : StaticDAcceptedCreationData eta D hD) (cap : ℕ) :
    AcceptedCreationClockData (cap := (coarseFiber eta).coordinateCap cap)
      eta.1.initial.1 t eta.1.start eta.1.retained eta.1.tail.1 D
        (data.upper cap) where
  stoppingTime := (coarseFiber eta).stoppingTime cap
  predicate := (coarseFiber eta).atomPredicate cap
  selected := staticSelected eta D hD cap
  baseAccepts := data.baseAccepts cap
  forward := by
    intro q hq
    refine ⟨?_, data.forward cap q hq⟩
    refine ⟨(splitTilingCoordinatesEquiv t eta.1.start eta.1.retained D q).2,
      ?_⟩
    rw [Equiv.symm_apply_apply]
    exact hq
  recover := data.recover cap

end StaticDAcceptedCreationData

end

end Erdos1165.TilingOrientedExternalStaticDAcceptedCreation
