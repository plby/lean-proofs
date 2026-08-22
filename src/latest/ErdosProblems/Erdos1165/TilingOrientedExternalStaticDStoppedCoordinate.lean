/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.TilingOrientedExternalAllCreationStoppedCoordinate

/-!
# Coarse external stopped fibres with an independent static split

The trace atom fixes only the physical oriented external word.  It does not
fix current favorites or either source/replacement `V₂` support.  A static
distinguished set `D` is then chosen independently for the finite-coordinate
split.  In particular `D = ∅` makes every represented domino an away
coordinate, which is the denominator-free carrier used for absolute Theta
screens and is also a valid common cross-clock carrier.
-/

open MeasureTheory Set

namespace Erdos1165.TilingOrientedExternalStaticDStoppedCoordinate

open FiniteDominoProductLaw HLOZPathEvents LazyDecomposition
open TilingCappedMarginalization TilingConditionalCappedMarginalization
open TilingOrientedAllCreationConcreteFamily
open TilingOrientedExternalAllCreationStoppedCoordinate
open TilingOrientedShellZeroSourcePartition
open TilingPrefixedStoppedProductDisintegration
open TilingSpatialInsertionFiber VariableStoppedTracePartition

noncomputable section

abbrev DominoTiling := Tilings.Tiling

def externalOnlySupportAt (_s : WalkPath) (_n : ℕ) : Finset Point := ∅

theorem externalOnlySupportData
    (t : DominoTiling) (o : Orientation) (m k : ℕ) :
    OrientedAllCreationSupportSelectorData t o m k externalOnlySupportAt where
  measurableAtCreation := measurable_const
  prefix_invariant := by intros; rfl
  represented := by
    intro s n hvalid
    exact Finset.empty_subset _

/-- The exact valid creation atom fixing only the complete physical external
word. -/
def orientedExternalOnlyCreationTraceAtom (t : DominoTiling)
    (o : Orientation) (m k : ℕ) (z : OrientedTilingTypedExternalWordCode t) :
    Set WalkPath :=
  {s | s ∈ validStepWalk ∧ ReachesThreshold s m k ∧
    fixedOrientedTypedExternalWordCode t o (creationTimeNat m k s) s = z}

theorem orientedExternalOnlyCreationTraceAtom_eq_supportAtom
    (t : DominoTiling) (o : Orientation) (m k : ℕ)
    (z : OrientedTilingTypedExternalWordCode t) :
    orientedExternalOnlyCreationTraceAtom t o m k z =
      orientedExternalAllCreationSupportTraceAtom t o m k
        externalOnlySupportAt z ∅ := by
  rw [orientedExternalAllCreationSupportTraceAtom_eq]
  ext s
  simp only [orientedExternalOnlyCreationTraceAtom, Set.mem_ofPred_eq,
    externalOnlySupportAt]
  tauto

abbrev SupportedIndex (t : DominoTiling) (o : Orientation) (m k : ℕ) :=
  {z : OrientedTilingTypedExternalWordCode t //
    (orientedExternalOnlyCreationTraceAtom t o m k z).Nonempty}

noncomputable def toSupportedSupportIndex
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    (eta : SupportedIndex t o m k) :
    TilingOrientedExternalAllCreationStoppedCoordinate.SupportedIndex
      t o m k externalOnlySupportAt := by
  refine ⟨⟨eta.1, ∅⟩, ?_⟩
  rw [← orientedExternalOnlyCreationTraceAtom_eq_supportAtom]
  exact eta.2

/-- The constructed physical-prefix fibre for a coarse external atom. -/
noncomputable def coarseFiber
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    (eta : SupportedIndex t o m k) :=
  concreteFiber o m k externalOnlySupportAt
    (externalOnlySupportData t o m k) (toSupportedSupportIndex eta)

/-- Distinguished projection after re-splitting the coarse atom by an
independent static set `D`. -/
def staticSelected
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    (eta : SupportedIndex t o m k) (D : Finset Point)
    (_hD : D ⊆ tilingExternalDominoBases t eta.1.start eta.1.retained)
    (cap : ℕ)
    (d : TilingDistinguishedCoordinates
      (cap := (coarseFiber eta).coordinateCap cap)
      t eta.1.start eta.1.retained D) : Prop :=
  ∃ a, let q :=
      (splitTilingCoordinatesEquiv t eta.1.start eta.1.retained D).symm (d, a)
    (coarseFiber eta).atomPredicate cap q ∧
      PrefixedTilingStoppingAccepted ((coarseFiber eta).stoppingTime cap)
        eta.1.initial.1 t eta.1.start eta.1.retained (fun j ↦ (q j : ℕ))
          eta.1.tail.1

/-- Direct factorization for any reconstructed away screen.  The reverse
direction receives the complete screen proof; no strict-only recovery is
accepted. -/
theorem coarseExternalScreenedPredicate_factorization
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    (eta : SupportedIndex t o m k) (D : Finset Point)
    (hD : D ⊆ tilingExternalDominoBases t eta.1.start eta.1.retained)
    (cap : ℕ)
    (upper : TilingAwayDomino t eta.1.start eta.1.retained D → ℕ)
    (accepts : TruncatedTotals upper → Prop)
    (recover : ∀
      (q : TilingCappedCoordinates eta.1.retainedCount
        ((coarseFiber eta).coordinateCap cap)),
      staticSelected eta D hD cap
          ((splitTilingCoordinatesEquiv t eta.1.start eta.1.retained D q).1) →
        TilingAwayTotalsScreen t eta.1.start eta.1.retained D upper accepts
            ((splitTilingCoordinatesEquiv t eta.1.start eta.1.retained D q).2) →
          (coarseFiber eta).atomPredicate cap q ∧
            PrefixedTilingStoppingAccepted ((coarseFiber eta).stoppingTime cap)
              eta.1.initial.1 t eta.1.start eta.1.retained
                (fun j ↦ (q j : ℕ)) eta.1.tail.1)
    (q : TilingCappedCoordinates eta.1.retainedCount
      ((coarseFiber eta).coordinateCap cap)) :
    ((coarseFiber eta).atomPredicate cap q ∧
        TilingAwayTotalsScreen t eta.1.start eta.1.retained D upper accepts
          ((splitTilingCoordinatesEquiv t eta.1.start eta.1.retained D q).2)) ∧
      PrefixedTilingStoppingAccepted ((coarseFiber eta).stoppingTime cap)
        eta.1.initial.1 t eta.1.start eta.1.retained (fun j ↦ (q j : ℕ))
          eta.1.tail.1 ↔
    staticSelected eta D hD cap
        ((splitTilingCoordinatesEquiv t eta.1.start eta.1.retained D q).1) ∧
      TilingAwayTotalsScreen t eta.1.start eta.1.retained D upper accepts
        ((splitTilingCoordinatesEquiv t eta.1.start eta.1.retained D q).2) := by
  constructor
  · rintro ⟨⟨hatom, hscreen⟩, haccepted⟩
    refine ⟨?_, hscreen⟩
    refine ⟨(splitTilingCoordinatesEquiv t eta.1.start eta.1.retained D q).2,
      ?_⟩
    rw [Equiv.symm_apply_apply]
    exact ⟨hatom, haccepted⟩
  · rintro ⟨hselected, hscreen⟩
    have hr := recover q hselected hscreen
    exact ⟨⟨hr.1, hscreen⟩, hr.2⟩

end

end Erdos1165.TilingOrientedExternalStaticDStoppedCoordinate
