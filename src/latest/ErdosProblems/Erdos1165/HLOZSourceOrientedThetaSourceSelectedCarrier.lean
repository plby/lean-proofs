/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.HLOZSourceOrientedThetaSourceSlotAcceptedPath
import ErdosProblems.Erdos1165.HLOZSourceOrientedThetaOneAwayProduct

/-!
# Source-window selected carriers

For a one-away source slot, a distinguished assignment is retained only if
it has an accepted witness whose exposed total is itself in the rank-stable
source Theta window.  The older broad existential selector is insufficient:
its witness may lie above level `m`, in which case replacing it by a source
total can change the creation rank.
-/

namespace Erdos1165.HLOZSourceOrientedThetaSourceSelectedCarrier

open FiniteDominoProductLaw
open HLOZSourceOrientedThetaExternalSourceAccepted
open HLOZSourceOrientedThetaOneAwayProduct
open LazyDecomposition TilingCappedMarginalization
open TilingOrientedExternalAllCreationStoppedCoordinate
open TilingOrientedShellZeroSourcePartition
open TilingOrientedSupportAwayCoordinates
open TilingPrefixedStoppedProductDisintegration
open TilingSpatialInsertionFiber VariableStoppedTracePartition

noncomputable section

abbrev DominoTiling := Tilings.Tiling

/-- A distinguished assignment with a literal accepted I1 witness. -/
def externalSourceSelected
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    {supportAt : WalkPath → ℕ → Finset Point} {S : Finset Point}
    {z : OrientedTilingTypedExternalWordCode t}
    (data : Spec t o m k supportAt S z)
    (w externalLow externalHigh cap : ℕ)
    (d : TilingDistinguishedCoordinates (cap := data.coordinateCap cap)
      t z.start z.retained
        (supportComplementDistinguished t z.start z.retained S)) : Prop :=
  ∃ a ell,
    let q := (splitTilingCoordinatesEquiv t z.start z.retained
      (supportComplementDistinguished t z.start z.retained S)).symm (d, a)
    data.atomPredicate cap q ∧
      PrefixedTilingStoppingAccepted (data.stoppingTime cap) z.initial.1 t
        z.start z.retained (fun j ↦ (q j : ℕ)) z.tail.1 ∧
      externalSourceThetaAccepts data w externalLow externalHigh cap ell = true ∧
      ∀ b, tilingAwayTotal t z.start z.retained
        (supportComplementDistinguished t z.start z.retained S) a b = ell b

/-- The same stopped fibre with only its distinguished selector strengthened.
All atom, stopping, cap, and away-total data remain definitionally equal. -/
noncomputable def withExternalSourceSelected
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    {supportAt : WalkPath → ℕ → Finset Point} {S : Finset Point}
    {z : OrientedTilingTypedExternalWordCode t}
    (data : Spec t o m k supportAt S z)
    (w externalLow externalHigh : ℕ) : Spec t o m k supportAt S z where
  coordinateCap := data.coordinateCap
  capStart := data.capStart
  coordinateCap_eq := data.coordinateCap_eq
  totalCap := data.totalCap
  totalCap_le_capStart := data.totalCap_le_capStart
  retainedCount_le_totalCap := data.retainedCount_le_totalCap
  stoppingTime := data.stoppingTime
  isStoppingTime := data.isStoppingTime
  atomPredicate := data.atomPredicate
  support_represented := data.support_represented
  selected := fun cap ↦ externalSourceSelected data w externalLow externalHigh cap
  upper := data.upper
  upper_pos := data.upper_pos
  totalCap_lt_upper := data.totalCap_lt_upper
  atom_measurable := data.atom_measurable
  atom_sound := data.atom_sound
  atom_complete := data.atom_complete
  atom_monotone := data.atom_monotone

@[simp] theorem withExternalSourceSelected_coordinateCap
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    {supportAt : WalkPath → ℕ → Finset Point} {S : Finset Point}
    {z : OrientedTilingTypedExternalWordCode t}
    (data : Spec t o m k supportAt S z)
    (w externalLow externalHigh cap : ℕ) :
    (withExternalSourceSelected data w externalLow externalHigh).coordinateCap cap =
      data.coordinateCap cap := rfl

@[simp] theorem withExternalSourceSelected_stoppingTime
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    {supportAt : WalkPath → ℕ → Finset Point} {S : Finset Point}
    {z : OrientedTilingTypedExternalWordCode t}
    (data : Spec t o m k supportAt S z)
    (w externalLow externalHigh cap : ℕ) :
    (withExternalSourceSelected data w externalLow externalHigh).stoppingTime cap =
      data.stoppingTime cap := rfl

@[simp] theorem withExternalSourceSelected_atomPredicate
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    {supportAt : WalkPath → ℕ → Finset Point} {S : Finset Point}
    {z : OrientedTilingTypedExternalWordCode t}
    (data : Spec t o m k supportAt S z)
    (w externalLow externalHigh cap : ℕ)
    (q : TilingCappedCoordinates z.retainedCount (data.coordinateCap cap)) :
    (withExternalSourceSelected data w externalLow externalHigh).atomPredicate
        cap q ↔ data.atomPredicate cap q :=
  Iff.rfl

@[simp] theorem withExternalSourceSelected_upper
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    {supportAt : WalkPath → ℕ → Finset Point} {S : Finset Point}
    {z : OrientedTilingTypedExternalWordCode t}
    (data : Spec t o m k supportAt S z)
    (w externalLow externalHigh cap : ℕ) (b) :
    (withExternalSourceSelected data w externalLow externalHigh).upper cap b =
      data.upper cap b := rfl

/-- Exact factorization for the strengthened carrier.  Unlike the generic
external theorem, the forward selector is constructed from the actual
source-bad away vector carried by the screened predicate itself. -/
theorem externalSourceSelectedPredicate_factorization
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    {supportAt : WalkPath → ℕ → Finset Point} {S : Finset Point}
    {z : OrientedTilingTypedExternalWordCode t}
    (data : Spec t o m k supportAt S z)
    (w externalLow externalHigh cap : ℕ)
    (q : TilingCappedCoordinates z.retainedCount (data.coordinateCap cap)) :
    let sourceData := withExternalSourceSelected data w externalLow externalHigh
    externalAcceptedSourceThetaPredicate sourceData w externalLow externalHigh
          cap q ∧
        PrefixedTilingStoppingAccepted (sourceData.stoppingTime cap)
          z.initial.1 t z.start z.retained (fun j ↦ (q j : ℕ)) z.tail.1 ↔
      sourceData.selected cap
          ((splitTilingCoordinatesEquiv t z.start z.retained
            (supportComplementDistinguished t z.start z.retained S) q).1) ∧
        TilingAwayTotalsScreen t z.start z.retained
          (supportComplementDistinguished t z.start z.retained S)
          (sourceData.upper cap)
          (externalAcceptedSourceThetaAtTotals sourceData w externalLow
            externalHigh cap)
          ((splitTilingCoordinatesEquiv t z.start z.retained
            (supportComplementDistinguished t z.start z.retained S) q).2) := by
  classical
  let sourceData := withExternalSourceSelected data w externalLow externalHigh
  constructor
  · rintro ⟨⟨hatom, hscreen⟩, haccepted⟩
    rcases hscreen with ⟨ell, hell, htotal⟩
    refine ⟨?_, ⟨ell, hell, htotal⟩⟩
    change externalSourceSelected data w externalLow externalHigh cap
      ((splitTilingCoordinatesEquiv t z.start z.retained
        (supportComplementDistinguished t z.start z.retained S) q).1)
    refine ⟨(splitTilingCoordinatesEquiv t z.start z.retained
      (supportComplementDistinguished t z.start z.retained S) q).2, ?_⟩
    refine ⟨ell, ?_⟩
    have hq : (splitTilingCoordinatesEquiv t z.start z.retained
        (supportComplementDistinguished t z.start z.retained S)).symm
          ((splitTilingCoordinatesEquiv t z.start z.retained
            (supportComplementDistinguished t z.start z.retained S) q).1,
           (splitTilingCoordinatesEquiv t z.start z.retained
            (supportComplementDistinguished t z.start z.retained S) q).2) = q := by
      rw [Prod.eta, Equiv.symm_apply_apply]
    dsimp only
    rw [hq]
    exact ⟨hatom, haccepted, hell.2, htotal⟩
  · rintro ⟨hselected, hscreen⟩
    rcases hscreen with ⟨ell, hell, htotal⟩
    have hrecover := hell.1 q hselected htotal
    exact ⟨⟨hrecover.1, ⟨ell, hell, htotal⟩⟩, hrecover.2⟩

end

end Erdos1165.HLOZSourceOrientedThetaSourceSelectedCarrier
