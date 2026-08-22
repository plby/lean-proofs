/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.HLOZSourceOrientedThetaExternalAccepted
import ErdosProblems.Erdos1165.HLOZSourceOrientedThetaSlotSupport
import ErdosProblems.Erdos1165.HLOZPrefixedCanonicalSourceAtomRecovery
import ErdosProblems.Erdos1165.HLOZSourceOrientedThetaAcceptedCreationPath

/-!
# Path recovery for one retained-word Theta slot

This file begins the physical bridge from a singleton retained-word support
atom to the honest accepted product.  The external atom predicate is recovered
from stopping acceptance and the literal retained code; no current-favorite
datum is conditioned on.
-/

open Set

namespace Erdos1165.HLOZSourceOrientedThetaSlotAcceptedPath

open HLOZPathEvents HLOZSourceOrientedThetaAcceptedCreationPath
open HLOZSourceOrientedThetaSlotSupport LazyDecomposition
open TilingCappedMarginalization TilingConditionalCappedMarginalization
open TilingDistinguishedTraceInvariant
open TilingOrientedAllCreationConcreteFamily
open TilingOrientedAllCreationStoppedCoordinate
open TilingOrientedExternalAllCreationStoppedCoordinate
open TilingOrientedShellZeroSourcePartition
open TilingOrientedSupportAwayCoordinates
open TilingPrefixedStoppedProductDisintegration
open TilingSpatialInsertionFiber VariableStoppedTracePartition
open PreStoppingFiber StoppedInsertion

noncomputable section

abbrev DominoTiling := Tilings.Tiling

/-- On a constructed external fibre, membership in the atom together with
stopping acceptance always supplies the distinguished selector witness. -/
theorem concreteFiber_selected_of_atom_accepted
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    {supportAt : WalkPath → ℕ → Finset Point}
    (supportData : OrientedAllCreationSupportSelectorData t o m k supportAt)
    (eta : SupportedIndex t o m k supportAt) (cap : ℕ)
    (q : TilingCappedCoordinates eta.1.1.retainedCount
      ((concreteFiber o m k supportAt supportData eta).coordinateCap cap))
    (hq : (concreteFiber o m k supportAt supportData eta).atomPredicate cap q ∧
      PrefixedTilingStoppingAccepted
        ((concreteFiber o m k supportAt supportData eta).stoppingTime cap)
        eta.1.1.initial.1 t eta.1.1.start eta.1.1.retained
        (fun j ↦ (q j : ℕ)) eta.1.1.tail.1) :
    (concreteFiber o m k supportAt supportData eta).selected cap
      ((splitTilingCoordinatesEquiv t eta.1.1.start eta.1.1.retained
        (supportComplementDistinguished t eta.1.1.start eta.1.1.retained
          eta.1.2) q).1) := by
  classical
  change externalSelected o m k supportAt eta.1.2 eta.1.1
    ((concreteFiber o m k supportAt supportData eta).coordinateCap cap)
    ((splitTilingCoordinatesEquiv t eta.1.1.start eta.1.1.retained
      (supportComplementDistinguished t eta.1.1.start eta.1.1.retained
        eta.1.2) q).1)
  refine ⟨(splitTilingCoordinatesEquiv t eta.1.1.start eta.1.1.retained
    (supportComplementDistinguished t eta.1.1.start eta.1.1.retained
      eta.1.2) q).2, ?_⟩
  rw [Equiv.symm_apply_apply]
  exact hq

/-- Reconstructing any accepted coordinate vector in a nonempty external
creation atom gives back that exact external atom predicate. -/
theorem concreteFiber_atomPredicate_of_accepted
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    {supportAt : WalkPath → ℕ → Finset Point}
    (supportData : OrientedAllCreationSupportSelectorData t o m k supportAt)
    (supportOfCode : OrientedTilingTypedExternalWordCode t → Finset Point)
    (support_code : ∀ s n, supportAt s n = supportOfCode
      (fixedOrientedTypedExternalWordCode t o n s))
    (eta : SupportedIndex t o m k supportAt)
    (hm : 1 < m) (hk : 0 < k) (cap : ℕ)
    (q : TilingCappedCoordinates eta.1.1.retainedCount
      ((concreteFiber o m k supportAt supportData eta).coordinateCap cap))
    (haccepted : PrefixedTilingStoppingAccepted
      ((concreteFiber o m k supportAt supportData eta).stoppingTime cap)
      eta.1.1.initial.1 t eta.1.1.start eta.1.1.retained
      (fun j ↦ (q j : ℕ)) eta.1.1.tail.1) :
    (concreteFiber o m k supportAt supportData eta).atomPredicate cap q := by
  let z := eta.1.1
  let actualCap :=
    (concreteFiber o m k supportAt supportData eta).coordinateCap cap
  let qNat : Fin (z.retainedCount + 1) → ℕ := fun j ↦ (q j : ℕ)
  let v := prefixedTilingInsertionPrefixList z.initial.1 t z.start z.retained
    qNat z.tail.1
  let s := trajectory (extendPrefix (directionVectorOfList v))
  let favorite := (fixedOrientedAllCreationTraceCode t o v.length s).favorite
  have hlt : v.length < externalCoordinateCutoff z actualCap := by
    have hraw := prefixedInsertion_lt_orientedAllCreationCoordinateCutoff
      (withFavorite z favorite) actualCap q
    rw [orientedAllCreationCoordinateCutoff_withFavorite] at hraw
    exact hraw
  have hcreation : ThresholdCreation s m k v.length := by
    apply (truncatedLevelTime_eq_iff_thresholdCreation_of_lt_cutoff
      m k (externalCoordinateCutoff z actualCap) v.length _ hlt).mp
    exact haccepted
  have hcode : fixedOrientedTypedExternalWordCode t o v.length s = z := by
    have heta_nonempty :
        (TilingOrientedAllRepresentedExternalFiber.allRepresentedExternalCreationTraceAtom
          t o m k eta.1.1).Nonempty := by
      rcases eta.2 with ⟨s₀, hs₀⟩
      rw [orientedExternalAllCreationSupportTraceAtom_eq] at hs₀
      exact ⟨s₀, hs₀.1, hs₀.2.1, hs₀.2.2.1⟩
    have hraw := fixedCode_prefixedInsertion
      (⟨eta.1.1, heta_nonempty⟩ :
        TilingOrientedAllRepresentedExternalFiber.SupportedIndex t o m k)
      hm hk qNat
    simpa only [z, v, s, qNat] using hraw
  change externalStoppedAtomPredicate o m k supportAt eta.1.2 z actualCap q
  refine ⟨favorite, ?_⟩
  intro omega homega
  let somega := trajectory omega
  have hp : pathPrefix somega v.length = pathPrefix s v.length := by
    simpa only [somega, s, v, qNat, z] using
      (pathPrefix_eq_canonical_of_mem_prefixedTilingStoppedInsertionAtom
        z.initial.1 z.start z.retained qNat z.tail.1 omega homega)
  have homegaCreation : ThresholdCreation somega m k v.length :=
    (thresholdCreation_iff_of_pathPrefix_eq hp
      (Nat.le_refl v.length)).mpr hcreation
  have homegaTime : creationTimeNat m k somega = v.length :=
    creationTimeNat_eq_of_creation homegaCreation
  refine ⟨⟨trajectory_mem_validStepWalk omega,
    ⟨v.length, homegaCreation.1⟩, ?_⟩, ?_⟩
  · change fixedOrientedAllCreationTraceCode t o
      (creationTimeNat m k somega) somega = withFavorite z favorite
    rw [homegaTime]
    have htrace := fixedOrientedAllCreationTraceCode_eq_of_pathPrefix_eq
      t o hp
    calc
      fixedOrientedAllCreationTraceCode t o v.length somega =
          fixedOrientedAllCreationTraceCode t o v.length s := htrace
      _ = withFavorite z favorite := by
        rw [OrientedAllCreationTraceCode.mk.injEq]
        exact ⟨hcode, rfl⟩
  · have hsupport :
        supportAt somega (creationTimeNat m k somega) = eta.1.2 := by
      rw [homegaTime, support_code]
      rw [fixedOrientedTypedExternalWordCode_eq_of_pathPrefix_eq t o hp, hcode]
      rcases eta.2 with ⟨s₀, hs₀⟩
      rw [orientedExternalAllCreationSupportTraceAtom_eq] at hs₀
      have hcode₀ := hs₀.2.2.1
      have hsupp₀ := hs₀.2.2.2
      rw [support_code, hcode₀] at hsupp₀
      simpa only [z] using hsupp₀
    change supportAt (trajectory omega)
      (creationTimeNat m k (trajectory omega)) = eta.1.2
    exact hsupport

end

end Erdos1165.HLOZSourceOrientedThetaSlotAcceptedPath
