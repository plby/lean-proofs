/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.HLOZPositiveInterfacePairActualDeltaWalkCap

/-!
# Monotonicity of positive-interface pair source caps

The exact pair source carrier is stable when its coordinate cap is enlarged.
The proof casts both the selected source completion and the screened
replacement without changing any natural-valued insertion coordinate.
-/

open Set

namespace Erdos1165.HLOZPositiveInterfacePairSourceCapMonotone

open FiniteDominoProductLaw HeterogeneousProductTail
open HLOZPositiveInterfacePairActualDeltaCapBound
open HLOZPositiveInterfacePairActualDeltaSelected
open HLOZPositiveInterfacePairActualDeltaWalkCap
open HLOZPositiveInterfacePairSupportFiber
open HLOZPositiveInterfacePairWeightedScreen
open HLOZProposition48Candidates
open LazyDecomposition PreStoppingFiber StoppedInsertion
open TilingCappedMarginalization
open TilingOrientedAllCreationConcreteFamily
open TilingOrientedExternalAllCreationStoppedCoordinate
open TilingOrientedShellZeroSourcePartition
open TilingOrientedSupportAwayCoordinates
open TilingPrefixedStoppedProductDisintegration
open TilingSpatialInsertionFiber
open TilingVariableStoppedTracePartition
open VariableStoppedTracePartition

noncomputable section

abbrev DominoTiling := Tilings.Tiling

attribute [local instance] Classical.propDecidable

private theorem positiveInterfaceExternalPairCoordinateCap_mono
    {t : DominoTiling} {o : Orientation}
    {m k externalThreshold width shell : ℕ}
    (eta : PositiveInterfaceExternalPairSupportedIndex t o m k
      externalThreshold width shell) {cap cap' : ℕ} (hcap : cap ≤ cap') :
    (PositiveInterfaceExternalPairFiber eta).coordinateCap cap ≤
      (PositiveInterfaceExternalPairFiber eta).coordinateCap cap' := by
  rw [(PositiveInterfaceExternalPairFiber eta).coordinateCap_eq,
    (PositiveInterfaceExternalPairFiber eta).coordinateCap_eq]
  omega

private noncomputable def pairCapFavorite
    {t : DominoTiling} {o : Orientation}
    {m k externalThreshold width shell : ℕ}
    (eta : PositiveInterfaceExternalPairSupportedIndex t o m k
      externalThreshold width shell) : TilingCreationFavoriteData := by
  let s := Classical.choose eta.2
  exact (TilingOrientedAllCreationStoppedCoordinate.fixedOrientedAllCreationTraceCode
    t o (creationTimeNat m k s) s).favorite

/-- The value-preserving coordinate embedding, stated without adding
irrelevant current-favorite data to an external history. -/
private def castPositiveInterfaceExternalPairCoordinates
    {t : DominoTiling} {o : Orientation}
    {m k externalThreshold width shell : ℕ}
    (eta : PositiveInterfaceExternalPairSupportedIndex t o m k
      externalThreshold width shell) {cap cap' : ℕ} (hcap : cap ≤ cap')
    (q : TilingCappedCoordinates eta.1.1.retainedCount
      ((PositiveInterfaceExternalPairFiber eta).coordinateCap cap)) :
    TilingCappedCoordinates eta.1.1.retainedCount
      ((PositiveInterfaceExternalPairFiber eta).coordinateCap cap') :=
  fun j ↦ Fin.castLE (Nat.succ_le_succ
    (positiveInterfaceExternalPairCoordinateCap_mono eta hcap)) (q j)

@[simp] private theorem coe_castPositiveInterfaceExternalPairCoordinates
    {t : DominoTiling} {o : Orientation}
    {m k externalThreshold width shell : ℕ}
    (eta : PositiveInterfaceExternalPairSupportedIndex t o m k
      externalThreshold width shell) {cap cap' : ℕ} (hcap : cap ≤ cap')
    (q : TilingCappedCoordinates eta.1.1.retainedCount
      ((PositiveInterfaceExternalPairFiber eta).coordinateCap cap)) (j) :
    ((castPositiveInterfaceExternalPairCoordinates eta hcap q j : Fin
      ((PositiveInterfaceExternalPairFiber eta).coordinateCap cap' + 1)) : ℕ) =
      (q j : ℕ) := rfl

private theorem positiveInterfaceExternalPairAtomPredicate_cast
    {t : DominoTiling} {o : Orientation}
    {m k externalThreshold width shell : ℕ}
    (eta : PositiveInterfaceExternalPairSupportedIndex t o m k
      externalThreshold width shell) {cap cap' : ℕ} (hcap : cap ≤ cap')
    (q : TilingCappedCoordinates eta.1.1.retainedCount
      ((PositiveInterfaceExternalPairFiber eta).coordinateCap cap))
    (hpred : (PositiveInterfaceExternalPairFiber eta).atomPredicate cap q)
    (haccepted : PrefixedTilingStoppingAccepted
      ((PositiveInterfaceExternalPairFiber eta).stoppingTime cap)
      eta.1.1.initial.1 t eta.1.1.start eta.1.1.retained
      (fun j ↦ (q j : ℕ)) eta.1.1.tail.1) :
    (PositiveInterfaceExternalPairFiber eta).atomPredicate cap'
      (castPositiveInterfaceExternalPairCoordinates eta hcap q) := by
  rcases hpred with ⟨favorite, hfavorite⟩
  refine ⟨favorite, ?_⟩
  change orientedAllCreationStoppedAtomPredicate o m k
    (PositiveInterfacePairSupportAt t o m externalThreshold width shell)
    eta.1.2 (withFavorite eta.1.1 favorite)
    ((PositiveInterfaceExternalPairFiber eta).coordinateCap cap')
    (castPositiveInterfaceExternalPairCoordinates eta hcap q)
  have hcast := orientedAllCreationStoppedAtomPredicate_cast
    o m k (PositiveInterfacePairSupportAt t o m externalThreshold width shell)
    eta.1.2 (withFavorite eta.1.1 favorite)
    (positiveInterfaceExternalPairCoordinateCap_mono eta hcap) q hfavorite
    haccepted
  change orientedAllCreationStoppedAtomPredicate o m k
    (PositiveInterfacePairSupportAt t o m externalThreshold width shell)
    eta.1.2 (withFavorite eta.1.1 favorite)
    ((PositiveInterfaceExternalPairFiber eta).coordinateCap cap')
    (castPositiveInterfaceExternalPairCoordinates eta hcap q) at hcast
  exact hcast

private theorem positiveInterfaceExternalPairSelected_cast
    {t : DominoTiling} {o : Orientation}
    {m k externalThreshold width shell : ℕ}
    (eta : PositiveInterfaceExternalPairSupportedIndex t o m k
      externalThreshold width shell) {cap cap' : ℕ} (hcap : cap ≤ cap')
    (q : TilingCappedCoordinates eta.1.1.retainedCount
      ((PositiveInterfaceExternalPairFiber eta).coordinateCap cap))
    (hselected : positiveInterfaceExternalPairSelected eta cap
      ((splitTilingCoordinatesEquiv t eta.1.1.start eta.1.1.retained
        (supportComplementDistinguished t eta.1.1.start eta.1.1.retained
          eta.1.2) q).1)) :
    let q' := castPositiveInterfaceExternalPairCoordinates eta hcap q
    positiveInterfaceExternalPairSelected eta cap'
      ((splitTilingCoordinatesEquiv t eta.1.1.start eta.1.1.retained
        (supportComplementDistinguished t eta.1.1.start eta.1.1.retained
          eta.1.2) q').1) := by
  classical
  dsimp only
  let data := PositiveInterfaceExternalPairFiber eta
  let D := supportComplementDistinguished t eta.1.1.start
    eta.1.1.retained eta.1.2
  let hcoord := positiveInterfaceExternalPairCoordinateCap_mono eta hcap
  let q' := castPositiveInterfaceExternalPairCoordinates eta hcap q
  rcases hselected with
    ⟨aSource, ellSource, hatomSource, hacceptedSource,
      hbaseSource, htotalSource⟩
  let qSource := (splitTilingCoordinatesEquiv t eta.1.1.start
      eta.1.1.retained D).symm
    ((splitTilingCoordinatesEquiv t eta.1.1.start eta.1.1.retained D q).1,
      aSource)
  let qSource' := castPositiveInterfaceExternalPairCoordinates eta hcap qSource
  let aSource' :=
    (splitTilingCoordinatesEquiv t eta.1.1.start eta.1.1.retained D
      qSource').2
  have hdist :
      (splitTilingCoordinatesEquiv t eta.1.1.start eta.1.1.retained D
        qSource').1 =
      (splitTilingCoordinatesEquiv t eta.1.1.start eta.1.1.retained D q').1 := by
    funext b c
    apply Fin.ext
    change (qSource c.1 : ℕ) = (q c.1 : ℕ)
    have hsourcePair := congrArg Prod.fst
      ((splitTilingCoordinatesEquiv t eta.1.1.start eta.1.1.retained D).apply_symm_apply
        ((splitTilingCoordinatesEquiv t eta.1.1.start eta.1.1.retained D q).1,
          aSource))
    have hsource := congrFun (congrFun hsourcePair b) c
    have hsourceNat := congrArg
      (fun v : Fin ((PositiveInterfaceExternalPairFiber eta).coordinateCap
        cap + 1) ↦ (v : ℕ)) hsource
    change (qSource c.1 : ℕ) = (q c.1 : ℕ) at hsourceNat
    exact hsourceNat
  have hreassemble :
      (splitTilingCoordinatesEquiv t eta.1.1.start eta.1.1.retained D).symm
          ((splitTilingCoordinatesEquiv t eta.1.1.start eta.1.1.retained D
            q').1, aSource') = qSource' := by
    rw [← hdist]
    exact (splitTilingCoordinatesEquiv t eta.1.1.start eta.1.1.retained D).symm_apply_apply
      qSource'
  refine ⟨aSource', ellSource, ?_, ?_, ?_, ?_⟩
  · rw [hreassemble]
    exact positiveInterfaceExternalPairAtomPredicate_cast eta hcap qSource
      hatomSource hacceptedSource
  · rw [hreassemble]
    change PrefixedTilingStoppingAccepted
      (truncatedLevelTime m k (externalCoordinateCutoff eta.1.1
        ((PositiveInterfaceExternalPairFiber eta).coordinateCap cap')))
      eta.1.1.initial.1 t eta.1.1.start eta.1.1.retained
      (fun j ↦ (qSource' j : ℕ)) eta.1.1.tail.1
    have hcast := prefixedStoppingAccepted_castAllCreation m k
      (withFavorite eta.1.1 (pairCapFavorite eta)) hcoord qSource
      hacceptedSource
    change PrefixedTilingStoppingAccepted
      (truncatedLevelTime m k (externalCoordinateCutoff eta.1.1
        ((PositiveInterfaceExternalPairFiber eta).coordinateCap cap')))
      eta.1.1.initial.1 t eta.1.1.start eta.1.1.retained
      (fun j ↦ (qSource' j : ℕ)) eta.1.1.tail.1 at hcast
    exact hcast
  · exact hbaseSource
  · intro b
    change tilingAwayTotal t eta.1.1.start eta.1.1.retained D aSource' b =
      ellSource b
    calc
      _ = tilingDominoTotal t eta.1.1.start eta.1.1.retained
          (fun j ↦ (qSource' j : ℕ)) b.1 :=
        tilingAwayTotal_split_eq_dominoTotal _ _ _ _ _ _
      _ = tilingDominoTotal t eta.1.1.start eta.1.1.retained
          (fun j ↦ (qSource j : ℕ)) b.1 := by
        simp only [qSource',
          coe_castPositiveInterfaceExternalPairCoordinates]
      _ = tilingAwayTotal t eta.1.1.start eta.1.1.retained D aSource b := by
        rw [← tilingAwayTotal_split_eq_dominoTotal t eta.1.1.start
          eta.1.1.retained D qSource b]
        simp only [qSource, Equiv.apply_symm_apply]
      _ = ellSource b := htotalSource b

private theorem positiveInterfaceExternalPairSourcePredicate_cast
    {t : DominoTiling} {o : Orientation}
    {m k externalThreshold width shell : ℕ}
    (eta : PositiveInterfaceExternalPairSupportedIndex t o m k
      externalThreshold width shell) (threshold : ℕ → ℕ) (bound : ℕ)
    {cap cap' : ℕ} (hcap : cap ≤ cap')
    (q : TilingCappedCoordinates eta.1.1.retainedCount
      ((PositiveInterfaceExternalPairFiber eta).coordinateCap cap))
    (hsource : positiveInterfaceExternalPairSourcePredicate eta cap threshold
      bound q) :
    let q' := castPositiveInterfaceExternalPairCoordinates eta hcap q
    positiveInterfaceExternalPairSourcePredicate eta cap' threshold bound q' := by
  classical
  dsimp only
  let D := supportComplementDistinguished t eta.1.1.start
    eta.1.1.retained eta.1.2
  let hcoord := positiveInterfaceExternalPairCoordinateCap_mono eta hcap
  let q' := castPositiveInterfaceExternalPairCoordinates eta hcap q
  rcases hsource with ⟨hselected, ell, hscreen, htotal⟩
  refine ⟨positiveInterfaceExternalPairSelected_cast eta hcap q hselected,
    ell, ?_, ?_⟩
  · exact hscreen
  · intro b
    calc
      _ = tilingDominoTotal t eta.1.1.start eta.1.1.retained
          (fun j ↦ (q' j : ℕ)) b.1 :=
        tilingAwayTotal_split_eq_dominoTotal _ _ _ _ _ _
      _ = tilingDominoTotal t eta.1.1.start eta.1.1.retained
          (fun j ↦ (q j : ℕ)) b.1 := by
        simp only [q', coe_castPositiveInterfaceExternalPairCoordinates]
      _ = tilingAwayTotal t eta.1.1.start eta.1.1.retained D
          ((splitTilingCoordinatesEquiv t eta.1.1.start eta.1.1.retained D
            q).2) b :=
        (tilingAwayTotal_split_eq_dominoTotal _ _ _ _ _ _).symm
      _ = ell b := htotal b

/-- The exact external-pair source caps form an increasing family. -/
theorem monotone_positiveInterfaceExternalPairSourceCap
    {t : DominoTiling} {o : Orientation}
    {m k externalThreshold width shell : ℕ}
    (eta : PositiveInterfaceExternalPairSupportedIndex t o m k
      externalThreshold width shell) (threshold : ℕ → ℕ) (bound : ℕ) :
    Monotone fun cap ↦
      positiveInterfaceExternalPairSourceCap eta cap threshold bound := by
  intro cap cap' hcap s hs
  rcases hs with ⟨hvalid, hevent⟩
  rcases Set.mem_iUnion.mp hevent with ⟨q, hq⟩
  let hcoord := positiveInterfaceExternalPairCoordinateCap_mono eta hcap
  let q' := castPositiveInterfaceExternalPairCoordinates eta hcap q.1
  have haccepted' : PrefixedTilingStoppingAccepted
      ((PositiveInterfaceExternalPairFiber eta).stoppingTime cap')
      eta.1.1.initial.1 t eta.1.1.start eta.1.1.retained
      (fun j ↦ (q' j : ℕ)) eta.1.1.tail.1 := by
    change PrefixedTilingStoppingAccepted
      (truncatedLevelTime m k (externalCoordinateCutoff eta.1.1
        ((PositiveInterfaceExternalPairFiber eta).coordinateCap cap')))
      eta.1.1.initial.1 t eta.1.1.start eta.1.1.retained
      (fun j ↦ (q' j : ℕ)) eta.1.1.tail.1
    have hcast := prefixedStoppingAccepted_castAllCreation m k
      (withFavorite eta.1.1 (pairCapFavorite eta)) hcoord q.1 q.2.2
    change PrefixedTilingStoppingAccepted
      (truncatedLevelTime m k (externalCoordinateCutoff eta.1.1
        ((PositiveInterfaceExternalPairFiber eta).coordinateCap cap')))
      eta.1.1.initial.1 t eta.1.1.start eta.1.1.retained
      (fun j ↦ (q' j : ℕ)) eta.1.1.tail.1 at hcast
    exact hcast
  refine ⟨hvalid, Set.mem_iUnion.mpr ⟨⟨q', ?_, haccepted'⟩, ?_⟩⟩
  · exact positiveInterfaceExternalPairSourcePredicate_cast eta threshold
      bound hcap q.1 q.2.1
  · change stepsOfWalk s ∈ prefixedTilingStoppedInsertionAtom
      ((PositiveInterfaceExternalPairFiber eta).stoppingTime cap')
      eta.1.1.initial.1 t eta.1.1.start eta.1.1.retained
      (fun j ↦ (q' j : ℕ)) eta.1.1.tail.1
    rw [prefixedTilingStoppedInsertionAtom_eq_cylinder
      ((PositiveInterfaceExternalPairFiber eta).isStoppingTime cap')
      eta.1.1.initial.1 t eta.1.1.start eta.1.1.retained
      (fun j ↦ (q' j : ℕ)) eta.1.1.tail.1 haccepted']
    rw [prefixedTilingStoppedInsertionAtom_eq_cylinder
      (isFiniteStoppingTime_truncatedLevelTime m k
        (externalCoordinateCutoff eta.1.1
          ((PositiveInterfaceExternalPairFiber eta).coordinateCap cap)))
      eta.1.1.initial.1 t eta.1.1.start eta.1.1.retained
      (fun j ↦ (q.1 j : ℕ)) eta.1.1.tail.1 q.2.2] at hq
    simpa only [q', coe_castPositiveInterfaceExternalPairCoordinates] using hq

end

end Erdos1165.HLOZPositiveInterfacePairSourceCapMonotone
