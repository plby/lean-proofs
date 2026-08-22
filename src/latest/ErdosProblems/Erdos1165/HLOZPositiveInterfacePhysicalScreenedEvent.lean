/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.HLOZPositiveInterfaceLocalWindowData
import ErdosProblems.Erdos1165.HLOZPrefixedAllCreationStaticSupportPhysicalInterface

/-!
# Honest positive-interface events with physical deficit-shell windows

This is the path-space counterpart of
`HLOZAllCreationCofinalPhysicalInterface`.  It takes the cofinal union of the
literal stopped screens on every exact `(external trace, support)` atom.
Unlike the legacy active-window event, its coordinate labels are exactly the
physical deficit shells.
-/

open Set

namespace Erdos1165.HLOZPositiveInterfacePhysicalScreenedEvent

open FiniteDominoProductLaw
open HLOZAllCreationCofinalConditionalSharpWindow
open HLOZAllCreationCofinalPhysicalInterface
open HLOZPositiveInterfaceAggregateRecovery
open HLOZPositiveInterfaceLocalWindowData
open HLOZPositiveInterfacePhysicalWindows
open HLOZProposition48Candidates
open HLOZPrefixedAllCreationStaticSupportAggregateRefinement
open HLOZPrefixedAllCreationStaticSupportAggregateRefinement.StaticSupportRecoveryCertificate
open LazyDecomposition
open ScreeningInstantiation TilingCappedMarginalization
open TilingOrientedAllCreationConcreteFamily
open TilingOrientedAllCreationStoppedCoordinate
open TilingOrientedSupportAwayCoordinates
open TilingPrefixedStoppedProductDisintegration
open TilingSpatialInsertionFiber
open VariableStoppedTracePartition

noncomputable section

abbrev DominoTiling := Tilings.Tiling

attribute [local instance] Classical.propDecidable

private theorem positiveInterfacePhysicalCoordinateCap_mono
    {t : DominoTiling} {o : Orientation} {m k externalThreshold : ℕ}
    (eta : PositiveInterfaceSupportedIndex t o m k externalThreshold)
    {cap cap' : ℕ} (hcap : cap ≤ cap') :
    (PositiveInterfaceFiber eta).coordinateCap cap ≤
      (PositiveInterfaceFiber eta).coordinateCap cap' := by
  change max eta.1.1.external.retainedCount (m + shellWidth48 m) + cap ≤
    max eta.1.1.external.retainedCount (m + shellWidth48 m) + cap'
  omega

/-- The physical narrow predicate is stable under enlargement of the
coordinate cap. -/
private theorem positiveInterfacePhysicalScreenedPredicate_cast
    {t : DominoTiling} {o : Orientation} {m k externalThreshold : ℕ}
    (eta : PositiveInterfaceSupportedIndex t o m k externalThreshold)
    (hm : 1 < m) (hk : 0 < k) (threshold : ℕ → ℕ)
    (width shell bound : ℕ) {cap cap' : ℕ} (hcap : cap ≤ cap')
    (q : TilingCappedCoordinates eta.1.1.external.retainedCount
      ((PositiveInterfaceFiber eta).coordinateCap cap))
    (haccepted : PrefixedTilingStoppingAccepted
      ((PositiveInterfaceFiber eta).stoppingTime cap)
      ((PositiveInterfaceFiber eta).initial cap) t
      ((PositiveInterfaceFiber eta).start cap)
      ((PositiveInterfaceFiber eta).retained cap) (fun j ↦ (q j : ℕ))
      ((PositiveInterfaceFiber eta).tail cap))
    (hscreen :
      physicalScreenedPredicate
        (positiveInterfaceStaticSupportRecoveryCertificate eta hm hk)
        threshold width shell bound cap q) :
    physicalScreenedPredicate
      (positiveInterfaceStaticSupportRecoveryCertificate eta hm hk)
      threshold width shell bound cap'
        (castAllCreationCappedCoordinates eta.1.1
          (positiveInterfacePhysicalCoordinateCap_mono eta hcap) q) := by
  classical
  let cert := positiveInterfaceStaticSupportRecoveryCertificate eta hm hk
  rcases hscreen with ⟨hpred, ell, hell, htotal⟩
  refine ⟨?_, ell, ?_, ?_⟩
  · exact orientedAllCreationStoppedAtomPredicate_cast
      o m k (PositiveInterfaceSupportAt t o m externalThreshold)
      eta.1.2 eta.1.1 (positiveInterfacePhysicalCoordinateCap_mono eta hcap)
      q hpred haccepted
  · exact hell
  · intro b
    simp only [OrientedAllCreationPrefixedStoppedCoordinateSpec.start,
      OrientedAllCreationPrefixedStoppedCoordinateSpec.retained,
      OrientedAllCreationPrefixedStoppedCoordinateSpec.distinguished]
      at htotal b ⊢
    calc
      _ = tilingDominoTotal t eta.1.1.external.start
          eta.1.1.external.retained
          (fun j ↦ (castAllCreationCappedCoordinates eta.1.1
            (positiveInterfacePhysicalCoordinateCap_mono eta hcap) q j : ℕ))
          b.1 := tilingAwayTotal_split_eq_dominoTotal _ _ _ _ _ _
      _ = tilingDominoTotal t eta.1.1.external.start
          eta.1.1.external.retained (fun j ↦ (q j : ℕ)) b.1 := by
        simp only [coe_castAllCreationCappedCoordinates]
      _ = tilingAwayTotal t eta.1.1.external.start
          eta.1.1.external.retained
          (supportComplementDistinguished t eta.1.1.external.start
            eta.1.1.external.retained eta.1.2)
          ((splitTilingCoordinatesEquiv t eta.1.1.external.start
            eta.1.1.external.retained
            (supportComplementDistinguished t eta.1.1.external.start
              eta.1.1.external.retained eta.1.2) q).2) b :=
        (tilingAwayTotal_split_eq_dominoTotal _ _ _ _ _ _).symm
      _ = ell b := htotal b

/-- One capped physical deficit-shell screen on an exact positive-interface
atom. -/
def positiveInterfacePhysicalScreenedFiber
    {t : DominoTiling} {o : Orientation} {m k externalThreshold : ℕ}
    (eta : PositiveInterfaceSupportedIndex t o m k externalThreshold)
    (hm : 1 < m) (hk : 0 < k) (threshold : ℕ → ℕ)
    (width shell bound cap : ℕ) : Set WalkPath :=
  let cert := positiveInterfaceStaticSupportRecoveryCertificate eta hm hk
  walkLift (prefixedTilingPreStoppingFiberEvent
    ((PositiveInterfaceFiber eta).stoppingTime cap)
    ((PositiveInterfaceFiber eta).initial cap) t
    ((PositiveInterfaceFiber eta).start cap)
    ((PositiveInterfaceFiber eta).retained cap)
    ((PositiveInterfaceFiber eta).coordinateCap cap)
    ((PositiveInterfaceFiber eta).tail cap)
    (cert.physicalScreenedPredicate threshold width shell bound cap))

/-- Concrete characterization of the physical Boolean screen on a
positive-interface fibre.  This specialization keeps the dependent fibre
projections definitionally aligned with `PositiveInterfaceFiber` for
downstream path reconstruction. -/
theorem positiveInterfacePhysicalScreenedAccepts_eq_true_iff
    {t : DominoTiling} {o : Orientation} {m k externalThreshold : ℕ}
    (eta : PositiveInterfaceSupportedIndex t o m k externalThreshold)
    (hm : 1 < m) (hk : 0 < k) (threshold : ℕ → ℕ)
    (width shell bound cap : ℕ)
    (ell : TruncatedTotals ((PositiveInterfaceFiber eta).upper cap)) :
    StaticSupportRecoveryCertificate.physicalScreenedAccepts
        (positiveInterfaceStaticSupportRecoveryCertificate eta hm hk)
          threshold width shell bound cap ell = true ↔
      StaticSupportRecoveryCertificate.baseProp
          (positiveInterfaceStaticSupportRecoveryCertificate eta hm hk)
            cap ell ∧
        allCreationRandomTotalThresholdedUpperTail
          (PositiveInterfaceFiber eta) cap
          (fun b (v : Fin ((PositiveInterfaceFiber eta).upper cap b)) ↦
            (v : ℕ) ∈ physicalDeficitFailureWindow m width
              (Fintype.card (TilingCoordinatesAt t
                ((PositiveInterfaceFiber eta).start cap)
                ((PositiveInterfaceFiber eta).retained cap) b.1))
              (shell + 1))
          (fun b (v : Fin ((PositiveInterfaceFiber eta).upper cap b)) ↦
            (v : ℕ) ∈ physicalDeficitFailureWindow m width
              (Fintype.card (TilingCoordinatesAt t
                ((PositiveInterfaceFiber eta).start cap)
                ((PositiveInterfaceFiber eta).retained cap) b.1)) shell)
          threshold shellGrowth48 shell bound ell := by
  exact StaticSupportRecoveryCertificate.physicalScreenedAccepts_eq_true_iff
    (positiveInterfaceStaticSupportRecoveryCertificate eta hm hk)
      threshold width shell bound cap ell

theorem measurableSet_positiveInterfacePhysicalScreenedFiber
    {t : DominoTiling} {o : Orientation} {m k externalThreshold : ℕ}
    (eta : PositiveInterfaceSupportedIndex t o m k externalThreshold)
    (hm : 1 < m) (hk : 0 < k) (threshold : ℕ → ℕ)
    (width shell bound cap : ℕ) :
    MeasurableSet (positiveInterfacePhysicalScreenedFiber eta hm hk threshold
      width shell bound cap) := by
  apply measurableSet_walkLift
  exact measurableSet_prefixedTilingPreStoppingFiberEvent
    ((PositiveInterfaceFiber eta).isStoppingTime cap)
    ((PositiveInterfaceFiber eta).initial cap) t
    ((PositiveInterfaceFiber eta).start cap)
    ((PositiveInterfaceFiber eta).retained cap)
    ((PositiveInterfaceFiber eta).coordinateCap cap)
    ((PositiveInterfaceFiber eta).tail cap)
    (physicalScreenedPredicate
      (positiveInterfaceStaticSupportRecoveryCertificate eta hm hk)
      threshold width shell bound cap)

theorem positiveInterfacePhysicalScreenedFiber_subset_atom
    {t : DominoTiling} {o : Orientation} {m k externalThreshold : ℕ}
    (eta : PositiveInterfaceSupportedIndex t o m k externalThreshold)
    (hm : 1 < m) (hk : 0 < k) (threshold : ℕ → ℕ)
    (width shell bound cap : ℕ) :
    positiveInterfacePhysicalScreenedFiber eta hm hk threshold width shell
        bound cap ⊆
      orientedAllCreationSupportTraceAtom t o m k
        (PositiveInterfaceSupportAt t o m externalThreshold)
        eta.1.1 eta.1.2 := by
  intro s hs
  apply (PositiveInterfaceFiber eta).atom_sound cap
  exact ⟨hs.1, prefixedTilingPreStoppingFiberEvent_mono
    ((PositiveInterfaceFiber eta).stoppingTime cap)
    ((PositiveInterfaceFiber eta).initial cap) t
    ((PositiveInterfaceFiber eta).start cap)
    ((PositiveInterfaceFiber eta).retained cap)
    ((PositiveInterfaceFiber eta).tail cap)
    (fun _q hq ↦ hq.1) hs.2⟩

theorem monotone_positiveInterfacePhysicalScreenedFiber
    {t : DominoTiling} {o : Orientation} {m k externalThreshold : ℕ}
    (eta : PositiveInterfaceSupportedIndex t o m k externalThreshold)
    (hm : 1 < m) (hk : 0 < k) (threshold : ℕ → ℕ)
    (width shell bound : ℕ) :
    Monotone fun cap ↦ positiveInterfacePhysicalScreenedFiber eta hm hk
      threshold width shell bound cap := by
  intro cap cap' hcap s hs
  rcases hs with ⟨hvalid, hevent⟩
  rcases Set.mem_iUnion.mp hevent with ⟨q, hq⟩
  let q' := castAllCreationCappedCoordinates eta.1.1
    (positiveInterfacePhysicalCoordinateCap_mono eta hcap) q.1
  have haccepted' := prefixedStoppingAccepted_castAllCreation
    m k eta.1.1 (positiveInterfacePhysicalCoordinateCap_mono eta hcap)
      q.1 q.2.2
  refine ⟨hvalid, Set.mem_iUnion.mpr ⟨⟨q', ?_, haccepted'⟩, ?_⟩⟩
  · exact positiveInterfacePhysicalScreenedPredicate_cast eta hm hk
      threshold width shell bound hcap q.1 q.2.2 q.2.1
  · rw [prefixedTilingStoppedInsertionAtom_eq_cylinder
      ((PositiveInterfaceFiber eta).isStoppingTime cap')
      ((PositiveInterfaceFiber eta).initial cap') t
      ((PositiveInterfaceFiber eta).start cap')
      ((PositiveInterfaceFiber eta).retained cap') (fun j ↦ (q' j : ℕ))
      ((PositiveInterfaceFiber eta).tail cap') haccepted']
    rw [prefixedTilingStoppedInsertionAtom_eq_cylinder
      ((PositiveInterfaceFiber eta).isStoppingTime cap)
      ((PositiveInterfaceFiber eta).initial cap) t
      ((PositiveInterfaceFiber eta).start cap)
      ((PositiveInterfaceFiber eta).retained cap) (fun j ↦ (q.1 j : ℕ))
      ((PositiveInterfaceFiber eta).tail cap) q.2.2] at hq
    simpa only [OrientedAllCreationPrefixedStoppedCoordinateSpec.initial,
      OrientedAllCreationPrefixedStoppedCoordinateSpec.start,
      OrientedAllCreationPrefixedStoppedCoordinateSpec.retained,
      OrientedAllCreationPrefixedStoppedCoordinateSpec.tail, q',
      coe_castAllCreationCappedCoordinates] using hq

/-- Cofinal union of the literal physical screens over all exact atoms. -/
def positiveInterfacePhysicalScreenedEvent
    (t : DominoTiling) (o : Orientation) (m k externalThreshold : ℕ)
    (hm : 1 < m) (hk : 0 < k) (threshold : ℕ → ℕ)
    (width shell bound : ℕ) : Set WalkPath :=
  ⋃ eta : PositiveInterfaceSupportedIndex t o m k externalThreshold,
    ⋃ cap : ℕ,
      positiveInterfacePhysicalScreenedFiber eta hm hk threshold width shell
        bound cap

theorem measurableSet_positiveInterfacePhysicalScreenedEvent
    (t : DominoTiling) (o : Orientation) (m k externalThreshold : ℕ)
    (hm : 1 < m) (hk : 0 < k) (threshold : ℕ → ℕ)
    (width shell bound : ℕ) :
    MeasurableSet (positiveInterfacePhysicalScreenedEvent t o m k
      externalThreshold hm hk threshold width shell bound) := by
  apply MeasurableSet.iUnion
  intro eta
  apply MeasurableSet.iUnion
  intro cap
  exact measurableSet_positiveInterfacePhysicalScreenedFiber eta hm hk
    threshold width shell bound cap

theorem positiveInterfacePhysicalScreenedEvent_subset_stage_valid
    (t : DominoTiling) (o : Orientation) (m k externalThreshold : ℕ)
    (hm : 1 < m) (hk : 0 < k) (threshold : ℕ → ℕ)
    (width shell bound : ℕ) :
    positiveInterfacePhysicalScreenedEvent t o m k externalThreshold hm hk
        threshold width shell bound ⊆
      thresholdReachStage m k ∩ validStepWalk := by
  intro s hs
  rcases Set.mem_iUnion.mp hs with ⟨eta, hs⟩
  rcases Set.mem_iUnion.mp hs with ⟨cap, hs⟩
  rw [← iUnion_supported_orientedAllCreationSupportTraceAtom
    t o m k (PositiveInterfaceSupportAt t o m externalThreshold)]
  exact Set.mem_iUnion.mpr ⟨eta,
    positiveInterfacePhysicalScreenedFiber_subset_atom eta hm hk threshold
      width shell bound cap hs⟩

theorem atom_inter_positiveInterfacePhysicalScreenedEvent_subset_localScreen
    {t : DominoTiling} {o : Orientation} {m k externalThreshold : ℕ}
    (eta : PositiveInterfaceSupportedIndex t o m k externalThreshold)
    (hm : 1 < m) (hk : 0 < k) (threshold : ℕ → ℕ)
    (width shell bound : ℕ) :
    orientedAllCreationSupportTraceAtom t o m k
          (PositiveInterfaceSupportAt t o m externalThreshold)
          eta.1.1 eta.1.2 ∩
        positiveInterfacePhysicalScreenedEvent t o m k externalThreshold hm hk
          threshold width shell bound ⊆
      ⋃ cap, positiveInterfacePhysicalScreenedFiber eta hm hk threshold
        width shell bound cap := by
  intro s hs
  rcases Set.mem_iUnion.mp hs.2 with ⟨eta', hs'⟩
  rcases Set.mem_iUnion.mp hs' with ⟨cap, hcap⟩
  have hatom' := positiveInterfacePhysicalScreenedFiber_subset_atom eta' hm hk
    threshold width shell bound cap hcap
  have hval : eta.1 = eta'.1 := by
    by_contra hne
    have hdisjoint := pairwise_disjoint_orientedAllCreationSupportTraceAtom
      t o m k (PositiveInterfaceSupportAt t o m externalThreshold) hne
    exact Set.disjoint_left.mp hdisjoint hs.1 hatom'
  have heta : eta = eta' := Subtype.ext hval
  subst eta'
  exact Set.mem_iUnion.mpr ⟨cap, hcap⟩

/-- The exact positive-interface partition packages a checked physical local
ratio into the usual cofinal interface product. -/
noncomputable def positiveInterfacePhysicalScreenedProductData
    (t : DominoTiling) (o : Orientation) (m k externalThreshold : ℕ)
    (hm : 1 < m) (hk : 0 < k) (threshold : ℕ → ℕ)
    (width shell bound : ℕ)
    (window_ratio_inter_base : ∀
      (eta : PositiveInterfaceSupportedIndex t o m k externalThreshold)
      (cap : ℕ)
      (b : TilingAwayDomino t ((PositiveInterfaceFiber eta).start cap)
        ((PositiveInterfaceFiber eta).retained cap)
        ((PositiveInterfaceFiber eta).distinguished cap)),
      (∑ v : Fin ((PositiveInterfaceFiber eta).upper cap b),
        if (v : ℕ) ∈ physicalDeficitFailureWindow m width
              (Fintype.card (TilingCoordinatesAt t
                ((PositiveInterfaceFiber eta).start cap)
                ((PositiveInterfaceFiber eta).retained cap) b.1))
              (shell + 1) ∧
            (v : ℕ) ∈ positiveInterfaceBaseWindow eta cap b then
          coordinateMass
            (tilingAwayPointMass
              (cap := (PositiveInterfaceFiber eta).coordinateCap cap) t
              ((PositiveInterfaceFiber eta).start cap)
              ((PositiveInterfaceFiber eta).retained cap)
              ((PositiveInterfaceFiber eta).distinguished cap))
            ((PositiveInterfaceFiber eta).upper cap) b v else 0) ≤
        (4 / 3 : ℝ) *
          ∑ v : Fin ((PositiveInterfaceFiber eta).upper cap b),
            if (v : ℕ) ∈ physicalDeficitFailureWindow m width
                  (Fintype.card (TilingCoordinatesAt t
                    ((PositiveInterfaceFiber eta).start cap)
                    ((PositiveInterfaceFiber eta).retained cap) b.1)) shell ∧
                (v : ℕ) ∈ positiveInterfaceBaseWindow eta cap b then
              coordinateMass
                (tilingAwayPointMass
                  (cap := (PositiveInterfaceFiber eta).coordinateCap cap) t
                  ((PositiveInterfaceFiber eta).start cap)
                  ((PositiveInterfaceFiber eta).retained cap)
                  ((PositiveInterfaceFiber eta).distinguished cap))
                ((PositiveInterfaceFiber eta).upper cap) b v else 0) :
    OrientedAllCreationCofinalSharpWindowInterfaceProductData
      t o m k
      (positiveInterfacePhysicalScreenedEvent t o m k externalThreshold hm hk
        threshold width shell bound)
      threshold shell bound where
  supportAt := PositiveInterfaceSupportAt t o m externalThreshold
  supportData := positiveInterfaceSupportData t o m k externalThreshold
  next_measurable := measurableSet_positiveInterfacePhysicalScreenedEvent
    t o m k externalThreshold hm hk threshold width shell bound
  next_subset_stage_valid :=
    positiveInterfacePhysicalScreenedEvent_subset_stage_valid
      t o m k externalThreshold hm hk threshold width shell bound
  tail := fun eta ↦ by
    let cert := positiveInterfaceStaticSupportRecoveryCertificate eta hm hk
    let data := cert.physicalInterfaceTailData
      (orientedAllCreationSupportTraceAtom t o m k
        (PositiveInterfaceSupportAt t o m externalThreshold)
        eta.1.1 eta.1.2)
      (positiveInterfacePhysicalScreenedEvent t o m k externalThreshold hm hk
        threshold width shell bound)
      threshold width shell bound Subset.rfl
      (fun cap b ↦ positiveInterfaceBaseLocalPos eta hm cap b)
      (monotone_positiveInterfacePhysicalScreenedFiber eta hm hk threshold
        width shell bound)
      (atom_inter_positiveInterfacePhysicalScreenedEvent_subset_localScreen
        eta hm hk threshold width shell bound)
      0 (fun cap _hcap b ↦ window_ratio_inter_base eta cap b)
    exact data.toCofinalData

end

end Erdos1165.HLOZPositiveInterfacePhysicalScreenedEvent
