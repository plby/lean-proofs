import ErdosProblems.Erdos1165.TilingTypedTransitionFactorization

/-!
# Cap coherence for typed retained-trace screens

The actual HLOZ finite screen is a predicate on natural-valued away-domino
totals and does not depend on the auxiliary coordinate cap.  This module
shows that the corresponding stopped cylinders are automatically monotone
in that cap.  Thus an eventual product package only needs the semantic path
coverage and the finite product estimate.
-/

open MeasureTheory Set
open scoped ENNReal NNReal

namespace Erdos1165.TilingTypedCapCoherence

open HLOZPathEvents
open TilingLazyDecomposition TilingSpatialInsertionFiber
open TilingCappedMarginalization TilingTypedFavoriteTrace
open TilingTypedFavoriteFactorization TilingTypedTransitionFactorization
open TilingFavoriteTraceSupport TilingStoppedAcceptanceFactorization
open VariableStoppedTracePartition

noncomputable section

abbrev DominoTiling := Tilings.Tiling

/-- Embed capped coordinates into a larger cap without changing any natural
coordinate value. -/
def castTypedCappedCoordinates {t : DominoTiling}
    (z : TypedFavoriteTilingTraceCode t) {cap cap' : ℕ}
    (hcap : cap ≤ cap')
    (q : TilingCappedCoordinates (typedRetainedCount z) cap) :
    TilingCappedCoordinates (typedRetainedCount z) cap' :=
  fun j ↦ Fin.castLE (Nat.succ_le_succ hcap) (q j)

@[simp] theorem coe_castTypedCappedCoordinates {t : DominoTiling}
    (z : TypedFavoriteTilingTraceCode t) {cap cap' : ℕ}
    (hcap : cap ≤ cap')
    (q : TilingCappedCoordinates (typedRetainedCount z) cap) (j) :
    ((castTypedCappedCoordinates z hcap q j :
      Fin (cap' + 1)) : ℕ) = (q j : ℕ) := rfl

theorem typedCoordinateCutoff_mono {t : DominoTiling}
    (z : TypedFavoriteTilingTraceCode t) :
    Monotone (typedCoordinateCutoff z) := by
  intro cap cap' hcap
  have hmul :
      (typedRetainedCount z + 1) * cap ≤
        (typedRetainedCount z + 1) * cap' :=
    Nat.mul_le_mul_left _ hcap
  unfold typedCoordinateCutoff
  omega

/-- Acceptance by a genuine creation clock persists when only the auxiliary
cap is enlarged. -/
theorem typedStoppingAccepted_cast
    {t : DominoTiling} (m k : ℕ)
    (z : TypedFavoriteTilingTraceCode t) {cap cap' : ℕ}
    (hcap : cap ≤ cap')
    (q : TilingCappedCoordinates (typedRetainedCount z) cap)
    (haccepted : TilingStoppingAccepted (typedStoppingTime m k z cap)
      t (0, 0) (typedRetained z) (fun j ↦ (q j : ℕ))
      (typedBoundaryTail z).1) :
    TilingStoppingAccepted (typedStoppingTime m k z cap')
      t (0, 0) (typedRetained z)
      (fun j ↦ (castTypedCappedCoordinates z hcap q j : ℕ))
      (typedBoundaryTail z).1 := by
  let v := tilingInsertionPrefixList t (0, 0) (typedRetained z)
    (fun j ↦ (q j : ℕ)) (typedBoundaryTail z).1
  have hcreation : ThresholdCreation (typedInsertionWalk z q) m k v.length :=
    (tilingStoppingAccepted_truncatedLevelTime_iff_thresholdCreation
      m k (typedCoordinateCutoff z cap) t (0, 0) (typedRetained z)
      (fun j ↦ (q j : ℕ)) (typedBoundaryTail z)
      (tilingInsertionPrefixList_lt_typedCoordinateCutoff z cap q)).mp
        haccepted
  have hlt : v.length < typedCoordinateCutoff z cap' :=
    (tilingInsertionPrefixList_lt_typedCoordinateCutoff z cap q).trans_le
      (typedCoordinateCutoff_mono z hcap)
  apply (tilingStoppingAccepted_truncatedLevelTime_iff_thresholdCreation
    m k (typedCoordinateCutoff z cap') t (0, 0) (typedRetained z)
    (fun j ↦ (castTypedCappedCoordinates z hcap q j : ℕ))
    (typedBoundaryTail z) ?_).mpr
  · simpa [typedInsertionWalk, v] using hcreation
  · simpa only [coe_castTypedCappedCoordinates] using hlt

/-- The cylinder-level trace/stage predicate also persists under cap
enlargement. -/
theorem typedStoppedFavoriteStageBasePredicate_cast
    {t : DominoTiling} (m k : ℕ) (stage : Set WalkPath)
    (z : TypedFavoriteTilingTraceCode t) {cap cap' : ℕ}
    (hcap : cap ≤ cap')
    (q : TilingCappedCoordinates (typedRetainedCount z) cap)
    (hbase : typedStoppedFavoriteStageBasePredicate
      t m k stage z cap q)
    (haccepted : TilingStoppingAccepted (typedStoppingTime m k z cap)
      t (0, 0) (typedRetained z) (fun j ↦ (q j : ℕ))
      (typedBoundaryTail z).1) :
    typedStoppedFavoriteStageBasePredicate t m k stage z cap'
      (castTypedCappedCoordinates z hcap q) := by
  have haccepted' := typedStoppingAccepted_cast m k z hcap q haccepted
  intro omega homega
  apply hbase
  rw [tilingStoppedInsertionAtom_eq_cylinder
    (isFiniteStoppingTime_typedStoppingTime m k z cap)
    t (0, 0) (typedRetained z) (fun j ↦ (q j : ℕ))
    (typedBoundaryTail z).1 haccepted]
  rw [tilingStoppedInsertionAtom_eq_cylinder
    (isFiniteStoppingTime_typedStoppingTime m k z cap')
    t (0, 0) (typedRetained z)
    (fun j ↦ (castTypedCappedCoordinates z hcap q j : ℕ))
    (typedBoundaryTail z).1 haccepted'] at homega
  simpa only [coe_castTypedCappedCoordinates] using homega

/-- A cap-independent away-total screen is preserved by the coordinate
embedding. -/
theorem typedStoppedScreenedPredicate_cast
    {t : DominoTiling} (m k : ℕ) (stage : Set WalkPath)
    (z : TypedFavoriteTilingTraceCode t) {cap cap' : ℕ}
    (hcap : cap ≤ cap')
    (accepts : FiniteDominoProductLaw.TruncatedTotals
      (typedPositiveAwayUpper t m z) → Bool)
    (q : TilingCappedCoordinates (typedRetainedCount z) cap)
    (haccepted : TilingStoppingAccepted (typedStoppingTime m k z cap)
      t (0, 0) (typedRetained z) (fun j ↦ (q j : ℕ))
      (typedBoundaryTail z).1)
    (hscreen : typedStoppedScreenedPredicate
      t m k stage z cap accepts q) :
    typedStoppedScreenedPredicate t m k stage z cap' accepts
      (castTypedCappedCoordinates z hcap q) := by
  rcases hscreen with ⟨hbase, haway⟩
  refine ⟨typedStoppedFavoriteStageBasePredicate_cast
    m k stage z hcap q hbase haccepted, ?_⟩
  rcases haway with ⟨ell, hell, htot⟩
  refine ⟨ell, hell, fun b ↦ ?_⟩
  rw [tilingAwayTotal_split_eq_dominoTotal]
  calc
    tilingDominoTotal t (0, 0) (typedRetained z)
        (fun j ↦ (castTypedCappedCoordinates z hcap q j : ℕ)) b.1 =
        tilingDominoTotal t (0, 0) (typedRetained z)
          (fun j ↦ (q j : ℕ)) b.1 := by
      unfold tilingDominoTotal
      apply Finset.sum_congr rfl
      intro j _hj
      exact coe_castTypedCappedCoordinates z hcap q j.1
    _ = tilingAwayTotal t (0, 0) (typedRetained z)
        (typedDistinguished z)
        (splitTilingCoordinatesEquiv t (0, 0) (typedRetained z)
          (typedDistinguished z) q).2 b :=
      (tilingAwayTotal_split_eq_dominoTotal t (0, 0)
        (typedRetained z) (typedDistinguished z) q b).symm
    _ = ell b := htot b

/-- Therefore the full lifted screened stopped fibre is monotone in the cap. -/
theorem monotone_typedStoppedScreenedFiber_of_capIndependent
    {t : DominoTiling} (m k : ℕ) (stage : Set WalkPath)
    (z : TypedFavoriteTilingTraceCode t)
    (accepts : FiniteDominoProductLaw.TruncatedTotals
      (typedPositiveAwayUpper t m z) → Bool) :
    Monotone fun cap ↦
      walkLift (tilingPreStoppingFiberEvent (typedStoppingTime m k z cap)
        t (0, 0) (typedRetained z) cap (typedBoundaryTail z).1
        (typedStoppedScreenedPredicate t m k stage z cap accepts)) := by
  intro cap cap' hcap s hs
  rcases hs with ⟨hvalid, hevent⟩
  rcases Set.mem_iUnion.mp hevent with ⟨q, hq⟩
  let q' := castTypedCappedCoordinates z hcap q.1
  have haccepted' := typedStoppingAccepted_cast m k z hcap q.1 q.2.2
  refine ⟨hvalid, Set.mem_iUnion.mpr ⟨⟨q', ?_, haccepted'⟩, ?_⟩⟩
  · exact typedStoppedScreenedPredicate_cast m k stage z hcap
      accepts q.1 q.2.2 q.2.1
  · rw [tilingStoppedInsertionAtom_eq_cylinder
      (isFiniteStoppingTime_typedStoppingTime m k z cap')
      t (0, 0) (typedRetained z) (fun j ↦ (q' j : ℕ))
      (typedBoundaryTail z).1 haccepted']
    rw [tilingStoppedInsertionAtom_eq_cylinder
      (isFiniteStoppingTime_typedStoppingTime m k z cap)
      t (0, 0) (typedRetained z) (fun j ↦ (q.1 j : ℕ))
      (typedBoundaryTail z).1 q.2.2] at hq
    simpa only [q', coe_castTypedCappedCoordinates] using hq

/-- Residual cap-independent finite screen data.  Cap monotonicity is no
longer a field. -/
structure TypedCapIndependentAwayScreenData
    (t : DominoTiling) (m k : ℕ) (stage next : Set WalkPath)
    (cost : ℝ≥0∞) where
  accepts : ∀ z : TypedFavoriteTilingTraceCode t,
    FiniteDominoProductLaw.TruncatedTotals
      (typedPositiveAwayUpper t m z) → Bool
  transition_covered : ∀ z,
    typedFavoriteTilingStagePiece t m k stage z ∩ next ⊆ ⋃ cap,
      walkLift (tilingPreStoppingFiberEvent (typedStoppingTime m k z cap)
        t (0, 0) (typedRetained z) cap (typedBoundaryTail z).1
        (typedStoppedScreenedPredicate t m k stage z cap (accepts z)))
  product_bound : ∀ z cap,
    FiniteDominoProductLaw.screenMass
      (tilingAwayPointMass (cap := cap) t (0, 0) (typedRetained z)
        (typedDistinguished z)) (typedPositiveAwayUpper t m z)
      (fun ell ↦ accepts z ell = true) ≤ cost.toReal

/-- Restore the general finite-screen interface, deriving cap monotonicity. -/
noncomputable def TypedCapIndependentAwayScreenData.toFiniteAwayScreenData
    {t : DominoTiling} {m k : ℕ} {stage next : Set WalkPath}
    {cost : ℝ≥0∞}
    (data : TypedCapIndependentAwayScreenData t m k stage next cost) :
    TypedFiniteAwayScreenData t m k stage next cost where
  accepts z _ := data.accepts z
  monotone_screened z :=
    monotone_typedStoppedScreenedFiber_of_capIndependent
      m k stage z (data.accepts z)
  transition_covered := data.transition_covered
  product_bound := data.product_bound

end

end Erdos1165.TilingTypedCapCoherence
