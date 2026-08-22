import ErdosProblems.Erdos1165.TilingVariableStoppedTracePartition
import ErdosProblems.Erdos1165.FiniteDominoProductLaw
import ErdosProblems.Erdos1165.VariableStoppedProductDisintegration

/-!
# Exact product disintegration for all six state-dependent tilings

This file transports the prefix-free stopped-cylinder calculation in
`TilingSpatialInsertionFiber` to the coordinate-system-neutral capped
certificate consumed by the HLOZ trace endgame.  The only genuinely spatial
input to the constructor is an equality of two explicit finite geometric
sums.  In particular, no path-space transition inequality is assumed.
-/

open MeasureTheory Set
open scoped BigOperators ENNReal NNReal

namespace Erdos1165.TilingStoppedProductDisintegration

open LazyDecomposition PathInsertion StoppedInsertion SpatialInsertionFiber
open VariableStoppedFiber VariableStoppedTracePartition
open PreStoppingFiber PreStoppingConditionalLaw
open TilingLazyDecomposition TilingSpatialInsertionFiber
open TilingVariableStoppedTracePartition
open CappedCoordinateMassCertificate HLOZTraceCappedProductScreening
open HLOZPathEvents HLOZStoppedSpatialScreening
open FiniteDominoProductLaw

noncomputable section

/-- The explicit finite geometric mass of the accepted capped coordinates
selected by `P` in one state-dependent tiling fibre. -/
noncomputable def tilingStoppedAcceptedGeometricMass
    (tau : StepPath → ℕ) {i : ℕ} (t : DominoTiling) (x : Point)
    (r : TilingRetainedWord t x i) (cap : ℕ) (tail : List Direction)
    (P : TilingCappedCoordinates i cap → Prop) : ℝ :=
  ∑ q : TilingAcceptedCappedCoordinates tau t x r cap tail P,
    gapVectorMass (fun j ↦ (q.1 j : ℕ))

theorem tilingStoppedAcceptedGeometricMass_nonneg
    (tau : StepPath → ℕ) {i : ℕ} (t : DominoTiling) (x : Point)
    (r : TilingRetainedWord t x i) (cap : ℕ) (tail : List Direction)
    (P : TilingCappedCoordinates i cap → Prop) :
    0 ≤ tilingStoppedAcceptedGeometricMass tau t x r cap tail P := by
  unfold tilingStoppedAcceptedGeometricMass
  exact Finset.sum_nonneg fun q _ ↦
    VariableStoppedProductDisintegration.gapVectorMass_nonneg _

/-- Product geometric weight carried by the coordinates attached to one
domino of a state-dependent tiling. -/
noncomputable def tilingDominoCoordinateMass {i : ℕ}
    (t : DominoTiling) (x : Point) (r : TilingRetainedWord t x i)
    (q : Fin (i + 1) → ℕ) (b : TilingExternalDomino t x r) : ℝ :=
  ∏ k : TilingCoordinatesAt t x r b, geometricGapMass (q k.1)

/-- Exact factorization of a state-dependent insertion-vector weight over
the dominoes met by its retained external word. -/
theorem gapVectorMass_tiling_factorization {i : ℕ}
    (t : DominoTiling) (x : Point) (r : TilingRetainedWord t x i)
    (q : Fin (i + 1) → ℕ) :
    gapVectorMass q =
      ∏ b : TilingExternalDomino t x r,
        tilingDominoCoordinateMass t x r q b := by
  classical
  unfold gapVectorMass tilingDominoCoordinateMass
  rw [← Fintype.prod_sigma
    (fun z : Σ b : TilingExternalDomino t x r,
      TilingCoordinatesAt t x r b ↦ geometricGapMass (q z.2.1))]
  exact Fintype.prod_equiv (tilingCoordinateSigmaEquiv t x r)
    (fun k ↦ geometricGapMass (q k))
    (fun z ↦ geometricGapMass (q z.2.1)) (fun _ ↦ rfl)

/-- Exact real mass of a finite capped state-dependent stopped fibre. -/
theorem fairSteps_real_tilingPreStoppingFiberEvent
    {tau : StepPath → ℕ} (htau : IsFiniteStoppingTime tau)
    {i : ℕ} (t : DominoTiling) (x : Point)
    (r : TilingRetainedWord t x i) (cap : ℕ) (tail : List Direction)
    (P : TilingCappedCoordinates i cap → Prop) :
    fairSteps.real (tilingPreStoppingFiberEvent tau t x r cap tail P) =
      prefixFiberConstant i tail *
        tilingStoppedAcceptedGeometricMass tau t x r cap tail P := by
  rw [Measure.real,
    fairSteps_tilingPreStoppingFiberEvent_eq_geometricSum
      htau t x r cap tail P]
  exact ENNReal.toReal_ofReal (mul_nonneg
    (VariableStoppedProductDisintegration.prefixFiberConstant_nonneg i tail)
    (tilingStoppedAcceptedGeometricMass_nonneg tau t x r cap tail P))

/-- Exact real mass after lifting the stopped fibre to walk paths. -/
theorem simpleRandomWalk_real_walkLift_tilingPreStoppingFiberEvent
    {tau : StepPath → ℕ} (htau : IsFiniteStoppingTime tau)
    {i : ℕ} (t : DominoTiling) (x : Point)
    (r : TilingRetainedWord t x i) (cap : ℕ) (tail : List Direction)
    (P : TilingCappedCoordinates i cap → Prop) :
    simpleRandomWalk.real
        (walkLift (tilingPreStoppingFiberEvent tau t x r cap tail P)) =
      prefixFiberConstant i tail *
        tilingStoppedAcceptedGeometricMass tau t x r cap tail P := by
  have hmeas : MeasurableSet
      (tilingPreStoppingFiberEvent tau t x r cap tail P) :=
    measurableSet_tilingPreStoppingFiberEvent htau t x r cap tail P
  rw [Measure.real, simpleRandomWalk_walkLift hmeas]
  exact fairSteps_real_tilingPreStoppingFiberEvent htau t x r cap tail P

/-- Dominoes away from the finite distinguished set in one fixed stateful
external word. -/
abbrev TilingAwayDomino {i : ℕ} (t : DominoTiling) (x : Point)
    (r : TilingRetainedWord t x i) (D : Finset Point) :=
  {b : TilingExternalDomino t x r // b.1 ∉ D}

noncomputable instance tilingAwayDominoFintype {i : ℕ}
    (t : DominoTiling) (x : Point) (r : TilingRetainedWord t x i)
    (D : Finset Point) : Fintype (TilingAwayDomino t x r D) :=
  Fintype.ofFinite _

/-! ## Distinguished-coordinate marginalization -/

/-- Once a tiling-specific local-time calculation has identified the base
and screened accepted sums with the indicated distinguished/away sums, the
normalized product identity follows by finite algebra. -/
theorem tilingStoppedAcceptedGeometricMass_eq_screenMass_mul_of_marginals
    {tau : StepPath → ℕ} {i cap : ℕ}
    (t : DominoTiling) (x : Point) (r : TilingRetainedWord t x i)
    (tail : List Direction)
    (base screened : TilingCappedCoordinates i cap → Prop)
    (D : Finset Point)
    (upper : TilingAwayDomino t x r D → ℕ)
    (pointMass : TilingAwayDomino t x r D → ℕ → ℝ)
    (screen : TruncatedTotals upper → Prop) [DecidablePred screen]
    {delta : Type*} [Fintype delta] (distinguishedMass : delta → ℝ)
    (htotal : (∑ ell : TruncatedTotals upper,
      jointMass pointMass upper ell) ≠ 0)
    (hbase : tilingStoppedAcceptedGeometricMass tau t x r cap tail base =
      ∑ ell : TruncatedTotals upper,
        FiniteDominoProductLaw.distinguishedAwayMass pointMass upper
          distinguishedMass ell)
    (hscreen : tilingStoppedAcceptedGeometricMass tau t x r cap tail screened =
      ∑ ell : TruncatedTotals upper,
        if screen ell then
          FiniteDominoProductLaw.distinguishedAwayMass pointMass upper
            distinguishedMass ell else 0) :
    tilingStoppedAcceptedGeometricMass tau t x r cap tail screened =
      screenMass pointMass upper screen *
        tilingStoppedAcceptedGeometricMass tau t x r cap tail base := by
  rw [hscreen, hbase]
  exact (screenMass_mul_distinguishedBase pointMass upper screen
    distinguishedMass htotal).symm

/-! ## Direct finite coordinate product under the away truncation -/

/-- Arbitrary coordinatewise upper bounds on the away domino totals. -/
def TilingUpperTruncation {i : ℕ} (t : DominoTiling) (x : Point)
    (r : TilingRetainedWord t x i) (D : Finset Point)
    (upper : TilingExternalDomino t x r → ℕ)
    (q : Fin (i + 1) → ℕ) : Prop :=
  ∀ b : TilingExternalDomino t x r, b.1 ∉ D →
    tilingDominoTotal t x r q b < upper b

def TilingDominoAdmissible {i : ℕ} (t : DominoTiling) (x : Point)
    (r : TilingRetainedWord t x i) (D : Finset Point)
    (upper : TilingExternalDomino t x r → ℕ)
    (q : Fin (i + 1) → ℕ) (b : TilingExternalDomino t x r) : Prop :=
  b.1 ∈ D ∨ tilingDominoTotal t x r q b < upper b

theorem tilingUpperTruncation_iff_forall_admissible {i : ℕ}
    (t : DominoTiling) (x : Point) (r : TilingRetainedWord t x i)
    (D : Finset Point) (upper : TilingExternalDomino t x r → ℕ)
    (q : Fin (i + 1) → ℕ) :
    TilingUpperTruncation t x r D upper q ↔
      ∀ b, TilingDominoAdmissible t x r D upper q b := by
  constructor
  · intro h b
    by_cases hb : b.1 ∈ D
    · exact Or.inl hb
    · exact Or.inr (h b hb)
  · intro h b hb
    exact (h b).resolve_left hb

noncomputable def tilingConditionedGapVectorMass {i : ℕ}
    (t : DominoTiling) (x : Point) (r : TilingRetainedWord t x i)
    (D : Finset Point) (upper : TilingExternalDomino t x r → ℕ)
    (q : Fin (i + 1) → ℕ) : ℝ := by
  classical
  exact if TilingUpperTruncation t x r D upper q then gapVectorMass q else 0

noncomputable def tilingConditionedDominoCoordinateMass {i : ℕ}
    (t : DominoTiling) (x : Point) (r : TilingRetainedWord t x i)
    (D : Finset Point) (upper : TilingExternalDomino t x r → ℕ)
    (q : Fin (i + 1) → ℕ) (b : TilingExternalDomino t x r) : ℝ := by
  classical
  exact if TilingDominoAdmissible t x r D upper q b then
    tilingDominoCoordinateMass t x r q b else 0

theorem tilingConditionedGapVectorMass_factorization {i : ℕ}
    (t : DominoTiling) (x : Point) (r : TilingRetainedWord t x i)
    (D : Finset Point) (upper : TilingExternalDomino t x r → ℕ)
    (q : Fin (i + 1) → ℕ) :
    tilingConditionedGapVectorMass t x r D upper q =
      ∏ b : TilingExternalDomino t x r,
        tilingConditionedDominoCoordinateMass t x r D upper q b := by
  classical
  by_cases htr : TilingUpperTruncation t x r D upper q
  · rw [tilingConditionedGapVectorMass, if_pos htr,
      gapVectorMass_tiling_factorization]
    apply Finset.prod_congr rfl
    intro b _
    rw [tilingConditionedDominoCoordinateMass,
      if_pos ((tilingUpperTruncation_iff_forall_admissible
        t x r D upper q).mp htr b)]
  · rw [tilingConditionedGapVectorMass, if_neg htr]
    have hnall : ¬∀ b, TilingDominoAdmissible t x r D upper q b :=
      mt (tilingUpperTruncation_iff_forall_admissible
        t x r D upper q).mpr htr
    push_neg at hnall
    obtain ⟨b, hb⟩ := hnall
    rw [Finset.prod_eq_zero (Finset.mem_univ b)]
    exact if_neg hb

noncomputable def tilingConditionedCappedDominoMass {i cap : ℕ}
    (t : DominoTiling) (x : Point) (r : TilingRetainedWord t x i)
    (D : Finset Point) (upper : TilingExternalDomino t x r → ℕ)
    (b : TilingExternalDomino t x r)
    (v : TilingCoordinatesAt t x r b → Fin (cap + 1)) : ℝ := by
  classical
  exact if b.1 ∈ D ∨ (∑ k, (v k : ℕ)) < upper b then
    ∏ k, geometricGapMass (v k : ℕ) else 0

@[simp] theorem regroupTilingCoordinatesEquiv_apply {i : ℕ}
    (t : DominoTiling) (x : Point) (r : TilingRetainedWord t x i)
    (alpha : Type*) (q : Fin (i + 1) → alpha)
    (b : TilingExternalDomino t x r) (k : TilingCoordinatesAt t x r b) :
    (regroupTilingCoordinatesEquiv t x r alpha q) b k = q k.1 := rfl

theorem tilingConditionedCappedMass_eq {i cap : ℕ}
    (t : DominoTiling) (x : Point) (r : TilingRetainedWord t x i)
    (D : Finset Point) (upper : TilingExternalDomino t x r → ℕ)
    (q : TilingCappedCoordinates i cap) (b : TilingExternalDomino t x r) :
    tilingConditionedDominoCoordinateMass t x r D upper
        (fun k ↦ (q k : ℕ)) b =
      tilingConditionedCappedDominoMass t x r D upper b
        ((regroupTilingCoordinatesEquiv t x r _ q) b) := by
  classical
  unfold tilingConditionedDominoCoordinateMass
    tilingConditionedCappedDominoMass TilingDominoAdmissible
    tilingDominoCoordinateMass tilingDominoTotal
  simp only [regroupTilingCoordinatesEquiv_apply]
  rfl

noncomputable def tilingCappedConditionedPartition {i cap : ℕ}
    (t : DominoTiling) (x : Point) (r : TilingRetainedWord t x i)
    (D : Finset Point) (upper : TilingExternalDomino t x r → ℕ) : ℝ :=
  ∑ q : TilingCappedCoordinates i cap,
    tilingConditionedGapVectorMass t x r D upper
      (fun k ↦ (q k : ℕ))

noncomputable def tilingCappedDominoPartition {i cap : ℕ}
    (t : DominoTiling) (x : Point) (r : TilingRetainedWord t x i)
    (D : Finset Point) (upper : TilingExternalDomino t x r → ℕ)
    (b : TilingExternalDomino t x r) : ℝ :=
  ∑ v : TilingCoordinatesAt t x r b → Fin (cap + 1),
    tilingConditionedCappedDominoMass t x r D upper b v

/-- Exact capped coordinate independence for every HLOZ tiling. -/
theorem tilingCappedConditionedPartition_factorization {i cap : ℕ}
    (t : DominoTiling) (x : Point) (r : TilingRetainedWord t x i)
    (D : Finset Point) (upper : TilingExternalDomino t x r → ℕ) :
    tilingCappedConditionedPartition (cap := cap) t x r D upper =
      ∏ b : TilingExternalDomino t x r,
        tilingCappedDominoPartition (cap := cap) t x r D upper b := by
  classical
  unfold tilingCappedConditionedPartition tilingCappedDominoPartition
  calc
    (∑ q : TilingCappedCoordinates i cap,
        tilingConditionedGapVectorMass t x r D upper
          (fun k ↦ (q k : ℕ))) =
        ∑ Q : (b : TilingExternalDomino t x r) →
            TilingCoordinatesAt t x r b → Fin (cap + 1),
          ∏ b, tilingConditionedCappedDominoMass t x r D upper b (Q b) :=
      Fintype.sum_equiv (regroupTilingCoordinatesEquiv t x r (Fin (cap + 1)))
        _ _ (fun q ↦ by
          rw [tilingConditionedGapVectorMass_factorization]
          apply Finset.prod_congr rfl
          intro b _
          exact tilingConditionedCappedMass_eq t x r D upper q b)
    _ = ∏ b : TilingExternalDomino t x r,
        ∑ v : TilingCoordinatesAt t x r b → Fin (cap + 1),
          tilingConditionedCappedDominoMass t x r D upper b v :=
      (Fintype.prod_sum fun b v ↦
        tilingConditionedCappedDominoMass t x r D upper b v).symm

/-- A stopped-coordinate product specification for an arbitrary one of the
six HLOZ tilings.  `coordinate_identity` is an equality of explicit finite
geometric sums.  Its right-hand factor is definitionally a normalized finite
product probability over the away dominoes. -/
structure TilingStoppedCoordinateProductSpec {index : Type*}
    (piece : index → Set WalkPath) (next : Set WalkPath) (cost : ℝ≥0∞) where
  tiling : index → ℕ → DominoTiling
  retainedCount : index → ℕ → ℕ
  start : index → ℕ → Point
  retained : ∀ z cap,
    TilingRetainedWord (tiling z cap) (start z cap) (retainedCount z cap)
  tail : index → ℕ → List Direction
  stoppingTime : index → ℕ → StepPath → ℕ
  isStoppingTime : ∀ z cap, IsFiniteStoppingTime (stoppingTime z cap)
  basePredicate : ∀ z cap,
    TilingCappedCoordinates (retainedCount z cap) cap → Prop
  screenedPredicate : ∀ z cap,
    TilingCappedCoordinates (retainedCount z cap) cap → Prop
  screened_subset_base : ∀ z cap q,
    screenedPredicate z cap q → basePredicate z cap q
  base_subset_piece : ∀ z cap,
    walkLift (tilingPreStoppingFiberEvent (stoppingTime z cap)
      (tiling z cap) (start z cap) (retained z cap) cap (tail z cap)
      (basePredicate z cap)) ⊆ piece z
  distinguished : index → ℕ → Finset Point
  upper : ∀ z cap,
    TilingAwayDomino (tiling z cap) (start z cap) (retained z cap)
      (distinguished z cap) → ℕ
  pointMass : ∀ z cap,
    TilingAwayDomino (tiling z cap) (start z cap) (retained z cap)
      (distinguished z cap) → ℕ → ℝ
  accepts : ∀ z cap,
    TruncatedTotals (upper z cap) → Bool
  coordinate_identity : ∀ z cap,
    tilingStoppedAcceptedGeometricMass (stoppingTime z cap)
        (tiling z cap) (start z cap) (retained z cap) cap (tail z cap)
        (screenedPredicate z cap) =
      screenMass (pointMass z cap) (upper z cap)
          (fun ell ↦ accepts z cap ell = true) *
        tilingStoppedAcceptedGeometricMass (stoppingTime z cap)
          (tiling z cap) (start z cap) (retained z cap) cap (tail z cap)
          (basePredicate z cap)
  monotone_screened : ∀ z, Monotone fun cap ↦
    walkLift (tilingPreStoppingFiberEvent (stoppingTime z cap)
      (tiling z cap) (start z cap) (retained z cap) cap (tail z cap)
      (screenedPredicate z cap))
  transition_covered : ∀ z, piece z ∩ next ⊆ ⋃ cap,
    walkLift (tilingPreStoppingFiberEvent (stoppingTime z cap)
      (tiling z cap) (start z cap) (retained z cap) cap (tail z cap)
      (screenedPredicate z cap))
  product_bound : ∀ z cap,
    screenMass (pointMass z cap) (upper z cap)
        (fun ell ↦ accepts z cap ell = true) ≤ cost.toReal

/-- The literal coordinate-system-neutral mass certificate obtained from a
state-dependent tiling stopped-coordinate specification. -/
def coordinateMassSpecOfTilingStoppedCoordinateProductSpec
    {index : Type*} {piece : index → Set WalkPath}
    {next : Set WalkPath} {cost : ℝ≥0∞}
    (spec : TilingStoppedCoordinateProductSpec piece next cost) :
    CoordinateMassSpec piece next cost where
  screened z cap := walkLift
    (tilingPreStoppingFiberEvent (spec.stoppingTime z cap)
      (spec.tiling z cap) (spec.start z cap) (spec.retained z cap) cap
      (spec.tail z cap) (spec.screenedPredicate z cap))
  fiber z cap := walkLift
    (tilingPreStoppingFiberEvent (spec.stoppingTime z cap)
      (spec.tiling z cap) (spec.start z cap) (spec.retained z cap) cap
      (spec.tail z cap) (spec.basePredicate z cap))
  measurable_screened z cap := measurableSet_walkLift
    (measurableSet_tilingPreStoppingFiberEvent (spec.isStoppingTime z cap)
      (spec.tiling z cap) (spec.start z cap) (spec.retained z cap) cap
      (spec.tail z cap) (spec.screenedPredicate z cap))
  measurable_fiber z cap := measurableSet_walkLift
    (measurableSet_tilingPreStoppingFiberEvent (spec.isStoppingTime z cap)
      (spec.tiling z cap) (spec.start z cap) (spec.retained z cap) cap
      (spec.tail z cap) (spec.basePredicate z cap))
  screened_subset_piece z cap := by
    intro s hs
    apply spec.base_subset_piece z cap
    exact ⟨hs.1, tilingPreStoppingFiberEvent_mono
      (spec.stoppingTime z cap) (spec.tiling z cap) (spec.start z cap)
      (spec.retained z cap) (spec.tail z cap)
      (spec.screened_subset_base z cap) hs.2⟩
  fiber_subset_piece := spec.base_subset_piece
  monotone_screened := spec.monotone_screened
  transition_covered := spec.transition_covered
  commonFactor z cap := prefixFiberConstant (spec.retainedCount z cap)
    (spec.tail z cap)
  screenedCoordinateMass z cap :=
    tilingStoppedAcceptedGeometricMass (spec.stoppingTime z cap)
      (spec.tiling z cap) (spec.start z cap) (spec.retained z cap) cap
      (spec.tail z cap) (spec.screenedPredicate z cap)
  fiberCoordinateMass z cap :=
    tilingStoppedAcceptedGeometricMass (spec.stoppingTime z cap)
      (spec.tiling z cap) (spec.start z cap) (spec.retained z cap) cap
      (spec.tail z cap) (spec.basePredicate z cap)
  productProbability z cap :=
    screenMass (spec.pointMass z cap) (spec.upper z cap)
      (fun ell ↦ spec.accepts z cap ell = true)
  coordinate_identity := spec.coordinate_identity
  screened_event_mass z cap :=
    simpleRandomWalk_real_walkLift_tilingPreStoppingFiberEvent
      (spec.isStoppingTime z cap) (spec.tiling z cap) (spec.start z cap)
      (spec.retained z cap) cap (spec.tail z cap)
      (spec.screenedPredicate z cap)
  fiber_event_mass z cap :=
    simpleRandomWalk_real_walkLift_tilingPreStoppingFiberEvent
      (spec.isStoppingTime z cap) (spec.tiling z cap) (spec.start z cap)
      (spec.retained z cap) cap (spec.tail z cap)
      (spec.basePredicate z cap)
  product_bound := spec.product_bound

/-- Complete capped product certificate for the all-six tiling coordinate
system. -/
def cappedProductScreenCertificateOfTilingStoppedCoordinateProductSpec
    {index : Type*} {piece : index → Set WalkPath}
    {next : Set WalkPath} {cost : ℝ≥0∞}
    (spec : TilingStoppedCoordinateProductSpec piece next cost) :
    CappedProductScreenCertificate piece next cost :=
  cappedProductScreenCertificateOfCoordinateMassSpec
    (coordinateMassSpecOfTilingStoppedCoordinateProductSpec spec)

/-- Complete existential trace screen for a genuine all-six favorite-stage
partition. -/
def someFavoriteTilingTraceCappedScreenOfStoppedCoordinateSpec
    (t : DominoTiling) (m k : ℕ) (stage next : Set WalkPath)
    (cost : ℝ≥0∞) (hstageMeasurable : MeasurableSet stage)
    (hstage : stage ⊆ thresholdReachStage m k) (hnext : next ⊆ stage)
    (spec : TilingStoppedCoordinateProductSpec
      (favoriteTilingStagePiece t m k stage) next cost) :
    SomeTraceCappedProductScreening stage next cost :=
  someTraceCappedProductScreeningOfFavoriteTilingStage t m k stage next cost
    hstageMeasurable hstage hnext
    (coordinateMassSpecOfTilingStoppedCoordinateProductSpec spec)

end

end Erdos1165.TilingStoppedProductDisintegration
