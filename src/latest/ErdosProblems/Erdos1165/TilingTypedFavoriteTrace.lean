import ErdosProblems.Erdos1165.TilingValidTraceCappedStageAdapter

/-!
# Typed non-null tiling trace codes

Raw external trace codes use an arbitrary block list.  Actual stateful
deletion always produces a retained list, so this module packages that proof
in the trace index.  Coordinate specifications can then read their retained
word and boundary tail directly, with no invalid-code fallback.
-/

open MeasureTheory Set
open scoped ENNReal

namespace Erdos1165.TilingTypedFavoriteTrace

open HLOZPathEvents VariableStoppedTracePartition
open TilingLazyDecomposition TilingSpatialInsertionFiber
open TilingVariableStoppedTracePartition
open TilingValidTraceCappedStageAdapter
open LazyDecomposition PathInsertion SpatialInsertionFiber
open VariableStoppedFiber
open HLOZTraceCappedProductScreening CappedCoordinateMassCertificate
open TilingStoppedProductDisintegration

noncomputable section

abbrev DominoTiling := Tilings.Tiling

/-- List form of the stateful retained-word predicate. -/
def ValidTilingRetainedList (t : DominoTiling) : Point → List Block → Prop
  | _, [] => True
  | x, b :: bs =>
      b ≠ tilingRemovableBlock t x ∧
        ValidTilingRetainedList t (blockEnd x b) bs

/-- The list predicate packages as the function-valued retained-word type. -/
theorem ValidTilingRetainedList.toRetainedWord
    (t : DominoTiling) (x : Point) (bs : List Block)
    (h : ValidTilingRetainedList t x bs) :
    ValidTilingRetainedWord t x (fun k ↦ bs.get k) := by
  induction bs generalizing x with
  | nil => intro k; exact Fin.elim0 k
  | cons b bs ih =>
      intro k
      refine Fin.cases ?_ (fun j ↦ ?_) k
      · simpa [rawExternalBase, followBlocks] using h.1
      · have htail := ih (blockEnd x b) h.2 j
        change bs.get j ≠
          tilingRemovableBlock t
            (rawExternalBase x (fun k ↦ (b :: bs).get k) j.succ.castSucc)
        rw [rawExternalBase_succ_castSucc]
        simpa using htail

/-- Stateful deletion always returns a statefully retained list. -/
theorem validTilingRetainedList_deleteTilingBlocks
    (t : DominoTiling) (x : Point) (bs : List Block) :
    ValidTilingRetainedList t x (deleteTilingBlocks t x bs) := by
  induction bs generalizing x with
  | nil => trivial
  | cons b bs ih =>
      by_cases hb : b = tilingRemovableBlock t x
      · simp [deleteTilingBlocks, hb, ih]
      · simp [deleteTilingBlocks, hb, ValidTilingRetainedList,
          ih (blockEnd x b)]

/-- Canonical typed retained word associated to a raw block list after
stateful deletion. -/
def deletedTilingRetainedWord (t : DominoTiling) (x : Point)
    (bs : List Block) :
    TilingRetainedWord t x (deleteTilingBlocks t x bs).length :=
  ⟨fun k ↦ (deleteTilingBlocks t x bs).get k,
    (validTilingRetainedList_deleteTilingBlocks t x bs).toRetainedWord
      t x (deleteTilingBlocks t x bs)⟩

/-- A typed external word carries the length, retained-word validity, and
the optional one-step boundary tail. -/
abbrev TilingTypedExternalWordCode (t : DominoTiling) :=
  Σ i : ℕ, TilingRetainedWord t (0, 0) i × BoundaryTail

/-- Typed non-null trace code, including the terminal favorite data. -/
abbrev TypedFavoriteTilingTraceCode (t : DominoTiling) :=
  TilingTypedExternalWordCode t × TilingCreationFavoriteData

/-- Forget the retained-word proof and recover the raw non-null trace code. -/
def eraseTypedFavoriteTilingTraceCode (t : DominoTiling)
    (z : TypedFavoriteTilingTraceCode t) : ValidFavoriteTilingTraceCode t :=
  ((List.ofFn z.1.2.1.1, z.1.2.2), z.2)

/-- Stage piece indexed by a genuinely retained external word. -/
def typedFavoriteTilingStagePiece (t : DominoTiling) (m k : ℕ)
    (stage : Set WalkPath) (z : TypedFavoriteTilingTraceCode t) : Set WalkPath :=
  validFavoriteTilingStagePiece t m k stage
    (eraseTypedFavoriteTilingTraceCode t z)

theorem measurableSet_typedFavoriteTilingStagePiece (t : DominoTiling)
    (m k : ℕ) {stage : Set WalkPath} (hstage : MeasurableSet stage)
    (z : TypedFavoriteTilingTraceCode t) :
    MeasurableSet (typedFavoriteTilingStagePiece t m k stage z) :=
  measurableSet_validFavoriteTilingStagePiece t m k hstage _

theorem disjoint_typedFavoriteTilingStagePiece_of_ne (t : DominoTiling)
    (m k : ℕ) (stage : Set WalkPath)
    {z w : TypedFavoriteTilingTraceCode t} (hzw : z ≠ w) :
    Disjoint (typedFavoriteTilingStagePiece t m k stage z)
      (typedFavoriteTilingStagePiece t m k stage w) := by
  apply disjoint_validFavoriteTilingStagePiece_of_ne t m k stage
  intro herase
  apply hzw
  rcases z with ⟨⟨i, r, tail⟩, data⟩
  rcases w with ⟨⟨i', r', tail'⟩, data'⟩
  simp only [eraseTypedFavoriteTilingTraceCode] at herase
  have hlist : List.ofFn r.1 = List.ofFn r'.1 := congrArg (fun u ↦ u.1.1) herase
  have htail : tail = tail' := congrArg (fun u ↦ u.1.2) herase
  have hdata : data = data' := congrArg Prod.snd herase
  have hlen : i = i' := by
    simpa using congrArg List.length hlist
  subst i'
  have hr : r = r' := by
    apply Subtype.ext
    exact List.ofFn_injective hlist
  subst r'
  subst tail'
  subst data'
  rfl

/-- The typed codes partition precisely the canonical part of any reaching
stage. -/
theorem iUnion_typedFavoriteTilingStagePiece (t : DominoTiling) (m k : ℕ)
    {stage : Set WalkPath} (hstage : stage ⊆ thresholdReachStage m k) :
    (⋃ z : TypedFavoriteTilingTraceCode t,
        typedFavoriteTilingStagePiece t m k stage z) =
      stage ∩ validStepWalk := by
  classical
  ext s
  constructor
  · intro hs
    rcases Set.mem_iUnion.mp hs with ⟨z, hz⟩
    exact (Set.ext_iff.mp
      (iUnion_validFavoriteTilingStagePiece t m k hstage) s).mp
        (Set.mem_iUnion.mpr ⟨eraseTypedFavoriteTilingTraceCode t z, hz⟩)
  · intro hs
    let omega := stepsOfWalk s
    let raw := prefixBlockWord (creationTimeNat m k s) omega
    let deleted := deleteTilingBlocks t (0, 0) raw
    let r := deletedTilingRetainedWord t (0, 0) raw
    let tail : BoundaryTail :=
      ⟨prefixDirectionTail (creationTimeNat m k s) omega,
        unpairedDirectionTail_length_le_one
          (incrementPrefixList (creationTimeNat m k s) omega)⟩
    let z : TypedFavoriteTilingTraceCode t :=
      (⟨deleted.length, r, tail⟩, tilingCreationFavoriteData t m k s)
    apply Set.mem_iUnion.mpr
    refine ⟨z, ?_⟩
    have hraw : eraseTypedFavoriteTilingTraceCode t z =
        (tilingCreationExternalCode t m k s,
          tilingCreationFavoriteData t m k s) := by
      apply Prod.ext
      · apply Prod.ext
        · change List.ofFn (fun k ↦ deleted.get k) = deleted
          exact List.ofFn_get deleted
        · rfl
      · rfl
    change s ∈ validFavoriteTilingStagePiece t m k stage
      (eraseTypedFavoriteTilingTraceCode t z)
    rw [hraw]
    exact ⟨⟨⟨⟨hstage hs.1, hs.2⟩, rfl⟩, rfl⟩, hs.1⟩

/-- A typed retained-word specification gives a complete capped trace screen
on canonical walk support. -/
def someTypedFavoriteTilingTraceCappedScreenOfStoppedCoordinateSpec
    (t : DominoTiling) (m k : ℕ) (stage next : Set WalkPath)
    (cost : ℝ≥0∞) (hstageMeasurable : MeasurableSet stage)
    (hstage : stage ⊆ thresholdReachStage m k) (hnext : next ⊆ stage)
    (spec : TilingStoppedCoordinateProductSpec
      (typedFavoriteTilingStagePiece t m k stage)
      (next ∩ validStepWalk) cost) :
    SomeTraceCappedProductScreening (stage ∩ validStepWalk)
      (next ∩ validStepWalk) cost := by
  exact someTraceCappedProductScreeningOfCoordinateMassSpec
    (stage ∩ validStepWalk) (next ∩ validStepWalk) cost
    (typedFavoriteTilingStagePiece t m k stage)
    (measurableSet_typedFavoriteTilingStagePiece t m k hstageMeasurable)
    (fun _ _ h ↦ disjoint_typedFavoriteTilingStagePiece_of_ne
      t m k stage h)
    (iUnion_typedFavoriteTilingStagePiece t m k hstage)
    (fun _ hs ↦ ⟨hnext hs.1, hs.2⟩)
    (coordinateMassSpecOfTilingStoppedCoordinateProductSpec spec)

/-- Typed-coordinate version of the valid-support transition theorem. -/
theorem transition_measure_le_of_typedFavoriteTilingStoppedCoordinateSpec
    (t : DominoTiling) (m k : ℕ) (stage next : Set WalkPath)
    (cost : ℝ≥0∞) (hstageMeasurable : MeasurableSet stage)
    (hnextMeasurable : MeasurableSet next)
    (hstage : stage ⊆ thresholdReachStage m k) (hnext : next ⊆ stage)
    (hcost : cost ≠ ∞)
    (spec : TilingStoppedCoordinateProductSpec
      (typedFavoriteTilingStagePiece t m k stage)
      (next ∩ validStepWalk) cost) :
    simpleRandomWalk next ≤ cost * simpleRandomWalk stage := by
  let cert := someTypedFavoriteTilingTraceCappedScreenOfStoppedCoordinateSpec
    t m k stage next cost hstageMeasurable hstage hnext spec
  have hvalidBound : simpleRandomWalk (next ∩ validStepWalk) ≤
      cost * simpleRandomWalk (stage ∩ validStepWalk) :=
    @transition_measure_le_of_traceCappedProductScreening cert.Index
      cert.countableIndex (stage ∩ validStepWalk) (next ∩ validStepWalk)
      (hnextMeasurable.inter measurableSet_validStepWalk) cost hcost
      cert.screening
  rw [← simpleRandomWalk_inter_validStepWalk next hnextMeasurable]
  exact hvalidBound.trans (by
    simpa only [mul_comm] using
      (mul_le_mul_left (measure_mono inter_subset_left) cost))

end

end Erdos1165.TilingTypedFavoriteTrace
