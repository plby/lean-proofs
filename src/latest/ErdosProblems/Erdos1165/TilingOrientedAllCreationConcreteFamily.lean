/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.TilingOrientedAllCreationStoppedCoordinate
import ErdosProblems.Erdos1165.TilingTypedTransitionFactorization
import ErdosProblems.Erdos1165.HLOZProposition48Candidates

/-!
# Concrete physical-prefix fibres for all creation traces

This file constructs the reusable pre-Theta coordinate family.  The only
inputs concerning the chosen finite support are deterministic: it is
measurable at the creation clock, depends only on the stopped prefix, and is
represented by the retained endpoint carrier.  The stopping clocks, capped
coordinates, atom predicate, cofinal coverage, and cap monotonicity are all
constructed here.
-/

open MeasureTheory Set

namespace Erdos1165.TilingOrientedAllCreationConcreteFamily

open HLOZPathEvents LazyDecomposition
open HLOZProposition48Candidates
open PreStoppingFiber SpatialInsertionFiber StoppedInsertion VariableStoppedFiber
open VariableStoppedTracePartition
open TilingCappedMarginalization TilingLazyDecomposition
open TilingSpatialInsertionFiber TilingTypedTransitionFactorization
open TilingDistinguishedTraceInvariant
open TilingOrientedShellZeroSourcePartition
open TilingOrientedPrefixedSupportBridge
open TilingOrientedSupportAwayCoordinates
open TilingPrefixedStoppedProductDisintegration
open TilingOrientedAllCreationStoppedCoordinate

noncomputable section

abbrev DominoTiling := Tilings.Tiling

local instance {t : DominoTiling} :
    MeasurableSpace (OrientedAllCreationTraceCode t) := ⊤

local instance {t : DominoTiling} :
    MeasurableSingletonClass (OrientedAllCreationTraceCode t) :=
  ⟨fun _ ↦ trivial⟩

/-- The exact deterministic properties of a creation-time support selector.
No probability estimate or source-goodness assertion occurs here. -/
structure OrientedAllCreationSupportSelectorData
    (t : DominoTiling) (o : Orientation) (m k : ℕ)
    (supportAt : WalkPath → ℕ → Finset Point) where
  measurableAtCreation : Measurable fun s ↦
    supportAt s (creationTimeNat m k s)
  prefix_invariant : ∀ {s s' : WalkPath} {n : ℕ},
    pathPrefix s n = pathPrefix s' n → supportAt s n = supportAt s' n
  represented : ∀ (s : WalkPath) (n : ℕ), s ∈ validStepWalk →
    supportAt s n ⊆ tilingExternalDominoBases t
      (fixedOrientedTypedExternalWordCode t o n s).start
      (fixedOrientedTypedExternalWordCode t o n s).retained

/-- The oriented external code as a literal function of the whole physical
increment list.  Factoring through this definition avoids dependent rewrites
through the retained-word proof fields. -/
def orientedTypedExternalWordCodeOfPrefix
    (t : DominoTiling) (o : Orientation) (whole : List Direction) :
    OrientedTilingTypedExternalWordCode t :=
  let directions := match o with
    | .even => whole
    | .shifted => whole.drop 1
  let initial : BoundaryTail := match o with
    | .even => ⟨[], by simp⟩
    | .shifted => ⟨whole.take 1, List.length_take_le _ _⟩
  let start := trajectory (extendPrefix (directionVectorOfList initial.1))
    initial.1.length
  let blocks := pairDirectionList directions
  let retained := TilingTypedFavoriteTrace.deletedTilingRetainedWord
    t start blocks
  { initial := initial
    retainedCount := (deleteTilingBlocks t start blocks).length
    retained := retained
    tail := ⟨unpairedDirectionTail directions,
      unpairedDirectionTail_length_le_one directions⟩ }

theorem fixedOrientedTypedExternalWordCode_eq_ofPrefix
    (t : DominoTiling) (o : Orientation) (n : ℕ) (s : WalkPath) :
    fixedOrientedTypedExternalWordCode t o n s =
      orientedTypedExternalWordCodeOfPrefix t o
        (incrementPrefixList n (stepsOfWalk s)) := by
  cases o <;> rfl

/-- The oriented retained external code is fixed by the physical prefix. -/
theorem fixedOrientedTypedExternalWordCode_eq_of_pathPrefix_eq
    (t : DominoTiling) (o : Orientation) {s s' : WalkPath} {n : ℕ}
    (hp : pathPrefix s n = pathPrefix s' n) :
    fixedOrientedTypedExternalWordCode t o n s =
      fixedOrientedTypedExternalWordCode t o n s' := by
  have hstep := stepPrefix_stepsOfWalk_eq_of_pathPrefix_eq hp
  have hword : incrementPrefixList n (stepsOfWalk s) =
      incrementPrefixList n (stepsOfWalk s') := by
    unfold incrementPrefixList
    rw [hstep]
  rw [fixedOrientedTypedExternalWordCode_eq_ofPrefix,
    fixedOrientedTypedExternalWordCode_eq_ofPrefix, hword]

/-- Equality of the complete all-creation trace is fixed by the physical
path prefix. -/
theorem fixedOrientedAllCreationTraceCode_eq_of_pathPrefix_eq
    (t : DominoTiling) (o : Orientation) {s s' : WalkPath} {n : ℕ}
    (hp : pathPrefix s n = pathPrefix s' n) :
    fixedOrientedAllCreationTraceCode t o n s =
      fixedOrientedAllCreationTraceCode t o n s' := by
  unfold fixedOrientedAllCreationTraceCode
  rw [OrientedAllCreationTraceCode.mk.injEq]
  constructor
  · exact fixedOrientedTypedExternalWordCode_eq_of_pathPrefix_eq t o hp
  · apply Prod.ext
    · apply Prod.ext
      · unfold favoriteSites
        rw [hp]
      · congr 1
        unfold favoriteSites
        rw [hp]
    · apply Prod.ext
      · exact congrArg OrientedTilingTypedExternalWordCode.start
          (fixedOrientedTypedExternalWordCode_eq_of_pathPrefix_eq t o hp)
      · exact walkPoint_eq_of_pathPrefix_eq hp (Nat.le_refl n)

/-- A function into a countable discrete space is measurable when it is
constant on every deterministic path-prefix fibre. -/
theorem measurable_of_pathPrefix_invariant
    {alpha : Type*} [MeasurableSpace alpha] [Countable alpha]
    [MeasurableSingletonClass alpha]
    (n : ℕ) (f : WalkPath → alpha)
    (hf : ∀ {s s' : WalkPath}, pathPrefix s n = pathPrefix s' n →
      f s = f s') : Measurable f := by
  classical
  let defaultPath : WalkPath := fun _ ↦ 0
  let representative (u : Fin (n + 1) → Point) : WalkPath :=
    if h : ∃ s, pathPrefix s n = u then Classical.choose h else defaultPath
  let F : (Fin (n + 1) → Point) → alpha := fun u ↦ f (representative u)
  have hfactor : f = F ∘ pathPrefix (n := n) := by
    funext s
    change f s = f (representative (pathPrefix s n))
    apply hf
    dsimp only [representative]
    rw [dif_pos ⟨s, rfl⟩]
    have hrep := Classical.choose_spec
      (show ∃ s' : WalkPath, pathPrefix s' n = pathPrefix s n from ⟨s, rfl⟩)
    exact hrep.symm
  rw [hfactor]
  exact (measurable_of_countable F).comp (measurable_pathPrefix n)

theorem measurable_fixedOrientedAllCreationTraceCode
    (t : DominoTiling) (o : Orientation) (n : ℕ) :
    Measurable (fixedOrientedAllCreationTraceCode t o n) := by
  apply measurable_of_pathPrefix_invariant n
  exact fixedOrientedAllCreationTraceCode_eq_of_pathPrefix_eq t o

theorem measurable_orientedAllCreationTraceCodeAtCreation
    (t : DominoTiling) (o : Orientation) (m k : ℕ) :
    Measurable fun s ↦ fixedOrientedAllCreationTraceCode t o
      (creationTimeNat m k s) s := by
  exact measurable_natIndexed (creationTimeNat m k)
    (measurable_creationTimeNat m k)
    (fixedOrientedAllCreationTraceCode t o)
    (measurable_fixedOrientedAllCreationTraceCode t o)

theorem measurableSet_orientedAllCreationTraceAtom
    (t : DominoTiling) (o : Orientation) (m k : ℕ)
    (z : OrientedAllCreationTraceCode t) :
    MeasurableSet (orientedAllCreationTraceAtom t o m k z) := by
  have heq : orientedAllCreationTraceAtom t o m k z =
      validStepWalk ∩ thresholdReachStage m k ∩
        {s | fixedOrientedAllCreationTraceCode t o
          (creationTimeNat m k s) s = z} := by
    ext s
    simp only [orientedAllCreationTraceAtom, Set.mem_ofPred_eq,
      Set.mem_inter_iff, thresholdReachStage]
    tauto
  rw [heq]
  exact (measurableSet_validStepWalk.inter
    (measurableSet_thresholdReachStage m k)).inter
      (measurableSet_eq_fun
        (measurable_orientedAllCreationTraceCodeAtCreation t o m k)
        measurable_const)

/-- A cutoff which is strictly beyond every prefixed insertion word whose
coordinates are bounded by `cap`. -/
def orientedAllCreationCoordinateCutoff
    {t : DominoTiling} (z : OrientedAllCreationTraceCode t)
    (cap : ℕ) : ℕ :=
  z.external.initial.1.length +
    2 * (z.external.retainedCount +
      (z.external.retainedCount + 1) * cap) +
    z.external.tail.1.length + 1

theorem prefixedInsertion_lt_orientedAllCreationCoordinateCutoff
    {t : DominoTiling} (z : OrientedAllCreationTraceCode t)
    (cap : ℕ) (q : TilingCappedCoordinates z.external.retainedCount cap) :
    (prefixedTilingInsertionPrefixList z.external.initial.1 t
      z.external.start z.external.retained (fun j ↦ (q j : ℕ))
      z.external.tail.1).length <
        orientedAllCreationCoordinateCutoff z cap := by
  change (prefixedTilingInsertionPrefixList z.external.initial.1 t
      (trajectory (extendPrefix
        (directionVectorOfList z.external.initial.1))
        z.external.initial.1.length)
      z.external.retained (fun j ↦ (q j : ℕ))
      z.external.tail.1).length <
        orientedAllCreationCoordinateCutoff z cap
  rw [prefixedTilingInsertionPrefixList_length]
  have hsum : ∑ j, (q j : ℕ) ≤
      (z.external.retainedCount + 1) * cap := by
    calc
      ∑ j, (q j : ℕ) ≤ ∑ _j : Fin (z.external.retainedCount + 1), cap := by
        apply Finset.sum_le_sum
        intro j _hj
        exact Nat.le_of_lt_succ (q j).isLt
      _ = (z.external.retainedCount + 1) * cap := by simp
  unfold orientedAllCreationCoordinateCutoff
  omega

theorem orientedAllCreationCoordinateCutoff_mono
    {t : DominoTiling} (z : OrientedAllCreationTraceCode t) :
    Monotone (orientedAllCreationCoordinateCutoff z) := by
  intro cap cap' hcap
  unfold orientedAllCreationCoordinateCutoff
  have hmul : (z.external.retainedCount + 1) * cap ≤
      (z.external.retainedCount + 1) * cap' :=
    Nat.mul_le_mul_left _ hcap
  omega

/-- Membership in a physical-prefix stopped atom fixes the whole path prefix
through the end of the insertion word. -/
theorem pathPrefix_eq_canonical_of_mem_prefixedTilingStoppedInsertionAtom
    {t : DominoTiling} {τ : StepPath → ℕ} {i : ℕ}
    (initial : List Direction) (x : Point)
    (r : TilingRetainedWord t x i) (q : Fin (i + 1) → ℕ)
    (tail : List Direction) (omega : StepPath)
    (homega : omega ∈ prefixedTilingStoppedInsertionAtom τ initial t x r q tail) :
    let v := prefixedTilingInsertionPrefixList initial t x r q tail
    pathPrefix (trajectory omega) v.length =
      pathPrefix
        (trajectory (extendPrefix (directionVectorOfList v))) v.length := by
  let v := prefixedTilingInsertionPrefixList initial t x r q tail
  change τ omega = v.length ∧ incrementPrefixList v.length omega = v at homega
  have hstep : stepPrefix v.length omega = directionVectorOfList v :=
    (incrementPrefixList_eq_iff_stepPrefix_eq_directionVector omega v).mp
      homega.2
  calc
    pathPrefix (trajectory omega) v.length =
        trajectoryPrefix (stepPrefix v.length omega) :=
      (trajectoryPrefix_stepPrefix omega v.length).symm
    _ = trajectoryPrefix (directionVectorOfList v) := by rw [hstep]
    _ = pathPrefix
        (trajectory (extendPrefix (directionVectorOfList v))) v.length := by
      simpa only [stepPrefix_extendPrefix] using
        trajectoryPrefix_stepPrefix
          (extendPrefix (directionVectorOfList v)) v.length

/-- The actual physical increment prefix produces its own path prefix under
the canonical eventually-constant reconstruction. -/
theorem pathPrefix_canonical_eq_of_prefixedInsertionPrefix_eq
    {t : DominoTiling} {i n : ℕ} (s : WalkPath)
    (initial : List Direction) (x : Point)
    (r : TilingRetainedWord t x i) (q : Fin (i + 1) → ℕ)
    (tail : List Direction)
    (hvalid : s ∈ validStepWalk)
    (hword : prefixedTilingInsertionPrefixList initial t x r q tail =
      incrementPrefixList n (stepsOfWalk s)) :
    pathPrefix
        (trajectory (extendPrefix (directionVectorOfList
          (prefixedTilingInsertionPrefixList initial t x r q tail)))) n =
      pathPrefix s n := by
  have hlen : (prefixedTilingInsertionPrefixList initial t x r q tail).length = n := by
    rw [hword]
    simp [incrementPrefixList]
  have hstep : stepPrefix n
      (extendPrefix (directionVectorOfList
        (prefixedTilingInsertionPrefixList initial t x r q tail))) =
      stepPrefix n (stepsOfWalk s) := by
    apply List.ofFn_injective
    change incrementPrefixList n
        (extendPrefix (directionVectorOfList
          (prefixedTilingInsertionPrefixList initial t x r q tail))) =
      incrementPrefixList n (stepsOfWalk s)
    rw [← hword]
    unfold incrementPrefixList
    rw [show n = (prefixedTilingInsertionPrefixList initial t x r q tail).length
      from hlen.symm]
    rw [stepPrefix_extendPrefix, ofFn_directionVectorOfList]
  calc
    pathPrefix
        (trajectory (extendPrefix (directionVectorOfList
          (prefixedTilingInsertionPrefixList initial t x r q tail)))) n =
      trajectoryPrefix (stepPrefix n
        (extendPrefix (directionVectorOfList
          (prefixedTilingInsertionPrefixList initial t x r q tail)))) :=
      (trajectoryPrefix_stepPrefix _ n).symm
    _ = trajectoryPrefix (stepPrefix n (stepsOfWalk s)) := by rw [hstep]
    _ = pathPrefix (trajectory (stepsOfWalk s)) n :=
      trajectoryPrefix_stepPrefix (stepsOfWalk s) n
    _ = pathPrefix s n := by rw [show trajectory (stepsOfWalk s) = s from hvalid]

/-- The cylinder predicate used by the concrete fibre. -/
def orientedAllCreationStoppedAtomPredicate
    {t : DominoTiling} (o : Orientation) (m k : ℕ)
    (supportAt : WalkPath → ℕ → Finset Point)
    (S : Finset Point) (z : OrientedAllCreationTraceCode t)
    (cap : ℕ)
    (q : TilingCappedCoordinates z.external.retainedCount cap) : Prop :=
  prefixedTilingStoppedInsertionAtom
      (truncatedLevelTime m k (orientedAllCreationCoordinateCutoff z cap))
      z.external.initial.1 t z.external.start z.external.retained
      (fun j ↦ (q j : ℕ)) z.external.tail.1 ⊆
    trajectory ⁻¹'
      orientedAllCreationSupportTraceAtom t o m k supportAt z S

/-- The common distinguished selector is the existential projection of the
literal stopped atom along the away coordinates. -/
def orientedAllCreationSelected
    {t : DominoTiling} (o : Orientation) (m k : ℕ)
    (supportAt : WalkPath → ℕ → Finset Point)
    (S : Finset Point) (z : OrientedAllCreationTraceCode t)
    (cap : ℕ)
    (d : TilingDistinguishedCoordinates (cap := cap) t z.external.start
      z.external.retained
      (supportComplementDistinguished t z.external.start
        z.external.retained S)) : Prop :=
  ∃ a, let q :=
      (splitTilingCoordinatesEquiv t z.external.start z.external.retained
        (supportComplementDistinguished t z.external.start
          z.external.retained S)).symm (d, a)
    orientedAllCreationStoppedAtomPredicate o m k supportAt S z cap q ∧
      PrefixedTilingStoppingAccepted
        (truncatedLevelTime m k
          (orientedAllCreationCoordinateCutoff z cap))
        z.external.initial.1 t z.external.start z.external.retained
        (fun j ↦ (q j : ℕ)) z.external.tail.1

/-- Embed coordinates into a larger cap without changing their natural
values. -/
def castAllCreationCappedCoordinates
    {t : DominoTiling} (z : OrientedAllCreationTraceCode t)
    {cap cap' : ℕ} (hcap : cap ≤ cap')
    (q : TilingCappedCoordinates z.external.retainedCount cap) :
    TilingCappedCoordinates z.external.retainedCount cap' :=
  fun j ↦ Fin.castLE (Nat.succ_le_succ hcap) (q j)

@[simp] theorem coe_castAllCreationCappedCoordinates
    {t : DominoTiling} (z : OrientedAllCreationTraceCode t)
    {cap cap' : ℕ} (hcap : cap ≤ cap')
    (q : TilingCappedCoordinates z.external.retainedCount cap) (j) :
    ((castAllCreationCappedCoordinates z hcap q j : Fin (cap' + 1)) : ℕ) =
      (q j : ℕ) := rfl

theorem prefixedStoppingAccepted_castAllCreation
    {t : DominoTiling} (m k : ℕ) (z : OrientedAllCreationTraceCode t)
    {cap cap' : ℕ} (hcap : cap ≤ cap')
    (q : TilingCappedCoordinates z.external.retainedCount cap)
    (haccepted : PrefixedTilingStoppingAccepted
      (truncatedLevelTime m k (orientedAllCreationCoordinateCutoff z cap))
      z.external.initial.1 t z.external.start z.external.retained
      (fun j ↦ (q j : ℕ)) z.external.tail.1) :
    PrefixedTilingStoppingAccepted
      (truncatedLevelTime m k (orientedAllCreationCoordinateCutoff z cap'))
      z.external.initial.1 t z.external.start z.external.retained
      (fun j ↦ (castAllCreationCappedCoordinates z hcap q j : ℕ))
      z.external.tail.1 := by
  let v := prefixedTilingInsertionPrefixList z.external.initial.1 t
    z.external.start z.external.retained (fun j ↦ (q j : ℕ))
    z.external.tail.1
  have hlt := prefixedInsertion_lt_orientedAllCreationCoordinateCutoff z cap q
  have hcreation : ThresholdCreation
      (trajectory (extendPrefix (directionVectorOfList v))) m k v.length :=
    (truncatedLevelTime_eq_iff_thresholdCreation_of_lt_cutoff
      m k (orientedAllCreationCoordinateCutoff z cap) v.length _ hlt).mp
        haccepted
  have hlt' : v.length < orientedAllCreationCoordinateCutoff z cap' :=
    hlt.trans_le (orientedAllCreationCoordinateCutoff_mono z hcap)
  apply (truncatedLevelTime_eq_iff_thresholdCreation_of_lt_cutoff
    m k (orientedAllCreationCoordinateCutoff z cap') v.length _ hlt').mpr
  simpa only [v, coe_castAllCreationCappedCoordinates] using hcreation

theorem orientedAllCreationStoppedAtomPredicate_cast
    {t : DominoTiling} (o : Orientation) (m k : ℕ)
    (supportAt : WalkPath → ℕ → Finset Point)
    (S : Finset Point) (z : OrientedAllCreationTraceCode t)
    {cap cap' : ℕ} (hcap : cap ≤ cap')
    (q : TilingCappedCoordinates z.external.retainedCount cap)
    (hpred : orientedAllCreationStoppedAtomPredicate
      o m k supportAt S z cap q)
    (haccepted : PrefixedTilingStoppingAccepted
      (truncatedLevelTime m k (orientedAllCreationCoordinateCutoff z cap))
      z.external.initial.1 t z.external.start z.external.retained
      (fun j ↦ (q j : ℕ)) z.external.tail.1) :
    orientedAllCreationStoppedAtomPredicate o m k supportAt S z cap'
      (castAllCreationCappedCoordinates z hcap q) := by
  have haccepted' := prefixedStoppingAccepted_castAllCreation
    m k z hcap q haccepted
  intro omega homega
  apply hpred
  rw [prefixedTilingStoppedInsertionAtom_eq_cylinder
    (isFiniteStoppingTime_truncatedLevelTime m k
      (orientedAllCreationCoordinateCutoff z cap))
    z.external.initial.1 t z.external.start z.external.retained
    (fun j ↦ (q j : ℕ)) z.external.tail.1 haccepted]
  rw [prefixedTilingStoppedInsertionAtom_eq_cylinder
    (isFiniteStoppingTime_truncatedLevelTime m k
      (orientedAllCreationCoordinateCutoff z cap'))
    z.external.initial.1 t z.external.start z.external.retained
    (fun j ↦ (castAllCreationCappedCoordinates z hcap q j : ℕ))
    z.external.tail.1 haccepted'] at homega
  simpa only [coe_castAllCreationCappedCoordinates] using homega

/-- The lifted exact-atom fibres constructed from the cylinder predicate are
monotone along the affine cap schedule. -/
theorem monotone_orientedAllCreationStoppedAtomFiber
    {t : DominoTiling} (o : Orientation) (m k capStart : ℕ)
    (supportAt : WalkPath → ℕ → Finset Point)
    (S : Finset Point) (z : OrientedAllCreationTraceCode t) :
    Monotone fun cap ↦ walkLift
      (prefixedTilingPreStoppingFiberEvent
        (truncatedLevelTime m k
          (orientedAllCreationCoordinateCutoff z (capStart + cap)))
        z.external.initial.1 t z.external.start z.external.retained
        (capStart + cap) z.external.tail.1
        (orientedAllCreationStoppedAtomPredicate
          o m k supportAt S z (capStart + cap))) := by
  intro cap cap' hcap s hs
  rcases hs with ⟨hvalid, hevent⟩
  rcases Set.mem_iUnion.mp hevent with ⟨q, hq⟩
  have htotal : capStart + cap ≤ capStart + cap' := Nat.add_le_add_left hcap _
  let q' := castAllCreationCappedCoordinates z htotal q.1
  have haccepted' := prefixedStoppingAccepted_castAllCreation
    m k z htotal q.1 q.2.2
  refine ⟨hvalid, Set.mem_iUnion.mpr ⟨⟨q', ?_, haccepted'⟩, ?_⟩⟩
  · exact orientedAllCreationStoppedAtomPredicate_cast
      o m k supportAt S z htotal q.1 q.2.1 q.2.2
  · rw [prefixedTilingStoppedInsertionAtom_eq_cylinder
      (isFiniteStoppingTime_truncatedLevelTime m k
        (orientedAllCreationCoordinateCutoff z (capStart + cap')))
      z.external.initial.1 t z.external.start z.external.retained
      (fun j ↦ (q' j : ℕ)) z.external.tail.1 haccepted']
    rw [prefixedTilingStoppedInsertionAtom_eq_cylinder
      (isFiniteStoppingTime_truncatedLevelTime m k
        (orientedAllCreationCoordinateCutoff z (capStart + cap)))
      z.external.initial.1 t z.external.start z.external.retained
      (fun j ↦ (q.1 j : ℕ)) z.external.tail.1 q.2.2] at hq
    simpa only [q', coe_castAllCreationCappedCoordinates] using hq

/-- Coordinates reconstructed from a path in an exact `(trace,S)` atom are
accepted by the genuine creation clock and their whole stopped cylinder stays
inside that same atom. -/
theorem reconstructedCoordinates_mem_exactAtom
    {t : DominoTiling} (o : Orientation) (m k : ℕ)
    (supportAt : WalkPath → ℕ → Finset Point)
    (supportData : OrientedAllCreationSupportSelectorData t o m k supportAt)
    (S : Finset Point) (z : OrientedAllCreationTraceCode t)
    (s : WalkPath)
    (hs : s ∈ orientedAllCreationSupportTraceAtom t o m k supportAt z S)
    (q : Fin (z.external.retainedCount + 1) → ℕ)
    (hword : prefixedTilingInsertionPrefixList z.external.initial.1 t
      z.external.start z.external.retained q z.external.tail.1 =
        incrementPrefixList (creationTimeNat m k s) (stepsOfWalk s))
    (cap : ℕ) (hqcap : ∀ j, q j ≤ cap) :
    let qc : TilingCappedCoordinates z.external.retainedCount cap :=
      fun j ↦ ⟨q j, Nat.lt_succ_of_le (hqcap j)⟩
    orientedAllCreationStoppedAtomPredicate
        o m k supportAt S z cap qc ∧
      PrefixedTilingStoppingAccepted
        (truncatedLevelTime m k (orientedAllCreationCoordinateCutoff z cap))
        z.external.initial.1 t z.external.start z.external.retained
        (fun j ↦ (qc j : ℕ)) z.external.tail.1 := by
  classical
  let n := creationTimeNat m k s
  let qc : TilingCappedCoordinates z.external.retainedCount cap :=
    fun j ↦ ⟨q j, Nat.lt_succ_of_le (hqcap j)⟩
  let v := prefixedTilingInsertionPrefixList z.external.initial.1 t
    z.external.start z.external.retained q z.external.tail.1
  have hvalid : s ∈ validStepWalk := hs.1.1
  have hreach : ReachesThreshold s m k := hs.1.2.1
  have hcreation : ThresholdCreation s m k n := by
    let hr : ReachesThreshold s m k := hreach
    have hfind := thresholdCreation_natFind hr
    simpa only [n, creationTimeNat, dif_pos hr] using hfind
  have hlen : v.length = n := by
    rw [show v = incrementPrefixList n (stepsOfWalk s) from hword]
    simp [incrementPrefixList]
  have hwordV : v = incrementPrefixList v.length (stepsOfWalk s) := by
    simpa only [hlen] using hword
  have hcreationV : ThresholdCreation s m k v.length := by
    rw [hlen]
    exact hcreation
  have hcanonicalPrefix : pathPrefix
      (trajectory (extendPrefix (directionVectorOfList v))) v.length =
        pathPrefix s v.length := by
    exact pathPrefix_canonical_eq_of_prefixedInsertionPrefix_eq s
      z.external.initial.1 z.external.start z.external.retained q
      z.external.tail.1 hvalid hwordV
  have hcanonicalCreation : ThresholdCreation
      (trajectory (extendPrefix (directionVectorOfList v))) m k v.length :=
    (thresholdCreation_iff_of_pathPrefix_eq hcanonicalPrefix
      (Nat.le_refl v.length)).mpr hcreationV
  have hlt : v.length < orientedAllCreationCoordinateCutoff z cap := by
    simpa only [v, qc] using
      (prefixedInsertion_lt_orientedAllCreationCoordinateCutoff z cap qc)
  have haccepted : PrefixedTilingStoppingAccepted
      (truncatedLevelTime m k (orientedAllCreationCoordinateCutoff z cap))
      z.external.initial.1 t z.external.start z.external.retained
      (fun j ↦ (qc j : ℕ)) z.external.tail.1 := by
    apply (truncatedLevelTime_eq_iff_thresholdCreation_of_lt_cutoff
      m k (orientedAllCreationCoordinateCutoff z cap) v.length _ hlt).mpr
    simpa only [v, qc] using hcanonicalCreation
  refine ⟨?_, haccepted⟩
  intro omega homega
  let somega := trajectory omega
  have homegaCanonical : pathPrefix somega v.length =
      pathPrefix (trajectory (extendPrefix (directionVectorOfList v)))
        v.length := by
    simpa only [somega, v, qc] using
      (pathPrefix_eq_canonical_of_mem_prefixedTilingStoppedInsertionAtom
        z.external.initial.1 z.external.start z.external.retained
        (fun j ↦ (qc j : ℕ)) z.external.tail.1 omega homega)
  have homegaS : pathPrefix somega v.length = pathPrefix s v.length :=
    homegaCanonical.trans hcanonicalPrefix
  have homegaCreation : ThresholdCreation somega m k v.length :=
    (thresholdCreation_iff_of_pathPrefix_eq homegaS
      (Nat.le_refl v.length)).mpr hcreationV
  have homegaTime : creationTimeNat m k somega = v.length :=
    creationTimeNat_eq_of_creation homegaCreation
  refine ⟨⟨trajectory_mem_validStepWalk omega,
    ⟨v.length, homegaCreation.1⟩, ?_⟩, ?_⟩
  · change fixedOrientedAllCreationTraceCode t o
      (creationTimeNat m k somega) somega = z
    rw [homegaTime]
    have hsCode : fixedOrientedAllCreationTraceCode t o v.length s = z := by
      rw [hlen]
      exact hs.1.2.2
    exact (fixedOrientedAllCreationTraceCode_eq_of_pathPrefix_eq
      t o homegaS).trans hsCode
  · change supportAt somega (creationTimeNat m k somega) = S
    rw [homegaTime]
    have hsSupport : supportAt s v.length = S := by
      rw [hlen]
      exact hs.2
    exact (supportData.prefix_invariant homegaS).trans hsSupport

/-- Every path in an exact supported atom occurs in some cap of the concrete
physical-prefix fibre. -/
theorem exactAtom_subset_iUnion_orientedAllCreationStoppedAtomFiber
    {t : DominoTiling} (o : Orientation) (m k capStart : ℕ)
    (supportAt : WalkPath → ℕ → Finset Point)
    (supportData : OrientedAllCreationSupportSelectorData t o m k supportAt)
    (S : Finset Point) (z : OrientedAllCreationTraceCode t) :
    orientedAllCreationSupportTraceAtom t o m k supportAt z S ⊆
      ⋃ cap, walkLift
        (prefixedTilingPreStoppingFiberEvent
          (truncatedLevelTime m k
            (orientedAllCreationCoordinateCutoff z (capStart + cap)))
          z.external.initial.1 t z.external.start z.external.retained
          (capStart + cap) z.external.tail.1
          (orientedAllCreationStoppedAtomPredicate
            o m k supportAt S z (capStart + cap))) := by
  classical
  intro s hs
  let n := creationTimeNat m k s
  obtain ⟨q, hword⟩ :=
    exists_prefixedTilingInsertionPrefixList_eq_incrementPrefixList
      t o n s z.external
        (congrArg OrientedAllCreationTraceCode.external hs.1.2.2)
  let cap := ∑ j, q j
  have hqcap (j : Fin (z.external.retainedCount + 1)) :
      q j ≤ capStart + cap := by
    have hj : q j ≤ cap :=
      Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _)
        (Finset.mem_univ j)
    omega
  let qc : TilingCappedCoordinates z.external.retainedCount
      (capStart + cap) := fun j ↦
    ⟨q j, Nat.lt_succ_of_le (hqcap j)⟩
  have hdata := reconstructedCoordinates_mem_exactAtom
    o m k supportAt supportData S z s hs q hword
    (capStart + cap) hqcap
  have hvalid : s ∈ validStepWalk := hs.1.1
  have hlen : (prefixedTilingInsertionPrefixList z.external.initial.1 t
      z.external.start z.external.retained q z.external.tail.1).length = n := by
    rw [hword]
    simp [incrementPrefixList]
  have hstepmem : stepsOfWalk s ∈ prefixedTilingStoppedInsertionAtom
      (truncatedLevelTime m k
        (orientedAllCreationCoordinateCutoff z (capStart + cap)))
      z.external.initial.1 t z.external.start z.external.retained
      (fun j ↦ (qc j : ℕ)) z.external.tail.1 := by
    rw [prefixedTilingStoppedInsertionAtom_eq_cylinder
      (isFiniteStoppingTime_truncatedLevelTime m k
        (orientedAllCreationCoordinateCutoff z (capStart + cap)))
      z.external.initial.1 t z.external.start z.external.retained
      (fun j ↦ (qc j : ℕ)) z.external.tail.1 hdata.2]
    apply List.ofFn_injective
    rw [ofFn_directionVectorOfList]
    change incrementPrefixList
        (prefixedTilingInsertionPrefixList z.external.initial.1 t
          z.external.start z.external.retained
          (fun j ↦ (qc j : ℕ)) z.external.tail.1).length
        (stepsOfWalk s) =
      prefixedTilingInsertionPrefixList z.external.initial.1 t
        z.external.start z.external.retained
        (fun j ↦ (qc j : ℕ)) z.external.tail.1
    simpa only [qc, hlen] using hword.symm
  apply Set.mem_iUnion.mpr
  refine ⟨cap, ⟨hvalid, Set.mem_iUnion.mpr ⟨⟨qc, hdata.1, hdata.2⟩,
    hstepmem⟩⟩⟩

/-- The cylinder predicate makes the lifted stopped fibre a literal subset
of its exact supported atom. -/
theorem walkLift_orientedAllCreationStoppedAtomFiber_subset
    {t : DominoTiling} (o : Orientation) (m k : ℕ)
    (supportAt : WalkPath → ℕ → Finset Point)
    (S : Finset Point) (z : OrientedAllCreationTraceCode t)
    (cap : ℕ) :
    walkLift
      (prefixedTilingPreStoppingFiberEvent
        (truncatedLevelTime m k
          (orientedAllCreationCoordinateCutoff z cap))
        z.external.initial.1 t z.external.start z.external.retained cap
        z.external.tail.1
        (orientedAllCreationStoppedAtomPredicate
          o m k supportAt S z cap)) ⊆
      orientedAllCreationSupportTraceAtom t o m k supportAt z S := by
  intro s hs
  rcases hs with ⟨hvalid, hevent⟩
  rcases Set.mem_iUnion.mp hevent with ⟨q, hq⟩
  have hatom := q.2.1 hq
  change trajectory (stepsOfWalk s) ∈
    orientedAllCreationSupportTraceAtom t o m k supportAt z S at hatom
  rw [show trajectory (stepsOfWalk s) = s from hvalid] at hatom
  exact hatom

/-- One fully concrete pre-source fibre.  Its cap-zero coordinates already
cover both the retained multiplicity and the complete source window used by
the broad/narrow screens.  The ambient truncation is one larger; the later
broad acceptor records the genuine favorite/source classification. -/
noncomputable def orientedAllCreationConcreteFiber
    {t : DominoTiling} (o : Orientation) (m k : ℕ)
    (supportAt : WalkPath → ℕ → Finset Point)
    (supportData : OrientedAllCreationSupportSelectorData t o m k supportAt)
    (eta : OrientedAllCreationSupportedAtomIndex t o m k supportAt) :
    OrientedAllCreationPrefixedStoppedCoordinateSpec t o m k supportAt
      eta.1.2 eta.1.1 := by
  classical
  let z := eta.1.1
  let S := eta.1.2
  have hrepresented : S ⊆
      tilingExternalDominoBases t z.external.start z.external.retained := by
    obtain ⟨s, hs⟩ := eta.2
    have hrep := supportData.represented s (creationTimeNat m k s) hs.1.1
    have hext : fixedOrientedTypedExternalWordCode t o
        (creationTimeNat m k s) s = z.external :=
      congrArg OrientedAllCreationTraceCode.external hs.1.2.2
    have hsupport : supportAt s (creationTimeNat m k s) = S := hs.2
    rw [hext] at hrep
    simpa only [hsupport] using hrep
  refine {
    coordinateCap := fun cap ↦
      max z.external.retainedCount (m + shellWidth48 m) + cap
    capStart := max z.external.retainedCount (m + shellWidth48 m)
    coordinateCap_eq := fun _ ↦ rfl
    totalCap := max z.external.retainedCount (m + shellWidth48 m)
    totalCap_le_capStart := le_rfl
    retainedCount_le_totalCap := Nat.le_max_left _ _
    stoppingTime := fun cap ↦ truncatedLevelTime m k
      (orientedAllCreationCoordinateCutoff z
        (max z.external.retainedCount (m + shellWidth48 m) + cap))
    isStoppingTime := fun cap ↦ isFiniteStoppingTime_truncatedLevelTime
      m k (orientedAllCreationCoordinateCutoff z
        (max z.external.retainedCount (m + shellWidth48 m) + cap))
    atomPredicate := fun cap ↦ orientedAllCreationStoppedAtomPredicate
      o m k supportAt S z
        (max z.external.retainedCount (m + shellWidth48 m) + cap)
    support_represented := hrepresented
    selected := fun cap ↦ orientedAllCreationSelected o m k supportAt S z
      (max z.external.retainedCount (m + shellWidth48 m) + cap)
    upper := fun _cap _b ↦
      max z.external.retainedCount (m + shellWidth48 m) + 1
    upper_pos := by intro _cap _b; omega
    totalCap_lt_upper := by intro _cap _b; omega
    atom_measurable := measurableSet_orientedAllCreationSupportTraceAtom_of
      t o m k supportAt z S
      (measurableSet_orientedAllCreationTraceAtom t o m k z)
      supportData.measurableAtCreation
    atom_sound := fun cap ↦
      walkLift_orientedAllCreationStoppedAtomFiber_subset o m k supportAt S z
        (max z.external.retainedCount (m + shellWidth48 m) + cap)
    atom_complete := exactAtom_subset_iUnion_orientedAllCreationStoppedAtomFiber
      o m k (max z.external.retainedCount (m + shellWidth48 m))
        supportAt supportData S z
    atom_monotone := monotone_orientedAllCreationStoppedAtomFiber
      o m k (max z.external.retainedCount (m + shellWidth48 m))
        supportAt S z }

/-- The promised reusable literal family: every nonempty exact `(trace,S)`
atom receives the concrete physical-prefix stopped-coordinate fibre above. -/
noncomputable def orientedAllCreationConcreteFamily
    (t : DominoTiling) (o : Orientation) (m k : ℕ)
    (supportAt : WalkPath → ℕ → Finset Point)
    (supportData : OrientedAllCreationSupportSelectorData t o m k supportAt) :
    OrientedAllCreationPrefixedStoppedCoordinateFamily
      t o m k supportAt where
  fiber eta := orientedAllCreationConcreteFiber
    o m k supportAt supportData eta

end

end Erdos1165.TilingOrientedAllCreationConcreteFamily
