import ErdosProblems.Erdos1165.VariableStoppedFiber
import ErdosProblems.Erdos1165.HLOZStoppedProductRefinement

open Filter MeasureTheory Set
open scoped ENNReal

namespace Erdos1165.VariableStoppedTracePartition

open LazyDecomposition VariableStoppedFiber HLOZPathEvents

noncomputable section

/-!
# A literal WalkPath partition from the variable stopped fibres

The product-space construction lives on increment paths.  This file lifts it
to `WalkPath` and adds one null junk piece for functions which are not planar
simple-walk trajectories.  Consequently the union statements below are
literal set equalities on all `WalkPath`, as required by
`TraceUpperProductScreening`, not merely almost-everywhere identities.
-/

/-! ## A measurable inverse on the support of simple random walk -/

/-- Decode a lattice vector which is known to be one of the four allowed
increments.  Its value off that four-point range is irrelevant. -/
def directionOfVector : Point → Direction :=
  Function.invFun directionVector

theorem directionOfVector_directionVector (d : Direction) :
    directionOfVector (directionVector d) = d := by
  exact Function.leftInverse_invFun directionVector_injective d

theorem measurable_directionOfVector : Measurable directionOfVector :=
  measurable_of_countable _

/-- Decode successive increments of an arbitrary lattice-valued function. -/
def stepsOfWalk (s : WalkPath) : StepPath :=
  fun n ↦ directionOfVector (s (n + 1) - s n)

theorem measurable_stepsOfWalk : Measurable stepsOfWalk := by
  apply measurable_pi_lambda
  intro n
  exact measurable_directionOfVector.comp (by fun_prop)

@[simp] theorem stepsOfWalk_trajectory (omega : StepPath) :
    stepsOfWalk (trajectory omega) = omega := by
  funext n
  rw [stepsOfWalk, trajectory_increment]
  exact directionOfVector_directionVector (omega n)

/-- The measurable support on which decoding and re-encoding is exact. -/
def validStepWalk : Set WalkPath :=
  {s | trajectory (stepsOfWalk s) = s}

theorem measurableSet_validStepWalk : MeasurableSet validStepWalk := by
  exact measurableSet_eq_fun
    (measurable_trajectory.comp measurable_stepsOfWalk) measurable_id

@[simp] theorem trajectory_mem_validStepWalk (omega : StepPath) :
    trajectory omega ∈ validStepWalk := by
  simp [validStepWalk]

/-- Lift an increment event to the exact trajectory support. -/
def walkLift (A : Set StepPath) : Set WalkPath :=
  validStepWalk ∩ stepsOfWalk ⁻¹' A

theorem measurableSet_walkLift {A : Set StepPath} (hA : MeasurableSet A) :
    MeasurableSet (walkLift A) :=
  measurableSet_validStepWalk.inter (hA.preimage measurable_stepsOfWalk)

theorem trajectory_preimage_walkLift (A : Set StepPath) :
    trajectory ⁻¹' walkLift A = A := by
  ext omega
  simp [walkLift]

/-- The lift preserves the actual probability, not only its null class. -/
theorem simpleRandomWalk_walkLift {A : Set StepPath} (hA : MeasurableSet A) :
    simpleRandomWalk (walkLift A) = fairSteps A := by
  rw [simpleRandomWalk, Measure.map_apply measurable_trajectory
    (measurableSet_walkLift hA), trajectory_preimage_walkLift]

theorem walkLift_inter (A B : Set StepPath) :
    walkLift A ∩ walkLift B = walkLift (A ∩ B) := by
  ext s
  simp only [walkLift, Set.mem_inter_iff, Set.mem_preimage]
  tauto

/-- Restricted real measures are transported exactly through the lift. -/
theorem restrictedReal_walkLift {A B : Set StepPath}
    (hA : MeasurableSet A) (hB : MeasurableSet B) :
    (simpleRandomWalk.restrict (walkLift A)).real (walkLift B) =
      (fairSteps.restrict A).real B := by
  have hLA := measurableSet_walkLift hA
  have hLB := measurableSet_walkLift hB
  change (simpleRandomWalk.restrict (walkLift A) (walkLift B)).toReal =
    (fairSteps.restrict A B).toReal
  congr 1
  rw [Measure.restrict_apply hLB, Measure.restrict_apply hB]
  rw [walkLift_inter, simpleRandomWalk_walkLift (hB.inter hA)]

/-! ## A literal countable partition of the reaching stage -/

/-- The entire rank-`k` threshold-reaching stage on path space. -/
def thresholdReachStage (m k : ℕ) : Set WalkPath :=
  {s | ReachesThreshold s m k}

theorem thresholdReachStage_eq_iUnion_creation (m k : ℕ) :
    thresholdReachStage m k = ⋃ n, thresholdCreationSet m k n := by
  classical
  ext s
  simp only [thresholdReachStage, Set.mem_ofPred_eq, Set.mem_iUnion,
    thresholdCreationSet, Set.mem_ofPred_eq]
  constructor
  · intro hreach
    exact ⟨Nat.find hreach, thresholdCreation_natFind hreach⟩
  · rintro ⟨n, hn⟩
    exact ⟨n, hn.1⟩

theorem measurableSet_thresholdReachStage (m k : ℕ) :
    MeasurableSet (thresholdReachStage m k) := by
  rw [thresholdReachStage_eq_iUnion_creation]
  exact MeasurableSet.iUnion fun n ↦ measurableSet_thresholdCreationSet m k n

/-- The genuine first creation time, with an irrelevant zero value off the
reaching stage. -/
def creationTimeNat (m k : ℕ) (s : WalkPath) : ℕ := by
  classical
  exact if h : ReachesThreshold s m k then Nat.find h else 0

theorem creationTimeNat_eq_of_creation {m k n : ℕ} {s : WalkPath}
    (h : ThresholdCreation s m k n) : creationTimeNat m k s = n := by
  let hreach : ReachesThreshold s m k := ⟨n, h.1⟩
  have hfind : Nat.find hreach = n :=
    HLOZSpatialAdapter.thresholdCreation_time_unique
      (thresholdCreation_natFind hreach) h
  simp [creationTimeNat, hreach, hfind]

theorem creationTimeNat_eq_zero_of_not_reaches {m k : ℕ} {s : WalkPath}
    (h : ¬ReachesThreshold s m k) : creationTimeNat m k s = 0 := by
  simp [creationTimeNat, h]

/-- A function to a countable singleton-measurable space is measurable once
all of its fibres are measurable. -/
theorem measurable_of_measurable_fibers
    {alpha beta : Type*} [MeasurableSpace alpha] [MeasurableSpace beta]
    [Countable beta] [MeasurableSingletonClass beta]
    (f : alpha → beta) (hf : ∀ b, MeasurableSet {x | f x = b}) :
    Measurable f := by
  intro U _
  have heq : f ⁻¹' U = ⋃ b : U, {x | f x = b.1} := by
    ext x
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_setOf_eq]
    constructor
    · intro hx
      exact ⟨⟨f x, hx⟩, rfl⟩
    · rintro ⟨b, hb⟩
      exact hb.symm ▸ b.2
  rw [heq]
  exact MeasurableSet.iUnion fun b ↦ hf b.1

theorem measurable_creationTimeNat (m k : ℕ) :
    Measurable (creationTimeNat m k) := by
  apply measurable_of_measurable_fibers
  intro n
  by_cases hn : n = 0
  · subst n
    have heq : {s | creationTimeNat m k s = 0} =
        (thresholdReachStage m k)ᶜ ∪ thresholdCreationSet m k 0 := by
      ext s
      simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_compl_iff,
        thresholdReachStage, Set.mem_ofPred_eq, thresholdCreationSet]
      constructor
      · intro hzero
        by_cases hreach : ReachesThreshold s m k
        · right
          have hcreation := thresholdCreation_natFind hreach
          have hfind : Nat.find hreach = 0 := by
            simpa [creationTimeNat, hreach] using hzero
          simpa [hfind] using hcreation
        · exact Or.inl hreach
      · rintro (hnot | hcreation)
        · exact creationTimeNat_eq_zero_of_not_reaches hnot
        · exact creationTimeNat_eq_of_creation hcreation
    rw [heq]
    exact (measurableSet_thresholdReachStage m k).compl.union
      (measurableSet_thresholdCreationSet m k 0)
  · have heq : {s | creationTimeNat m k s = n} =
        thresholdCreationSet m k n := by
      ext s
      simp only [Set.mem_setOf_eq, thresholdCreationSet, Set.mem_ofPred_eq]
      constructor
      · intro htime
        by_cases hreach : ReachesThreshold s m k
        · have hcreation := thresholdCreation_natFind hreach
          have hfind : Nat.find hreach = n := by
            simpa [creationTimeNat, hreach] using htime
          simpa [hfind] using hcreation
        · have : creationTimeNat m k s = 0 :=
            creationTimeNat_eq_zero_of_not_reaches hreach
          exact (hn (htime.symm.trans this)).elim
      · exact creationTimeNat_eq_of_creation
    rw [heq]
    exact measurableSet_thresholdCreationSet m k n

/-- Evaluate a measurable countable family at a measurable natural-valued
index. -/
theorem measurable_natIndexed
    {alpha beta : Type*} [MeasurableSpace alpha] [MeasurableSpace beta]
    (index : alpha → ℕ) (hindex : Measurable index)
    (f : ℕ → alpha → beta) (hf : ∀ n, Measurable (f n)) :
    Measurable fun x ↦ f (index x) x := by
  intro U hU
  have heq : (fun x ↦ f (index x) x) ⁻¹' U =
      ⋃ n, {x | index x = n} ∩ f n ⁻¹' U := by
    ext x
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_inter_iff,
      Set.mem_setOf_eq]
    constructor
    · intro hx
      exact ⟨index x, rfl, hx⟩
    · rintro ⟨n, hn, hx⟩
      simpa [hn] using hx
  rw [heq]
  exact MeasurableSet.iUnion fun n ↦
    (measurableSet_eq_fun hindex measurable_const).inter (hf n hU)

/-! ## Favorite locations and bases in the trace index -/

/-- The favorite data which must be held fixed before applying the spatial
product law: exact favorite locations, their oriented domino bases, the
oriented external-path start, and the terminal creation location.  The start
is `0` in the even decomposition and `s 1` in the shifted decomposition.
Recording it is essential: the retained direction word alone does not locate
the shifted external trace in space. -/
abbrev CreationFavoriteData :=
  (Finset Point × Finset Point) × (Point × Point)

/-- Spatial start of the oriented external trace. -/
def orientedCreationStart (o : Orientation) (s : WalkPath) : Point :=
  match o with
  | .even => (0, 0)
  | .shifted => s 1

theorem measurable_orientedCreationStart (o : Orientation) :
    Measurable (orientedCreationStart o) := by
  cases o with
  | even => exact measurable_const
  | shifted => exact measurable_pi_apply 1

def favoriteBasesAt (o : Orientation) (n : ℕ) (s : WalkPath) : Finset Point :=
  (favoriteSites s n).image (PreStoppingSpatialLaw.dominoBase o)

theorem measurable_favoriteBasesAt (o : Orientation) (n : ℕ) :
    Measurable (favoriteBasesAt o n) := by
  exact (measurable_of_countable
    (fun D : Finset Point ↦ D.image (PreStoppingSpatialLaw.dominoBase o))).comp
      (measurable_favoriteSites n)

def fixedCreationFavoriteData (o : Orientation) (n : ℕ)
    (s : WalkPath) : CreationFavoriteData :=
  ((favoriteSites s n, favoriteBasesAt o n s),
    (orientedCreationStart o s, s n))

theorem measurable_fixedCreationFavoriteData (o : Orientation) (n : ℕ) :
    Measurable (fixedCreationFavoriteData o n) := by
  exact ((measurable_favoriteSites n).prodMk
    (measurable_favoriteBasesAt o n)).prodMk
      ((measurable_orientedCreationStart o).prodMk (measurable_pi_apply n))

/-- Favorite/terminal data at the genuine variable threshold-creation time. -/
def creationFavoriteData (o : Orientation) (m k : ℕ)
    (s : WalkPath) : CreationFavoriteData :=
  fixedCreationFavoriteData o (creationTimeNat m k s) s

theorem measurable_creationFavoriteData (o : Orientation) (m k : ℕ) :
    Measurable (creationFavoriteData o m k) := by
  exact measurable_natIndexed (creationTimeNat m k)
    (measurable_creationTimeNat m k) (fixedCreationFavoriteData o)
    (measurable_fixedCreationFavoriteData o)

/-- The index has one null junk piece and otherwise records exactly one
external retained word and boundary tail. -/
abbrev WalkExternalCode (o : Orientation) := Option (ExternalWordCode o)

/-- A literal path-space partition.  `none` is the part of the reaching
stage outside the trajectory support; a `some code` piece is the lift of the
sound variable-time fibre. -/
def walkCreationPiece {o : Orientation} (m k : ℕ) :
    WalkExternalCode o → Set WalkPath
  | none => thresholdReachStage m k \ validStepWalk
  | some code => walkLift (variableCreationFiber m k code)

theorem measurableSet_walkCreationPiece {o : Orientation}
    (m k : ℕ) (z : WalkExternalCode o) :
    MeasurableSet (walkCreationPiece m k z) := by
  cases z with
  | none =>
      exact (measurableSet_thresholdReachStage m k).diff
        measurableSet_validStepWalk
  | some code =>
      exact measurableSet_walkLift
        (measurableSet_variableCreationFiber m k code)

theorem disjoint_walkCreationPiece_of_ne {o : Orientation}
    (m k : ℕ) {z w : WalkExternalCode o} (hzw : z ≠ w) :
    Disjoint (walkCreationPiece m k z) (walkCreationPiece m k w) := by
  classical
  cases z with
  | none =>
      cases w with
      | none => exact (hzw rfl).elim
      | some code =>
          rw [Set.disjoint_left]
          intro s hs ht
          exact hs.2 ht.1
  | some code =>
      cases w with
      | none =>
          rw [Set.disjoint_left]
          intro s hs ht
          exact ht.2 hs.1
      | some code' =>
          have hcode : code ≠ code' := by
            intro h
            exact hzw (congrArg some h)
          rw [Set.disjoint_left]
          intro s hs ht
          exact Set.disjoint_left.1
            (disjoint_variableCreationFiber_of_ne m k hcode)
            hs.2 ht.2

theorem iUnion_walkCreationPiece {o : Orientation} (m k : ℕ) :
    (⋃ z : WalkExternalCode o, walkCreationPiece m k z) =
      thresholdReachStage m k := by
  classical
  ext s
  simp only [Set.mem_iUnion]
  constructor
  · rintro ⟨z, hz⟩
    cases z with
    | none => exact hz.1
    | some code =>
        have hreachSteps : ReachesThreshold
            (trajectory (stepsOfWalk s)) m k := by
          change stepsOfWalk s ∈
            {omega | ReachesThreshold (trajectory omega) m k}
          rw [← iUnion_variableCreationFiber (o := o) m k]
          exact Set.mem_iUnion.mpr ⟨code, hz.2⟩
        change ReachesThreshold s m k
        rw [← hz.1]
        exact hreachSteps
  · intro hs
    by_cases hvalid : s ∈ validStepWalk
    · have hreachSteps : ReachesThreshold
          (trajectory (stepsOfWalk s)) m k := by
        rw [hvalid]
        exact hs
      have hunion : stepsOfWalk s ∈ ⋃ code : ExternalWordCode o,
          variableCreationFiber m k code := by
        rw [iUnion_variableCreationFiber]
        exact hreachSteps
      rcases Set.mem_iUnion.mp hunion with ⟨code, hcode⟩
      exact ⟨some code, hvalid, hcode⟩
    · exact ⟨none, hs, hvalid⟩

/-- The junk piece is exactly null under simple random walk. -/
theorem simpleRandomWalk_walkCreationPiece_none {o : Orientation}
    (m k : ℕ) :
    simpleRandomWalk (walkCreationPiece (o := o) m k none) = 0 := by
  have hvalid : simpleRandomWalk validStepWalk = 1 := by
    have huniv : walkLift (Set.univ : Set StepPath) = validStepWalk := by
      ext s
      simp [walkLift]
    rw [← huniv, simpleRandomWalk_walkLift MeasurableSet.univ]
    simp
  have hcompl : simpleRandomWalk validStepWalkᶜ = 0 := by
    rw [measure_compl measurableSet_validStepWalk
      (measure_ne_top simpleRandomWalk validStepWalk), hvalid]
    simp
  exact measure_mono_null (by
    intro s hs
    exact hs.2) hcompl

/-! ## The favorite-refined trace partition -/

/-- A sound fine index: external retained word and boundary tail, together
with the exact favorite locations, favorite domino bases, oriented trace
start, and terminal creation location.  There is deliberately no physical
time or insertion total in this index. -/
abbrev FavoriteTraceCode (o : Orientation) :=
  Option (ExternalWordCode o × CreationFavoriteData)

def stepFavoriteCreationFiber {o : Orientation} (m k : ℕ)
    (z : ExternalWordCode o × CreationFavoriteData) : Set StepPath :=
  variableCreationFiber m k z.1 ∩
    {omega | creationFavoriteData o m k (trajectory omega) = z.2}

theorem measurableSet_stepFavoriteCreationFiber {o : Orientation}
    (m k : ℕ) (z : ExternalWordCode o × CreationFavoriteData) :
    MeasurableSet (stepFavoriteCreationFiber m k z) := by
  exact (measurableSet_variableCreationFiber m k z.1).inter
    (measurableSet_eq_fun
      ((measurable_creationFavoriteData o m k).comp measurable_trajectory)
      measurable_const)

/-- The literal WalkPath fine piece.  Its `none` branch is the same null
junk piece as before. -/
def favoriteCreationPiece {o : Orientation} (m k : ℕ) :
    FavoriteTraceCode o → Set WalkPath
  | none => thresholdReachStage m k \ validStepWalk
  | some z => walkLift (stepFavoriteCreationFiber m k z)

theorem measurableSet_favoriteCreationPiece {o : Orientation}
    (m k : ℕ) (z : FavoriteTraceCode o) :
    MeasurableSet (favoriteCreationPiece m k z) := by
  cases z with
  | none =>
      exact (measurableSet_thresholdReachStage m k).diff
        measurableSet_validStepWalk
  | some z =>
      exact measurableSet_walkLift
        (measurableSet_stepFavoriteCreationFiber m k z)

theorem disjoint_favoriteCreationPiece_of_ne {o : Orientation}
    (m k : ℕ) {z w : FavoriteTraceCode o} (hzw : z ≠ w) :
    Disjoint (favoriteCreationPiece m k z)
      (favoriteCreationPiece m k w) := by
  classical
  cases z with
  | none =>
      cases w with
      | none => exact (hzw rfl).elim
      | some w =>
          rw [Set.disjoint_left]
          intro s hs ht
          exact hs.2 ht.1
  | some z =>
      cases w with
      | none =>
          rw [Set.disjoint_left]
          intro s hs ht
          exact ht.2 hs.1
      | some w =>
          have hpair : z ≠ w := by
            intro h
            exact hzw (congrArg some h)
          rw [Set.disjoint_left]
          intro s hs ht
          by_cases hcode : z.1 = w.1
          · have hdata : z.2 ≠ w.2 := by
              intro hd
              exact hpair (Prod.ext hcode hd)
            exact hdata (hs.2.2.symm.trans ht.2.2)
          · exact Set.disjoint_left.1
              (disjoint_variableCreationFiber_of_ne m k hcode)
              hs.2.1 ht.2.1

/-- The favorite-refined fine pieces still cover the whole reaching stage. -/
theorem iUnion_favoriteCreationPiece {o : Orientation} (m k : ℕ) :
    (⋃ z : FavoriteTraceCode o, favoriteCreationPiece m k z) =
      thresholdReachStage m k := by
  classical
  ext s
  simp only [Set.mem_iUnion]
  constructor
  · rintro ⟨z, hz⟩
    cases z with
    | none => exact hz.1
    | some z =>
        have hreachSteps : ReachesThreshold
            (trajectory (stepsOfWalk s)) m k := by
          change stepsOfWalk s ∈
            {omega | ReachesThreshold (trajectory omega) m k}
          rw [← iUnion_variableCreationFiber (o := o) m k]
          exact Set.mem_iUnion.mpr ⟨z.1, hz.2.1⟩
        change ReachesThreshold s m k
        rw [← hz.1]
        exact hreachSteps
  · intro hs
    by_cases hvalid : s ∈ validStepWalk
    · have hreachSteps : ReachesThreshold
          (trajectory (stepsOfWalk s)) m k := by
        rw [hvalid]
        exact hs
      have hunion : stepsOfWalk s ∈ ⋃ code : ExternalWordCode o,
          variableCreationFiber m k code := by
        rw [iUnion_variableCreationFiber]
        exact hreachSteps
      rcases Set.mem_iUnion.mp hunion with ⟨code, hcode⟩
      let data := creationFavoriteData o m k (trajectory (stepsOfWalk s))
      refine ⟨some (code, data), hvalid, hcode, ?_⟩
      rfl
    · exact ⟨none, hs, hvalid⟩

theorem simpleRandomWalk_favoriteCreationPiece_none {o : Orientation}
    (m k : ℕ) :
    simpleRandomWalk (favoriteCreationPiece (o := o) m k none) = 0 :=
  simpleRandomWalk_walkCreationPiece_none (o := o) m k

/-- At rank one this is literally the stage used by
`FirstTraceProductScreening`. -/
theorem thresholdReachStage_one_eq_firstCreationStage (m : ℕ) :
    thresholdReachStage m 1 =
      HLOZStoppedProductRefinement.firstCreationStage m := by
  rw [thresholdReachStage_eq_iUnion_creation]
  rfl

theorem iUnion_favoriteCreationPiece_eq_firstCreationStage
    {o : Orientation} (m : ℕ) :
    (⋃ z : FavoriteTraceCode o, favoriteCreationPiece m 1 z) =
      HLOZStoppedProductRefinement.firstCreationStage m := by
  rw [iUnion_favoriteCreationPiece,
    thresholdReachStage_one_eq_firstCreationStage]

end

end Erdos1165.VariableStoppedTracePartition
