/- leanprover/lean4:v4.33.0 -/
import ErdosProblems.Erdos547b.Lemma58GlobalPlannedOwnerSuccessor
import ErdosProblems.Erdos547b.Lemma58FixedCombinedResidual
import ErdosProblems.Erdos547b.Lemma58SelectedOrientationReindex

/-!
# Global fixed orientations as synchronized side plans

For Parts 1/2 the balancing calculation is performed once on each complete
matching-edge fiber.  This file pulls that fixed edge orientation back to
every owner batch and records its literal singleton branch/coordinate plan.
-/

open scoped SimpleGraph
noncomputable section

namespace Erdos547b.ZhaoLemma58GlobalFixedOrientationPlan

open Finset Fintype SimpleGraph
open Erdos547b.RegularPair
open Erdos547b.ZhaoLemma59Part2Full
open Erdos547b.ZhaoClaim616SourceBridge
open Erdos547b.ZhaoClaim616SourceBridge.OrderedBranchForest
open Erdos547b.ZhaoLemma58MatchingAssembly
open Erdos547b.ZhaoLemma58DynamicBatchAppend
open Erdos547b.ZhaoLemma58ChosenOwnerBatches
open Erdos547b.ZhaoLemma58ChosenMatchingAssembly
open Erdos547b.ZhaoLemma58GroupedSmallForest
open Erdos547b.ZhaoLemma58OwnerLocalStep
open Erdos547b.ZhaoLemma58OwnerForbidden
open Erdos547b.ZhaoLemma58CombinedResidual
open Erdos547b.ZhaoLemma58FixedCombinedResidual
open Erdos547b.ZhaoLemma58SelectedOrientationReindex
open Erdos547b.ZhaoLemma58PlannedOwnerLocalStep
open Erdos547b.ZhaoLemma58GlobalOwnerOnlineState
open Erdos547b.ZhaoLemma58GlobalPlannedOnlineState
open Erdos547b.ZhaoLemma58GlobalPlannedOwnerSuccessor

/-- Actual side of one global coordinate under fixed edge-fiber
orientations. -/
def globalFixedCoordinateSide
    {r b k : ℕ}
    (F : OrderedBranchForest r b) (_assign : Fin b → Fin k)
    (orient : Fin b → Fin 2 ≃ Fin 2)
    (z : Σ j, Fin (F.branches.size j)) : Fin 2 :=
  orient z.1
    ((F.branches.isTree z.1).coloringTwoOfVert
      (F.branches.root z.1) z.2)

/-- Singleton branch-root plan induced by fixed edge orientations. -/
def globalFixedRootAllowed
    {r b k : ℕ}
    (F : OrderedBranchForest r b) (assign : Fin b → Fin k)
    (orient : Fin b → Fin 2 ≃ Fin 2)
    (j : Fin b) : Finset (Fin 2) :=
  {globalFixedCoordinateSide F assign orient ⟨j, F.branches.root j⟩}

/-- Singleton coordinate plan induced by fixed edge orientations. -/
def globalFixedCoordinateAllowed
    {r b k : ℕ}
    (F : OrderedBranchForest r b) (assign : Fin b → Fin k)
    (orient : Fin b → Fin 2 ≃ Fin 2)
    (z : Σ j, Fin (F.branches.size j)) : Finset (Fin 2) :=
  {globalFixedCoordinateSide F assign orient z}

/-- Pull the global fixed orientation back to the canonical enumeration of
one matching-edge fiber. -/
def globalFixedFiberOrientation
    {r b k : ℕ}
    (_F : OrderedBranchForest r b) (assign : Fin b → Fin k)
    (orient : Fin b → Fin 2 ≃ Fin 2) (e : Fin k)
    (i : Fin (matchingFiber assign e).card) : Fin 2 ≃ Fin 2 :=
  orient (OrderedBranchForest.selectedEquiv (matchingFiber assign e) i)

/-- Restricting an orientation assembled from matching fibers recovers the
literal local orientation on that fiber. -/
theorem globalFixedFiberOrientation_assembledOrient
    {r b k : ℕ}
    (F : OrderedBranchForest r b) (assign : Fin b → Fin k)
    (localOrient : ∀ e,
      Fin (matchingFiber assign e).card → Fin 2 ≃ Fin 2)
    (e : Fin k) :
    globalFixedFiberOrientation F assign
        (assembledOrient assign (fun f ↦
          extendSelectedOrient (matchingFiber assign f) (localOrient f))) e =
      localOrient e := by
  funext i
  simp only [globalFixedFiberOrientation, assembledOrient]
  have hassign : assign
      (OrderedBranchForest.selectedEquiv (matchingFiber assign e) i) = e :=
    (mem_matchingFiber assign e _).mp
      (OrderedBranchForest.selectedEquiv (matchingFiber assign e) i).property
  rw [hassign]
  exact extendSelectedOrient_selectedEquiv (matchingFiber assign e)
    (localOrient e) i

/-- Consequently the complete-fiber side load in the synchronized recursion
is exactly the side load certified by the local matching-fiber calculation. -/
theorem sideLoad_globalFixedFiberOrientation_assembledOrient
    {r b k : ℕ}
    (F : OrderedBranchForest r b) (assign : Fin b → Fin k)
    (localOrient : ∀ e,
      Fin (matchingFiber assign e).card → Fin 2 ≃ Fin 2)
    (e : Fin k) (c : Fin 2) :
    sideLoad (onlineFiberForest F assign e)
        (globalFixedFiberOrientation F assign
          (assembledOrient assign (fun f ↦
            extendSelectedOrient (matchingFiber assign f) (localOrient f))) e) c =
      sideLoad (onlineFiberForest F assign e) (localOrient e) c := by
  rw [globalFixedFiberOrientation_assembledOrient F assign localOrient e]

/-- Exact fixed-orientation load already realized on one endpoint before
owner `n` is processed. -/
def globalFixedPrefixLoad
    {r b k : ℕ}
    (F : OrderedBranchForest r b) (assign : Fin b → Fin k)
    (orient : Fin b → Fin 2 ≃ Fin 2) (e : Fin k) (n : ℕ)
    (c : Fin 2) : ℕ :=
  ∑ i ∈ ownerPrefix Finset.univ (onlineFiberOwner F assign e) n,
    orientedClassSize (onlineFiberForest F assign e)
      (globalFixedFiberOrientation F assign orient e) i c

private theorem plannedFiberCoordinateSide_eq_fixed
    {r b k : ℕ} {B : Type*} [Fintype B] [DecidableEq B]
    (F : OrderedBranchForest r b) (G : SimpleGraph B)
    (assign : Fin b → Fin k)
    (endpoint : Fin k → Fin 2 → Finset B)
    (rootCandidate : Fin r → Finset B)
    (orient : Fin b → Fin 2 ≃ Fin 2) (n : ℕ)
    (S : PlannedOnlineOwnerPrefixState F G assign endpoint rootCandidate
      (globalFixedCoordinateAllowed F assign orient) n)
    (e : Fin k) (j : Fin b) (hj : assign j = e)
    (howner : (F.owner j).val < n) (a : Fin (F.branches.size j)) :
    ((S.state.edgeState e).orient (fiberIndex assign e j hj))
        ((onlineFiberForest F assign e).isTree (fiberIndex assign e j hj)
          |>.coloringTwoOfVert
            ((onlineFiberForest F assign e).root (fiberIndex assign e j hj))
            (fiberVertex F assign e j hj a)) =
      orient j ((F.branches.isTree j).coloringTwoOfVert
        (F.branches.root j) a) := by
  subst e
  have hmem := S.coordinate_side_mem j howner a
  have hside := Finset.mem_singleton.mp hmem
  convert hside using 1
  all_goals
    simp only [globalFixedCoordinateSide, fiberIndex, fiberVertex,
      assignmentIndex, assignmentVertex]
    try rfl

theorem fiberVertex_coloring
    {r b k : ℕ}
    (F : OrderedBranchForest r b) (assign : Fin b → Fin k)
    (e : Fin k) (j : Fin b) (hj : assign j = e)
    (a : Fin (F.branches.size j)) :
    ((onlineFiberForest F assign e).isTree (fiberIndex assign e j hj)
      |>.coloringTwoOfVert
        ((onlineFiberForest F assign e).root (fiberIndex assign e j hj))
        (fiberVertex F assign e j hj a)) =
      (F.branches.isTree j).coloringTwoOfVert (F.branches.root j) a := by
  subst e
  convert assignmentVertex_coloring F assign j a using 1
  all_goals
    simp only [fiberIndex, fiberVertex, assignmentIndex, assignmentVertex]
    try rfl

theorem onlineFiber_coloring_eq_of_index_eq
    {r b k : ℕ}
    (F : OrderedBranchForest r b) (assign : Fin b → Fin k) (e : Fin k)
    (i i' : Fin (matchingFiber assign e).card) (hii : i = i')
    (a : Fin ((onlineFiberForest F assign e).size i))
    (a' : Fin ((onlineFiberForest F assign e).size i'))
    (haa : a.val = a'.val) :
    ((onlineFiberForest F assign e).isTree i |>.coloringTwoOfVert
        ((onlineFiberForest F assign e).root i) a) =
      ((onlineFiberForest F assign e).isTree i' |>.coloringTwoOfVert
        ((onlineFiberForest F assign e).root i') a') := by
  subst i'
  have ha : a = a' := Fin.ext haa
  subst a'
  rfl

/-- A synchronized prefix has the expected fixed-side load whenever its
literal stored orientations agree with the prescribed complete-fiber
orientation on all already selected coordinates. -/
theorem card_edgeState_used_le_fixedPrefixLoad_of_orient_eq
    {r b k : ℕ} {B : Type*} [Fintype B] [DecidableEq B]
    (F : OrderedBranchForest r b) (G : SimpleGraph B)
    (assign : Fin b → Fin k)
    (endpoint : Fin k → Fin 2 → Finset B)
    (rootCandidate : Fin r → Finset B)
    (orient : Fin b → Fin 2 ≃ Fin 2) (n : ℕ)
    (S : OnlineOwnerPrefixState F G assign endpoint rootCandidate n)
    (e : Fin k)
    (hside : ∀ i
      (_hi : i ∈ ownerPrefix Finset.univ (onlineFiberOwner F assign e) n) a,
      (S.edgeState e).orient i
          ((onlineFiberForest F assign e).isTree i |>.coloringTwoOfVert
            ((onlineFiberForest F assign e).root i) a) =
        (globalFixedFiberOrientation F assign orient e i)
          ((onlineFiberForest F assign e).isTree i |>.coloringTwoOfVert
            ((onlineFiberForest F assign e).root i) a))
    (c : Fin 2) :
    #((S.edgeState e).used c) ≤ globalFixedPrefixLoad F assign orient e n c := by
  exact card_chosenPartial_used_le_orientedLoad (S.edgeState e)
    (globalFixedFiberOrientation F assign orient e) hside c

/-- A synchronized prefix respecting the singleton fixed-coordinate plan
has used at most the literal fixed oriented load of its processed fiber. -/
theorem PlannedOnlineOwnerPrefixState.card_edgeState_used_le_fixedPrefixLoad
    {r b k : ℕ} {B : Type*} [Fintype B] [DecidableEq B]
    (F : OrderedBranchForest r b) (G : SimpleGraph B)
    (assign : Fin b → Fin k)
    (endpoint : Fin k → Fin 2 → Finset B)
    (rootCandidate : Fin r → Finset B)
    (orient : Fin b → Fin 2 ≃ Fin 2) (n : ℕ)
    (S : PlannedOnlineOwnerPrefixState F G assign endpoint rootCandidate
      (globalFixedCoordinateAllowed F assign orient) n)
    (e : Fin k) (c : Fin 2) :
    #((S.state.edgeState e).used c) ≤
      globalFixedPrefixLoad F assign orient e n c := by
  classical
  apply card_chosenPartial_used_le_orientedLoad
  intro i hi a
  let fiberEquiv :=
    OrderedBranchForest.selectedEquiv (matchingFiber assign e)
  obtain ⟨sj, hisj⟩ := fiberEquiv.symm.surjective i
  subst i
  let j : Fin b := sj.1
  have hjassign : assign j = e := by
    exact (mem_matchingFiber assign e j).mp
      sj.2
  have howner : (F.owner j).val < n := by
    simpa only [onlineFiberOwner, fiberEquiv, Equiv.apply_symm_apply, j]
      using (Finset.mem_filter.mp hi).2
  let aGlobal : Fin (F.branches.size j) :=
    ⟨a.val, by
      simpa only [onlineFiberForest, OrderedBranchForest.restrict_size,
        fiberEquiv, Equiv.apply_symm_apply, j] using a.isLt⟩
  have hindex : fiberIndex assign e j hjassign = fiberEquiv.symm sj := by
    apply (OrderedBranchForest.selectedEquiv (matchingFiber assign e)).injective
    apply Subtype.ext
    simp only [fiberIndex, Equiv.apply_symm_apply, fiberEquiv, j]
  have hcolor := fiberVertex_coloring F assign e j hjassign aGlobal
  have hside := plannedFiberCoordinateSide_eq_fixed F G assign endpoint
    rootCandidate orient n S e j hjassign howner aGlobal
  have htargetColor :
      ((onlineFiberForest F assign e).isTree (fiberEquiv.symm sj)
        |>.coloringTwoOfVert
          ((onlineFiberForest F assign e).root (fiberEquiv.symm sj)) a) =
        ((onlineFiberForest F assign e).isTree
          (fiberIndex assign e j hjassign) |>.coloringTwoOfVert
            ((onlineFiberForest F assign e).root
              (fiberIndex assign e j hjassign))
            (fiberVertex F assign e j hjassign aGlobal)) := by
    apply onlineFiber_coloring_eq_of_index_eq F assign e
      (fiberEquiv.symm sj) (fiberIndex assign e j hjassign) hindex.symm
    rfl
  have hlocalColor := htargetColor.trans hcolor
  have horient := congrArg (S.state.edgeState e).orient hindex
  calc
    ((S.state.edgeState e).orient (fiberEquiv.symm sj))
        ((onlineFiberForest F assign e).isTree (fiberEquiv.symm sj)
          |>.coloringTwoOfVert
            ((onlineFiberForest F assign e).root (fiberEquiv.symm sj)) a) =
        ((S.state.edgeState e).orient
          (fiberIndex assign e j hjassign))
          ((onlineFiberForest F assign e).isTree (fiberEquiv.symm sj)
            |>.coloringTwoOfVert
              ((onlineFiberForest F assign e).root (fiberEquiv.symm sj)) a) := by
          rw [horient]
    _ = ((S.state.edgeState e).orient
          (fiberIndex assign e j hjassign))
          ((onlineFiberForest F assign e).isTree
            (fiberIndex assign e j hjassign) |>.coloringTwoOfVert
              ((onlineFiberForest F assign e).root
                (fiberIndex assign e j hjassign))
              (fiberVertex F assign e j hjassign aGlobal)) := by
          exact congrArg _ htargetColor
    _ = orient j ((F.branches.isTree j).coloringTwoOfVert
          (F.branches.root j) aGlobal) := hside
    _ = (globalFixedFiberOrientation F assign orient e
          (fiberEquiv.symm sj))
          ((onlineFiberForest F assign e).isTree (fiberEquiv.symm sj)
            |>.coloringTwoOfVert
              ((onlineFiberForest F assign e).root (fiberEquiv.symm sj)) a) := by
          rw [hlocalColor]
          simp only [globalFixedFiberOrientation, fiberEquiv,
            Equiv.apply_symm_apply, j]

/-- Reparenting the synchronized prefix at the current owner preserves the
same exact fixed-prefix load bound. -/
theorem PlannedOnlineOwnerPrefixState.card_reparented_used_le_fixedPrefixLoad
    {r b k : ℕ} {B : Type*} [Fintype B] [DecidableEq B]
    (F : OrderedBranchForest r b) (G : SimpleGraph B)
    (assign : Fin b → Fin k)
    (endpoint : Fin k → Fin 2 → Finset B)
    (rootCandidate : Fin r → Finset B)
    (orient : Fin b → Fin 2 ≃ Fin 2) (n : ℕ) (hn : n < r)
    (S : PlannedOnlineOwnerPrefixState F G assign endpoint rootCandidate
      (globalFixedCoordinateAllowed F assign orient) n)
    (z : B) (e : Fin k) (c : Fin 2) :
    #((reparentedEdgeState F G assign endpoint rootCandidate n hn S.state z e).used
        c) ≤ globalFixedPrefixLoad F assign orient e n c := by
  change #((S.state.edgeState e).used c) ≤ _
  exact card_edgeState_used_le_fixedPrefixLoad F G assign endpoint
    rootCandidate orient n S e c

/-- Restriction of a fixed edge orientation to one owner batch. -/
def onlineOwnerBatchFixedOrientation
    {r b k : ℕ}
    (F : OrderedBranchForest r b) (assign : Fin b → Fin k)
    (orient : Fin b → Fin 2 ≃ Fin 2)
    (e : Fin k) (n : ℕ) (hn : n < r)
    (i : Fin (onlineOwnerBatch F assign e n hn).card) : Fin 2 ≃ Fin 2 :=
  orient (onlineOwnerBatchBranch F assign e n hn i)

/-- The restricted fixed orientation sends every owner-batch coordinate to
the singleton side prescribed for its literal global coordinate. -/
theorem onlineOwnerBatchFixedOrientation_coordinate_mem
    {r b k : ℕ}
    (F : OrderedBranchForest r b) (assign : Fin b → Fin k)
    (orient : Fin b → Fin 2 ≃ Fin 2)
    (e : Fin k) (n : ℕ) (hn : n < r)
    (i : Fin (onlineOwnerBatch F assign e n hn).card)
    (a : Fin ((onlineOwnerBatchForest F assign e n hn).size i)) :
    onlineOwnerBatchFixedOrientation F assign orient e n hn i
        ((onlineOwnerBatchForest F assign e n hn).isTree i
          |>.coloringTwoOfVert
            ((onlineOwnerBatchForest F assign e n hn).root i) a) ∈
      onlineOwnerBatchCoordinateAllowed F assign e n hn
        (globalFixedCoordinateAllowed F assign orient) ⟨i, a⟩ := by
  simp only [onlineOwnerBatchCoordinateAllowed,
    globalFixedCoordinateAllowed, Finset.mem_singleton,
    onlineOwnerBatchFixedOrientation, globalFixedCoordinateSide]
  rfl

/-- The restricted fixed orientation sends every owner-batch root to the
singleton branch-root side prescribed globally. -/
theorem onlineOwnerBatchFixedOrientation_root_mem
    {r b k : ℕ}
    (F : OrderedBranchForest r b) (assign : Fin b → Fin k)
    (orient : Fin b → Fin 2 ≃ Fin 2)
    (e : Fin k) (n : ℕ) (hn : n < r)
    (i : Fin (onlineOwnerBatch F assign e n hn).card) :
    branchRootSide (onlineOwnerBatchForest F assign e n hn)
        (onlineOwnerBatchFixedOrientation F assign orient e n hn) i ∈
      onlineOwnerBatchRootAllowed F assign e n hn
        (globalFixedRootAllowed F assign orient) i := by
  apply Finset.mem_singleton.mpr
  change (onlineOwnerBatchFixedOrientation F assign orient e n hn i) 0 =
    globalFixedCoordinateSide F assign orient
      ⟨onlineOwnerBatchBranch F assign e n hn i,
        F.branches.root (onlineOwnerBatchBranch F assign e n hn i)⟩
  rw [onlineOwnerBatchFixedOrientation, globalFixedCoordinateSide,
    coloringTwoOfVert_root]

/-- The side load of one owner batch is exactly the corresponding summand
of the fixed full-fiber orientation. -/
theorem sideLoad_onlineOwnerBatchFixedOrientation
    {r b k : ℕ}
    (F : OrderedBranchForest r b) (assign : Fin b → Fin k)
    (orient : Fin b → Fin 2 ≃ Fin 2)
    (e : Fin k) (n : ℕ) (hn : n < r) (c : Fin 2) :
    sideLoad (onlineOwnerBatchForest F assign e n hn)
        (onlineOwnerBatchFixedOrientation F assign orient e n hn) c =
      ∑ i ∈ onlineOwnerBatch F assign e n hn,
        orientedClassSize (onlineFiberForest F assign e)
          (globalFixedFiberOrientation F assign orient e) i c := by
  classical
  rw [sideLoad]
  calc
    ∑ i : Fin (onlineOwnerBatch F assign e n hn).card,
        orientedClassSize (onlineOwnerBatchForest F assign e n hn)
          (onlineOwnerBatchFixedOrientation F assign orient e n hn) i c =
      ∑ i : Fin (onlineOwnerBatch F assign e n hn).card,
        orientedClassSize (onlineFiberForest F assign e)
          (globalFixedFiberOrientation F assign orient e)
          (OrderedBranchForest.selectedEquiv
            (onlineOwnerBatch F assign e n hn) i) c := by
      apply Finset.sum_congr rfl
      intro i _
      unfold orientedClassSize
      congr 1
    _ = ∑ i ∈ onlineOwnerBatch F assign e n hn,
        orientedClassSize (onlineFiberForest F assign e)
          (globalFixedFiberOrientation F assign orient e) i c :=
      OrderedBranchForest.sum_selectedEquiv
        (onlineOwnerBatch F assign e n hn)
        (fun i ↦ orientedClassSize (onlineFiberForest F assign e)
          (globalFixedFiberOrientation F assign orient e) i c)

/-- Prefix occupancy plus the current owner batch never exceeds the final
fixed-oriented load of the complete matching-edge fiber. -/
theorem globalFixedPrefixLoad_add_batch_le_sideLoad
    {r b k : ℕ}
    (F : OrderedBranchForest r b) (assign : Fin b → Fin k)
    (orient : Fin b → Fin 2 ≃ Fin 2)
    (e : Fin k) (n : ℕ) (hn : n < r) (c : Fin 2) :
    globalFixedPrefixLoad F assign orient e n c +
        sideLoad (onlineOwnerBatchForest F assign e n hn)
          (onlineOwnerBatchFixedOrientation F assign orient e n hn) c ≤
      sideLoad (onlineFiberForest F assign e)
        (globalFixedFiberOrientation F assign orient e) c := by
  classical
  rw [globalFixedPrefixLoad,
    sideLoad_onlineOwnerBatchFixedOrientation F assign orient e n hn c,
    sideLoad]
  rw [← Finset.sum_union
    (ownerPrefix_disjoint_ownerBatch Finset.univ
      (onlineFiberOwner F assign e) n hn)]
  rw [ownerPrefix_succ]
  exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)

/-- Before any branch of the current owner batch, the old prefix together
with that branch's within-batch prefix is bounded by the final fiber load. -/
theorem globalFixedPrefixLoad_add_sideLoadBefore_le_sideLoad
    {r b k : ℕ}
    (F : OrderedBranchForest r b) (assign : Fin b → Fin k)
    (orient : Fin b → Fin 2 ≃ Fin 2)
    (e : Fin k) (n : ℕ) (hn : n < r)
    (i : Fin (onlineOwnerBatch F assign e n hn).card) (c : Fin 2) :
    globalFixedPrefixLoad F assign orient e n c +
        sideLoadBefore (onlineOwnerBatchForest F assign e n hn)
          (onlineOwnerBatchFixedOrientation F assign orient e n hn) i c ≤
      sideLoad (onlineFiberForest F assign e)
        (globalFixedFiberOrientation F assign orient e) c := by
  have hbatch := sideLoadBefore_le_sideLoad
    (onlineOwnerBatchForest F assign e n hn)
    (onlineOwnerBatchFixedOrientation F assign orient e n hn) i c
  have hfull := globalFixedPrefixLoad_add_batch_le_sideLoad F assign orient e n
    hn c
  omega

/-- Add the automatically verified singleton plan certificates to a fixed
orientation local step. -/
def plannedFixedOwnerLocalStepData
    {r b k : ℕ} {B : Type*} [Fintype B] [DecidableEq B]
    (F : OrderedBranchForest r b) (G : SimpleGraph B) [DecidableRel G.Adj]
    (assign : Fin b → Fin k)
    (orient : Fin b → Fin 2 ≃ Fin 2)
    (whole live : Fin 2 → Finset B) (rho density : ℝ)
    (e : Fin k) (n : ℕ) (hn : n < r)
    (externalParent : Fin (onlineOwnerBatch F assign e n hn).card → B)
    (D : FixedOrientationStepData
      (onlineOwnerBatchForest F assign e n hn) G externalParent
      (onlineOwnerBatchFixedOrientation F assign orient e n hn)
      whole live rho density) :
    PlannedOwnerLocalStepData (onlineOwnerBatchForest F assign e n hn) G
      externalParent whole live rho density
      (onlineOwnerBatchRootAllowed F assign e n hn
        (globalFixedRootAllowed F assign orient))
      (onlineOwnerBatchCoordinateAllowed F assign e n hn
        (globalFixedCoordinateAllowed F assign orient)) :=
  .fixed D
    (onlineOwnerBatchFixedOrientation_root_mem F assign orient e n hn)
    (onlineOwnerBatchFixedOrientation_coordinate_mem F assign orient e n hn)

/-- Scalar combined-deletion bounds for one owner batch directly produce
the plan-certified fixed continuation consumed by the global recursion. -/
noncomputable def plannedFixedOwnerLocalStepDataOfCombinedBounds
    {r b k : ℕ} {B : Type*} [Fintype B] [DecidableEq B]
    (F : OrderedBranchForest r b) (G : SimpleGraph B) [DecidableRel G.Adj]
    (assign : Fin b → Fin k)
    (orient : Fin b → Fin 2 ≃ Fin 2)
    (e : Fin k) (n : ℕ) (hn : n < r)
    (externalParent : Fin (onlineOwnerBatch F assign e n hn).card → B)
    (whole available used bad : Fin 2 → Finset B)
    (rho density : ℝ) (reserve : Fin 2 → ℕ)
    (havailable : ∀ c, available c ⊆ whole c)
    (husedSub : ∀ c, used c ⊆ available c)
    (hbadSub : ∀ c, bad c ⊆ available c)
    (hunif : G.IsUniform rho (whole 0) (whole 1))
    (hwholeDisjoint : Disjoint (whole 0) (whole 1))
    (hdensity : density ≤ G.edgeDensity (whole 0) (whole 1))
    (hfactor : 0 ≤ density - rho)
    (hreserve : ∀ c, rho * (#(whole c) : ℝ) ≤ reserve c)
    (lossBound : Fin 2 → ℕ)
    (hloss : ∀ c,
      #(combinedDeleted whole available used bad c) ≤ lossBound c)
    (htotal : ∀ c,
      lossBound c + sideLoad (onlineOwnerBatchForest F assign e n hn)
          (onlineOwnerBatchFixedOrientation F assign orient e n hn) c +
          reserve c ≤ #(whole c))
    (heligible : ∀ i,
      let c := branchRootSide (onlineOwnerBatchForest F assign e n hn)
        (onlineOwnerBatchFixedOrientation F assign orient e n hn) i
      lossBound c +
          (1 + reserve c +
            sideLoadBefore (onlineOwnerBatchForest F assign e n hn)
              (onlineOwnerBatchFixedOrientation F assign orient e n hn)
              i c) ≤
        #((whole c).filter (G.Adj (externalParent i))))
    (hcomponent : ∀ i c,
      ((onlineOwnerBatchForest F assign e n hn).size i : ℝ) +
          rho * (#(whole c) : ℝ) + 1 ≤
        (density - rho) *
          ((#(whole c) : ℝ) - lossBound c -
            sideLoad (onlineOwnerBatchForest F assign e n hn)
              (onlineOwnerBatchFixedOrientation F assign orient e n hn) c)) :
    PlannedOwnerLocalStepData (onlineOwnerBatchForest F assign e n hn) G
      externalParent whole
      (ownerCleanedLive (fun c ↦ available c \ used c) bad) rho density
      (onlineOwnerBatchRootAllowed F assign e n hn
        (globalFixedRootAllowed F assign orient))
      (onlineOwnerBatchCoordinateAllowed F assign e n hn
        (globalFixedCoordinateAllowed F assign orient)) :=
  plannedFixedOwnerLocalStepData F G assign orient whole
    (ownerCleanedLive (fun c ↦ available c \ used c) bad) rho density e n hn
    externalParent
    (fixedOrientationStepDataOfCombinedBounds
      (onlineOwnerBatchForest F assign e n hn) G externalParent
      (onlineOwnerBatchFixedOrientation F assign orient e n hn) whole available
      used bad rho density reserve havailable husedSub hbadSub hunif
      hwholeDisjoint hdensity hfactor hreserve lossBound hloss htotal
      heligible hcomponent)

end Erdos547b.ZhaoLemma58GlobalFixedOrientationPlan

#print axioms Erdos547b.ZhaoLemma58GlobalFixedOrientationPlan.globalFixedFiberOrientation_assembledOrient
#print axioms Erdos547b.ZhaoLemma58GlobalFixedOrientationPlan.sideLoad_globalFixedFiberOrientation_assembledOrient
#print axioms Erdos547b.ZhaoLemma58GlobalFixedOrientationPlan.globalFixedPrefixLoad_add_sideLoadBefore_le_sideLoad
#print axioms Erdos547b.ZhaoLemma58GlobalFixedOrientationPlan.card_edgeState_used_le_fixedPrefixLoad_of_orient_eq
