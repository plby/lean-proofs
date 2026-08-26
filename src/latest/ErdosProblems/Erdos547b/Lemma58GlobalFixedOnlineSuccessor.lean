/- leanprover/lean4:v4.33.0 -/
import ErdosProblems.Erdos547b.Lemma58GlobalFixedOrientationPlan

/-!
# Scalar fixed-orientation successors for the synchronized recursion

The record in this file contains only the per-edge scalar and regular-pair
facts remaining after permanent cleaning and the exact prefix image are
known.  Endpoint containment, prefix-used containment, and the literal live
set identity are derived by the constructor.
-/

open scoped SimpleGraph
noncomputable section

namespace Erdos547b.ZhaoLemma58GlobalFixedOnlineSuccessor

open Finset Fintype SimpleGraph
open Erdos547b.RegularPair
open Erdos547b.ZhaoLemma59Part2Full
open Erdos547b.ZhaoClaim616SourceBridge
open Erdos547b.ZhaoLemma58MatchingAssembly
open Erdos547b.ZhaoLemma58DynamicBatchAppend
open Erdos547b.ZhaoLemma58ChosenOwnerBatches
open Erdos547b.ZhaoLemma58GroupedSmallForest
open Erdos547b.ZhaoLemma58OwnerLocalStep
open Erdos547b.ZhaoLemma58OwnerForbidden
open Erdos547b.ZhaoLemma58GlobalOwnerOnlineState
open Erdos547b.ZhaoLemma58CombinedResidual
open Erdos547b.ZhaoLemma58FixedCombinedResidual
open Erdos547b.ZhaoLemma58GlobalPlannedOwnerSuccessor
open Erdos547b.ZhaoLemma58GlobalPlannedOnlineState
open Erdos547b.ZhaoLemma58GlobalFixedOrientationPlan

universe v

/-- Per-edge source and host inequalities for one fixed-orientation owner
batch in the exact current synchronized state. -/
structure FixedOnlineOwnerEdgeFacts
    {r b k : ℕ} {B : Type v} [Fintype B] [DecidableEq B]
    (F : OrderedBranchForest r b) (G : SimpleGraph B) [DecidableRel G.Adj]
    (assign : Fin b → Fin k)
    (orient : Fin b → Fin 2 ≃ Fin 2)
    (whole endpoint : Fin k → Fin 2 → Finset B)
    (rho density : Fin k → ℝ)
    (rootCandidate : Fin r → Finset B)
    (n : ℕ) (hn : n < r)
    (S : OnlineOwnerPrefixState F G assign endpoint rootCandidate n)
    (z : B) (e : Fin k) : Type (max 0 v) where
  reserve : Fin 2 → ℕ
  lossBound : Fin 2 → ℕ
  uniform : G.IsUniform (rho e) (whole e 0) (whole e 1)
  density_lower : density e ≤ G.edgeDensity (whole e 0) (whole e 1)
  factor_nonneg : 0 ≤ density e - rho e
  reserve_regular : ∀ c, rho e * (#(whole e c) : ℝ) ≤ reserve c
  loss : ∀ c,
    #(combinedDeleted (whole e) (endpoint e)
      (reparentedEdgeState F G assign endpoint rootCandidate n hn S z e).used
      (fun _ ↦ ∅) c) ≤ lossBound c
  total : ∀ c,
    lossBound c +
        sideLoad (onlineOwnerBatchForest F assign e n hn)
          (onlineOwnerBatchFixedOrientation F assign orient e n hn) c +
        reserve c ≤ #(whole e c)
  eligible : ∀ i,
    let c := branchRootSide (onlineOwnerBatchForest F assign e n hn)
      (onlineOwnerBatchFixedOrientation F assign orient e n hn) i
    lossBound c +
        (1 + reserve c +
          sideLoadBefore (onlineOwnerBatchForest F assign e n hn)
            (onlineOwnerBatchFixedOrientation F assign orient e n hn) i c) ≤
      #((whole e c).filter
        (G.Adj (extendedRootImage S.rootImage n hn z
          (onlineFiberOwner F assign e
            (OrderedBranchForest.selectedEquiv
              (onlineOwnerBatch F assign e n hn) i)))))
  component : ∀ i c,
    ((onlineOwnerBatchForest F assign e n hn).size i : ℝ) +
        rho e * (#(whole e c) : ℝ) + 1 ≤
      (density e - rho e) *
        ((#(whole e c) : ℝ) - lossBound c -
          sideLoad (onlineOwnerBatchForest F assign e n hn)
            (onlineOwnerBatchFixedOrientation F assign orient e n hn) c)

namespace FixedOnlineOwnerEdgeFacts

/-- Build the exact edge record from separate bounds for permanent cleaning
and the already embedded prefix image. -/
def ofBounds
    {r b k : ℕ} {B : Type v} [Fintype B] [DecidableEq B]
    (F : OrderedBranchForest r b) (G : SimpleGraph B) [DecidableRel G.Adj]
    (assign : Fin b → Fin k)
    (orient : Fin b → Fin 2 ≃ Fin 2)
    (whole endpoint : Fin k → Fin 2 → Finset B)
    (rho density : Fin k → ℝ)
    (rootCandidate : Fin r → Finset B)
    (n : ℕ) (hn : n < r)
    (S : OnlineOwnerPrefixState F G assign endpoint rootCandidate n)
    (z : B) (e : Fin k)
    (reserve permanentBound usedBound : Fin 2 → ℕ)
    (huniform : G.IsUniform (rho e) (whole e 0) (whole e 1))
    (hdensity : density e ≤ G.edgeDensity (whole e 0) (whole e 1))
    (hfactor : 0 ≤ density e - rho e)
    (hreserve : ∀ c, rho e * (#(whole e c) : ℝ) ≤ reserve c)
    (hpermanent : ∀ c,
      #(whole e c \ endpoint e c) ≤ permanentBound c)
    (hused : ∀ c,
      #((reparentedEdgeState F G assign endpoint rootCandidate n hn S z e).used
        c) ≤ usedBound c)
    (htotal : ∀ c,
      permanentBound c + usedBound c +
          sideLoad (onlineOwnerBatchForest F assign e n hn)
            (onlineOwnerBatchFixedOrientation F assign orient e n hn) c +
          reserve c ≤ #(whole e c))
    (heligible : ∀ i,
      let c := branchRootSide (onlineOwnerBatchForest F assign e n hn)
        (onlineOwnerBatchFixedOrientation F assign orient e n hn) i
      permanentBound c + usedBound c +
          (1 + reserve c +
            sideLoadBefore (onlineOwnerBatchForest F assign e n hn)
              (onlineOwnerBatchFixedOrientation F assign orient e n hn)
              i c) ≤
        #((whole e c).filter
          (G.Adj (extendedRootImage S.rootImage n hn z
            (onlineFiberOwner F assign e
              (OrderedBranchForest.selectedEquiv
                (onlineOwnerBatch F assign e n hn) i))))))
    (hcomponent : ∀ i c,
      ((onlineOwnerBatchForest F assign e n hn).size i : ℝ) +
          rho e * (#(whole e c) : ℝ) + 1 ≤
        (density e - rho e) *
          ((#(whole e c) : ℝ) -
            ((permanentBound c + usedBound c : ℕ) : ℝ) -
            sideLoad (onlineOwnerBatchForest F assign e n hn)
              (onlineOwnerBatchFixedOrientation F assign orient e n hn) c)) :
    FixedOnlineOwnerEdgeFacts F G assign orient whole endpoint rho density
      rootCandidate n hn S z e where
  reserve := reserve
  lossBound := fun c ↦ permanentBound c + usedBound c
  uniform := huniform
  density_lower := hdensity
  factor_nonneg := hfactor
  reserve_regular := hreserve
  loss := by
    intro c
    exact card_combinedDeleted_le_of_bounds (whole e) (endpoint e)
      (reparentedEdgeState F G assign endpoint rootCandidate n hn S z e).used
      (fun _ ↦ ∅) permanentBound usedBound (fun _ ↦ 0) hpermanent hused
      (by intro d; simp) c
  total := htotal
  eligible := heligible
  component := hcomponent

/-- Recover the literal fixed-orientation local record from synchronized
per-edge facts.  The current live set is exactly the permanently cleaned
endpoint with the already embedded prefix removed. -/
noncomputable def toFixedOrientationStepData
    {r b k : ℕ} {B : Type v} [Fintype B] [DecidableEq B]
    (F : OrderedBranchForest r b) (G : SimpleGraph B) [DecidableRel G.Adj]
    (assign : Fin b → Fin k)
    (orient : Fin b → Fin 2 ≃ Fin 2)
    (whole endpoint : Fin k → Fin 2 → Finset B)
    (rho density : Fin k → ℝ)
    (rootCandidate : Fin r → Finset B)
    (n : ℕ) (hn : n < r)
    (S : OnlineOwnerPrefixState F G assign endpoint rootCandidate n)
    (z : B) (e : Fin k)
    (D : FixedOnlineOwnerEdgeFacts F G assign orient whole endpoint rho
      density rootCandidate n hn S z e)
    (hendpoint : ∀ c, endpoint e c ⊆ whole e c)
    (hwholeDisjoint : Disjoint (whole e 0) (whole e 1)) :
    FixedOrientationStepData
      (onlineOwnerBatchForest F assign e n hn) G
      (fun i ↦ extendedRootImage S.rootImage n hn z
        (onlineFiberOwner F assign e
          (OrderedBranchForest.selectedEquiv
            (onlineOwnerBatch F assign e n hn) i)))
      (onlineOwnerBatchFixedOrientation F assign orient e n hn)
      (whole e)
      (fun c ↦ endpoint e c \
        (reparentedEdgeState F G assign endpoint rootCandidate n hn S z e).used
          c)
      (rho e) (density e) := by
  let used : Fin 2 → Finset B :=
    (reparentedEdgeState F G assign endpoint rootCandidate n hn S z e).used
  have hused : ∀ c, used c ⊆ endpoint e c := by
    intro c
    exact (reparentedEdgeState F G assign endpoint rootCandidate n hn S z e
      |>.state.used_subset c)
  have hempty : ∀ c, (∅ : Finset B) ⊆ endpoint e c := by
    intro c
    exact Finset.empty_subset _
  have H := fixedOrientationStepDataOfCombinedBounds
    (onlineOwnerBatchForest F assign e n hn) G
    (fun i ↦ extendedRootImage S.rootImage n hn z
      (onlineFiberOwner F assign e
        (OrderedBranchForest.selectedEquiv
          (onlineOwnerBatch F assign e n hn) i)))
    (onlineOwnerBatchFixedOrientation F assign orient e n hn)
    (whole e) (endpoint e) used (fun _ ↦ ∅) (rho e) (density e) D.reserve
    hendpoint hused hempty D.uniform hwholeDisjoint D.density_lower
    D.factor_nonneg D.reserve_regular D.lossBound D.loss D.total D.eligible
    D.component
  have hLive :
      ownerCleanedLive
          (fun c ↦ endpoint e c \
            (reparentedEdgeState F G assign endpoint rootCandidate n hn S z e
              |>.used c))
          (fun _ ↦ ∅) =
        (fun c ↦ endpoint e c \
          (reparentedEdgeState F G assign endpoint rootCandidate n hn S z e
            |>.used c)) := by
    funext c
    simp only [ownerCleanedLive, Finset.sdiff_empty]
  rw [← hLive]
  exact H

end FixedOnlineOwnerEdgeFacts

/-- Per-edge scalar facts after replacing the actual used-set cardinality by
the exact fixed-orientation prefix load forced by the synchronized plan. -/
structure FixedPrefixOnlineOwnerEdgeFacts
    {r b k : ℕ} {B : Type v} [Fintype B] [DecidableEq B]
    (F : OrderedBranchForest r b) (G : SimpleGraph B) [DecidableRel G.Adj]
    (assign : Fin b → Fin k)
    (orient : Fin b → Fin 2 ≃ Fin 2)
    (whole endpoint : Fin k → Fin 2 → Finset B)
    (rho density : Fin k → ℝ)
    (rootCandidate : Fin r → Finset B)
    (n : ℕ) (hn : n < r)
    (S : OnlineOwnerPrefixState F G assign endpoint rootCandidate n)
    (z : B) (e : Fin k) : Type (max 0 v) where
  reserve : Fin 2 → ℕ
  permanentBound : Fin 2 → ℕ
  uniform : G.IsUniform (rho e) (whole e 0) (whole e 1)
  density_lower : density e ≤ G.edgeDensity (whole e 0) (whole e 1)
  factor_nonneg : 0 ≤ density e - rho e
  reserve_regular : ∀ c, rho e * (#(whole e c) : ℝ) ≤ reserve c
  permanent : ∀ c,
    #(whole e c \ endpoint e c) ≤ permanentBound c
  total : ∀ c,
    permanentBound c + globalFixedPrefixLoad F assign orient e n c +
        sideLoad (onlineOwnerBatchForest F assign e n hn)
          (onlineOwnerBatchFixedOrientation F assign orient e n hn) c +
        reserve c ≤ #(whole e c)
  eligible : ∀ i,
    let c := branchRootSide (onlineOwnerBatchForest F assign e n hn)
      (onlineOwnerBatchFixedOrientation F assign orient e n hn) i
    permanentBound c + globalFixedPrefixLoad F assign orient e n c +
        (1 + reserve c +
          sideLoadBefore (onlineOwnerBatchForest F assign e n hn)
            (onlineOwnerBatchFixedOrientation F assign orient e n hn)
            i c) ≤
      #((whole e c).filter
        (G.Adj (extendedRootImage S.rootImage n hn z
          (onlineFiberOwner F assign e
            (OrderedBranchForest.selectedEquiv
              (onlineOwnerBatch F assign e n hn) i)))))
  component : ∀ i c,
    ((onlineOwnerBatchForest F assign e n hn).size i : ℝ) +
        rho e * (#(whole e c) : ℝ) + 1 ≤
      (density e - rho e) *
        ((#(whole e c) : ℝ) -
          ((permanentBound c +
            globalFixedPrefixLoad F assign orient e n c : ℕ) : ℝ) -
          sideLoad (onlineOwnerBatchForest F assign e n hn)
            (onlineOwnerBatchFixedOrientation F assign orient e n hn) c)

namespace FixedPrefixOnlineOwnerEdgeFacts

/-- Supply the internally derived prefix-image bound to obtain the complete
edge facts consumed by the already checked successor constructor. -/
def toFixedOnlineOwnerEdgeFacts
    {r b k : ℕ} {B : Type v} [Fintype B] [DecidableEq B]
    (F : OrderedBranchForest r b) (G : SimpleGraph B) [DecidableRel G.Adj]
    (assign : Fin b → Fin k)
    (orient : Fin b → Fin 2 ≃ Fin 2)
    (whole endpoint : Fin k → Fin 2 → Finset B)
    (rho density : Fin k → ℝ)
    (rootCandidate : Fin r → Finset B)
    (n : ℕ) (hn : n < r)
    (S : OnlineOwnerPrefixState F G assign endpoint rootCandidate n)
    (z : B) (e : Fin k)
    (D : FixedPrefixOnlineOwnerEdgeFacts F G assign orient whole endpoint
      rho density rootCandidate n hn S z e)
    (hused : ∀ c,
      #((reparentedEdgeState F G assign endpoint rootCandidate n hn S z e).used
        c) ≤ globalFixedPrefixLoad F assign orient e n c) :
    FixedOnlineOwnerEdgeFacts F G assign orient whole endpoint rho density
      rootCandidate n hn S z e :=
  FixedOnlineOwnerEdgeFacts.ofBounds F G assign orient whole endpoint rho
    density rootCandidate n hn S z e D.reserve D.permanentBound
    (globalFixedPrefixLoad F assign orient e n) D.uniform D.density_lower
    D.factor_nonneg D.reserve_regular D.permanent hused D.total D.eligible
    D.component

end FixedPrefixOnlineOwnerEdgeFacts

/-- Per-edge facts where total capacity and component margin are stated only
against the final fixed-oriented load of the complete physical fiber.  The
current prefix and owner batch are bounded by that load internally. -/
structure FixedFullFiberOnlineOwnerEdgeFacts
    {r b k : ℕ} {B : Type v} [Fintype B] [DecidableEq B]
    (F : OrderedBranchForest r b) (G : SimpleGraph B) [DecidableRel G.Adj]
    (assign : Fin b → Fin k)
    (orient : Fin b → Fin 2 ≃ Fin 2)
    (whole endpoint : Fin k → Fin 2 → Finset B)
    (rho density : Fin k → ℝ)
    (rootCandidate : Fin r → Finset B)
    (n : ℕ) (hn : n < r)
    (S : OnlineOwnerPrefixState F G assign endpoint rootCandidate n)
    (z : B) (e : Fin k) : Type (max 0 v) where
  reserve : Fin 2 → ℕ
  permanentBound : Fin 2 → ℕ
  uniform : G.IsUniform (rho e) (whole e 0) (whole e 1)
  density_lower : density e ≤ G.edgeDensity (whole e 0) (whole e 1)
  factor_nonneg : 0 ≤ density e - rho e
  reserve_regular : ∀ c, rho e * (#(whole e c) : ℝ) ≤ reserve c
  permanent : ∀ c,
    #(whole e c \ endpoint e c) ≤ permanentBound c
  total : ∀ c,
    permanentBound c +
        sideLoad (onlineFiberForest F assign e)
          (globalFixedFiberOrientation F assign orient e) c +
        reserve c ≤ #(whole e c)
  eligible : ∀ i,
    let c := branchRootSide (onlineOwnerBatchForest F assign e n hn)
      (onlineOwnerBatchFixedOrientation F assign orient e n hn) i
    permanentBound c + globalFixedPrefixLoad F assign orient e n c +
        (1 + reserve c +
          sideLoadBefore (onlineOwnerBatchForest F assign e n hn)
            (onlineOwnerBatchFixedOrientation F assign orient e n hn)
            i c) ≤
      #((whole e c).filter
        (G.Adj (extendedRootImage S.rootImage n hn z
          (onlineFiberOwner F assign e
            (OrderedBranchForest.selectedEquiv
              (onlineOwnerBatch F assign e n hn) i)))))
  component : ∀ i c,
    ((onlineOwnerBatchForest F assign e n hn).size i : ℝ) +
        rho e * (#(whole e c) : ℝ) + 1 ≤
      (density e - rho e) *
        ((#(whole e c) : ℝ) - permanentBound c -
          sideLoad (onlineFiberForest F assign e)
            (globalFixedFiberOrientation F assign orient e) c)

namespace FixedFullFiberOnlineOwnerEdgeFacts

/-- Restrict complete-fiber capacity and margin estimates to the exact
prefix-plus-current-batch load. -/
def toFixedPrefixOnlineOwnerEdgeFacts
    {r b k : ℕ} {B : Type v} [Fintype B] [DecidableEq B]
    (F : OrderedBranchForest r b) (G : SimpleGraph B) [DecidableRel G.Adj]
    (assign : Fin b → Fin k)
    (orient : Fin b → Fin 2 ≃ Fin 2)
    (whole endpoint : Fin k → Fin 2 → Finset B)
    (rho density : Fin k → ℝ)
    (rootCandidate : Fin r → Finset B)
    (n : ℕ) (hn : n < r)
    (S : OnlineOwnerPrefixState F G assign endpoint rootCandidate n)
    (z : B) (e : Fin k)
    (D : FixedFullFiberOnlineOwnerEdgeFacts F G assign orient whole endpoint
      rho density rootCandidate n hn S z e) :
    FixedPrefixOnlineOwnerEdgeFacts F G assign orient whole endpoint rho
      density rootCandidate n hn S z e where
  reserve := D.reserve
  permanentBound := D.permanentBound
  uniform := D.uniform
  density_lower := D.density_lower
  factor_nonneg := D.factor_nonneg
  reserve_regular := D.reserve_regular
  permanent := D.permanent
  total := by
    intro c
    have hload := globalFixedPrefixLoad_add_batch_le_sideLoad F assign orient
      e n hn c
    calc
      D.permanentBound c + globalFixedPrefixLoad F assign orient e n c +
            sideLoad (onlineOwnerBatchForest F assign e n hn)
              (onlineOwnerBatchFixedOrientation F assign orient e n hn) c +
            D.reserve c ≤
          D.permanentBound c +
            sideLoad (onlineFiberForest F assign e)
              (globalFixedFiberOrientation F assign orient e) c +
            D.reserve c := by omega
      _ ≤ #(whole e c) := D.total c
  eligible := D.eligible
  component := by
    intro i c
    have hload := globalFixedPrefixLoad_add_batch_le_sideLoad F assign orient
      e n hn c
    have hloadReal :
        ((globalFixedPrefixLoad F assign orient e n c +
          sideLoad (onlineOwnerBatchForest F assign e n hn)
            (onlineOwnerBatchFixedOrientation F assign orient e n hn) c : ℕ) :
            ℝ) ≤
          sideLoad (onlineFiberForest F assign e)
            (globalFixedFiberOrientation F assign orient e) c := by
      exact_mod_cast hload
    have hbase := D.component i c
    norm_num only [Nat.cast_add] at hloadReal ⊢
    nlinarith [D.factor_nonneg]

end FixedFullFiberOnlineOwnerEdgeFacts

/-- Convert per-edge scalar facts into the complete plan-certified successor
datum for the synchronized owner recursion. -/
noncomputable def plannedOnlineOwnerSuccessorDataOfFixedFacts
    {r b k : ℕ} {B : Type v} [Fintype B] [DecidableEq B]
    (F : OrderedBranchForest r b) (G : SimpleGraph B) [DecidableRel G.Adj]
    (assign : Fin b → Fin k)
    (orient : Fin b → Fin 2 ≃ Fin 2)
    (whole endpoint : Fin k → Fin 2 → Finset B)
    (hendpoint : ∀ e c, endpoint e c ⊆ whole e c)
    (hwholeDisjoint : ∀ e, Disjoint (whole e 0) (whole e 1))
    (rho density : Fin k → ℝ)
    (rootCandidate : Fin r → Finset B)
    (n : ℕ) (hn : n < r)
    (S : OnlineOwnerPrefixState F G assign endpoint rootCandidate n)
    (z : B)
    (facts : ∀ e, FixedOnlineOwnerEdgeFacts F G assign orient whole endpoint
      rho density rootCandidate n hn S z e) :
    PlannedOnlineOwnerSuccessorData F G assign whole endpoint rho density
      rootCandidate (globalFixedRootAllowed F assign orient)
      (globalFixedCoordinateAllowed F assign orient) n hn S z := by
  intro e
  let used : Fin 2 → Finset B :=
    (reparentedEdgeState F G assign endpoint rootCandidate n hn S z e).used
  let externalParent : Fin (onlineOwnerBatch F assign e n hn).card → B :=
    fun i ↦ extendedRootImage S.rootImage n hn z
      (onlineFiberOwner F assign e
        (OrderedBranchForest.selectedEquiv
          (onlineOwnerBatch F assign e n hn) i))
  let D := facts e
  have hused : ∀ c, used c ⊆ endpoint e c := by
    intro c
    exact (reparentedEdgeState F G assign endpoint rootCandidate n hn S z e
      |>.state.used_subset c)
  have hempty : ∀ c, (∅ : Finset B) ⊆ endpoint e c := by
    intro c
    exact Finset.empty_subset _
  have H := plannedFixedOwnerLocalStepDataOfCombinedBounds F G assign orient e
    n hn externalParent (whole e) (endpoint e) used (fun _ ↦ ∅)
    (rho e) (density e) D.reserve (hendpoint e) hused hempty D.uniform
    (hwholeDisjoint e) D.density_lower D.factor_nonneg D.reserve_regular
    D.lossBound D.loss D.total D.eligible D.component
  have hLive :
      ownerCleanedLive (fun c ↦ endpoint e c \ used c) (fun _ ↦ ∅) =
        (fun c ↦ endpoint e c \ used c) := by
    funext c
    simp only [ownerCleanedLive, Finset.sdiff_empty]
  rw [← hLive]
  exact H

/-- Plan-certified successor obtained from scalar facts in which the used
prefix is charged by its exact global fixed-orientation load. -/
noncomputable def plannedOnlineOwnerSuccessorDataOfFixedPrefixFacts
    {r b k : ℕ} {B : Type v} [Fintype B] [DecidableEq B]
    (F : OrderedBranchForest r b) (G : SimpleGraph B) [DecidableRel G.Adj]
    (assign : Fin b → Fin k)
    (orient : Fin b → Fin 2 ≃ Fin 2)
    (whole endpoint : Fin k → Fin 2 → Finset B)
    (hendpoint : ∀ e c, endpoint e c ⊆ whole e c)
    (hwholeDisjoint : ∀ e, Disjoint (whole e 0) (whole e 1))
    (rho density : Fin k → ℝ)
    (rootCandidate : Fin r → Finset B)
    (n : ℕ) (hn : n < r)
    (S : PlannedOnlineOwnerPrefixState F G assign endpoint rootCandidate
      (globalFixedCoordinateAllowed F assign orient) n)
    (z : B)
    (facts : ∀ e, FixedPrefixOnlineOwnerEdgeFacts F G assign orient whole
      endpoint rho density rootCandidate n hn S.state z e) :
    PlannedOnlineOwnerSuccessorData F G assign whole endpoint rho density
      rootCandidate (globalFixedRootAllowed F assign orient)
      (globalFixedCoordinateAllowed F assign orient) n hn S.state z :=
  plannedOnlineOwnerSuccessorDataOfFixedFacts F G assign orient whole endpoint
    hendpoint hwholeDisjoint rho density rootCandidate n hn S.state z
    (fun e ↦ (facts e).toFixedOnlineOwnerEdgeFacts F G assign orient whole
      endpoint rho density rootCandidate n hn S.state z e
      (fun c ↦
        Erdos547b.ZhaoLemma58GlobalFixedOrientationPlan.PlannedOnlineOwnerPrefixState.card_reparented_used_le_fixedPrefixLoad
          F G assign endpoint rootCandidate orient n hn S z e c))

/-- Full-fiber scalar form of the fixed-plan successor. -/
noncomputable def plannedOnlineOwnerSuccessorDataOfFixedFullFiberFacts
    {r b k : ℕ} {B : Type v} [Fintype B] [DecidableEq B]
    (F : OrderedBranchForest r b) (G : SimpleGraph B) [DecidableRel G.Adj]
    (assign : Fin b → Fin k)
    (orient : Fin b → Fin 2 ≃ Fin 2)
    (whole endpoint : Fin k → Fin 2 → Finset B)
    (hendpoint : ∀ e c, endpoint e c ⊆ whole e c)
    (hwholeDisjoint : ∀ e, Disjoint (whole e 0) (whole e 1))
    (rho density : Fin k → ℝ)
    (rootCandidate : Fin r → Finset B)
    (n : ℕ) (hn : n < r)
    (S : PlannedOnlineOwnerPrefixState F G assign endpoint rootCandidate
      (globalFixedCoordinateAllowed F assign orient) n)
    (z : B)
    (facts : ∀ e, FixedFullFiberOnlineOwnerEdgeFacts F G assign orient whole
      endpoint rho density rootCandidate n hn S.state z e) :
    PlannedOnlineOwnerSuccessorData F G assign whole endpoint rho density
      rootCandidate (globalFixedRootAllowed F assign orient)
      (globalFixedCoordinateAllowed F assign orient) n hn S.state z :=
  plannedOnlineOwnerSuccessorDataOfFixedPrefixFacts F G assign orient whole
    endpoint hendpoint hwholeDisjoint rho density rootCandidate n hn S z
    (fun e ↦ (facts e).toFixedPrefixOnlineOwnerEdgeFacts F G assign orient
      whole endpoint rho density rootCandidate n hn S.state z e)

end Erdos547b.ZhaoLemma58GlobalFixedOnlineSuccessor

#print axioms Erdos547b.ZhaoLemma58GlobalFixedOnlineSuccessor.FixedOnlineOwnerEdgeFacts.toFixedOrientationStepData
#print axioms Erdos547b.ZhaoLemma58GlobalFixedOnlineSuccessor.plannedOnlineOwnerSuccessorDataOfFixedFacts
#print axioms Erdos547b.ZhaoLemma58GlobalFixedOnlineSuccessor.plannedOnlineOwnerSuccessorDataOfFixedPrefixFacts
#print axioms Erdos547b.ZhaoLemma58GlobalFixedOnlineSuccessor.plannedOnlineOwnerSuccessorDataOfFixedFullFiberFacts
