/- leanprover/lean4:v4.33.0 -/
import ErdosProblems.Erdos547b.Lemma58GlobalPlannedOwnerSuccessor
import ErdosProblems.Erdos547b.Lemma58OwnerLocalStep
import ErdosProblems.Erdos547b.Lemma58CombinedResidual
import ErdosProblems.Erdos547b.Lemma58SelectedOrientationReindex

/-!
# Scalar Appendix successors in the synchronized online state

This is the Part-3 analogue of the fixed-orientation per-edge records.  The
record contains only the exact current Appendix numeric and regular-pair
facts.  The common-parent identity of an owner batch is derived internally
from the synchronized owner indexing.
-/

open scoped SimpleGraph
noncomputable section

namespace Erdos547b.ZhaoLemma58GlobalAppendixOnlineSuccessor

open Finset Fintype SimpleGraph
open Erdos547b.RegularPair
open Erdos547b.ZhaoLemma59Part2Full
open Erdos547b.ZhaoClaim616SourceBridge
open Erdos547b.ZhaoClaim616SourceBridge.OrderedBranchForest
open Erdos547b.ZhaoLemma58GroupedSmallForest
open Erdos547b.ZhaoLemma54AppendixA
open Erdos547b.ZhaoLemma58OwnerLocalStep
open Erdos547b.ZhaoLemma58GlobalOwnerOnlineState
open Erdos547b.ZhaoLemma58GlobalPlannedOwnerSuccessor
open Erdos547b.ZhaoLemma58CombinedResidual
open Erdos547b.ZhaoLemma58SelectedOrientationReindex
open Erdos547b.ZhaoLemma58DynamicBatchAppend

universe v

/-- Deleting a bounded permanent set and then a bounded prefix image from a
raw target preserves the advertised number of neighbours.  This is the
two-stage cardinal estimate used for the live Appendix root pools. -/
theorem card_liveRootPool_ge_of_two_stage_bounds
    {B : Type v} [Fintype B] [DecidableEq B]
    (G : SimpleGraph B) [DecidableRel G.Adj]
    (z : B) (raw clean used : Finset B)
    (rootMargin cleanBound usedBound : ℕ)
    (hclean : clean ⊆ raw)
    (hcleanLoss : #(raw \ clean) ≤ cleanBound)
    (husedCard : #used ≤ usedBound)
    (hdegree : rootMargin + cleanBound + usedBound ≤
      #(raw.filter (G.Adj z))) :
    rootMargin ≤ #((clean \ used).filter (G.Adj z)) := by
  have hrawFirst : rootMargin + usedBound + #(raw \ clean) ≤
      #(raw.filter (G.Adj z)) := by omega
  have hfirst := card_neighbors_cleaned_ge G raw (raw \ clean) z
    (rootMargin + usedBound) hrawFirst
  have hcleanEq : raw \ (raw \ clean) = clean := by
    ext x
    constructor
    · intro hx
      have hx' := Finset.mem_sdiff.mp hx
      by_contra hxc
      exact hx'.2 (Finset.mem_sdiff.mpr ⟨hx'.1, hxc⟩)
    · intro hx
      exact Finset.mem_sdiff.mpr
        ⟨hclean hx, fun hbad ↦ (Finset.mem_sdiff.mp hbad).2 hx⟩
  rw [hcleanEq] at hfirst
  have hcleanSecond : rootMargin + #used ≤ #(clean.filter (G.Adj z)) := by
    omega
  exact card_neighbors_cleaned_ge G clean used z rootMargin hcleanSecond

/-- Two bounded deletions preserve the advertised number of vertices.  This
is the non-neighbour analogue of `card_liveRootPool_ge_of_two_stage_bounds`. -/
theorem card_live_ge_of_two_stage_bounds
    {B : Type v} [Fintype B] [DecidableEq B]
    (raw clean used : Finset B) (liveMargin cleanBound usedBound : ℕ)
    (hclean : clean ⊆ raw)
    (hcleanLoss : #(raw \ clean) ≤ cleanBound)
    (husedCard : #used ≤ usedBound)
    (hcapacity : liveMargin + cleanBound + usedBound ≤ #raw) :
    liveMargin ≤ #(clean \ used) := by
  have hsplitClean := Finset.card_sdiff_add_card_inter clean used
  have hinter : #(clean ∩ used) ≤ #used :=
    Finset.card_le_card Finset.inter_subset_right
  have hsplitRaw := Finset.card_sdiff_add_card_eq_card hclean
  omega

/-- In a synchronized edge state, the old used set together with one root
for every component in the current owner batch is bounded by the order of the
complete edge fiber. -/
theorem card_reparented_used_add_ownerBatch_card_le_fiber_order
    {r b k : ℕ} {B : Type v} [Fintype B] [DecidableEq B]
    (F : OrderedBranchForest r b) (G : SimpleGraph B)
    (assign : Fin b → Fin k) (endpoint : Fin k → Fin 2 → Finset B)
    (rootCandidate : Fin r → Finset B)
    (n : ℕ) (hn : n < r)
    (state : OnlineOwnerPrefixState F G assign endpoint rootCandidate n)
    (z : B) (e : Fin k)
    (hcomponent : ∀ i, 1 ≤ (onlineOwnerBatchForest F assign e n hn).size i)
    (c : Fin 2) :
    #((reparentedEdgeState F G assign endpoint rootCandidate n hn state z e
        |>.used c)) + #(onlineOwnerBatch F assign e n hn) ≤
      (onlineFiberForest F assign e).order := by
  classical
  let fiber := onlineFiberForest F assign e
  let owner := onlineFiberOwner F assign e
  let prior := ownerPrefix Finset.univ owner n
  let batch := ownerBatch Finset.univ owner ⟨n, hn⟩
  have hused :
      #((reparentedEdgeState F G assign endpoint rootCandidate n hn state z e
          |>.used c)) ≤ ∑ i ∈ prior, fiber.size i := by
    simpa only [prior, fiber, owner] using
      card_chosenPartial_used_le_selectedOrder
        (reparentedEdgeState F G assign endpoint rootCandidate n hn state z e) c
  have hbatch : #batch ≤ ∑ i ∈ batch, fiber.size i := by
    calc
      #batch = ∑ _i : Fin batch.card, 1 := by simp
      _ ≤ ∑ i : Fin batch.card, (selectedForest fiber batch).size i := by
        exact Finset.sum_le_sum fun i _ ↦ hcomponent i
      _ = (selectedForest fiber batch).order := rfl
      _ = ∑ i ∈ batch, fiber.size i := selectedForest_order fiber batch
  have hsum : (∑ i ∈ prior, fiber.size i) +
        (∑ i ∈ batch, fiber.size i) ≤ fiber.order := by
    rw [← Finset.sum_union
      (ownerPrefix_disjoint_ownerBatch Finset.univ owner n hn)]
    rw [ownerPrefix_succ]
    exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  exact (Nat.add_le_add hused hbatch).trans hsum

/-- Exact source and residual-host facts for one Appendix owner batch in a
synchronized matching-edge state. -/
structure AppendixOnlineOwnerEdgeFacts
    {r b k : ℕ} {B : Type v} [Fintype B] [DecidableEq B]
    (F : OrderedBranchForest r b) (G : SimpleGraph B) [DecidableRel G.Adj]
    (assign : Fin b → Fin k)
    (whole endpoint : Fin k → Fin 2 → Finset B)
    (rho density : Fin k → ℝ)
    (rootCandidate : Fin r → Finset B)
    (n : ℕ) (hn : n < r)
    (state : OnlineOwnerPrefixState F G assign endpoint rootCandidate n)
    (z : B) (e : Fin k) : Type (max 0 v) where
  small : ℕ
  rootMargin : ℕ
  sideMargin : ℕ
  gamma : ℝ
  epsilon : ℝ
  N : ℝ
  numeric : AppendixA2NumericData
    (onlineOwnerBatchForest F assign e n hn) small rootMargin sideMargin
    #(endpoint e 0 \
      (reparentedEdgeState F G assign endpoint rootCandidate n hn state z e
        |>.used 0))
    #(endpoint e 1 \
      (reparentedEdgeState F G assign endpoint rootCandidate n hn state z e
        |>.used 1))
    #(currentRootPool G z
      (fun c ↦ endpoint e c \
        (reparentedEdgeState F G assign endpoint rootCandidate n hn state z e
          |>.used c)) 0)
    #(currentRootPool G z
      (fun c ↦ endpoint e c \
        (reparentedEdgeState F G assign endpoint rootCandidate n hn state z e
          |>.used c)) 1)
    gamma epsilon N
  uniform : G.IsUniform (rho e) (whole e 0) (whole e 1)
  live_subset : ∀ c,
    endpoint e c \
        (reparentedEdgeState F G assign endpoint rootCandidate n hn state z e
          |>.used c) ⊆ whole e c
  whole_disjoint : Disjoint (whole e 0) (whole e 1)
  density_lower : density e ≤ G.edgeDensity (whole e 0) (whole e 1)
  factor_nonneg : 0 ≤ density e - rho e
  epsilonN_nonneg : 0 ≤ epsilon * N
  regular_root : ∀ c, rho e * (#(whole e c) : ℝ) < 3 * epsilon * N
  regular_interior : ∀ c, rho e * (#(whole e c) : ℝ) ≤ gamma * N
  component_margin : ∀ i c,
    ((onlineOwnerBatchForest F assign e n hn).size i : ℝ) +
        rho e * (#(whole e c) : ℝ) ≤
      (density e - rho e) * (gamma * N)

/-- The same synchronized Appendix facts after choosing a local ordering of
the two physical endpoints. -/
structure ReindexedAppendixOnlineOwnerEdgeFacts
    {r b k : ℕ} {B : Type v} [Fintype B] [DecidableEq B]
    (F : OrderedBranchForest r b) (G : SimpleGraph B) [DecidableRel G.Adj]
    (assign : Fin b → Fin k)
    (whole endpoint : Fin k → Fin 2 → Finset B)
    (rho density : Fin k → ℝ)
    (rootCandidate : Fin r → Finset B)
    (n : ℕ) (hn : n < r)
    (state : OnlineOwnerPrefixState F G assign endpoint rootCandidate n)
    (z : B) (e : Fin k) : Type (max 0 v) where
  sideEquiv : Fin 2 ≃ Fin 2
  small : ℕ
  rootMargin : ℕ
  sideMargin : ℕ
  gamma : ℝ
  epsilon : ℝ
  N : ℝ
  numeric : AppendixA2NumericData
    (onlineOwnerBatchForest F assign e n hn) small rootMargin sideMargin
    #(endpoint e (sideEquiv 0) \
      (reparentedEdgeState F G assign endpoint rootCandidate n hn state z e
        |>.used (sideEquiv 0)))
    #(endpoint e (sideEquiv 1) \
      (reparentedEdgeState F G assign endpoint rootCandidate n hn state z e
        |>.used (sideEquiv 1)))
    #(currentRootPool G z
      (fun c ↦ endpoint e c \
        (reparentedEdgeState F G assign endpoint rootCandidate n hn state z e
          |>.used c)) (sideEquiv 0))
    #(currentRootPool G z
      (fun c ↦ endpoint e c \
        (reparentedEdgeState F G assign endpoint rootCandidate n hn state z e
          |>.used c)) (sideEquiv 1))
    gamma epsilon N
  uniform : G.IsUniform (rho e) (whole e (sideEquiv 0))
    (whole e (sideEquiv 1))
  live_subset : ∀ c,
    endpoint e (sideEquiv c) \
        (reparentedEdgeState F G assign endpoint rootCandidate n hn state z e
          |>.used (sideEquiv c)) ⊆ whole e (sideEquiv c)
  whole_disjoint : Disjoint (whole e (sideEquiv 0))
    (whole e (sideEquiv 1))
  density_lower : density e ≤
    G.edgeDensity (whole e (sideEquiv 0)) (whole e (sideEquiv 1))
  factor_nonneg : 0 ≤ density e - rho e
  epsilonN_nonneg : 0 ≤ epsilon * N
  regular_root : ∀ c,
    rho e * (#(whole e (sideEquiv c)) : ℝ) < 3 * epsilon * N
  regular_interior : ∀ c,
    rho e * (#(whole e (sideEquiv c)) : ℝ) ≤ gamma * N
  component_margin : ∀ i c,
    ((onlineOwnerBatchForest F assign e n hn).size i : ℝ) +
        rho e * (#(whole e (sideEquiv c)) : ℝ) ≤
      (density e - rho e) * (gamma * N)

/-- Choose the smaller literal residual endpoint as Appendix side zero.  All
input inequalities are symmetric in the physical sides, so no persistent
endpoint-cardinality ordering is assumed. -/
noncomputable def reindexedAppendixOnlineOwnerEdgeFactsOfSymmetricBounds
    {r b k : ℕ} {B : Type v} [Fintype B] [DecidableEq B]
    (F : OrderedBranchForest r b) (G : SimpleGraph B) [DecidableRel G.Adj]
    (assign : Fin b → Fin k)
    (whole endpoint : Fin k → Fin 2 → Finset B)
    (rho density : Fin k → ℝ)
    (rootCandidate : Fin r → Finset B)
    (n : ℕ) (hn : n < r)
    (state : OnlineOwnerPrefixState F G assign endpoint rootCandidate n)
    (z : B) (e : Fin k)
    (small rootMargin sideMargin : ℕ) (gamma epsilon N : ℝ)
    (hcomponentLower : ∀ i,
      2 ≤ (onlineOwnerBatchForest F assign e n hn).size i)
    (hcomponentUpper : ∀ i,
      (onlineOwnerBatchForest F assign e n hn).size i ≤ small)
    (hrootReserve : ∀ c,
      rootMargin ≤ #(currentRootPool G z
        (fun d ↦ endpoint e d \
          (reparentedEdgeState F G assign endpoint rootCandidate n hn state z e
            |>.used d)) c))
    (hrootSide : rootMargin ≤ sideMargin)
    (hrootSlots : #(onlineOwnerBatch F assign e n hn) + 2 * rootMargin ≤
      #(currentRootPool G z
        (fun d ↦ endpoint e d \
          (reparentedEdgeState F G assign endpoint rootCandidate n hn state z e
            |>.used d)) 0) +
      #(currentRootPool G z
        (fun d ↦ endpoint e d \
          (reparentedEdgeState F G assign endpoint rootCandidate n hn state z e
            |>.used d)) 1))
    (hsideSlots : (onlineOwnerBatchForest F assign e n hn).order +
        2 * sideMargin + small ≤
      Nat.min
        #(currentRootPool G z
          (fun d ↦ endpoint e d \
            (reparentedEdgeState F G assign endpoint rootCandidate n hn state z e
              |>.used d)) 0)
        #(currentRootPool G z
          (fun d ↦ endpoint e d \
            (reparentedEdgeState F G assign endpoint rootCandidate n hn state z e
              |>.used d)) 1) +
      Nat.min
        #(endpoint e 0 \
          (reparentedEdgeState F G assign endpoint rootCandidate n hn state z e
            |>.used 0))
        #(endpoint e 1 \
          (reparentedEdgeState F G assign endpoint rootCandidate n hn state z e
            |>.used 1)))
    (hrootRound : 3 * epsilon * N ≤ rootMargin)
    (hsideRound : (gamma + 3 * epsilon) * N ≤ sideMargin)
    (huniform : G.IsUniform (rho e) (whole e 0) (whole e 1))
    (hliveSubset : ∀ c,
      endpoint e c \
          (reparentedEdgeState F G assign endpoint rootCandidate n hn state z e
            |>.used c) ⊆ whole e c)
    (hwholeDisjoint : Disjoint (whole e 0) (whole e 1))
    (hdensity : density e ≤ G.edgeDensity (whole e 0) (whole e 1))
    (hfactor : 0 ≤ density e - rho e)
    (hepsilonN : 0 ≤ epsilon * N)
    (hregularRoot : ∀ c,
      rho e * (#(whole e c) : ℝ) < 3 * epsilon * N)
    (hregularInterior : ∀ c,
      rho e * (#(whole e c) : ℝ) ≤ gamma * N)
    (hcomponentMargin : ∀ i c,
      ((onlineOwnerBatchForest F assign e n hn).size i : ℝ) +
          rho e * (#(whole e c) : ℝ) ≤
        (density e - rho e) * (gamma * N)) :
    ReindexedAppendixOnlineOwnerEdgeFacts F G assign whole endpoint rho density
      rootCandidate n hn state z e := by
  let live : Fin 2 → Finset B := fun c ↦ endpoint e c \
    (reparentedEdgeState F G assign endpoint rootCandidate n hn state z e
      |>.used c)
  let roots : Fin 2 → Finset B := currentRootPool G z live
  by_cases hle : #(live 0) ≤ #(live 1)
  · have hnumeric : AppendixA2NumericData
        (onlineOwnerBatchForest F assign e n hn) small rootMargin sideMargin
        #(live 0) #(live 1) #(roots 0) #(roots 1) gamma epsilon N := by
      refine {
        component_lower := hcomponentLower
        component_upper := hcomponentUpper
        X_le_Y := hle
        P_le_X := Finset.card_le_card (Finset.filter_subset _ _)
        rootReserve_le_P := ?_
        rootReserve_le_Q := ?_
        rootReserve_le_sideReserve := hrootSide
        root_slots := ?_
        side_slots := ?_
        root_rounding := hrootRound
        side_rounding := hsideRound
      }
      · simpa only [roots, live] using hrootReserve 0
      · simpa only [roots, live] using hrootReserve 1
      · simpa only [roots, live] using hrootSlots
      · simpa only [roots, live, Nat.min_eq_left hle] using hsideSlots
    have hlive : ∀ c,
        endpoint e ((Equiv.refl (Fin 2)) c) \
            (reparentedEdgeState F G assign endpoint rootCandidate n hn state z e
              |>.used ((Equiv.refl (Fin 2)) c)) ⊆
          whole e ((Equiv.refl (Fin 2)) c) := by
      intro c
      simpa only [Equiv.refl_apply] using hliveSubset c
    exact {
      sideEquiv := Equiv.refl _
      small := small
      rootMargin := rootMargin
      sideMargin := sideMargin
      gamma := gamma
      epsilon := epsilon
      N := N
      numeric := by simpa only [live, roots, Equiv.refl_apply] using hnumeric
      uniform := huniform
      live_subset := hlive
      whole_disjoint := hwholeDisjoint
      density_lower := hdensity
      factor_nonneg := hfactor
      epsilonN_nonneg := hepsilonN
      regular_root := fun c ↦ by
        simpa only [Equiv.refl_apply] using hregularRoot c
      regular_interior := fun c ↦ by
        simpa only [Equiv.refl_apply] using hregularInterior c
      component_margin := fun i c ↦ by
        simpa only [Equiv.refl_apply] using hcomponentMargin i c
    }
  · have hrev : #(live 1) ≤ #(live 0) := by omega
    have hswap0 : Equiv.swap (0 : Fin 2) 1 0 = 1 := by decide
    have hswap1 : Equiv.swap (0 : Fin 2) 1 1 = 0 := by decide
    have hnumeric : AppendixA2NumericData
        (onlineOwnerBatchForest F assign e n hn) small rootMargin sideMargin
        #(live 1) #(live 0) #(roots 1) #(roots 0) gamma epsilon N := by
      refine {
        component_lower := hcomponentLower
        component_upper := hcomponentUpper
        X_le_Y := hrev
        P_le_X := Finset.card_le_card (Finset.filter_subset _ _)
        rootReserve_le_P := ?_
        rootReserve_le_Q := ?_
        rootReserve_le_sideReserve := hrootSide
        root_slots := ?_
        side_slots := ?_
        root_rounding := hrootRound
        side_rounding := hsideRound
      }
      · simpa only [roots, live] using hrootReserve 1
      · simpa only [roots, live] using hrootReserve 0
      · exact hrootSlots.trans_eq (Nat.add_comm _ _)
      · calc
          _ ≤ Nat.min #(roots 0) #(roots 1) +
                Nat.min #(live 0) #(live 1) := by
              simpa only [roots, live] using hsideSlots
          _ = Nat.min #(roots 1) #(roots 0) +
                Nat.min #(live 0) #(live 1) := by
              exact congrArg (fun t ↦ t + Nat.min #(live 0) #(live 1))
                (Nat.min_comm _ _)
          _ = Nat.min #(roots 1) #(roots 0) + #(live 1) := by
              exact congrArg (fun t ↦ Nat.min #(roots 1) #(roots 0) + t)
                (Nat.min_eq_right hrev)
    have huniform' : G.IsUniform (rho e) (whole e 1) (whole e 0) := by
      exact huniform.symm
    have hwholeDisjoint' : Disjoint (whole e 1) (whole e 0) :=
      hwholeDisjoint.symm
    have hdensity' : density e ≤ G.edgeDensity (whole e 1) (whole e 0) := by
      simpa only [G.edgeDensity_comm] using hdensity
    exact {
      sideEquiv := Equiv.swap (0 : Fin 2) 1
      small := small
      rootMargin := rootMargin
      sideMargin := sideMargin
      gamma := gamma
      epsilon := epsilon
      N := N
      numeric := by simpa only [hswap0, hswap1, live, roots] using hnumeric
      uniform := by simpa only [hswap0, hswap1] using huniform'
      live_subset := fun c ↦ hliveSubset _
      whole_disjoint := by simpa only [hswap0, hswap1] using hwholeDisjoint'
      density_lower := by simpa only [hswap0, hswap1] using hdensity'
      factor_nonneg := hfactor
      epsilonN_nonneg := hepsilonN
      regular_root := fun c ↦ hregularRoot _
      regular_interior := fun c ↦ hregularInterior _
      component_margin := fun i c ↦ hcomponentMargin i _
    }

namespace AppendixOnlineOwnerEdgeFacts

/-- Convert the scalar synchronized record to the literal local Appendix
datum. -/
noncomputable def toAppendixStepData
    {r b k : ℕ} {B : Type v} [Fintype B] [DecidableEq B]
    (F : OrderedBranchForest r b) (G : SimpleGraph B) [DecidableRel G.Adj]
    (assign : Fin b → Fin k)
    (whole endpoint : Fin k → Fin 2 → Finset B)
    (rho density : Fin k → ℝ)
    (rootCandidate : Fin r → Finset B)
    (n : ℕ) (hn : n < r)
    (state : OnlineOwnerPrefixState F G assign endpoint rootCandidate n)
    (z : B) (e : Fin k)
    (D : AppendixOnlineOwnerEdgeFacts F G assign whole endpoint rho density
      rootCandidate n hn state z e) :
    AppendixStepData
      (onlineOwnerBatchForest F assign e n hn) G
      (fun i ↦ extendedRootImage state.rootImage n hn z
        (onlineFiberOwner F assign e
          (OrderedBranchForest.selectedEquiv
            (onlineOwnerBatch F assign e n hn) i)))
      (whole e)
      (fun c ↦ endpoint e c \
        (reparentedEdgeState F G assign endpoint rootCandidate n hn state z e
          |>.used c))
      (rho e) (density e) where
  parent := z
  small := D.small
  rootMargin := D.rootMargin
  sideMargin := D.sideMargin
  gamma := D.gamma
  epsilon := D.epsilon
  N := D.N
  common_parent := by
    intro i
    have howner :
        onlineFiberOwner F assign e
            (OrderedBranchForest.selectedEquiv
              (onlineOwnerBatch F assign e n hn) i) = ⟨n, hn⟩ := by
      change F.owner (onlineOwnerBatchBranch F assign e n hn i) = ⟨n, hn⟩
      exact onlineOwnerBatchBranch_owner F assign e n hn i
    rw [howner, extendedRootImage_current]
  numeric := D.numeric
  uniform := D.uniform
  live_subset := D.live_subset
  whole_disjoint := D.whole_disjoint
  density_lower := D.density_lower
  factor_nonneg := D.factor_nonneg
  epsilonN_nonneg := D.epsilonN_nonneg
  regular_root := D.regular_root
  regular_interior := D.regular_interior
  component_margin := D.component_margin

end AppendixOnlineOwnerEdgeFacts

namespace ReindexedAppendixOnlineOwnerEdgeFacts

/-- Convert locally reordered synchronized facts to the literal reindexed
Appendix datum. -/
noncomputable def toReindexedAppendixStepData
    {r b k : ℕ} {B : Type v} [Fintype B] [DecidableEq B]
    (F : OrderedBranchForest r b) (G : SimpleGraph B) [DecidableRel G.Adj]
    (assign : Fin b → Fin k)
    (whole endpoint : Fin k → Fin 2 → Finset B)
    (rho density : Fin k → ℝ)
    (rootCandidate : Fin r → Finset B)
    (n : ℕ) (hn : n < r)
    (state : OnlineOwnerPrefixState F G assign endpoint rootCandidate n)
    (z : B) (e : Fin k)
    (D : ReindexedAppendixOnlineOwnerEdgeFacts F G assign whole endpoint rho
      density rootCandidate n hn state z e) :
    ReindexedAppendixStepData
      (onlineOwnerBatchForest F assign e n hn) G
      (fun i ↦ extendedRootImage state.rootImage n hn z
        (onlineFiberOwner F assign e
          (OrderedBranchForest.selectedEquiv
            (onlineOwnerBatch F assign e n hn) i)))
      (whole e)
      (fun c ↦ endpoint e c \
        (reparentedEdgeState F G assign endpoint rootCandidate n hn state z e
          |>.used c))
      (rho e) (density e) where
  sideEquiv := D.sideEquiv
  data := {
    parent := z
    small := D.small
    rootMargin := D.rootMargin
    sideMargin := D.sideMargin
    gamma := D.gamma
    epsilon := D.epsilon
    N := D.N
    common_parent := by
      intro i
      have howner :
          onlineFiberOwner F assign e
              (OrderedBranchForest.selectedEquiv
                (onlineOwnerBatch F assign e n hn) i) = ⟨n, hn⟩ := by
        change F.owner (onlineOwnerBatchBranch F assign e n hn i) = ⟨n, hn⟩
        exact onlineOwnerBatchBranch_owner F assign e n hn i
      rw [howner, extendedRootImage_current]
    numeric := D.numeric
    uniform := D.uniform
    live_subset := D.live_subset
    whole_disjoint := D.whole_disjoint
    density_lower := D.density_lower
    factor_nonneg := D.factor_nonneg
    epsilonN_nonneg := D.epsilonN_nonneg
    regular_root := D.regular_root
    regular_interior := D.regular_interior
    component_margin := D.component_margin
  }

end ReindexedAppendixOnlineOwnerEdgeFacts

end Erdos547b.ZhaoLemma58GlobalAppendixOnlineSuccessor

#print axioms Erdos547b.ZhaoLemma58GlobalAppendixOnlineSuccessor.AppendixOnlineOwnerEdgeFacts.toAppendixStepData
#print axioms Erdos547b.ZhaoLemma58GlobalAppendixOnlineSuccessor.ReindexedAppendixOnlineOwnerEdgeFacts.toReindexedAppendixStepData
#print axioms Erdos547b.ZhaoLemma58GlobalAppendixOnlineSuccessor.reindexedAppendixOnlineOwnerEdgeFactsOfSymmetricBounds
#print axioms Erdos547b.ZhaoLemma58GlobalAppendixOnlineSuccessor.card_liveRootPool_ge_of_two_stage_bounds
