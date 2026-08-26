/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.Lemma58ChosenOwnerBatches
import ErdosProblems.Erdos547b.Lemma58ThresholdGroupEmbedding
import ErdosProblems.Erdos547b.Lemma58PartThreeEmbedding
import ErdosProblems.Erdos547b.Lemma58FixedThresholdGroupEmbedding

/-!
# No-result-premise local owner steps for Zhao Lemma 5.8

This is the concrete boundary consumed by the chosen-orientation owner
recursion.  A local step is either:

* Parts 1/2: the actual maximal-fitting threshold constructor, with its
  source suffix display and live parent-neighbour cardinalities; or
* Part 3: the fixed-parent Appendix A.2/A.1 constructor, using the literal
  current neighbourhoods of that parent as its two root pools.

Both records contain only source inequalities, uniform-pair facts, and
cardinality/adjacency facts about the current live sets.  Their `realize`
theorems call the already proved concrete constructors.  In particular no
embedding, copy, containment, or continuation conclusion is a record field.
-/

open scoped SimpleGraph
noncomputable section

namespace Erdos547b.ZhaoLemma58OwnerLocalStep

open Finset Fintype SimpleGraph
open Erdos547b.RegularPair
open Erdos547b.ZhaoLemma58GroupedSmallForest
open Erdos547b.ZhaoLemma54ThresholdOrientation
open Erdos547b.ZhaoLemma54ThresholdNumerics
open Erdos547b.ZhaoLemma54CanonicalThresholdOrientation
open Erdos547b.ZhaoLemma54AppendixA
open Erdos547b.ZhaoLemma58ThresholdGroupEmbedding
open Erdos547b.ZhaoLemma58FixedThresholdGroupEmbedding
open Erdos547b.ZhaoLemma58PartThreeEmbedding
open Erdos547b.ZhaoLemma58DynamicBatchAppend
open Erdos547b.ZhaoLemma58ChosenOwnerBatches

universe v

/-- The literal live neighbours of one already embedded outer root on a
physical matching side. -/
def currentRootPool {B : Type v} [Fintype B] [DecidableEq B]
    (G : SimpleGraph B) [DecidableRel G.Adj] (parent : B)
    (live : Fin 2 → Finset B) (c : Fin 2) : Finset B :=
  (live c).filter (G.Adj parent)

@[simp] theorem mem_currentRootPool
    {B : Type v} [Fintype B] [DecidableEq B]
    (G : SimpleGraph B) [DecidableRel G.Adj] (parent : B)
    (live : Fin 2 → Finset B) (c : Fin 2) (w : B) :
    w ∈ currentRootPool G parent live c ↔
      w ∈ live c ∧ G.Adj parent w := by
  simp [currentRootPool]

/-- Primitive source and live-host facts for a Parts-1/2 owner step. -/
structure ActualThresholdStepData
    {b : ℕ} {B : Type v} [Fintype B] [DecidableEq B]
    (F : OrderedRootedForest b) (G : SimpleGraph B) [DecidableRel G.Adj]
    (externalParent : Fin b → B)
    (whole live : Fin 2 → Finset B)
    (rho density : ℝ) where
  slack : ℕ
  lowBudget : ℕ
  highBudget : ℕ
  lowSide : Fin 2
  highSide : Fin 2
  reserve : Fin 2 → ℕ
  small : ∀ i, F.size i ≤ slack
  sides_ne : highSide ≠ lowSide
  suffix_display : ∀ (base : Fin b → Fin 2 ≃ Fin 2),
    (∀ t c, 2 * sideLoadPrefix F base t c ≤ prefixOrder F t + slack) →
    ∀ c,
      lowBudget + fixedSuffixLoad F
          (maximalFittingCutoff F base lowBudget) highSide c ≤
        highBudget
  low_le_high : lowBudget ≤ highBudget
  uniform : G.IsUniform rho (whole 0) (whole 1)
  live_subset : ∀ c, live c ⊆ whole c
  whole_disjoint : Disjoint (whole 0) (whole 1)
  density_lower : density ≤ G.edgeDensity (whole 0) (whole 1)
  factor_nonneg : 0 ≤ density - rho
  reserve_regular : ∀ c, rho * (#(whole c) : ℝ) ≤ reserve c
  live_capacity : ∀ c, highBudget + reserve c ≤ #(live c)
  /-- Only the endpoint which actually receives the branch root needs a
  parent-neighbour bound.  In particular, a zero-density low endpoint is
  harmless when the maximal fitting cutoff is empty. -/
  parent_neighbours : ∀ (base : Fin b → Fin 2 ≃ Fin 2)
      (hbase : ∀ t c,
        2 * sideLoadPrefix F base t c ≤ prefixOrder F t + slack),
    let O := actualThresholdSwitchOrientation F slack lowBudget highBudget
      lowSide highSide small sides_ne suffix_display base hbase
    ∀ i,
      1 + reserve (branchRootSide F O.orient i) +
          sideLoadBefore F O.orient i (branchRootSide F O.orient i) ≤
        #((live (branchRootSide F O.orient i)).filter
          (G.Adj (externalParent i)))
  component_margin : ∀ i c,
    (F.size i : ℝ) + rho * (#(whole c) : ℝ) + 1 ≤
      (density - rho) * ((#(live c) : ℝ) - highBudget)

/-- The actual Parts-1/2 local constructor. -/
theorem ActualThresholdStepData.realize
    {b : ℕ} {B : Type v} [Fintype B] [DecidableEq B]
    (F : OrderedRootedForest b) (G : SimpleGraph B) [DecidableRel G.Adj]
    (externalParent : Fin b → B)
    (whole live : Fin 2 → Finset B)
    (rho density : ℝ)
    (D : ActualThresholdStepData
      F G externalParent whole live rho density) :
    ∃ orient : Fin b → Fin 2 ≃ Fin 2,
      Nonempty (DynamicAttachedForestEmbedding
        F G externalParent orient live) := by
  exact exists_actualThresholdDynamicGroupEmbedding_of_actualParent
    F D.slack D.lowBudget
    D.highBudget D.lowSide D.highSide D.small D.sides_ne D.suffix_display
    G externalParent whole live D.reserve rho density D.low_le_high D.uniform
    D.live_subset D.whole_disjoint D.density_lower D.factor_nonneg
    D.reserve_regular D.live_capacity D.parent_neighbours D.component_margin

/-- Primitive source and live-host facts for one owner-coherent Part-3 step.
The root pools are definitionally the current live neighbourhoods of
`parent`, rather than arbitrary caller-supplied subsets. -/
structure AppendixStepData
    {b : ℕ} {B : Type v} [Fintype B] [DecidableEq B]
    (F : OrderedRootedForest b) (G : SimpleGraph B) [DecidableRel G.Adj]
    (externalParent : Fin b → B)
    (whole live : Fin 2 → Finset B)
    (rho density : ℝ) where
  parent : B
  small : ℕ
  rootMargin : ℕ
  sideMargin : ℕ
  gamma : ℝ
  epsilon : ℝ
  N : ℝ
  common_parent : ∀ i, externalParent i = parent
  numeric : AppendixA2NumericData F small rootMargin sideMargin
    #(live 0) #(live 1)
    #(currentRootPool G parent live 0)
    #(currentRootPool G parent live 1) gamma epsilon N
  uniform : G.IsUniform rho (whole 0) (whole 1)
  live_subset : ∀ c, live c ⊆ whole c
  whole_disjoint : Disjoint (whole 0) (whole 1)
  density_lower : density ≤ G.edgeDensity (whole 0) (whole 1)
  factor_nonneg : 0 ≤ density - rho
  epsilonN_nonneg : 0 ≤ epsilon * N
  regular_root : ∀ c,
    rho * (#(whole c) : ℝ) < 3 * epsilon * N
  regular_interior : ∀ c,
    rho * (#(whole c) : ℝ) ≤ gamma * N
  component_margin : ∀ i c,
    (F.size i : ℝ) + rho * (#(whole c) : ℝ) ≤
      (density - rho) * (gamma * N)

/-- The actual Part-3 local constructor. -/
theorem AppendixStepData.realize
    {b : ℕ} {B : Type v} [Fintype B] [DecidableEq B]
    (F : OrderedRootedForest b) (G : SimpleGraph B) [DecidableRel G.Adj]
    (externalParent : Fin b → B)
    (whole live : Fin 2 → Finset B)
    (rho density : ℝ)
    (D : AppendixStepData F G externalParent whole live rho density) :
    ∃ orient : Fin b → Fin 2 ≃ Fin 2,
      Nonempty (DynamicAttachedForestEmbedding
        F G externalParent orient live) := by
  have hrootSubset (c : Fin 2) :
      currentRootPool G D.parent live c ⊆ live c :=
    Finset.filter_subset _ _
  have hattach (c : Fin 2) (w : B)
      (hw : w ∈ currentRootPool G D.parent live c) : G.Adj D.parent w :=
    (mem_currentRootPool G D.parent live c w).mp hw |>.2
  obtain ⟨E⟩ := exists_partThreeDynamicGroupEmbedding F D.small D.rootMargin
    D.sideMargin G D.parent whole live (currentRootPool G D.parent live)
    rho density D.gamma D.epsilon D.N D.numeric D.uniform D.live_subset
    hrootSubset D.whole_disjoint D.density_lower D.factor_nonneg
    D.epsilonN_nonneg D.regular_root D.regular_interior D.component_margin
    hattach
  let Eactual : DynamicAttachedForestEmbedding F G externalParent
      E.orient live := {
    embedding := E.embedding.embedding
    attach := by
      intro i
      rw [D.common_parent i]
      exact E.embedding.attach i
    map_side := E.embedding.map_side
  }
  exact ⟨E.orient, ⟨Eactual⟩⟩

/-- Primitive source and live-host facts for a batch whose orientation was
fixed by one global edge-level Part-1/2 calculation.  This is the form used
when owner batches are realized successively: the balancing slack is paid by
the global orientation, not once again for every owner. -/
structure FixedOrientationStepData
    {b : ℕ} {B : Type v} [Fintype B] [DecidableEq B]
    (F : OrderedRootedForest b) (G : SimpleGraph B) [DecidableRel G.Adj]
    (externalParent : Fin b → B)
    (orient : Fin b → Fin 2 ≃ Fin 2)
    (whole live : Fin 2 → Finset B)
    (rho density : ℝ) where
  reserve : Fin 2 → ℕ
  uniform : G.IsUniform rho (whole 0) (whole 1)
  live_subset : ∀ c, live c ⊆ whole c
  whole_disjoint : Disjoint (whole 0) (whole 1)
  density_lower : density ≤ G.edgeDensity (whole 0) (whole 1)
  factor_nonneg : 0 ≤ density - rho
  reserve_regular : ∀ c, rho * (#(whole c) : ℝ) ≤ reserve c
  live_capacity : ∀ c,
    sideLoad F orient c + reserve c ≤ #(live c)
  parent_neighbours : ∀ i,
    1 + reserve (branchRootSide F orient i) +
        sideLoadBefore F orient i (branchRootSide F orient i) ≤
      #((live (branchRootSide F orient i)).filter
        (G.Adj (externalParent i)))
  component_margin : ∀ i c,
    (F.size i : ℝ) + rho * (#(whole c) : ℝ) + 1 ≤
      (density - rho) * ((#(live c) : ℝ) - sideLoad F orient c)

/-- Realize a globally fixed orientation in the literal current residual
sets. -/
theorem FixedOrientationStepData.realize
    {b : ℕ} {B : Type v} [Fintype B] [DecidableEq B]
    (F : OrderedRootedForest b) (G : SimpleGraph B) [DecidableRel G.Adj]
    (externalParent : Fin b → B)
    (orient : Fin b → Fin 2 ≃ Fin 2)
    (whole live : Fin 2 → Finset B)
    (rho density : ℝ)
    (D : FixedOrientationStepData F G externalParent orient whole live rho
      density) :
    Nonempty (DynamicAttachedForestEmbedding
      F G externalParent orient live) := by
  exact exists_dynamic_ordered_forest_embedding_of_uniform F G externalParent
    orient whole live D.reserve rho density D.uniform D.live_subset
    D.whole_disjoint D.density_lower D.factor_nonneg D.reserve_regular
    D.live_capacity D.parent_neighbours D.component_margin

/-- Appendix source data after an arbitrary reindexing of the two physical
endpoints.  This lets the A.2 numeric theorem name the smaller current live
side first, without imposing a permanent ordering on residual endpoint
cardinalities. -/
structure ReindexedAppendixStepData
    {b : ℕ} {B : Type v} [Fintype B] [DecidableEq B]
    (F : OrderedRootedForest b) (G : SimpleGraph B) [DecidableRel G.Adj]
    (externalParent : Fin b → B)
    (whole live : Fin 2 → Finset B)
    (rho density : ℝ) : Type (max 0 v) where
  sideEquiv : Fin 2 ≃ Fin 2
  data : AppendixStepData F G externalParent
    (fun c ↦ whole (sideEquiv c)) (fun c ↦ live (sideEquiv c)) rho density

/-- Reindex an Appendix realization back to the literal physical endpoints. -/
theorem ReindexedAppendixStepData.realize
    {b : ℕ} {B : Type v} [Fintype B] [DecidableEq B]
    (F : OrderedRootedForest b) (G : SimpleGraph B) [DecidableRel G.Adj]
    (externalParent : Fin b → B)
    (whole live : Fin 2 → Finset B)
    (rho density : ℝ)
    (D : ReindexedAppendixStepData F G externalParent whole live rho density) :
    ∃ orient : Fin b → Fin 2 ≃ Fin 2,
      Nonempty (DynamicAttachedForestEmbedding
        F G externalParent orient live) := by
  obtain ⟨orient0, ⟨E⟩⟩ := D.data.realize F G externalParent
    (fun c ↦ whole (D.sideEquiv c)) (fun c ↦ live (D.sideEquiv c)) rho density
  let orient : Fin b → Fin 2 ≃ Fin 2 := fun i ↦
    (orient0 i).trans D.sideEquiv
  refine ⟨orient, ⟨{
    embedding := E.embedding
    attach := E.attach
    map_side := ?_
  }⟩⟩
  intro i a
  simpa only [orient, Equiv.trans_apply] using E.map_side i a

/-- Vacuous source data for an owner/edge batch containing no components.
Keeping this as an explicit local case avoids imposing regular-pair or root
degree hypotheses on physical edges unused by the current owner. -/
structure EmptyStepData
    {b : ℕ} (F : OrderedRootedForest b) : Prop where
  card_eq_zero : b = 0

/-- The canonical vacuous orientation of an empty owner batch. -/
noncomputable def EmptyStepData.orientation
    {b : ℕ} {F : OrderedRootedForest b} (D : EmptyStepData F) :
    Fin b → Fin 2 ≃ Fin 2 := by
  intro i
  exfalso
  have hi := i.isLt
  have hb := D.card_eq_zero
  omega

/-- An empty owner batch has a concrete attached forest embedding without
any host-side premise. -/
theorem EmptyStepData.realize
    {b : ℕ} {B : Type v} [Fintype B] [DecidableEq B]
    (F : OrderedRootedForest b) (G : SimpleGraph B)
    (externalParent : Fin b → B) (live : Fin 2 → Finset B)
    (D : EmptyStepData F) :
    Nonempty (DynamicAttachedForestEmbedding F G externalParent
      D.orientation live) := by
  have hempty (i : Fin b) : False := by
    have hi := i.isLt
    have hb := D.card_eq_zero
    omega
  let copies : ∀ i, (F.tree i).Copy G := fun i ↦ False.elim (hempty i)
  have hinjective : Function.Injective
      (fun z : Σ i, Fin (F.size i) ↦ copies z.1 z.2) := by
    rintro ⟨i, a⟩
    exact False.elim (hempty i)
  exact ⟨{
    embedding := ⟨copies, hinjective⟩
    attach := fun i ↦ False.elim (hempty i)
    map_side := fun i ↦ False.elim (hempty i)
  }⟩

/-- The genuine local cases in Zhao Lemma 5.4.  `fixed` is the continuation
form of Parts 1/2 after the edge-level orientation has already been chosen. -/
inductive OwnerLocalStepData
    {b : ℕ} {B : Type v} [Fintype B] [DecidableEq B]
    (F : OrderedRootedForest b) (G : SimpleGraph B) [DecidableRel G.Adj]
    (externalParent : Fin b → B)
    (whole live : Fin 2 → Finset B)
    (rho density : ℝ) : Type (max 0 v)
  | threshold : ActualThresholdStepData
      F G externalParent whole live rho density → OwnerLocalStepData
      F G externalParent whole live rho density
  | appendix : AppendixStepData
      F G externalParent whole live rho density → OwnerLocalStepData
      F G externalParent whole live rho density
  | reindexedAppendix : ReindexedAppendixStepData
      F G externalParent whole live rho density → OwnerLocalStepData
      F G externalParent whole live rho density
  | empty : EmptyStepData F → OwnerLocalStepData
      F G externalParent whole live rho density
  | fixed {orient : Fin b → Fin 2 ≃ Fin 2} : FixedOrientationStepData
      F G externalParent orient whole live rho density → OwnerLocalStepData
      F G externalParent whole live rho density

/-- Deterministic orientation carried by a local source datum.  Threshold
steps use the canonical prefix-balanced/maximal-cutoff orientation; Appendix
steps retain the orientation chosen by A.2; fixed continuations use their
supplied global orientation. -/
noncomputable def OwnerLocalStepData.orientation
    {b : ℕ} {B : Type v} [Fintype B] [DecidableEq B]
    (F : OrderedRootedForest b) (G : SimpleGraph B) [DecidableRel G.Adj]
    (externalParent : Fin b → B)
    (whole live : Fin 2 → Finset B)
    (rho density : ℝ)
    (D : OwnerLocalStepData F G externalParent whole live rho density) :
    Fin b → Fin 2 ≃ Fin 2 := by
  cases D with
  | threshold D =>
      exact (canonicalActualThresholdSwitchOrientation F D.slack D.lowBudget
        D.highBudget D.lowSide D.highSide D.small D.sides_ne
        D.suffix_display).orient
  | appendix D =>
      exact Classical.choose (D.realize F G externalParent whole live rho
        density)
  | reindexedAppendix D =>
      exact Classical.choose (D.realize F G externalParent whole live rho
        density)
  | empty D => exact D.orientation
  | @fixed orient D => exact orient

/-- Realize exactly the deterministic orientation of a local datum. -/
theorem OwnerLocalStepData.realize_orientation
    {b : ℕ} {B : Type v} [Fintype B] [DecidableEq B]
    (F : OrderedRootedForest b) (G : SimpleGraph B) [DecidableRel G.Adj]
    (externalParent : Fin b → B)
    (whole live : Fin 2 → Finset B)
    (rho density : ℝ)
    (D : OwnerLocalStepData F G externalParent whole live rho density) :
    Nonempty (DynamicAttachedForestEmbedding F G externalParent
      (D.orientation F G externalParent whole live rho density) live) := by
  cases D with
  | threshold D =>
      exact exists_canonicalActualThresholdDynamicGroupEmbedding F D.slack
        D.lowBudget D.highBudget D.lowSide D.highSide D.small D.sides_ne
        D.suffix_display G externalParent whole live D.reserve rho density
        D.low_le_high D.uniform D.live_subset D.whole_disjoint D.density_lower
        D.factor_nonneg D.reserve_regular D.live_capacity
        (by
          intro i
          exact D.parent_neighbours
            (canonicalPrefixBalancedOrientation F D.slack D.small)
            (canonicalPrefixBalancedOrientation_spec F D.slack D.small) i)
        D.component_margin
  | appendix D =>
      exact Classical.choose_spec
        (D.realize F G externalParent whole live rho density)
  | reindexedAppendix D =>
      exact Classical.choose_spec
        (D.realize F G externalParent whole live rho density)
  | empty D => exact D.realize F G externalParent live
  | @fixed orient D =>
      change Nonempty
        (DynamicAttachedForestEmbedding F G externalParent orient live)
      exact D.realize F G externalParent orient whole live rho density

theorem OwnerLocalStepData.realize
    {b : ℕ} {B : Type v} [Fintype B] [DecidableEq B]
    (F : OrderedRootedForest b) (G : SimpleGraph B) [DecidableRel G.Adj]
    (externalParent : Fin b → B)
    (whole live : Fin 2 → Finset B)
    (rho density : ℝ)
    (D : OwnerLocalStepData F G externalParent whole live rho density) :
    ∃ orient : Fin b → Fin 2 ≃ Fin 2,
      Nonempty (DynamicAttachedForestEmbedding
        F G externalParent orient live) := by
  exact ⟨D.orientation F G externalParent whole live rho density,
    D.realize_orientation F G externalParent whole live rho density⟩

/-- Feed concrete threshold/Appendix live facts into the chosen owner
recursion.  The caller supplies no embedding-valued local result. -/
theorem exists_dynamicEmbedding_of_ownerLocalSteps
    {b r : ℕ} {B : Type v} [Fintype B] [DecidableEq B]
    (F : OrderedRootedForest b) (G : SimpleGraph B) [DecidableRel G.Adj]
    (externalParent : Fin b → B)
    (whole available : Fin 2 → Finset B)
    (havailable : ∀ c, available c ⊆ whole c)
    (hwholeDisjoint : Disjoint (whole 0) (whole 1))
    (owner : Fin b → Fin r) (rho density : ℝ)
    (hdata : ∀ n (hn : n < r)
      (Eprefix : ChosenPartialDynamicEmbedding F G externalParent available
        (ownerPrefix Finset.univ owner n)),
      Nonempty (OwnerLocalStepData
        (selectedForest F (ownerBatch Finset.univ owner ⟨n, hn⟩)) G
        (fun k ↦ externalParent
          (Erdos547b.ZhaoClaim616SourceBridge.OrderedBranchForest.selectedEquiv
            (ownerBatch Finset.univ owner ⟨n, hn⟩) k))
        whole (fun c ↦ available c \ Eprefix.used c) rho density)) :
    ∃ orient : Fin b → Fin 2 ≃ Fin 2,
      Nonempty (DynamicAttachedForestEmbedding
        F G externalParent orient available) := by
  apply exists_dynamicAttachedForestEmbedding_of_chosenOwnerBatches
    F G externalParent whole available havailable hwholeDisjoint owner
  intro n hn Eprefix
  obtain ⟨D⟩ := hdata n hn Eprefix
  exact D.realize
    (selectedForest F (ownerBatch Finset.univ owner ⟨n, hn⟩)) G
    (fun k ↦ externalParent
      (Erdos547b.ZhaoClaim616SourceBridge.OrderedBranchForest.selectedEquiv
        (ownerBatch Finset.univ owner ⟨n, hn⟩) k))
    whole (fun c ↦ available c \ Eprefix.used c) rho density

end Erdos547b.ZhaoLemma58OwnerLocalStep

#print axioms Erdos547b.ZhaoLemma58OwnerLocalStep.ActualThresholdStepData.realize
#print axioms Erdos547b.ZhaoLemma58OwnerLocalStep.AppendixStepData.realize
#print axioms Erdos547b.ZhaoLemma58OwnerLocalStep.ReindexedAppendixStepData.realize
#print axioms Erdos547b.ZhaoLemma58OwnerLocalStep.EmptyStepData.realize
#print axioms Erdos547b.ZhaoLemma58OwnerLocalStep.FixedOrientationStepData.realize
#print axioms Erdos547b.ZhaoLemma58OwnerLocalStep.OwnerLocalStepData.realize_orientation
#print axioms Erdos547b.ZhaoLemma58OwnerLocalStep.exists_dynamicEmbedding_of_ownerLocalSteps
