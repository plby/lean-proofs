/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.Lemma58OwnerLocalStep
import ErdosProblems.Erdos547b.Lemma54ThresholdSourceNumerics

/-!
# Residual host capacities for Zhao Lemma 5.4(1)/(2)

This is the graph-side bookkeeping complementary to
`Lemma54ThresholdSourceNumerics`.  The live sides are the literal whole
matching endpoints after deleting the images of earlier owner batches.
From their exact deletion loads, one total-capacity inequality, and the
literal endpoint-eligibility degree bound, the file derives the three live
host fields required by `ActualThresholdStepData`.

The public constructor contains no embedding, copy, continuation, or
result-valued premise.  The only facts still expected from the rich matching
allocator are the paper's scalar packing inequality and endpoint eligibility
for the already chosen outer-root image.
-/

open scoped SimpleGraph

noncomputable section

namespace Erdos547b.ZhaoLemma58ThresholdResidualCapacity

open Finset Fintype SimpleGraph
open Erdos547b.RegularPair
open Erdos547b.ZhaoLemma58GroupedSmallForest
open Erdos547b.ZhaoLemma58OwnerLocalStep
open Erdos547b.ZhaoLemma54ThresholdNumerics
open Erdos547b.ZhaoLemma54ThresholdSourceNumerics

universe v

/-- Literal live endpoint after deleting all images of earlier batches. -/
def residualSide {B : Type v} [DecidableEq B]
    (whole deleted : Fin 2 → Finset B) (c : Fin 2) : Finset B :=
  whole c \ deleted c

theorem residualSide_subset {B : Type v} [DecidableEq B]
    (whole deleted : Fin 2 → Finset B) (c : Fin 2) :
    residualSide whole deleted c ⊆ whole c :=
  Finset.sdiff_subset

/-- If the whole endpoint has enough neighbours to pay for the literal
deleted set and a requested remainder, then the residual endpoint contains
that many neighbours.  Unlike `ResidualThresholdHostFacts.parent_neighbours`,
this pointwise form can be applied only to the endpoint selected by Zhao's
canonical maximal-cutoff orientation. -/
theorem residualSide_filter_card_ge_of_deleted_card_add_le
    {B : Type v} [Fintype B] [DecidableEq B]
    (G : SimpleGraph B) [DecidableRel G.Adj]
    (whole deleted : Fin 2 → Finset B)
    (parent : B) (c : Fin 2) (need : ℕ)
    (hbound : #(deleted c) + need ≤
      #((whole c).filter (G.Adj parent))) :
    need ≤ #((residualSide whole deleted c).filter (G.Adj parent)) := by
  let wholeNeighbors := (whole c).filter (G.Adj parent)
  let liveNeighbors :=
    (residualSide whole deleted c).filter (G.Adj parent)
  have hcover : wholeNeighbors ⊆ liveNeighbors ∪ deleted c := by
    intro x hx
    have hxWhole : x ∈ whole c := (Finset.mem_filter.mp hx).1
    have hxAdj : G.Adj parent x := (Finset.mem_filter.mp hx).2
    by_cases hxDeleted : x ∈ deleted c
    · exact Finset.mem_union_right _ hxDeleted
    · apply Finset.mem_union_left
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_sdiff.mpr ⟨hxWhole, hxDeleted⟩, hxAdj⟩
  have hcoverCard : #wholeNeighbors ≤ #liveNeighbors + #(deleted c) :=
    (Finset.card_le_card hcover).trans (Finset.card_union_le _ _)
  dsimp only [wholeNeighbors, liveNeighbors] at hbound hcoverCard ⊢
  omega

/-- The load needed before the next root on physical side `c`. -/
def thresholdNeed (lowBudget highBudget : ℕ) (lowSide c : Fin 2) : ℕ :=
  if c = lowSide then lowBudget else highBudget

/-- Raw host inputs which survive the matching/source-density specialization.
`prefixLoad` is not a free loss estimate: `deleted_card` identifies it with
the exact number of already used host vertices. -/
structure ResidualThresholdHostFacts
    {b : ℕ} {B : Type v} [Fintype B] [DecidableEq B]
    (F : OrderedRootedForest b) (G : SimpleGraph B) [DecidableRel G.Adj]
    (externalParent : Fin b → B)
    (whole deleted : Fin 2 → Finset B)
    (rho density : ℝ)
    (lowBudget highBudget : ℕ) (lowSide : Fin 2) where
  prefixLoad : Fin 2 → ℕ
  deleted_subset : ∀ c, deleted c ⊆ whole c
  deleted_card : ∀ c, #(deleted c) = prefixLoad c
  /-- Completed batches plus the current high budget and regularity reserve
  fit in each whole endpoint. -/
  total_capacity : ∀ c,
    prefixLoad c + highBudget + thresholdReserve rho #(whole c) ≤ #(whole c)
  /-- Eligibility of an outer-root image for this owner batch, stated in the
  whole endpoint before deleting the known prefix. -/
  endpoint_eligible : ∀ i c,
    prefixLoad c +
        (1 + thresholdReserve rho #(whole c) +
          thresholdNeed lowBudget highBudget lowSide c) ≤
      #((whole c).filter (G.Adj (externalParent i)))
  /-- The scalar regular-pair margin after charging the exact previous load
  and the current high budget. -/
  component_capacity : ∀ i c,
    (F.size i : ℝ) + rho * (#(whole c) : ℝ) + 1 ≤
      (density - rho) *
        ((#(whole c) : ℝ) - prefixLoad c - highBudget)

namespace ResidualThresholdHostFacts

theorem live_card
    {b : ℕ} {B : Type v} [Fintype B] [DecidableEq B]
    {F : OrderedRootedForest b} {G : SimpleGraph B} [DecidableRel G.Adj]
    {externalParent : Fin b → B}
    {whole deleted : Fin 2 → Finset B}
    {rho density : ℝ} {lowBudget highBudget : ℕ} {lowSide : Fin 2}
    (H : ResidualThresholdHostFacts F G externalParent whole deleted
      rho density lowBudget highBudget lowSide) (c : Fin 2) :
    #(residualSide whole deleted c) = #(whole c) - H.prefixLoad c := by
  rw [residualSide, Finset.card_sdiff_of_subset (H.deleted_subset c),
    H.deleted_card]

theorem live_capacity
    {b : ℕ} {B : Type v} [Fintype B] [DecidableEq B]
    {F : OrderedRootedForest b} {G : SimpleGraph B} [DecidableRel G.Adj]
    {externalParent : Fin b → B}
    {whole deleted : Fin 2 → Finset B}
    {rho density : ℝ} {lowBudget highBudget : ℕ} {lowSide : Fin 2}
    (H : ResidualThresholdHostFacts F G externalParent whole deleted
      rho density lowBudget highBudget lowSide) (c : Fin 2) :
    highBudget + thresholdReserve rho #(whole c) ≤
      #(residualSide whole deleted c) := by
  rw [H.live_card c]
  have := H.total_capacity c
  omega

/-- Deleting `prefixLoad` vertices loses at most `prefixLoad` neighbors of
any fixed parent. -/
theorem parent_neighbours
    {b : ℕ} {B : Type v} [Fintype B] [DecidableEq B]
    {F : OrderedRootedForest b} {G : SimpleGraph B} [DecidableRel G.Adj]
    {externalParent : Fin b → B}
    {whole deleted : Fin 2 → Finset B}
    {rho density : ℝ} {lowBudget highBudget : ℕ} {lowSide : Fin 2}
    (H : ResidualThresholdHostFacts F G externalParent whole deleted
      rho density lowBudget highBudget lowSide) (i : Fin b) (c : Fin 2) :
    1 + thresholdReserve rho #(whole c) +
        thresholdNeed lowBudget highBudget lowSide c ≤
      #((residualSide whole deleted c).filter (G.Adj (externalParent i))) := by
  let wholeNeighbors := (whole c).filter (G.Adj (externalParent i))
  let liveNeighbors :=
    (residualSide whole deleted c).filter (G.Adj (externalParent i))
  have hcover : wholeNeighbors ⊆ liveNeighbors ∪ deleted c := by
    intro x hx
    have hxWhole : x ∈ whole c := (Finset.mem_filter.mp hx).1
    have hxAdj : G.Adj (externalParent i) x := (Finset.mem_filter.mp hx).2
    by_cases hxDeleted : x ∈ deleted c
    · exact Finset.mem_union_right _ hxDeleted
    · apply Finset.mem_union_left
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_sdiff.mpr ⟨hxWhole, hxDeleted⟩, hxAdj⟩
  have hcoverCard : #wholeNeighbors ≤ #liveNeighbors + #(deleted c) :=
    (Finset.card_le_card hcover).trans (Finset.card_union_le _ _)
  have heligible := H.endpoint_eligible i c
  rw [H.deleted_card c] at hcoverCard
  dsimp only [wholeNeighbors, liveNeighbors] at heligible hcoverCard ⊢
  omega

theorem component_margin
    {b : ℕ} {B : Type v} [Fintype B] [DecidableEq B]
    {F : OrderedRootedForest b} {G : SimpleGraph B} [DecidableRel G.Adj]
    {externalParent : Fin b → B}
    {whole deleted : Fin 2 → Finset B}
    {rho density : ℝ} {lowBudget highBudget : ℕ} {lowSide : Fin 2}
    (H : ResidualThresholdHostFacts F G externalParent whole deleted
      rho density lowBudget highBudget lowSide) (i : Fin b) (c : Fin 2) :
    (F.size i : ℝ) + rho * (#(whole c) : ℝ) + 1 ≤
      (density - rho) *
        ((#(residualSide whole deleted c) : ℝ) - highBudget) := by
  have hprefix : H.prefixLoad c ≤ #(whole c) := by
    have := H.total_capacity c
    omega
  have hliveReal : (#(residualSide whole deleted c) : ℝ) =
      (#(whole c) : ℝ) - H.prefixLoad c := by
    rw [H.live_card c, Nat.cast_sub hprefix]
  rw [hliveReal]
  exact H.component_capacity i c

end ResidualThresholdHostFacts

/-! ## Full `ActualThresholdStepData` constructor -/

/-- Combine the source-only maximal-cutoff theorem with the literal residual
host bookkeeping.  This removes `live_capacity`, `parent_neighbours`, and
`component_margin` from the caller boundary simultaneously. -/
noncomputable def actualThresholdStepDataOfResidual
    {b : ℕ} {B : Type v} [Fintype B] [DecidableEq B]
    (F : OrderedRootedForest b) (G : SimpleGraph B) [DecidableRel G.Adj]
    (externalParent : Fin b → B)
    (whole deleted : Fin 2 → Finset B)
    (rho density ratio dx dy gamma epsilon N : ℝ) (slack : ℕ)
    (lowSide highSide : Fin 2)
    (Dsource : ClassifiedThresholdOwnerNumerics
      F ratio dx dy gamma epsilon N slack)
    (hsides : highSide ≠ lowSide)
    (hunif : G.IsUniform rho (whole 0) (whole 1))
    (hwholeDisjoint : Disjoint (whole 0) (whole 1))
    (hdensity : density ≤ G.edgeDensity (whole 0) (whole 1))
    (hfactor : 0 ≤ density - rho)
    (Hhost : ResidualThresholdHostFacts F G externalParent whole deleted
      rho density (thresholdLowBudget dx gamma N)
        (thresholdHighBudget dy gamma N) lowSide) :
    ActualThresholdStepData F G externalParent whole
      (residualSide whole deleted) rho density :=
  { slack := slack
    lowBudget := thresholdLowBudget dx gamma N
    highBudget := thresholdHighBudget dy gamma N
    lowSide := lowSide
    highSide := highSide
    reserve := fun c ↦ thresholdReserve rho #(whole c)
    small := Dsource.small
    sides_ne := hsides
    suffix_display := Dsource.suffix_display highSide
    low_le_high := Dsource.lowBudget_le_highBudget
    uniform := hunif
    live_subset := residualSide_subset whole deleted
    whole_disjoint := hwholeDisjoint
    density_lower := hdensity
    factor_nonneg := hfactor
    reserve_regular := fun c ↦ thresholdReserve_covers rho #(whole c)
    live_capacity := Hhost.live_capacity
    parent_neighbours := by
      intro base hbase O i
      let c := branchRootSide F O.orient i
      have hpref := O.prefix_root_le Dsource.lowBudget_le_highBudget i
      exact (Nat.add_le_add_left hpref
        (1 + thresholdReserve rho #(whole c))).trans
          (Hhost.parent_neighbours i c)
    component_margin := Hhost.component_margin }

#print axioms ResidualThresholdHostFacts.live_capacity
#print axioms ResidualThresholdHostFacts.parent_neighbours
#print axioms ResidualThresholdHostFacts.component_margin
#print axioms residualSide_filter_card_ge_of_deleted_card_add_le
#print axioms actualThresholdStepDataOfResidual

end Erdos547b.ZhaoLemma58ThresholdResidualCapacity
