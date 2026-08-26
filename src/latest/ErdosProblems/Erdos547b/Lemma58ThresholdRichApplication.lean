/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.Lemma58ThresholdResidualCapacity

/-!
# Rich-pair application of the Parts-1/2 threshold step

Parts 1 and 2 of Zhao Lemma 5.4 process the complete group assigned to one
matching edge.  Their dynamic constructor already permits a different
external parent for every branch, so this group must not be split into
owner batches: doing so would charge the full high-density budget once per
owner.  Consequently the Parts-1/2 residual prefix on this edge is empty.

This file specializes the general residual bookkeeping to that exact case.
Endpoint eligibility is the literal statement that every prescribed parent
is outside the regular-pair atypical set.  The only scalar inputs are the
three paper inequalities: high-side capacity, parent-degree need, and the
small-component regular-pair margin.  No embedding, copy, containment, or
continuation is an input.
-/

open scoped SimpleGraph

noncomputable section

namespace Erdos547b.ZhaoLemma58ThresholdRichApplication

open Finset Fintype SimpleGraph
open Erdos547b.RegularPair
open Erdos547b.ZhaoLemma58GroupedSmallForest
open Erdos547b.ZhaoLemma58OwnerLocalStep
open Erdos547b.ZhaoLemma54ThresholdOrientation
open Erdos547b.ZhaoLemma54ThresholdNumerics
open Erdos547b.ZhaoLemma54ThresholdSourceNumerics
open Erdos547b.ZhaoLemma58ThresholdResidualCapacity

universe v

/-- The degree threshold certified by avoiding the canonical atypical set. -/
def typicalDegreeTarget {B : Type v} [Fintype B] [DecidableEq B]
    (G : SimpleGraph B) [DecidableRel G.Adj]
    (rho : ℝ) (rootCluster target : Finset B) : ℝ :=
  (G.edgeDensity rootCluster target - rho) * #target

/-- A parent in `rootCluster` which is not atypical has the literal required
degree into `target`. -/
theorem card_filter_adj_ge_of_not_mem_atypical
    {B : Type v} [Fintype B] [DecidableEq B]
    (G : SimpleGraph B) [DecidableRel G.Adj]
    (rho : ℝ) (rootCluster target : Finset B) (z : B)
    (hz : z ∈ rootCluster)
    (htypical : z ∉ atypicalVertices G rho rootCluster target)
    {need : ℕ}
    (hneed : (need : ℝ) ≤ typicalDegreeTarget G rho rootCluster target) :
    need ≤ #(target.filter (G.Adj z)) := by
  have hdegree : typicalDegreeTarget G rho rootCluster target ≤
      (#(target.filter (G.Adj z)) : ℝ) := by
    simp only [atypicalVertices, Finset.mem_filter, hz, true_and] at htypical
    change ¬((#(target.filter (G.Adj z)) : ℝ) <
      typicalDegreeTarget G rho rootCluster target) at htypical
    exact le_of_not_gt htypical
  exact_mod_cast hneed.trans hdegree

/-- Exact scalar data remaining after source classification and aggregate
typicality have selected the current edge.  The natural budgets and reserve
are the canonical floor/ceiling values, not caller-chosen approximations. -/
structure WholeEdgeThresholdHostNumerics
    {b : ℕ} {B : Type v} [Fintype B] [DecidableEq B]
    (F : OrderedRootedForest b) (G : SimpleGraph B) [DecidableRel G.Adj]
    (externalParent : Fin b → B)
    (rootCluster : Finset B) (whole : Fin 2 → Finset B)
    (rho density dx dy gamma N : ℝ) (lowSide : Fin 2) : Prop where
  parent_mem : ∀ i, externalParent i ∈ rootCluster
  parent_typical : ∀ i c,
    externalParent i ∉ atypicalVertices G rho rootCluster (whole c)
  /-- One matching endpoint retains the full high budget and regularity
  reserve. -/
  high_capacity : ∀ c,
    thresholdHighBudget dy gamma N + thresholdReserve rho #(whole c) ≤
      #(whole c)
  /-- The source-density row dominates the exact next-root requirement. -/
  parent_budget : ∀ (_ : Fin b) (c : Fin 2),
    ((1 + thresholdReserve rho #(whole c) +
        thresholdNeed (thresholdLowBudget dx gamma N)
          (thresholdHighBudget dy gamma N) lowSide c : ℕ) : ℝ) ≤
      typicalDegreeTarget G rho rootCluster (whole c)
  /-- Smallness plus the matching-pair density leaves the dynamic one-tree
  margin after the full high budget is reserved. -/
  component_capacity : ∀ i c,
    (F.size i : ℝ) + rho * (#(whole c) : ℝ) + 1 ≤
      (density - rho) *
        ((#(whole c) : ℝ) - thresholdHighBudget dy gamma N)

namespace WholeEdgeThresholdHostNumerics

/-- The scalar part of a rich edge row.  It is independent of the branch
index: source smallness turns its last field into every component margin. -/
structure ScalarFacts
    {B : Type v} [Fintype B] [DecidableEq B]
    (G : SimpleGraph B) [DecidableRel G.Adj] (rootCluster : Finset B)
    (whole : Fin 2 → Finset B)
    (rho density dx dy gamma N : ℝ) (slack : ℕ)
    (lowSide : Fin 2) : Prop where
  high_capacity : ∀ c,
    thresholdHighBudget dy gamma N + thresholdReserve rho #(whole c) ≤
      #(whole c)
  parent_budget : ∀ c,
    ((1 + thresholdReserve rho #(whole c) +
        thresholdNeed (thresholdLowBudget dx gamma N)
          (thresholdHighBudget dy gamma N) lowSide c : ℕ) : ℝ) ≤
      typicalDegreeTarget G rho rootCluster (whole c)
  small_component_capacity : ∀ c,
    (slack : ℝ) + rho * (#(whole c) : ℝ) + 1 ≤
      (density - rho) *
        ((#(whole c) : ℝ) - thresholdHighBudget dy gamma N)

/-- Existing aggregate typicality (`edgeEligible`) and the scalar rich row
construct all graph/cardinality fields for one whole edge group. -/
theorem of_edgeEligible
    {b k : ℕ} {B : Type v} [Fintype B] [DecidableEq B]
    (F : OrderedRootedForest b) (G : SimpleGraph B) [DecidableRel G.Adj]
    (externalParent : Fin b → B)
    (rootCluster : Finset B) (endpoint : Fin k → Fin 2 → Finset B)
    (e : Fin k) (rho density dx dy gamma N : ℝ) (slack : ℕ)
    (lowSide : Fin 2)
    (hrootMem : ∀ i, externalParent i ∈ rootCluster)
    (heligible : ∀ i, edgeEligible G rho rootCluster endpoint
      (externalParent i) e)
    (hsmall : ∀ i, F.size i ≤ slack)
    (S : ScalarFacts G rootCluster (endpoint e)
      rho density dx dy gamma N slack lowSide) :
    WholeEdgeThresholdHostNumerics F G externalParent rootCluster (endpoint e)
      rho density dx dy gamma N lowSide :=
  { parent_mem := hrootMem
    parent_typical := fun i c ↦ heligible i c
    high_capacity := S.high_capacity
    parent_budget := fun _ c ↦ S.parent_budget c
    component_capacity := by
      intro i c
      have hsmallReal : (F.size i : ℝ) ≤ slack := by
        exact_mod_cast hsmall i
      calc
        (F.size i : ℝ) + rho * (#(endpoint e c) : ℝ) + 1 ≤
            (slack : ℝ) + rho * (#(endpoint e c) : ℝ) + 1 := by
          gcongr
        _ ≤ (density - rho) *
            ((#(endpoint e c) : ℝ) - thresholdHighBudget dy gamma N) :=
          S.small_component_capacity c }

/-- The concrete residual-host record for a whole Parts-1/2 edge group.
There are no prior images on this edge. -/
noncomputable def toResidualThresholdHostFacts
    {b : ℕ} {B : Type v} [Fintype B] [DecidableEq B]
    (F : OrderedRootedForest b) (G : SimpleGraph B) [DecidableRel G.Adj]
    (externalParent : Fin b → B)
    (rootCluster : Finset B) (whole : Fin 2 → Finset B)
    (rho density dx dy gamma N : ℝ) (lowSide : Fin 2)
    (H : WholeEdgeThresholdHostNumerics F G externalParent rootCluster whole
      rho density dx dy gamma N lowSide) :
    ResidualThresholdHostFacts F G externalParent whole (fun _ ↦ ∅)
      rho density (thresholdLowBudget dx gamma N)
        (thresholdHighBudget dy gamma N) lowSide :=
  { prefixLoad := fun _ ↦ 0
    deleted_subset := fun _ ↦ Finset.empty_subset _
    deleted_card := fun _ ↦ Finset.card_empty
    total_capacity := by
      intro c
      simpa only [Nat.zero_add] using H.high_capacity c
    endpoint_eligible := by
      intro i c
      have hdegree := card_filter_adj_ge_of_not_mem_atypical G rho rootCluster
        (whole c) (externalParent i) (H.parent_mem i) (H.parent_typical i c)
        (H.parent_budget i c)
      simpa only [Nat.zero_add] using hdegree
    component_capacity := by
      intro i c
      simpa only [Nat.cast_zero, sub_zero] using H.component_capacity i c }

end WholeEdgeThresholdHostNumerics

/-- A full no-result-premise Parts-1/2 owner-local datum for one assigned
matching edge.  Despite the common output type, this datum represents the
whole edge group; Part 3 alone is subsequently split owner by owner. -/
noncomputable def thresholdOwnerLocalStepDataOfWholeEdge
    {b : ℕ} {B : Type v} [Fintype B] [DecidableEq B]
    (F : OrderedRootedForest b) (G : SimpleGraph B) [DecidableRel G.Adj]
    (externalParent : Fin b → B)
    (rootCluster : Finset B) (whole : Fin 2 → Finset B)
    (rho density ratio dx dy gamma epsilon N : ℝ) (slack : ℕ)
    (lowSide highSide : Fin 2)
    (Dsource : ClassifiedThresholdOwnerNumerics
      F ratio dx dy gamma epsilon N slack)
    (hsides : highSide ≠ lowSide)
    (hunif : G.IsUniform rho (whole 0) (whole 1))
    (hwholeDisjoint : Disjoint (whole 0) (whole 1))
    (hdensity : density ≤ G.edgeDensity (whole 0) (whole 1))
    (hfactor : 0 ≤ density - rho)
    (H : WholeEdgeThresholdHostNumerics F G externalParent rootCluster whole
      rho density dx dy gamma N lowSide) :
    OwnerLocalStepData F G externalParent whole whole rho density := by
  apply OwnerLocalStepData.threshold
  have Hresidual := H.toResidualThresholdHostFacts F G externalParent
    rootCluster whole rho density dx dy gamma N lowSide
  have D := actualThresholdStepDataOfResidual F G externalParent whole
    (fun _ ↦ ∅) rho density ratio dx dy gamma epsilon N slack lowSide
    highSide Dsource hsides hunif hwholeDisjoint hdensity hfactor Hresidual
  have hlive : residualSide whole (fun _ ↦ ∅) = whole := by
    funext c
    exact Finset.sdiff_empty
  rw [hlive] at D
  exact D

/-- Direct existing-API wrapper: a root-image-dependent eligible matching
edge plus the scalar Eventual-parameter inequalities produces the complete
local Parts-1/2 datum. -/
noncomputable def thresholdOwnerLocalStepDataOfEligibleEdge
    {b k : ℕ} {B : Type v} [Fintype B] [DecidableEq B]
    (F : OrderedRootedForest b) (G : SimpleGraph B) [DecidableRel G.Adj]
    (externalParent : Fin b → B)
    (rootCluster : Finset B) (endpoint : Fin k → Fin 2 → Finset B)
    (e : Fin k)
    (rho density ratio dx dy gamma epsilon N : ℝ) (slack : ℕ)
    (lowSide highSide : Fin 2)
    (Dsource : ClassifiedThresholdOwnerNumerics
      F ratio dx dy gamma epsilon N slack)
    (hsides : highSide ≠ lowSide)
    (hrootMem : ∀ i, externalParent i ∈ rootCluster)
    (heligible : ∀ i, edgeEligible G rho rootCluster endpoint
      (externalParent i) e)
    (hunif : G.IsUniform rho (endpoint e 0) (endpoint e 1))
    (hwholeDisjoint : Disjoint (endpoint e 0) (endpoint e 1))
    (hdensity : density ≤ G.edgeDensity (endpoint e 0) (endpoint e 1))
    (hfactor : 0 ≤ density - rho)
    (S : WholeEdgeThresholdHostNumerics.ScalarFacts G rootCluster (endpoint e)
      rho density dx dy gamma N slack lowSide) :
    OwnerLocalStepData F G externalParent (endpoint e) (endpoint e)
      rho density := by
  let H := WholeEdgeThresholdHostNumerics.of_edgeEligible F G externalParent
    rootCluster endpoint e rho density dx dy gamma N slack lowSide hrootMem
    heligible Dsource.small S
  exact thresholdOwnerLocalStepDataOfWholeEdge F G externalParent rootCluster
    (endpoint e) rho density ratio dx dy gamma epsilon N slack lowSide highSide
    Dsource hsides hunif hwholeDisjoint hdensity hfactor H

/-! ## Source-exact canonical-cutoff specialization

The compatibility structures above ask for a parent budget on both physical
endpoints.  That is harmless for balanced rows, but it is stronger than
Zhao's Part-2 argument when the low `A`-density is zero.  The actual maximal
cutoff is then zero and every branch root is sent to the high endpoint.  The
following parallel interface asks for the degree bound only on the endpoint
used by that literal canonical orientation.
-/

/-- Whole-edge host facts with the parent budget tied to the canonical
prefix-balanced base and maximal fitting cutoff. -/
structure CanonicalWholeEdgeThresholdHostNumerics
    {b : ℕ} {B : Type v} [Fintype B] [DecidableEq B]
    (F : OrderedRootedForest b) (G : SimpleGraph B) [DecidableRel G.Adj]
    (externalParent : Fin b → B)
    (rootCluster : Finset B) (whole : Fin 2 → Finset B)
    (rho density ratio dx dy gamma epsilon N : ℝ) (slack : ℕ)
    (lowSide highSide : Fin 2)
    (Dsource : ClassifiedThresholdOwnerNumerics
      F ratio dx dy gamma epsilon N slack)
    (hsides : highSide ≠ lowSide) : Prop where
  parent_mem : ∀ i, externalParent i ∈ rootCluster
  parent_typical : ∀ i c,
    externalParent i ∉ atypicalVertices G rho rootCluster (whole c)
  high_capacity : ∀ c,
    thresholdHighBudget dy gamma N + thresholdReserve rho #(whole c) ≤
      #(whole c)
  parent_budget : ∀ (base : Fin b → Fin 2 ≃ Fin 2)
      (hbase : ∀ t c,
        2 * sideLoadPrefix F base t c ≤ prefixOrder F t + slack) (i : Fin b),
    let O := actualThresholdSwitchOrientation F slack
      (thresholdLowBudget dx gamma N) (thresholdHighBudget dy gamma N)
      lowSide highSide Dsource.small hsides (Dsource.suffix_display highSide)
        base hbase
    let c := branchRootSide F O.orient i
    ((1 + thresholdReserve rho #(whole c) +
        sideLoadBefore F O.orient i c : ℕ) : ℝ) ≤
      typicalDegreeTarget G rho rootCluster (whole c)
  component_capacity : ∀ i c,
    (F.size i : ℝ) + rho * (#(whole c) : ℝ) + 1 ≤
      (density - rho) *
        ((#(whole c) : ℝ) - thresholdHighBudget dy gamma N)

namespace CanonicalWholeEdgeThresholdHostNumerics

/-- Branch-independent scalar form used after an eligible edge has been
chosen from the root-image-dependent carry allocation. -/
structure ScalarFacts
    {b : ℕ} {B : Type v} [Fintype B] [DecidableEq B]
    (F : OrderedRootedForest b) (G : SimpleGraph B) [DecidableRel G.Adj]
    (rootCluster : Finset B) (whole : Fin 2 → Finset B)
    (rho density ratio dx dy gamma epsilon N : ℝ) (slack : ℕ)
    (lowSide highSide : Fin 2)
    (Dsource : ClassifiedThresholdOwnerNumerics
      F ratio dx dy gamma epsilon N slack)
    (hsides : highSide ≠ lowSide) : Prop where
  high_capacity : ∀ c,
    thresholdHighBudget dy gamma N + thresholdReserve rho #(whole c) ≤
      #(whole c)
  parent_budget : ∀ (base : Fin b → Fin 2 ≃ Fin 2)
      (hbase : ∀ t c,
        2 * sideLoadPrefix F base t c ≤ prefixOrder F t + slack) (i : Fin b),
    let O := actualThresholdSwitchOrientation F slack
      (thresholdLowBudget dx gamma N) (thresholdHighBudget dy gamma N)
      lowSide highSide Dsource.small hsides (Dsource.suffix_display highSide)
        base hbase
    let c := branchRootSide F O.orient i
    ((1 + thresholdReserve rho #(whole c) +
        sideLoadBefore F O.orient i c : ℕ) : ℝ) ≤
      typicalDegreeTarget G rho rootCluster (whole c)
  small_component_capacity : ∀ c,
    (slack : ℝ) + rho * (#(whole c) : ℝ) + 1 ≤
      (density - rho) *
        ((#(whole c) : ℝ) - thresholdHighBudget dy gamma N)

/-- Product-scale regularity arithmetic for one equal-size matching
endpoint.  This is the exact conversion used with
`three_regularityEpsilon_le_density_gap_mul_embeddingGamma`: one epsilon
charge for the component, one for the regularity reserve, and one for the
integer rounding unit fit in the `gamma` fraction left beyond the rounded
high occupancy budget. -/
theorem ScalarFacts.small_component_capacity_of_product_scale
    (rho density dy gamma N : ℝ) (slack m : ℕ)
    (hcard : (m : ℝ) = N)
    (hN : 0 ≤ N)
    (hdy : dy ≤ 1)
    (hhigh : 0 ≤ (dy - gamma) * N)
    (hslack : (slack : ℝ) ≤ rho * N)
    (hone : 1 ≤ rho * N)
    (hfactor : 0 ≤ density - rho)
    (hproduct : 3 * rho ≤ (density - rho) * gamma) :
    (slack : ℝ) + rho * m + 1 ≤
      (density - rho) * ((m : ℝ) - thresholdHighBudget dy gamma N) := by
  have hbudget : (thresholdHighBudget dy gamma N : ℝ) ≤
      (dy - gamma) * N := thresholdHighBudget_cast_le hhigh
  have htarget : (dy - gamma) * N ≤ (1 - gamma) * N :=
    mul_le_mul_of_nonneg_right (sub_le_sub_right hdy gamma) hN
  have hremaining : gamma * N ≤
      N - (thresholdHighBudget dy gamma N : ℝ) := by
    linarith
  have hleft : (slack : ℝ) + rho * m + 1 ≤ 3 * rho * N := by
    rw [hcard]
    linarith
  have hcoefficient : 3 * rho * N ≤
      ((density - rho) * gamma) * N :=
    mul_le_mul_of_nonneg_right hproduct hN
  have hright : ((density - rho) * gamma) * N ≤
      (density - rho) *
        (N - (thresholdHighBudget dy gamma N : ℝ)) := by
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left hremaining hfactor
  simpa only [hcard] using hleft.trans (hcoefficient.trans hright)

/-- It is enough to verify the parent budget separately at the two physical
endpoints.  The low-endpoint bound is only needed when its canonical budget
is nonzero: if that budget vanishes, maximality forces cutoff zero and every
root of the literal switch is sent to `highSide`. -/
theorem ScalarFacts.of_endpoint_budgets
    {b : ℕ} {B : Type v} [Fintype B] [DecidableEq B]
    (F : OrderedRootedForest b) (G : SimpleGraph B) [DecidableRel G.Adj]
    (rootCluster : Finset B) (whole : Fin 2 → Finset B)
    (rho density ratio dx dy gamma epsilon N : ℝ) (slack : ℕ)
    (lowSide highSide : Fin 2)
    (Dsource : ClassifiedThresholdOwnerNumerics
      F ratio dx dy gamma epsilon N slack)
    (hsides : highSide ≠ lowSide)
    (hhighCapacity : ∀ c,
      thresholdHighBudget dy gamma N + thresholdReserve rho #(whole c) ≤
        #(whole c))
    (hlowParent : thresholdLowBudget dx gamma N ≠ 0 →
      ((1 + thresholdReserve rho #(whole lowSide) +
          thresholdLowBudget dx gamma N : ℕ) : ℝ) ≤
        typicalDegreeTarget G rho rootCluster (whole lowSide))
    (hhighParent :
      ((1 + thresholdReserve rho #(whole highSide) +
          thresholdHighBudget dy gamma N : ℕ) : ℝ) ≤
        typicalDegreeTarget G rho rootCluster (whole highSide))
    (hcomponent : ∀ c,
      (slack : ℝ) + rho * (#(whole c) : ℝ) + 1 ≤
        (density - rho) *
          ((#(whole c) : ℝ) - thresholdHighBudget dy gamma N)) :
    ScalarFacts F G rootCluster whole rho density ratio dx dy gamma epsilon N
      slack lowSide highSide Dsource hsides :=
  { high_capacity := hhighCapacity
    parent_budget := by
      intro base hbase i
      let lowBudget := thresholdLowBudget dx gamma N
      let highBudget := thresholdHighBudget dy gamma N
      let O := actualThresholdSwitchOrientation F slack lowBudget highBudget
        lowSide highSide Dsource.small hsides
        (Dsource.suffix_display highSide) base hbase
      let c := branchRootSide F O.orient i
      have hpref : sideLoadBefore F O.orient i c ≤
          if c = lowSide then lowBudget else highBudget := by
        exact O.prefix_root_le Dsource.lowBudget_le_highBudget i
      by_cases hlowZero : lowBudget = 0
      · have hcut : O.cutoff = 0 := by
          change maximalFittingCutoff F base lowBudget = 0
          simpa only [hlowZero] using
            maximalFittingCutoff_eq_zero_of_budget_zero F base
        have hcLow : c ≠ lowSide := by
          exact O.late_root_high i (by rw [hcut]; exact Nat.zero_le _)
        have hcHigh : c = highSide := by
          have hcLowVal : c.val ≠ lowSide.val := fun h ↦ hcLow (Fin.ext h)
          have hsidesVal : highSide.val ≠ lowSide.val :=
            fun h ↦ hsides (Fin.ext h)
          apply Fin.ext
          omega
        have hprefHigh : sideLoadBefore F O.orient i c ≤ highBudget := by
          simpa only [hcLow, if_false] using hpref
        have hneedNat :
            1 + thresholdReserve rho #(whole c) +
                sideLoadBefore F O.orient i c ≤
              1 + thresholdReserve rho #(whole c) + highBudget :=
          Nat.add_le_add_left hprefHigh _
        have hneedReal :
            ((1 + thresholdReserve rho #(whole c) +
                sideLoadBefore F O.orient i c : ℕ) : ℝ) ≤
              ((1 + thresholdReserve rho #(whole c) + highBudget : ℕ) : ℝ) := by
          exact_mod_cast hneedNat
        have hhighParent' :
            ((1 + thresholdReserve rho #(whole c) + highBudget : ℕ) : ℝ) ≤
              typicalDegreeTarget G rho rootCluster (whole c) := by
          rw [hcHigh]
          simpa only [highBudget] using hhighParent
        exact hneedReal.trans hhighParent'
      · by_cases hcLow : c = lowSide
        · have hprefLow : sideLoadBefore F O.orient i c ≤ lowBudget := by
            simpa only [hcLow, if_true] using hpref
          have hneedNat :
              1 + thresholdReserve rho #(whole c) +
                  sideLoadBefore F O.orient i c ≤
                1 + thresholdReserve rho #(whole c) + lowBudget :=
            Nat.add_le_add_left hprefLow _
          have hneedReal :
              ((1 + thresholdReserve rho #(whole c) +
                  sideLoadBefore F O.orient i c : ℕ) : ℝ) ≤
                ((1 + thresholdReserve rho #(whole c) + lowBudget : ℕ) : ℝ) := by
            exact_mod_cast hneedNat
          have hlowBudgetNe : thresholdLowBudget dx gamma N ≠ 0 := by
            simpa only [lowBudget] using hlowZero
          have hlowParent' :
              ((1 + thresholdReserve rho #(whole c) + lowBudget : ℕ) : ℝ) ≤
                typicalDegreeTarget G rho rootCluster (whole c) := by
            rw [hcLow]
            simpa only [lowBudget] using hlowParent hlowBudgetNe
          exact hneedReal.trans hlowParent'
        · have hcHigh : c = highSide := by
            have hcLowVal : c.val ≠ lowSide.val := fun h ↦ hcLow (Fin.ext h)
            have hsidesVal : highSide.val ≠ lowSide.val :=
              fun h ↦ hsides (Fin.ext h)
            apply Fin.ext
            omega
          have hprefHigh : sideLoadBefore F O.orient i c ≤ highBudget := by
            simpa only [hcLow, if_false] using hpref
          have hneedNat :
              1 + thresholdReserve rho #(whole c) +
                  sideLoadBefore F O.orient i c ≤
                1 + thresholdReserve rho #(whole c) + highBudget :=
            Nat.add_le_add_left hprefHigh _
          have hneedReal :
              ((1 + thresholdReserve rho #(whole c) +
                  sideLoadBefore F O.orient i c : ℕ) : ℝ) ≤
                ((1 + thresholdReserve rho #(whole c) + highBudget : ℕ) : ℝ) := by
            exact_mod_cast hneedNat
          have hhighParent' :
              ((1 + thresholdReserve rho #(whole c) + highBudget : ℕ) : ℝ) ≤
                typicalDegreeTarget G rho rootCluster (whole c) := by
            rw [hcHigh]
            simpa only [highBudget] using hhighParent
          exact hneedReal.trans hhighParent'
    small_component_capacity := hcomponent }

/-- Aggregate endpoint typicality and canonical scalar inequalities give
the exact whole-edge record, without a low-endpoint degree premise when the
canonical orientation never uses that endpoint for roots. -/
theorem of_edgeEligible
    {b k : ℕ} {B : Type v} [Fintype B] [DecidableEq B]
    (F : OrderedRootedForest b) (G : SimpleGraph B) [DecidableRel G.Adj]
    (externalParent : Fin b → B)
    (rootCluster : Finset B) (endpoint : Fin k → Fin 2 → Finset B)
    (e : Fin k)
    (rho density ratio dx dy gamma epsilon N : ℝ) (slack : ℕ)
    (lowSide highSide : Fin 2)
    (Dsource : ClassifiedThresholdOwnerNumerics
      F ratio dx dy gamma epsilon N slack)
    (hsides : highSide ≠ lowSide)
    (hrootMem : ∀ i, externalParent i ∈ rootCluster)
    (heligible : ∀ i, edgeEligible G rho rootCluster endpoint
      (externalParent i) e)
    (S : ScalarFacts F G rootCluster (endpoint e)
      rho density ratio dx dy gamma epsilon N slack lowSide highSide
      Dsource hsides) :
    CanonicalWholeEdgeThresholdHostNumerics F G externalParent rootCluster
      (endpoint e) rho density ratio dx dy gamma epsilon N slack lowSide
      highSide Dsource hsides :=
  { parent_mem := hrootMem
    parent_typical := fun i c ↦ heligible i c
    high_capacity := S.high_capacity
    parent_budget := S.parent_budget
    component_capacity := by
      intro i c
      have hsmallReal : (F.size i : ℝ) ≤ slack := by
        exact_mod_cast Dsource.small i
      calc
        (F.size i : ℝ) + rho * (#(endpoint e c) : ℝ) + 1 ≤
            (slack : ℝ) + rho * (#(endpoint e c) : ℝ) + 1 := by
          gcongr
        _ ≤ (density - rho) *
            ((#(endpoint e c) : ℝ) - thresholdHighBudget dy gamma N) :=
          S.small_component_capacity c }

end CanonicalWholeEdgeThresholdHostNumerics

/-- Direct construction of the dynamic threshold datum on the complete
edge.  No residual prefix exists for Parts 1/2; the chosen orientation is
the literal maximal-cutoff orientation appearing in the parent budget. -/
noncomputable def canonicalThresholdStepDataOfWholeEdge
    {b : ℕ} {B : Type v} [Fintype B] [DecidableEq B]
    (F : OrderedRootedForest b) (G : SimpleGraph B) [DecidableRel G.Adj]
    (externalParent : Fin b → B)
    (rootCluster : Finset B) (whole : Fin 2 → Finset B)
    (rho density ratio dx dy gamma epsilon N : ℝ) (slack : ℕ)
    (lowSide highSide : Fin 2)
    (Dsource : ClassifiedThresholdOwnerNumerics
      F ratio dx dy gamma epsilon N slack)
    (hsides : highSide ≠ lowSide)
    (hunif : G.IsUniform rho (whole 0) (whole 1))
    (hwholeDisjoint : Disjoint (whole 0) (whole 1))
    (hdensity : density ≤ G.edgeDensity (whole 0) (whole 1))
    (hfactor : 0 ≤ density - rho)
    (H : CanonicalWholeEdgeThresholdHostNumerics F G externalParent
      rootCluster whole rho density ratio dx dy gamma epsilon N slack lowSide
      highSide Dsource hsides) :
    ActualThresholdStepData F G externalParent whole whole rho density :=
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
    live_subset := fun _ ↦ Finset.Subset.rfl
    whole_disjoint := hwholeDisjoint
    density_lower := hdensity
    factor_nonneg := hfactor
    reserve_regular := fun c ↦ thresholdReserve_covers rho #(whole c)
    live_capacity := H.high_capacity
    parent_neighbours := by
      intro base hbase O i
      let c := branchRootSide F O.orient i
      exact card_filter_adj_ge_of_not_mem_atypical G rho rootCluster (whole c)
        (externalParent i) (H.parent_mem i) (H.parent_typical i c)
        (H.parent_budget base hbase i)
    component_margin := H.component_capacity }

/-- Root-image-dependent eligible edge plus the exact canonical scalar row
produces a complete no-result-premise Parts-1/2 local datum. -/
noncomputable def canonicalThresholdOwnerLocalStepDataOfEligibleEdge
    {b k : ℕ} {B : Type v} [Fintype B] [DecidableEq B]
    (F : OrderedRootedForest b) (G : SimpleGraph B) [DecidableRel G.Adj]
    (externalParent : Fin b → B)
    (rootCluster : Finset B) (endpoint : Fin k → Fin 2 → Finset B)
    (e : Fin k)
    (rho density ratio dx dy gamma epsilon N : ℝ) (slack : ℕ)
    (lowSide highSide : Fin 2)
    (Dsource : ClassifiedThresholdOwnerNumerics
      F ratio dx dy gamma epsilon N slack)
    (hsides : highSide ≠ lowSide)
    (hrootMem : ∀ i, externalParent i ∈ rootCluster)
    (heligible : ∀ i, edgeEligible G rho rootCluster endpoint
      (externalParent i) e)
    (hunif : G.IsUniform rho (endpoint e 0) (endpoint e 1))
    (hwholeDisjoint : Disjoint (endpoint e 0) (endpoint e 1))
    (hdensity : density ≤ G.edgeDensity (endpoint e 0) (endpoint e 1))
    (hfactor : 0 ≤ density - rho)
    (S : CanonicalWholeEdgeThresholdHostNumerics.ScalarFacts F G rootCluster
      (endpoint e) rho density ratio dx dy gamma epsilon N slack lowSide
      highSide Dsource hsides) :
    OwnerLocalStepData F G externalParent (endpoint e) (endpoint e)
      rho density := by
  apply OwnerLocalStepData.threshold
  let H := CanonicalWholeEdgeThresholdHostNumerics.of_edgeEligible F G
    externalParent rootCluster endpoint e rho density ratio dx dy gamma
    epsilon N slack lowSide highSide Dsource hsides hrootMem heligible S
  exact canonicalThresholdStepDataOfWholeEdge F G externalParent rootCluster
    (endpoint e) rho density ratio dx dy gamma epsilon N slack lowSide highSide
    Dsource hsides hunif hwholeDisjoint hdensity hfactor H

#print axioms card_filter_adj_ge_of_not_mem_atypical
#print axioms WholeEdgeThresholdHostNumerics.toResidualThresholdHostFacts
#print axioms thresholdOwnerLocalStepDataOfWholeEdge
#print axioms thresholdOwnerLocalStepDataOfEligibleEdge
#print axioms CanonicalWholeEdgeThresholdHostNumerics.ScalarFacts.small_component_capacity_of_product_scale
#print axioms CanonicalWholeEdgeThresholdHostNumerics.ScalarFacts.of_endpoint_budgets
#print axioms CanonicalWholeEdgeThresholdHostNumerics.of_edgeEligible
#print axioms canonicalThresholdStepDataOfWholeEdge
#print axioms canonicalThresholdOwnerLocalStepDataOfEligibleEdge

end Erdos547b.ZhaoLemma58ThresholdRichApplication
