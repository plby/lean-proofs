/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayCofinalGlobalTransition
import ErdosProblems.Erdos599.HalfwayClubFinalGeometry
import ErdosProblems.Erdos599.HalfwayExactFrontierClause
import ErdosProblems.Erdos599.PathFilterComponents

/-!
# Cofinal unions of honest blueprint real parts

An intermediate honest blueprint may still contain unresolved imaginary
edges inherited from an earlier stage.  The terminal scheduler must not
demand that every whole stage edge set is already real.  This file instead
takes the monotone union of the real parts of actual blueprint stages.

Local bi-uniqueness, acyclicity, and absence of reverse rays follow from the
warp carried by each blueprint.  Countable boundedness localizes a
hypothetical final cycle or reverse ray at one stage.  Thus the union is a
globally ranked fair relation and every one of its edges is original by
construction.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599
namespace Blueprint
namespace LinkageBlueprint

open DirectedPath Alternating
open Alternating.RelationDecomposition

universe u v

variable {V : Type u}
variable {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa : Cardinal.{u}}

/-- A countably directed fair run of actual blueprints.  Only real-edge and
carrier monotonicity are required. -/
structure CofinalBlueprintRelationRun
    (Gamma : DWeb V) (Y : Set Gamma.DPath) (kappa : Cardinal.{u})
    (B : Set V) (I : Type v) [Preorder I] [Nonempty I]
    [IsDirectedOrder I] where
  stage : I → LinkageBlueprint Gamma Y kappa
  scheduled : I → V
  realEdge_mono : Monotone fun i ↦ (stage i).realPart.edges
  carrier_mono : Monotone fun i ↦ (stage i).vertexSet
  countably_bounded : HasCountableUpperBounds I
  fair : ∀ x,
    x ∈ ⋃ i, (stage i).vertexSet →
    (¬ ∃ y, (x, y) ∈ ⋃ i, (stage i).realPart.edges) →
    x ∉ B → ∃ i, scheduled i = x
  targetPath : I → FinitePath Gamma.graph
  targetPath_start : ∀ i, (targetPath i).start = scheduled i
  targetPath_finish : ∀ i, (targetPath i).finish ∈ B
  targetPath_vertices : ∀ i,
    (targetPath i).support ⊆ (stage i).vertexSet
  targetPath_edges : ∀ i,
    (targetPath i).edgeSet ⊆ (stage i).realPart.edges

/-- The scheduler-facing formulation of the same run.  A two-diamond
successor naturally proves `RealExtends` and `RealLinksTo`; the concrete
target route stored in `CofinalBlueprintRelationRun` is selected from the
latter only when compiling the final relation. -/
structure CofinalRealExtensionRun
    (Gamma : DWeb V) (Y : Set Gamma.DPath) (kappa : Cardinal.{u})
    (B : Set V) (I : Type v) [Preorder I] [Nonempty I]
    [IsDirectedOrder I] where
  stage : I → LinkageBlueprint Gamma Y kappa
  scheduled : I → V
  realExtends : ∀ {i j}, i ≤ j → (stage i).RealExtends (stage j) B
  countably_bounded : HasCountableUpperBounds I
  fair : ∀ x,
    x ∈ ⋃ i, (stage i).vertexSet →
    (¬ ∃ y, (x, y) ∈ ⋃ i, (stage i).realPart.edges) →
    x ∉ B → ∃ i, scheduled i = x
  resolved : ∀ i, (stage i).RealLinksTo (scheduled i) B

namespace CofinalRealExtensionRun

variable {B : Set V} {I : Type v}
variable [Preorder I] [Nonempty I] [IsDirectedOrder I]

private noncomputable def chosenTargetPath
    (R : CofinalRealExtensionRun Gamma Y kappa B I) (i : I) :
    FinitePath Gamma.graph :=
  Classical.choose (R.resolved i)

private theorem chosenTargetPath_spec
    (R : CofinalRealExtensionRun Gamma Y kappa B I) (i : I) :
    (R.chosenTargetPath i).start = R.scheduled i ∧
      (R.chosenTargetPath i).finish ∈ B ∧
      (R.chosenTargetPath i).support ⊆ (R.stage i).vertexSet ∧
      (R.chosenTargetPath i).edgeSet ⊆ (R.stage i).realPart.edges := by
  simpa only [chosenTargetPath, realPart_vertices] using
    (Classical.choose_spec (R.resolved i))

/-- Compile pairwise real extension and scheduled real links into the exact
cofinal real-relation run. -/
noncomputable def toBlueprintRelationRun
    (R : CofinalRealExtensionRun Gamma Y kappa B I) :
    CofinalBlueprintRelationRun Gamma Y kappa B I where
  stage := R.stage
  scheduled := R.scheduled
  realEdge_mono := fun _ _ hij ↦ (R.realExtends hij).realEdges_mono
  carrier_mono := fun _ _ hij ↦ (R.realExtends hij).vertices_mono
  countably_bounded := R.countably_bounded
  fair := R.fair
  targetPath := R.chosenTargetPath
  targetPath_start := fun i ↦ (R.chosenTargetPath_spec i).1
  targetPath_finish := fun i ↦ (R.chosenTargetPath_spec i).2.1
  targetPath_vertices := fun i ↦ (R.chosenTargetPath_spec i).2.2.1
  targetPath_edges := fun i ↦ (R.chosenTargetPath_spec i).2.2.2

end CofinalRealExtensionRun

namespace CofinalBlueprintRelationRun

variable {B : Set V} {I : Type v}
variable [Preorder I] [Nonempty I] [IsDirectedOrder I]

def finalEdge (R : CofinalBlueprintRelationRun Gamma Y kappa B I) :
    Set (V × V) :=
  ⋃ i, (R.stage i).realPart.edges

def finalCarrier (R : CofinalBlueprintRelationRun Gamma Y kappa B I) :
    Set V :=
  ⋃ i, (R.stage i).vertexSet

theorem stageRealEdge_subset_finalEdge
    (R : CofinalBlueprintRelationRun Gamma Y kappa B I) (i : I) :
    (R.stage i).realPart.edges ⊆ R.finalEdge := by
  intro e he
  exact Set.mem_iUnion.2 ⟨i, he⟩

theorem stageCarrier_subset_finalCarrier
    (R : CofinalBlueprintRelationRun Gamma Y kappa B I) (i : I) :
    (R.stage i).vertexSet ⊆ R.finalCarrier := by
  intro x hx
  exact Set.mem_iUnion.2 ⟨i, hx⟩

private theorem stageRealEdge_biunique
    (R : CofinalBlueprintRelationRun Gamma Y kappa B I) (i : I) :
    Relator.BiUnique
      (fun x y ↦ (x, y) ∈ (R.stage i).realPart.edges) := by
  have hfull := Alternating.IsWarp.familyEdges_biUnique
    (R.stage i).isWarp
  constructor
  · intro x y z hxz hyz
    exact hfull.1 hxz.1 hyz.1
  · intro x y z hxy hxz
    exact hfull.2 hxy.1 hxz.1

theorem finalEdge_biunique
    (R : CofinalBlueprintRelationRun Gamma Y kappa B I) :
    Relator.BiUnique (fun x y ↦ (x, y) ∈ R.finalEdge) := by
  constructor
  · intro x y z hxz hyz
    obtain ⟨i, hixz⟩ := Set.mem_iUnion.1 hxz
    obtain ⟨j, hjyz⟩ := Set.mem_iUnion.1 hyz
    obtain ⟨m, him, hjm⟩ := exists_ge_ge i j
    exact (R.stageRealEdge_biunique m).1
      (R.realEdge_mono him hixz) (R.realEdge_mono hjm hjyz)
  · intro x y z hxy hxz
    obtain ⟨i, hixy⟩ := Set.mem_iUnion.1 hxy
    obtain ⟨j, hjxz⟩ := Set.mem_iUnion.1 hxz
    obtain ⟨m, him, hjm⟩ := exists_ge_ge i j
    exact (R.stageRealEdge_biunique m).2
      (R.realEdge_mono him hixy) (R.realEdge_mono hjm hjxz)

theorem finalEdge_endpoints
    (R : CofinalBlueprintRelationRun Gamma Y kappa B I)
    {e : V × V} (he : e ∈ R.finalEdge) :
    e.1 ∈ R.finalCarrier ∧ e.2 ∈ R.finalCarrier := by
  obtain ⟨i, hi⟩ := Set.mem_iUnion.1 he
  have hsupport : e.1 ∈ (R.stage i).vertexSet ∧
      e.2 ∈ (R.stage i).vertexSet := by
    have hiedge := hi.1
    change e ∈ ⋃ p ∈ (R.stage i).paths, p.edgeSet at hiedge
    simp only [Set.mem_iUnion] at hiedge
    obtain ⟨p, hp, hep⟩ := hiedge
    have hend := p.edgeSet_subset_support_prod hep
    exact ⟨⟨p, hp, hend.1⟩, ⟨p, hp, hend.2⟩⟩
  exact ⟨R.stageCarrier_subset_finalCarrier i hsupport.1,
    R.stageCarrier_subset_finalCarrier i hsupport.2⟩

private theorem stageRealEdge_not_containsDirectedCycle
    (R : CofinalBlueprintRelationRun Gamma Y kappa B I) (i : I) :
    ¬ ContainsDirectedCycle (R.stage i).realPart.edges := by
  rintro ⟨cycle, hcycle⟩
  exact PathFilterComponents.DWeb.IsWarp.familyEdges_not_containsDirectedCycle
    (R.stage i).isWarp ⟨cycle, hcycle.trans Set.inter_subset_left⟩

private theorem stageRealEdge_not_containsReverseDirectedRay
    (R : CofinalBlueprintRelationRun Gamma Y kappa B I) (i : I) :
    ¬ ContainsReverseDirectedRay (R.stage i).realPart.edges := by
  rintro ⟨ray, hray⟩
  exact PathFilterComponents.DWeb.IsWarp.familyEdges_not_containsReverseDirectedRay
    (R.stage i).isWarp ⟨ray, fun n ↦ Set.inter_subset_left (hray n)⟩

theorem finalEdge_not_containsReverseDirectedRay
    (R : CofinalBlueprintRelationRun Gamma Y kappa B I) :
    ¬ ContainsReverseDirectedRay R.finalEdge := by
  rintro ⟨ray, hray⟩
  let edgeAt : ℕ → V × V := fun n ↦
    (ray.vertex (n + 1), ray.vertex n)
  have hedge : ∀ n, edgeAt n ∈ R.finalEdge := fun n ↦ hray n
  let stageAt : ℕ → I := fun n ↦
    Classical.choose (Set.mem_iUnion.1 (hedge n))
  have hstage : ∀ n,
      edgeAt n ∈ (R.stage (stageAt n)).realPart.edges := fun n ↦
    Classical.choose_spec (Set.mem_iUnion.1 (hedge n))
  obtain ⟨j, hj⟩ := R.countably_bounded stageAt
  apply R.stageRealEdge_not_containsReverseDirectedRay j
  refine ⟨ray, ?_⟩
  intro n
  exact R.realEdge_mono (hj n) (hstage n)

theorem finalEdge_not_containsDirectedCycle
    (R : CofinalBlueprintRelationRun Gamma Y kappa B I) :
    ¬ ContainsDirectedCycle R.finalEdge := by
  rintro ⟨cycle, hcycle⟩
  let indexAt : ℕ → Fin cycle.length := fun n ↦
    ⟨n % cycle.length, Nat.mod_lt n cycle.positive⟩
  let edgeAt : ℕ → V × V := fun n ↦
    (cycle.vertex (indexAt n), cycle.vertex (cycle.next (indexAt n)))
  have hedge : ∀ n, edgeAt n ∈ R.finalEdge := by
    intro n
    apply hcycle
    exact ⟨indexAt n, rfl⟩
  let stageAt : ℕ → I := fun n ↦
    Classical.choose (Set.mem_iUnion.1 (hedge n))
  have hstage : ∀ n,
      edgeAt n ∈ (R.stage (stageAt n)).realPart.edges := fun n ↦
    Classical.choose_spec (Set.mem_iUnion.1 (hedge n))
  obtain ⟨j, hj⟩ := R.countably_bounded stageAt
  apply R.stageRealEdge_not_containsDirectedCycle j
  refine ⟨cycle, ?_⟩
  rintro e ⟨i, rfl⟩
  have hindex : indexAt i.1 = i := by
    apply Fin.ext
    exact Nat.mod_eq_of_lt i.2
  have he := R.realEdge_mono (hj i.1) (hstage i.1)
  simpa only [edgeAt, hindex] using he

theorem finalEdge_real
    (R : CofinalBlueprintRelationRun Gamma Y kappa B I) :
    R.finalEdge ⊆ {e | Gamma.graph.Adj e.1 e.2} := by
  intro e he
  obtain ⟨i, hi⟩ := Set.mem_iUnion.1 he
  exact hi.2

theorem targetPath_support_subset_finalCarrier
    (R : CofinalBlueprintRelationRun Gamma Y kappa B I) (i : I) :
    (R.targetPath i).support ⊆ R.finalCarrier :=
  (R.targetPath_vertices i).trans (R.stageCarrier_subset_finalCarrier i)

theorem targetPath_edges_subset_finalEdge
    (R : CofinalBlueprintRelationRun Gamma Y kappa B I) (i : I) :
    (R.targetPath i).edgeSet ⊆ R.finalEdge :=
  (R.targetPath_edges i).trans (R.stageRealEdge_subset_finalEdge i)

def wellFoundedFairGlobalRelation
    (R : CofinalBlueprintRelationRun Gamma Y kappa B I) :
    CardinalInduction.HalfwayScheduler.WellFoundedFairGlobalRelation
      Gamma Y kappa B I where
  edge := R.finalEdge
  carrier := R.finalCarrier
  endpoints_mem := fun _ he ↦ R.finalEdge_endpoints he
  biunique := R.finalEdge_biunique
  no_directed_cycle := R.finalEdge_not_containsDirectedCycle
  no_reverse_ray := R.finalEdge_not_containsReverseDirectedRay
  edge_real := R.finalEdge_real
  scheduled := R.scheduled
  fair := R.fair
  targetPath := R.targetPath
  targetPath_start := R.targetPath_start
  targetPath_finish := R.targetPath_finish
  targetPath_vertices := R.targetPath_support_subset_finalCarrier
  targetPath_edges := R.targetPath_edges_subset_finalEdge

def rankedFairGlobalRelation
    (R : CofinalBlueprintRelationRun Gamma Y kappa B I) :
    CardinalInduction.HalfwayScheduler.RankedFairGlobalRelation
      Gamma Y kappa B I :=
  R.wellFoundedFairGlobalRelation.ranked

@[simp] theorem rankedFairGlobalRelation_edge
    (R : CofinalBlueprintRelationRun Gamma Y kappa B I) :
    R.rankedFairGlobalRelation.edge = R.finalEdge :=
  rfl

@[simp] theorem rankedFairGlobalRelation_carrier
    (R : CofinalBlueprintRelationRun Gamma Y kappa B I) :
    R.rankedFairGlobalRelation.carrier = R.finalCarrier :=
  rfl

/-- Exact club-frontier geometry closes the honest real-part run directly
to the common final construction certificate. -/
theorem exists_certificate
    {C : ClubStageGeometry Gamma Y kappa (Order.succ kappa)}
    (R : CofinalBlueprintRelationRun Gamma Y kappa Gamma.target I)
    {A0 : Set V}
    (boundary :
      CardinalInduction.HalfwayScheduler.RankedClubFrontierBoundary
        C R.rankedFairGlobalRelation A0) :
    Nonempty (CardinalInduction.GloballyResolvedBlueprintCertificate
      Gamma A0 kappa) := by
  obtain ⟨F⟩ := boundary.exists_finalGeometry
  exact ⟨F.certificate⟩

/-- The same concrete boundary already yields the exact-frontier qualified
half-way linkage. -/
theorem exists_exactFrontierHalfwayLinkage
    {C : ClubStageGeometry Gamma Y kappa (Order.succ kappa)}
    (R : CofinalBlueprintRelationRun Gamma Y kappa Gamma.target I)
    {A0 : Set V}
    (boundary :
      CardinalInduction.HalfwayScheduler.RankedClubFrontierBoundary
        C R.rankedFairGlobalRelation A0) :
    ∃ W : Set Gamma.DPath,
      CardinalInduction.ExactFrontierHalfwayLinkageOfAltitude
        Gamma A0 kappa W := by
  exact (R.exists_certificate boundary).some
    |>.exists_exactFrontierHalfwayLinkage

#print axioms CofinalBlueprintRelationRun.finalEdge_biunique
#print axioms CofinalBlueprintRelationRun.finalEdge_not_containsDirectedCycle
#print axioms CofinalBlueprintRelationRun.finalEdge_not_containsReverseDirectedRay
#print axioms CofinalBlueprintRelationRun.rankedFairGlobalRelation
#print axioms CofinalBlueprintRelationRun.exists_exactFrontierHalfwayLinkage

end CofinalBlueprintRelationRun

end LinkageBlueprint
end Blueprint
end Erdos599
