/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayInsideFragmentUnion
import ErdosProblems.Erdos599.HalfwayScheduler

/-!
# Assembling the Section 9 transactions into one globally ranked relation

The relation used at the end of the half-way construction is not the union
of the full request-local splice relations.  Those relations contain
compressed imaginary edges, and Assertion 9.30 later deletes such edges.
The surviving real-edge relations, on the other hand, are monotone under
the exact real-extension invariant (9.32).

This file records the precise compatibility needed of the transfinite
scheduler.  Every stage is an actual `ClubStageUnionData`, not an arbitrary
edge relation.  Its real part is filtered by `relationRealEdges`.  The
scheduler retains one rank which agrees with every stage rank and makes the
real-edge family monotone.  Directedness then proves that the union is
bi-unique, while the common rank excludes both directed cycles and reverse
rays.  Thus the construction produces the single
`RankedFairGlobalRelation` required by the sound relation-level form of
Assertion 9.33.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599
namespace Blueprint
namespace LinkageBlueprint

open DirectedPath Alternating

universe u v

variable {V : Type u}
variable {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa theta : Cardinal.{u}}

/-- A fair directed run of concrete Section 9 splice transactions.

`realEdge_mono` concerns only original-web edges.  Imaginary edges may be
deleted by later 9.30 cuts and are deliberately absent from this invariant.
`rank_agrees` is the exact no-backward-growth invariant: the local rank
constructed by each inside/outside splice is the restriction of one common
rank, rather than an unrelated rank chosen afresh at every request. -/
structure GloballyCompatibleClubStageRun
    (C : ClubStageGeometry Gamma Y kappa theta)
    (I : Type v) [Preorder I] [Nonempty I] [IsDirectedOrder I] where
  blueprint : I → LinkageBlueprint Gamma Y kappa
  fractured : I → FracturedWarp Gamma
  assignment : ∀ i, SimultaneousAssignment (fractured i).paths Y
  scheduled : I → V
  data : ∀ i, ClubStageUnionData C (blueprint i) (assignment i) (scheduled i)
  rank : V → ℕ
  rank_agrees : ∀ i, (data i).rank = rank
  realEdge_mono : Monotone fun i ↦
    relationRealEdges (Gamma := Gamma)
      ((data i).inside ∪ assignedFiniteEdges (assignment i))
  fair : ∀ x,
    x ∈ ⋃ i, (data i).carrier →
    (¬ ∃ y, (x, y) ∈ ⋃ i,
      relationRealEdges (Gamma := Gamma)
        ((data i).inside ∪ assignedFiniteEdges (assignment i))) →
    x ∉ Gamma.target → ∃ i, scheduled i = x

namespace GloballyCompatibleClubStageRun

variable {C : ClubStageGeometry Gamma Y kappa theta}
variable {I : Type v} [Preorder I] [Nonempty I] [IsDirectedOrder I]

/-- The surviving original-web relation at one transaction. -/
def stageRealEdge (R : GloballyCompatibleClubStageRun C I) (i : I) :
    Set (V × V) :=
  relationRealEdges (Gamma := Gamma)
    ((R.data i).inside ∪ assignedFiniteEdges (R.assignment i))

/-- The final real relation is the directed union of the surviving real
relations, not the union of the full imaginary splice relations. -/
def finalEdge (R : GloballyCompatibleClubStageRun C I) : Set (V × V) :=
  ⋃ i, R.stageRealEdge i

/-- Every carrier vertex ever introduced is retained. -/
def finalCarrier (R : GloballyCompatibleClubStageRun C I) : Set V :=
  ⋃ i, (R.data i).carrier

theorem stageRealEdge_mono (R : GloballyCompatibleClubStageRun C I) :
    Monotone R.stageRealEdge := by
  intro i j hij
  exact R.realEdge_mono hij

private theorem stageRelation_biunique
    (R : GloballyCompatibleClubStageRun C I) (i : I) :
    Relator.BiUnique (fun x y ↦
      (x, y) ∈ (R.data i).inside ∪
        assignedFiniteEdges (R.assignment i)) :=
  biUnique_union_of_cross (R.data i).inside_biunique
    (assignedFiniteEdges_biUnique (R.assignment i))
    (R.data i).cross_in (R.data i).cross_out

private theorem stageRealEdge_biunique
    (R : GloballyCompatibleClubStageRun C I) (i : I) :
    Relator.BiUnique (fun x y ↦ (x, y) ∈ R.stageRealEdge i) := by
  have h := R.stageRelation_biunique i
  constructor
  · intro x y z hxz hyz
    exact h.1 hxz.1 hyz.1
  · intro x y z hxy hxz
    exact h.2 hxy.1 hxz.1

theorem finalEdge_biunique (R : GloballyCompatibleClubStageRun C I) :
    Relator.BiUnique (fun x y ↦ (x, y) ∈ R.finalEdge) := by
  constructor
  · intro x y z hxz hyz
    obtain ⟨i, hixz⟩ := Set.mem_iUnion.1 hxz
    obtain ⟨j, hjyz⟩ := Set.mem_iUnion.1 hyz
    obtain ⟨k, hik, hjk⟩ := exists_ge_ge i j
    exact (R.stageRealEdge_biunique k).1
      (R.stageRealEdge_mono hik hixz)
      (R.stageRealEdge_mono hjk hjyz)
  · intro x y z hxy hxz
    obtain ⟨i, hixy⟩ := Set.mem_iUnion.1 hxy
    obtain ⟨j, hjxz⟩ := Set.mem_iUnion.1 hxz
    obtain ⟨k, hik, hjk⟩ := exists_ge_ge i j
    exact (R.stageRealEdge_biunique k).2
      (R.stageRealEdge_mono hik hixy)
      (R.stageRealEdge_mono hjk hjxz)

theorem finalEdge_endpoints
    (R : GloballyCompatibleClubStageRun C I) {e : V × V}
    (he : e ∈ R.finalEdge) :
    e.1 ∈ R.finalCarrier ∧ e.2 ∈ R.finalCarrier := by
  obtain ⟨i, hi⟩ := Set.mem_iUnion.1 he
  have hi' : e ∈ (R.data i).inside ∪
      assignedFiniteEdges (R.assignment i) := hi.1
  have hend : e.1 ∈ (R.data i).carrier ∧
      e.2 ∈ (R.data i).carrier := by
    rcases hi' with hi' | hi'
    · exact (R.data i).inside_endpoints e hi'
    · exact (R.data i).assigned_endpoints e hi'
  exact ⟨Set.mem_iUnion.2 ⟨i, hend.1⟩,
    Set.mem_iUnion.2 ⟨i, hend.2⟩⟩

theorem finalEdge_rank
    (R : GloballyCompatibleClubStageRun C I) {x y : V}
    (hxy : (x, y) ∈ R.finalEdge) : R.rank x < R.rank y := by
  obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hxy
  have hi' := hi.1
  have hrank : (R.data i).rank x < (R.data i).rank y := by
    rcases hi' with hi' | hi'
    · exact (R.data i).inside_rank hi'
    · exact (R.data i).assigned_rank hi'
  simpa only [R.rank_agrees i] using hrank

theorem finalEdge_real
    (R : GloballyCompatibleClubStageRun C I) :
    R.finalEdge ⊆ {e | Gamma.graph.Adj e.1 e.2} := by
  intro e he
  obtain ⟨i, hi⟩ := Set.mem_iUnion.1 he
  exact hi.2

/-- A globally compatible run of the concrete closing transactions produces
the exact single-relation scheduler input.  Bi-uniqueness is a theorem of
directed monotonicity, and target paths are inherited from their actual
transaction data. -/
def rankedFairGlobalRelation
    (R : GloballyCompatibleClubStageRun C I) :
    CardinalInduction.HalfwayScheduler.RankedFairGlobalRelation
      Gamma Y kappa Gamma.target I where
  edge := R.finalEdge
  carrier := R.finalCarrier
  rank := R.rank
  endpoints_mem := fun e he ↦ R.finalEdge_endpoints he
  biunique := R.finalEdge_biunique
  rank_step := fun hxy ↦ R.finalEdge_rank hxy
  edge_real := R.finalEdge_real
  scheduled := R.scheduled
  fair := by
    intro x hx hno htarget
    exact R.fair x hx hno htarget
  targetPath := fun i ↦ (R.data i).target_path
  targetPath_start := fun i ↦ (R.data i).target_path_start
  targetPath_finish := fun i ↦ (R.data i).target_path_finish
  targetPath_vertices := by
    intro i x hx
    exact Set.mem_iUnion.2 ⟨i, (R.data i).target_path_vertices hx⟩
  targetPath_edges := by
    intro i e he
    exact Set.mem_iUnion.2 ⟨i, (R.data i).target_path_edges he⟩

end GloballyCompatibleClubStageRun

end LinkageBlueprint
end Blueprint
end Erdos599

