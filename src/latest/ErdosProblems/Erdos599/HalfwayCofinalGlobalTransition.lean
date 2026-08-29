/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayInsideFragmentUnion
import ErdosProblems.Erdos599.HalfwayScheduler

/-!
# The cofinal global transition in the half-way scheduler

The ranks which orient two different Section 9 transactions are local
objects.  There is no reason for them to agree, and requiring a common
local rank would hide the main limit argument of Assertion 9.33.

The actual invariant is instead the following.  The surviving real-edge
relations and their carriers are monotone, and every countable family of
stages has a common upper bound.  If the final union contained a reverse
ray, choose one stage for each of its countably many edges and pass to a
common upper bound.  The entire reverse ray would then occur in one local
splice relation, contradicting that transaction's local natural-number
rank.  The same argument (with a periodic enumeration of the finitely many
cycle edges) excludes directed cycles.

Consequently the predecessor relation of the final union is well-founded.
Its canonical well-founded depth is a *global* natural-number rank.  This
file uses that derived rank to construct the exact `RankedFairGlobalRelation`
consumed by `HalfwayScheduler`.  It also retains the two survival statements
needed by the scheduler: every old real edge and every edge of a scheduled
target path belongs to the final relation.
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
variable {kappa theta : Cardinal.{u}}

/-- Every countable family of stages has a common upper bound.  This is the
precise cofinality property used to localize a reverse ray at one stage. -/
def HasCountableUpperBounds (I : Type v) [Preorder I] : Prop :=
  forall f : Nat -> I, exists j : I, forall n, f n <= j

/-- The stage order below the successor cardinal used by Section 9 has the
countable-upper-bound property.  The supremum of the countably many stage
ordinals is still below `(succ kappa).ord`, because the successor cardinal
is regular and has cofinality strictly above `aleph0`. -/
theorem hasCountableUpperBounds_ladderStage_succ
    (hkappa : aleph0 <= kappa) :
    HasCountableUpperBounds (Ladder.Stage (Order.succ kappa)) := by
  intro f
  have hregular : (Order.succ kappa).IsRegular :=
    Cardinal.isRegular_succ hkappa
  have hsup : (iSup fun n : Nat => (f n).1) <
      (Order.succ kappa).ord := by
    apply Ordinal.lift_iSup_lt_of_lt_cof
    · simpa [hregular.cof_ord] using
        hkappa.trans_lt (Order.lt_succ kappa)
    · intro n
      exact (f n).2
  let j : Ladder.Stage (Order.succ kappa) :=
    ⟨iSup fun n : Nat => (f n).1, hsup⟩
  refine ⟨j, ?_⟩
  intro n
  exact Ordinal.le_iSup (fun m : Nat => (f m).1) n

/-- There is always a least stage below a successor cardinal.  Keeping this
instance next to the specialized scheduler record makes the latter usable
without an otherwise irrelevant nonemptiness field. -/
instance successorLadderStage_nonempty :
    Nonempty (Ladder.Stage (Order.succ kappa)) :=
  ⟨⟨0, Cardinal.ord_pos.mpr
    (Cardinal.succ_pos kappa)⟩⟩

/-- A fair run of actual Section 9 transactions with the genuine global
transition invariant.

Unlike `GloballyCompatibleClubStageRun`, this record does not ask the local
ranks to agree.  The global rank is constructed below, after acyclicity and
absence of reverse rays have been proved for the final union. -/
structure CofinalClubStageRun
    (C : ClubStageGeometry Gamma Y kappa theta)
    (I : Type v) [Preorder I] [Nonempty I] [IsDirectedOrder I] where
  blueprint : I -> LinkageBlueprint Gamma Y kappa
  fractured : I -> FracturedWarp Gamma
  assignment : forall i, SimultaneousAssignment (fractured i).paths Y
  scheduled : I -> V
  data : forall i,
    ClubStageUnionData C (blueprint i) (assignment i) (scheduled i)
  realEdge_mono : Monotone fun i =>
    relationRealEdges (Gamma := Gamma)
      ((data i).inside ∪ assignedFiniteEdges (assignment i))
  carrier_mono : Monotone fun i => (data i).carrier
  countably_bounded : HasCountableUpperBounds I
  fair : forall x,
    x ∈ ⋃ i, (data i).carrier ->
    (¬ ∃ y, (x, y) ∈ ⋃ i,
      relationRealEdges (Gamma := Gamma)
        ((data i).inside ∪ assignedFiniteEdges (assignment i))) ->
    x ∉ Gamma.target -> exists i, scheduled i = x

/-- Scheduler data indexed by the actual `kappa+` ladder stages.  Countable
boundedness is deliberately absent: `toCofinalRun` derives it from
`aleph0 <= kappa`. -/
structure SuccessorClubStageRun
    (C : ClubStageGeometry Gamma Y kappa (Order.succ kappa)) where
  blueprint : Ladder.Stage (Order.succ kappa) ->
    LinkageBlueprint Gamma Y kappa
  fractured : Ladder.Stage (Order.succ kappa) -> FracturedWarp Gamma
  assignment : forall i, SimultaneousAssignment (fractured i).paths Y
  scheduled : Ladder.Stage (Order.succ kappa) -> V
  data : forall i,
    ClubStageUnionData C (blueprint i) (assignment i) (scheduled i)
  realEdge_mono : Monotone fun i =>
    relationRealEdges (Gamma := Gamma)
      ((data i).inside ∪ assignedFiniteEdges (assignment i))
  carrier_mono : Monotone fun i => (data i).carrier
  fair : forall x,
    x ∈ ⋃ i, (data i).carrier ->
    (¬ ∃ y, (x, y) ∈ ⋃ i,
      relationRealEdges (Gamma := Gamma)
        ((data i).inside ∪ assignedFiniteEdges (assignment i))) ->
    x ∉ Gamma.target -> exists i, scheduled i = x

namespace SuccessorClubStageRun

variable {C : ClubStageGeometry Gamma Y kappa (Order.succ kappa)}

/-- Insert the countable-upper-bound theorem into a concrete successor-stage
scheduler run. -/
def toCofinalRun (R : SuccessorClubStageRun C)
    (hkappa : aleph0 <= kappa) :
    CofinalClubStageRun C (Ladder.Stage (Order.succ kappa)) where
  blueprint := R.blueprint
  fractured := R.fractured
  assignment := R.assignment
  scheduled := R.scheduled
  data := R.data
  realEdge_mono := R.realEdge_mono
  carrier_mono := R.carrier_mono
  countably_bounded := hasCountableUpperBounds_ladderStage_succ hkappa
  fair := R.fair

end SuccessorClubStageRun

namespace CofinalClubStageRun

variable {C : ClubStageGeometry Gamma Y kappa theta}
variable {I : Type v} [Preorder I] [Nonempty I] [IsDirectedOrder I]

/-- The surviving original-web relation at one transaction. -/
def stageRealEdge (R : CofinalClubStageRun C I) (i : I) : Set (V × V) :=
  relationRealEdges (Gamma := Gamma)
    ((R.data i).inside ∪ assignedFiniteEdges (R.assignment i))

/-- The full (real and imaginary) splice relation at one transaction. -/
def stageFullEdge (R : CofinalClubStageRun C I) (i : I) : Set (V × V) :=
  (R.data i).inside ∪ assignedFiniteEdges (R.assignment i)

/-- The final relation consists exactly of the real edges which survive at
some stage. -/
def finalEdge (R : CofinalClubStageRun C I) : Set (V × V) :=
  ⋃ i, R.stageRealEdge i

/-- Every carrier vertex introduced at a stage remains visible in the final
root-orbit decomposition, including isolated vertices. -/
def finalCarrier (R : CofinalClubStageRun C I) : Set V :=
  ⋃ i, (R.data i).carrier

theorem stageRealEdge_mono (R : CofinalClubStageRun C I) :
    Monotone R.stageRealEdge := by
  intro i j hij
  exact R.realEdge_mono hij

theorem stageCarrier_mono (R : CofinalClubStageRun C I) :
    Monotone fun i => (R.data i).carrier :=
  R.carrier_mono

theorem stageRealEdge_subset_finalEdge
    (R : CofinalClubStageRun C I) (i : I) :
    R.stageRealEdge i ⊆ R.finalEdge := by
  intro e he
  exact Set.mem_iUnion.2 (Exists.intro i he)

theorem stageCarrier_subset_finalCarrier
    (R : CofinalClubStageRun C I) (i : I) :
    (R.data i).carrier ⊆ R.finalCarrier := by
  intro x hx
  exact Set.mem_iUnion.2 (Exists.intro i hx)

/-- The real part of the incoming blueprint at every transaction survives
in the exact final real-edge union.  This is the edge-survival content of
the stable 9.34 transition. -/
theorem blueprint_realEdges_subset_finalEdge
    (R : CofinalClubStageRun C I) (i : I) :
    (R.blueprint i).realPart.edges ⊆ R.finalEdge := by
  exact (R.data i).old_real_edges |>.trans
    (R.stageRealEdge_subset_finalEdge i)

/-- The target route produced when a terminal is scheduled survives in the
final real-edge relation. -/
theorem targetPath_edges_subset_finalEdge
    (R : CofinalClubStageRun C I) (i : I) :
    (R.data i).target_path.edgeSet ⊆ R.finalEdge := by
  exact (R.data i).target_path_edges |>.trans
    (R.stageRealEdge_subset_finalEdge i)

/-- Every vertex of a scheduled target route remains in the final carrier. -/
theorem targetPath_support_subset_finalCarrier
    (R : CofinalClubStageRun C I) (i : I) :
    (R.data i).target_path.support ⊆ R.finalCarrier := by
  exact (R.data i).target_path_vertices |>.trans
    (R.stageCarrier_subset_finalCarrier i)

private theorem stageFullEdge_biunique
    (R : CofinalClubStageRun C I) (i : I) :
    Relator.BiUnique (fun x y => (x, y) ∈ R.stageFullEdge i) := by
  exact biUnique_union_of_cross (R.data i).inside_biunique
    (assignedFiniteEdges_biUnique (R.assignment i))
    (R.data i).cross_in (R.data i).cross_out

private theorem stageRealEdge_biunique
    (R : CofinalClubStageRun C I) (i : I) :
    Relator.BiUnique (fun x y => (x, y) ∈ R.stageRealEdge i) := by
  have h := R.stageFullEdge_biunique i
  constructor
  · intro x y z hxz hyz
    exact h.1 hxz.1 hyz.1
  · intro x y z hxy hxz
    exact h.2 hxy.1 hxz.1

/-- Directed monotonicity localizes two incidences at one stage, so the
final relation is still bi-unique. -/
theorem finalEdge_biunique (R : CofinalClubStageRun C I) :
    Relator.BiUnique (fun x y => (x, y) ∈ R.finalEdge) := by
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
    (R : CofinalClubStageRun C I) {e : V × V}
    (he : e ∈ R.finalEdge) :
    e.1 ∈ R.finalCarrier ∧ e.2 ∈ R.finalCarrier := by
  obtain ⟨i, hi⟩ := Set.mem_iUnion.1 he
  have hiFull : e ∈ R.stageFullEdge i := hi.1
  have hend : e.1 ∈ (R.data i).carrier ∧
      e.2 ∈ (R.data i).carrier := by
    rcases hiFull with hiInside | hiAssigned
    · exact (R.data i).inside_endpoints e hiInside
    · exact (R.data i).assigned_endpoints e hiAssigned
  exact ⟨R.stageCarrier_subset_finalCarrier i hend.1,
    R.stageCarrier_subset_finalCarrier i hend.2⟩

/-- Each local full splice relation is acyclic. -/
private theorem stageFullEdge_not_containsDirectedCycle
    (R : CofinalClubStageRun C I) (i : I) :
    ¬ ContainsDirectedCycle (R.stageFullEdge i) := by
  apply not_containsDirectedCycle_of_rank
    (R.stageFullEdge i) (R.data i).rank
  intro x y hxy
  exact hxy.elim (R.data i).inside_rank (R.data i).assigned_rank

/-- Each local full splice relation has no reverse ray. -/
private theorem stageFullEdge_not_containsReverseDirectedRay
    (R : CofinalClubStageRun C I) (i : I) :
    ¬ ContainsReverseDirectedRay (R.stageFullEdge i) := by
  apply not_containsReverseDirectedRay_of_rank
    (R.stageFullEdge i) (R.data i).rank
  intro x y hxy
  exact hxy.elim (R.data i).inside_rank (R.data i).assigned_rank

/-- Countable cofinality is exactly what excludes a reverse ray in the
monotone final union. -/
theorem finalEdge_not_containsReverseDirectedRay
    (R : CofinalClubStageRun C I) :
    ¬ ContainsReverseDirectedRay R.finalEdge := by
  rintro ⟨ray, hray⟩
  let edgeAt : Nat -> V × V :=
    fun n => (ray.vertex (n + 1), ray.vertex n)
  have hedge : forall n, edgeAt n ∈ R.finalEdge := by
    intro n
    exact hray n
  let stageAt : Nat -> I := fun n =>
    Classical.choose (Set.mem_iUnion.1 (hedge n))
  have hstageAt : forall n, edgeAt n ∈ R.stageRealEdge (stageAt n) := by
    intro n
    exact Classical.choose_spec (Set.mem_iUnion.1 (hedge n))
  obtain ⟨j, hj⟩ := R.countably_bounded stageAt
  apply R.stageFullEdge_not_containsReverseDirectedRay j
  refine ⟨ray, ?_⟩
  intro n
  have hreal : edgeAt n ∈ R.stageRealEdge j :=
    R.stageRealEdge_mono (hj n) (hstageAt n)
  exact hreal.1

/-- A periodic enumeration of the finitely many cycle edges lets the same
countable-upper-bound argument localize a directed cycle at one stage. -/
theorem finalEdge_not_containsDirectedCycle
    (R : CofinalClubStageRun C I) :
    ¬ ContainsDirectedCycle R.finalEdge := by
  rintro ⟨cycle, hcycle⟩
  let indexAt : Nat -> Fin cycle.length := fun n =>
    ⟨n % cycle.length, Nat.mod_lt n cycle.positive⟩
  let edgeAt : Nat -> V × V := fun n =>
    (cycle.vertex (indexAt n), cycle.vertex (cycle.next (indexAt n)))
  have hedge : forall n, edgeAt n ∈ R.finalEdge := by
    intro n
    apply hcycle
    exact ⟨indexAt n, rfl⟩
  let stageAt : Nat -> I := fun n =>
    Classical.choose (Set.mem_iUnion.1 (hedge n))
  have hstageAt : forall n, edgeAt n ∈ R.stageRealEdge (stageAt n) := by
    intro n
    exact Classical.choose_spec (Set.mem_iUnion.1 (hedge n))
  obtain ⟨j, hj⟩ := R.countably_bounded stageAt
  apply R.stageFullEdge_not_containsDirectedCycle j
  refine ⟨cycle, ?_⟩
  rintro e ⟨i, rfl⟩
  have hindex : indexAt i.1 = i := by
    apply Fin.ext
    change i.1 % cycle.length = i.1
    exact Nat.mod_eq_of_lt i.2
  have hreal : edgeAt i.1 ∈ R.stageRealEdge j :=
    R.stageRealEdge_mono (hj i.1) (hstageAt i.1)
  simpa only [stageFullEdge, edgeAt, hindex] using hreal.1

/-- The other local ray invariant also survives the cofinal union.  A final
forward ray is not excluded: original edges may themselves be strong
imaginary edges.  Instead, all of its countably many edges are localized at
one transaction, whose `every_relation_ray_strong` field proves that the
ray has infinitely many strong indices. -/
theorem finalEdge_every_relation_ray_strong
    (R : CofinalClubStageRun C I)
    (r : DirectedPath.Ray (imaginaryGraph Gamma Y kappa))
    (hr : r.edgeSet ⊆ R.finalEdge) :
    (strongEdgeIndices r).Infinite := by
  let edgeAt : Nat -> V × V := fun n => (r n, r (n + 1))
  have hedge : forall n, edgeAt n ∈ R.finalEdge := by
    intro n
    apply hr
    exact ⟨n, rfl⟩
  let stageAt : Nat -> I := fun n =>
    Classical.choose (Set.mem_iUnion.1 (hedge n))
  have hstageAt : forall n, edgeAt n ∈ R.stageRealEdge (stageAt n) := by
    intro n
    exact Classical.choose_spec (Set.mem_iUnion.1 (hedge n))
  obtain ⟨j, hj⟩ := R.countably_bounded stageAt
  apply (R.data j).every_relation_ray_strong r
  rintro e ⟨n, rfl⟩
  have hreal : edgeAt n ∈ R.stageRealEdge j :=
    R.stageRealEdge_mono (hj n) (hstageAt n)
  exact hreal.1

/-- The predecessor relation of the final union is well-founded. -/
def predecessorWellFounded (R : CofinalClubStageRun C I) :
    WellFounded (fun x y => (x, y) ∈ R.finalEdge) :=
  ForwardOrientation.predecessor_wellFounded R.finalEdge
    R.finalEdge_not_containsDirectedCycle
    R.finalEdge_not_containsReverseDirectedRay

/-- The global depth is derived from the final union; it is not an assumed
agreement between unrelated local ranks. -/
def globalRank (R : CofinalClubStageRun C I) : V -> Nat :=
  ForwardOrientation.wellFoundedDepth R.finalEdge
    R.predecessorWellFounded

theorem globalRank_step (R : CofinalClubStageRun C I)
    {x y : V} (hxy : (x, y) ∈ R.finalEdge) :
    R.globalRank y = R.globalRank x + 1 := by
  exact ForwardOrientation.wellFoundedDepth_step R.finalEdge
    R.finalEdge_biunique R.predecessorWellFounded hxy

theorem globalRank_strict (R : CofinalClubStageRun C I)
    {x y : V} (hxy : (x, y) ∈ R.finalEdge) :
    R.globalRank x < R.globalRank y := by
  rw [R.globalRank_step hxy]
  exact Nat.lt_succ_self _

theorem finalEdge_real (R : CofinalClubStageRun C I) :
    R.finalEdge ⊆ {e | Gamma.graph.Adj e.1 e.2} := by
  intro e he
  obtain ⟨i, hi⟩ := Set.mem_iUnion.1 he
  exact hi.2

/-- The cofinal stage run produces the exact one-relation scheduler input.
The rank field is the canonical depth of the final well-founded relation. -/
def rankedFairGlobalRelation (R : CofinalClubStageRun C I) :
    CardinalInduction.HalfwayScheduler.RankedFairGlobalRelation
      Gamma Y kappa Gamma.target I where
  edge := R.finalEdge
  carrier := R.finalCarrier
  rank := R.globalRank
  endpoints_mem := fun _e he => R.finalEdge_endpoints he
  biunique := R.finalEdge_biunique
  rank_step := fun hxy => R.globalRank_strict hxy
  edge_real := R.finalEdge_real
  scheduled := R.scheduled
  fair := by
    intro x hx hno htarget
    exact R.fair x hx hno htarget
  targetPath := fun i => (R.data i).target_path
  targetPath_start := fun i => (R.data i).target_path_start
  targetPath_finish := fun i => (R.data i).target_path_finish
  targetPath_vertices := fun i => R.targetPath_support_subset_finalCarrier i
  targetPath_edges := fun i => R.targetPath_edges_subset_finalEdge i

/-- The orientation constructed from the final well-founded relation has
exactly the surviving real-edge union. -/
theorem rankedFairGlobalRelation_orientation_edge
    (R : CofinalClubStageRun C I) :
    R.rankedFairGlobalRelation.oriented.orientation.edge = R.finalEdge :=
  R.rankedFairGlobalRelation.oriented.edge_eq

/-- It also retains every carrier vertex, including vertices isolated in
the final relation. -/
theorem rankedFairGlobalRelation_orientation_carrier
    (R : CofinalClubStageRun C I) :
    R.rankedFairGlobalRelation.oriented.orientation.carrier =
      R.finalCarrier :=
  R.rankedFairGlobalRelation.oriented.carrier_eq

/-- The canonical root-orbit blueprint inherits the source's forward-ray
condition.  Forward rays are allowed, but the cofinal localization theorem
shows that each still has infinitely many strong imaginary edges. -/
theorem rankedFairGlobalRelation_infinitelyManyStrong
    (R : CofinalClubStageRun C I) :
    (orientationBlueprint
      R.rankedFairGlobalRelation.oriented.orientation)
        |>.InfinitelyManyStrongEdges := by
  intro r hr
  apply R.finalEdge_every_relation_ray_strong r
  intro e he
  have heBlueprint : e ∈
      (orientationBlueprint
        R.rankedFairGlobalRelation.oriented.orientation).edgeSet := by
    simp only [LinkageBlueprint.edgeSet, Set.mem_iUnion]
    exact ⟨Sum.inr r, hr, he⟩
  rw [orientationBlueprint_edgeSet,
    R.rankedFairGlobalRelation_orientation_edge] at heBlueprint
  exact heBlueprint

/-- A construction-specific proof that no surviving edge is strong turns
the localized strong-ray invariant into genuine absence of forward rays.

This is intentionally not a field of `CofinalClubStageRun`: original graph
edges can also be strong imaginary edges, so the premise must come from the
particular macro transaction or provenance filter used by the scheduler. -/
theorem finalEdge_not_containsDirectedRay_of_no_strong_edge
    (R : CofinalClubStageRun C I)
    (hnoStrong : ∀ {x y}, (x, y) ∈ R.finalEdge →
      ¬ IsStrongImaginaryEdge Gamma Y kappa x y) :
    ¬ ContainsDirectedRay R.finalEdge := by
  apply R.rankedFairGlobalRelation.no_directedRay_of_no_strong_edge
  · exact R.finalEdge_every_relation_ray_strong
  · exact hnoStrong

end CofinalClubStageRun

end LinkageBlueprint
end Blueprint
end Erdos599
