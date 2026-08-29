/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingSelectedRootPrefix

/-!
# Why the initial selected root does not determine the request-exit root

An alternating switch transfers the suffix following a backward link to the
root of the ladder path which owns that link.  Consequently a root prefix
ending at the *initial* vertex of a selected route does not, by itself, give
reachability to the route's terminal.

The five-vertex relation below is the smallest useful audit of this issue.
After the initial rooted prefix `0 -> 1`, the alternating traversal is

`1 --forward--> 3 --backward along 2 -> 3--> 2 --forward--> 4`.

The base has the two rooted paths `0 -> 1` (with the route attached at `1`;
the first displayed forward run is `1 -> 3`) and `2 -> 3`.  Switching deletes
`2 -> 3` and inserts `1 -> 3` and `2 -> 4`.  Thus the initial root `0` reaches
the route initial and then `3`, while the request exit `4` is reached from the
other root `2`.  If `2` is the stationary ``unused'' root, there is no allowed
root for the request exit.

This is a relation-level obstruction, not a counterexample to the final
grounding theorem.  It pinpoints the missing decoder statement needed there:
the owner of the last backward link (or, equivalently, the actual switched
component root of the request exit) must be proved different from the unused
grounded record.
-/

noncomputable section

open Set

namespace Erdos599
namespace GroundingSelectedRootPrefixObstruction

abbrev Vertex := Fin 5

/-- The two pre-switch rooted ladder edges. -/
def baseEdges : Set (Vertex × Vertex) :=
  {(0, 1), (2, 3)}

/-- The ladder edge traversed backwards by the alternating route. -/
def backwardEdges : Set (Vertex × Vertex) :=
  {(2, 3)}

/-- The two forward runs of the alternating route. -/
def forwardEdges : Set (Vertex × Vertex) :=
  {(1, 3), (2, 4)}

/-- The literal delete-backward/add-forward switch. -/
def switchedEdges : Set (Vertex × Vertex) :=
  (baseEdges \ backwardEdges) ∪ forwardEdges

/-- The switched relation has exactly three edges. -/
theorem switchedEdges_eq :
    switchedEdges = {(0, 1), (1, 3), (2, 4)} := by
  ext e
  rcases e with ⟨x, y⟩
  simp only [switchedEdges, baseEdges, backwardEdges, forwardEdges,
    Set.mem_union, Set.mem_sdiff, Set.mem_insert_iff,
    Set.mem_singleton_iff, Prod.mk.injEq]
  aesop

/-- The selected initial root still reaches the selected route initial. -/
theorem initialRoot_reaches_routeInitial :
    Relation.ReflTransGen
      (fun x y ↦ (x, y) ∈ switchedEdges) 0 1 := by
  exact Relation.ReflTransGen.single (by
    rw [switchedEdges_eq]
    simp)

/-- The request exit is instead attached to the owner of the backward link. -/
theorem backwardOwnerRoot_reaches_requestExit :
    Relation.ReflTransGen
      (fun x y ↦ (x, y) ∈ switchedEdges) 2 4 := by
  exact Relation.ReflTransGen.single (by
    rw [switchedEdges_eq]
    simp)

private def InInitialComponent (x : Vertex) : Prop :=
  x = 0 ∨ x = 1 ∨ x = 3

private theorem inInitialComponent_of_edge
    {x y : Vertex} (hxy : (x, y) ∈ switchedEdges)
    (hx : InInitialComponent x) : InInitialComponent y := by
  rw [switchedEdges_eq] at hxy
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at hxy
  rcases hxy with hxy | hxy | hxy <;>
    rcases hxy with ⟨rfl, rfl⟩ <;>
    simp [InInitialComponent] at hx ⊢

private theorem inInitialComponent_of_reachable
    {x y : Vertex}
    (hxy : Relation.ReflTransGen
      (fun u v ↦ (u, v) ∈ switchedEdges) x y)
    (hx : InInitialComponent x) : InInitialComponent y := by
  induction hxy with
  | refl => exact hx
  | tail _ hyz ih => exact inInitialComponent_of_edge hyz ih

/-- Excluding the actual backward-link owner leaves no source root for the
request exit, even though the other source has the required initial prefix. -/
theorem requestExit_has_no_root_after_excluding_backwardOwner :
    ¬ ∃ a ∈ ({0, 2} : Set Vertex) \ {2},
      Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈ switchedEdges) a 4 := by
  rintro ⟨a, ha, hreach⟩
  have ha0 : a = 0 := by
    simpa using ha
  subst a
  have hcomponent : InInitialComponent 4 :=
    inInitialComponent_of_reachable hreach (by
      simp [InInitialComponent])
  simp [InInitialComponent] at hcomponent

end GroundingSelectedRootPrefixObstruction
end Erdos599
