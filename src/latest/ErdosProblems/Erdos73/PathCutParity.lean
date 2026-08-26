import ErdosProblems.Erdos73.GraphPaths

/-! Exact lengths and one-vertex overlap of cuts in simple paths, with parity transfer. -/

namespace Erdos73.GraphPath
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq
open SimpleGraph Finset Erdos73Infrastructure.SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

theorem takeUntil_length_of_getVert_eq (P : GraphPath G) {v : V} (hv : v ∈ P.vertexSet)
    {i : ℕ} (hi : i ≤ P.walk.length) (he : P.walk.getVert i = v) :
    (P.takeUntil hv).walk.length = i := by
  have hv' : v ∈ P.walk.support := List.mem_toFinset.mp hv
  have hl := P.walk.length_takeUntil_le_length hv'
  have hg := Walk.getVert_length_takeUntil hv'
  exact P.isPath.getVert_injOn hl hi (hg.trans he.symm)

theorem dropUntil_length_of_getVert_eq (P : GraphPath G) {v : V} (hv : v ∈ P.vertexSet)
    {i : ℕ} (hi : i ≤ P.walk.length) (he : P.walk.getVert i = v) :
    (P.dropUntil hv).walk.length = P.walk.length - i := by
  have hsum : (P.takeUntil hv).walk.length + (P.dropUntil hv).walk.length = P.walk.length :=
    (_root_.SimpleGraph.Walk.length_append (P.takeUntil hv).walk (P.dropUntil hv).walk).symm.trans
      (congrArg _root_.SimpleGraph.Walk.length (P.takeUntil_append_dropUntil_walk hv))
  rw [takeUntil_length_of_getVert_eq P hv hi he] at hsum
  omega

theorem takeUntil_dropUntil_intersection (P : GraphPath G) {v : V} (hv : v ∈ P.vertexSet)
    {x : V} (hx : x ∈ (P.takeUntil hv).vertexSet) (hx' : x ∈ (P.dropUntil hv).vertexSet) :
    x = v := by
  have hpath : ((P.takeUntil hv).walk.append (P.dropUntil hv).walk).IsPath := by
    rw [P.takeUntil_append_dropUntil_walk hv]
    exact P.isPath
  by_contra hne
  exact hpath.ne_of_mem_support_of_append hne (List.mem_toFinset.mp hx)
    (List.mem_toFinset.mp hx') rfl

theorem odd_parts_of_even_path_odd_cut (P : GraphPath G) {v : V} (hv : v ∈ P.vertexSet)
    {i : ℕ} (hi : i ≤ P.walk.length) (he : P.walk.getVert i = v)
    (hP : Even P.walk.length) (hiodd : Odd i) :
    Odd (P.takeUntil hv).walk.length ∧ Odd (P.dropUntil hv).walk.length := by
  rw [takeUntil_length_of_getVert_eq P hv hi he, dropUntil_length_of_getVert_eq P hv hi he]
  refine ⟨hiodd, ?_⟩
  rw [Nat.even_iff] at hP
  rw [Nat.odd_iff] at hiodd ⊢
  omega

end
end Erdos73.GraphPath
