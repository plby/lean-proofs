import ErdosProblems.Erdos73.OddCycleWalks
import ErdosProblems.Erdos73.GraphPaths

/-! The two arcs between distinct vertices of an odd cycle have opposite parity. -/

namespace Erdos73
noncomputable section
open scoped Classical

open SimpleGraph Finset Erdos73Infrastructure.SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

theorem IsOddCycleSubgraph.exists_oppositeParity_paths {H : G.Subgraph}
    (hH : IsOddCycleSubgraph H) {a b : V} (ha : a ∈ H.verts) (hb : b ∈ H.verts) (hab : a ≠ b) :
    ∃ L R : GraphPath G, L.source = a ∧ L.target = b ∧ R.source = a ∧ R.target = b ∧
      L.vertexSet ⊆ H.verts.toFinset ∧ R.vertexSet ⊆ H.verts.toFinset ∧
      Odd (L.walk.length + R.walk.length) := by
  obtain ⟨v, c, hc, ho, hsupport⟩ := hH.exists_cycleWalk
  have haC : a ∈ c.support := List.mem_toFinset.mp
    (show a ∈ (c.support.toFinset : Set V) from hsupport.symm ▸ ha)
  have hbC : b ∈ c.support := List.mem_toFinset.mp
    (show b ∈ (c.support.toFinset : Set V) from hsupport.symm ▸ hb)
  let d := c.rotate a haC
  have hd : d.IsCycle := hc.rotate haC
  have hbD : b ∈ d.support := (c.mem_support_rotate_iff a haC).mpr hbC
  have hdSupport : ∀ x ∈ d.support, x ∈ H.verts := by
    intro x hx
    have hh : x ∈ c.support := (c.mem_support_rotate_iff a haC).mp hx
    exact hsupport ▸ List.mem_toFinset.mpr hh
  have hright : (d.dropUntil b hbD).IsPath :=
    Walk.IsCycle.isPath_of_append_right (p := d.takeUntil b hbD) (Walk.not_nil_of_ne hab)
      (by simpa only [Walk.take_spec] using hd)
  let L : GraphPath G := ⟨a, b, d.takeUntil b hbD, hd.isPath_takeUntil hbD⟩
  let R : GraphPath G := ⟨a, b, (d.dropUntil b hbD).reverse, hright.reverse⟩
  refine ⟨L, R, rfl, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · intro x hx
    exact Set.mem_toFinset.mpr (hdSupport x (d.support_takeUntil_subset hbD (List.mem_toFinset.mp hx)))
  · intro x hx
    have hx' : x ∈ (d.dropUntil b hbD).support := by
      simpa only [R, GraphPath.vertexSet, List.mem_toFinset, Walk.support_reverse,
        List.mem_reverse] using hx
    exact Set.mem_toFinset.mpr (hdSupport x (d.support_dropUntil_subset hbD hx'))
  · have hsum := congrArg Walk.length (d.take_spec hbD)
    have hlen : L.walk.length + R.walk.length = c.length := by
      simpa only [L, R, Walk.length_reverse, Walk.length_append, d, Walk.length_rotate] using hsum
    rw [hlen]
    exact ho

end
end Erdos73
