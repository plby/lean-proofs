/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos916.AHTTriangle

/-!
# The connectivity input to the AHT triangle obstruction

This file develops the two-connected path fact used in AHT Lemma 6.1.  Two
vertex-disjoint paths whose far ends are adjacent splice to a simple path
through either far end.  Finite vertex Menger then supplies those paths in a
two-connected graph.
-/

attribute [local instance] Classical.propDecidable

namespace Erdos916

open SimpleGraph

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Two disjoint paths with adjacent far ends splice to a simple path between
their near ends, passing through both far ends. -/
theorem exists_path_through_of_disjoint_paths_adj
    {a b c d : V} {p : G.Walk a c} {q : G.Walk b d}
    (hp : p.IsPath) (hq : q.IsPath)
    (hdisj : Disjoint {v | v ∈ p.support} {v | v ∈ q.support})
    (hcd : G.Adj c d) :
    ∃ r : G.Walk a b, r.IsPath ∧ c ∈ r.support ∧ d ∈ r.support := by
  have hd_not_p : d ∉ p.support := by
    intro hd
    exact Set.disjoint_left.mp hdisj hd q.end_mem_support
  have hc_not_q : c ∉ q.support := by
    intro hc
    exact Set.disjoint_left.mp hdisj p.end_mem_support hc
  let p' : G.Walk a d := p.concat hcd
  have hp' : p'.IsPath := hp.concat hd_not_p hcd
  have hsupp_disj : p'.support.Disjoint q.reverse.support.tail := by
    rw [List.disjoint_left]
    intro z hzp hzq
    have hzq_full : z ∈ q.support := by
      have : z ∈ q.reverse.support := List.mem_of_mem_tail hzq
      simpa only [SimpleGraph.Walk.support_reverse, List.mem_reverse] using this
    have hzp_cases : z ∈ p.support ∨ z = d := by
      simpa only [p', SimpleGraph.Walk.support_concat, List.mem_append,
        List.mem_singleton] using hzp
    rcases hzp_cases with hzp | rfl
    · exact Set.disjoint_left.mp hdisj hzp hzq_full
    · have hnodup : q.reverse.support.Nodup := hq.reverse.support_nodup
      rw [← q.reverse.cons_tail_support] at hnodup
      exact (List.nodup_cons.mp hnodup).1 hzq
  let r : G.Walk a b := p'.append q.reverse
  have hr : r.IsPath := by
    change (p'.append q.reverse).IsPath
    rw [SimpleGraph.Walk.isPath_def, SimpleGraph.Walk.support_append,
      List.nodup_append']
    exact ⟨hp'.support_nodup, hq.reverse.support_nodup.tail, hsupp_disj⟩
  have hc_mem : c ∈ r.support := by
    simp only [r, SimpleGraph.Walk.support_append, List.mem_append,
      p', SimpleGraph.Walk.support_concat, List.mem_singleton]
    exact Or.inl (Or.inl p.end_mem_support)
  have hd_mem : d ∈ r.support := by
    simp [r, p']
  exact ⟨r, hr, hc_mem, hd_mem⟩

end Erdos916
