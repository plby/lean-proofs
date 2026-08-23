import ErdosProblems.Erdos1105.Basic

namespace Erdos1105

open SimpleGraph

lemma cycle_dart_eq_of_fst_eq {V : Type*} {G : SimpleGraph V} {u : V}
    {p : G.Walk u u} (hp : p.IsCycle) {d e : G.Dart}
    (hd : d ∈ p.darts) (he : e ∈ p.darts) (hfst : d.fst = e.fst) : d = e := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hd
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem he
  have hi' : i < p.support.dropLast.length := by simpa using hi
  have hj' : j < p.support.dropLast.length := by simpa using hj
  have hget : p.support.dropLast[i]'hi' = p.support.dropLast[j]'hj' := by
    simpa [p.fst_darts_getElem hi, p.fst_darts_getElem hj] using hfst
  have hij := (List.Nodup.getElem_inj_iff hp.nodup_dropLast_support).mp hget
  subst j
  rfl

/-- Cutting a cycle at any specified dart preserves all its other edges. -/
theorem path_of_cycle_cut_dart {V : Type*} {G : SimpleGraph V} {u : V}
    (p : G.Walk u u) (hp : p.IsCycle) (d : G.Dart) (hd : d ∈ p.darts) :
    ∃ q : (G.deleteEdges {d.edge}).Walk d.snd d.fst,
      q.IsPath ∧ q.length + 1 = p.length := by
  classical
  let r := p.rotate d.fst (p.dart_fst_mem_support_of_mem_darts hd)
  have hr : r.IsCycle := hp.rotate _
  have hd' : d ∈ r.darts := (p.rotate_darts _ _).mem_iff.mpr hd
  have hfirst : r.firstDart hr.not_nil = d :=
    cycle_dart_eq_of_fst_eq hr (r.firstDart_mem_darts hr.not_nil) hd' rfl
  have hsnd : r.snd = d.snd := congrArg (fun a : G.Dart ↦ a.snd) hfirst
  have hnot : s(d.fst, r.snd) ∉ r.tail.edges := by
    have hn := hr.isTrail.edges_nodup
    have heq := congrArg (fun q : G.Walk d.fst d.fst ↦ q.edges) (r.cons_tail_eq hr.not_nil)
    rw [Walk.edges_cons] at heq
    rw [← heq] at hn
    exact (List.nodup_cons.mp hn).1
  have hsub : ∀ e ∈ r.tail.edges, e ∈ (G.deleteEdges {d.edge}).edgeSet := by
    intro e he
    rw [edgeSet_deleteEdges]
    refine ⟨r.tail.edges_subset_edgeSet he, ?_⟩
    intro hed
    have hed' : e = s(d.fst, r.snd) := by
      simpa only [Set.mem_singleton_iff, hsnd, Dart.edge] using hed
    exact hnot (hed' ▸ he)
  let q := r.tail.transfer (G.deleteEdges {d.edge}) hsub
  refine ⟨q.copy hsnd rfl, ?_, ?_⟩
  · simpa only [Walk.isPath_copy] using hr.isPath_tail.transfer hsub
  simp only [Walk.length_copy, q, Walk.length_transfer]
  rw [Walk.length_tail_add_one hr.not_nil]
  exact p.length_rotate _ _

end Erdos1105

#print axioms Erdos1105.path_of_cycle_cut_dart
