import ErdosProblems.Erdos1105.CycleCut

namespace Erdos1105

open SimpleGraph

/-- A support-aware version of cutting a cycle at a prescribed edge. -/
theorem cycle_path_avoiding_dart {V : Type*} [DecidableEq V] {G : SimpleGraph V} {u : V}
    (p : G.Walk u u) (hp : p.IsCycle) (d : G.Dart) (hd : d ∈ p.darts) :
    ∃ q : G.Walk d.snd d.fst, q.IsPath ∧ q.length + 1 = p.length ∧
      q.support ⊆ p.support ∧ q.edges ⊆ p.edges ∧ d.edge ∉ q.edges := by
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
  refine ⟨r.tail.copy hsnd rfl, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [Walk.isPath_copy] using hr.isPath_tail
  · rw [Walk.length_copy, Walk.length_tail_add_one hr.not_nil]
    exact p.length_rotate _ _
  · intro x hx
    rw [Walk.support_copy] at hx
    have hrr : r.IsSubwalk r := by rfl
    have hxr := hrr.tail.support_subset hx
    exact (p.mem_support_rotate_iff _ _).mp hxr
  · intro e he
    rw [Walk.edges_copy] at he
    have hrr : r.IsSubwalk r := by rfl
    exact (p.rotate_edges _ _).perm.mem_iff.mp (hrr.tail.edges_subset he)
  · simpa only [Walk.edges_copy, hsnd, Dart.edge] using hnot

/-- Starting at any cycle vertex and cutting the last edge gives a
path using all the cycle's vertices and only its edges. -/
theorem cycle_path_from_vertex {V : Type*} [DecidableEq V] {G : SimpleGraph V} {u x : V}
    (p : G.Walk u u) (hp : p.IsCycle) (hx : x ∈ p.support) :
    ∃ y, ∃ q : G.Walk x y, q.IsPath ∧ q.length + 1 = p.length ∧
      q.support ⊆ p.support ∧ q.edges ⊆ p.edges := by
  let r := p.rotate x hx
  have hr : r.IsCycle := hp.rotate _
  refine ⟨r.penultimate, r.dropLast, hr.isPath_dropLast, ?_, ?_, ?_⟩
  · rw [Walk.length_dropLast, p.length_rotate]
    have h := hp.three_le_length
    omega
  · intro y hy
    have hrr : r.IsSubwalk r := by rfl
    exact (p.mem_support_rotate_iff _ _).mp (hrr.dropLast.support_subset hy)
  · intro e he
    have hrr : r.IsSubwalk r := by rfl
    exact (p.rotate_edges _ _).perm.mem_iff.mp (hrr.dropLast.edges_subset he)

end Erdos1105

#print axioms Erdos1105.cycle_path_avoiding_dart
