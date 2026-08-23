import ErdosProblems.Erdos1105.Basic

namespace Erdos1105

open SimpleGraph

/-- Two paths meeting only at the joining endpoint concatenate to a path. -/
theorem isPath_append_of_inter_eq_end {V : Type*} {G : SimpleGraph V}
    {a b c : V} {p : G.Walk a b} {q : G.Walk b c}
    (hp : p.IsPath) (hq : q.IsPath)
    (hinter : ∀ x : V, x ∈ p.support → x ∈ q.support → x = b) :
    (p.append q).IsPath := by
  apply Walk.IsPath.mk'
  rw [Walk.support_append, List.nodup_append']
  refine ⟨hp.support_nodup, hq.support_nodup.tail, ?_⟩
  intro x hxp hxq
  have hxb : x = b := hinter x hxp (List.tail_subset _ hxq)
  subst x
  have hn := hq.support_nodup
  rw [← q.cons_tail_support, List.nodup_cons] at hn
  exact hn.1 hxq

theorem cycle_of_two_disjoint_paths {V : Type*} {G : SimpleGraph V}
    {a b u v : V} (p : G.Walk a b) (q : G.Walk u v)
    (hp : p.IsPath) (hq : q.IsPath) (hdisj : p.support.Disjoint q.support)
    (hbu : G.Adj b u) (hva : G.Adj v a) (hlen : 3 ≤ p.length + q.length + 2) :
    ∃ s : G.Walk v v, s.IsCycle ∧ s.length = p.length + q.length + 2 := by
  let r := p.append (Walk.cons hbu q)
  have hr : r.IsPath := by
    apply Walk.IsPath.mk'
    simp only [r, Walk.support_append, Walk.support_cons, List.tail_cons]
    exact List.nodup_append'.mpr ⟨hp.support_nodup, hq.support_nodup, hdisj⟩
  refine ⟨Walk.cons hva r, ?_, by simp [r]; omega⟩
  apply (Walk.cons_isCycle_iff r hva).mpr
  refine ⟨hr, ?_⟩
  intro he
  have h := hr.length_eq_one_of_mem_edges (Sym2.eq_swap ▸ he)
  simp only [r, Walk.length_append, Walk.length_cons] at h
  omega

theorem path_prefix_suffix_disjoint {V : Type*} {G : SimpleGraph V} {x y : V}
    (p : G.Walk x y) (hp : p.IsPath) {i j : ℕ} (hij : i < j) (hj : j ≤ p.length) :
    (p.take i).support.Disjoint (p.drop j).support := by
  intro z hz₁ hz₂
  obtain ⟨a, ha, hai⟩ := (Walk.mem_support_iff_exists_getVert).mp hz₁
  obtain ⟨b, hb, hbj⟩ := (Walk.mem_support_iff_exists_getVert).mp hz₂
  have hai' : a ≤ i := by
    rw [Walk.take_length] at hai
    omega
  have hbj' : j + b ≤ p.length := by
    rw [Walk.drop_length] at hbj
    omega
  have hae : p.getVert a = z := by
    simpa only [Walk.take_getVert, Nat.min_eq_right hai'] using ha
  have hbe : p.getVert (j + b) = z := by
    simpa only [Walk.drop_getVert] using hb
  have := hp.getVert_injOn (show a ≤ p.length by omega) hbj' (hae.trans hbe.symm)
  omega

theorem cycle_of_crossing_chords {V : Type*} {G : SimpleGraph V} {x y : V}
    (p : G.Walk x y) (hp : p.IsPath) {i j : ℕ}
    (hij : i < j) (hj : j ≤ p.length)
    (hiadj : G.Adj y (p.getVert i)) (hjadj : G.Adj x (p.getVert j))
    (hlen : 3 ≤ i + (p.length - j) + 2) :
    ∃ (v : V) (s : G.Walk v v), s.IsCycle ∧ s.length = i + (p.length - j) + 2 := by
  have hdisj := path_prefix_suffix_disjoint p hp hij hj
  have hdisj' : (p.take i).support.Disjoint (p.drop j).reverse.support := by
    simpa only [Walk.support_reverse, List.disjoint_reverse_right] using hdisj
  have htake : (p.take i).length = i := by rw [Walk.take_length, Nat.min_eq_left (by omega)]
  obtain ⟨s, hs, hslen⟩ := cycle_of_two_disjoint_paths (p.take i) (p.drop j).reverse
    (hp.take i) (hp.drop j).reverse hdisj' hiadj.symm hjadj.symm
    (by simpa only [htake, Walk.length_reverse, Walk.drop_length] using hlen)
  exact ⟨p.getVert j, s, hs, by simpa only [htake, Walk.length_reverse, Walk.drop_length] using hslen⟩

end Erdos1105

#print axioms Erdos1105.cycle_of_crossing_chords
