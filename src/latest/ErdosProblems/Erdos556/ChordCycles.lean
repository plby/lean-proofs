import ErdosProblems.Erdos556.IndexedCycles
import ErdosProblems.Erdos556.ClosingPaths

/-! The short cycles forced by one chord or by two interlaced chords. -/

namespace Erdos556

open SimpleGraph

theorem exists_cycle_of_path_and_edge {V : Type*} {G : SimpleGraph V} {u v : V}
    (p : G.Walk u v) (hp : p.IsPath) (hlen : 2 ≤ p.length) (h : G.Adj u v) :
    ∃ c : G.Walk u u, c.IsCycle ∧ c.length = p.length + 1 := by
  let q : G.Walk u v := Walk.cons h Walk.nil
  have hq : q.IsPath := by simp [q, h.ne]
  refine ⟨p.append q.reverse, ?_, ?_⟩
  · apply isCycle_append_reverse_of_support_inter p q hp hq (by omega)
    intro x _ hx
    simpa only [q, Walk.support_cons, Walk.support_nil, List.mem_cons,
      List.mem_singleton, List.not_mem_nil, or_false] using hx
  · simp [q]

theorem pathSegment_isPath_of_isCycle {V : Type*} {G : SimpleGraph V} {v : V}
    (c : G.Walk v v) (hc : c.IsCycle) (i j : ℕ) (hij : i ≤ j) (hj : j < c.length) :
    (pathSegment c i j hij).IsPath := by
  by_cases hi : i = 0
  · subst i
    apply Walk.IsPath.mk'
    have hnodup := (hc.isPath_take hj).support_nodup
    simpa only [pathSegment, Walk.support_copy, Walk.support_take,
      Walk.drop_support_eq_support_drop_min, Nat.zero_min, List.drop_zero, Nat.sub_zero] using hnodup
  · simpa only [pathSegment, Walk.isPath_copy] using
      (hc.isPath_drop (by omega : 0 < i)).take (j - i)

theorem exists_cycle_of_chord_inside {V : Type*} {G : SimpleGraph V} {v : V}
    (c : G.Walk v v) (hc : c.IsCycle) (i j : ℕ) (hij : i + 2 ≤ j) (hj : j < c.length)
    (h : G.Adj (c.getVert i) (c.getVert j)) :
    ∃ (w : V) (q : G.Walk w w), q.IsCycle ∧ q.length = j - i + 1 := by
  obtain ⟨q, hq, hlen⟩ := exists_cycle_of_path_and_edge
    (pathSegment c i j (by omega)) (pathSegment_isPath_of_isCycle c hc i j (by omega) hj)
    (by rw [pathSegment_length c i j (by omega) hj.le]; omega) h
  exact ⟨_, q, hq, by simpa only [pathSegment_length c i j (by omega) hj.le] using hlen⟩

theorem exists_cycle_of_chord_outside {V : Type*} {G : SimpleGraph V} {v : V}
    (c : G.Walk v v) (hc : c.IsCycle) (i j : ℕ) (hij : i < j) (hj : j < c.length)
    (hgap : j + 2 ≤ c.length + i) (h : G.Adj (c.getVert i) (c.getVert j)) :
    ∃ (w : V) (q : G.Walk w w), q.IsCycle ∧ q.length = c.length - j + i + 1 := by
  obtain ⟨q, hq, hlen⟩ := exists_cycle_of_path_and_edge
    (cycleOutsideArc c i j) (cycleOutsideArc_isPath c hc i j hij hj.le)
    (by rw [cycleOutsideArc_length c i j (by omega)]; omega) h.symm
  exact ⟨_, q, hq, by simpa only [cycleOutsideArc_length c i j (by omega)] using hlen⟩

theorem complement_adj_of_short_chord {V : Type*} {G : SimpleGraph V} {v : V}
    (c : G.Walk v v) (hc : c.IsCycle) (hm : 4 ≤ c.length)
    (hno : ¬ cycleGraph (c.length - 1) ⊑ G)
    (i j : ℕ) (hij : i < j) (hj : j < c.length)
    (hshort : j = i + 2 ∨ j + 2 = c.length + i) :
    Gᶜ.Adj (c.getVert i) (c.getVert j) := by
  rw [compl_adj]
  refine ⟨?_, ?_⟩
  · intro h
    have heq := hc.getVert_injOn' (by change i ≤ c.length - 1; omega)
      (by change j ≤ c.length - 1; omega) h
    omega
  · intro h
    apply hno
    apply (cycleGraph_isContained_iff (by omega : 2 < c.length - 1)).mpr
    rcases hshort with hshort | hshort
    · obtain ⟨w, q, hq, hlen⟩ := exists_cycle_of_chord_outside c hc i j hij hj (by omega) h
      exact ⟨w, q, hq, by omega⟩
    · obtain ⟨w, q, hq, hlen⟩ := exists_cycle_of_chord_inside c hc i j (by omega) hj h
      exact ⟨w, q, hq, by omega⟩

def reverseSkipIndex (j k : ℕ) : ℕ := if k = 0 then 0 else if k < j then j + 1 - k else k + 1

theorem reverseSkipIndex_lt (m j k : ℕ) (hj : 2 ≤ j) (hjm : j + 1 < m) (hk : k < m - 1) :
    reverseSkipIndex j k < m := by
  unfold reverseSkipIndex
  split_ifs <;> omega

theorem reverseSkipIndex_injective (j : ℕ) (hj : 2 ≤ j) : Function.Injective (reverseSkipIndex j) := by
  intro a b h
  unfold reverseSkipIndex at h
  split_ifs at h <;> omega

theorem exists_cycle_of_two_chords_skip_one {V : Type*} {G : SimpleGraph V} {v : V}
    (c : G.Walk v v) (hc : c.IsCycle) (j : ℕ) (hj : 2 ≤ j) (hjm : j + 1 < c.length)
    (hfirst : G.Adj (c.getVert 0) (c.getVert j))
    (hsecond : G.Adj (c.getVert 2) (c.getVert (j + 1))) :
    ∃ (w : V) (q : G.Walk w w), q.IsCycle ∧ q.length = c.length - 1 := by
  apply exists_cycle_of_indexed_vertices G (c.length - 1) (by omega)
    (fun k => c.getVert (reverseSkipIndex j k))
  · intro a ha b hb hab
    apply reverseSkipIndex_injective j hj
    apply hc.getVert_injOn' _ _ hab
    · change reverseSkipIndex j a ≤ c.length - 1
      have h := reverseSkipIndex_lt c.length j a hj hjm ha
      omega
    · change reverseSkipIndex j b ≤ c.length - 1
      have h := reverseSkipIndex_lt c.length j b hj hjm hb
      omega
  · intro k hk
    by_cases hk0 : k = 0
    · subst k
      simpa [reverseSkipIndex, show 1 < j by omega] using hfirst
    by_cases hkj : k + 1 < j
    · have hstep := (c.adj_getVert_succ (by omega : j - k < c.length)).symm
      have h₁ : reverseSkipIndex j k = j - k + 1 := by unfold reverseSkipIndex; split_ifs <;> omega
      have h₂ : reverseSkipIndex j (k + 1) = j - k := by simp [reverseSkipIndex, hkj]
      simpa only [h₁, h₂] using hstep
    by_cases hke : k + 1 = j
    · have h₁ : reverseSkipIndex j k = 2 := by unfold reverseSkipIndex; split_ifs <;> omega
      have h₂ : reverseSkipIndex j (k + 1) = j + 1 := by unfold reverseSkipIndex; split_ifs <;> omega
      simpa only [h₁, h₂] using hsecond
    · have h₁ : reverseSkipIndex j k = k + 1 := by unfold reverseSkipIndex; split_ifs <;> omega
      have h₂ : reverseSkipIndex j (k + 1) = (k + 1) + 1 := by unfold reverseSkipIndex; split_ifs <;> omega
      simpa only [h₁, h₂] using c.adj_getVert_succ (by omega : k + 1 < c.length)
  · have hlast : reverseSkipIndex j (c.length - 1 - 1) = c.length - 1 := by
      unfold reverseSkipIndex
      split_ifs <;> omega
    have hstep := c.adj_getVert_succ (by omega : c.length - 1 < c.length)
    have hlen : c.length - 1 + 1 = c.length := by omega
    have hzero : reverseSkipIndex j 0 = 0 := by simp [reverseSkipIndex]
    rw [hlast, hzero]
    simpa only [hlen, Walk.getVert_length, Walk.getVert_zero] using hstep

#print axioms exists_cycle_of_two_chords_skip_one

end Erdos556
