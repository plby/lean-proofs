import ErdosProblems.Erdos556.ParityConnections
import ErdosProblems.Erdos556.Reservoir

/-!
# Closing a long path through a reservoir

The support hypotheses ensure that the closing walk is a simple cycle.
A parity connection makes that cycle odd without shortening the long path.
-/

namespace Erdos556

open SimpleGraph

theorem start_not_mem_tail_support_of_isPath {V : Type*} {G : SimpleGraph V}
    {u v : V} (p : G.Walk u v) (hp : p.IsPath) : u ∉ p.support.tail := by
  have h := hp.support_nodup
  rw [← p.cons_tail_support, List.nodup_cons] at h
  exact h.1

theorem isCycle_append_reverse_of_support_inter {V : Type*} {G : SimpleGraph V}
    {u v : V} (p q : G.Walk u v) (hp : p.IsPath) (hq : q.IsPath) (hlen : 1 < p.length)
    (hinter : ∀ x ∈ p.support, x ∈ q.support → x = u ∨ x = v) :
    (p.append q.reverse).IsCycle := by
  apply hp.isCycle_append hq.reverse _ (Or.inl hlen)
  rw [List.disjoint_left]
  intro x hxp hxq
  have hxp' : x ∈ p.support := List.mem_of_mem_tail hxp
  have hxq' : x ∈ q.support := by
    simpa only [Walk.support_reverse, List.mem_reverse] using List.mem_of_mem_tail hxq
  rcases hinter x hxp' hxq' with hxu | hxv
  · exact start_not_mem_tail_support_of_isPath p hp (hxu ▸ hxp)
  · exact start_not_mem_tail_support_of_isPath q.reverse hq.reverse (hxv ▸ hxq)

theorem exists_cycle_of_path_and_connection {V : Type*} {G : SimpleGraph V}
    {u v : V} (p : G.Walk u v) (hp : p.IsPath) (hlen : 1 < p.length)
    (L : ℕ) (R : Finset V) (hav : ∀ x ∈ p.support, x ∉ R)
    (hconn : ShortConnection G L u v R) :
    ∃ c : G.Walk u u, c.IsCycle ∧ p.length ≤ c.length ∧ c.length ≤ p.length + L := by
  obtain ⟨q, hq, hqL, hqR⟩ := hconn
  have hc : (p.append q.reverse).IsCycle := by
    apply isCycle_append_reverse_of_support_inter p q hp hq hlen
    intro x hxp hxq
    by_cases hxu : x = u
    · exact Or.inl hxu
    by_cases hxv : x = v
    · exact Or.inr hxv
    exact (hav x hxp (hqR x hxq hxu hxv)).elim
  refine ⟨p.append q.reverse, hc, ?_, ?_⟩ <;>
    simp only [Walk.length_append, Walk.length_reverse] <;> omega

theorem exists_odd_cycle_of_path_and_parity_connection {V : Type*} {G : SimpleGraph V}
    {u v : V} (p : G.Walk u v) (hp : p.IsPath) (hlen : 1 < p.length)
    (L : ℕ) (R : Finset V) (hav : ∀ x ∈ p.support, x ∉ R)
    (hconn : ParityConnection G L u v R) :
    ∃ c : G.Walk u u, c.IsCycle ∧ Odd c.length ∧
      p.length ≤ c.length ∧ c.length ≤ p.length + L := by
  let r : Fin 2 := ⟨(p.length + 1) % 2, Nat.mod_lt _ (by decide)⟩
  obtain ⟨q, hq, hqL, hqpar, hqR⟩ := hconn r
  have hc : (p.append q.reverse).IsCycle := by
    apply isCycle_append_reverse_of_support_inter p q hp hq hlen
    intro x hxp hxq
    by_cases hxu : x = u
    · exact Or.inl hxu
    by_cases hxv : x = v
    · exact Or.inr hxv
    exact (hav x hxp (hqR x hxq hxu hxv)).elim
  refine ⟨p.append q.reverse, hc, ?_, ?_, ?_⟩
  · apply Nat.odd_iff.mpr
    simp only [Walk.length_append, Walk.length_reverse]
    change q.length % 2 = (p.length + 1) % 2 at hqpar
    omega
  · simp only [Walk.length_append, Walk.length_reverse]
    omega
  · simp only [Walk.length_append, Walk.length_reverse]
    omega

#print axioms exists_odd_cycle_of_path_and_parity_connection

end Erdos556
