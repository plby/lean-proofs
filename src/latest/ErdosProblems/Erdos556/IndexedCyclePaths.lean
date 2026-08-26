import ErdosProblems.Erdos556.PathSegments

/-!
# Indexed complementary arcs of a cycle

Removing an indexed interval leaves a simple complementary path.
The endpoint and support formulas record exactly which vertices of the
removed interval can still occur on that path.
-/

namespace Erdos556

open SimpleGraph

def cycleOutsideArc {V : Type*} {G : SimpleGraph V} {v : V}
    (c : G.Walk v v) (i j : ℕ) : G.Walk (c.getVert j) (c.getVert i) :=
  (c.drop j).append (c.take i)

theorem cycleOutsideArc_length {V : Type*} {G : SimpleGraph V} {v : V}
    (c : G.Walk v v) (i j : ℕ) (hi : i ≤ c.length) :
    (cycleOutsideArc c i j).length = c.length - j + i := by
  simp only [cycleOutsideArc, Walk.length_append, Walk.drop_length,
    Walk.take_length, min_eq_left hi]

theorem cycleOutsideArc_isPath {V : Type*} {G : SimpleGraph V} {v : V}
    (c : G.Walk v v) (hc : c.IsCycle) (i j : ℕ) (hij : i < j) (hj : j ≤ c.length) :
    (cycleOutsideArc c i j).IsPath := by
  apply isPath_append_of_support_inter (c.drop j) (c.take i)
    (hc.isPath_drop (by omega)) (hc.isPath_take (by omega))
  intro x hxd hxt
  obtain ⟨a, hja, ha, hax⟩ := (mem_support_drop_iff c j hj).mp hxd
  obtain ⟨b, hb, hbx⟩ := (mem_support_take_iff c i (by omega)).mp hxt
  by_cases he : a = c.length
  · rw [he, Walk.getVert_length] at hax
    exact hax.symm
  · have hab := hc.getVert_injOn' (by change a ≤ c.length - 1; omega)
      (by change b ≤ c.length - 1; omega) (hax.trans hbx.symm)
    omega

theorem cycleOutsideArc_support_subset {V : Type*} {G : SimpleGraph V} {v x : V}
    (c : G.Walk v v) (i j : ℕ) (hi : i ≤ c.length) (hj : j ≤ c.length)
    (hx : x ∈ (cycleOutsideArc c i j).support) : x ∈ c.support := by
  rcases (Walk.mem_support_append_iff (c.drop j) (c.take i)).mp hx with hxd | hxt
  · obtain ⟨a, _, _, hax⟩ := (mem_support_drop_iff c j hj).mp hxd
    exact hax ▸ c.getVert_mem_support a
  · obtain ⟨a, _, hax⟩ := (mem_support_take_iff c i hi).mp hxt
    exact hax ▸ c.getVert_mem_support a

theorem cycleOutsideArc_meets_interval_only_at_ends {V : Type*} {G : SimpleGraph V} {v : V}
    (c : G.Walk v v) (hc : c.IsCycle) (i j a : ℕ)
    (hia : i ≤ a) (haj : a ≤ j) (hj : j < c.length)
    (ha : c.getVert a ∈ (cycleOutsideArc c i j).support) : a = i ∨ a = j := by
  rcases (Walk.mem_support_append_iff (c.drop j) (c.take i)).mp ha with had | hat
  · obtain ⟨b, hjb, hb, hba⟩ := (mem_support_drop_iff c j hj.le).mp had
    by_cases hbe : b = c.length
    · rw [hbe, Walk.getVert_length] at hba
      have h := (hc.getVert_endpoint_iff (by omega)).mp hba.symm
      left
      omega
    · have hba' := hc.getVert_injOn' (by change b ≤ c.length - 1; omega)
        (by change a ≤ c.length - 1; omega) hba
      right
      omega
  · obtain ⟨b, hbi, hba⟩ := (mem_support_take_iff c i (by omega)).mp hat
    have hba' := hc.getVert_injOn' (by change b ≤ c.length - 1; omega)
      (by change a ≤ c.length - 1; omega) hba
    left
    omega

#print axioms cycleOutsideArc_isPath
#print axioms cycleOutsideArc_meets_interval_only_at_ends

end Erdos556
