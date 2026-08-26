import ErdosProblems.Erdos556.PathOperations

/-!
# Supports of indexed path segments

The prefix and suffix descriptions keep index inequalities explicit,
which is useful when rerouting a path without introducing repeated vertices.
-/

namespace Erdos556

open SimpleGraph

theorem mem_support_take_iff {V : Type*} {G : SimpleGraph V} {u v x : V}
    (p : G.Walk u v) (i : ℕ) (hi : i ≤ p.length) :
    x ∈ (p.take i).support ↔ ∃ j, j ≤ i ∧ p.getVert j = x := by
  constructor
  · intro hx
    obtain ⟨j, hjx, hj⟩ := Walk.mem_support_iff_exists_getVert.mp hx
    have hj' : j ≤ i := by simpa only [Walk.take_length, min_eq_left hi] using hj
    refine ⟨j, hj', ?_⟩
    simpa only [Walk.take_getVert, inf_eq_right.mpr hj'] using hjx
  · rintro ⟨j, hj, hjx⟩
    apply Walk.mem_support_iff_exists_getVert.mpr
    refine ⟨j, ?_, ?_⟩
    · simpa only [Walk.take_getVert, inf_eq_right.mpr hj] using hjx
    · simpa only [Walk.take_length, min_eq_left hi] using hj

theorem mem_support_drop_iff {V : Type*} {G : SimpleGraph V} {u v x : V}
    (p : G.Walk u v) (i : ℕ) (hi : i ≤ p.length) :
    x ∈ (p.drop i).support ↔ ∃ j, i ≤ j ∧ j ≤ p.length ∧ p.getVert j = x := by
  constructor
  · intro hx
    obtain ⟨j, hjx, hj⟩ := Walk.mem_support_iff_exists_getVert.mp hx
    rw [Walk.drop_length] at hj
    refine ⟨i + j, by omega, by omega, ?_⟩
    simpa only [Walk.drop_getVert] using hjx
  · rintro ⟨j, hij, hj, hjx⟩
    apply Walk.mem_support_iff_exists_getVert.mpr
    refine ⟨j - i, ?_, ?_⟩
    · simpa only [Walk.drop_getVert, Nat.add_sub_of_le hij] using hjx
    · rw [Walk.drop_length]
      omega

theorem disjoint_support_take_drop {V : Type*} {G : SimpleGraph V} {u v : V}
    (p : G.Walk u v) (hp : p.IsPath) (i j : ℕ) (hij : i < j) (hj : j ≤ p.length) :
    (p.take i).support.Disjoint (p.drop j).support := by
  rw [List.disjoint_left]
  intro x hx hy
  obtain ⟨a, ha, hax⟩ := (mem_support_take_iff p i (by omega)).mp hx
  obtain ⟨b, hjb, hb, hbx⟩ := (mem_support_drop_iff p j hj).mp hy
  have hab : a = b := hp.getVert_injOn (by change a ≤ p.length; omega) hb (hax.trans hbx.symm)
  omega

#print axioms disjoint_support_take_drop

def pathSegment {V : Type*} {G : SimpleGraph V} {u v : V}
    (p : G.Walk u v) (i j : ℕ) (hij : i ≤ j) : G.Walk (p.getVert i) (p.getVert j) :=
  ((p.drop i).take (j - i)).copy rfl (by
    rw [Walk.drop_getVert, Nat.add_sub_of_le hij])

theorem pathSegment_length {V : Type*} {G : SimpleGraph V} {u v : V}
    (p : G.Walk u v) (i j : ℕ) (hij : i ≤ j) (hj : j ≤ p.length) :
    (pathSegment p i j hij).length = j - i := by
  simp only [pathSegment, Walk.length_copy, Walk.take_length, Walk.drop_length]
  exact min_eq_left (by omega)

theorem pathSegment_isPath {V : Type*} {G : SimpleGraph V} {u v : V}
    (p : G.Walk u v) (hp : p.IsPath) (i j : ℕ) (hij : i ≤ j) :
    (pathSegment p i j hij).IsPath := by
  simpa only [pathSegment, Walk.isPath_copy] using ((hp.drop i).take (j - i))

theorem mem_support_pathSegment_iff {V : Type*} {G : SimpleGraph V} {u v x : V}
    (p : G.Walk u v) (i j : ℕ) (hij : i ≤ j) (hj : j ≤ p.length) :
    x ∈ (pathSegment p i j hij).support ↔
      ∃ a, i ≤ a ∧ a ≤ j ∧ p.getVert a = x := by
  rw [pathSegment, Walk.support_copy]
  have hlen : j - i ≤ (p.drop i).length := by rw [Walk.drop_length]; omega
  rw [mem_support_take_iff (p.drop i) (j - i) hlen]
  constructor
  · rintro ⟨a, ha, hax⟩
    refine ⟨i + a, by omega, by omega, ?_⟩
    simpa only [Walk.drop_getVert] using hax
  · rintro ⟨a, hia, haj, hax⟩
    refine ⟨a - i, by omega, ?_⟩
    simpa only [Walk.drop_getVert, Nat.add_sub_of_le hia] using hax

#print axioms mem_support_pathSegment_iff

end Erdos556
