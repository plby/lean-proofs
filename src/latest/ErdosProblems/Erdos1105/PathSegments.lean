import ErdosProblems.Erdos1105.Basic

namespace Erdos1105

open SimpleGraph

def pathSegment {V : Type*} {G : SimpleGraph V} {x y : V}
    (p : G.Walk x y) (i j : ℕ) (hij : i ≤ j) : G.Walk (p.getVert i) (p.getVert j) :=
  ((p.drop i).take (j - i)).copy rfl (by rw [Walk.drop_getVert, Nat.add_sub_of_le hij])

theorem pathSegment_isPath {V : Type*} {G : SimpleGraph V} {x y : V}
    (p : G.Walk x y) (hp : p.IsPath) (i j : ℕ) (hij : i ≤ j) :
    (pathSegment p i j hij).IsPath := by
  simpa only [pathSegment, Walk.isPath_copy] using (hp.drop i).take (j - i)

theorem pathSegment_length {V : Type*} {G : SimpleGraph V} {x y : V}
    (p : G.Walk x y) (i j : ℕ) (hij : i ≤ j) (hj : j ≤ p.length) :
    (pathSegment p i j hij).length = j - i := by
  simp only [pathSegment, Walk.length_copy, Walk.take_length, Walk.drop_length]
  exact Nat.min_eq_left (by omega)

theorem mem_pathSegment_support {V : Type*} {G : SimpleGraph V} {x y w : V}
    (p : G.Walk x y) (i j : ℕ) (hij : i ≤ j) (hj : j ≤ p.length) :
    w ∈ (pathSegment p i j hij).support ↔ ∃ r, i ≤ r ∧ r ≤ j ∧ p.getVert r = w := by
  simp only [pathSegment, Walk.support_copy]
  constructor
  · intro hw
    obtain ⟨r, hr, hrlen⟩ := Walk.mem_support_iff_exists_getVert.mp hw
    have hrle : r ≤ j - i := by rw [Walk.take_length] at hrlen; omega
    refine ⟨i + r, by omega, by omega, ?_⟩
    simpa only [Walk.take_getVert, Nat.min_eq_right hrle, Walk.drop_getVert] using hr
  · rintro ⟨r, hir, hrj, hr⟩
    apply Walk.mem_support_iff_exists_getVert.mpr
    refine ⟨r - i, ?_, ?_⟩
    · rw [Walk.take_getVert, Nat.min_eq_right (by omega), Walk.drop_getVert,
        Nat.add_sub_of_le hir]
      exact hr
    · rw [Walk.take_length, Walk.drop_length, Nat.min_eq_left (by omega)]
      omega

theorem disjoint_pathSegments {V : Type*} {G : SimpleGraph V} {x y : V}
    (p : G.Walk x y) (hp : p.IsPath) (a b c d : ℕ)
    (hab : a ≤ b) (hbc : b < c) (hcd : c ≤ d) (hd : d ≤ p.length) :
    (pathSegment p a b hab).support.Disjoint (pathSegment p c d hcd).support := by
  intro w hw₁ hw₂
  obtain ⟨i, hai, hib, hi⟩ := (mem_pathSegment_support p a b hab (by omega)).mp hw₁
  obtain ⟨j, hcj, hjd, hj⟩ := (mem_pathSegment_support p c d hcd hd).mp hw₂
  have hij := hp.getVert_injOn (show i ≤ p.length by omega)
    (show j ≤ p.length by omega) (hi.trans hj.symm)
  omega

theorem pathSegment_support_subset {V : Type*} {G : SimpleGraph V} {x y : V}
    (p : G.Walk x y) (i j : ℕ) (hij : i ≤ j) (hj : j ≤ p.length) :
    (pathSegment p i j hij).support ⊆ p.support := by
  intro w hw
  obtain ⟨r, _, _, hr⟩ := (mem_pathSegment_support p i j hij hj).mp hw
  exact hr ▸ p.getVert_mem_support r

theorem getVert_mem_pathSegment {V : Type*} {G : SimpleGraph V} {x y : V}
    (p : G.Walk x y) (hp : p.IsPath) (i j : ℕ) (hij : i ≤ j) (hj : j ≤ p.length)
    (r : ℕ) (hr : r ≤ p.length) :
    p.getVert r ∈ (pathSegment p i j hij).support ↔ i ≤ r ∧ r ≤ j := by
  rw [mem_pathSegment_support p i j hij hj]
  constructor
  · rintro ⟨s, his, hsj, hsr⟩
    have h := hp.getVert_injOn (show s ≤ p.length by omega) hr hsr
    omega
  · rintro ⟨hir, hrj⟩
    exact ⟨r, hir, hrj, rfl⟩

end Erdos1105

#print axioms Erdos1105.disjoint_pathSegments
