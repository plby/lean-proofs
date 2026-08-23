import ErdosProblems.Erdos1105.ThreePathCycle

namespace Erdos1105

open SimpleGraph

/-- A chord between two middle positions, with the preceding positions
joined to opposite endpoints, closes a cycle through the whole path. -/
theorem cycle_of_middle_chord {V : Type*} {G : SimpleGraph V} {x y : V}
    (p : G.Walk x y) (hp : p.IsPath) {i j : ℕ}
    (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ p.length)
    (hyi : G.Adj y (p.getVert (i - 1)))
    (hxj : G.Adj x (p.getVert (j - 1))) (hijAdj : G.Adj (p.getVert i) (p.getVert j)) :
    ∃ v, ∃ s : G.Walk v v, s.IsCycle ∧ s.length = p.length + 1 := by
  let r := pathSegment p i (j - 1) (by omega)
  have hpq := path_prefix_suffix_disjoint p hp (by omega : i - 1 < j) hj
  have hpr : (p.take (i - 1)).support.Disjoint r.support := by
    intro w hw₁ hw₂
    obtain ⟨a, ha, hai⟩ := Walk.mem_support_iff_exists_getVert.mp hw₁
    have hai' : a ≤ i - 1 := by rw [Walk.take_length] at hai; omega
    have hae : p.getVert a = w := by
      simpa only [Walk.take_getVert, Nat.min_eq_right hai'] using ha
    obtain ⟨b, hib, hbj, hbe⟩ := (mem_pathSegment_support p i (j - 1) (by omega) (by omega)).mp hw₂
    have := hp.getVert_injOn (show a ≤ p.length by omega) (show b ≤ p.length by omega)
      (hae.trans hbe.symm)
    omega
  have hqr : (p.drop j).reverse.support.Disjoint r.support := by
    intro w hw₁ hw₂
    have hw₁' : w ∈ (p.drop j).support := by simpa using hw₁
    obtain ⟨a, ha, hai⟩ := Walk.mem_support_iff_exists_getVert.mp hw₁'
    have hja : j + a ≤ p.length := by rw [Walk.drop_length] at hai; omega
    have hae : p.getVert (j + a) = w := by simpa only [Walk.drop_getVert] using ha
    obtain ⟨b, hib, hbj, hbe⟩ := (mem_pathSegment_support p i (j - 1) (by omega) (by omega)).mp hw₂
    have := hp.getVert_injOn hja (show b ≤ p.length by omega) (hae.trans hbe.symm)
    omega
  obtain ⟨s, hs, hlen⟩ := cycle_of_three_disjoint_paths (p.take (i - 1)) (p.drop j).reverse r
    (hp.take _) (hp.drop _).reverse (pathSegment_isPath p hp _ _ _)
    (by simpa using hpq) hpr hqr hyi.symm hijAdj.symm hxj.symm
  refine ⟨p.getVert (j - 1), s, hs, ?_⟩
  have hrlen : r.length = j - 1 - i := pathSegment_length p _ _ _ (by omega)
  rw [Walk.take_length, Nat.min_eq_left (by omega : i - 1 ≤ p.length),
    Walk.length_reverse, Walk.drop_length, hrlen] at hlen
  omega

end Erdos1105

#print axioms Erdos1105.cycle_of_middle_chord
