import ErdosProblems.Erdos1105.ThreePathCycle
import ErdosProblems.Erdos1105.UniversalPath

namespace Erdos1105

open SimpleGraph

/-- A new vertex adjacent to the start and to a later attachment closes
the two outer pieces of a path into a cycle. -/
theorem cycle_of_external_crossing {V : Type*} {G : SimpleGraph V} {x y z : V}
    (p : G.Walk x y) (hp : p.IsPath) {a b : ℕ} (hab : a < b) (hb : b ≤ p.length)
    (hz : z ∉ p.support) (hya : G.Adj y (p.getVert a))
    (hbz : G.Adj (p.getVert b) z) (hzx : G.Adj z x) :
    ∃ s : G.Walk z z, s.IsCycle ∧ s.length = a + (p.length - b) + 3 := by
  have hdisj := path_prefix_suffix_disjoint p hp hab hb
  have hpz : (p.take a).support.Disjoint (Walk.nil : G.Walk z z).support := by
    intro w hw hwz
    have heq : w = z := by simpa using hwz
    exact hz (heq ▸ (p.isSubwalk_take a).support_subset hw)
  have hqz : (p.drop b).reverse.support.Disjoint (Walk.nil : G.Walk z z).support := by
    intro w hw hwz
    have heq : w = z := by simpa using hwz
    have hw' : w ∈ (p.drop b).support := by simpa using hw
    exact hz (heq ▸ (p.isSubwalk_drop b).support_subset hw')
  obtain ⟨s, hs, hlen⟩ := cycle_of_three_disjoint_paths (p.take a) (p.drop b).reverse
    (Walk.nil : G.Walk z z) (hp.take a) (hp.drop b).reverse (by simp)
    (by simpa using hdisj) hpz hqz hya.symm hbz hzx
  refine ⟨s, hs, ?_⟩
  simpa only [Walk.take_length, Nat.min_eq_left (by omega : a ≤ p.length),
    Walk.length_reverse, Walk.drop_length, Walk.length_nil, Nat.add_zero] using hlen

/-- The corresponding cycle when the universal attachment is the
earlier one: bypass it along a chord, and return through it and the new vertex. -/
theorem cycle_of_external_early_attachment {V : Type*} {G : SimpleGraph V} {x y z : V}
    (p : G.Walk x y) (hp : p.IsPath) {a b : ℕ} (ha : 1 ≤ a)
    (hab : a < b) (hb : b ≤ p.length) (hz : z ∉ p.support)
    (hchord : G.Adj (p.getVert (a - 1)) (p.getVert b))
    (hya : G.Adj y (p.getVert a)) (haz : G.Adj (p.getVert a) z) (hzx : G.Adj z x) :
    ∃ s : G.Walk z z, s.IsCycle ∧ s.length = a + (p.length - b) + 3 := by
  let r : G.Walk (p.getVert a) z := Walk.cons haz Walk.nil
  have hr : r.IsPath := Walk.IsPath.mk' (by simp [r, haz.ne])
  have hpq := path_prefix_suffix_disjoint p hp (by omega : a - 1 < b) hb
  have hpr : (p.take (a - 1)).support.Disjoint r.support := by
    intro w hw hwr
    have hwP := (p.isSubwalk_take (a - 1)).support_subset hw
    rcases List.mem_cons.mp hwr with heq | heq
    · obtain ⟨i, hi, hiL⟩ := Walk.mem_support_iff_exists_getVert.mp hw
      have hia : i ≤ a - 1 := by rw [Walk.take_length] at hiL; omega
      have hi' : p.getVert i = p.getVert a := by
        simpa only [Walk.take_getVert, Nat.min_eq_right hia, heq] using hi
      have := hp.getVert_injOn (show i ≤ p.length by omega) (show a ≤ p.length by omega) hi'
      omega
    · have heq' : w = z := by simpa using heq
      exact hz (heq' ▸ hwP)
  have hqr : (p.drop b).support.Disjoint r.support := by
    intro w hw hwr
    have hwP := (p.isSubwalk_drop b).support_subset hw
    rcases List.mem_cons.mp hwr with heq | heq
    · obtain ⟨i, hi, hiL⟩ := Walk.mem_support_iff_exists_getVert.mp hw
      have hia : b + i ≤ p.length := by rw [Walk.drop_length] at hiL; omega
      have hi' : p.getVert (b + i) = p.getVert a := by
        simpa only [Walk.drop_getVert, heq] using hi
      have := hp.getVert_injOn hia (show a ≤ p.length by omega) hi'
      omega
    · have heq' : w = z := by simpa using heq
      exact hz (heq' ▸ hwP)
  obtain ⟨s, hs, hlen⟩ := cycle_of_three_disjoint_paths (p.take (a - 1)) (p.drop b) r
    (hp.take _) (hp.drop _) hr hpq hpr hqr hchord hya hzx
  refine ⟨s, hs, ?_⟩
  simp only [Walk.take_length, Nat.min_eq_left (by omega : a - 1 ≤ p.length),
    Walk.drop_length, r, Walk.length_cons, Walk.length_nil] at hlen
  omega

theorem endpoint_neighbors_on_path_of_two_attachments {V : Type*} {G : SimpleGraph V}
    {x y u : V} {k a b : ℕ} (hG : NoLongCycle G k) (hu : G.IsUniversal u)
    (p : G.Walk x y) (hp : p.IsPath) (ha : 1 ≤ a) (hab : a < b) (hb : b ≤ p.length)
    (hlen : k ≤ a + (p.length - b) + 3)
    (huab : u = p.getVert a ∨ u = p.getVert b)
    (hya : G.Adj y (p.getVert a))
    (hchord : G.Adj (p.getVert (a - 1)) (p.getVert b)) :
    ∀ z, G.Adj x z → z ∈ p.support := by
  intro z hxz
  by_contra hz
  have huz : u ≠ z := by
    intro heq
    rcases huab with h | h <;> exact hz (heq ▸ h.symm ▸ p.getVert_mem_support _)
  rcases huab with hua | hub
  · obtain ⟨s, hs, hslen⟩ := cycle_of_external_early_attachment p hp ha hab hb hz hchord hya
      (hua ▸ hu huz) hxz.symm
    have := hG z s hs
    omega
  · obtain ⟨s, hs, hslen⟩ := cycle_of_external_crossing p hp hab hb hz hya
      (hub ▸ hu huz) hxz.symm
    have := hG z s hs
    omega

end Erdos1105

#print axioms Erdos1105.endpoint_neighbors_on_path_of_two_attachments
