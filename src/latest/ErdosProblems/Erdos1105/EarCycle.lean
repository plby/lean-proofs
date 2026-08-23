import ErdosProblems.Erdos1105.PathSegments
import ErdosProblems.Erdos1105.PathCycleSplice

namespace Erdos1105

open SimpleGraph

/-- A detour outside a path, together with two endpoint chords into the
skipped middle, forms the cycle used in the noncrossing Pósa argument. -/
theorem cycle_of_ear_and_middle_chords {V : Type*} {G : SimpleGraph V} {x y : V}
    (p : G.Walk x y) (hp : p.IsPath) {i a b j : ℕ}
    (hia : i < a) (hab : a ≤ b) (hbj : b < j) (hj : j ≤ p.length)
    (q : G.Walk (p.getVert i) (p.getVert j)) (hq : q.IsPath)
    (hmeet : ∀ w ∈ q.support, w ∈ p.support → w = p.getVert i ∨ w = p.getVert j)
    (hxa : G.Adj x (p.getVert a)) (hyb : G.Adj y (p.getVert b))
    (hlen : 3 ≤ i + q.length + (p.length - j) + (b - a) + 2) :
    ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      c.length = i + q.length + (p.length - j) + (b - a) + 2 := by
  let pre := pathSegment p 0 i (Nat.zero_le i)
  let post := pathSegment p j p.length hj
  let mid := pathSegment p a b hab
  have hpre : pre.IsPath := pathSegment_isPath p hp 0 i _
  have hpost : post.IsPath := pathSegment_isPath p hp j p.length _
  have hmid : mid.IsPath := pathSegment_isPath p hp a b _
  have pre_sub : pre.support ⊆ p.support := pathSegment_support_subset p 0 i _ (by omega)
  have post_sub : post.support ⊆ p.support := pathSegment_support_subset p j p.length _ le_rfl
  have mid_sub : mid.support ⊆ p.support := pathSegment_support_subset p a b _ (by omega)
  have hjnotpre : p.getVert j ∉ pre.support := by
    rw [getVert_mem_pathSegment p hp 0 i _ (by omega) j hj]
    omega
  have hinotpost : p.getVert i ∉ post.support := by
    rw [getVert_mem_pathSegment p hp j p.length _ le_rfl i (by omega)]
    omega
  have hinotmid : p.getVert i ∉ mid.support := by
    rw [getVert_mem_pathSegment p hp a b _ (by omega) i (by omega)]
    omega
  have hjnotmid : p.getVert j ∉ mid.support := by
    rw [getVert_mem_pathSegment p hp a b _ (by omega) j hj]
    omega
  have hprepost : pre.support.Disjoint post.support :=
    disjoint_pathSegments p hp 0 i j p.length _ (by omega) hj le_rfl
  let r := pre.append q
  have hr : r.IsPath := by
    apply isPath_append_of_inter_eq_end hpre hq
    intro w hwpre hwq
    rcases hmeet w hwq (pre_sub hwpre) with h | h
    · exact h
    · exact (hjnotpre (h ▸ hwpre)).elim
  let s := r.append post
  have hs : s.IsPath := by
    apply isPath_append_of_inter_eq_end hr hpost
    intro w hwr hwpost
    rcases (Walk.mem_support_append_iff pre q).mp hwr with hwpre | hwq
    · exact (hprepost hwpre hwpost).elim
    · rcases hmeet w hwq (post_sub hwpost) with h | h
      · exact (hinotpost (h ▸ hwpost)).elim
      · exact h
  have hsmid : s.support.Disjoint mid.support := by
    intro w hws hwmid
    rcases (Walk.mem_support_append_iff r post).mp hws with hwr | hwpost
    · rcases (Walk.mem_support_append_iff pre q).mp hwr with hwpre | hwq
      · exact (disjoint_pathSegments p hp 0 i a b _ hia hab (by omega)) hwpre hwmid
      · rcases hmeet w hwq (mid_sub hwmid) with h | h
        · exact hinotmid (h ▸ hwmid)
        · exact hjnotmid (h ▸ hwmid)
    · exact (disjoint_pathSegments p hp a b j p.length hab hbj hj le_rfl) hwmid hwpost
  have hsmid' : s.support.Disjoint mid.reverse.support := by
    simpa only [Walk.support_reverse, List.disjoint_reverse_right] using hsmid
  have hprelen : pre.length = i := by simpa using pathSegment_length p 0 i _ (by omega)
  have hpostlen : post.length = p.length - j := pathSegment_length p j p.length _ le_rfl
  have hmidlen : mid.length = b - a := pathSegment_length p a b _ (by omega)
  have hslen : s.length = i + q.length + (p.length - j) := by
    simp only [s, r, Walk.length_append, hprelen, hpostlen]
  obtain ⟨c, hc, hclen⟩ := cycle_of_two_disjoint_paths s mid.reverse hs hmid.reverse hsmid'
    (by simpa only [Walk.getVert_length] using hyb)
    (by simpa only [Walk.getVert_zero] using hxa.symm)
    (by simpa only [hslen, Walk.length_reverse, hmidlen] using hlen)
  exact ⟨p.getVert a, c, hc, by simpa only [hslen, Walk.length_reverse, hmidlen] using hclen⟩

end Erdos1105

#print axioms Erdos1105.cycle_of_ear_and_middle_chords
