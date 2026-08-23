import ErdosProblems.Erdos1105.SetPath
import ErdosProblems.Erdos1105.PathCycleSplice
import ErdosProblems.Erdos1105.CycleSaturation

namespace Erdos1105

open SimpleGraph

/-- If every nonuniversal attachment into a set can be reached from the
universal vertex by a sufficiently long path inside that set, the
vertices outside the set are independent. -/
theorem outside_independent_of_attachment_paths {V : Type*} [DecidableEq V]
    {G : SimpleGraph V} {u : V} {k : ℕ} {S : Set V}
    (hG : NoLongCycle G k) (hk : 3 ≤ k) (hu : G.IsUniversal u)
    (hconn : (G.induce {v | v ≠ u}).Preconnected) (huS : u ∈ S)
    (hSne : ∃ v ∈ S, v ≠ u)
    (hboundary : ∀ z ∉ S, ∀ v ∈ S, v ≠ u → G.Adj z v →
      ∃ q : G.Walk u v, q.IsPath ∧ k - 3 ≤ q.length ∧ ∀ w ∈ q.support, w ∈ S) :
    ∀ z ∉ S, ∀ w ∉ S, ¬G.Adj z w := by
  intro z hz w hw hzw
  obtain ⟨v, hvS, hvu⟩ := hSne
  have hzu : z ≠ u := fun h ↦ hz (h ▸ huS)
  let f := (Embedding.induce (G := G) {v | v ≠ u}).toHom
  obtain ⟨r₀, hr₀⟩ := hconn.exists_isPath (⟨z, hzu⟩ : {v | v ≠ u}) ⟨v, hvu⟩
  have havoid₀ : ∀ t ∈ (r₀.map f).support, t ≠ u := by
    intro t ht
    rw [Walk.support_map] at ht
    obtain ⟨t', _, rfl⟩ := List.mem_map.mp ht
    exact t'.property
  obtain ⟨a, ha, b, hb, r, hr, havoid, hmeetA, hmeetS⟩ := exists_set_path_within G
    {z, w} {t | t ∈ S ∧ t ≠ u} {t | t ≠ u}
    ⟨z, by simp, v, ⟨hvS, hvu⟩, r₀.map f,
      hr₀.map (Embedding.induce (G := G) {v | v ≠ u}).injective, havoid₀⟩
  obtain ⟨a', ha'S, haa', ha'A⟩ : ∃ a' ∉ S, G.Adj a a' ∧ a' ∈ ({z, w} : Set V) := by
    rcases Set.mem_insert_iff.mp ha with rfl | ha
    · exact ⟨w, hw, hzw, by simp⟩
    · have heq : a = w := ha
      subst a
      exact ⟨z, hz, hzw.symm, by simp⟩
  have haS : a ∉ S := by
    rcases Set.mem_insert_iff.mp ha with rfl | ha
    · exact hz
    · have heq : a = w := ha
      exact heq ▸ hw
  have hrpos : 1 ≤ r.length := by
    by_contra h
    have hlen : r.length = 0 := by omega
    have hab : a = b := by
      have h := r.getVert_length
      simpa only [hlen, Walk.getVert_zero] using h
    exact haS (hab ▸ hb.1)
  have hpre : G.Adj (r.getVert (r.length - 1)) b := by
    have h := r.adj_getVert_succ (i := r.length - 1) (by omega)
    simpa only [Nat.sub_add_cancel hrpos, Walk.getVert_length] using h
  have hpreS : r.getVert (r.length - 1) ∉ S := by
    intro hpreS
    exact hpre.ne (hmeetS _ (r.getVert_mem_support _) ⟨hpreS, havoid _ (r.getVert_mem_support _)⟩)
  obtain ⟨q, hq, hqlen, hqS⟩ := hboundary _ hpreS b hb.1 hb.2 hpre
  have hqr : (q.append r.reverse).IsPath := by
    apply isPath_append_of_inter_eq_end hq hr.reverse
    intro t htq htr
    have htr' : t ∈ r.support := by simpa using htr
    exact hmeetS t htr' ⟨hqS t htq, havoid t htr'⟩
  have ha'not : a' ∉ (q.append r.reverse).support := by
    intro h
    rw [Walk.support_append, List.mem_append] at h
    rcases h with hqmem | hrmem
    · exact ha'S (hqS a' hqmem)
    · have hrmem' : a' ∈ r.support := by simpa using List.tail_subset _ hrmem
      exact haa'.ne.symm (hmeetA a' hrmem' ha'A)
  let s := (q.append r.reverse).concat haa'
  have hs : s.IsPath := hqr.concat ha'not haa'
  have ha'u : a' ≠ u := fun h ↦ ha'S (h ▸ huS)
  have hclose : G.Adj a' u := (hu ha'u.symm).symm
  have hcycle : (Walk.cons hclose s).IsCycle := by
    apply (Walk.cons_isCycle_iff s hclose).mpr
    refine ⟨hs, ?_⟩
    intro he
    have h := hs.length_eq_one_of_mem_edges (Sym2.eq_swap ▸ he)
    simp only [s, Walk.length_concat, Walk.length_append, Walk.length_reverse] at h
    omega
  have h := hG a' (Walk.cons hclose s) hcycle
  simp only [s, Walk.length_cons, Walk.length_concat, Walk.length_append, Walk.length_reverse] at h
  omega

end Erdos1105

#print axioms Erdos1105.outside_independent_of_attachment_paths
