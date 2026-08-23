import ErdosProblems.Erdos1105.Representatives
import ErdosProblems.Erdos1105.PrivateColors

namespace Erdos1105

open SimpleGraph

/-- A rainbow cycle walk gives a rainbow non-induced cycle copy. -/
theorem exists_rainbow_cycle_copy_of_walk {V C : Type*} {G : SimpleGraph V}
    (c : G.edgeSet → C) {v : V} (p : G.Walk v v) (hp : p.IsCycle)
    (hcols : (p.edges.map (extendColor c)).Nodup) :
    ∃ f : (cycleGraph p.length).Copy G, IsRainbow f c := by
  let R := p.toSubgraph.spanningCoe
  have hR : R ≤ G := p.toSubgraph.spanningCoe_le
  have hmem (e : Sym2 V) : e ∈ R.edgeSet ↔ e ∈ p.edges := by
    rw [Subgraph.edgeSet_spanningCoe, Walk.mem_edges_toSubgraph]
  have hsub : ∀ e ∈ p.edges, e ∈ R.edgeSet := fun e he ↦ (hmem e).mpr he
  have hcopy : cycleGraph p.length ⊑ R :=
    (cycleGraph_isContained_iff (by have := hp.three_le_length; omega)).mpr
      ⟨v, p.transfer R hsub, hp.transfer hsub, p.length_transfer hsub⟩
  obtain ⟨f⟩ := hcopy
  refine ⟨(Copy.ofLE R G hR).comp f, isRainbow_comp_of_color_injOn hR c ?_ f⟩
  intro e he d hd hed
  exact List.inj_on_of_nodup_map hcols ((hmem e).mp he) ((hmem d).mp hd) hed

/-- A rainbow path walk gives a rainbow non-induced path copy. -/
theorem exists_rainbow_path_copy_of_walk {V C : Type*} {G : SimpleGraph V}
    (c : G.edgeSet → C) {u v : V} (p : G.Walk u v) (hp : p.IsPath)
    (hcols : (p.edges.map (extendColor c)).Nodup) :
    ∃ f : (pathGraph (p.length + 1)).Copy G, IsRainbow f c := by
  let R := p.toSubgraph.spanningCoe
  have hR : R ≤ G := p.toSubgraph.spanningCoe_le
  have hmem (e : Sym2 V) : e ∈ R.edgeSet ↔ e ∈ p.edges := by
    rw [Subgraph.edgeSet_spanningCoe, Walk.mem_edges_toSubgraph]
  have hsub : ∀ e ∈ p.edges, e ∈ R.edgeSet := fun e he ↦ (hmem e).mpr he
  have hcopy := (hp.transfer hsub).isContained_pathGraph
  rw [Walk.length_transfer] at hcopy
  obtain ⟨f⟩ := hcopy
  refine ⟨(Copy.ofLE R G hR).comp f, isRainbow_comp_of_color_injOn hR c ?_ f⟩
  intro e he d hd hed
  exact List.inj_on_of_nodup_map hcols ((hmem e).mp he) ((hmem d).mp hd) hed

/-- Inserting an external vertex into a rainbow cycle can fail only through
a collision between the two new colors or with a retained edge color. -/
theorem cycle_insertion_collision {V C : Type*}
    (c : (⊤ : SimpleGraph V).edgeSet → C) {k : ℕ}
    (hH : ∀ f : (cycleGraph (k + 1)).Copy (⊤ : SimpleGraph V), ¬IsRainbow f c)
    {x y : V} (hxy : x ≠ y) (p : (⊤ : SimpleGraph V).Walk y x)
    (hp : (Walk.cons hxy p).IsCycle) (hlen : p.length + 1 = k)
    (hcols : (p.edges.map (extendColor c)).Nodup)
    (z : V) (hz : z ∉ p.support) :
    extendColor c s(x, z) = extendColor c s(z, y) ∨
      extendColor c s(x, z) ∈ p.edges.map (extendColor c) ∨
      extendColor c s(z, y) ∈ p.edges.map (extendColor c) := by
  by_contra h
  have hne : extendColor c s(x, z) ≠ extendColor c s(z, y) := fun he ↦ h (.inl he)
  have ha : extendColor c s(x, z) ∉ p.edges.map (extendColor c) :=
    fun he ↦ h (.inr (.inl he))
  have hb : extendColor c s(z, y) ∉ p.edges.map (extendColor c) :=
    fun he ↦ h (.inr (.inr he))
  have hxz : x ≠ z := fun he ↦ hz (he ▸ p.end_mem_support)
  have hzy : z ≠ y := fun he ↦ hz (he ▸ p.start_mem_support)
  let q := Walk.cons hxz (Walk.cons hzy p)
  have hq : q.IsCycle := by
    apply Walk.isCycle_iff_isPath_tail_and_le_length.mpr
    constructor
    · exact (Walk.cons_isPath_iff _ _).mpr ⟨(Walk.cons_isCycle_iff p hxy).mp hp |>.1, hz⟩
    · have hlenp := hp.three_le_length
      simp only [q, Walk.length_cons] at hlenp ⊢
      omega
  have hqcols : (q.edges.map (extendColor c)).Nodup := by
    simp only [q, Walk.edges_cons, List.map_cons, List.nodup_cons, List.mem_cons,
      not_or]
    exact ⟨⟨hne, ha⟩, hb, hcols⟩
  obtain ⟨f, hf⟩ := exists_rainbow_cycle_copy_of_walk c q hq hqcols
  have hqlen : q.length = k + 1 := by simp only [q, Walk.length_cons]; omega
  have hHq : ∀ f : (cycleGraph q.length).Copy (⊤ : SimpleGraph V), ¬IsRainbow f c := by
    rwa [hqlen]
  exact hHq f hf

/-- Two distinct colors private to an external vertex force the closing
edge of a path extension to reuse an internal path color. -/
theorem private_path_closing_color {V C : Type*}
    (c : (⊤ : SimpleGraph V).edgeSet → C) {x y : V}
    (p : (⊤ : SimpleGraph V).Walk x y) (hp : p.IsPath)
    (hcols : (p.edges.map (extendColor c)).Nodup)
    (hH : ∀ f : (cycleGraph (p.length + 3)).Copy (⊤ : SimpleGraph V), ¬IsRainbow f c)
    (u w : V) (hu : u ∉ p.support) (hw : w ∉ p.support) (huw : u ≠ w)
    (hux : u ≠ x)
    (hpu : PrivateAt c u (c ⟨s(u, x), hux⟩))
    (hpw : PrivateAt c u (c ⟨s(u, w), huw⟩))
    (hne : c ⟨s(u, x), hux⟩ ≠ c ⟨s(u, w), huw⟩) :
    extendColor c s(y, w) ∈ p.edges.map (extendColor c) := by
  by_contra hclose
  have hyw : y ≠ w := fun h ↦ hw (h ▸ p.end_mem_support)
  have hnot (e : (⊤ : SimpleGraph V).edgeSet) (he : PrivateAt c u (c e)) :
      extendColor c e.val ∉ p.edges.map (extendColor c) := by
    rintro hm
    obtain ⟨d, hd, hcol⟩ := List.mem_map.mp hm
    have hraw : c ⟨d, p.edges_subset_edgeSet hd⟩ = c e := by
      apply Option.some.inj
      rw [← extendColor_edge c ⟨d, p.edges_subset_edgeSet hd⟩, ← extendColor_edge c e]
      exact hcol
    exact hu (Walk.mem_support_iff_exists_mem_edges.mpr
      (.inr ⟨d, hd, he ⟨d, p.edges_subset_edgeSet hd⟩ hraw⟩))
  have hdiff (e : (⊤ : SimpleGraph V).edgeSet) (he : PrivateAt c u (c e)) :
      extendColor c e.val ≠ extendColor c s(y, w) := by
    intro hcol
    have hraw : c ⟨s(y, w), hyw⟩ = c e := by
      apply Option.some.inj
      rw [← extendColor_edge c ⟨s(y, w), hyw⟩, ← extendColor_edge c e]
      exact hcol.symm
    have hm := he ⟨s(y, w), hyw⟩ hraw
    rcases Sym2.mem_iff.mp hm with h | h
    · exact hu (h.symm ▸ p.end_mem_support)
    · exact huw h
  have hnew : extendColor c s(w, u) ≠ extendColor c s(u, x) := by
    rw [show s(w, u) = s(u, w) from Sym2.eq_swap,
      extendColor_edge c ⟨s(u, w), huw⟩, extendColor_edge c ⟨s(u, x), hux⟩]
    exact fun h ↦ hne (Option.some.inj h).symm
  have hnot₁ : extendColor c s(w, u) ∉ p.edges.map (extendColor c) := by
    rw [show s(w, u) = s(u, w) from Sym2.eq_swap]
    exact hnot ⟨s(u, w), huw⟩ hpw
  have hdiff₁ : extendColor c s(w, u) ≠ extendColor c s(y, w) := by
    rw [show s(w, u) = s(u, w) from Sym2.eq_swap]
    exact hdiff ⟨s(u, w), huw⟩ hpw
  let q := Walk.cons huw.symm (Walk.cons hux (p.concat hyw))
  have hq : q.IsCycle := by
    apply Walk.isCycle_iff_isPath_tail_and_le_length.mpr
    refine ⟨?_, by simp [q]⟩
    apply (Walk.cons_isPath_iff _ _).mpr
    refine ⟨hp.concat hw hyw, ?_⟩
    simp only [Walk.support_concat, List.mem_append, List.mem_singleton, not_or]
    exact ⟨hu, huw⟩
  have hqcols : (q.edges.map (extendColor c)).Nodup := by
    have hremaining : ∀ a ∈ p.edges, extendColor c a ≠ extendColor c s(y, w) := by
      intro a ha he
      exact hclose (List.mem_map.mpr ⟨a, ha, he⟩)
    simpa [q, Walk.edges_concat, List.concat_eq_append, List.nodup_append,
      hcols, hnew, hnot₁, hdiff₁, hnot ⟨s(u, x), hux⟩ hpu,
      hdiff ⟨s(u, x), hux⟩ hpu] using hremaining
  obtain ⟨f, hf⟩ := exists_rainbow_cycle_copy_of_walk c q hq hqcols
  have hqlen : q.length = p.length + 3 := by simp [q]
  have hHq : ∀ f : (cycleGraph q.length).Copy (⊤ : SimpleGraph V), ¬IsRainbow f c := by
    rwa [hqlen]
  exact hHq f hf

end Erdos1105
