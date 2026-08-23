import ErdosProblems.Erdos1105.RainbowWalks

namespace Erdos1105

open SimpleGraph

lemma path_snd_ne_end {V : Type*} {G : SimpleGraph V} {x y : V}
    (p : G.Walk x y) (hp : p.IsPath) (hlen : 2 ≤ p.length) : p.snd ≠ y := by
  intro h
  have heq : p.getVert 1 = p.getVert p.length := by simpa using h
  have hi : 1 = p.length := hp.getVert_injOn (by change 1 ≤ p.length; omega) (by simp) heq
  omega

/-- A private representative cannot contain a forbidden-length path whose
two terminal edge colors are private to the adjacent interior vertices:
the edge closing that path would have a new color. -/
theorem private_inward_path_impossible {V C : Type*}
    (c : (⊤ : SimpleGraph V).edgeSet → C) (R : SimpleGraph V)
    (hR : Set.InjOn (extendColor c) R.edgeSet)
    (howned : ∀ e : R.edgeSet, ∃ w, PrivateAt c w
      (c ⟨e.val, edgeSet_mono (show R ≤ ⊤ from le_top) e.property⟩))
    {x y : V} (p : R.Walk x y) (hp : p.IsPath) (hlen : 2 ≤ p.length) (hnil : ¬p.Nil)
    (hfirst : PrivateAt c p.snd (c ⟨s(x, p.snd), (p.adj_snd hnil).ne⟩))
    (hlast : PrivateAt c p.penultimate
      (c ⟨s(p.penultimate, y), (p.adj_penultimate hnil).ne⟩))
    (hH : ∀ f : (cycleGraph (p.length + 1)).Copy (⊤ : SimpleGraph V), ¬IsRainbow f c) : False := by
  have hxy : x ≠ y := by
    intro h
    have heq : p.getVert 0 = p.getVert p.length := by simpa using h
    have hi : 0 = p.length := hp.getVert_injOn (by simp) (by simp) heq
    omega
  let closing : (⊤ : SimpleGraph V).edgeSet := ⟨s(y, x), hxy.symm⟩
  have hnew : extendColor c closing.val ∉ p.edges.map (extendColor c) := by
    intro hm
    obtain ⟨d, hd, hcol⟩ := List.mem_map.mp hm
    have hdR := p.edges_subset_edgeSet hd
    have hraw : c closing = c ⟨d, edgeSet_mono le_top hdR⟩ := by
      apply Option.some.inj
      rw [← extendColor_edge c closing, ← extendColor_edge c ⟨d, edgeSet_mono le_top hdR⟩]
      exact hcol.symm
    obtain ⟨w, hw⟩ := howned ⟨d, hdR⟩
    have hwm : w = y ∨ w = x := Sym2.mem_iff.mp (hw closing hraw)
    have hwd : w ∈ d := hw ⟨d, edgeSet_mono le_top hdR⟩ rfl
    rcases hwm with hwy | hwx
    · subst w
      obtain ⟨z, rfl⟩ := Sym2.mem_iff_exists.mp hwd
      have hz : z = p.penultimate := hp.eq_penultimate_of_mem_edges hd
      subst z
      have hraw' : c closing = c ⟨s(p.penultimate, y), (p.adj_penultimate hnil).ne⟩ :=
        hraw.trans (congrArg c (Subtype.ext Sym2.eq_swap))
      have hm := hlast closing hraw'
      rcases Sym2.mem_iff.mp hm with h | h
      · exact (p.adj_penultimate hnil).ne h
      · have hne := path_snd_ne_end p.reverse hp.reverse (by simpa using hlen)
        rw [Walk.snd_reverse] at hne
        exact hne h
    · subst w
      obtain ⟨z, rfl⟩ := Sym2.mem_iff_exists.mp hwd
      have hz : z = p.snd := hp.eq_snd_of_mem_edges hd
      subst z
      have hm := hfirst closing hraw
      rcases Sym2.mem_iff.mp hm with h | h
      · exact path_snd_ne_end p hp hlen h
      · exact (p.adj_snd hnil).ne h.symm
  have hsub : ∀ e ∈ p.edges, e ∈ (⊤ : SimpleGraph V).edgeSet :=
    fun _ he ↦ edgeSet_mono le_top (p.edges_subset_edgeSet he)
  let p' := p.transfer ⊤ hsub
  have hp' : p'.IsPath := hp.transfer hsub
  let q := Walk.cons hxy.symm p'
  have hq : q.IsCycle := by
    apply (Walk.cons_isCycle_iff p' hxy.symm).mpr
    refine ⟨hp', ?_⟩
    intro he
    have h := hp'.length_eq_one_of_mem_edges (Sym2.eq_swap ▸ he)
    rw [Walk.length_transfer] at h
    omega
  have hcols : (p'.edges.map (extendColor c)).Nodup := by
    rw [Walk.edges_transfer]
    apply hp.isTrail.edges_nodup.map_on
    intro e he d hd hed
    exact hR (p.edges_subset_edgeSet he) (p.edges_subset_edgeSet hd) hed
  have hqcols : (q.edges.map (extendColor c)).Nodup := by
    rw [Walk.edges_cons, List.map_cons, List.nodup_cons]
    exact ⟨by rwa [Walk.edges_transfer], hcols⟩
  obtain ⟨f, hf⟩ := exists_rainbow_cycle_copy_of_walk c q hq hqcols
  have hqlen : q.length = p.length + 1 := by rw [Walk.length_cons, Walk.length_transfer]
  have hHq : ∀ f : (cycleGraph q.length).Copy (⊤ : SimpleGraph V), ¬IsRainbow f c := by
    rwa [hqlen]
  exact hHq f hf

/-- The closing edge of a rainbow path must reuse a path color when the
corresponding rainbow cycle is forbidden. -/
theorem rainbow_path_closing_color {V C : Type*}
    (c : (⊤ : SimpleGraph V).edgeSet → C) (R : SimpleGraph V)
    (hR : Set.InjOn (extendColor c) R.edgeSet)
    {x y : V} (p : R.Walk x y) (hp : p.IsPath) (hlen : 2 ≤ p.length)
    (hH : ∀ f : (cycleGraph (p.length + 1)).Copy (⊤ : SimpleGraph V), ¬IsRainbow f c) :
    extendColor c s(y, x) ∈ p.edges.map (extendColor c) := by
  by_contra hnew
  have hxy : x ≠ y := by
    intro h
    have heq : p.getVert 0 = p.getVert p.length := by simpa using h
    have hi : 0 = p.length := hp.getVert_injOn (by simp) (by simp) heq
    omega
  have hsub : ∀ e ∈ p.edges, e ∈ (⊤ : SimpleGraph V).edgeSet :=
    fun _ he ↦ edgeSet_mono le_top (p.edges_subset_edgeSet he)
  let p' := p.transfer ⊤ hsub
  have hp' : p'.IsPath := hp.transfer hsub
  let q := Walk.cons hxy.symm p'
  have hq : q.IsCycle := by
    apply (Walk.cons_isCycle_iff p' hxy.symm).mpr
    refine ⟨hp', ?_⟩
    intro he
    have h := hp'.length_eq_one_of_mem_edges (Sym2.eq_swap ▸ he)
    rw [Walk.length_transfer] at h
    omega
  have hcols : (p'.edges.map (extendColor c)).Nodup := by
    rw [Walk.edges_transfer]
    exact hp.isTrail.edges_nodup.map_on
      (fun _ he _ hd hed ↦ hR (p.edges_subset_edgeSet he) (p.edges_subset_edgeSet hd) hed)
  have hqcols : (q.edges.map (extendColor c)).Nodup := by
    rw [Walk.edges_cons, List.map_cons, List.nodup_cons]
    exact ⟨by rwa [Walk.edges_transfer], hcols⟩
  obtain ⟨f, hf⟩ := exists_rainbow_cycle_copy_of_walk c q hq hqcols
  have hqlen : q.length = p.length + 1 := by rw [Walk.length_cons, Walk.length_transfer]
  have hHq : ∀ f : (cycleGraph q.length).Copy (⊤ : SimpleGraph V), ¬IsRainbow f c := by
    rwa [hqlen]
  exact hHq f hf

/-- With the last edge private to the penultimate vertex, only the first
edge can share the closing color of a private representative path. -/
theorem private_path_closing_eq_first {V C : Type*}
    (c : (⊤ : SimpleGraph V).edgeSet → C) (R : SimpleGraph V)
    (hR : Set.InjOn (extendColor c) R.edgeSet)
    (howned : ∀ e : R.edgeSet, ∃ w, PrivateAt c w
      (c ⟨e.val, edgeSet_mono (show R ≤ ⊤ from le_top) e.property⟩))
    {x y : V} (p : R.Walk x y) (hp : p.IsPath) (hlen : 2 ≤ p.length) (hnil : ¬p.Nil)
    (hlast : PrivateAt c p.penultimate
      (c ⟨s(p.penultimate, y), (p.adj_penultimate hnil).ne⟩))
    (hH : ∀ f : (cycleGraph (p.length + 1)).Copy (⊤ : SimpleGraph V), ¬IsRainbow f c) :
    extendColor c s(y, x) = extendColor c s(x, p.snd) := by
  have hm := rainbow_path_closing_color c R hR p hp hlen hH
  obtain ⟨d, hd, hcol⟩ := List.mem_map.mp hm
  have hdR := p.edges_subset_edgeSet hd
  have hxy : x ≠ y := by
    intro h
    have heq : p.getVert 0 = p.getVert p.length := by simpa using h
    have hi : 0 = p.length := hp.getVert_injOn (by simp) (by simp) heq
    omega
  let closing : (⊤ : SimpleGraph V).edgeSet := ⟨s(y, x), hxy.symm⟩
  have hraw : c closing = c ⟨d, edgeSet_mono le_top hdR⟩ := by
    apply Option.some.inj
    rw [← extendColor_edge c closing, ← extendColor_edge c ⟨d, edgeSet_mono le_top hdR⟩]
    exact hcol.symm
  obtain ⟨w, hw⟩ := howned ⟨d, hdR⟩
  have hwm : w = y ∨ w = x := Sym2.mem_iff.mp (hw closing hraw)
  have hwd : w ∈ d := hw ⟨d, edgeSet_mono le_top hdR⟩ rfl
  rcases hwm with hwy | hwx
  · subst w
    obtain ⟨z, rfl⟩ := Sym2.mem_iff_exists.mp hwd
    have hz : z = p.penultimate := hp.eq_penultimate_of_mem_edges hd
    subst z
    have hraw' : c closing = c ⟨s(p.penultimate, y), (p.adj_penultimate hnil).ne⟩ :=
      hraw.trans (congrArg c (Subtype.ext Sym2.eq_swap))
    have hm := hlast closing hraw'
    rcases Sym2.mem_iff.mp hm with h | h
    · exact ((p.adj_penultimate hnil).ne h).elim
    · have hne := path_snd_ne_end p.reverse hp.reverse (by simpa using hlen)
      rw [Walk.snd_reverse] at hne
      exact (hne h).elim
  · subst w
    obtain ⟨z, rfl⟩ := Sym2.mem_iff_exists.mp hwd
    have hz : z = p.snd := hp.eq_snd_of_mem_edges hd
    subst z
    exact hcol.symm

end Erdos1105
