import ErdosProblems.Erdos1105.RainbowWalks

namespace Erdos1105

open SimpleGraph

lemma cycle_head_not_mem_tail {V : Type*} {G : SimpleGraph V} {v : V}
    (q : G.Walk v v) (hq : q.IsCycle) : s(v, q.snd) ∉ q.tail.edges := by
  cases q with
  | nil => simp at hq
  | cons h q =>
    simpa only [Walk.snd_cons, Walk.edges_tail, Walk.edges_cons, List.tail_cons] using
      ((Walk.cons_isCycle_iff q h).mp hq).2

/-- Removing the first edge in each orientation leaves no edge at the base vertex. -/
lemma cycle_tails_no_incident_edge {V : Type*} {G : SimpleGraph V} {v : V}
    (q : G.Walk v v) (hq : q.IsCycle) {e : Sym2 V}
    (he : e ∈ q.tail.edges) (her : e ∈ q.reverse.tail.edges) (hv : v ∈ e) : False := by
  obtain ⟨w, rfl⟩ := Sym2.mem_iff_exists.mp hv
  have heq : s(v, w) ∈ q.edges := List.mem_of_mem_tail (by rwa [← Walk.edges_tail])
  have hm : w ∈ q.toSubgraph.neighborSet v := Walk.adj_toSubgraph_iff_mem_edges.mpr heq
  rw [hq.neighborSet_toSubgraph_endpoint] at hm
  rcases hm with rfl | rfl
  · exact cycle_head_not_mem_tail q hq he
  · apply cycle_head_not_mem_tail q.reverse hq.reverse
    simpa only [Walk.snd_reverse] using her

/-- If two distinct colors are private to an external vertex, a rainbow
private cycle cannot have a monochromatic boundary at that vertex. -/
theorem private_cycle_two_colors_impossible {V C : Type*}
    (c : (⊤ : SimpleGraph V).edgeSet → C) (R : SimpleGraph V)
    (hR : Set.InjOn (extendColor c) R.edgeSet)
    (howned : ∀ e : R.edgeSet, ∃ w, PrivateAt c w
      (c ⟨e.val, edgeSet_mono (show R ≤ ⊤ from le_top) e.property⟩))
    {v : V} (q : R.Walk v v) (hq : q.IsCycle)
    (hH : ∀ f : (cycleGraph (q.length + 1)).Copy (⊤ : SimpleGraph V), ¬IsRainbow f c)
    (u w : V) (hu : u ∉ q.support) (hw : w ∉ q.support) (huw : u ≠ w)
    (a : C) (ha : PrivateAt c u a)
    (hconst : ∀ x ∈ q.support, extendColor c s(u, x) = some a)
    (hb : PrivateAt c u (c ⟨s(u, w), huw⟩)) (hab : a ≠ c ⟨s(u, w), huw⟩) : False := by
  have hforce {v : V} (q : R.Walk v v) (hq : q.IsCycle)
      (hH : ∀ f : (cycleGraph (q.length + 1)).Copy (⊤ : SimpleGraph V), ¬IsRainbow f c)
      (hu : u ∉ q.support) (hw : w ∉ q.support)
      (hconst : ∀ x ∈ q.support, extendColor c s(u, x) = some a) :
      ∃ e ∈ q.tail.tail.edges, extendColor c e = extendColor c s(v, w) := by
    cases q with
    | nil => simp at hq
    | cons h q =>
      cases q with
      | nil => exact (h.ne rfl).elim
      | cons h₂ p =>
        have hps : p.support ⊆ (Walk.cons h (Walk.cons h₂ p)).support := by
          intro z hz
          exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hz)
        have hpu : u ∉ p.support := fun hm ↦ hu (hps hm)
        have hpw : w ∉ p.support := fun hm ↦ hw (hps hm)
        have hpath : p.IsPath := ((Walk.cons_isCycle_iff _ _).mp hq).1.of_cons
        have hsub : ∀ e ∈ p.edges, e ∈ (⊤ : SimpleGraph V).edgeSet :=
          fun e he ↦ edgeSet_mono le_top (p.edges_subset_edgeSet he)
        let p' := p.transfer ⊤ hsub
        have hpath' : p'.IsPath := hpath.transfer hsub
        have hcols : (p'.edges.map (extendColor c)).Nodup := by
          rw [Walk.edges_transfer]
          apply hpath.isTrail.edges_nodup.map_on
          intro e he d hd hed
          exact hR (p.edges_subset_edgeSet he) (p.edges_subset_edgeSet hd) hed
        have hux : u ≠ p.getVert 0 := by
          intro he
          exact hpu (he.symm ▸ p.getVert_mem_support 0)
        have hraw : c ⟨s(u, p.getVert 0), hux⟩ = a := by
          apply Option.some.inj
          rw [← extendColor_edge c ⟨s(u, p.getVert 0), hux⟩]
          exact hconst _ (hps (p.getVert_mem_support 0))
        have hH' : ∀ f : (cycleGraph (p'.length + 3)).Copy (⊤ : SimpleGraph V),
            ¬IsRainbow f c := by
          have hlen : p'.length + 3 = (Walk.cons h (Walk.cons h₂ p)).length + 1 := by
            rw [Walk.length_transfer, Walk.length_cons, Walk.length_cons]
          rwa [hlen]
        simp only [Walk.getVert_zero] at hux hraw
        have hforced := private_path_closing_color c p' hpath' hcols hH' u w
          (by simpa only [p', Walk.support_transfer] using hpu)
          (by simpa only [p', Walk.support_transfer] using hpw) huw hux
          (by rwa [hraw]) hb (by rwa [hraw])
        rw [Walk.edges_transfer] at hforced
        simpa only [Walk.edges_tail, Walk.edges_cons, List.tail_cons] using List.mem_map.mp hforced
  obtain ⟨e, he, hce⟩ := hforce q hq hH hu hw hconst
  obtain ⟨d, hd, hcd⟩ := hforce q.reverse hq.reverse
    (by rwa [Walk.length_reverse])
    (by simpa only [Walk.support_reverse, List.mem_reverse] using hu)
    (by simpa only [Walk.support_reverse, List.mem_reverse] using hw)
    (by simpa only [Walk.support_reverse, List.mem_reverse] using hconst)
  have hem : e ∈ q.edges := by
    rw [Walk.edges_tail, Walk.edges_tail] at he
    exact List.mem_of_mem_tail (List.mem_of_mem_tail he)
  have hdm : d ∈ q.edges := by
    rw [Walk.edges_tail, Walk.edges_tail] at hd
    simpa only [Walk.edges_reverse, List.mem_reverse] using
      List.mem_of_mem_tail (List.mem_of_mem_tail hd)
  have hed : e = d := hR (q.edges_subset_edgeSet hem) (q.edges_subset_edgeSet hdm)
    (hce.trans hcd.symm)
  subst d
  have hwe : w ∉ e := fun hm ↦ hw
    (Walk.mem_support_iff_exists_mem_edges.mpr (.inr ⟨e, hem, hm⟩))
  have hwv : w ≠ v := fun heq ↦ hw (heq.symm ▸ q.start_mem_support)
  have hpv := privateAt_of_external_color_collision c
    ⟨e, edgeSet_mono le_top (q.edges_subset_edgeSet hem)⟩
    (howned ⟨e, q.edges_subset_edgeSet hem⟩) w v hwe hwv
    (by rw [show s(w, v) = s(v, w) from Sym2.eq_swap]; exact hce.symm)
  have hve : v ∈ e := hpv ⟨e, edgeSet_mono le_top (q.edges_subset_edgeSet hem)⟩ rfl
  apply cycle_tails_no_incident_edge q hq _ _ hve
  · rw [Walk.edges_tail] at he
    exact List.mem_of_mem_tail he
  · rw [Walk.edges_tail] at hd
    exact List.mem_of_mem_tail hd

end Erdos1105
