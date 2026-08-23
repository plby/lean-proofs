import ErdosProblems.Erdos1105.CycleCutSupport
import ErdosProblems.Erdos1105.RainbowPathExtension

namespace Erdos1105

open SimpleGraph

/-- A rainbow cycle can be opened at the color of an external edge,
provided an endpoint of that cut can be joined to the external pair. -/
theorem rainbow_path_of_cycle_color_cut {V C : Type*} [DecidableEq V]
    (c : (⊤ : SimpleGraph V).edgeSet → C) {R : SimpleGraph V}
    (hR : Set.InjOn (extendColor c) R.edgeSet) {u : V} (p : R.Walk u u) (hp : p.IsCycle)
    (A : Set V) (hAsub : A ⊆ {x | x ∈ p.support})
    {y z : V} (hy : y ∉ p.support) (hz : z ∉ p.support) (hyz : y ≠ z)
    (hyA : ∀ x ∈ A, R.Adj y x)
    (hcover : ∀ d ∈ p.darts, extendColor c d.edge = extendColor c s(z, y) →
      d.fst ∈ A ∨ d.snd ∈ A)
    (hxchoice : ∃ x ∈ A, extendColor c s(z, y) ≠ extendColor c s(y, x)) :
    ∃ f : (pathGraph (p.length + 2)).Copy (⊤ : SimpleGraph V), IsRainbow f c := by
  classical
  have hynew : ∀ x ∈ A, ∀ e ∈ p.edges, extendColor c s(y, x) ≠ extendColor c e := by
    intro x hx e he hc
    have heq := hR (hyA x hx) (p.edges_subset_edgeSet he) hc
    exact hy (p.fst_mem_support_of_mem_edges (heq.symm ▸ he))
  have hfinish (x : V) (hx : x ∈ A) (v : V) (q : R.Walk x v) (hq : q.IsPath)
      (hlen : q.length + 1 = p.length) (hsub : q.support ⊆ p.support)
      (hnew : extendColor c s(z, y) ∉ q.edges.map (extendColor c))
      (hdiff : extendColor c s(z, y) ≠ extendColor c s(y, x)) :
      ∃ f : (pathGraph (p.length + 2)).Copy (⊤ : SimpleGraph V), IsRainbow f c := by
    have h := rainbow_path_prepend_two c hR q hq (fun h ↦ hz (hsub h))
      (fun h ↦ hy (hsub h)) hyz.symm (hyA x hx) hdiff hnew
    have heq : q.length + 3 = p.length + 2 := by omega
    rwa [heq] at h
  by_cases hbad : ∃ e ∈ p.edges, extendColor c e = extendColor c s(z, y)
  · obtain ⟨e, he, hc⟩ := hbad
    change e ∈ p.darts.map Dart.edge at he
    obtain ⟨d, hd, hde⟩ := List.mem_map.mp he
    obtain ⟨q, hq, hlen, hsupp, hedges, havoid⟩ := cycle_path_avoiding_dart p hp d hd
    have havoidColor : extendColor c s(z, y) ∉ q.edges.map (extendColor c) := by
      rintro hm
      obtain ⟨f, hf, hfc⟩ := List.mem_map.mp hm
      have hef := hR (q.edges_subset_edgeSet hf) (p.edges_subset_edgeSet
        (show e ∈ p.edges from List.mem_map.mpr ⟨d, hd, hde⟩)) (hfc.trans hc.symm)
      exact havoid ((hef.trans hde.symm) ▸ hf)
    have hdiff : ∀ x ∈ A, extendColor c s(z, y) ≠ extendColor c s(y, x) := by
      intro x hx h
      exact hynew x hx e (List.mem_map.mpr ⟨d, hd, hde⟩) (h.symm.trans hc.symm)
    rcases hcover d hd (hde ▸ hc) with hfst | hsnd
    · apply hfinish d.fst hfst d.snd q.reverse hq.reverse
      · simpa only [Walk.length_reverse] using hlen
      · intro x hx
        exact hsupp (by simpa only [Walk.support_reverse, List.mem_reverse] using hx)
      · simpa only [Walk.edges_reverse, List.map_reverse, List.mem_reverse] using havoidColor
      · exact hdiff _ hfst
    · exact hfinish d.snd hsnd d.fst q hq hlen hsupp havoidColor (hdiff _ hsnd)
  · obtain ⟨x, hx, hdiff⟩ := hxchoice
    obtain ⟨v, q, hq, hlen, hsub, hedges⟩ := cycle_path_from_vertex p hp (hAsub hx)
    apply hfinish x hx v q hq hlen hsub ?_ hdiff
    rintro hm
    obtain ⟨e, he, hc⟩ := List.mem_map.mp hm
    exact hbad ⟨e, hedges he, hc⟩

/-- The cycle-extension step in the even-path split-graph argument. -/
theorem rainbow_path_of_cycle_two_external {V C : Type*} [DecidableEq V]
    (c : (⊤ : SimpleGraph V).edgeSet → C) {R : SimpleGraph V}
    (hR : Set.InjOn (extendColor c) R.edgeSet) {u : V} (p : R.Walk u u) (hp : p.IsCycle)
    (A : Set V) (hAsub : A ⊆ {x | x ∈ p.support})
    (hAtwo : ∃ a ∈ A, ∃ b ∈ A, a ≠ b)
    (hcover : ∀ d ∈ p.darts, d.fst ∈ A ∨ d.snd ∈ A)
    {y z : V} (hy : y ∉ p.support) (hz : z ∉ p.support) (hyz : y ≠ z)
    (hyA : ∀ x ∈ A, R.Adj y x) :
    ∃ f : (pathGraph (p.length + 2)).Copy (⊤ : SimpleGraph V), IsRainbow f c := by
  classical
  apply rainbow_path_of_cycle_color_cut c hR p hp A hAsub hy hz hyz hyA
    (fun d hd _ ↦ hcover d hd)
  obtain ⟨a, ha, b, hb, hab⟩ := hAtwo
  by_cases hca : extendColor c s(z, y) = extendColor c s(y, a)
  · refine ⟨b, hb, ?_⟩
    intro hcb
    have heq := hR (hyA a ha) (hyA b hb) (hca.symm.trans hcb)
    rcases Sym2.eq_iff.mp heq with ⟨_, h⟩ | ⟨hyb, hay⟩
    · exact hab h
    · exact hab (hay.trans hyb)
  · exact ⟨a, ha, hca⟩

/-- When both external vertices see a nonempty attachment set, one of
the two orientations of their edge supplies the needed distinct color. -/
theorem rainbow_path_of_cycle_two_attached {V C : Type*} [DecidableEq V]
    (c : (⊤ : SimpleGraph V).edgeSet → C) {R : SimpleGraph V}
    (hR : Set.InjOn (extendColor c) R.edgeSet) {u : V} (p : R.Walk u u) (hp : p.IsCycle)
    (A : Set V) (hAsub : A ⊆ {x | x ∈ p.support}) (hA : A.Nonempty)
    {y z : V} (hy : y ∉ p.support) (hz : z ∉ p.support) (hyz : y ≠ z)
    (hyA : ∀ x ∈ A, R.Adj y x) (hzA : ∀ x ∈ A, R.Adj z x)
    (hcover : ∀ d ∈ p.darts, extendColor c d.edge = extendColor c s(z, y) →
      d.fst ∈ A ∨ d.snd ∈ A) :
    ∃ f : (pathGraph (p.length + 2)).Copy (⊤ : SimpleGraph V), IsRainbow f c := by
  classical
  obtain ⟨a, ha⟩ := hA
  by_cases hca : extendColor c s(z, y) = extendColor c s(y, a)
  · apply rainbow_path_of_cycle_color_cut c hR p hp A hAsub hz hy hyz.symm hzA
    · simpa only [Sym2.eq_swap] using hcover
    · refine ⟨a, ha, ?_⟩
      intro hcb
      have heq := hR (hyA a ha) (hzA a ha)
        (hca.symm.trans ((congrArg (extendColor c)
          (show s(z, y) = s(y, z) from Sym2.eq_swap)).trans hcb))
      rcases Sym2.eq_iff.mp heq with ⟨hyz', _⟩ | ⟨hya, haz⟩
      · exact hyz hyz'
      · exact hyz (hya.trans haz)
  · exact rainbow_path_of_cycle_color_cut c hR p hp A hAsub hy hz hyz hyA hcover
      ⟨a, ha, hca⟩

end Erdos1105

#print axioms Erdos1105.rainbow_path_of_cycle_two_external
