import ErdosProblems.Erdos1105.RainbowWalks

namespace Erdos1105

open SimpleGraph

/-- Prepend an existing representative edge and a fresh-colored edge
to a representative path, using two new vertices. -/
theorem rainbow_path_prepend_two {V C : Type*}
    (c : (⊤ : SimpleGraph V).edgeSet → C) {R : SimpleGraph V}
    (hR : Set.InjOn (extendColor c) R.edgeSet) {a b x y : V}
    (p : R.Walk a b) (hp : p.IsPath) (hx : x ∉ p.support) (hy : y ∉ p.support)
    (hxy : x ≠ y) (hya : R.Adj y a)
    (hne : extendColor c s(x, y) ≠ extendColor c s(y, a))
    (hnew : extendColor c s(x, y) ∉ p.edges.map (extendColor c)) :
    ∃ f : (pathGraph (p.length + 3)).Copy (⊤ : SimpleGraph V), IsRainbow f c := by
  classical
  have hpcols : (p.edges.map (extendColor c)).Nodup := by
    apply hp.isTrail.edges_nodup.map_on
    exact fun e he d hd hcol ↦ hR (p.edges_subset_edgeSet he) (p.edges_subset_edgeSet hd) hcol
  have hyaNew : extendColor c s(y, a) ∉ p.edges.map (extendColor c) := by
    rintro hm
    obtain ⟨e, he, hc⟩ := List.mem_map.mp hm
    have heq := hR (p.edges_subset_edgeSet he) hya hc
    exact hy (p.fst_mem_support_of_mem_edges (heq ▸ he))
  have hsub : ∀ e ∈ p.edges, e ∈ (⊤ : SimpleGraph V).edgeSet :=
    fun _ he ↦ edgeSet_mono le_top (p.edges_subset_edgeSet he)
  let p' := p.transfer ⊤ hsub
  let q := Walk.cons (show (⊤ : SimpleGraph V).Adj x y from hxy)
    (Walk.cons (show (⊤ : SimpleGraph V).Adj y a from hya.ne) p')
  have hq : q.IsPath := by
    apply (Walk.cons_isPath_iff _ _).mpr
    constructor
    · apply (Walk.cons_isPath_iff _ _).mpr
      exact ⟨hp.transfer hsub, by simpa only [p', Walk.support_transfer] using hy⟩
    · simpa only [p', Walk.support_cons, Walk.support_transfer, List.mem_cons, not_or]
        using And.intro hxy hx
  have hqcolors : (q.edges.map (extendColor c)).Nodup := by
    simpa only [q, p', Walk.edges_cons, Walk.edges_transfer, List.map_cons, List.nodup_cons,
      List.mem_cons, not_or] using And.intro (And.intro hne hnew) (And.intro hyaNew hpcols)
  have hlen : q.length + 1 = p.length + 3 := by
    simp only [q, p', Walk.length_cons, Walk.length_transfer]
  have h := exists_rainbow_path_copy_of_walk c q hq hqcolors
  rwa [hlen] at h

end Erdos1105

#print axioms Erdos1105.rainbow_path_prepend_two
