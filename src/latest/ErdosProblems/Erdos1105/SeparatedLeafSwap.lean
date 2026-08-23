import ErdosProblems.Erdos1105.SeparatedTreeLeaf
import ErdosProblems.Erdos1105.RainbowWalks

namespace Erdos1105

open SimpleGraph

theorem SeparatedRepresentative.leaf_extension_color {V C : Type*}
    [Fintype V] [DecidableEq V] {k : ℕ} (c : (⊤ : SimpleGraph V).edgeSet → C)
    {R H : SimpleGraph V} (hsep : SeparatedRepresentative ⊤ (extendColor c) R H)
    (hk : 3 ≤ k) (hfree : ∀ f : (pathGraph k).Copy (⊤ : SimpleGraph V), ¬IsRainbow f c)
    {a b x y : V} (p : H.Walk a b) (hp : p.IsPath) (hlen : p.length + 1 = k - 2)
    (hxy : R.Adj x y) (hxb : ¬R.Reachable x b) :
    extendColor c s(x, y) = extendColor c s(y, a) := by
  classical
  by_contra hne
  have hyb : ¬R.Reachable y b := fun h ↦ hxb (hxy.reachable.trans h)
  have houtside (z : V) (hz : ¬R.Reachable z b) : z ∉ p.support := by
    intro hm
    exact hz ((p.dropUntil z hm).reachable.mono hsep.le)
  have hxout := houtside x hxb
  have hyout := houtside y hyb
  have hya : y ≠ a := fun h ↦ hyout (h ▸ p.start_mem_support)
  have hnot : ¬H.Reachable a y := fun h ↦ hyb ((h.symm.trans p.reachable).mono hsep.le)
  have hpcols : (p.edges.map (extendColor c)).Nodup := by
    apply hp.isTrail.edges_nodup.map_on
    intro e he f hf hef
    exact hsep.representative.rainbow (edgeSet_mono hsep.le (p.edges_subset_edgeSet he))
      (edgeSet_mono hsep.le (p.edges_subset_edgeSet hf)) hef
  have hcross : extendColor c s(y, a) ∉ p.edges.map (extendColor c) := by
    rintro hm
    obtain ⟨e, he, hc⟩ := List.mem_map.mp hm
    have h := hsep.fresh_walk_color (by simpa using hya.symm) hnot p he
    exact h (by simpa only [Sym2.eq_swap] using hc)
  have hleaf : extendColor c s(x, y) ∉ p.edges.map (extendColor c) := by
    rintro hm
    obtain ⟨e, he, hc⟩ := List.mem_map.mp hm
    have heq := hsep.representative.rainbow (edgeSet_mono hsep.le (p.edges_subset_edgeSet he)) hxy hc
    have hxyP : s(x, y) ∈ p.edges := heq ▸ he
    exact hxout (p.fst_mem_support_of_mem_edges hxyP)
  have hsub : ∀ e ∈ p.edges, e ∈ (⊤ : SimpleGraph V).edgeSet :=
    fun _ he ↦ edgeSet_mono le_top (p.edges_subset_edgeSet he)
  let p' := p.transfer ⊤ hsub
  let q := Walk.cons (show (⊤ : SimpleGraph V).Adj x y from hxy.ne)
    (Walk.cons (show (⊤ : SimpleGraph V).Adj y a from hya) p')
  have hq : q.IsPath := by
    apply (Walk.cons_isPath_iff _ _).mpr
    constructor
    · apply (Walk.cons_isPath_iff _ _).mpr
      exact ⟨hp.transfer hsub, by simpa only [p', Walk.support_transfer] using hyout⟩
    · simpa only [p', Walk.support_cons, Walk.support_transfer, List.mem_cons, not_or]
        using And.intro hxy.ne hxout
  have hqcolors : (q.edges.map (extendColor c)).Nodup := by
    simpa only [q, p', Walk.edges_cons, Walk.edges_transfer, List.map_cons, List.nodup_cons,
      List.mem_cons, not_or] using And.intro (And.intro hne hleaf) (And.intro hcross hpcols)
  obtain ⟨f, hf⟩ := exists_rainbow_path_copy_of_walk c q hq hqcolors
  have hqlen : q.length + 1 = k := by
    simp only [q, p', Walk.length_cons, Walk.length_transfer]
    omega
  have hfree' : ∀ f : (pathGraph (q.length + 1)).Copy (⊤ : SimpleGraph V), ¬IsRainbow f c := by
    rwa [hqlen]
  exact hfree' f hf

/-- A disconnected counterexample has a full representative with an
isolated vertex, enabling a deletion without losing a color. -/
theorem SeparatedRepresentative.high_colors_isolated_representative {V C : Type*}
    [Fintype V] [DecidableEq V] {k : ℕ} (c : (⊤ : SimpleGraph V).edgeSet → C)
    {R H : SimpleGraph V} (hsep : SeparatedRepresentative ⊤ (extendColor c) R H)
    (hk : 5 ≤ k) (hn : k ≤ Fintype.card V)
    (hfree : ∀ f : (pathGraph k).Copy (⊤ : SimpleGraph V), ¬IsRainbow f c)
    (hnot : ¬R.Preconnected) (hhigh : pathFormula (Fintype.card V) k < Nat.card R.edgeSet) :
    ∃ Q, ColorRepresentative ⊤ (extendColor c) Q ∧ ∃ x, Q.IsIsolated x := by
  classical
  obtain ⟨a, b, p, hp, hlen, hsmall⟩ := hsep.high_colors_long_path c hk hn hfree hnot hhigh
  obtain ⟨x, hxb, hleaf⟩ := hsep.exists_outside_leaf b hnot hsmall
  by_cases hneighbor : ∃ y, R.Adj x y
  · obtain ⟨y, hxy⟩ := hneighbor
    have hcol := hsep.leaf_extension_color c (by omega) hfree p hp hlen hxy hxb
    have hxa : x ≠ a := fun h ↦ hxb (h ▸ p.reachable.mono hsep.le)
    have hya : y ≠ a := fun h ↦ hxb (hxy.reachable.trans (h ▸ p.reachable.mono hsep.le))
    let e : R.edgeSet := ⟨s(x, y), hxy⟩
    let d : (⊤ : SimpleGraph V).edgeSet := ⟨s(y, a), hya⟩
    refine ⟨swapRepresentative R e.val d.val, hsep.representative.swap e d hcol.symm, x, ?_⟩
    intro z hxz
    rcases (mem_swapRepresentative R e.val d s(x, z)).mp hxz with h | h
    · have hz := hleaf z y h.1 hxy
      exact h.2 (by simp only [e, hz])
    · rcases Sym2.eq_iff.mp h with h | h
      · exact hxy.ne h.1
      · exact hxa h.1
  · exact ⟨R, hsep.representative, x, fun y hxy ↦ hneighbor ⟨y, hxy⟩⟩

end Erdos1105

#print axioms Erdos1105.SeparatedRepresentative.high_colors_isolated_representative
