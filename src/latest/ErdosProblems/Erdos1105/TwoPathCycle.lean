import ErdosProblems.Erdos1105.AdjoinRepresentative

namespace Erdos1105

open SimpleGraph

/-- Two disjoint representative paths whose vertex counts total `k`
force their two cross-edge colors to agree, provided neither cross color
occurs in the representative. -/
theorem two_paths_cross_colors_eq {V C : Type*} {k : ℕ}
    (c : (⊤ : SimpleGraph V).edgeSet → C) (R : SimpleGraph V)
    (hR : Set.InjOn (extendColor c) R.edgeSet)
    (hH : ∀ f : (cycleGraph k).Copy (⊤ : SimpleGraph V), ¬IsRainbow f c)
    {a b u v : V} (p : R.Walk a b) (q : R.Walk u v) (hp : p.IsPath) (hq : q.IsPath)
    (hdisj : p.support.Disjoint q.support) (hlen : p.length + q.length + 2 = k) (hk : 3 ≤ k)
    (hnew₁ : ∀ e ∈ R.edgeSet, extendColor c s(b, u) ≠ extendColor c e)
    (hnew₂ : ∀ e ∈ R.edgeSet, extendColor c s(v, a) ≠ extendColor c e) :
    extendColor c s(b, u) = extendColor c s(v, a) := by
  by_contra hne
  have hbu : b ≠ u := fun h ↦ hdisj p.end_mem_support (h.symm ▸ q.start_mem_support)
  have hva : v ≠ a := fun h ↦ hdisj p.start_mem_support (h ▸ q.end_mem_support)
  let d₁ : (⊤ : SimpleGraph V).edgeSet := ⟨s(b, u), hbu⟩
  let d₂ : (⊤ : SimpleGraph V).edgeSet := ⟨s(v, a), hva⟩
  let H₁ := adjoinRepresentative R d₁
  let H := adjoinRepresentative H₁ d₂
  have hr₁ : Set.InjOn (extendColor c) H₁.edgeSet := adjoinRepresentative_rainbow c R hR d₁ hnew₁
  have hr : Set.InjOn (extendColor c) H.edgeSet := by
    apply adjoinRepresentative_rainbow c H₁ hr₁ d₂
    intro e he
    rw [mem_adjoinRepresentative] at he
    rcases he with he | rfl
    · exact hnew₂ e he
    · exact fun h ↦ hne h.symm
  have hRH : R ≤ H := (le_adjoinRepresentative R d₁).trans (le_adjoinRepresentative H₁ d₂)
  have hbuH : H.Adj b u := edgeSet_mono (le_adjoinRepresentative H₁ d₂)
    (added_mem_adjoinRepresentative R d₁)
  have hvaH : H.Adj v a := added_mem_adjoinRepresentative H₁ d₂
  have hsubp : ∀ e ∈ p.edges, e ∈ H.edgeSet := fun _ he ↦ edgeSet_mono hRH (p.edges_subset_edgeSet he)
  have hsubq : ∀ e ∈ q.edges, e ∈ H.edgeSet := fun _ he ↦ edgeSet_mono hRH (q.edges_subset_edgeSet he)
  let p' := p.transfer H hsubp
  let q' := q.transfer H hsubq
  let r := p'.append (Walk.cons hbuH q')
  have hrpath : r.IsPath := by
    apply Walk.IsPath.mk'
    simp only [r, p', q', Walk.support_append, Walk.support_cons, List.tail_cons, Walk.support_transfer]
    exact List.nodup_append'.mpr ⟨hp.support_nodup, hq.support_nodup, hdisj⟩
  have hrlen : r.length = p.length + q.length + 1 := by
    simp only [r, p', q', Walk.length_append, Walk.length_cons, Walk.length_transfer]
    omega
  let s := Walk.cons hvaH r
  have hscycle : s.IsCycle := by
    apply (Walk.cons_isCycle_iff r hvaH).mpr
    refine ⟨hrpath, ?_⟩
    intro he
    have h := hrpath.length_eq_one_of_mem_edges (Sym2.eq_swap ▸ he)
    omega
  have hslen : s.length = k := by rw [Walk.length_cons, hrlen]; omega
  obtain ⟨f⟩ := (cycleGraph_isContained_iff (by omega : 2 < k)).mpr ⟨v, s, hscycle, hslen⟩
  exact hH ((Copy.ofLE H ⊤ le_top).comp f) (isRainbow_comp_of_color_injOn le_top c hr f)

end Erdos1105
