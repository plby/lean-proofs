import ErdosProblems.Erdos1105.SeparatedRepresentative
import ErdosProblems.Erdos1105.AdjoinRepresentative
import ErdosProblems.Erdos1105.PathFree

namespace Erdos1105

open SimpleGraph

theorem SeparatedRepresentative.fresh_walk_color {V C : Type*}
    {G R H : SimpleGraph V} {c : Sym2 V → C} (h : SeparatedRepresentative G c R H)
    {a b w : V} (hab : G.Adj a b) (hnot : ¬H.Reachable a b) (p : H.Walk a w)
    {e : Sym2 V} (he : e ∈ p.edges) : c e ≠ c s(a, b) := by
  classical
  induction e using Sym2.inductionOn with
  | _ x y =>
    have hx := p.fst_mem_support_of_mem_edges he
    exact h.fresh a b hab hnot x y (p.edges_subset_edgeSet he) ⟨p.takeUntil x hx⟩

/-- Paths in distinct remaining components can be joined by a fresh
color. Consequently their vertex counts sum to less than `k`. -/
theorem SeparatedRepresentative.two_path_lengths_lt {V C : Type*} {k : ℕ}
    (c : (⊤ : SimpleGraph V).edgeSet → C) {R H : SimpleGraph V}
    (hsep : SeparatedRepresentative ⊤ (extendColor c) R H)
    (hfree : ∀ f : (pathGraph k).Copy (⊤ : SimpleGraph V), ¬IsRainbow f c)
    {a b u v : V} (p : H.Walk a b) (q : H.Walk u v) (hp : p.IsPath) (hq : q.IsPath)
    (hnot : ¬H.Reachable b u) : p.length + q.length + 2 < k := by
  classical
  by_contra! hlen
  have hbu : b ≠ u := fun heq ↦ hnot (heq ▸ Reachable.refl b)
  have hdisj : p.support.Disjoint q.support := by
    intro x hx hy
    exact hnot (((p.dropUntil x hx).reverse.reachable).trans ((q.takeUntil x hy).reverse.reachable))
  let P := p.toSubgraph.spanningCoe
  let Q := q.toSubgraph.spanningCoe
  let T := P ⊔ Q
  have hTH : T ≤ H := sup_le p.toSubgraph.spanningCoe_le q.toSubgraph.spanningCoe_le
  have hmem : ∀ e, e ∈ T.edgeSet ↔ e ∈ p.edges ∨ e ∈ q.edges := by
    intro e
    simp only [T, P, Q, edgeSet_sup, Set.mem_union, Subgraph.edgeSet_spanningCoe,
      Walk.mem_edges_toSubgraph]
  have hrainbow : Set.InjOn (extendColor c) T.edgeSet :=
    hsep.representative.rainbow.mono (edgeSet_mono (hTH.trans hsep.le))
  let d : (⊤ : SimpleGraph V).edgeSet := ⟨s(b, u), hbu⟩
  have hnew : ∀ e ∈ T.edgeSet, extendColor c d.val ≠ extendColor c e := by
    intro e he
    rcases (hmem e).mp he with he | he
    · exact (hsep.fresh_walk_color (by simpa using hbu) hnot p.reverse
        (by simpa only [Walk.edges_reverse, List.mem_reverse] using he)).symm
    · have hnot' : ¬H.Reachable u b := fun h ↦ hnot h.symm
      have h := hsep.fresh_walk_color (by simpa using hbu.symm) hnot' q he
      simpa only [d, Sym2.eq_swap] using h.symm
  let J := adjoinRepresentative T d
  have hJ := adjoinRepresentative_rainbow c T hrainbow d hnew
  have hpJ : ∀ e ∈ p.edges, e ∈ J.edgeSet := fun e he ↦
    edgeSet_mono (le_adjoinRepresentative T d) ((hmem e).mpr (Or.inl he))
  have hqJ : ∀ e ∈ q.edges, e ∈ J.edgeSet := fun e he ↦
    edgeSet_mono (le_adjoinRepresentative T d) ((hmem e).mpr (Or.inr he))
  have hdJ : J.Adj b u := added_mem_adjoinRepresentative T d
  let r := (p.transfer J hpJ).append (Walk.cons hdJ (q.transfer J hqJ))
  have hr : r.IsPath := by
    apply Walk.IsPath.mk'
    simp only [r, Walk.support_append, Walk.support_cons, List.tail_cons, Walk.support_transfer]
    exact List.nodup_append'.mpr ⟨hp.support_nodup, hq.support_nodup, hdisj⟩
  have hrlen : k ≤ r.length + 1 := by
    simp only [r, Walk.length_append, Walk.length_cons, Walk.length_transfer]
    omega
  let f : (pathGraph k).Copy J := hr.pathGraphCopy.comp (pathCopyOfLE hrlen)
  exact hfree ((Copy.ofLE J ⊤ le_top).comp f) (isRainbow_comp_of_color_injOn le_top c hJ f)

end Erdos1105

#print axioms Erdos1105.SeparatedRepresentative.two_path_lengths_lt
