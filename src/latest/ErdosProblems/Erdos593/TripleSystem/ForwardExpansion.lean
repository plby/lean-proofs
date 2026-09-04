import ErdosProblems.Erdos593.Graph.Parity
import ErdosProblems.Erdos593.TripleSystem.ExpansionIntrinsic

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Forward properties of private-vertex expansions

The generator side of the finite structural theorem starts with the elementary
intrinsic properties of the private-vertex expansion of a simple graph.
-/

namespace Erdos593

universe u

namespace TripleSystem

/-- Distinct expanded graph edges meet in at most one point. -/
-- ARISTOTLE_TARGET F1
theorem privateVertexExpansion_linear {V : Type u}
    (G : _root_.SimpleGraph V) :
    (privateVertexExpansion G).Linear := by
  unfold TripleSystem.Linear
  intro e f x y hef hxe hxf hye hyf
  change PrivateVertexExpansion.Inc G x e at hxe
  change PrivateVertexExpansion.Inc G x f at hxf
  change PrivateVertexExpansion.Inc G y e at hye
  change PrivateVertexExpansion.Inc G y f at hyf
  rcases x with x | x
  · rcases y with y | y
    · congr 1
      by_contra hxy
      apply hef
      apply Subtype.ext
      exact Sym2.eq_of_ne_mem hxy hxe hye hxf hyf
    · exfalso
      apply hef
      exact hye.symm.trans hyf
  · rcases y with y | y
    · exfalso
      apply hef
      exact hxe.symm.trans hxf
    · exfalso
      apply hef
      exact hxe.symm.trans hxf

/-- A private point of an expanded edge cannot occur on a cycle in the Levi
graph. -/
-- ARISTOTLE_TARGET F3A
theorem privateVertex_not_mem_cycle_support {V : Type u}
    (G : _root_.SimpleGraph V)
    {z : PrivateVertexExpansion.Point G ⊕ PrivateVertexExpansion.Edge G}
    (c : (privateVertexExpansion G).levi.Walk z z) (hc : c.IsCycle)
    (e : PrivateVertexExpansion.Edge G) :
    Sum.inl (PrivateVertexExpansion.privateVertex G e) ∉ c.support := by
  let x := PrivateVertexExpansion.privateVertex G e
  let v : PrivateVertexExpansion.Point G ⊕
      PrivateVertexExpansion.Edge G := Sum.inl x
  have hAdj : (privateVertexExpansion G).levi.Adj v (.inr e) := by
    simp [v, x]
  have hbridge :
      (privateVertexExpansion G).levi.IsBridge s(v, Sum.inr e) := by
    rw [show s(v, Sum.inr e) = s(Sum.inr e, v) from Sym2.eq_swap]
    apply Erdos593.SimpleGraph.isBridge_of_adj_of_unique_neighbor _ hAdj.symm
    intro w hw
    rcases w with y | f
    · exact (not_levi_adj_point_point (privateVertexExpansion G) hw).elim
    · congr 1
      exact (by simpa [v, x] using! hw : e = f).symm
  intro hx
  obtain ⟨a, ha, hxa⟩ :=
    (c.mem_support_iff_exists_mem_edges_of_not_nil hc.not_nil).mp hx
  obtain ⟨w, rfl⟩ := Sym2.mem_iff_exists.mp hxa
  have haw : (privateVertexExpansion G).levi.Adj v w :=
    c.edges_subset_edgeSet ha
  rcases w with y | f
  · exact (not_levi_adj_point_point (privateVertexExpansion G) haw).elim
  · have hef : e = f := by simpa [v, x] using! haw
    subst f
    exact hbridge.notMem_edges_of_isCycle hc ha

/-- A private-free core-to-core trail in an expansion Levi graph contracts to
a graph walk of exactly half its length. -/
-- ARISTOTLE_TARGET F3B
theorem exists_graph_walk_of_privateVertexExpansion_walk {V : Type u}
    (G : _root_.SimpleGraph V) {x y : V}
    (p : (privateVertexExpansion G).levi.Walk
      (Sum.inl (PrivateVertexExpansion.core G x))
      (Sum.inl (PrivateVertexExpansion.core G y)))
    (hp : p.IsTrail)
    (hprivate : ∀ e : PrivateVertexExpansion.Edge G,
      Sum.inl (PrivateVertexExpansion.privateVertex G e) ∉ p.support) :
    ∃ q : G.Walk x y, p.length = 2 * q.length := by
  induction hn : p.length using Nat.strongRec generalizing x y with
  | ind n ih =>
      cases p with
      | nil =>
          exact ⟨.nil, by simpa using! hn.symm⟩
      | @cons _ w _ hxw p =>
          rcases w with w | e
          · exact (not_levi_adj_point_point
              (privateVertexExpansion G) hxw).elim
          · obtain ⟨w, hew, r, rfl⟩ := p.exists_eq_cons_of_ne (by simp)
            rcases w with w | f
            · rcases w with x' | f
              · have hxe : x ∈ (e : Sym2 V) := by simpa using! hxw
                have hx'Inc : (privateVertexExpansion G).Inc
                    (PrivateVertexExpansion.core G x') e := by
                  simpa [PrivateVertexExpansion.core] using! hew
                have hx'e : x' ∈ (e : Sym2 V) :=
                  (privateVertexExpansion_inc_core G x' e).mp hx'Inc
                have hxx' : x ≠ x' := by
                  intro h
                  subst x'
                  have hnot :=
                    (_root_.SimpleGraph.Walk.isTrail_cons hxw
                      (_root_.SimpleGraph.Walk.cons hew r)).mp hp |>.2
                  apply hnot
                  simp [PrivateVertexExpansion.core, Sym2.eq_swap]
                have heq : (e : Sym2 V) = s(x, x') :=
                  (Sym2.mem_and_mem_iff hxx').mp ⟨hxe, hx'e⟩
                have hxx'Edge : s(x, x') ∈ G.edgeSet := by
                  rw [← heq]
                  exact e.property
                have hxx'Adj : G.Adj x x' := by
                  simpa using! hxx'Edge
                have hrtrail : r.IsTrail :=
                  (_root_.SimpleGraph.Walk.isTrail_cons hew r).mp
                    ((_root_.SimpleGraph.Walk.isTrail_cons hxw
                      (_root_.SimpleGraph.Walk.cons hew r)).mp hp).1 |>.1
                have hrprivate : ∀ d : PrivateVertexExpansion.Edge G,
                    Sum.inl (PrivateVertexExpansion.privateVertex G d) ∉
                      r.support := by
                  intro d hd
                  exact hprivate d (by simp [hd])
                have hr_lt : r.length <
                    (_root_.SimpleGraph.Walk.cons hxw
                      (_root_.SimpleGraph.Walk.cons hew r)).length := by
                  simp
                obtain ⟨q, hq⟩ :=
                  ih r.length (by simpa only [hn] using! hr_lt)
                    r hrtrail hrprivate rfl
                refine ⟨q.cons hxx'Adj, ?_⟩
                simp only [_root_.SimpleGraph.Walk.length_cons] at hn ⊢
                omega
              · have hfmem :
                    Sum.inl (PrivateVertexExpansion.privateVertex G f) ∈
                      (_root_.SimpleGraph.Walk.cons hxw
                        (_root_.SimpleGraph.Walk.cons hew r)).support := by
                  simp only [_root_.SimpleGraph.Walk.support_cons, List.mem_cons]
                  exact Or.inr (Or.inr r.start_mem_support)
                exact (hprivate f hfmem).elim
            · exact (not_levi_adj_edge_edge
                (privateVertexExpansion G) hew).elim

/-- The private-vertex expansion of a two-colourable graph has only even
Berge cycles. No finiteness assumption is needed. -/
-- ARISTOTLE_TARGET F3
theorem privateVertexExpansion_evenBergeCycles {V : Type u}
    (G : _root_.SimpleGraph V) (hG : G.Colorable 2) :
    (privateVertexExpansion G).EvenBergeCycles := by
  classical
  intro z c hc
  obtain ⟨x, hx⟩ : ∃ x : V,
      Sum.inl (PrivateVertexExpansion.core G x) ∈ c.support := by
    rcases z with (x | e) | e
    · exact ⟨x, c.start_mem_support⟩
    · exact (privateVertex_not_mem_cycle_support G c hc e
        c.start_mem_support).elim
    · obtain ⟨w, hw, hew⟩ :=
        _root_.SimpleGraph.adj_of_mem_walk_support c hc.not_nil
          c.start_mem_support
      rcases w with (x | f) | f
      · exact ⟨x, hw⟩
      · exact (privateVertex_not_mem_cycle_support G c hc f hw).elim
      · exact (not_levi_adj_edge_edge (privateVertexExpansion G) hew).elim
  let d := c.rotate (Sum.inl (PrivateVertexExpansion.core G x)) hx
  have hdcycle : d.IsCycle := by
    exact hc.rotate hx
  have hdprivate : ∀ e : PrivateVertexExpansion.Edge G,
      Sum.inl (PrivateVertexExpansion.privateVertex G e) ∉ d.support := by
    intro e he
    apply privateVertex_not_mem_cycle_support G c hc e
    exact (c.mem_support_rotate_iff
      (Sum.inl (PrivateVertexExpansion.core G x)) hx).mp he
  obtain ⟨q, hq⟩ :=
    exists_graph_walk_of_privateVertexExpansion_walk G d hdcycle.isTrail
      hdprivate
  have hqeven : Even q.length :=
    (_root_.SimpleGraph.two_colorable_iff_forall_loop_even.mp hG) x q
  obtain ⟨k, hk⟩ := hqeven
  use k
  dsimp only [d] at hq
  simp only [_root_.SimpleGraph.Walk.length_rotate] at hq
  omega

/-- The private-vertex expansion of a two-colourable graph satisfies all three
intrinsic conditions. No finiteness assumption is needed. -/
-- ARISTOTLE_TARGET F4
theorem privateVertexExpansion_intrinsic {V : Type u}
    (G : _root_.SimpleGraph V) (hG : G.Colorable 2) :
    (privateVertexExpansion G).Intrinsic := by
  exact ⟨privateVertexExpansion_linear G,
    privateVertexExpansion_bridgeAtEveryEdge G,
    privateVertexExpansion_evenBergeCycles G hG⟩

end TripleSystem

end Erdos593
