import ErdosProblems.Erdos593.TripleSystem.FiniteLiftGenerated
import ErdosProblems.Erdos593.TripleSystem.DisjointUnionForward
import ErdosProblems.Erdos593.TripleSystem.ForwardExpansion
import ErdosProblems.Erdos593.TripleSystem.IsomorphIntrinsic
import ErdosProblems.Erdos593.TripleSystem.OnePointAmalgamationIntrinsic
import ErdosProblems.Erdos593.Graph.OddClosedWalk

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Berge-cycle traces in a host graph

A finite lift is assembled from private-vertex expansions of finite graph
factors.  A Levi cycle in such an expansion contracts to a closed walk in the
factor graph, with exactly half the length.  `BergeCycleTraceTo` records only
this information.  In particular, the host walk need not be a cycle: keeping
closed walks here avoids an unnecessary cycle-extraction argument during the
structural induction.
-/

namespace Erdos593

universe u w

namespace TripleSystem

variable {V : Type u}

/-- Every Berge cycle of `K` contracts to a closed walk in `G` of exactly half
its Levi length. -/
def BergeCycleTraceTo (G : _root_.SimpleGraph V) (K : TripleSystem X I) : Prop :=
  ∀ ⦃z : X ⊕ I⦄ (c : K.levi.Walk z z), c.IsCycle →
    ∃ (v : V) (q : G.Walk v v), c.length = 2 * q.length

namespace BergeCycleTraceTo

/-- A bounded odd-closed-walk exclusion in the host blocks odd Berge cycles
whose Levi length is at most twice the host cutoff. -/
theorem evenBergeCycles_up_to
    (G : _root_.SimpleGraph V) {K : TripleSystem X I}
    (htrace : BergeCycleTraceTo G K) (m : ℕ)
    (hodd : ∀ ⦃v : V⦄ (q : G.Walk v v), q.length ≤ m → ¬ Odd q.length) :
    ∀ ⦃z : X ⊕ I⦄ (c : K.levi.Walk z z), c.IsCycle →
      c.length ≤ 2 * m → 4 ∣ c.length := by
  intro z c hc hclen
  obtain ⟨v, q, hlen⟩ := htrace c hc
  have hqle : q.length ≤ m := by omega
  have hqeven : Even q.length := Nat.not_odd_iff_even.mp (hodd q hqle)
  obtain ⟨k, hk⟩ := hqeven
  use k
  omega

/-- If Berge cycles in `K` trace to closed walks in `G`, and `G` has no odd
closed walk up to the finite Levi-edge bound for `K`, then `K` has only even
Berge cycles.  This is the bridge used by the final odd-Berge obstruction:
the trace divides the Levi-cycle length by two, and the host odd-girth
hypothesis makes the traced length even. -/
theorem evenBergeCycles_of_no_odd_closedWalk_up_to
    (G : _root_.SimpleGraph V) (K : TripleSystem X I)
    [Fintype K.levi.edgeSet]
    (htrace : BergeCycleTraceTo G K)
    (hG : ∀ ⦃v : V⦄ (q : G.Walk v v),
      q.length ≤ K.levi.edgeFinset.card → ¬ Odd q.length) :
    K.EvenBergeCycles := by
  intro z c hc
  obtain ⟨v, q, hq⟩ := htrace c hc
  have hcBound : c.length ≤ K.levi.edgeFinset.card := by
    exact hc.isTrail.length_le_card_edgeFinset
  have hqBound : q.length ≤ K.levi.edgeFinset.card := by
    rw [hq] at hcBound
    omega
  have hqEven : Even q.length := Nat.not_odd_iff_even.mp (hG q hqBound)
  obtain ⟨k, hk⟩ := hqEven
  use k
  omega

/-- An edgeless triple system has no Berge cycle, so its trace property is
vacuous. -/
theorem edgeless (G : _root_.SimpleGraph V) (X : Type w) :
    BergeCycleTraceTo G (TripleSystem.edgeless X) := by
  intro z c hc
  cases c with
  | nil => exact (hc.not_nil (by simp)).elim
  | @cons _ y _ h p =>
      rcases z with x | e
      · rcases y with y | e
        · exact (TripleSystem.not_levi_adj_point_point
            (TripleSystem.edgeless X) h).elim
        · exact e.down.elim
      · exact e.down.elim

/-- A private-vertex expansion carrying a non-induced factor into `G` has the
host trace property. -/
theorem privateVertexExpansion_of_nonInducedFactor
    (G : _root_.SimpleGraph V) {X : Type w}
    {J : _root_.SimpleGraph X}
    (f : Erdos593.SimpleGraph.NonInducedFactor J G) :
    BergeCycleTraceTo G (privateVertexExpansion J) := by
  classical
  intro z c hc
  obtain ⟨x, hx⟩ : ∃ x : X,
      Sum.inl (PrivateVertexExpansion.core J x) ∈ c.support := by
    rcases z with (x | e) | e
    · exact ⟨x, c.start_mem_support⟩
    · exact (privateVertex_not_mem_cycle_support J c hc e
        c.start_mem_support).elim
    · obtain ⟨y, hy, hey⟩ :=
        _root_.SimpleGraph.adj_of_mem_walk_support c hc.not_nil
          c.start_mem_support
      rcases y with (x | d) | d
      · exact ⟨x, hy⟩
      · exact (privateVertex_not_mem_cycle_support J c hc d hy).elim
      · exact (not_levi_adj_edge_edge (privateVertexExpansion J) hey).elim
  let d := c.rotate (Sum.inl (PrivateVertexExpansion.core J x)) hx
  have hdcycle : d.IsCycle := hc.rotate hx
  have hdprivate : ∀ e : PrivateVertexExpansion.Edge J,
      Sum.inl (PrivateVertexExpansion.privateVertex J e) ∉ d.support := by
    intro e he
    apply privateVertex_not_mem_cycle_support J c hc e
    exact (c.mem_support_rotate_iff
      (Sum.inl (PrivateVertexExpansion.core J x)) hx).mp he
  obtain ⟨q, hq⟩ :=
    exists_graph_walk_of_privateVertexExpansion_walk J d hdcycle.isTrail
      hdprivate
  refine ⟨f.vertex x, f.mapWalk q, ?_⟩
  dsimp only [d] at hq
  simp only [_root_.SimpleGraph.Walk.length_rotate] at hq
  simpa using! hq

/-- The trace property is preserved by disjoint union. -/
theorem disjointUnion
    (G : _root_.SimpleGraph V)
    (F : TripleSystem X I) (H : TripleSystem Y J)
    (hF : BergeCycleTraceTo G F) (hH : BergeCycleTraceTo G H) :
    BergeCycleTraceTo G (F.disjointUnion H) := by
  intro z c hc
  let e := disjointUnionLeviIso F H
  let c' := c.map e.toHom
  have hc' : c'.IsCycle := hc.map e.injective
  have hlength : c'.length = c.length :=
    _root_.SimpleGraph.Walk.length_map e.toHom c
  have left
      {z' : X ⊕ I}
      (d : (F.levi ⊕g H.levi).Walk (.inl z') (.inl z'))
      (hd : d.IsCycle) :
      ∃ (v : V) (q : G.Walk v v), d.length = 2 * q.length := by
    obtain ⟨zF, dF, hdF, hdlength⟩ :=
      exists_cycle_of_sum_inl F.levi H.levi d hd
    obtain ⟨v, q, hq⟩ := hF dF hdF
    exact ⟨v, q, hdlength.trans hq⟩
  have right
      {z' : Y ⊕ J}
      (d : (F.levi ⊕g H.levi).Walk (.inr z') (.inr z'))
      (hd : d.IsCycle) :
      ∃ (v : V) (q : G.Walk v v), d.length = 2 * q.length := by
    obtain ⟨zH, dH, hdH, hdlength⟩ :=
      exists_cycle_of_sum_inr F.levi H.levi d hd
    obtain ⟨v, q, hq⟩ := hH dH hdH
    exact ⟨v, q, hdlength.trans hq⟩
  rcases z with (x | y) | (i | j)
  · obtain ⟨v, q, hq⟩ := left c' hc'
    exact ⟨v, q, hlength.symm.trans hq⟩
  · obtain ⟨v, q, hq⟩ := right c' hc'
    exact ⟨v, q, hlength.symm.trans hq⟩
  · obtain ⟨v, q, hq⟩ := left c' hc'
    exact ⟨v, q, hlength.symm.trans hq⟩
  · obtain ⟨v, q, hq⟩ := right c' hc'
    exact ⟨v, q, hlength.symm.trans hq⟩

/-- The trace property is preserved by one-point amalgamation. -/
theorem amalgam
    (G : _root_.SimpleGraph V)
    (F₀ : TripleSystem X₀ I₀) (F₁ : TripleSystem X₁ I₁)
    (r₀ : X₀) (r₁ : X₁)
    (h₀ : BergeCycleTraceTo G F₀) (h₁ : BergeCycleTraceTo G F₁) :
    BergeCycleTraceTo G (OnePointAmalgamation.amalgam F₀ F₁ r₀ r₁) := by
  intro z c hc
  let f₀ := OnePointAmalgamation.leftLeviEmbedding F₀ F₁ r₀ r₁
  let f₁ := OnePointAmalgamation.rightLeviEmbedding F₀ F₁ r₀ r₁
  let A : Set (OnePointAmalgamation.Vertex r₀ r₁ ⊕
      OnePointAmalgamation.Edge I₀ I₁) := Set.range f₀
  let B : Set (OnePointAmalgamation.Vertex r₀ r₁ ⊕
      OnePointAmalgamation.Edge I₀ I₁) := Set.range f₁
  let root : OnePointAmalgamation.Vertex r₀ r₁ ⊕
      OnePointAmalgamation.Edge I₀ I₁ :=
    .inl (OnePointAmalgamation.left r₀ r₁ r₀)
  have hrootA : root ∈ A := by
    exact ⟨.inl r₀, rfl⟩
  have hrootB : root ∈ B := by
    refine ⟨.inl r₁, ?_⟩
    exact congrArg Sum.inl (OnePointAmalgamation.root_eq r₀ r₁).symm
  have hinter : A ∩ B ⊆ {root} := by
    rintro w ⟨⟨a, rfl⟩, ⟨b, hb⟩⟩
    rcases a with x | e <;> rcases b with y | f
    all_goals
      simp [f₀, f₁, root,
        OnePointAmalgamation.leftLeviEmbedding,
        OnePointAmalgamation.rightLeviEmbedding] at hb ⊢ <;> aesop
  have hadj : ∀ ⦃a b⦄,
      (OnePointAmalgamation.amalgam F₀ F₁ r₀ r₁).levi.Adj a b →
      (a ∈ A ∧ b ∈ A) ∨ (a ∈ B ∧ b ∈ B) := by
    intro a b hab
    rcases a with q | (e | e)
    · rcases b with q' | (f | f)
      · exact ((OnePointAmalgamation.amalgam F₀ F₁ r₀ r₁).not_levi_adj_point_point
          hab).elim
      · have hi := (OnePointAmalgamation.amalgam F₀ F₁ r₀ r₁).levi_adj_point_edge.mp
          hab
        change q ∈ OnePointAmalgamation.left r₀ r₁ '' F₀.edgeSet f at hi
        rcases hi with ⟨x, hx, rfl⟩
        exact Or.inl ⟨⟨.inl x, rfl⟩, ⟨.inr f, rfl⟩⟩
      · have hi := (OnePointAmalgamation.amalgam F₀ F₁ r₀ r₁).levi_adj_point_edge.mp
          hab
        change q ∈ OnePointAmalgamation.right r₀ r₁ '' F₁.edgeSet f at hi
        rcases hi with ⟨y, hy, rfl⟩
        exact Or.inr ⟨⟨.inl y, rfl⟩, ⟨.inr f, rfl⟩⟩
    · rcases b with q' | (f | f)
      · have hi := (OnePointAmalgamation.amalgam F₀ F₁ r₀ r₁).levi_adj_edge_point.mp
          hab
        change q' ∈ OnePointAmalgamation.left r₀ r₁ '' F₀.edgeSet e at hi
        rcases hi with ⟨x, hx, rfl⟩
        exact Or.inl ⟨⟨.inr e, rfl⟩, ⟨.inl x, rfl⟩⟩
      · exact ((OnePointAmalgamation.amalgam F₀ F₁ r₀ r₁).not_levi_adj_edge_edge
          hab).elim
      · exact ((OnePointAmalgamation.amalgam F₀ F₁ r₀ r₁).not_levi_adj_edge_edge
          hab).elim
    · rcases b with q' | (f | f)
      · have hi := (OnePointAmalgamation.amalgam F₀ F₁ r₀ r₁).levi_adj_edge_point.mp
          hab
        change q' ∈ OnePointAmalgamation.right r₀ r₁ '' F₁.edgeSet e at hi
        rcases hi with ⟨y, hy, rfl⟩
        exact Or.inr ⟨⟨.inr e, rfl⟩, ⟨.inl y, rfl⟩⟩
      · exact ((OnePointAmalgamation.amalgam F₀ F₁ r₀ r₁).not_levi_adj_edge_edge
          hab).elim
      · exact ((OnePointAmalgamation.amalgam F₀ F₁ r₀ r₁).not_levi_adj_edge_edge
          hab).elim
  rcases OnePointAmalgamation.cycle_support_in_one_of_two_sets
      (OnePointAmalgamation.amalgam F₀ F₁ r₀ r₁).levi A B root
      hrootA hrootB hinter hadj c hc with hsupp | hsupp
  · obtain ⟨x, d, hd, hlength⟩ :=
      OnePointAmalgamation.cycle_lifts_through_embedding f₀ c hc hsupp
    obtain ⟨v, q, hq⟩ := h₀ d hd
    exact ⟨v, q, hlength.trans hq⟩
  · obtain ⟨y, d, hd, hlength⟩ :=
      OnePointAmalgamation.cycle_lifts_through_embedding f₁ c hc hsupp
    obtain ⟨v, q, hq⟩ := h₁ d hd
    exact ⟨v, q, hlength.trans hq⟩

/-- The trace property is invariant under relabelling of the triple system. -/
theorem ofIso
    (G : _root_.SimpleGraph V)
    {F : TripleSystem X I} {H : TripleSystem Y J}
    (hF : BergeCycleTraceTo G F) (f : TripleSystem.Iso F H) :
    BergeCycleTraceTo G H := by
  intro z c hc
  let e := TripleSystem.Iso.leviIso f
  let d := c.map e.symm.toHom
  have hd : d.IsCycle := hc.map e.symm.injective
  obtain ⟨v, q, hq⟩ := hF d hd
  refine ⟨v, q, ?_⟩
  have hlength : d.length = c.length :=
    _root_.SimpleGraph.Walk.length_map e.symm.toHom c
  exact hlength.symm.trans hq

end BergeCycleTraceTo

namespace FiniteLiftGenerated

/-- Every system generated by finite host-factor expansions has a
length-preserving Berge-cycle trace in the host graph. -/
theorem bergeCycleTraceTo
    (G : _root_.SimpleGraph V)
    {X I : Type w} {K : TripleSystem X I}
    (hK : FiniteLiftGenerated G K) :
    BergeCycleTraceTo G K := by
  induction hK with
  | ofEdgeless X =>
      exact BergeCycleTraceTo.edgeless G X
  | ofFactorExpansion f =>
      exact BergeCycleTraceTo.privateVertexExpansion_of_nonInducedFactor G f
  | disjointUnion hF hH ihF ihH =>
      exact BergeCycleTraceTo.disjointUnion G _ _ ihF ihH
  | amalgam hF hH x y ihF ihH =>
      exact BergeCycleTraceTo.amalgam G _ _ x y ihF ihH
  | ofIso hF f ihF =>
      exact BergeCycleTraceTo.ofIso G ihF f

end FiniteLiftGenerated

end TripleSystem

end Erdos593
