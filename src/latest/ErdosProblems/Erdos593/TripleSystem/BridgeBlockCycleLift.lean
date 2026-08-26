import ErdosProblems.Erdos593.TripleSystem.BridgeBlockContraction
import ErdosProblems.Erdos593.Graph.Parity

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Lifting cycles from contracted bridge-free blocks

An edge of a contracted bridge-free Levi component remembers its unique
degree-two hyperedge-node.  Replacing each contracted edge by the associated
point-hyperedge-point segment lifts walks, paths, and cycles back to the Levi
graph.  The resulting length-doubling statement transfers even-Berge-cycle
parity to ordinary cycle parity in the contracted graph.
-/

namespace Erdos593

open scoped Sym2

universe u v

namespace TripleSystem
namespace BridgeBlock

noncomputable section

variable {V : Type u} {E : Type v} (F : TripleSystem V E)
variable [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
  [DecidableRel F.levi.Adj]

private noncomputable abbrev B := Erdos593.SimpleGraph.bridgeFree F.levi

/-- Canonical hyperedge witness for an edge of the contracted graph. -/
noncomputable def edgeWitness (hlinear : F.Linear) {C : Component F}
    {x y : Point F C} (hxy : (contractedGraph F C).Adj x y) :
    ContractibleEdge F C :=
  Exists.choose (contractedGraph_existsUnique_edge F hlinear hxy)

theorem edgeWitness_spec (hlinear : F.Linear) {C : Component F}
    {x y : Point F C} (hxy : (contractedGraph F C).Adj x y) :
    (B F).Adj (Sum.inl x.1) (Sum.inr (edgeWitness F hlinear hxy).1) ∧
      (B F).Adj (Sum.inl y.1) (Sum.inr (edgeWitness F hlinear hxy).1) :=
  Exists.choose_spec (contractedGraph_existsUnique_edge F hlinear hxy) |>.1

/-- Expand every contracted edge to its two-edge point-hyperedge-point segment. -/
noncomputable def liftWalk (hlinear : F.Linear) {C : Component F} {x y : Point F C} :
    (contractedGraph F C).Walk x y →
      (B F).Walk (Sum.inl x.1) (Sum.inl y.1)
  | .nil => .nil
  | .cons hxy p =>
      .cons (edgeWitness_spec F hlinear hxy).1
        (.cons (edgeWitness_spec F hlinear hxy).2.symm (liftWalk hlinear p))

theorem liftWalk_length (hlinear : F.Linear) {C : Component F}
    {x y : Point F C} (p : (contractedGraph F C).Walk x y) :
    (liftWalk F hlinear p).length = 2 * p.length := by
  induction p with
  | nil => rfl
  | cons h p ih => simp [liftWalk, ih, Nat.mul_add]

/-- Point-nodes in a lift are exactly the lifted contracted-walk vertices. -/
theorem point_mem_liftWalk_support_iff (hlinear : F.Linear)
    {C : Component F} {x y : Point F C}
    (p : (contractedGraph F C).Walk x y) (z : Point F C) :
    Sum.inl z.1 ∈ (liftWalk F hlinear p).support ↔ z ∈ p.support := by
  induction p with
  | nil => simp [liftWalk, Subtype.ext_iff]
  | cons h p ih => simp [liftWalk, ih, Subtype.ext_iff]

/-- Equality of chosen hyperedge witnesses forces equality of the underlying
contracted (undirected) edges.  The degree-two field of `ContractibleEdge` is
the essential input. -/
theorem contracted_edge_eq_of_edgeWitness_eq (hlinear : F.Linear)
    {C : Component F} {x y a b : Point F C}
    (hxy : (contractedGraph F C).Adj x y)
    (hab : (contractedGraph F C).Adj a b)
    (hw : edgeWitness F hlinear hxy = edgeWitness F hlinear hab) :
    s(x, y) = s(a, b) := by
  have hxySpec := edgeWitness_spec F hlinear hxy
  have haAdj :
      (B F).Adj (Sum.inl a.1)
        (Sum.inr (edgeWitness F hlinear hxy).1) := by
    rw [hw]
    exact (edgeWitness_spec F hlinear hab).1
  have hbAdj :
      (B F).Adj (Sum.inl b.1)
        (Sum.inr (edgeWitness F hlinear hxy).1) := by
    rw [hw]
    exact (edgeWitness_spec F hlinear hab).2
  have hxyNe : x ≠ y := ((contractedGraph_adj F C x y).mp hxy).1
  have hxyNodesNe : (Sum.inl x.1 : V ⊕ E) ≠ Sum.inl y.1 := by
    intro h
    apply hxyNe
    exact Subtype.ext (Sum.inl.inj h)
  have hpairSubset :
      ({Sum.inl x.1, Sum.inl y.1} : Finset (V ⊕ E)) ⊆
        (B F).neighborFinset
          (Sum.inr (edgeWitness F hlinear hxy).1) := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact ((B F).mem_neighborFinset _ _).2 hxySpec.1.symm
    · exact ((B F).mem_neighborFinset _ _).2 hxySpec.2.symm
  have hneighborCard :
      ((B F).neighborFinset
          (Sum.inr (edgeWitness F hlinear hxy).1)).card = 2 := by
    rw [_root_.SimpleGraph.card_neighborFinset_eq_degree]
    exact (edgeWitness F hlinear hxy).property.2
  have hpairCard :
      ({Sum.inl x.1, Sum.inl y.1} : Finset (V ⊕ E)).card = 2 := by
    simp [hxyNodesNe]
  have hpairEq :
      ({Sum.inl x.1, Sum.inl y.1} : Finset (V ⊕ E)) =
        (B F).neighborFinset
          (Sum.inr (edgeWitness F hlinear hxy).1) := by
    apply Finset.eq_of_subset_of_card_le hpairSubset
    omega
  have haMem :
      (Sum.inl a.1 : V ⊕ E) ∈
        ({Sum.inl x.1, Sum.inl y.1} : Finset (V ⊕ E)) := by
    rw [hpairEq]
    exact ((B F).mem_neighborFinset _ _).2 haAdj.symm
  have hbMem :
      (Sum.inl b.1 : V ⊕ E) ∈
        ({Sum.inl x.1, Sum.inl y.1} : Finset (V ⊕ E)) := by
    rw [hpairEq]
    exact ((B F).mem_neighborFinset _ _).2 hbAdj.symm
  have haCases : a = x ∨ a = y := by
    simpa only [Finset.mem_insert, Finset.mem_singleton, Sum.inl.injEq,
      Subtype.ext_iff] using! haMem
  have hbCases : b = x ∨ b = y := by
    simpa only [Finset.mem_insert, Finset.mem_singleton, Sum.inl.injEq,
      Subtype.ext_iff] using! hbMem
  have habNe : a ≠ b := ((contractedGraph_adj F C a b).mp hab).1
  rcases haCases with ha | ha <;> rcases hbCases with hb | hb
  · exact (habNe (ha.trans hb.symm)).elim
  · simp [ha, hb]
  · simp [ha, hb]
  · exact (habNe (ha.trans hb.symm)).elim

/-- A contracted edge witness does not occur later in a lifted walk if the
underlying contracted edge does not occur later. -/
theorem edgeWitness_not_mem_liftWalk_support (hlinear : F.Linear)
    {C : Component F} {x y z : Point F C}
    (hxy : (contractedGraph F C).Adj x y)
    (p : (contractedGraph F C).Walk y z)
    (hnot : s(x, y) ∉ p.edges) :
    Sum.inr (edgeWitness F hlinear hxy).1 ∉
      (liftWalk F hlinear p).support := by
  have aux : ∀ {u v : Point F C}
      (q : (contractedGraph F C).Walk u v),
      s(x, y) ∉ q.edges →
        Sum.inr (edgeWitness F hlinear hxy).1 ∉
          (liftWalk F hlinear q).support := by
    intro u v q
    induction q with
    | nil => simp [liftWalk]
    | @cons u w v huw q ih =>
        intro hqnot
        have hqnot' : s(x, y) ≠ s(u, w) ∧ s(x, y) ∉ q.edges := by
          simpa using! hqnot
        have hwitness :
            edgeWitness F hlinear hxy ≠ edgeWitness F hlinear huw := by
          intro hw
          exact hqnot'.1
            (contracted_edge_eq_of_edgeWitness_eq F hlinear hxy huw hw)
        have hwitnessVal :
            (edgeWitness F hlinear hxy).1 ≠
              (edgeWitness F hlinear huw).1 := by
          intro hw
          exact hwitness (Subtype.ext hw)
        have htail := ih hqnot'.2
        simpa [liftWalk, hwitnessVal] using! htail
  exact aux p hnot

/-- Subdivision preserves simple paths. -/
theorem liftWalk_isPath (hlinear : F.Linear) {C : Component F}
    {x y : Point F C} (p : (contractedGraph F C).Walk x y)
    (hp : p.IsPath) :
    (liftWalk F hlinear p).IsPath := by
  induction p with
  | nil => exact _root_.SimpleGraph.Walk.IsPath.nil
  | @cons x y z hxy p ih =>
      have htrail :=
        (_root_.SimpleGraph.Walk.isTrail_cons hxy p).mp hp.isTrail
      rcases (_root_.SimpleGraph.Walk.cons_isPath_iff hxy p).mp hp with
        ⟨hpTail, hxnot⟩
      have htail :
          (_root_.SimpleGraph.Walk.cons
            (edgeWitness_spec F hlinear hxy).2.symm
            (liftWalk F hlinear p)).IsPath :=
        (ih hpTail).cons
          (edgeWitness_not_mem_liftWalk_support F hlinear hxy p htrail.2)
      apply htail.cons
      simp [point_mem_liftWalk_support_iff F hlinear p x, hxnot]

/-- Core proof obligation: subdivision preserves a simple contracted cycle. -/
theorem liftWalk_isCycle (hlinear : F.Linear) {C : Component F}
    {x : Point F C} (c : (contractedGraph F C).Walk x x)
    (hc : c.IsCycle) :
    (liftWalk F hlinear c).IsCycle := by
  cases c with
  | nil => exact (_root_.SimpleGraph.Walk.not_isCycle_nil hc).elim
  | @cons _ y _ hxy p =>
      rcases (_root_.SimpleGraph.Walk.cons_isCycle_iff p hxy).mp hc with
        ⟨hp, hedge⟩
      have htail :
          (_root_.SimpleGraph.Walk.cons
            (edgeWitness_spec F hlinear hxy).2.symm
            (liftWalk F hlinear p)).IsPath :=
        (liftWalk_isPath F hlinear p hp).cons
          (edgeWitness_not_mem_liftWalk_support F hlinear hxy p hedge)
      apply (_root_.SimpleGraph.Walk.isCycle_iff_isPath_tail_and_le_length).2
      constructor
      · simpa [liftWalk] using! htail
      · rw [liftWalk_length]
        have := hc.three_le_length
        omega

/-- Public lift theorem, phrased in the full Levi graph. -/
theorem exists_levi_cycle_of_contractedGraph_cycle
    (hlinear : F.Linear) {C : Component F} {x : Point F C}
    (c : (contractedGraph F C).Walk x x) (hc : c.IsCycle) :
    ∃ d : F.levi.Walk (Sum.inl x.1) (Sum.inl x.1),
      d.IsCycle ∧ d.length = 2 * c.length := by
  let hle : B F ≤ F.levi := by
    dsimp only [B, Erdos593.SimpleGraph.bridgeFree]
    exact F.levi.deleteEdges_le _
  let d := (liftWalk F hlinear c).mapLe hle
  refine ⟨d, ?_, ?_⟩
  · exact (liftWalk_isCycle F hlinear c hc).mapLe hle
  · exact (_root_.SimpleGraph.Walk.length_map
      (_root_.SimpleGraph.Hom.ofLE hle) (liftWalk F hlinear c)).trans
        (liftWalk_length F hlinear c)

/-- Exact parity transfer needed for two-colourability. -/
theorem contractedGraph_every_cycle_even
    (hlinear : F.Linear) (hberge : F.EvenBergeCycles)
    (C : Component F) {x : Point F C}
    (c : (contractedGraph F C).Walk x x) (hc : c.IsCycle) :
    Even c.length := by
  obtain ⟨d, hdcycle, hdlen⟩ :=
    exists_levi_cycle_of_contractedGraph_cycle F hlinear c hc
  obtain ⟨k, hk⟩ := hberge d hdcycle
  use k
  omega

/-- Non-circular endpoint: the contracted graph is two-colourable. -/
theorem contractedGraph_colorable_two
    (hlinear : F.Linear) (hberge : F.EvenBergeCycles)
    (C : Component F) :
    (contractedGraph F C).Colorable 2 := by
  apply (Erdos593.SimpleGraph.two_colorable_iff_every_cycle_even
    (contractedGraph F C)).2
  intro x c hc
  exact contractedGraph_every_cycle_even F hlinear hberge C c hc

end
end BridgeBlock
end TripleSystem
end Erdos593
