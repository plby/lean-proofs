import ErdosProblems.Erdos593.TripleSystem.BridgeBlockPackaging
import ErdosProblems.Erdos593.TripleSystem.Constructive
import ErdosProblems.Erdos593.TripleSystem.EdgeRestriction

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Exact restrictions represented by active bridge-free blocks

An active bridge-free Levi component represents not merely an embedded
private-vertex expansion, but the exact restriction of the original triple
system to the hyperedges whose Levi nodes lie in that component.  The main
point is vertex surjectivity: the support of those hyperedges consists exactly
of the component's point-nodes together with the unique private point of each
component hyperedge.
-/

namespace Erdos593

open scoped Sym2

universe u v w

namespace TripleSystem
namespace BridgeBlock

noncomputable section

variable {V : Type u} {E : Type v} (F : TripleSystem V E)
variable [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
  [DecidableRel F.levi.Adj]

private noncomputable abbrev restrictionCore :=
  Erdos593.SimpleGraph.bridgeFree F.levi

/-- The original hyperedges whose Levi nodes belong to a bridge-free
component. -/
def componentHyperedgeSet (C : Component F) : Set E :=
  {e | Sum.inr e ∈ C.supp}

@[simp]
theorem mem_componentHyperedgeSet_iff {C : Component F} {e : E} :
    e ∈ componentHyperedgeSet F C ↔ Sum.inr e ∈ C.supp :=
  Iff.rfl

/-- Every point-node of an active component lies on a hyperedge belonging to
that component. -/
theorem point_mem_componentHyperedgeSupport {C : Component F}
    (hC : HasIncidence F C) (x : Point F C) :
    x.1 ∈ F.edgeSupportSet (componentHyperedgeSet F C) := by
  rcases hC with ⟨u, e, huC, heC, hue⟩
  have hreach : (restrictionCore F).Reachable (Sum.inl x.1) (Sum.inr e) :=
    C.reachable_of_mem_supp x.2 heC
  have hne : (Sum.inl x.1 : V ⊕ E) ≠ Sum.inr e := by simp
  obtain ⟨z, hxz⟩ := hreach.nonempty_neighborSet_left hne
  rcases z with y | f
  · exact (F.not_levi_adj_point_point
      ((show restrictionCore F ≤ F.levi by
        dsimp only [restrictionCore, Erdos593.SimpleGraph.bridgeFree]
        exact F.levi.deleteEdges_le _) hxz)).elim
  · have hfC : Sum.inr f ∈ C.supp :=
      C.mem_supp_of_adj_mem_supp x.2 hxz
    refine ⟨f, hfC, ?_⟩
    apply F.levi_adj_point_edge.mp
    exact (show restrictionCore F ≤ F.levi by
      dsimp only [restrictionCore, Erdos593.SimpleGraph.bridgeFree]
      exact F.levi.deleteEdges_le _) hxz

/-- The vertex map of the component expansion, with codomain restricted to
the exact support of the component hyperedges. -/
noncomputable def componentExpansionSupportMap
    (hlinear : F.Linear) {C : Component F} (hC : HasIncidence F C) :
    PrivateVertexExpansion.Point (contractedGraph F C) →
      F.EdgeSupport (componentHyperedgeSet F C)
  | .inl x =>
      ⟨x.1, point_mem_componentHyperedgeSupport F hC x⟩
  | .inr a =>
      ⟨privatePoint F (graphEdgeWitness F hlinear (C := C) a),
        ⟨(graphEdgeWitness F hlinear (C := C) a).1,
          (graphEdgeWitness F hlinear (C := C) a).2.1,
          (privatePoint_spec F
            (graphEdgeWitness F hlinear (C := C) a)).1⟩⟩

theorem componentExpansionSupportMap_injective
    (hlinear : F.Linear) {C : Component F} (hC : HasIncidence F C) :
    Function.Injective (componentExpansionSupportMap F hlinear hC) := by
  intro p q hpq
  apply (componentExpansionEmbedding F hlinear C).vertex.injective
  have hpqVal := congrArg Subtype.val hpq
  rcases p with x | a <;> rcases q with y | b <;>
    exact hpqVal

theorem componentExpansionSupportMap_surjective
    (hlinear : F.Linear) (hbridge : F.BridgeAtEveryEdge)
    {C : Component F} (hC : HasIncidence F C) :
    Function.Surjective (componentExpansionSupportMap F hlinear hC) := by
  intro z
  rcases z.2 with ⟨e, heC, hze⟩
  let eC : Hyperedge F C := ⟨e, heC⟩
  let edgeEquiv := graphEdgeEquivHyperedge F hlinear hbridge hC
  let a : (contractedGraph F C).edgeSet := edgeEquiv.symm eC
  have ha : edgeEquiv a = eC := edgeEquiv.apply_symm_apply eC
  have hwitness :
      (graphEdgeWitness F hlinear (C := C) a).1 = e := by
    have hval := congrArg Subtype.val ha
    simpa [edgeEquiv, graphEdgeEquivHyperedge,
      graphEdgeEquivContractibleEdge, contractibleEdgeEquivHyperedge] using! hval
  have hzWitness :
      F.Inc z.1 (graphEdgeWitness F hlinear (C := C) a).1 := by
    rw [hwitness]
    exact hze
  rcases (inc_iff_bridgeFree_or_privatePoint F
      (graphEdgeWitness F hlinear (C := C) a) z.1).mp hzWitness with
    hcore | hprivate
  · have hzC : Sum.inl z.1 ∈ C.supp :=
      C.mem_supp_of_adj_mem_supp
        (graphEdgeWitness F hlinear (C := C) a).2.1 hcore.symm
    let x : Point F C := ⟨z.1, hzC⟩
    refine ⟨Sum.inl x, ?_⟩
    apply Subtype.ext
    rfl
  · refine ⟨Sum.inr a, ?_⟩
    apply Subtype.ext
    exact hprivate.symm

/-- The exact vertex equivalence between an active component expansion and
the support of the corresponding original hyperedges. -/
noncomputable def componentExpansionVertexEquiv
    (hlinear : F.Linear) (hbridge : F.BridgeAtEveryEdge)
    {C : Component F} (hC : HasIncidence F C) :
    PrivateVertexExpansion.Point (contractedGraph F C) ≃
      F.EdgeSupport (componentHyperedgeSet F C) :=
  Equiv.ofBijective (componentExpansionSupportMap F hlinear hC)
    ⟨componentExpansionSupportMap_injective F hlinear hC,
      componentExpansionSupportMap_surjective F hlinear hbridge hC⟩

/-- The canonical equivalence from contracted graph edges to the exact
component-hyperedge subtype used by `edgeRestriction`. -/
noncomputable def componentExpansionEdgeEquiv
    (hlinear : F.Linear) (hbridge : F.BridgeAtEveryEdge)
    {C : Component F} (hC : HasIncidence F C) :
    (contractedGraph F C).edgeSet ≃ componentHyperedgeSet F C := by
  change (contractedGraph F C).edgeSet ≃ Hyperedge F C
  exact graphEdgeEquivHyperedge F hlinear hbridge hC

@[simp]
theorem componentExpansionEdgeEquiv_val
    (hlinear : F.Linear) (hbridge : F.BridgeAtEveryEdge)
    {C : Component F} (hC : HasIncidence F C)
    (a : (contractedGraph F C).edgeSet) :
    (componentExpansionEdgeEquiv F hlinear hbridge hC a).1 =
      (graphEdgeWitness F hlinear (C := C) a).1 :=
  rfl

@[simp]
theorem componentExpansionSupportMap_val
    (hlinear : F.Linear) {C : Component F} (hC : HasIncidence F C)
    (p : PrivateVertexExpansion.Point (contractedGraph F C)) :
    (componentExpansionSupportMap F hlinear hC p).1 =
      (componentExpansionEmbedding F hlinear C).vertex p := by
  rcases p with x | a <;> rfl

/-- An active bridge-free component is exactly the restriction to its own
hyperedges, not merely an embedded copy of their private-vertex expansion. -/
noncomputable def activeComponentExpansionRestrictionIso
    (hlinear : F.Linear) (hbridge : F.BridgeAtEveryEdge)
    {C : Component F} (hC : HasIncidence F C) :
    Iso (privateVertexExpansion (contractedGraph F C))
      (F.edgeRestriction (componentHyperedgeSet F C)) where
  vertexEquiv := componentExpansionVertexEquiv F hlinear hbridge hC
  edgeEquiv := componentExpansionEdgeEquiv F hlinear hbridge hC
  map_inc_iff := by
    intro p a
    let emb := componentExpansionEmbedding F hlinear C
    have hset := Set.ext_iff.mp (emb.map_edge a) (emb.vertex p)
    change (privateVertexExpansion (contractedGraph F C)).Inc p a ↔
      F.Inc
        (componentExpansionSupportMap F hlinear hC p).1
        (componentExpansionEdgeEquiv F hlinear hbridge hC a).1
    rw [componentExpansionSupportMap_val, componentExpansionEdgeEquiv_val]
    change _ ↔ F.Inc
      ((componentExpansionEmbedding F hlinear C).vertex p)
      ((componentExpansionEmbedding F hlinear C).edge a)
    constructor
    · intro hp
      apply hset.mp
      exact ⟨p, hp, rfl⟩
    · intro hp
      rcases hset.mpr hp with ⟨q, hqa, hqp⟩
      have hq : q = p := emb.vertex.injective hqp
      subst q
      exact hqa

section Constructible

variable {V₀ E₀ : Type w} (K : TripleSystem V₀ E₀)
variable [Fintype V₀] [Fintype E₀] [DecidableEq V₀] [DecidableEq E₀]
  [DecidableRel K.levi.Adj]

/-- If the ambient finite system has the intrinsic hypotheses needed to
two-colour the contracted graph, then its exact active-component restriction
is a member of the constructive class. -/
theorem activeComponentRestriction_constructible
    (hlinear : K.Linear) (hbridge : K.BridgeAtEveryEdge)
    (hberge : K.EvenBergeCycles) {C : Component K}
    (hC : HasIncidence K C) :
    Constructible (K.edgeRestriction (componentHyperedgeSet K C)) := by
  letI : Fintype (Point K C) := Fintype.ofFinite (Point K C)
  have hExpansion :
      Constructible (privateVertexExpansion (contractedGraph K C)) :=
    Constructible.ofExpansion (contractedGraph K C)
      (contractedGraph_colorable_two K hlinear hberge C)
  exact Constructible.ofIso hExpansion
    (activeComponentExpansionRestrictionIso K hlinear hbridge hC)

end Constructible

end
end BridgeBlock
end TripleSystem
end Erdos593
