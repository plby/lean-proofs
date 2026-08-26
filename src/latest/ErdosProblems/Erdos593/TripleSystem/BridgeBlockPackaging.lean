import ErdosProblems.Erdos593.TripleSystem.BridgeBlockExpansion
import ErdosProblems.Erdos593.TripleSystem.Embedding
import ErdosProblems.Erdos593.TripleSystem.Expansion

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Erdos593

open scoped Sym2

universe u v

namespace TripleSystem
namespace BridgeBlock

noncomputable section

variable {V : Type u} {E : Type v} (F : TripleSystem V E)
variable [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
  [DecidableRel F.levi.Adj]

private noncomputable abbrev packagingCore :=
  Erdos593.SimpleGraph.bridgeFree F.levi

/-- The unique contractible hyperedge represented by an edge of the
contracted graph. -/
noncomputable def graphEdgeWitness (hlinear : F.Linear) {C : Component F} :
    (contractedGraph F C).edgeSet → ContractibleEdge F C := by
  intro a
  let x := a.1.out.1
  let y := a.1.out.2
  have hxy : (contractedGraph F C).Adj x y := by
    change Quot.mk (Sym2.Rel (Point F C)) a.1.out ∈
      (contractedGraph F C).edgeSet
    simpa only [Quot.out_eq] using! a.2
  exact edgeWitness F hlinear hxy

theorem graphEdgeWitness_spec (hlinear : F.Linear) {C : Component F}
    (a : (contractedGraph F C).edgeSet) :
    (Erdos593.SimpleGraph.bridgeFree F.levi).Adj
        (Sum.inl a.1.out.1.1)
        (Sum.inr (graphEdgeWitness F hlinear (C := C) a).1) ∧
      (Erdos593.SimpleGraph.bridgeFree F.levi).Adj
        (Sum.inl a.1.out.2.1)
        (Sum.inr (graphEdgeWitness F hlinear (C := C) a).1) := by
  unfold graphEdgeWitness
  dsimp only
  exact edgeWitness_spec F hlinear _

/-- Contracted graph edges and degree-two hyperedge-nodes are in canonical
bijection. -/
-- ARISTOTLE_REVERSE_TARGET P1
theorem graphEdgeWitness_bijective (hlinear : F.Linear) (C : Component F) :
    Function.Bijective (graphEdgeWitness F hlinear (C := C)) := by
  constructor
  · intro a b hw
    apply Subtype.ext
    have ha : (contractedGraph F C).Adj a.1.out.1 a.1.out.2 := by
      change Quot.mk (Sym2.Rel (Point F C)) a.1.out ∈
        (contractedGraph F C).edgeSet
      simpa only [Quot.out_eq] using! a.2
    have hb : (contractedGraph F C).Adj b.1.out.1 b.1.out.2 := by
      change Quot.mk (Sym2.Rel (Point F C)) b.1.out ∈
        (contractedGraph F C).edgeSet
      simpa only [Quot.out_eq] using! b.2
    have hw' : edgeWitness F hlinear ha = edgeWitness F hlinear hb := by
      simpa only [graphEdgeWitness] using! hw
    have hout := contracted_edge_eq_of_edgeWitness_eq F hlinear ha hb hw'
    exact a.1.out_eq.symm.trans (hout.trans b.1.out_eq)
  · intro e
    let B := packagingCore F
    have hcard : (B.neighborFinset (Sum.inr e.1)).card = 2 := by
      rw [_root_.SimpleGraph.card_neighborFinset_eq_degree]
      exact e.2.2
    obtain ⟨z, w, hzw, hneighbors⟩ := Finset.card_eq_two.mp hcard
    have hzmem : z ∈ B.neighborFinset (Sum.inr e.1) := by
      rw [hneighbors]
      simp
    have hwmem : w ∈ B.neighborFinset (Sum.inr e.1) := by
      rw [hneighbors]
      simp
    have hze : B.Adj (Sum.inr e.1) z :=
      (B.mem_neighborFinset _ _).mp hzmem
    have hwe : B.Adj (Sum.inr e.1) w :=
      (B.mem_neighborFinset _ _).mp hwmem
    have hle : B ≤ F.levi := by
      dsimp only [B, packagingCore, Erdos593.SimpleGraph.bridgeFree]
      exact F.levi.deleteEdges_le _
    rcases z with x | f
    · rcases w with y | g
      · change (packagingCore F).Adj (Sum.inr e.1) (Sum.inl x) at hze
        change (packagingCore F).Adj (Sum.inr e.1) (Sum.inl y) at hwe
        have hxC : Sum.inl x ∈ C.supp :=
          C.mem_supp_of_adj_mem_supp e.2.1 hze
        have hyC : Sum.inl y ∈ C.supp :=
          C.mem_supp_of_adj_mem_supp e.2.1 hwe
        let px : Point F C := ⟨x, hxC⟩
        let py : Point F C := ⟨y, hyC⟩
        have hxy : px ≠ py := by
          intro h
          apply hzw
          simpa [px, py] using! congrArg Subtype.val h
        have hadj : (contractedGraph F C).Adj px py := by
          refine (contractedGraph_adj F C px py).mpr ⟨hxy, e, ?_, ?_⟩
          · exact hze.symm
          · exact hwe.symm
        let a : (contractedGraph F C).edgeSet :=
          ⟨s(px, py), hadj⟩
        refine ⟨a, ?_⟩
        have houtAdj : (contractedGraph F C).Adj a.1.out.1 a.1.out.2 := by
          change Quot.mk (Sym2.Rel (Point F C)) a.1.out ∈
            (contractedGraph F C).edgeSet
          simpa only [Quot.out_eq] using! a.2
        have hout1 : a.1.out.1 = px ∨ a.1.out.1 = py := by
          simpa only [a, Sym2.mem_iff] using! Sym2.out_fst_mem a.1
        have hout2 : a.1.out.2 = px ∨ a.1.out.2 = py := by
          simpa only [a, Sym2.mem_iff] using! Sym2.out_snd_mem a.1
        have heout1 : (packagingCore F).Adj
            (Sum.inl a.1.out.1.1) (Sum.inr e.1) := by
          rcases hout1 with h | h
          · simpa only [h] using! hze.symm
          · simpa only [h] using! hwe.symm
        have heout2 : (packagingCore F).Adj
            (Sum.inl a.1.out.2.1) (Sum.inr e.1) := by
          rcases hout2 with h | h
          · simpa only [h] using! hze.symm
          · simpa only [h] using! hwe.symm
        apply (contractedGraph_existsUnique_edge F hlinear houtAdj).unique
        · exact graphEdgeWitness_spec F hlinear a
        · exact ⟨heout1, heout2⟩
      · exact (F.not_levi_adj_edge_edge (hle hwe)).elim
    · exact (F.not_levi_adj_edge_edge (hle hze)).elim

/-- The resulting canonical edge equivalence. -/
noncomputable def graphEdgeEquivContractibleEdge (hlinear : F.Linear)
    (C : Component F) :
    (contractedGraph F C).edgeSet ≃ ContractibleEdge F C :=
  Equiv.ofBijective (graphEdgeWitness F hlinear (C := C))
    (graphEdgeWitness_bijective F hlinear C)

/-- In an active component, the degree-two hyperedge subtype is canonically
equivalent to the subtype of all component hyperedges. -/
-- ARISTOTLE_REVERSE_TARGET P2
noncomputable def contractibleEdgeEquivHyperedge
    (hbridge : F.BridgeAtEveryEdge) {C : Component F}
    (hC : HasIncidence F C) : ContractibleEdge F C ≃ Hyperedge F C := by
  exact
    { toFun := fun e => ⟨e.1, e.2.1⟩
      invFun := contractibleEdgeOfHyperedge F hbridge hC
      left_inv := by
        intro e
        apply Subtype.ext
        rfl
      right_inv := by
        intro e
        apply Subtype.ext
        rfl }

/-- Contracted graph edges are canonically equivalent to the original
hyperedges belonging to an active bridge-free component. -/
noncomputable def graphEdgeEquivHyperedge
    (hlinear : F.Linear) (hbridge : F.BridgeAtEveryEdge)
    {C : Component F} (hC : HasIncidence F C) :
    (contractedGraph F C).edgeSet ≃ Hyperedge F C :=
  (graphEdgeEquivContractibleEdge F hlinear C).trans
    (contractibleEdgeEquivHyperedge F hbridge hC)

/-- Membership in a contracted ordinary edge is exactly surviving
bridge-free incidence with its hyperedge witness. -/
-- ARISTOTLE_REVERSE_TARGET P3
theorem mem_graphEdge_iff_bridgeFree_adj_graphEdgeWitness
    (hlinear : F.Linear) {C : Component F}
    (a : (contractedGraph F C).edgeSet) (x : Point F C) :
    x ∈ (a.1 : Sym2 (Point F C)) ↔
      (packagingCore F).Adj (Sum.inl x.1)
        (Sum.inr (graphEdgeWitness F hlinear (C := C) a).1) := by
  have hspec := graphEdgeWitness_spec F hlinear a
  change (packagingCore F).Adj
        (Sum.inl a.1.out.1.1)
        (Sum.inr (graphEdgeWitness F hlinear (C := C) a).1) ∧
      (packagingCore F).Adj
        (Sum.inl a.1.out.2.1)
        (Sum.inr (graphEdgeWitness F hlinear (C := C) a).1) at hspec
  have houtAdj : (contractedGraph F C).Adj a.1.out.1 a.1.out.2 := by
    change Quot.mk (Sym2.Rel (Point F C)) a.1.out ∈
      (contractedGraph F C).edgeSet
    simpa only [Quot.out_eq] using! a.2
  have houtNe : a.1.out.1 ≠ a.1.out.2 :=
    ((contractedGraph_adj F C _ _).mp houtAdj).1
  constructor
  · intro hx
    have hx' : x ∈ s(a.1.out.1, a.1.out.2) := by
      change x ∈ Quot.mk (Sym2.Rel (Point F C)) a.1.out
      simpa only [Quot.out_eq] using! hx
    rcases (Sym2.mem_iff.mp hx') with h | h
    · simpa only [h] using! hspec.1
    · simpa only [h] using! hspec.2
  · intro hx
    have hnodesNe : (Sum.inl a.1.out.1.1 : V ⊕ E) ≠
        Sum.inl a.1.out.2.1 := by
      intro h
      apply houtNe
      apply Subtype.ext
      exact Sum.inl.inj h
    have hpairSubset :
        ({Sum.inl a.1.out.1.1, Sum.inl a.1.out.2.1} : Finset (V ⊕ E)) ⊆
          (packagingCore F).neighborFinset
            (Sum.inr (graphEdgeWitness F hlinear (C := C) a).1) := by
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl
      · exact ((packagingCore F).mem_neighborFinset _ _).mpr hspec.1.symm
      · exact ((packagingCore F).mem_neighborFinset _ _).mpr hspec.2.symm
    have hneighborCard :
        ((packagingCore F).neighborFinset
          (Sum.inr (graphEdgeWitness F hlinear (C := C) a).1)).card = 2 := by
      rw [_root_.SimpleGraph.card_neighborFinset_eq_degree]
      exact (graphEdgeWitness F hlinear (C := C) a).2.2
    have hpairCard :
        ({Sum.inl a.1.out.1.1, Sum.inl a.1.out.2.1} :
          Finset (V ⊕ E)).card = 2 := by
      simp [hnodesNe]
    have hpairEq :
        ({Sum.inl a.1.out.1.1, Sum.inl a.1.out.2.1} : Finset (V ⊕ E)) =
          (packagingCore F).neighborFinset
            (Sum.inr (graphEdgeWitness F hlinear (C := C) a).1) := by
      apply Finset.eq_of_subset_of_card_le hpairSubset
      omega
    have hxMem : (Sum.inl x.1 : V ⊕ E) ∈
        ({Sum.inl a.1.out.1.1, Sum.inl a.1.out.2.1} : Finset (V ⊕ E)) := by
      rw [hpairEq]
      exact ((packagingCore F).mem_neighborFinset _ _).mpr hx.symm
    have hxCases : x = a.1.out.1 ∨ x = a.1.out.2 := by
      simpa only [Finset.mem_insert, Finset.mem_singleton, Sum.inl.injEq,
        Subtype.ext_iff] using! hxMem
    rcases hxCases with h | h
    · rw [h]
      exact Sym2.out_fst_mem a.1
    · rw [h]
      exact Sym2.out_snd_mem a.1

/-- The contracted graph of any bridge-free component embeds back into the
original triple system through its canonical private-vertex expansion. -/
noncomputable def componentExpansionEmbedding
    (hlinear : F.Linear) (C : Component F) :
    (privateVertexExpansion (contractedGraph F C)).Embedding F := by
  let G := contractedGraph F C
  let witness : G.edgeSet → ContractibleEdge F C :=
    graphEdgeWitness F hlinear (C := C)
  let vertexMap : PrivateVertexExpansion.Point G → V
    | .inl x => x.1
    | .inr a => privatePoint F (witness a)
  have hvertexMap : Function.Injective vertexMap := by
    intro p q hpq
    rcases p with x | a <;> rcases q with y | b
    · change x.1 = y.1 at hpq
      exact congrArg Sum.inl (Subtype.ext hpq)
    · exfalso
      change x.1 = privatePoint F (witness b) at hpq
      apply privatePoint_not_mem_component F (witness b)
      rw [← hpq]
      exact x.2
    · exfalso
      change privatePoint F (witness a) = y.1 at hpq
      apply privatePoint_not_mem_component F (witness a)
      rw [hpq]
      exact y.2
    · change privatePoint F (witness a) = privatePoint F (witness b) at hpq
      have hab : a = b := (graphEdgeWitness_bijective F hlinear C).1
        (privatePoint_injective F C hpq)
      exact congrArg Sum.inr hab
  let vertexEmbedding : PrivateVertexExpansion.Point G ↪ V :=
    { toFun := vertexMap
      inj' := hvertexMap }
  exact
    { vertex := vertexEmbedding
      edge := fun a => (witness a).1
      map_edge := by
        intro a
        ext z
        constructor
        · rintro ⟨p, hp, rfl⟩
          change (privateVertexExpansion G).Inc p a at hp
          rcases p with x | b
          · change x ∈ (a.1 : Sym2 (Point F C)) at hp
            apply (inc_iff_bridgeFree_or_privatePoint F (witness a) x.1).mpr
            left
            exact (mem_graphEdge_iff_bridgeFree_adj_graphEdgeWitness
              F hlinear a x).mp hp
          · change b = a at hp
            subst b
            exact (privatePoint_spec F (witness a)).1
        · intro hz
          change F.Inc z (witness a).1 at hz
          rcases (inc_iff_bridgeFree_or_privatePoint F (witness a) z).mp hz with
            hcore | hprivate
          · have hzC : Sum.inl z ∈ C.supp :=
              C.mem_supp_of_adj_mem_supp (witness a).2.1 hcore.symm
            let x : Point F C := ⟨z, hzC⟩
            refine ⟨Sum.inl x, ?_, ?_⟩
            · change x ∈ (a.1 : Sym2 (Point F C))
              exact (mem_graphEdge_iff_bridgeFree_adj_graphEdgeWitness
                F hlinear a x).mpr hcore
            · rfl
          · refine ⟨Sum.inr a, ?_, ?_⟩
            · rfl
            · exact hprivate.symm }

/-- The full reverse package carried by an active bridge-free component:
its graph edges cover exactly all component hyperedges, and its canonical
private-vertex expansion embeds into the original triple system. -/
structure ActiveComponentExpansionPackage (C : Component F) where
  edgeEquiv : (contractedGraph F C).edgeSet ≃ Hyperedge F C
  embedding : (privateVertexExpansion (contractedGraph F C)).Embedding F

/-- Assemble the active-component edge coverage and expansion embedding. -/
noncomputable def activeComponentExpansionPackage
    (hlinear : F.Linear) (hbridge : F.BridgeAtEveryEdge)
    {C : Component F} (hC : HasIncidence F C) :
    ActiveComponentExpansionPackage F C where
  edgeEquiv := graphEdgeEquivHyperedge F hlinear hbridge hC
  embedding := componentExpansionEmbedding F hlinear C

/-- Every active bridge-free block is represented by an embedded
private-vertex expansion of its contracted two-colourable graph. -/
-- ARISTOTLE_REVERSE_TARGET P4
noncomputable def activeComponentExpansionEmbedding
    (hlinear : F.Linear) (hbridge : F.BridgeAtEveryEdge)
    {C : Component F} (hC : HasIncidence F C) :
    (privateVertexExpansion (contractedGraph F C)).Embedding F :=
  (activeComponentExpansionPackage F hlinear hbridge hC).embedding

end
end BridgeBlock
end TripleSystem
end Erdos593
