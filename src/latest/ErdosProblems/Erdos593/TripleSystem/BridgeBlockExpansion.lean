import ErdosProblems.Erdos593.TripleSystem.BridgeBlockCycleLift

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Reconstructing expansion data inside bridge-free Levi blocks

The bridge-free incidences at a hyperedge-node form the two core incidences of
an expansion edge.  The unique deleted incidence supplies its private point.
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

private noncomputable abbrev expansionCore :=
  Erdos593.SimpleGraph.bridgeFree F.levi

/-- Hyperedge-nodes lying in a bridge-free Levi component. -/
abbrev Hyperedge (C : Component F) :=
  {e : E // Sum.inr e ∈ C.supp}

/-- A degree-two hyperedge-node has exactly one original incidence deleted by
the bridge-free reduction. -/
theorem contractibleEdge_existsUnique_privatePoint
    {C : Component F} (e : ContractibleEdge F C) :
    ∃! x : V,
      F.Inc x e.1 ∧ ¬(expansionCore F).Adj (Sum.inl x) (Sum.inr e.1) := by
  classical
  let T := F.levi.neighborFinset (Sum.inr e.1)
  let S := (expansionCore F).neighborFinset (Sum.inr e.1)
  have hle : expansionCore F ≤ F.levi := by
    dsimp only [expansionCore, Erdos593.SimpleGraph.bridgeFree]
    exact F.levi.deleteEdges_le _
  have hsub : S ⊆ T := by
    intro z hz
    rw [_root_.SimpleGraph.mem_neighborFinset] at hz ⊢
    exact hle hz
  have hdeg : F.levi.degree (Sum.inr e.1) = 3 := by
    rw [(_root_.SimpleGraph.card_neighborFinset_eq_degree
          F.levi (Sum.inr e.1)).symm,
      _root_.SimpleGraph.neighborFinset_def,
      (Set.ncard_eq_toFinset_card'
        (F.levi.neighborSet (Sum.inr e.1))).symm]
    exact F.levi_edge_neighbor_ncard e.1
  have hTcard : T.card = 3 := by
    dsimp only [T]
    rw [_root_.SimpleGraph.card_neighborFinset_eq_degree, hdeg]
  have hScard : S.card = 2 := by
    dsimp only [S]
    rw [_root_.SimpleGraph.card_neighborFinset_eq_degree]
    exact e.2.2
  have hdiff : (T \ S).card = 1 := by
    rw [Finset.card_sdiff_of_subset hsub, hTcard, hScard]
  obtain ⟨z, hz⟩ := Finset.card_eq_one.mp hdiff
  have hzmem : z ∈ T \ S := by
    rw [hz]
    simp
  rcases Finset.mem_sdiff.mp hzmem with ⟨hzT, hzS⟩
  cases z with
  | inl x =>
      have hxFull : F.levi.Adj (Sum.inr e.1) (Sum.inl x) := by
        exact (F.levi.mem_neighborFinset _ _).mp hzT
      have hxNot : ¬(expansionCore F).Adj (Sum.inl x) (Sum.inr e.1) := by
        intro hx
        apply hzS
        exact ((expansionCore F).mem_neighborFinset _ _).mpr hx.symm
      refine ⟨x, ⟨F.levi_adj_edge_point.mp hxFull, hxNot⟩, ?_⟩
      intro y hy
      have hyT : (Sum.inl y : V ⊕ E) ∈ T := by
        exact (F.levi.mem_neighborFinset _ _).mpr
          (F.levi_adj_point_edge.mpr hy.1).symm
      have hyS : (Sum.inl y : V ⊕ E) ∉ S := by
        intro hymem
        apply hy.2
        exact (((expansionCore F).mem_neighborFinset _ _).mp hymem).symm
      have hymem : (Sum.inl y : V ⊕ E) ∈ T \ S :=
        Finset.mem_sdiff.mpr ⟨hyT, hyS⟩
      rw [hz] at hymem
      simpa using! hymem
  | inr f =>
      have hef : F.levi.Adj (Sum.inr e.1) (Sum.inr f) :=
        (F.levi.mem_neighborFinset _ _).mp hzT
      exact (F.not_levi_adj_edge_edge hef).elim

/-- The unique point on `e` whose incidence is deleted with the Levi bridges. -/
noncomputable def privatePoint {C : Component F}
    (e : ContractibleEdge F C) : V :=
  Exists.choose (contractibleEdge_existsUnique_privatePoint F e)

theorem privatePoint_spec {C : Component F}
    (e : ContractibleEdge F C) :
    F.Inc (privatePoint F e) e.1 ∧
      ¬(expansionCore F).Adj
        (Sum.inl (privatePoint F e)) (Sum.inr e.1) :=
  (Exists.choose_spec (contractibleEdge_existsUnique_privatePoint F e)).1

/-- The deleted private incidence is an actual Levi bridge. -/
theorem privatePoint_isBridge {C : Component F}
    (e : ContractibleEdge F C) :
    F.levi.IsBridge
      s(Sum.inl (privatePoint F e), Sum.inr e.1) := by
  have hspec := privatePoint_spec F e
  have hadj : F.levi.Adj
      (Sum.inl (privatePoint F e)) (Sum.inr e.1) :=
    F.levi_adj_point_edge.mpr hspec.1
  have hmem :
      s(Sum.inl (privatePoint F e), Sum.inr e.1) ∈
        Erdos593.SimpleGraph.bridgeFinset F.levi := by
    by_contra hnot
    apply hspec.2
    change (Erdos593.SimpleGraph.bridgeFree F.levi).Adj
      (Sum.inl (privatePoint F e)) (Sum.inr e.1)
    dsimp only [Erdos593.SimpleGraph.bridgeFree]
    rw [_root_.SimpleGraph.deleteEdges_adj]
    exact ⟨hadj, hnot⟩
  exact (Erdos593.SimpleGraph.mem_bridgeFinset.mp hmem).2

/-- A private point lies outside the bridge-free component containing its
hyperedge-node. -/
theorem privatePoint_not_mem_component {C : Component F}
    (e : ContractibleEdge F C) :
    Sum.inl (privatePoint F e) ∉ C.supp := by
  intro hpC
  have hreach : (expansionCore F).Reachable
      (Sum.inl (privatePoint F e)) (Sum.inr e.1) :=
    C.reachable_of_mem_supp hpC e.2.1
  have hadj : F.levi.Adj
      (Sum.inl (privatePoint F e)) (Sum.inr e.1) :=
    F.levi_adj_point_edge.mpr (privatePoint_spec F e).1
  have hbridge := privatePoint_isBridge F e
  have hmono : (expansionCore F).Adj ≤
      (F.levi.deleteEdges
        {s(Sum.inl (privatePoint F e), Sum.inr e.1)}).Adj := by
    intro a b hab
    change (Erdos593.SimpleGraph.bridgeFree F.levi).Adj a b at hab
    dsimp only [Erdos593.SimpleGraph.bridgeFree] at hab
    rw [_root_.SimpleGraph.deleteEdges_adj] at hab
    rw [_root_.SimpleGraph.deleteEdges_adj]
    refine ⟨hab.1, ?_⟩
    intro heq
    apply hab.2
    have heq' : s(a, b) =
        s(Sum.inl (privatePoint F e), Sum.inr e.1) := by
      simpa using! heq
    rw [heq']
    exact Erdos593.SimpleGraph.mem_bridgeFinset.mpr ⟨hadj, hbridge⟩
  rw [_root_.SimpleGraph.isBridge_iff] at hbridge
  exact hbridge (hreach.mono hmono)

/-- Different hyperedges in one bridge-free component have different private
points. -/
theorem privatePoint_injective (C : Component F) :
    Function.Injective (fun e : ContractibleEdge F C => privatePoint F e) := by
  intro e f hef
  change privatePoint F e = privatePoint F f at hef
  have heAdj : F.levi.Adj
      (Sum.inl (privatePoint F e)) (Sum.inr e.1) :=
    F.levi_adj_point_edge.mpr (privatePoint_spec F e).1
  have hfAdj : F.levi.Adj
      (Sum.inl (privatePoint F e)) (Sum.inr f.1) := by
    rw [hef]
    exact F.levi_adj_point_edge.mpr (privatePoint_spec F f).1
  have hreach : (expansionCore F).Reachable
      (Sum.inr e.1) (Sum.inr f.1) :=
    C.reachable_of_mem_supp e.2.1 f.2.1
  have hedge :=
    Erdos593.SimpleGraph.edge_eq_of_bridgeFree_reachable_endpoints_of_isBridge
      F.levi heAdj (privatePoint_isBridge F e) hfAdj
        (_root_.SimpleGraph.Reachable.refl _) hreach
  have hmem : (Sum.inr e.1 : V ⊕ E) ∈
      s(Sum.inl (privatePoint F e), Sum.inr f.1) := by
    rw [hedge]
    simp
  apply Subtype.ext
  simpa using! hmem

/-- Incidence on a contractible edge is exactly a surviving core incidence or
the edge's private point. -/
theorem inc_iff_bridgeFree_or_privatePoint {C : Component F}
    (e : ContractibleEdge F C) (z : V) :
    F.Inc z e.1 ↔
      (expansionCore F).Adj (Sum.inl z) (Sum.inr e.1) ∨
        z = privatePoint F e := by
  constructor
  · intro hinc
    by_cases hsurvives :
        (expansionCore F).Adj (Sum.inl z) (Sum.inr e.1)
    · exact Or.inl hsurvives
    · exact Or.inr
        ((Exists.choose_spec
          (contractibleEdge_existsUnique_privatePoint F e)).2 z
            ⟨hinc, hsurvives⟩)
  · rintro (hsurvives | rfl)
    · have hle : expansionCore F ≤ F.levi := by
        dsimp only [expansionCore, Erdos593.SimpleGraph.bridgeFree]
        exact F.levi.deleteEdges_le _
      exact F.levi_adj_point_edge.mp (hle hsurvives)
    · exact (privatePoint_spec F e).1

/-- In an active component, every hyperedge-node is contractible. -/
def contractibleEdgeOfHyperedge
    (hbridge : F.BridgeAtEveryEdge) {C : Component F}
    (hC : HasIncidence F C) (e : Hyperedge F C) : ContractibleEdge F C :=
  ⟨e.1, e.2, edge_degree_eq_two_of_hasIncidence F hbridge hC e.2⟩

/-- Exact expansion data determined by an active bridge-free component: the
private-point assignment is injective, its image is disjoint from the core
component, and every component hyperedge consists precisely of its two
surviving core incidences together with its private point. -/
theorem activeComponent_privateVertexExpansionData
    (hbridge : F.BridgeAtEveryEdge) {C : Component F}
    (hC : HasIncidence F C) :
    ∃ p : Hyperedge F C → V,
      Function.Injective p ∧
      (∀ e, Sum.inl (p e) ∉ C.supp) ∧
      ∀ (e : Hyperedge F C) (z : V),
        F.Inc z e.1 ↔
          (expansionCore F).Adj (Sum.inl z) (Sum.inr e.1) ∨ z = p e := by
  let q : Hyperedge F C → ContractibleEdge F C :=
    fun e => contractibleEdgeOfHyperedge F hbridge hC e
  let p : Hyperedge F C → V := fun e => privatePoint F (q e)
  refine ⟨p, ?_, ?_, ?_⟩
  · intro e f hef
    change privatePoint F (q e) = privatePoint F (q f) at hef
    have hq : q e = q f := privatePoint_injective F C hef
    apply Subtype.ext
    change e.1 = f.1
    simpa [q, contractibleEdgeOfHyperedge] using! congrArg Subtype.val hq
  · intro e
    exact privatePoint_not_mem_component F (q e)
  · intro e z
    exact inc_iff_bridgeFree_or_privatePoint F (q e) z

end
end BridgeBlock
end TripleSystem
end Erdos593
