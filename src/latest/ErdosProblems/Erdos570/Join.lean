/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos570.Support
import Mathlib.Combinatorics.SimpleGraph.Sum

/-! Complete joins and combining copies in two vertex regions. -/

open scoped SimpleGraph

noncomputable section

namespace Erdos570

open Erdos79

/-- The complete join of two graphs on a sum type. -/
def graphJoin {V W : Type*} (G : SimpleGraph V) (H : SimpleGraph W) :
    SimpleGraph (V ⊕ W) :=
  (Gᶜ ⊕g Hᶜ)ᶜ

@[simp] theorem graphJoin_adj_inl {V W : Type*} {G : SimpleGraph V}
    {H : SimpleGraph W} {u v : V} :
    (graphJoin G H).Adj (Sum.inl u) (Sum.inl v) ↔ G.Adj u v := by
  simp only [graphJoin, SimpleGraph.compl_adj, SimpleGraph.sum_adj_inl]
  constructor
  · intro h
    by_contra hn
    exact h.2 ⟨fun huv ↦ h.1 (congrArg Sum.inl huv), hn⟩
  · intro h
    exact ⟨fun huv ↦ h.ne (Sum.inl.inj huv), fun hc ↦ hc.2 h⟩

@[simp] theorem graphJoin_adj_inr {V W : Type*} {G : SimpleGraph V}
    {H : SimpleGraph W} {u v : W} :
    (graphJoin G H).Adj (Sum.inr u) (Sum.inr v) ↔ H.Adj u v := by
  simp only [graphJoin, SimpleGraph.compl_adj, SimpleGraph.sum_adj_inr]
  constructor
  · intro h
    by_contra hn
    exact h.2 ⟨fun huv ↦ h.1 (congrArg Sum.inr huv), hn⟩
  · intro h
    exact ⟨fun huv ↦ h.ne (Sum.inr.inj huv), fun hc ↦ hc.2 h⟩

@[simp] theorem graphJoin_adj_inl_inr {V W : Type*} {G : SimpleGraph V}
    {H : SimpleGraph W} (u : V) (v : W) :
    (graphJoin G H).Adj (Sum.inl u) (Sum.inr v) := by
  simp [graphJoin]

@[simp] theorem graphJoin_adj_inr_inl {V W : Type*} {G : SimpleGraph V}
    {H : SimpleGraph W} (u : W) (v : V) :
    (graphJoin G H).Adj (Sum.inr u) (Sum.inl v) := by
  simp [graphJoin]

/-- Canonical finite-ordinal code for a complete join. -/
def joinCode (G H : GraphCode) : GraphCode :=
  ⟨G.vertexCount + H.vertexCount,
    (graphJoin G.graph H.graph).map
      (finSumFinEquiv : Fin G.vertexCount ⊕ Fin H.vertexCount ≃
        Fin (G.vertexCount + H.vertexCount)).toEmbedding⟩

@[simp] theorem joinCode_vertexCount (G H : GraphCode) :
    (joinCode G H).vertexCount = G.vertexCount + H.vertexCount := rfl

@[simp] theorem joinCode_graph (G H : GraphCode) :
    (joinCode G H).graph =
      (graphJoin G.graph H.graph).map
        (finSumFinEquiv : Fin G.vertexCount ⊕ Fin H.vertexCount ≃
          Fin (G.vertexCount + H.vertexCount)).toEmbedding := rfl

/-- Copies in two disjoint induced regions combine into a copy of the complete
join whenever every cross edge is present. -/
theorem graphJoin_isContained_of_induced_copies
    {V W X : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    {C : SimpleGraph X} {S T : Set X} (hST : Disjoint S T)
    (hG : G ⊑ C.induce S) (hH : H ⊑ C.induce T)
    (hcross : ∀ s : S, ∀ t : T, C.Adj s.1 t.1) :
    graphJoin G H ⊑ C := by
  obtain ⟨copyG⟩ := hG
  obtain ⟨copyH⟩ := hH
  let fG : V → X := fun v ↦ (copyG v).1
  let fH : W → X := fun w ↦ (copyH w).1
  let hom : graphJoin G H →g C :=
    { toFun := Sum.elim fG fH
      map_rel' := by
        rintro (u | u) (v | v) huv
        · exact copyG.toHom.map_adj (graphJoin_adj_inl.mp huv)
        · exact hcross (copyG u) (copyH v)
        · exact (hcross (copyG v) (copyH u)).symm
        · exact copyH.toHom.map_adj (graphJoin_adj_inr.mp huv) }
  have hhom : Function.Injective hom := by
    rintro (u | u) (v | v) huv
    · exact congrArg Sum.inl (copyG.injective (Subtype.ext huv))
    · exfalso
      change (copyG u).1 = (copyH v).1 at huv
      exact Set.disjoint_left.mp hST (copyG u).2
        (huv ▸ (copyH v).2)
    · exfalso
      change (copyH u).1 = (copyG v).1 at huv
      exact Set.disjoint_left.mp hST (copyG v).2
        (huv.symm ▸ (copyH u).2)
    · exact congrArg Sum.inr (copyH.injective (Subtype.ext huv))
  exact ⟨hom.toCopy hhom⟩

/-- Coded form of `graphJoin_isContained_of_induced_copies`. -/
theorem joinCode_isContained_of_induced_copies
    {G H : GraphCode} {X : Type*} {C : SimpleGraph X} {S T : Set X}
    (hST : Disjoint S T) (hG : G.graph ⊑ C.induce S)
    (hH : H.graph ⊑ C.induce T)
    (hcross : ∀ s : S, ∀ t : T, C.Adj s.1 t.1) :
    (joinCode G H).graph ⊑ C := by
  have hjoin : graphJoin G.graph H.graph ⊑ C :=
    graphJoin_isContained_of_induced_copies hST hG hH hcross
  let e := SimpleGraph.Iso.map
    (finSumFinEquiv : Fin G.vertexCount ⊕ Fin H.vertexCount ≃
      Fin (G.vertexCount + H.vertexCount)) (graphJoin G.graph H.graph)
  exact ⟨hjoin.some.comp e.symm.toCopy⟩

/-- A graph is contained in the complete join of the graphs induced by a
finite vertex set and its complement.  Internal edges are preserved by the
two induced graphs, while every possible cross edge exists in the join. -/
theorem isContained_joinCode_induced_partition (H : GraphCode)
    (S : Finset (Fin H.vertexCount)) :
    IsContained H (joinCode (inducedCode H S) (inducedCode H Sᶜ)) := by
  classical
  let eS := inducedCodeIso H S
  let eT := inducedCodeIso H Sᶜ
  let f : Fin H.vertexCount →
      Fin (inducedCode H S).vertexCount ⊕
        Fin (inducedCode H Sᶜ).vertexCount := fun v ↦
    if hv : v ∈ S then Sum.inl (eS ⟨v, hv⟩)
    else Sum.inr (eT ⟨v, by simpa using hv⟩)
  let hom : H.graph →g
      graphJoin (inducedCode H S).graph (inducedCode H Sᶜ).graph :=
    { toFun := f
      map_rel' := by
        intro u v huv
        by_cases hu : u ∈ S <;> by_cases hv : v ∈ S
        · dsimp only [f]
          rw [dif_pos hu, dif_pos hv, graphJoin_adj_inl]
          exact eS.toHom.map_adj huv
        · dsimp only [f]
          rw [dif_pos hu, dif_neg hv]
          exact graphJoin_adj_inl_inr _ _
        · dsimp only [f]
          rw [dif_neg hu, dif_pos hv]
          exact graphJoin_adj_inr_inl _ _
        · dsimp only [f]
          rw [dif_neg hu, dif_neg hv, graphJoin_adj_inr]
          exact eT.toHom.map_adj huv }
  have hf : Function.Injective hom := by
    intro u v huv
    by_cases hu : u ∈ S <;> by_cases hv : v ∈ S
    · change f u = f v at huv
      dsimp only [f] at huv
      rw [dif_pos hu, dif_pos hv] at huv
      have he := Sum.inl.inj huv
      exact congrArg Subtype.val (eS.injective he)
    · change f u = f v at huv
      dsimp only [f] at huv
      rw [dif_pos hu, dif_neg hv] at huv
      contradiction
    · change f u = f v at huv
      dsimp only [f] at huv
      rw [dif_neg hu, dif_pos hv] at huv
      contradiction
    · change f u = f v at huv
      dsimp only [f] at huv
      rw [dif_neg hu, dif_neg hv] at huv
      have he := Sum.inr.inj huv
      exact congrArg Subtype.val (eT.injective he)
  have hbase : H.graph ⊑
      graphJoin (inducedCode H S).graph (inducedCode H Sᶜ).graph :=
    ⟨hom.toCopy hf⟩
  let e := SimpleGraph.Iso.map
    (finSumFinEquiv :
      Fin (inducedCode H S).vertexCount ⊕
        Fin (inducedCode H Sᶜ).vertexCount ≃
      Fin ((inducedCode H S).vertexCount +
        (inducedCode H Sᶜ).vertexCount))
    (graphJoin (inducedCode H S).graph (inducedCode H Sᶜ).graph)
  exact hbase.trans ⟨e.toCopy⟩

end Erdos570
