/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos570.Support
import ErdosProblems.Erdos570.RamseyRegion
import Mathlib.Combinatorics.SimpleGraph.Sum

/-!
# Disjoint-union infrastructure for Erdős Problem 570

This file packages the disjoint union of two coded finite graphs and proves
the elementary Ramsey composition lemma used when a target graph is split
into two unions of components.
-/

open scoped SimpleGraph

noncomputable section

namespace Erdos570

open Erdos79

/-- The canonical code for the disjoint union of two coded graphs. -/
def disjointUnionCode (G H : GraphCode) : GraphCode :=
  ⟨G.vertexCount + H.vertexCount,
    (G.graph ⊕g H.graph).map
      (finSumFinEquiv : Fin G.vertexCount ⊕ Fin H.vertexCount ≃
        Fin (G.vertexCount + H.vertexCount)).toEmbedding⟩

@[simp] theorem disjointUnionCode_vertexCount (G H : GraphCode) :
    (disjointUnionCode G H).vertexCount = G.vertexCount + H.vertexCount := rfl

@[simp] theorem disjointUnionCode_graph (G H : GraphCode) :
    (disjointUnionCode G H).graph =
      (G.graph ⊕g H.graph).map
        (finSumFinEquiv : Fin G.vertexCount ⊕ Fin H.vertexCount ≃
          Fin (G.vertexCount + H.vertexCount)).toEmbedding := rfl

@[simp] theorem disjointUnionCode_edgeCount (G H : GraphCode) :
    (disjointUnionCode G H).edgeCount = G.edgeCount + H.edgeCount := by
  let e := SimpleGraph.Iso.map
    (finSumFinEquiv : Fin G.vertexCount ⊕ Fin H.vertexCount ≃
      Fin (G.vertexCount + H.vertexCount)) (G.graph ⊕g H.graph)
  calc
    (disjointUnionCode G H).edgeCount =
        Nat.card ((disjointUnionCode G H).graph.edgeSet) := rfl
    _ = Nat.card (G.graph ⊕g H.graph).edgeSet := by
      exact (Nat.card_congr e.mapEdgeSet).symm
    _ = Nat.card (G.graph.edgeSet ⊕ H.graph.edgeSet) := by
      exact Nat.card_congr SimpleGraph.edgeSetSumEquiv
    _ = Nat.card G.graph.edgeSet + Nat.card H.graph.edgeSet := Nat.card_sum
    _ = G.edgeCount + H.edgeCount := rfl

/-- Disjoint union preserves absence of isolated vertices. -/
theorem noIsolated_disjointUnionCode {G H : GraphCode}
    (hG : NoIsolated G) (hH : NoIsolated H) :
    NoIsolated (disjointUnionCode G H) := by
  intro v
  apply (disjointUnionCode G H).graph.exists_adj_iff_not_isIsolated.mp
  let e := (finSumFinEquiv : Fin G.vertexCount ⊕ Fin H.vertexCount ≃
    Fin (G.vertexCount + H.vertexCount))
  have hv : e (e.symm v) = v := e.apply_symm_apply v
  rcases h : e.symm v with u | u
  · obtain ⟨w, huw⟩ := G.graph.exists_adj_iff_not_isIsolated.mpr (hG u)
    refine ⟨e (Sum.inl w), ?_⟩
    rw [← hv]
    rw [h]
    change ((G.graph ⊕g H.graph).map e.toEmbedding).Adj
      (e (Sum.inl u)) (e (Sum.inl w))
    exact (SimpleGraph.Iso.map e (G.graph ⊕g H.graph)).toHom.map_adj
      (by simpa using huw)
  · obtain ⟨w, huw⟩ := H.graph.exists_adj_iff_not_isIsolated.mpr (hH u)
    refine ⟨e (Sum.inr w), ?_⟩
    rw [← hv]
    rw [h]
    change ((G.graph ⊕g H.graph).map e.toEmbedding).Adj
      (e (Sum.inr u)) (e (Sum.inr w))
    exact (SimpleGraph.Iso.map e (G.graph ⊕g H.graph)).toHom.map_adj
      (by simpa using huw)

/-- The left summand is an ordinary subgraph of the coded disjoint union. -/
theorem left_isContained_disjointUnionCode (G H : GraphCode) :
    IsContained G (disjointUnionCode G H) := by
  let e := (SimpleGraph.Embedding.sumInl : G.graph ↪g G.graph ⊕g H.graph)
  let i := SimpleGraph.Iso.map
    (finSumFinEquiv : Fin G.vertexCount ⊕ Fin H.vertexCount ≃
      Fin (G.vertexCount + H.vertexCount)) (G.graph ⊕g H.graph)
  exact ⟨i.toCopy.comp e.toCopy⟩

/-- The right summand is an ordinary subgraph of the coded disjoint union. -/
theorem right_isContained_disjointUnionCode (G H : GraphCode) :
    IsContained H (disjointUnionCode G H) := by
  let e := (SimpleGraph.Embedding.sumInr : H.graph ↪g G.graph ⊕g H.graph)
  let i := SimpleGraph.Iso.map
    (finSumFinEquiv : Fin G.vertexCount ⊕ Fin H.vertexCount ≃
      Fin (G.vertexCount + H.vertexCount)) (G.graph ⊕g H.graph)
  exact ⟨i.toCopy.comp e.toCopy⟩

/-- Copies of two graphs in disjoint induced regions combine into a copy of
their disjoint union.  No condition on host cross-edges is needed. -/
theorem disjointUnionCode_isContained_of_induced_copies
    {G H : GraphCode} {V : Type*} {C : SimpleGraph V} {S T : Set V}
    (hST : Disjoint S T) (hG : G.graph ⊑ C.induce S)
    (hH : H.graph ⊑ C.induce T) :
    (disjointUnionCode G H).graph ⊑ C := by
  obtain ⟨copyG⟩ := hG
  obtain ⟨copyH⟩ := hH
  let hom : G.graph ⊕g H.graph →g C :=
    { toFun := Sum.elim (fun x ↦ (copyG x).1) (fun y ↦ (copyH y).1)
      map_rel' := by
        rintro (x | x) (y | y) hxy
        · exact copyG.toHom.map_adj (by simpa using hxy)
        · simp at hxy
        · simp at hxy
        · exact copyH.toHom.map_adj (by simpa using hxy) }
  have hinj : Function.Injective hom := by
    rintro (x | x) (y | y) hxy
    · exact congrArg Sum.inl (copyG.injective (Subtype.ext hxy))
    · exfalso
      change (copyG x).1 = (copyH y).1 at hxy
      have hxT : (copyG x).1 ∈ T := by
        rw [hxy]
        exact (copyH y).2
      exact Set.disjoint_left.mp hST (copyG x).2 hxT
    · exfalso
      change (copyH x).1 = (copyG y).1 at hxy
      have hyT : (copyG y).1 ∈ T := by
        rw [← hxy]
        exact (copyH x).2
      exact Set.disjoint_left.mp hST (copyG y).2 hyT
    · exact congrArg Sum.inr (copyH.injective (Subtype.ext hxy))
  have hsum : G.graph ⊕g H.graph ⊑ C := ⟨hom.toCopy hinj⟩
  let e := SimpleGraph.Iso.map
    (finSumFinEquiv : Fin G.vertexCount ⊕ Fin H.vertexCount ≃
      Fin (G.vertexCount + H.vertexCount)) (G.graph ⊕g H.graph)
  exact ⟨hsum.some.comp e.symm.toCopy⟩

/-- A vertex partition with no target cross-edge identifies the target as a
subgraph of the disjoint union of its two induced pieces. -/
theorem isContained_disjointUnionCode_induced_partition
    (H : GraphCode) (S : Finset (Fin H.vertexCount))
    (hcross : ∀ x ∈ S, ∀ y ∉ S, ¬ H.graph.Adj x y) :
    IsContained H
      (disjointUnionCode (inducedCode H S) (inducedCode H Sᶜ)) := by
  classical
  let eS := inducedCodeIso H S
  let eT := inducedCodeIso H Sᶜ
  let f : Fin H.vertexCount →
      Fin (inducedCode H S).vertexCount ⊕
        Fin (inducedCode H Sᶜ).vertexCount := fun v ↦
    if hv : v ∈ S then Sum.inl (eS ⟨v, hv⟩)
    else Sum.inr (eT ⟨v, by simpa using hv⟩)
  let hom : H.graph →g
      (inducedCode H S).graph ⊕g (inducedCode H Sᶜ).graph :=
    { toFun := f
      map_rel' := by
        intro x y hxy
        by_cases hx : x ∈ S <;> by_cases hy : y ∈ S
        · dsimp only [f]
          rw [dif_pos hx, dif_pos hy]
          exact eS.toHom.map_adj hxy
        · exact (hcross x hx y hy hxy).elim
        · exact (hcross y hy x hx hxy.symm).elim
        · dsimp only [f]
          rw [dif_neg hx, dif_neg hy]
          exact eT.toHom.map_adj hxy }
  have hinj : Function.Injective hom := by
    intro x y hxy
    by_cases hx : x ∈ S <;> by_cases hy : y ∈ S
    · change f x = f y at hxy
      dsimp only [f] at hxy
      rw [dif_pos hx, dif_pos hy] at hxy
      exact congrArg Subtype.val (eS.injective (Sum.inl.inj hxy))
    · change f x = f y at hxy
      dsimp only [f] at hxy
      rw [dif_pos hx, dif_neg hy] at hxy
      contradiction
    · change f x = f y at hxy
      dsimp only [f] at hxy
      rw [dif_neg hx, dif_pos hy] at hxy
      contradiction
    · change f x = f y at hxy
      dsimp only [f] at hxy
      rw [dif_neg hx, dif_neg hy] at hxy
      exact congrArg Subtype.val (eT.injective (Sum.inr.inj hxy))
  have hsum : H.graph ⊑
      (inducedCode H S).graph ⊕g (inducedCode H Sᶜ).graph :=
    ⟨hom.toCopy hinj⟩
  let e := SimpleGraph.Iso.map
    (finSumFinEquiv :
      Fin (inducedCode H S).vertexCount ⊕
        Fin (inducedCode H Sᶜ).vertexCount ≃
      Fin ((inducedCode H S).vertexCount +
        (inducedCode H Sᶜ).vertexCount))
    ((inducedCode H S).graph ⊕g (inducedCode H Sᶜ).graph)
  exact hsum.trans ⟨e.toCopy⟩

private theorem castAdd_ne_natAdd {n m : ℕ} (u : Fin n) (v : Fin m) :
    Fin.castAdd m u ≠ Fin.natAdd n v := by
  intro h
  have hval := congrArg Fin.val h
  simp only [Fin.val_castAdd, Fin.val_natAdd] at hval
  omega

/-- If two target graphs can be forced in disjoint vertex blocks (unless the
same red graph appears), their disjoint union can be forced in the sum of the
two ambient orders. -/
theorem ramseyAt_disjointUnion {F G H : GraphCode} {N₁ N₂ : ℕ}
    (hG : RamseyAt F G N₁) (hH : RamseyAt F H N₂) :
    RamseyAt F (disjointUnionCode G H) (N₁ + N₂) := by
  intro C
  let left : Fin N₁ ↪ Fin (N₁ + N₂) := Fin.castAddEmb N₂
  let right : Fin N₂ ↪ Fin (N₁ + N₂) := Fin.natAddEmb N₁
  rcases hG (C.comap left) with hred | hblueG
  · left
    exact hred.trans (SimpleGraph.Embedding.comap left C).isContained
  rcases hH (C.comap right) with hred | hblueH
  · left
    exact hred.trans (SimpleGraph.Embedding.comap right C).isContained
  · right
    have hcompLeft : (C.comap left)ᶜ = Cᶜ.comap left := by
      ext u v
      simp only [SimpleGraph.compl_adj, SimpleGraph.comap_adj]
      rw [left.injective.ne_iff]
    have hcompRight : (C.comap right)ᶜ = Cᶜ.comap right := by
      ext u v
      simp only [SimpleGraph.compl_adj, SimpleGraph.comap_adj]
      rw [right.injective.ne_iff]
    rw [hcompLeft] at hblueG
    rw [hcompRight] at hblueH
    obtain ⟨copyG⟩ := hblueG
    obtain ⟨copyH⟩ := hblueH
    let sumCopy : SimpleGraph.Copy (G.graph ⊕g H.graph) Cᶜ :=
      { toHom :=
          { toFun := Sum.elim (left ∘ copyG) (right ∘ copyH)
            map_rel' := by
              rintro (u | u) (v | v) huv
              · exact copyG.toHom.map_adj (by simpa using huv)
              · simp at huv
              · simp at huv
              · exact copyH.toHom.map_adj (by simpa using huv) }
        injective' := by
          rintro (u | u) (v | v) huv
          · exact congrArg Sum.inl (copyG.injective (left.injective huv))
          · exact (castAdd_ne_natAdd (copyG u) (copyH v) huv).elim
          · exact (castAdd_ne_natAdd (copyG v) (copyH u) huv.symm).elim
          · exact congrArg Sum.inr (copyH.injective (right.injective huv)) }
    let i := SimpleGraph.Iso.map
      (finSumFinEquiv : Fin G.vertexCount ⊕ Fin H.vertexCount ≃
        Fin (G.vertexCount + H.vertexCount)) (G.graph ⊕g H.graph)
    exact ⟨sumCopy.comp i.symm.toCopy⟩

/-- Least Ramsey numbers are subadditive under disjoint union in the target. -/
theorem graphRamseyNumber_disjointUnion_le (F G H : GraphCode) :
    graphRamseyNumber F (disjointUnionCode G H) ≤
      graphRamseyNumber F G + graphRamseyNumber F H := by
  apply graphRamseyNumber_le_of_ramseyAt
  exact ramseyAt_disjointUnion (graphRamseyNumber_spec F G)
    (graphRamseyNumber_spec F H)

/-- Adaptive disjoint-union composition.  First find a blue copy of `G`
anywhere in the host, remove precisely its image, and force `H` on the unused
vertices.  This is sharper than splitting the host into two predetermined
blocks. -/
theorem ramseyAt_disjointUnion_remove_first {F G H : GraphCode} {N : ℕ}
    (hG : RamseyAt F G N)
    (hH : RamseyAt F H (N - G.vertexCount)) :
    RamseyAt F (disjointUnionCode G H) N := by
  classical
  intro C
  rcases hG C with hred | hblueG
  · exact Or.inl hred
  · obtain ⟨copyG⟩ := hblueG
    let T : Finset (Fin N) := Finset.univ.image copyG.toHom
    let S : Finset (Fin N) := Finset.univ \ T
    have hTcard : T.card = G.vertexCount := by
      dsimp only [T]
      rw [Finset.card_image_of_injective _ copyG.injective]
      simp
    have hScard : S.card = N - G.vertexCount := by
      dsimp only [S]
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ T), Finset.card_univ,
        hTcard]
      simp
    rcases Erdos570.RamseyAt.on_finset hH C S (by rw [hScard]) with
      hredS | hblueH
    · left
      exact hredS.trans (SimpleGraph.Embedding.induce (S : Set (Fin N))).isContained
    · right
      have hGinduce : G.graph ⊑ Cᶜ.induce (T : Set (Fin N)) := by
        let hom : G.graph →g Cᶜ.induce (T : Set (Fin N)) :=
          { toFun := fun x ↦ ⟨copyG x, by
              simp only [T, Finset.coe_image, Finset.coe_univ, Set.image_univ,
                Set.mem_range]
              exact ⟨x, rfl⟩⟩
            map_rel' := by
              intro x y hxy
              exact copyG.toHom.map_adj hxy }
        refine ⟨hom.toCopy ?_⟩
        intro x y hxy
        apply copyG.injective
        exact congrArg Subtype.val hxy
      have hTS : Disjoint (T : Set (Fin N)) (S : Set (Fin N)) := by
        rw [Set.disjoint_left]
        intro x hxT hxS
        have hxS' : x ∈ S := hxS
        exact (Finset.mem_sdiff.mp hxS').2 hxT
      exact disjointUnionCode_isContained_of_induced_copies hTS hGinduce hblueH

end Erdos570
