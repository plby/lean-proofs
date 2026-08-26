import ErdosProblems.Erdos556.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite

/-! Extending a hereditary density bound by isolated vertices. -/

namespace Erdos556

open SimpleGraph Finset

theorem edgeFinset_card_eq_natCard_edgeSet {V : Type*} (G : SimpleGraph V) [Fintype G.edgeSet] :
    G.edgeFinset.card = Nat.card G.edgeSet :=
  G.card_edgeSet.symm.trans Nat.card_eq_fintype_card.symm

theorem induced_map_edge_count {V W : Type*} [Fintype V] [Fintype W]
    [DecidableEq V] [DecidableEq W] (G : SimpleGraph V) [DecidableRel G.Adj]
    (f : V ↪ W) (A : Finset W) :
    ((G.map f).induce (A : Set W)).edgeFinset.card =
      (G.induce ((univ.filter (fun v => f v ∈ A) : Finset V) : Set V)).edgeFinset.card := by
  classical
  let B := univ.filter (fun v : V => f v ∈ A)
  let g : (B : Set V) ↪ (A : Set W) :=
    { toFun := fun v => ⟨f v.val, (mem_filter.mp v.property).2⟩
      inj' := fun u v h => Subtype.ext (f.injective (congrArg Subtype.val h)) }
  have e : (G.map f).induce (A : Set W) ≃g (G.induce (B : Set V)).map g :=
    { toEquiv := Equiv.refl _
      map_rel_iff' := by
        intro u v
        constructor
        · rintro ⟨hne, a, b, hab, ha, hb⟩
          change (G.map f).Adj u.val v.val
          refine ⟨fun h => hne (Subtype.ext h), a.val, b.val, hab, ?_, ?_⟩
          · exact congrArg Subtype.val ha
          · exact congrArg Subtype.val hb
        · intro huv
          change (G.map f).Adj u.val v.val at huv
          obtain ⟨hne, a, b, hab, ha, hb⟩ := huv
          have haB : a ∈ B := mem_filter.mpr ⟨mem_univ _, ha ▸ u.property⟩
          have hbB : b ∈ B := mem_filter.mpr ⟨mem_univ _, hb ▸ v.property⟩
          refine ⟨fun h => hne (congrArg Subtype.val h), ⟨a, haB⟩, ⟨b, hbB⟩, hab, ?_, ?_⟩
          · exact Subtype.ext ha
          · exact Subtype.ext hb }
  exact e.card_edgeFinset_eq.trans (card_edgeFinset_map g (G.induce (B : Set V)))

theorem preimage_finset_card_le {V W : Type*} [Fintype V] [Fintype W]
    [DecidableEq W] (f : V ↪ W) (A : Finset W) :
    (univ.filter (fun v => f v ∈ A)).card ≤ A.card := by
  classical
  let B := univ.filter (fun v : V => f v ∈ A)
  let g : (B : Set V) ↪ (A : Set W) :=
    { toFun := fun v => ⟨f v.val, (mem_filter.mp v.property).2⟩
      inj' := fun u v h => Subtype.ext (f.injective (congrArg Subtype.val h)) }
  have h := Fintype.card_le_of_injective g g.injective
  have hcardB : Fintype.card (B : Set V) = B.card := by
    calc
      Fintype.card (B : Set V) = (B : Set V).ncard := Nat.card_eq_fintype_card.symm
      _ = B.card := Set.ncard_coe_finset B
  have hcardA : Fintype.card (A : Set W) = A.card := by
    calc
      Fintype.card (A : Set W) = (A : Set W).ncard := Nat.card_eq_fintype_card.symm
      _ = A.card := Set.ncard_coe_finset A
  rw [hcardB, hcardA] at h
  exact h

theorem hereditary_density_map_embedding {V W : Type*} [Fintype V] [Fintype W]
    [DecidableEq V] [DecidableEq W] (G : SimpleGraph V) [DecidableRel G.Adj]
    (f : V ↪ W) (D : ℝ) (hD : 0 ≤ D)
    (h : ∀ S : Finset V, ((G.induce (S : Set V)).edgeFinset.card : ℝ) ≤ D * S.card) :
    ∀ A : Finset W, (((G.map f).induce (A : Set W)).edgeFinset.card : ℝ) ≤ D * A.card := by
  intro A
  rw [induced_map_edge_count G f A]
  apply (h _).trans
  apply mul_le_mul_of_nonneg_left _ hD
  exact_mod_cast preimage_finset_card_le f A

#print axioms hereditary_density_map_embedding

theorem mapped_edges_in_set {V W : Type*} [DecidableEq W]
    (G : SimpleGraph V) (f : V ↪ W) (S : Finset V)
    (h : ∀ a b, G.Adj a b → a ∈ S ∧ b ∈ S) :
    ∀ a b, (G.map f).Adj a b → a ∈ S.map f ∧ b ∈ S.map f := by
  rintro a b ⟨_, u, v, huv, rfl, rfl⟩
  exact ⟨mem_map.mpr ⟨u, (h u v huv).1, rfl⟩, mem_map.mpr ⟨v, (h u v huv).2, rfl⟩⟩

theorem mapped_edges_off_set {V W : Type*} [DecidableEq W]
    (G : SimpleGraph V) (f : V ↪ W) (S : Finset V)
    (h : ∀ a b, G.Adj a b → a ∉ S ∧ b ∉ S) :
    ∀ a b, (G.map f).Adj a b → a ∉ S.map f ∧ b ∉ S.map f := by
  rintro a b ⟨_, u, v, huv, rfl, rfl⟩
  have hoff (x : V) (hx : x ∉ S) : f x ∉ S.map f := by
    intro hxmem
    obtain ⟨y, hy, hyx⟩ := mem_map.mp hxmem
    exact hx ((f.injective hyx) ▸ hy)
  exact ⟨hoff u (h u v huv).1, hoff v (h u v huv).2⟩

end Erdos556
