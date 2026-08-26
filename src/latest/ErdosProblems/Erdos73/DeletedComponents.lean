import ErdosProblems.Erdos73.MatchingComponents
import ErdosProblems.Erdos556.UniversalExtension

/-! Components after vertex deletion, with their supports in the original vertex type. -/

namespace Erdos73

open SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

abbrev vertexDeletedGraph (G : SimpleGraph V) (W : Finset V) :=
  G.induce {v : V | v ∉ W}

def topDeleteVertsIso (G : SimpleGraph V) (W : Finset V) :
    ((⊤ : G.Subgraph).deleteVerts (W : Set V)).coe ≃g vertexDeletedGraph G W where
  toFun v := ⟨v.val, v.property.2⟩
  invFun v := ⟨v.val, ⟨trivial, v.property⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := by
    intro u v
    change G.Adj u.val v.val ↔ (_ ∧ _ ∧ G.Adj u.val v.val)
    exact ⟨fun h => ⟨u.property, v.property, h⟩, fun h => h.2.2⟩

omit [Fintype V] [DecidableEq V] in
theorem topDeleteVerts_oddComponents_card (G : SimpleGraph V) (W : Finset V) :
    ((⊤ : G.Subgraph).deleteVerts (W : Set V)).coe.oddComponents.ncard =
      (vertexDeletedGraph G W).oddComponents.ncard :=
  Erdos556.isomorphic_oddComponents_ncard (topDeleteVertsIso G W)

open scoped Classical in
noncomputable def deletedComponentVertices {G : SimpleGraph V} {W : Finset V}
    (C : (vertexDeletedGraph G W).ConnectedComponent) : Finset V :=
  C.supp.toFinset.image Subtype.val

open scoped Classical in
theorem mem_deletedComponentVertices {G : SimpleGraph V} {W : Finset V}
    (C : (vertexDeletedGraph G W).ConnectedComponent) (x : V) :
    x ∈ deletedComponentVertices C ↔ ∃ hx : x ∉ W, ⟨x, hx⟩ ∈ C.supp := by
  constructor
  · intro hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    exact ⟨y.property, Set.mem_toFinset.mp hy⟩
  · rintro ⟨hx, hC⟩
    exact Finset.mem_image.mpr ⟨⟨x, hx⟩, Set.mem_toFinset.mpr hC, rfl⟩

open scoped Classical in
theorem deletedComponentVertices_card {G : SimpleGraph V} {W : Finset V}
    (C : (vertexDeletedGraph G W).ConnectedComponent) :
    (deletedComponentVertices C).card = C.supp.ncard := by
  rw [deletedComponentVertices, Finset.card_image_of_injective _ Subtype.val_injective]
  simp only [Set.toFinset_card, Fintype.card_eq_nat_card, Nat.card_coe_set_eq]

open scoped Classical in
theorem deletedComponentVertices_not_mem {G : SimpleGraph V} {W : Finset V}
    (C : (vertexDeletedGraph G W).ConnectedComponent) {x : V}
    (hx : x ∈ deletedComponentVertices C) : x ∉ W :=
  (mem_deletedComponentVertices C x).mp hx |>.choose

open scoped Classical in
theorem deletedComponentVertices_closed {G : SimpleGraph V} {W : Finset V}
    (C : (vertexDeletedGraph G W).ConnectedComponent) {x y : V}
    (hx : x ∈ deletedComponentVertices C) (hy : y ∉ W) (hxy : G.Adj x y) :
    y ∈ deletedComponentVertices C := by
  obtain ⟨hxW, hxC⟩ := (mem_deletedComponentVertices C x).mp hx
  apply (mem_deletedComponentVertices C y).mpr
  exact ⟨hy, (C.mem_supp_congr_adj (show (vertexDeletedGraph G W).Adj
    ⟨x, hxW⟩ ⟨y, hy⟩ from hxy)).mp hxC⟩

open scoped Classical in
theorem deletedComponentVertices_disjoint {G : SimpleGraph V} {W : Finset V} :
    Pairwise (fun C D : (vertexDeletedGraph G W).ConnectedComponent =>
      Disjoint (deletedComponentVertices C) (deletedComponentVertices D)) := by
  intro C D hne
  apply Finset.disjoint_left.mpr
  intro x hxC hxD
  obtain ⟨hx, hc⟩ := (mem_deletedComponentVertices C x).mp hxC
  obtain ⟨_, hd⟩ := (mem_deletedComponentVertices D x).mp hxD
  exact hne (ConnectedComponent.eq_of_common_vertex hc hd)

open scoped Classical in
theorem exists_deletedComponent_containing {G : SimpleGraph V} {W : Finset V}
    (x : V) (hx : x ∉ W) :
    ∃ C : (vertexDeletedGraph G W).ConnectedComponent, x ∈ deletedComponentVertices C := by
  exact ⟨(vertexDeletedGraph G W).connectedComponentMk ⟨x, hx⟩,
    (mem_deletedComponentVertices _ x).mpr ⟨hx, rfl⟩⟩

end Erdos73
