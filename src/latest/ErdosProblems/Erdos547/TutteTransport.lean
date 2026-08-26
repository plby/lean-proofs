import ErdosProblems.Erdos547.SeparatingPartitions
import ErdosProblems.Erdos547.FactorCriticalFractional

/-!
# Transporting Tutte's theorem to finite vertex regions
-/

noncomputable section

namespace Erdos547.DPRS

open Finset SimpleGraph

variable {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}

theorem oddComponents_ncard_eq_of_iso (φ : G ≃g H) :
    G.oddComponents.ncard = H.oddComponents.ncard := by
  have hcard (C : G.ConnectedComponent) : C.supp.ncard = (φ.connectedComponentEquiv C).supp.ncard :=
    Nat.card_congr (C.isoEquivSupp φ)
  let e : G.oddComponents ≃ H.oddComponents :=
    φ.connectedComponentEquiv.subtypeEquiv (fun C ↦ by
      change Odd C.supp.ncard ↔ Odd (φ.connectedComponentEquiv C).supp.ncard
      rw [hcard])
  exact Nat.card_congr e

def deleteInduceIso (G : SimpleGraph V) (A : Set V) (S : Set A) :
    ((⊤ : (G.induce A).Subgraph).deleteVerts S).coe ≃g
      G.induce (A \ (Subtype.val '' S)) where
  toFun x := ⟨x.val.val, x.val.property, by
    rintro ⟨y, hy, hyx⟩
    have heq : y = x.val := Subtype.ext hyx
    exact x.property.2 (heq ▸ hy)⟩
  invFun x := ⟨⟨x.val, x.property.1⟩, by
    refine ⟨Set.mem_univ _, ?_⟩
    intro h
    exact x.property.2 ⟨⟨x.val, x.property.1⟩, h, rfl⟩⟩
  left_inv x := by apply Subtype.ext; rfl
  right_inv x := by apply Subtype.ext; rfl
  map_rel_iff' := by
    intro x y
    change G.Adj x.val.val y.val.val ↔ _
    simp only [Subgraph.coe_adj, Subgraph.deleteVerts_adj, Subgraph.top_adj]
    exact ⟨fun h ↦ ⟨Set.mem_univ _, x.property.2, Set.mem_univ _, y.property.2, h⟩,
      fun h ↦ h.2.2.2.2⟩

/-- A perfect matching in an induced graph becomes a matching in the
original graph with exactly the prescribed vertex set. -/
theorem matching_on_of_induce {A : Set V}
    (h : ∃ M : (G.induce A).Subgraph, M.IsPerfectMatching) :
    ∃ M : G.Subgraph, M.IsMatching ∧ M.verts = A := by
  obtain ⟨M, hM⟩ := h
  let incl : (G.induce A) →g G := ⟨Subtype.val, fun h ↦ h⟩
  refine ⟨M.map incl, hM.1.map incl Subtype.val_injective, ?_⟩
  ext u
  constructor
  · rintro ⟨v, _, rfl⟩
    exact v.property
  · intro hu
    exact ⟨⟨u, hu⟩, hM.2 _, rfl⟩

variable [DecidableEq V] [Finite V]

/-- Tutte's condition stated using finite separating partitions of a region.
The universal quantifier covers, in particular, the connected-component
partition appearing in Mathlib's form of Tutte's theorem. -/
theorem perfect_matching_of_separation_bounds (G : SimpleGraph V) (A : Finset V)
    (h : ∀ S F, SeparatesOn G A S F → (oddParts F).card ≤ S.card) :
    ∃ M : (G.induce (A : Set V)).Subgraph, M.IsPerfectMatching := by
  classical
  let := Fintype.ofFinite V
  apply SimpleGraph.tutte.mpr
  intro S
  let U : Finset V := S.toFinset.image Subtype.val
  have hUA : U ⊆ A := by
    intro u hu
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hu
    exact x.property
  obtain ⟨F, hF, hodd⟩ := exists_separating_partition_with_odd_count G A U hUA
  have hbound := h U F hF
  have hcard : U.card = S.ncard := by
    dsimp [U]
    rw [Finset.card_image_of_injective _ Subtype.val_injective, ← Set.ncard_eq_toFinset_card']
  have hset : (↑(A \ U) : Set V) = (A : Set V) \ (Subtype.val '' S) := by
    ext u
    simp [U]
  have hiso := oddComponents_ncard_eq_of_iso (deleteInduceIso G (A : Set V) S)
  have htarget : ((⊤ : (G.induce (A : Set V)).Subgraph).deleteVerts S).coe.oddComponents.ncard =
      (oddParts F).card := by
    rw [hiso, hodd, hset]
  change ¬ S.ncard < _
  rw [htarget, ← hcard]
  exact not_lt_of_ge hbound

end Erdos547.DPRS

#print axioms Erdos547.DPRS.perfect_matching_of_separation_bounds
