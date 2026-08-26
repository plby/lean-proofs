import ErdosProblems.Erdos73.DeletedComponents
import ErdosProblems.Erdos73.OddPathAuxiliary

/-! Every odd deleted component contains a terminal or an exposed mate. -/

namespace Erdos73

open SimpleGraph Finset Erdos556 OddPathVertex

variable {V : Type*} [DecidableEq V]

def oddPathTerminals (A : Finset V) : Finset (OddPathVertex A) := A.image Sum.inl

theorem mem_oddPathTerminals (A : Finset V) (x : OddPathVertex A) :
    x ∈ oddPathTerminals A ↔ projection x ∈ A := by
  cases x with
  | inl v => simp [oddPathTerminals, projection]
  | inr v => simp [oddPathTerminals, projection, v.property]

theorem oddPathTerminals_card (A : Finset V) : (oddPathTerminals A).card = A.card :=
  Finset.card_image_of_injective _ Sum.inl_injective

variable [Fintype V]

def oddPathExposedMates (A : Finset V) (W : Finset (OddPathVertex A)) :
    Finset (OddPathVertex A) :=
  Finset.univ.filter (fun x => projection x ∉ A ∧ x ∉ W ∧ mate x ∈ W)

theorem mem_oddPathExposedMates {A : Finset V} (W : Finset (OddPathVertex A))
    (x : OddPathVertex A) :
    x ∈ oddPathExposedMates A W ↔ projection x ∉ A ∧ x ∉ W ∧ mate x ∈ W := by
  simp only [oddPathExposedMates, Finset.mem_filter, Finset.mem_univ, true_and]

theorem oddPathTerminals_disjoint_exposed {A : Finset V} (W : Finset (OddPathVertex A)) :
    Disjoint (oddPathTerminals A) (oddPathExposedMates A W) := by
  apply Finset.disjoint_left.mpr
  intro x hxT hxB
  exact ((mem_oddPathExposedMates W x).mp hxB).1 ((mem_oddPathTerminals A x).mp hxT)

open scoped Classical in
theorem odd_deletedComponent_meets_terminals_or_exposed {G : SimpleGraph V} {A : Finset V}
    (W : Finset (OddPathVertex A))
    (C : (vertexDeletedGraph (oddPathAuxiliary G A) W).ConnectedComponent)
    (hodd : Odd C.supp.ncard) :
    ((oddPathTerminals A ∪ oddPathExposedMates A W) ∩ deletedComponentVertices C).Nonempty := by
  by_contra hnone
  have hnot (x : OddPathVertex A) (hx : x ∈ deletedComponentVertices C) :
      x ∉ oddPathTerminals A ∪ oddPathExposedMates A W :=
    fun he => hnone ⟨x, Finset.mem_inter.mpr ⟨he, hx⟩⟩
  have hnonterminal (x : OddPathVertex A) (hx : x ∈ deletedComponentVertices C) :
      projection x ∉ A := fun ht => hnot x hx
    (Finset.mem_union_left _ ((mem_oddPathTerminals A x).mpr ht))
  have hmate (x : OddPathVertex A) (hx : x ∈ deletedComponentVertices C) :
      mate x ∈ deletedComponentVertices C := by
    have hmW : mate x ∉ W := by
      intro he
      exact hnot x hx (Finset.mem_union_right _ ((mem_oddPathExposedMates W x).mpr
        ⟨hnonterminal x hx, deletedComponentVertices_not_mem C hx, he⟩))
    exact deletedComponentVertices_closed C hx hmW
      (oddPathAuxiliary_adj_mate G A x (hnonterminal x hx))
  let M := matchingOn (oddPathBaseMatching A) (deletedComponentVertices C)
  have hM : EdgeMatching (oddPathAuxiliary G A) M :=
    matchingOn_isMatching (oddPathBaseMatching_isMatching G A) _
  have hsupp : matchingSupport M = deletedComponentVertices C := by
    apply Finset.Subset.antisymm (matchingOn_support_subset _ _)
    intro x hx
    apply matchingSupport_mem.mpr
    refine ⟨s(x, mate x), mem_matchingOn.mpr ⟨?_, hx, hmate x hx⟩, Sym2.mem_mk_left _ _⟩
    exact (mem_oddPathBaseMatching_iff x (mate x)).mpr ⟨rfl, hnonterminal x hx⟩
  have hcard := hM.card_support
  rw [hsupp, deletedComponentVertices_card] at hcard
  have heven : Even C.supp.ncard := ⟨M.card, by omega⟩
  exact (Nat.not_odd_iff_even.mpr heven) hodd

end Erdos73
