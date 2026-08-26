import ErdosProblems.Erdos19.Core

/-! # Restricting a set-valued hypergraph to a family of its edges -/

namespace Erdos19.SetHypergraph

attribute [local instance] Classical.propDecidable

variable {V : Type*} (H : SetHypergraph V)

def restrictEdges (S : Set H) : SetHypergraph V := Subtype.val '' S

theorem restrictEdges_subset (S : Set H) : H.restrictEdges S ⊆ H := by
  rintro e ⟨f, _, rfl⟩
  exact f.2

noncomputable def restrictEdgesEquiv (S : Set H) : S ≃ H.restrictEdges S :=
  Equiv.Set.image Subtype.val S Subtype.val_injective

@[simp] theorem restrictEdgesEquiv_val (S : Set H) (e : S) :
    (H.restrictEdgesEquiv S e).1 = e.1.1 := rfl

theorem restrictEdges_linear (hlinear : H.IsLinear) (S : Set H) :
    (H.restrictEdges S).IsLinear := by
  intro e he f hf hef
  exact hlinear (H.restrictEdges_subset S he) (H.restrictEdges_subset S hf) hef

theorem restrictEdges_union_compl (S : Set H) : H.restrictEdges S ∪ H.restrictEdges Sᶜ = H := by
  ext e
  constructor
  · rintro (he | he)
    · exact H.restrictEdges_subset S he
    · exact H.restrictEdges_subset Sᶜ he
  · intro he
    by_cases hS : (⟨e, he⟩ : H) ∈ S
    · exact Or.inl ⟨⟨e, he⟩, hS, rfl⟩
    · exact Or.inr ⟨⟨e, he⟩, hS, rfl⟩

theorem sum_restrictEdges [Fintype V] (S : Set H) (weight : Set V → ℕ) :
    (∑ e : H.restrictEdges S, weight e.1) = ∑ e : S, weight e.1.1 := by
  classical
  exact ((H.restrictEdgesEquiv S).sum_comp (fun e ↦ weight e.1)).symm

theorem sum_restrictEdges_finset [Fintype V] (S : Finset H) (weight : Set V → ℕ) :
    (∑ e : H.restrictEdges (S : Set H), weight e.1) = ∑ e ∈ S, weight e.1 := by
  rw [sum_restrictEdges]
  exact (Finset.sum_subtype S (fun _ ↦ Iff.rfl) (fun e ↦ weight e.1)).symm

theorem sum_restrictEdges_add_compl [Fintype V] (S : Set H) (weight : Set V → ℕ) :
    (∑ e : H.restrictEdges S, weight e.1) + (∑ e : H.restrictEdges Sᶜ, weight e.1) =
      ∑ e : H, weight e.1 := by
  rw [sum_restrictEdges, sum_restrictEdges]
  convert! Fintype.sum_subtype_add_sum_subtype (fun e : H ↦ e ∈ S) (fun e ↦ weight e.1) using 1
  congr 1
  apply Finset.sum_congr
  · ext e
    simp
  · intro e _
    rfl

noncomputable def restrictEdgesLineGraphIso (S : Set H) :
    H.lineGraph.induce S ≃g (H.restrictEdges S).lineGraph :=
  { H.restrictEdgesEquiv S with
    map_rel_iff' := by
      intro e f
      change ((H.restrictEdgesEquiv S e) ≠ (H.restrictEdgesEquiv S f) ∧
        (e.1.1 ∩ f.1.1).Nonempty) ↔ (e.1 ≠ f.1 ∧ (e.1.1 ∩ f.1.1).Nonempty)
      rw [ne_eq, ne_eq, (H.restrictEdgesEquiv S).injective.eq_iff,
        Subtype.val_injective.eq_iff] }

#print axioms sum_restrictEdges_add_compl
#print axioms restrictEdgesLineGraphIso

end Erdos19.SetHypergraph
