import ErdosProblems.Erdos547.IndependentDemandHall

/-!
# A transport with a bound on unused diagonal demand
-/

noncomputable section

namespace Erdos547.DPRS

open Finset SimpleGraph
open scoped BigOperators

variable {V : Type*} [Fintype V]

theorem exists_transport_with_diagonal_bound (G : SimpleGraph V) (a b : V → ℝ)
    (ha : ∀ u, 0 ≤ a u) (hab : ∀ u, a u ≤ b u)
    (hI : ∀ I : Finset V, (∀ u ∈ I, ∀ v ∈ I, ¬ G.Adj u v) →
      (∑ u ∈ I, a u) ≤ ∑ v ∈ graphNeighbours G I, b v) :
    ∃ f : V → V → ℝ, (∀ u v, 0 ≤ f u v) ∧ (∀ u, ∑ v, f u v = b u) ∧
      (∀ v, ∑ u, f u v = b v) ∧ (∀ u v, ¬ (G.Adj u v ∨ u = v) → f u v = 0) ∧
      ∀ u, f u u ≤ b u - a u := by
  classical
  let r : V ⊕ V → ℝ := Sum.elim a (fun u ↦ b u - a u)
  let P : V ⊕ V → V → Prop := fun x v ↦ match x with
    | .inl u => G.Adj u v
    | .inr u => G.Adj u v ∨ u = v
  have hr : ∀ x, 0 ≤ r x := by
    intro x
    cases x with
    | inl u => exact ha u
    | inr u => exact sub_nonneg.mpr (hab u)
  have hb (u : V) : 0 ≤ b u := (ha u).trans (hab u)
  have hHall : ∀ S : Finset (V ⊕ V), (∑ x ∈ S, r x) ≤
      ∑ v ∈ Finset.univ.filter (fun v ↦ ∃ x ∈ S, P x v), b v := by
    intro S
    let U := Finset.univ.filter (fun u ↦ Sum.inl u ∈ S)
    let W := Finset.univ.filter (fun u ↦ Sum.inr u ∈ S)
    have hdemand : (∑ x ∈ S, r x) = (∑ u ∈ U, a u) + ∑ u ∈ W, (b u - a u) := by
      calc
        _ = ∑ x : V ⊕ V, if x ∈ S then r x else 0 := by simp
        _ = _ := by
          simp only [Fintype.sum_sum_type, r, Sum.elim_inl, Sum.elim_inr, U, W,
            Finset.sum_filter]
    have hneigh : Finset.univ.filter (fun v ↦ ∃ x ∈ S, P x v) = graphNeighbours G (U ∪ W) ∪ W := by
      ext v
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
      constructor
      · rintro ⟨x, hx, hP⟩
        cases x with
        | inl u =>
          exact Or.inl (Finset.mem_filter.mpr ⟨Finset.mem_univ _, u,
            Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩), hP⟩)
        | inr u =>
          rcases hP with hP | hP
          · exact Or.inl (Finset.mem_filter.mpr ⟨Finset.mem_univ _, u,
              Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩), hP⟩)
          · subst u
            exact Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩)
      · rintro (h | h)
        · obtain ⟨u, hu, huv⟩ := (Finset.mem_filter.mp h).2
          rcases Finset.mem_union.mp hu with hu | hu
          · exact ⟨.inl u, (Finset.mem_filter.mp hu).2, huv⟩
          · exact ⟨.inr u, (Finset.mem_filter.mp hu).2, Or.inl huv⟩
        · exact ⟨.inr v, (Finset.mem_filter.mp h).2, Or.inr rfl⟩
    rw [hdemand, hneigh]
    exact independent_demand_hall G a b ha hab hI U W
  obtain ⟨F, hF, hsupp, hrow, hcol⟩ := exists_rectangular_transport P r b hr hb hHall
  let f := fun u v ↦ F (.inl u) v + F (.inr u) v
  have hrowf (u : V) : (∑ v, f u v) = b u := by
    simp only [f, Finset.sum_add_distrib, hrow, r, Sum.elim_inl, Sum.elim_inr]
    ring
  have hcolf (v : V) : (∑ u, f u v) ≤ b v := by
    simpa only [f, Finset.sum_add_distrib, Fintype.sum_sum_type] using hcol v
  have hcol_eq (v : V) : (∑ u, f u v) = b v := by
    apply le_antisymm (hcolf v)
    by_contra hn
    have hlt : (∑ u, f u v) < b v := lt_of_not_ge hn
    have hh := Finset.sum_lt_sum (fun z (_ : z ∈ (Finset.univ : Finset V)) ↦ hcolf z)
      ⟨v, Finset.mem_univ _, hlt⟩
    rw [Finset.sum_comm] at hh
    simp only [hrowf] at hh
    exact lt_irrefl _ hh
  refine ⟨f, fun u v ↦ add_nonneg (hF _ _) (hF _ _), hrowf, hcol_eq, ?_, ?_⟩
  · intro u v huv
    have h₁ : F (.inl u) v = 0 := hsupp _ _ (fun h ↦ huv (Or.inl h))
    have h₂ : F (.inr u) v = 0 := hsupp _ _ huv
    simp only [f, h₁, h₂, add_zero]
  · intro u
    have h₁ : F (.inl u) u = 0 := hsupp _ _ (G.loopless.irrefl u)
    have h₂ : F (.inr u) u ≤ ∑ v, F (.inr u) v :=
      Finset.single_le_sum (fun v _ ↦ hF (.inr u) v) (Finset.mem_univ u)
    simpa only [f, h₁, zero_add, hrow, r, Sum.elim_inr] using h₂

end Erdos547.DPRS

#print axioms Erdos547.DPRS.exists_transport_with_diagonal_bound
