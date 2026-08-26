import ErdosProblems.Erdos547.WeightedNeighbourhood

/-!
# A union-size bound from two weighted neighbourhoods and their overlap
-/

namespace Erdos547.DPRS

open Finset SimpleGraph
open scoped BigOperators

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

open scoped Classical in
theorem EdgeWeights.two_neighbourhoods_card_bound (w : EdgeWeights G) (S : Finset V)
    (d₁ d₂ : V) (h₁ : ∀ u, G.Adj d₁ u → u ∈ S) (h₂ : ∀ u, G.Adj d₂ u → u ∈ S) :
    w.degree d₁ + w.degree d₂ - w.degreeOn (Finset.univ.filter (G.Adj d₂)) d₁ ≤
      (S.card : ℝ) := by
  classical
  have he₁ : (∑ u ∈ S, w.weight d₁ u) = w.degree d₁ :=
    Finset.sum_subset (Finset.subset_univ _) (fun u _ hu ↦
      w.supported d₁ u (fun h ↦ hu (h₁ u h)))
  have he₂ : (∑ u ∈ S, w.weight d₂ u) = w.degree d₂ :=
    Finset.sum_subset (Finset.subset_univ _) (fun u _ hu ↦
      w.supported d₂ u (fun h ↦ hu (h₂ u h)))
  have hf : S.filter (G.Adj d₂) = Finset.univ.filter (G.Adj d₂) := by
    ext u
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun h ↦ h.2, fun h ↦ ⟨h₂ u h, h⟩⟩
  have hcommon : (∑ u ∈ S, if G.Adj d₂ u then w.weight d₁ u else 0) =
      w.degreeOn (Finset.univ.filter (G.Adj d₂)) d₁ := by
    rw [← Finset.sum_filter, hf]
    rfl
  have hp (u : V) : w.weight d₁ u + w.weight d₂ u ≤
      1 + if G.Adj d₂ u then w.weight d₁ u else 0 := by
    by_cases hu : G.Adj d₂ u
    · rw [if_pos hu]
      linarith [w.at_most_one d₂ u]
    · rw [if_neg hu, w.supported d₂ u hu, add_zero, add_zero]
      exact w.at_most_one d₁ u
  have hh := Finset.sum_le_sum (s := S) (fun u _ ↦ hp u)
  simp only [Finset.sum_add_distrib, he₁, he₂, hcommon, Finset.sum_const, nsmul_eq_mul,
    mul_one] at hh
  linarith

end Erdos547.DPRS

#print axioms Erdos547.DPRS.EdgeWeights.two_neighbourhoods_card_bound
