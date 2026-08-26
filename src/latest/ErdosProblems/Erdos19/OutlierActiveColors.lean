import ErdosProblems.Erdos19.ColorIncidence

/-! # Deterministic active-color sets for exceptional vertices

Only the degree excess over the intended residual bound must be matched.
The incidence budget guarantees enough colors not used by large edges.
-/

namespace Erdos19

open Finset

attribute [local instance] Classical.propDecidable

theorem exists_active_colors_for_residual_degree
    {V : Type*} (n m : ℕ) (hm : m < n) (degree : V → ℕ)
    (C : Fin m → Set V)
    (hbudget : ∀ v, degree v + (∑ i : Fin m, if v ∈ C i then 1 else 0) ≤ n - 1) :
    ∃ active : V → Finset (Fin m),
      (∀ v i, i ∈ active v → v ∉ C i) ∧
      (∀ v, (active v).card = degree v - (n - m - 1)) ∧
      (∀ v, degree v ≤ (n - m - 1) + (active v).card) ∧
      (∀ v, (active v).Nonempty → degree v = (n - m - 1) + (active v).card) := by
  classical
  let available (v : V) := (univ : Finset (Fin m)).filter fun i ↦ v ∉ C i
  have hroom : ∀ v, degree v - (n - m - 1) ≤ (available v).card := by
    intro v
    have hsplit : (∑ i : Fin m, if v ∈ C i then 1 else 0) + (available v).card = m := by
      have h := @card_filter_add_card_filter_not (Fin m) univ (fun i ↦ v ∈ C i) _ _
      simpa [available] using h
    have hb := hbudget v
    omega
  have hex : ∀ v, ∃ T : Finset (Fin m), T ⊆ available v ∧
      T.card = degree v - (n - m - 1) := by
    intro v
    exact exists_subset_card_eq (hroom v)
  choose active hsub hcard using hex
  refine ⟨active, ?_, hcard, ?_, ?_⟩
  · intro v i hi
    exact (mem_filter.mp (hsub v hi)).2
  · intro v
    rw [hcard]
    omega
  · intro v hv
    have hpos := card_pos.mpr hv
    have hc := hcard v
    omega

namespace SetHypergraph

theorem exists_large_coloring_active_sets {V : Type*} [Fintype V]
    (H : SetHypergraph V) (hlinear : H.IsLinear) (hcomplete : H.IsPairComplete)
    (hsize : ∀ e : H, 2 ≤ e.1.ncard) (m : ℕ) (hm : m < Fintype.card V)
    (large : H.largePart.EdgeColoring (Fin m)) :
    ∃ active : V → Finset (Fin m),
      (∀ v i, i ∈ active v → v ∉ H.largePart.colorCovered large i) ∧
      (∀ v, (active v).card = (H.twoGraph.neighborSet v).ncard - (Fintype.card V - m - 1)) ∧
      (∀ v, (H.twoGraph.neighborSet v).ncard ≤ (Fintype.card V - m - 1) + (active v).card) ∧
      (∀ v, (active v).Nonempty → (H.twoGraph.neighborSet v).ncard =
        (Fintype.card V - m - 1) + (active v).card) := by
  apply exists_active_colors_for_residual_degree (Fintype.card V) m hm
    (fun v ↦ (H.twoGraph.neighborSet v).ncard) (H.largePart.colorCovered large)
  intro v
  have h := H.large_coloring_parity_degree_budget hlinear hcomplete hsize large v
  omega

#print axioms exists_large_coloring_active_sets

end SetHypergraph
end Erdos19
