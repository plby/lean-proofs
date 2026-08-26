import ErdosProblems.Erdos547.IndependentDefect

/-!
# Saturation when the uncovered demand outside good vertices is small
-/

noncomputable section

namespace Erdos547.DPRS

open Finset SimpleGraph
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

omit [DecidableEq V] in
theorem FractionalMatching.sum_load_le_neighbour_capacity (μ : FractionalMatching G)
    (b : V → ℝ) (hcap : ∀ u, μ.load u ≤ b u) (S : Finset V) :
    (∑ u ∈ S, μ.load u) ≤ ∑ v ∈ graphNeighbours G S, b v := by
  classical
  have hrow (u : V) (hu : u ∈ S) : μ.load u = ∑ v ∈ graphNeighbours G S, μ.weight u v := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro v _ hv
    exact μ.supported u v (fun huv ↦ hv (Finset.mem_filter.mpr ⟨Finset.mem_univ _, u, hu, huv⟩))
  calc
    _ = ∑ u ∈ S, ∑ v ∈ graphNeighbours G S, μ.weight u v :=
      Finset.sum_congr rfl fun u hu ↦ hrow u hu
    _ = ∑ v ∈ graphNeighbours G S, ∑ u ∈ S, μ.weight u v := Finset.sum_comm
    _ ≤ ∑ v ∈ graphNeighbours G S, μ.load v := Finset.sum_le_sum fun v _ ↦ by
      calc
        _ = ∑ u ∈ S, μ.weight v u := Finset.sum_congr rfl fun u _ ↦ μ.symmetric u v
        _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun u _ _ ↦ μ.nonnegative v u)
    _ ≤ _ := Finset.sum_le_sum fun v _ ↦ hcap v

open scoped Classical in
theorem exists_fractional_saturation_of_deficit_bound (G : SimpleGraph V)
    (a b : V → ℝ) (A D₀ : ℝ)
    (ha : ∀ u, 0 ≤ a u) (hab : ∀ u, a u ≤ b u) (hb : ∀ u, b u ≤ 1)
    (μ₀ : FractionalMatching G) (hcap : ∀ u, μ₀.load u ≤ b u)
    (good : Finset V)
    (hgood : ∀ u ∈ good, A ≤ ∑ v ∈ Finset.univ.filter (G.Adj u), b v)
    (hbad : (∑ u ∈ goodᶜ, max 0 (a u - μ₀.load u)) ≤ D₀)
    (hsize : A + D₀ ≤ ∑ u, a u) :
    ∃ μ : FractionalMatching G, (∀ u, μ.load u ≤ b u) ∧
      A ≤ ∑ u, min (a u) (μ.load u) := by
  classical
  let D := (∑ u, a u) - A
  have hD₀ : 0 ≤ D₀ := (Finset.sum_nonneg fun u _ ↦ le_max_left 0 _).trans hbad
  have hD : 0 ≤ D := by dsimp [D]; linarith
  have hDD : D₀ ≤ D := by dsimp [D]; linarith
  have hbn (u : V) : 0 ≤ b u := (ha u).trans (hab u)
  have hHall : ∀ I : Finset V, (∀ u ∈ I, ∀ v ∈ I, ¬ G.Adj u v) →
      (∑ u ∈ I, a u) ≤ (∑ v ∈ graphNeighbours G I, b v) + D := by
    intro I _hind
    by_cases hmeet : ∃ u ∈ I, u ∈ good
    · obtain ⟨u, hu, hug⟩ := hmeet
      have hsub : Finset.univ.filter (G.Adj u) ⊆ graphNeighbours G I := by
        intro v hv
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, u, hu, (Finset.mem_filter.mp hv).2⟩
      have hN : A ≤ ∑ v ∈ graphNeighbours G I, b v := (hgood u hug).trans
        (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun v _ _ ↦ hbn v))
      have htotal : (∑ u ∈ I, a u) ≤ ∑ u, a u :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun u _ _ ↦ ha u)
      dsimp [D]
      linarith
    · have hsub : I ⊆ goodᶜ := fun u hu ↦ Finset.mem_compl.mpr (fun hug ↦ hmeet ⟨u, hu, hug⟩)
      have hdef : (∑ u ∈ I, max 0 (a u - μ₀.load u)) ≤ D₀ :=
        (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun u _ _ ↦ le_max_left 0 _)).trans hbad
      have hp : (∑ u ∈ I, a u) ≤ (∑ u ∈ I, μ₀.load u) +
          ∑ u ∈ I, max 0 (a u - μ₀.load u) := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_le_sum fun u _ ↦ by linarith [le_max_right 0 (a u - μ₀.load u)]
      have hn := μ₀.sum_load_le_neighbour_capacity b hcap I
      linarith
  obtain ⟨μ, hμ, hs⟩ :=
    exists_fractional_saturation_of_independent_defect G a b D hD ha hab hb hHall
  refine ⟨μ, hμ, ?_⟩
  dsimp [D] at hs
  linarith

end Erdos547.DPRS

#print axioms Erdos547.DPRS.exists_fractional_saturation_of_deficit_bound
