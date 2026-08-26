import ErdosProblems.Erdos547.WeightedHost

/-!
# Elementary weighted-neighbourhood estimates
-/

namespace Erdos547.DPRS

open Finset SimpleGraph
open scoped BigOperators

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

namespace EdgeWeights

theorem saturation_eq_of_covers_neighbours (w : EdgeWeights G) (l : V → ℝ)
    (hl : ∀ v, 0 ≤ l v) (c : V) (hcov : ∀ v, G.Adj c v → w.weight c v ≤ l v) :
    w.saturation l c = w.degree c := by
  apply Finset.sum_congr rfl
  intro v _
  by_cases hv : G.Adj c v
  · exact min_eq_left (hcov v hv)
  · rw [w.supported c v hv, min_eq_left (hl v)]

theorem exists_deficient_of_saturation_lt_degree (w : EdgeWeights G) (l : V → ℝ)
    (c : V) (h : w.saturation l c < w.degree c) : ∃ v, l v < w.weight c v := by
  by_contra hn
  push Not at hn
  have he : w.saturation l c = w.degree c :=
    Finset.sum_congr rfl fun v _ ↦ min_eq_left (hn v)
  exact (ne_of_lt h) he

theorem degree_le_card_of_neighbours_subset (w : EdgeWeights G) (c : V) (S : Finset V)
    (hS : ∀ v, G.Adj c v → v ∈ S) : w.degree c ≤ (S.card : ℝ) := by
  classical
  have he : w.degree c = ∑ v ∈ S, w.weight c v := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro v _ hv
    exact w.supported c v (fun h ↦ hv (hS v h))
  rw [he]
  calc
    _ ≤ ∑ _v ∈ S, (1 : ℝ) := Finset.sum_le_sum fun v _ ↦ w.at_most_one c v
    _ = _ := by simp

theorem exists_neighbour_of_degree_pos (w : EdgeWeights G) (c : V) (h : 0 < w.degree c) :
    ∃ d, G.Adj c d := by
  by_contra hn
  push Not at hn
  have he : w.degree c = 0 := Finset.sum_eq_zero fun v _ ↦ w.supported c v (hn v)
  linarith

open scoped Classical in
theorem degreeOn_le_card_neighbours (w : EdgeWeights G) (c : V) (U : Finset V) :
    w.degreeOn U c ≤ ((U.filter (G.Adj c)).card : ℝ) := by
  classical
  calc
    _ = ∑ u ∈ U.filter (G.Adj c), w.weight c u := by
      symm
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro u hu hn
      exact w.supported c u (fun h ↦ hn (Finset.mem_filter.mpr ⟨hu, h⟩))
    _ ≤ ∑ _u ∈ U.filter (G.Adj c), (1 : ℝ) := Finset.sum_le_sum fun u _ ↦ w.at_most_one c u
    _ = _ := by simp

end EdgeWeights

end Erdos547.DPRS
