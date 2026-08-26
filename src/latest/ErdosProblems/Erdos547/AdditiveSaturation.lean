import ErdosProblems.Erdos547.WeightedHost

/-!
# Exact saturation splitting for arbitrary nonnegative load functions
-/

namespace Erdos547.DPRS

open Finset SimpleGraph

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

theorem EdgeWeights.saturation_add_load (w : EdgeWeights G) (l m : V → ℝ)
    (hl : ∀ u, 0 ≤ l u) (hm : ∀ u, 0 ≤ m u) (c : V) :
    w.saturation l c + (w.truncate l hl).saturation m c =
      w.saturation (fun u ↦ l u + m u) c := by
  rw [EdgeWeights.saturation, EdgeWeights.saturation, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro u _
  have hh := EdgeWeights.min_add_min_truncated (w.weight c u) (l u) (l u + m u)
    (le_add_of_nonneg_right (hm u))
  simpa only [add_sub_cancel_left, EdgeWeights.truncate] using hh

theorem EdgeWeights.degreeOn_add_saturation (w : EdgeWeights G) (l : V → ℝ)
    (c : V) (R : Finset V) (hR : ∀ u ∈ R, l u ≤ w.weight c u)
    (hC : ∀ u ∉ R, w.weight c u ≤ l u) :
    w.degreeOn R c + w.saturation l c = w.degree c + ∑ u ∈ R, l u := by
  classical
  have hdeg : w.degreeOn R c + w.degreeOn Rᶜ c = w.degree c :=
    Finset.sum_add_sum_compl R (w.weight c)
  have hsat : (∑ u ∈ R, l u) + w.degreeOn Rᶜ c = w.saturation l c := by
    have he := Finset.sum_add_sum_compl R (fun u ↦ min (w.weight c u) (l u))
    have heR : (∑ u ∈ R, min (w.weight c u) (l u)) = ∑ u ∈ R, l u :=
      Finset.sum_congr rfl fun u hu ↦ min_eq_right (hR u hu)
    have heC : (∑ u ∈ Rᶜ, min (w.weight c u) (l u)) = w.degreeOn Rᶜ c :=
      Finset.sum_congr rfl fun u hu ↦ min_eq_left (hC u (Finset.mem_compl.mp hu))
    rwa [heR, heC] at he
  linarith

end Erdos547.DPRS

#print axioms Erdos547.DPRS.EdgeWeights.saturation_add_load
