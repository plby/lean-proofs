/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTConditionedVertexMean
import ErdosProblems.Erdos4b.FGKMTPinnedTripleProduct

/-! # Independent pinned pair averages and the three codegree charges -/

namespace Erdos4b.FGKMT.FiniteEdgeFamily

noncomputable section

open scoped BigOperators

variable {I Ω α : Type*} [Fintype I] [Fintype Ω] [DecidableEq α]

def pinnedPairAverage (F : FiniteEdgeFamily I Ω α) (v : α)
    (f : Finset α → Finset α → ℝ) : ℝ :=
  ∑ i, ∑ w ∈ F.vertexOutcomes i v, F.mass i w *
    ∑ j, ∑ z ∈ F.vertexOutcomes j v, F.mass j z * f (F.edge i w) (F.edge j z)

theorem pinnedPairAverage_add (F : FiniteEdgeFamily I Ω α) (v : α)
    (f g : Finset α → Finset α → ℝ) :
    F.pinnedPairAverage v (fun A B => f A B + g A B) =
      F.pinnedPairAverage v f + F.pinnedPairAverage v g := by
  simp only [pinnedPairAverage, mul_add, Finset.sum_add_distrib]

theorem pinnedPairAverage_sub (F : FiniteEdgeFamily I Ω α) (v : α)
    (f g : Finset α → Finset α → ℝ) :
    F.pinnedPairAverage v (fun A B => f A B - g A B) =
      F.pinnedPairAverage v f - F.pinnedPairAverage v g := by
  simp only [pinnedPairAverage, mul_sub, Finset.sum_sub_distrib]

theorem pinnedPairAverage_const_mul (F : FiniteEdgeFamily I Ω α) (v : α)
    (c : ℝ) (f : Finset α → Finset α → ℝ) :
    F.pinnedPairAverage v (fun A B => c * f A B) = c * F.pinnedPairAverage v f := by
  simp only [pinnedPairAverage, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  apply Finset.sum_congr rfl
  intro w _hw
  apply Finset.sum_congr rfl
  intro j _hj
  apply Finset.sum_congr rfl
  intro z _hz
  ring

theorem pinnedPairAverage_const (F : FiniteEdgeFamily I Ω α) (v : α) (c : ℝ) :
    F.pinnedPairAverage v (fun _ _ => c) = F.degree v ^ 2 * c := by
  simp only [pinnedPairAverage, ← Finset.sum_mul, F.vertexOutcomes_degree_mass]
  ring

theorem pinnedPairAverage_mono (F : FiniteEdgeFamily I Ω α) (v : α)
    {f g : Finset α → Finset α → ℝ}
    (h : ∀ i w, v ∈ F.edge i w → ∀ j z, v ∈ F.edge j z →
      f (F.edge i w) (F.edge j z) ≤ g (F.edge i w) (F.edge j z)) :
    F.pinnedPairAverage v f ≤ F.pinnedPairAverage v g := by
  apply Finset.sum_le_sum
  intro i _hi
  apply Finset.sum_le_sum
  intro w hw
  apply mul_le_mul_of_nonneg_left _ (F.mass_nonneg i w)
  apply Finset.sum_le_sum
  intro j _hj
  apply Finset.sum_le_sum
  intro z hz
  exact mul_le_mul_of_nonneg_left
    (h i w (Finset.mem_filter.mp hw).2 j z (Finset.mem_filter.mp hz).2) (F.mass_nonneg j z)

theorem pinnedPairAverage_abs_le (F : FiniteEdgeFamily I Ω α) (v : α)
    (f : Finset α → Finset α → ℝ) :
    |F.pinnedPairAverage v f| ≤ F.pinnedPairAverage v (fun A B => |f A B|) := by
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro i _hi
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro w _hw
  rw [abs_mul, abs_of_nonneg (F.mass_nonneg i w)]
  apply mul_le_mul_of_nonneg_left _ (F.mass_nonneg i w)
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro j _hj
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro z _hz
  rw [abs_mul, abs_of_nonneg (F.mass_nonneg j z)]

theorem pinnedPairAverage_left (F : FiniteEdgeFamily I Ω α) (v : α) (f : Finset α → ℝ) :
    F.pinnedPairAverage v (fun A _ => f A) =
      F.degree v * ∑ i, ∑ w ∈ F.vertexOutcomes i v, F.mass i w * f (F.edge i w) := by
  simp only [pinnedPairAverage, ← Finset.sum_mul, F.vertexOutcomes_degree_mass]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  apply Finset.sum_congr rfl
  intro w _hw
  ring

theorem pinnedPairAverage_right (F : FiniteEdgeFamily I Ω α) (v : α) (f : Finset α → ℝ) :
    F.pinnedPairAverage v (fun _ B => f B) =
      F.degree v * ∑ j, ∑ z ∈ F.vertexOutcomes j v, F.mass j z * f (F.edge j z) := by
  simp only [pinnedPairAverage, ← Finset.sum_mul, F.vertexOutcomes_degree_mass]

theorem vertexOutcomes_hit_mass (F : FiniteEdgeFamily I Ω α) (v : α) (A : Finset α) :
    (∑ i, ∑ w ∈ F.vertexOutcomes i v,
      F.mass i w * (if (A ∩ F.edge i w).Nonempty then 1 else 0)) =
      ∑ i, F.pinnedHitMass i v A := by
  simp only [vertexOutcomes, Finset.sum_filter, pinnedHitMass]
  apply Finset.sum_congr rfl
  intro i _hi
  apply Finset.sum_congr rfl
  intro w _hw
  by_cases hv : v ∈ F.edge i w <;> by_cases hhit : (A ∩ F.edge i w).Nonempty <;>
    simp only [hv, hhit, and_self, and_false, false_and, if_true, if_false, mul_one, mul_zero]

theorem pinnedPairAverage_extra_pair (F : FiniteEdgeFamily I Ω α) (v : α) :
    F.pinnedPairAverage v (fun A B => if (A.erase v ∩ B).Nonempty then 1 else 0) =
      F.pinnedIndependentIntersectionMass v := by
  unfold pinnedPairAverage
  simp_rw [F.vertexOutcomes_hit_mass]
  simp only [vertexOutcomes, Finset.sum_filter, pinnedIndependentIntersectionMass]

theorem pinnedPairAverage_tripleExtra_le (F : FiniteEdgeFamily I Ω α)
    (e : Finset α) (heV : e ⊆ F.vertices) (v : α) {δ : ℝ} (hδ : 0 ≤ δ)
    (hcodeg : ∀ u ∈ F.vertices, u ≠ v → F.codegree v u ≤ δ) :
    F.pinnedPairAverage v (fun A B => tripleExtraIndicator e A B v) ≤
      (2 * (e.card : ℝ) + F.rank) * δ * F.degree v := by
  have htest := F.pinned_test_intersection_le v e hδ (fun u hu => hcodeg u (heV hu))
  have hpair := F.pinnedIndependentIntersectionMass_le v hδ hcodeg
  simp only [tripleExtraIndicator, F.pinnedPairAverage_add, F.pinnedPairAverage_left,
    F.pinnedPairAverage_right, F.vertexOutcomes_hit_mass, F.pinnedPairAverage_extra_pair]
  nlinarith

end

end Erdos4b.FGKMT.FiniteEdgeFamily
