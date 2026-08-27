/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTConditionedContainment
import ErdosProblems.Erdos4b.FGKMTPinnedSurvivalProduct
import ErdosProblems.Erdos4b.FGKMTPinnedEdgeIntersection

/-! # The conditioned raw vertex mean, with the test-set codegree loss -/

namespace Erdos4b.FGKMT.FiniteEdgeFamily

noncomputable section

open scoped BigOperators

variable {I Ω α : Type*} [Fintype I] [Fintype Ω] [DecidableEq α]

def vertexOutcomes (F : FiniteEdgeFamily I Ω α) (i : I) (v : α) : Finset Ω :=
  Finset.univ.filter fun w => v ∈ F.edge i w

def rawVertexDegree (F : FiniteEdgeFamily I Ω α) (P : α → ℝ) (W : Finset α) (v : α) : ℝ :=
  ∑ i, F.rawEventMass P W i (F.vertexOutcomes i v)

def pinnedGeometricDegree (F : FiniteEdgeFamily I Ω α) (P : α → ℝ) (e : Finset α) (v : α) : ℝ :=
  ∑ i, ∑ w ∈ F.vertexOutcomes i v, F.mass i w *
    (survivalProduct P (e ∪ F.edge i w) /
      (survivalProduct P e * survivalProduct P (F.edge i w)))

theorem vertexOutcomes_mass (F : FiniteEdgeFamily I Ω α) (i : I) (v : α) :
    (∑ w ∈ F.vertexOutcomes i v, F.mass i w) = F.vertexMass i v := by
  simp only [vertexOutcomes, Finset.sum_filter, vertexMass]

theorem vertexOutcomes_degree_mass (F : FiniteEdgeFamily I Ω α) (v : α) :
    (∑ i, ∑ w ∈ F.vertexOutcomes i v, F.mass i w) = F.degree v := by
  simp only [F.vertexOutcomes_mass, degree]

theorem pinnedGeometricDegree_error (F : FiniteEdgeFamily I Ω α)
    {P : α → ℝ} {κ δ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1)
    (hP0 : ∀ u ∈ F.vertices, κ ≤ P u) (hP1 : ∀ u ∈ F.vertices, P u ≤ 1)
    (e : Finset α) (heV : e ⊆ F.vertices) (v : α) (hve : v ∈ e) (hδ : 0 ≤ δ)
    (hcodeg : ∀ u ∈ e, u ≠ v → F.codegree v u ≤ δ) :
    |F.pinnedGeometricDegree P e v - F.degree v / P v| ≤
      ((1 / P v) * (1 / κ ^ F.rank)) * ((e.card : ℝ) * δ) := by
  have hvpos : 0 < P v := hκ0.trans_le (hP0 v (heV hve))
  have hcoef : 0 ≤ (1 / P v) * (1 / κ ^ F.rank) := by positivity
  have heq : F.pinnedGeometricDegree P e v - F.degree v / P v =
      ∑ i, ∑ w ∈ F.vertexOutcomes i v, F.mass i w *
        (survivalProduct P (e ∪ F.edge i w) /
          (survivalProduct P e * survivalProduct P (F.edge i w)) - 1 / P v) := by
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul,
      F.vertexOutcomes_degree_mass, pinnedGeometricDegree]
    ring
  rw [heq]
  calc
    _ ≤ ∑ i, ∑ w ∈ F.vertexOutcomes i v, |F.mass i w *
        (survivalProduct P (e ∪ F.edge i w) /
          (survivalProduct P e * survivalProduct P (F.edge i w)) - 1 / P v)| :=
      (Finset.abs_sum_le_sum_abs _ _).trans
        (Finset.sum_le_sum fun i _hi => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ i, ∑ w ∈ F.vertexOutcomes i v, F.mass i w *
        (((1 / P v) * (1 / κ ^ F.rank)) *
          (if (e.erase v ∩ F.edge i w).Nonempty then 1 else 0)) := by
      apply Finset.sum_le_sum
      intro i _hi
      apply Finset.sum_le_sum
      intro w hw
      have hvw := (Finset.mem_filter.mp hw).2
      rw [abs_mul, abs_of_nonneg (F.mass_nonneg i w)]
      exact mul_le_mul_of_nonneg_left
        (survivalProduct_pinned_ratio_error hκ0 hκ1 hP0 hP1
          (F.edge_subset i w) heV (F.edge_card_le i w) hvw hve) (F.mass_nonneg i w)
    _ = ((1 / P v) * (1 / κ ^ F.rank)) * ∑ i, F.pinnedHitMass i v (e.erase v) := by
      simp only [vertexOutcomes, Finset.sum_filter, pinnedHitMass, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _hi
      apply Finset.sum_congr rfl
      intro w _hw
      by_cases hvw : v ∈ F.edge i w
      · by_cases hhit : (e.erase v ∩ F.edge i w).Nonempty
        · simp only [hvw, hhit, and_self, if_true, mul_one]
          ring
        · simp only [hvw, hhit, and_false, if_true, if_false, mul_zero]
      · simp only [hvw, false_and, if_false, mul_zero]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ hcoef
      calc
        _ ≤ ((e.erase v).card : ℝ) * δ := F.pinnedHitMass_sum_le_card_mul v (e.erase v)
          (fun u hu => hcodeg u (Finset.mem_erase.mp hu).2 (Finset.mem_erase.mp hu).1)
        _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast Finset.card_erase_le) hδ

variable {Ξ : Type*} [Fintype Ξ]

theorem rawVertexDegree_conditioned_relative_error (F : FiniteEdgeFamily I Ω α)
    {P : α → ℝ} (hP : ∀ v ∈ F.vertices, 0 < P v)
    (ρ : Ξ → ℝ) (W : Ξ → Finset α) (hρ : ∀ s, 0 ≤ ρ s)
    (e : Finset α) (heV : e ⊆ F.vertices) (v : α)
    {η : ℝ} (hη0 : 0 ≤ η) (hη : η ≤ 1 / 2)
    (he : |containmentMass ρ W e - survivalProduct P e| ≤ η * survivalProduct P e)
    (hU : ∀ i w, v ∈ F.edge i w → |containmentMass ρ W (e ∪ F.edge i w) -
        survivalProduct P (e ∪ F.edge i w)| ≤ η * survivalProduct P (e ∪ F.edge i w)) :
    |(∑ s, conditionedStateMass ρ W e s * F.rawVertexDegree P (W s) v) -
      F.pinnedGeometricDegree P e v| ≤ 4 * η * F.pinnedGeometricDegree P e v := by
  have hgeom (i : I) : (∑ w ∈ F.vertexOutcomes i v,
      F.mass i w / survivalProduct P (F.edge i w) *
        (survivalProduct P (e ∪ F.edge i w) / survivalProduct P e)) =
      ∑ w ∈ F.vertexOutcomes i v, F.mass i w *
        (survivalProduct P (e ∪ F.edge i w) /
          (survivalProduct P e * survivalProduct P (F.edge i w))) :=
    Finset.sum_congr rfl fun w _hw => by ring
  have hex : (∑ s, conditionedStateMass ρ W e s * F.rawVertexDegree P (W s) v) =
      ∑ i, ∑ s, conditionedStateMass ρ W e s *
        F.rawEventMass P (W s) i (F.vertexOutcomes i v) := by
    simp only [rawVertexDegree, Finset.mul_sum]
    exact Finset.sum_comm
  rw [hex, pinnedGeometricDegree, ← Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _hi
  have h := F.rawEventMass_conditioned_mean_error hP ρ W hρ e heV hη0 hη i
    (F.vertexOutcomes i v) he (fun w hw => hU i w (Finset.mem_filter.mp hw).2)
  simpa only [hgeom] using h

theorem rawVertexDegree_conditioned_mean_error (F : FiniteEdgeFamily I Ω α)
    {P : α → ℝ} {κ δ η : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1)
    (hP0 : ∀ u ∈ F.vertices, κ ≤ P u) (hP1 : ∀ u ∈ F.vertices, P u ≤ 1)
    (ρ : Ξ → ℝ) (W : Ξ → Finset α) (hρ : ∀ s, 0 ≤ ρ s)
    (e : Finset α) (heV : e ⊆ F.vertices) (v : α) (hve : v ∈ e) (hδ : 0 ≤ δ)
    (hcodeg : ∀ u ∈ e, u ≠ v → F.codegree v u ≤ δ)
    (hη0 : 0 ≤ η) (hη : η ≤ 1 / 2)
    (he : |containmentMass ρ W e - survivalProduct P e| ≤ η * survivalProduct P e)
    (hU : ∀ i w, v ∈ F.edge i w → |containmentMass ρ W (e ∪ F.edge i w) -
        survivalProduct P (e ∪ F.edge i w)| ≤ η * survivalProduct P (e ∪ F.edge i w)) :
    |(∑ s, conditionedStateMass ρ W e s * F.rawVertexDegree P (W s) v) -
      F.degree v / P v| ≤
      4 * η * (F.degree v / P v +
        ((1 / P v) * (1 / κ ^ F.rank)) * ((e.card : ℝ) * δ)) +
        ((1 / P v) * (1 / κ ^ F.rank)) * ((e.card : ℝ) * δ) := by
  have hm := F.rawVertexDegree_conditioned_relative_error
    (fun u hu => hκ0.trans_le (hP0 u hu)) ρ W hρ e heV v hη0 hη he hU
  have hg := F.pinnedGeometricDegree_error hκ0 hκ1 hP0 hP1 e heV v hve hδ hcodeg
  have hupper := (abs_le.mp hg).2
  have hscaled := mul_le_mul_of_nonneg_left hupper (by positivity : 0 ≤ 4 * η)
  calc
    _ ≤ |(∑ s, conditionedStateMass ρ W e s * F.rawVertexDegree P (W s) v) -
        F.pinnedGeometricDegree P e v| +
        |F.pinnedGeometricDegree P e v - F.degree v / P v| := abs_sub_le _ _ _
    _ ≤ _ := by linarith

end

end Erdos4b.FGKMT.FiniteEdgeFamily
