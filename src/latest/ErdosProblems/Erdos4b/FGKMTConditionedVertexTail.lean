/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTPinnedSecondMain

/-! # Explicit conditional vertex second moment, centered moment, and tail -/

namespace Erdos4b.FGKMT.FiniteEdgeFamily

noncomputable section

open scoped BigOperators

variable {I Ω α Ξ : Type*} [Fintype I] [Fintype Ω] [Fintype Ξ] [DecidableEq α]

def vertexFirstError (F : FiniteEdgeFamily I Ω α) (P : α → ℝ)
    (e : Finset α) (κ δ : ℝ) (v : α) : ℝ :=
  ((1 / P v) * (1 / κ ^ F.rank)) * ((e.card : ℝ) * δ)

def vertexMeanError (F : FiniteEdgeFamily I Ω α) (P : α → ℝ)
    (e : Finset α) (κ δ η : ℝ) (v : α) : ℝ :=
  4 * η * (F.degree v / P v + F.vertexFirstError P e κ δ v) + F.vertexFirstError P e κ δ v

def vertexVarianceError (F : FiniteEdgeFamily I Ω α) (P : α → ℝ)
    (e : Finset α) (κ δ η : ℝ) (v : α) : ℝ :=
  4 * η * (F.degree v / P v) ^ 2 + (1 + 4 * η) * F.vertexSecondError P e κ δ v +
    2 * (F.degree v / P v) * F.vertexMeanError P e κ δ η v

theorem rawVertexDegree_conditioned_second_le (F : FiniteEdgeFamily I Ω α)
    {P : α → ℝ} {κ δ η : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1)
    (hP0 : ∀ u ∈ F.vertices, κ ≤ P u) (hP1 : ∀ u ∈ F.vertices, P u ≤ 1)
    (ρ : Ξ → ℝ) (W : Ξ → Finset α) (hρ : ∀ s, 0 ≤ ρ s)
    (e : Finset α) (heV : e ⊆ F.vertices) (v : α) (hve : v ∈ e) (hδ : 0 ≤ δ)
    (hcodeg : ∀ u ∈ F.vertices, u ≠ v → F.codegree v u ≤ δ)
    (hη0 : 0 ≤ η) (hη : η ≤ 1 / 2)
    (he : |containmentMass ρ W e - survivalProduct P e| ≤ η * survivalProduct P e)
    (hU : ∀ i w, v ∈ F.edge i w → ∀ j z, v ∈ F.edge j z →
      |containmentMass ρ W (e ∪ F.edge i w ∪ F.edge j z) -
        survivalProduct P (e ∪ F.edge i w ∪ F.edge j z)| ≤
        η * survivalProduct P (e ∪ F.edge i w ∪ F.edge j z)) :
    (∑ s, conditionedStateMass ρ W e s * F.rawVertexDegree P (W s) v ^ 2) ≤
      (1 + 4 * η) * ((F.degree v / P v) ^ 2 + F.vertexSecondError P e κ δ v) := by
  have hrel := (abs_le.mp (F.rawVertexDegree_conditioned_second_relative_error
    (fun u hu => hκ0.trans_le (hP0 u hu)) ρ W hρ e heV v hη0 hη he hU)).2
  have hmain := F.pinnedGeometricSecond_le hκ0 hκ1 hP0 hP1 e heV v hve hδ hcodeg
  calc
    _ ≤ (1 + 4 * η) * F.pinnedGeometricSecond P e v := by linarith
    _ ≤ _ := mul_le_mul_of_nonneg_left hmain (by positivity)

theorem rawVertexDegree_conditioned_centered_le (F : FiniteEdgeFamily I Ω α)
    {P : α → ℝ} {κ δ η : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1)
    (hP0 : ∀ u ∈ F.vertices, κ ≤ P u) (hP1 : ∀ u ∈ F.vertices, P u ≤ 1)
    (ρ : Ξ → ℝ) (W : Ξ → Finset α) (hρ : ∀ s, 0 ≤ ρ s)
    (e : Finset α) (heV : e ⊆ F.vertices) (v : α) (hve : v ∈ e) (hδ : 0 ≤ δ)
    (hcodeg : ∀ u ∈ F.vertices, u ≠ v → F.codegree v u ≤ δ)
    (hη0 : 0 ≤ η) (hη : η ≤ 1 / 2)
    (he : |containmentMass ρ W e - survivalProduct P e| ≤ η * survivalProduct P e)
    (hU : ∀ i w, v ∈ F.edge i w → ∀ j z, v ∈ F.edge j z →
      |containmentMass ρ W (e ∪ F.edge i w ∪ F.edge j z) -
        survivalProduct P (e ∪ F.edge i w ∪ F.edge j z)| ≤
        η * survivalProduct P (e ∪ F.edge i w ∪ F.edge j z)) :
    (∑ s, conditionedStateMass ρ W e s *
      (F.rawVertexDegree P (W s) v - F.degree v / P v) ^ 2) ≤
      F.vertexVarianceError P e κ δ η v := by
  have hpos : ∀ u ∈ F.vertices, 0 < P u := fun u hu => hκ0.trans_le (hP0 u hu)
  have hq := containmentMass_pos_of_relative_error (fun u hu => hpos u (heV hu))
    (lt_of_le_of_lt hη (by norm_num)) he
  have hfirst (i : I) (w : Ω) (hvw : v ∈ F.edge i w) :
      |containmentMass ρ W (e ∪ F.edge i w) - survivalProduct P (e ∪ F.edge i w)| ≤
        η * survivalProduct P (e ∪ F.edge i w) := by
    simpa only [Finset.union_assoc, Finset.union_self] using hU i w hvw i w hvw
  have hm : |(∑ s, conditionedStateMass ρ W e s * F.rawVertexDegree P (W s) v) -
      F.degree v / P v| ≤ F.vertexMeanError P e κ δ η v := by
    exact F.rawVertexDegree_conditioned_mean_error hκ0 hκ1 hP0 hP1 ρ W hρ e heV v hve hδ
      (fun u hu => hcodeg u (heV hu)) hη0 hη he hfirst
  have hs := F.rawVertexDegree_conditioned_second_le
    hκ0 hκ1 hP0 hP1 ρ W hρ e heV v hve hδ hcodeg hη0 hη he hU
  have hcenter0 : 0 ≤ F.degree v / P v := div_nonneg (F.degree_nonneg v) (hpos v (heV hve)).le
  have hscaled := mul_le_mul_of_nonneg_left (abs_le.mp hm).1 hcenter0
  rw [finite_centered_second_moment _ _ _ (conditionedStateMass_sum_one hq)]
  unfold vertexVarianceError
  nlinarith

theorem rawVertexDegree_conditioned_tail_le (F : FiniteEdgeFamily I Ω α)
    {P : α → ℝ} {κ δ η t : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1)
    (hP0 : ∀ u ∈ F.vertices, κ ≤ P u) (hP1 : ∀ u ∈ F.vertices, P u ≤ 1)
    (ρ : Ξ → ℝ) (W : Ξ → Finset α) (hρ : ∀ s, 0 ≤ ρ s)
    (e : Finset α) (heV : e ⊆ F.vertices) (v : α) (hve : v ∈ e) (hδ : 0 ≤ δ)
    (hcodeg : ∀ u ∈ F.vertices, u ≠ v → F.codegree v u ≤ δ)
    (hη0 : 0 ≤ η) (hη : η ≤ 1 / 2) (ht : 0 < t)
    (he : |containmentMass ρ W e - survivalProduct P e| ≤ η * survivalProduct P e)
    (hU : ∀ i w, v ∈ F.edge i w → ∀ j z, v ∈ F.edge j z →
      |containmentMass ρ W (e ∪ F.edge i w ∪ F.edge j z) -
        survivalProduct P (e ∪ F.edge i w ∪ F.edge j z)| ≤
        η * survivalProduct P (e ∪ F.edge i w ∪ F.edge j z)) :
    (∑ s, if t ≤ |F.rawVertexDegree P (W s) v - F.degree v / P v|
      then conditionedStateMass ρ W e s else 0) ≤ F.vertexVarianceError P e κ δ η v / t ^ 2 := by
  have hq := containmentMass_pos_of_relative_error
    (fun u hu => hκ0.trans_le (hP0 u (heV hu))) (lt_of_le_of_lt hη (by norm_num)) he
  exact (finite_square_tail_le (conditionedStateMass ρ W e)
    (fun s => F.rawVertexDegree P (W s) v) (conditionedStateMass_nonneg hρ hq)
    (F.degree v / P v) ht).trans
    (div_le_div_of_nonneg_right
      (F.rawVertexDegree_conditioned_centered_le
        hκ0 hκ1 hP0 hP1 ρ W hρ e heV v hve hδ hcodeg hη0 hη he hU) (sq_nonneg _))

theorem rawVertexDegree_tail_from_containment (F : FiniteEdgeFamily I Ω α)
    {P : α → ℝ} {κ δ η t : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1)
    (hP0 : ∀ u ∈ F.vertices, κ ≤ P u) (hP1 : ∀ u ∈ F.vertices, P u ≤ 1)
    (ρ : Ξ → ℝ) (W : Ξ → Finset α) (hρ : ∀ s, 0 ≤ ρ s)
    (e : Finset α) (heV : e ⊆ F.vertices) (v : α) (hve : v ∈ e) (hδ : 0 ≤ δ)
    (hcodeg : ∀ u ∈ F.vertices, u ≠ v → F.codegree v u ≤ δ)
    (hη0 : 0 ≤ η) (hη : η ≤ 1 / 2) (ht : 0 < t)
    (hcor : ∀ A ⊆ F.vertices, A.card ≤ e.card + 2 * F.rank →
      |containmentMass ρ W A - survivalProduct P A| ≤ η * survivalProduct P A) :
    (∑ s, if t ≤ |F.rawVertexDegree P (W s) v - F.degree v / P v|
      then conditionedStateMass ρ W e s else 0) ≤ F.vertexVarianceError P e κ δ η v / t ^ 2 := by
  apply F.rawVertexDegree_conditioned_tail_le
    hκ0 hκ1 hP0 hP1 ρ W hρ e heV v hve hδ hcodeg hη0 hη ht
  · exact hcor e heV (Nat.le_add_right _ _)
  · intro i w _hvw j z _hvz
    apply hcor _ (Finset.union_subset (Finset.union_subset heV (F.edge_subset i w))
      (F.edge_subset j z))
    have hc1 := Finset.card_union_le e (F.edge i w)
    have hc2 := Finset.card_union_le (e ∪ F.edge i w) (F.edge j z)
    have ha := F.edge_card_le i w
    have hb := F.edge_card_le j z
    omega

end

end Erdos4b.FGKMT.FiniteEdgeFamily
