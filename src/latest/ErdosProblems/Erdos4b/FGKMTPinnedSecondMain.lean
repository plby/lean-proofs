/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTConditionedVertexSquare

/-! # The geometric pinned second main term differs little from squared degree -/

namespace Erdos4b.FGKMT.FiniteEdgeFamily

noncomputable section

variable {I Ω α : Type*} [Fintype I] [Fintype Ω] [DecidableEq α]

def vertexSecondError (F : FiniteEdgeFamily I Ω α) (P : α → ℝ)
    (e : Finset α) (κ δ : ℝ) (v : α) : ℝ :=
  (1 / P v ^ 2) * (1 / κ ^ (2 * F.rank)) *
    ((2 * (e.card : ℝ) + F.rank) * δ * F.degree v)

theorem pinnedGeometricSecond_eq_scaled (F : FiniteEdgeFamily I Ω α)
    (P : α → ℝ) (e : Finset α) (v : α) (hv : 0 < P v) :
    F.pinnedGeometricSecond P e v =
      (1 / P v ^ 2) * F.pinnedPairAverage v (fun A B => pinnedTripleRatio P e A B v) := by
  rw [← F.pinnedPairAverage_const_mul]
  unfold pinnedGeometricSecond
  congr 1
  funext A B
  unfold pinnedTripleRatio
  field_simp [hv.ne']

theorem pinnedTripleAverage_error (F : FiniteEdgeFamily I Ω α)
    {P : α → ℝ} {κ δ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1)
    (hP0 : ∀ u ∈ F.vertices, κ ≤ P u) (hP1 : ∀ u ∈ F.vertices, P u ≤ 1)
    (e : Finset α) (heV : e ⊆ F.vertices) (v : α) (hve : v ∈ e) (hδ : 0 ≤ δ)
    (hcodeg : ∀ u ∈ F.vertices, u ≠ v → F.codegree v u ≤ δ) :
    |F.pinnedPairAverage v (fun A B => pinnedTripleRatio P e A B v) - F.degree v ^ 2| ≤
      (1 / κ ^ (2 * F.rank)) * ((2 * (e.card : ℝ) + F.rank) * δ * F.degree v) := by
  have hconst : F.pinnedPairAverage v (fun _ _ => 1) = F.degree v ^ 2 := by
    rw [F.pinnedPairAverage_const, mul_one]
  calc
    _ = |F.pinnedPairAverage v (fun A B => pinnedTripleRatio P e A B v - 1)| := by
      rw [F.pinnedPairAverage_sub, hconst]
    _ ≤ F.pinnedPairAverage v (fun A B => |pinnedTripleRatio P e A B v - 1|) :=
      F.pinnedPairAverage_abs_le v _
    _ ≤ F.pinnedPairAverage v (fun A B =>
        (1 / κ ^ (2 * F.rank)) * tripleExtraIndicator e A B v) := by
      apply F.pinnedPairAverage_mono
      intro i w hvw j z hvz
      exact pinnedTripleRatio_error hκ0 hκ1 hP0 hP1 heV (F.edge_subset i w) (F.edge_subset j z)
        (F.edge_card_le i w) (F.edge_card_le j z) hve hvw hvz
    _ = (1 / κ ^ (2 * F.rank)) *
        F.pinnedPairAverage v (fun A B => tripleExtraIndicator e A B v) :=
      F.pinnedPairAverage_const_mul v _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (F.pinnedPairAverage_tripleExtra_le e heV v hδ hcodeg) (by positivity)

theorem pinnedGeometricSecond_error (F : FiniteEdgeFamily I Ω α)
    {P : α → ℝ} {κ δ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1)
    (hP0 : ∀ u ∈ F.vertices, κ ≤ P u) (hP1 : ∀ u ∈ F.vertices, P u ≤ 1)
    (e : Finset α) (heV : e ⊆ F.vertices) (v : α) (hve : v ∈ e) (hδ : 0 ≤ δ)
    (hcodeg : ∀ u ∈ F.vertices, u ≠ v → F.codegree v u ≤ δ) :
    |F.pinnedGeometricSecond P e v - (F.degree v / P v) ^ 2| ≤
      F.vertexSecondError P e κ δ v := by
  have hv : 0 < P v := hκ0.trans_le (hP0 v (heV hve))
  have hbase : (F.degree v / P v) ^ 2 = (1 / P v ^ 2) * F.degree v ^ 2 := by ring
  rw [F.pinnedGeometricSecond_eq_scaled P e v hv, hbase, ← mul_sub,
    abs_mul, abs_of_nonneg (by positivity : 0 ≤ 1 / P v ^ 2)]
  have h := mul_le_mul_of_nonneg_left
    (F.pinnedTripleAverage_error hκ0 hκ1 hP0 hP1 e heV v hve hδ hcodeg)
    (by positivity : 0 ≤ 1 / P v ^ 2)
  simpa only [vertexSecondError, mul_assoc] using h

theorem pinnedGeometricSecond_lower (F : FiniteEdgeFamily I Ω α)
    {P : α → ℝ} {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1)
    (hP0 : ∀ u ∈ F.vertices, κ ≤ P u) (hP1 : ∀ u ∈ F.vertices, P u ≤ 1)
    (e : Finset α) (heV : e ⊆ F.vertices) (v : α) (hve : v ∈ e) :
    (F.degree v / P v) ^ 2 ≤ F.pinnedGeometricSecond P e v := by
  have hv : 0 < P v := hκ0.trans_le (hP0 v (heV hve))
  have hmono : F.pinnedPairAverage v (fun _ _ => 1) ≤
      F.pinnedPairAverage v (fun A B => pinnedTripleRatio P e A B v) := by
    apply F.pinnedPairAverage_mono
    intro i w hvw j z hvz
    exact (pinnedTripleRatio_bounds hκ0 hκ1 hP0 hP1 heV (F.edge_subset i w) (F.edge_subset j z)
      (F.edge_card_le i w) (F.edge_card_le j z) hve hvw hvz).1
  rw [F.pinnedPairAverage_const, mul_one] at hmono
  rw [F.pinnedGeometricSecond_eq_scaled P e v hv]
  calc
    _ = (1 / P v ^ 2) * F.degree v ^ 2 := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hmono (by positivity)

theorem pinnedGeometricSecond_le (F : FiniteEdgeFamily I Ω α)
    {P : α → ℝ} {κ δ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1)
    (hP0 : ∀ u ∈ F.vertices, κ ≤ P u) (hP1 : ∀ u ∈ F.vertices, P u ≤ 1)
    (e : Finset α) (heV : e ⊆ F.vertices) (v : α) (hve : v ∈ e) (hδ : 0 ≤ δ)
    (hcodeg : ∀ u ∈ F.vertices, u ≠ v → F.codegree v u ≤ δ) :
    F.pinnedGeometricSecond P e v ≤ (F.degree v / P v) ^ 2 + F.vertexSecondError P e κ δ v := by
  have h := (abs_le.mp (F.pinnedGeometricSecond_error hκ0 hκ1 hP0 hP1 e heV v hve hδ hcodeg)).2
  linarith

end

end Erdos4b.FGKMT.FiniteEdgeFamily
