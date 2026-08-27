/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTConditionedState
import ErdosProblems.Erdos4b.FGKMTReweightedEventMass

/-! # Relative containment errors and exact event moments after conditioning -/

namespace Erdos4b.FGKMT.FiniteEdgeFamily

noncomputable section

open scoped BigOperators

variable {α Ξ : Type*} [Fintype Ξ] [DecidableEq α]

theorem conditionedState_containment_error {ρ : Ξ → ℝ} {W : Ξ → Finset α}
    {P : α → ℝ} {e A : Finset α} {η : ℝ}
    (hρ : ∀ s, 0 ≤ ρ s) (hPe : ∀ v ∈ e, 0 < P v) (hPA : ∀ v ∈ A, 0 < P v)
    (hη0 : 0 ≤ η) (hη : η ≤ 1 / 2)
    (he : |containmentMass ρ W e - survivalProduct P e| ≤ η * survivalProduct P e)
    (hU : |containmentMass ρ W (e ∪ A) - survivalProduct P (e ∪ A)| ≤
      η * survivalProduct P (e ∪ A)) :
    |containmentMass (conditionedStateMass ρ W e) W A -
      survivalProduct P (e ∪ A) / survivalProduct P e| ≤
      4 * η * (survivalProduct P (e ∪ A) / survivalProduct P e) := by
  rw [conditionedState_containment]
  have hprod : 0 < survivalProduct P (e ∪ A) := survivalProduct_pos
    (fun v hv => (Finset.mem_union.mp hv).elim (hPe v) (hPA v))
  have h := normalized_finite_sum_error ({()} : Finset Unit)
    (fun _ => containmentMass ρ W (e ∪ A)) (fun _ => containmentMass ρ W e)
    (T := survivalProduct P e) (U := survivalProduct P (e ∪ A))
    (fun _ _ => containmentMass_nonneg hρ W (e ∪ A))
    (survivalProduct_pos hPe) hprod hη0 hη (fun _ _ => he)
    (by simpa only [Finset.sum_singleton] using hU)
  simpa only [Finset.sum_singleton] using h

variable {I Ω : Type*} [Fintype I] [Fintype Ω]

theorem rawEventMass_mean (F : FiniteEdgeFamily I Ω α) (P : α → ℝ)
    (ρ : Ξ → ℝ) (W : Ξ → Finset α) (i : I) (T : Finset Ω) :
    (∑ s, ρ s * F.rawEventMass P (W s) i T) =
      ∑ w ∈ T, F.mass i w / survivalProduct P (F.edge i w) *
        containmentMass ρ W (F.edge i w) := by
  simp only [rawEventMass, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun w _hw => F.rawReweightMass_mean P ρ W i w

theorem rawEventMass_conditioned_mean (F : FiniteEdgeFamily I Ω α) (P : α → ℝ)
    (ρ : Ξ → ℝ) (W : Ξ → Finset α) (e : Finset α) (i : I) (T : Finset Ω) :
    (∑ s, conditionedStateMass ρ W e s * F.rawEventMass P (W s) i T) =
      ∑ w ∈ T, F.mass i w / survivalProduct P (F.edge i w) *
        (containmentMass ρ W (e ∪ F.edge i w) / containmentMass ρ W e) := by
  rw [F.rawEventMass_mean]
  simp only [conditionedState_containment]

theorem rawEventMass_conditioned_mean_error (F : FiniteEdgeFamily I Ω α) {P : α → ℝ}
    (hP : ∀ v ∈ F.vertices, 0 < P v) (ρ : Ξ → ℝ) (W : Ξ → Finset α)
    (hρ : ∀ s, 0 ≤ ρ s) (e : Finset α) (heV : e ⊆ F.vertices)
    {η : ℝ} (hη0 : 0 ≤ η) (hη : η ≤ 1 / 2) (i : I) (T : Finset Ω)
    (he : |containmentMass ρ W e - survivalProduct P e| ≤ η * survivalProduct P e)
    (hU : ∀ w ∈ T, |containmentMass ρ W (e ∪ F.edge i w) -
        survivalProduct P (e ∪ F.edge i w)| ≤ η * survivalProduct P (e ∪ F.edge i w)) :
    |(∑ s, conditionedStateMass ρ W e s * F.rawEventMass P (W s) i T) -
      (∑ w ∈ T, F.mass i w / survivalProduct P (F.edge i w) *
        (survivalProduct P (e ∪ F.edge i w) / survivalProduct P e))| ≤
      4 * η * (∑ w ∈ T, F.mass i w / survivalProduct P (F.edge i w) *
        (survivalProduct P (e ∪ F.edge i w) / survivalProduct P e)) := by
  rw [F.rawEventMass_mean, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ w ∈ T, |F.mass i w / survivalProduct P (F.edge i w) *
        containmentMass (conditionedStateMass ρ W e) W (F.edge i w) -
        F.mass i w / survivalProduct P (F.edge i w) *
          (survivalProduct P (e ∪ F.edge i w) / survivalProduct P e)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ w ∈ T, 4 * η * (F.mass i w / survivalProduct P (F.edge i w) *
        (survivalProduct P (e ∪ F.edge i w) / survivalProduct P e)) := by
      apply Finset.sum_le_sum
      intro w hw
      have hmass : 0 ≤ F.mass i w / survivalProduct P (F.edge i w) :=
        div_nonneg (F.mass_nonneg i w)
          (survivalProduct_pos (fun v hv => hP v (F.edge_subset i w hv))).le
      have hc := conditionedState_containment_error hρ (fun v hv => hP v (heV hv))
        (fun v hv => hP v (F.edge_subset i w hv)) hη0 hη he (hU w hw)
      rw [← mul_sub, abs_mul, abs_of_nonneg hmass]
      simpa only [mul_assoc, mul_left_comm, mul_comm] using
        mul_le_mul_of_nonneg_left hc hmass
    _ = _ := (Finset.mul_sum ..).symm

end

end Erdos4b.FGKMT.FiniteEdgeFamily
