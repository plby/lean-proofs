/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTIndependentEdgeIntersection

/-! # Codegree control of the exceptional intersections in pinned moments -/

namespace Erdos4b.FGKMT.FiniteEdgeFamily

noncomputable section

open scoped BigOperators

variable {I Ω α : Type*} [Fintype I] [Fintype Ω] [DecidableEq α]

def pinnedHitMass (F : FiniteEdgeFamily I Ω α) (i : I) (v : α) (A : Finset α) : ℝ :=
  ∑ w, if v ∈ F.edge i w ∧ (A ∩ F.edge i w).Nonempty then F.mass i w else 0

def pinnedIndependentIntersectionMass (F : FiniteEdgeFamily I Ω α) (v : α) : ℝ :=
  ∑ i, ∑ w, if v ∈ F.edge i w then
    F.mass i w * ∑ j, F.pinnedHitMass j v ((F.edge i w).erase v) else 0

theorem degree_nonneg (F : FiniteEdgeFamily I Ω α) (v : α) : 0 ≤ F.degree v :=
  Finset.sum_nonneg fun i _hi => F.vertexMass_nonneg i v

theorem pinnedHitMass_nonneg (F : FiniteEdgeFamily I Ω α) (i : I) (v : α) (A : Finset α) :
    0 ≤ F.pinnedHitMass i v A := by
  apply Finset.sum_nonneg
  intro w _hw
  split_ifs
  · exact F.mass_nonneg i w
  · exact le_rfl

theorem pinnedHitMass_le_sum_pairMass (F : FiniteEdgeFamily I Ω α)
    (i : I) (v : α) (A : Finset α) :
    F.pinnedHitMass i v A ≤ ∑ u ∈ A, F.pairMass i v u := by
  calc
    _ ≤ ∑ w, ∑ u ∈ A, if v ∈ F.edge i w ∧ u ∈ F.edge i w then F.mass i w else 0 := by
      apply Finset.sum_le_sum
      intro w _hw
      have hnonneg (u : α) :
          0 ≤ (if v ∈ F.edge i w ∧ u ∈ F.edge i w then F.mass i w else 0) := by
        split_ifs
        · exact F.mass_nonneg i w
        · exact le_rfl
      by_cases h : v ∈ F.edge i w ∧ (A ∩ F.edge i w).Nonempty
      · rw [if_pos h]
        obtain ⟨u, hu⟩ := h.2
        have huA := (Finset.mem_inter.mp hu).1
        have huE := (Finset.mem_inter.mp hu).2
        have hle := Finset.single_le_sum (s := A) (a := u)
          (f := fun u : α => if v ∈ F.edge i w ∧ u ∈ F.edge i w then F.mass i w else 0)
          (fun u _hu => hnonneg u) huA
        have hvu : v ∈ F.edge i w ∧ u ∈ F.edge i w := ⟨h.1, huE⟩
        simpa only [if_pos hvu] using hle
      · rw [if_neg h]
        exact Finset.sum_nonneg fun u _hu => hnonneg u
    _ = _ := Finset.sum_comm

theorem pinnedHitMass_sum_le_codegree (F : FiniteEdgeFamily I Ω α)
    (v : α) (A : Finset α) : (∑ i, F.pinnedHitMass i v A) ≤ ∑ u ∈ A, F.codegree v u := by
  calc
    _ ≤ ∑ i, ∑ u ∈ A, F.pairMass i v u :=
      Finset.sum_le_sum fun i _hi => F.pinnedHitMass_le_sum_pairMass i v A
    _ = _ := Finset.sum_comm

theorem pinnedHitMass_sum_le_card_mul (F : FiniteEdgeFamily I Ω α)
    (v : α) (A : Finset α) {δ : ℝ} (hcap : ∀ u ∈ A, F.codegree v u ≤ δ) :
    (∑ i, F.pinnedHitMass i v A) ≤ (A.card : ℝ) * δ := by
  calc
    _ ≤ ∑ u ∈ A, F.codegree v u := F.pinnedHitMass_sum_le_codegree v A
    _ ≤ ∑ _u ∈ A, δ := Finset.sum_le_sum hcap
    _ = _ := by simp

theorem pinnedIndependentIntersectionMass_eq (F : FiniteEdgeFamily I Ω α) (v : α) :
    F.pinnedIndependentIntersectionMass v = ∑ i, ∑ w, ∑ j, ∑ z,
      if v ∈ F.edge i w ∧ v ∈ F.edge j z ∧
          ((F.edge i w).erase v ∩ F.edge j z).Nonempty
      then F.mass i w * F.mass j z else 0 := by
  unfold pinnedIndependentIntersectionMass
  apply Finset.sum_congr rfl
  intro i _hi
  apply Finset.sum_congr rfl
  intro w _hw
  by_cases hv : v ∈ F.edge i w
  · simp only [pinnedHitMass, Finset.mul_sum, mul_ite, mul_zero, hv, true_and, if_true]
  · simp only [hv, false_and, if_false, Finset.sum_const_zero]

theorem pinnedIndependentIntersectionMass_le (F : FiniteEdgeFamily I Ω α)
    (v : α) {δ : ℝ} (hδ : 0 ≤ δ)
    (hcap : ∀ u ∈ F.vertices, u ≠ v → F.codegree v u ≤ δ) :
    F.pinnedIndependentIntersectionMass v ≤ ((F.rank : ℝ) * δ) * F.degree v := by
  have hhit (i : I) (w : Ω) :
      (∑ j, F.pinnedHitMass j v ((F.edge i w).erase v)) ≤ (F.rank : ℝ) * δ := by
    calc
      _ ≤ (((F.edge i w).erase v).card : ℝ) * δ :=
        F.pinnedHitMass_sum_le_card_mul v ((F.edge i w).erase v)
          (fun u hu => hcap u (F.edge_subset i w (Finset.mem_erase.mp hu).2)
            (Finset.mem_erase.mp hu).1)
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (by exact_mod_cast (Finset.card_erase_le).trans (F.edge_card_le i w)) hδ
  calc
    _ ≤ ∑ i, ∑ w, if v ∈ F.edge i w then
        F.mass i w * ((F.rank : ℝ) * δ) else 0 := by
      apply Finset.sum_le_sum
      intro i _hi
      apply Finset.sum_le_sum
      intro w _hw
      by_cases hv : v ∈ F.edge i w
      · rw [if_pos hv, if_pos hv]
        exact mul_le_mul_of_nonneg_left (hhit i w) (F.mass_nonneg i w)
      · rw [if_neg hv, if_neg hv]
    _ = _ := by
      simp only [degree, vertexMass, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _hi
      apply Finset.sum_congr rfl
      intro w _hw
      split_ifs <;> ring

theorem pinned_test_intersection_le (F : FiniteEdgeFamily I Ω α)
    (v : α) (e : Finset α) {δ : ℝ} (hδ : 0 ≤ δ)
    (hcap : ∀ u ∈ e, u ≠ v → F.codegree v u ≤ δ) :
    F.degree v * (∑ i, F.pinnedHitMass i v (e.erase v)) ≤
      F.degree v * ((e.card : ℝ) * δ) := by
  apply mul_le_mul_of_nonneg_left _ (F.degree_nonneg v)
  calc
    _ ≤ ((e.erase v).card : ℝ) * δ := F.pinnedHitMass_sum_le_card_mul v (e.erase v)
      (fun u hu => hcap u (Finset.mem_erase.mp hu).2 (Finset.mem_erase.mp hu).1)
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast Finset.card_erase_le) hδ

end

end Erdos4b.FGKMT.FiniteEdgeFamily
