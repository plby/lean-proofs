import ErdosProblems.Erdos745.EdgeLaw
import Mathlib.Combinatorics.SetFamily.FourFunctions

/-!
# Harris correlation for the finite independent-edge graph law

Mathlib's FKG theorem is applied to the exact finite Bernoulli weights.
The weight is modular, so the lattice hypothesis holds with equality.
-/

open scoped BigOperators

namespace Erdos745

noncomputable section

attribute [local instance] Classical.propDecidable

namespace FiniteHarris

open Erdos746.BernoulliFinset

variable {α : Type*} [Fintype α] [DecidableEq α]

theorem powerset_univ : (Finset.univ : Finset α).powerset = Finset.univ := by
  ext A
  simp only [Finset.mem_powerset, Finset.mem_univ, iff_true]
  exact Finset.subset_univ A

theorem weight_modular (p : ℝ) (A B : Finset α) :
    weight Finset.univ p A * weight Finset.univ p B =
      weight Finset.univ p (A ∩ B) * weight Finset.univ p (A ∪ B) := by
  have hcard := Finset.card_union_add_card_inter A B
  have hA := Finset.card_le_univ A
  have hB := Finset.card_le_univ B
  have hI := Finset.card_le_univ (A ∩ B)
  have hU := Finset.card_le_univ (A ∪ B)
  have hpres : A.card + B.card = (A ∩ B).card + (A ∪ B).card := by omega
  have habs : (Fintype.card α - A.card) + (Fintype.card α - B.card) =
      (Fintype.card α - (A ∩ B).card) + (Fintype.card α - (A ∪ B).card) := by omega
  simp only [weight, Finset.card_univ]
  calc
    _ = p ^ (A.card + B.card) *
        (1 - p) ^ ((Fintype.card α - A.card) + (Fintype.card α - B.card)) := by
      rw [pow_add, pow_add]
      ring
    _ = p ^ ((A ∩ B).card + (A ∪ B).card) *
        (1 - p) ^ ((Fintype.card α - (A ∩ B).card) + (Fintype.card α - (A ∪ B).card)) := by
      rw [hpres, habs]
    _ = _ := by rw [pow_add, pow_add]; ring

theorem sum_weight_univ (p : ℝ) :
    (∑ A : Finset α, weight Finset.univ p A) = 1 := by
  simpa only [powerset_univ] using sum_weight_powerset (Finset.univ : Finset α) p

theorem sum_indicator (p : ℝ) (P : Finset α → Prop) :
    (∑ A : Finset α, weight Finset.univ p A * (if P A then 1 else 0)) =
      eventMass Finset.univ p P := by
  simp only [eventMass, powerset_univ, Finset.sum_filter, mul_ite, mul_one, mul_zero]

/-- A lower event is preserved when present coordinates are removed. -/
def LowerEvent (P : Finset α → Prop) : Prop := ∀ ⦃A B⦄, A ⊆ B → P B → P A

theorem lower_indicator_monotone {P : Finset α → Prop} (hP : LowerEvent P) :
    Monotone (fun A : OrderDual (Finset α) ↦ if P A then (1 : ℝ) else 0) := by
  intro A B hAB
  by_cases hPA : P A
  · have hPB := hP hAB hPA
    simp only [if_pos hPA, if_pos hPB, le_refl]
  · simp only [if_neg hPA]
    split_ifs <;> norm_num

theorem eventMass_lower_inter {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (P Q : Finset α → Prop) (hP : LowerEvent P) (hQ : LowerEvent Q) :
    eventMass Finset.univ p P * eventMass Finset.univ p Q ≤
      eventMass Finset.univ p (fun A ↦ P A ∧ Q A) := by
  let w := fun A : Finset α ↦ weight Finset.univ p A
  let f := fun A : Finset α ↦ if P A then w A else 0
  let g := fun A : Finset α ↦ if Q A then w A else 0
  let t := fun A : Finset α ↦ if P A ∧ Q A then w A else 0
  have hw : 0 ≤ w := fun _ ↦ weight_nonneg hp hp1
  have hf : 0 ≤ f := by intro A; dsimp [f]; split_ifs; exact hw A; exact le_rfl
  have hg : 0 ≤ g := by intro A; dsimp [g]; split_ifs; exact hw A; exact le_rfl
  have ht : 0 ≤ t := by intro A; dsimp [t]; split_ifs; exact hw A; exact le_rfl
  have hmod : ∀ A B, f A * g B ≤ t (A ⊓ B) * w (A ⊔ B) := by
    intro A B
    by_cases hPA : P A
    · by_cases hQB : Q B
      · have hPI : P (A ∩ B) := hP Finset.inter_subset_left hPA
        have hQI : Q (A ∩ B) := hQ Finset.inter_subset_right hQB
        change (if P A then w A else 0) * (if Q B then w B else 0) ≤
          (if P (A ∩ B) ∧ Q (A ∩ B) then w (A ∩ B) else 0) * w (A ∪ B)
        rw [if_pos hPA, if_pos hQB, if_pos ⟨hPI, hQI⟩]
        exact le_of_eq (weight_modular p A B)
      · change f A * (if Q B then w B else 0) ≤ _
        rw [if_neg hQB, mul_zero]
        exact mul_nonneg (ht _) (hw _)
    · change (if P A then w A else 0) * g B ≤ _
      rw [if_neg hPA, zero_mul]
      exact mul_nonneg (ht _) (hw _)
  have h := four_functions_theorem_univ f g t w hf hg ht hw hmod
  have htSum : (∑ A, t A) = eventMass Finset.univ p (fun A ↦ P A ∧ Q A) := by
    simp only [t, w, eventMass, powerset_univ, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro A _
    by_cases hA : P A ∧ Q A <;> simp only [hA, if_true, if_false]
  rw [htSum, show (∑ A, w A) = 1 from sum_weight_univ p, mul_one] at h
  simpa only [f, g, w, eventMass, powerset_univ, Finset.sum_filter] using h

end FiniteHarris

/-- Decreasing graph events positively correlate in the exact `G(n,p)` law. -/
theorem probability_lower_inter (lam : ℝ) (n : ℕ)
    (P Q : SimpleGraph (Fin n) → Prop)
    (hP : ∀ ⦃G H⦄, G ≤ H → P H → P G)
    (hQ : ∀ ⦃G H⦄, G ≤ H → Q H → Q G) :
    probability lam n P * probability lam n Q ≤ probability lam n (fun G ↦ P G ∧ Q G) := by
  rw [probability_eq_edgeEventMass, probability_eq_edgeEventMass, probability_eq_edgeEventMass]
  apply FiniteHarris.eventMass_lower_inter (edgeProbability lam n).property.1
    (edgeProbability lam n).property.2
  · intro A B hAB hB
    exact hP (Erdos746.graphOfEdges_mono hAB) hB
  · intro A B hAB hB
    exact hQ (Erdos746.graphOfEdges_mono hAB) hB

theorem probability_lower_forall {ι : Type*} [DecidableEq ι]
    (lam : ℝ) (n : ℕ) (I : Finset ι) (P : ι → SimpleGraph (Fin n) → Prop)
    (hP : ∀ i ∈ I, ∀ ⦃G H⦄, G ≤ H → P i H → P i G) :
    (∏ i ∈ I, probability lam n (P i)) ≤ probability lam n (fun G ↦ ∀ i ∈ I, P i G) := by
  induction I using Finset.induction with
  | empty => simp
  | @insert i I hi ih =>
    have hI := ih (fun j hj ↦ hP j (Finset.mem_insert_of_mem hj))
    have hiLower := hP i (Finset.mem_insert_self _ _)
    have hILower : ∀ ⦃G H⦄, G ≤ H → (∀ j ∈ I, P j H) → ∀ j ∈ I, P j G := by
      intro G H hGH hAll j hj
      exact hP j (Finset.mem_insert_of_mem hj) hGH (hAll j hj)
    rw [Finset.prod_insert hi]
    have hevent : (fun G ↦ ∀ j ∈ insert i I, P j G) =
        (fun G ↦ P i G ∧ ∀ j ∈ I, P j G) := by
      funext G
      simp only [Finset.forall_mem_insert]
    rw [hevent]
    exact (mul_le_mul_of_nonneg_left hI (probability_nonneg _ _ _)).trans
      (probability_lower_inter lam n _ _ hiLower hILower)

end

end Erdos745
