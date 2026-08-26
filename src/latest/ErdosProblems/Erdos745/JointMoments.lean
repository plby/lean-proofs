import ErdosProblems.Erdos745.BernoulliUnion

/-! # Finite moments in the independent two-stage Bernoulli coupling -/

open scoped BigOperators

namespace Erdos745.BernoulliUnion

noncomputable section

attribute [local instance] Classical.propDecidable

open Erdos746.BernoulliFinset

variable {α : Type*} [DecidableEq α]

def subsetExpectation (U : Finset α) (p : ℝ) (f : Finset α → ℝ) : ℝ :=
  ∑ A ∈ U.powerset, weight U p A * f A

def jointExpectation (U : Finset α) (p q : ℝ) (f : Finset α → Finset α → ℝ) : ℝ :=
  ∑ A ∈ U.powerset, ∑ B ∈ U.powerset, weight U p A * weight U q B * f A B

theorem jointExpectation_congr_on (U : Finset α) (p q : ℝ)
    (f g : Finset α → Finset α → ℝ) (h : ∀ A ⊆ U, ∀ B ⊆ U, f A B = g A B) :
    jointExpectation U p q f = jointExpectation U p q g := by
  apply Finset.sum_congr rfl
  intro A hA
  apply Finset.sum_congr rfl
  intro B hB
  rw [h A (Finset.mem_powerset.mp hA) B (Finset.mem_powerset.mp hB)]

theorem jointExpectation_const_mul (U : Finset α) (p q c : ℝ)
    (f : Finset α → Finset α → ℝ) :
    jointExpectation U p q (fun A B ↦ c * f A B) = c * jointExpectation U p q f := by
  simp only [jointExpectation, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro A _
  apply Finset.sum_congr rfl
  intro B _
  ring

theorem jointExpectation_sub (U : Finset α) (p q : ℝ)
    (f g : Finset α → Finset α → ℝ) :
    jointExpectation U p q (fun A B ↦ f A B - g A B) =
      jointExpectation U p q f - jointExpectation U p q g := by
  simp only [jointExpectation, mul_sub, Finset.sum_sub_distrib]

theorem jointExpectation_sum {ι : Type*} (U : Finset α) (p q : ℝ) (I : Finset ι)
    (f : ι → Finset α → Finset α → ℝ) :
    jointExpectation U p q (fun A B ↦ ∑ i ∈ I, f i A B) =
      ∑ i ∈ I, jointExpectation U p q (f i) := by
  simp only [jointExpectation, Finset.mul_sum]
  calc
    _ = ∑ A ∈ U.powerset, ∑ i ∈ I, ∑ B ∈ U.powerset,
        weight U p A * weight U q B * f i A B := by
      apply Finset.sum_congr rfl
      intro A _
      exact Finset.sum_comm
    _ = _ := Finset.sum_comm

theorem jointExpectation_indicator (U : Finset α) (p q : ℝ)
    (P : Finset α → Finset α → Prop) :
    jointExpectation U p q (fun A B ↦ if P A B then 1 else 0) = jointMass U p q P := by
  simp only [jointExpectation, jointMass, eventMass, Finset.sum_filter,
    Finset.mul_sum, mul_ite, mul_one, mul_zero]

theorem jointExpectation_first (U : Finset α) (p q : ℝ) (f : Finset α → ℝ) :
    jointExpectation U p q (fun A _B ↦ f A) = subsetExpectation U p f := by
  apply Finset.sum_congr rfl
  intro A _
  calc
    _ = ∑ B ∈ U.powerset, (weight U p A * f A) * weight U q B := by
      apply Finset.sum_congr rfl
      intro B _
      ring
    _ = _ := by rw [← Finset.mul_sum, sum_weight_powerset, mul_one]

theorem jointExpectation_union (U : Finset α) (p q : ℝ) (f : Finset α → ℝ) :
    jointExpectation U p q (fun A B ↦ f (A ∪ B)) =
      subsetExpectation U (p + (1 - p) * q) f := by
  have heq : jointExpectation U p q (fun A B ↦ f (A ∪ B)) =
      jointExpectation U p q (fun A B ↦ ∑ C ∈ U.powerset,
        f C * (if A ∪ B = C then 1 else 0)) := by
    apply jointExpectation_congr_on
    intro A hA B hB
    rw [Finset.sum_eq_single (A ∪ B)]
    · simp
    · intro C _ hC
      simp only [if_neg hC.symm, mul_zero]
    · intro hnot
      exact False.elim (hnot (Finset.mem_powerset.mpr (Finset.union_subset hA hB)))
  rw [heq, jointExpectation_sum]
  simp only [jointExpectation_const_mul]
  apply Finset.sum_congr rfl
  intro C hC
  have hind : jointExpectation U p q (fun A B ↦ if A ∪ B = C then 1 else 0) =
      jointMass U p q (fun A B ↦ A ∪ B = C) := by
    convert! jointExpectation_indicator U p q (fun A B ↦ A ∪ B = C) using 1
    apply jointExpectation_congr_on
    intro A _ B _
    by_cases h : A ∪ B = C <;> simp only [h, if_true, if_false]
  rw [hind, jointMass_union_eq (Finset.mem_powerset.mp hC)]
  exact mul_comm _ _

theorem jointExpectation_mono {U : Finset α} {p q : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    {f g : Finset α → Finset α → ℝ} (h : ∀ A ⊆ U, ∀ B ⊆ U, f A B ≤ g A B) :
    jointExpectation U p q f ≤ jointExpectation U p q g := by
  apply Finset.sum_le_sum
  intro A hA
  apply Finset.sum_le_sum
  intro B hB
  exact mul_le_mul_of_nonneg_left
    (h A (Finset.mem_powerset.mp hA) B (Finset.mem_powerset.mp hB))
    (mul_nonneg (weight_nonneg hp0 hp1) (weight_nonneg hq0 hq1))

theorem jointMass_markov {U : Finset α} {p q t : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (ht : 0 < t)
    (f : Finset α → Finset α → ℝ) (hf : ∀ A ⊆ U, ∀ B ⊆ U, 0 ≤ f A B) :
    jointMass U p q (fun A B ↦ t ≤ f A B) ≤ jointExpectation U p q f / t := by
  have h : jointExpectation U p q (fun A B ↦ t * (if t ≤ f A B then 1 else 0)) ≤
      jointExpectation U p q f := by
    apply jointExpectation_mono hp0 hp1 hq0 hq1
    intro A hA B hB
    by_cases htf : t ≤ f A B
    · simpa only [if_pos htf, mul_one] using htf
    · simpa only [if_neg htf, mul_zero] using hf A hA B hB
  rw [jointExpectation_const_mul, jointExpectation_indicator] at h
  apply (le_div_iff₀ ht).mpr
  simpa only [mul_comm] using h

theorem jointMass_first (U : Finset α) (p q : ℝ) (P : Finset α → Prop) :
    jointMass U p q (fun A _B ↦ P A) = eventMass U p P := by
  unfold jointMass eventMass
  simp only [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro A _
  by_cases hP : P A
  · simp only [hP, if_true, sum_weight_powerset, mul_one]
  · simp only [hP, if_false, Finset.sum_const_zero, mul_zero]

theorem jointMass_mono {U : Finset α} {p q : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    {P Q : Finset α → Finset α → Prop} (h : ∀ A B, P A B → Q A B) :
    jointMass U p q P ≤ jointMass U p q Q := by
  apply Finset.sum_le_sum
  intro A _
  exact mul_le_mul_of_nonneg_left (eventMass_mono U hq0 hq1 _ _ (h A))
    (weight_nonneg hp0 hp1)

theorem jointMass_or_le {U : Finset α} {p q : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (P Q : Finset α → Finset α → Prop) :
    jointMass U p q (fun A B ↦ P A B ∨ Q A B) ≤ jointMass U p q P + jointMass U p q Q := by
  unfold jointMass
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro A _
  have h := mul_le_mul_of_nonneg_left (eventMass_or_le U hq0 hq1 (P A) (Q A))
    (weight_nonneg hp0 hp1 (U := U) (A := A))
  simpa only [mul_add] using h

theorem jointMass_le_of_rows {U : Finset α} {p q c : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (P : Finset α → Finset α → Prop)
    (h : ∀ A ⊆ U, eventMass U q (P A) ≤ c) : jointMass U p q P ≤ c := by
  calc
    _ ≤ ∑ A ∈ U.powerset, weight U p A * c :=
      Finset.sum_le_sum (fun A hA ↦ mul_le_mul_of_nonneg_left
        (h A (Finset.mem_powerset.mp hA)) (weight_nonneg hp0 hp1))
    _ = _ := by rw [← Finset.sum_mul, sum_weight_powerset, one_mul]

end

end Erdos745.BernoulliUnion
