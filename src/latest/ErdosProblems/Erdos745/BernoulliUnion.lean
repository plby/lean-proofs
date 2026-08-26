import ErdosProblems.Erdos746.BernoulliFinset

/-! # Exact superposition of two finite Bernoulli edge sets -/

open scoped BigOperators

namespace Erdos745.BernoulliUnion

noncomputable section

attribute [local instance] Classical.propDecidable

open Erdos746.BernoulliFinset

variable {α : Type*} [DecidableEq α]

theorem eventMass_congr_on (U : Finset α) (p : ℝ) (P Q : Finset α → Prop)
    (hPQ : ∀ A ⊆ U, P A ↔ Q A) : eventMass U p P = eventMass U p Q := by
  unfold eventMass
  have hsets : U.powerset.filter P = U.powerset.filter Q := by
    ext A
    simp only [Finset.mem_filter, Finset.mem_powerset]
    exact and_congr_right (fun hA ↦ hPQ A hA)
  rw [hsets]

theorem sum_powerset_powers (U : Finset α) (a b : ℝ) :
    (∑ A ∈ U.powerset, a ^ A.card * b ^ (U.card - A.card)) = (a + b) ^ U.card := by
  calc
    _ = ∑ A ∈ U.powerset, (∏ _i ∈ A, a) * ∏ _i ∈ U \ A, b := by
      apply Finset.sum_congr rfl
      intro A hA
      rw [Finset.prod_const, Finset.prod_const,
        Finset.card_sdiff_of_subset (Finset.mem_powerset.mp hA)]
    _ = ∏ _i ∈ U, (a + b) := (Finset.prod_add _ _ _).symm
    _ = _ := Finset.prod_const _

theorem union_eq_iff_cylinder {U A B C : Finset α} (hAC : A ⊆ C) (hBU : B ⊆ U) :
    A ∪ B = C ↔ C \ A ⊆ B ∧ Disjoint (U \ C) B := by
  constructor
  · intro h
    constructor
    · intro x hx
      have hxC := (Finset.mem_sdiff.mp hx).1
      rw [← h, Finset.mem_union] at hxC
      exact hxC.resolve_left (Finset.mem_sdiff.mp hx).2
    · rw [Finset.disjoint_left]
      intro x hx hxB
      exact (Finset.mem_sdiff.mp hx).2 (h ▸ Finset.mem_union_right A hxB)
  · rintro ⟨hcover, hdis⟩
    apply Finset.Subset.antisymm
    · intro x hx
      rcases Finset.mem_union.mp hx with hxA | hxB
      · exact hAC hxA
      · by_contra hxC
        exact Finset.disjoint_left.mp hdis (Finset.mem_sdiff.mpr ⟨hBU hxB, hxC⟩) hxB
    · intro x hxC
      by_cases hxA : x ∈ A
      · exact Finset.mem_union_left B hxA
      · exact Finset.mem_union_right A (hcover (Finset.mem_sdiff.mpr ⟨hxC, hxA⟩))

theorem eventMass_union_eq {U A C : Finset α} (hCU : C ⊆ U) (q : ℝ) :
    eventMass U q (fun B ↦ A ∪ B = C) =
      if A ⊆ C then q ^ (C \ A).card * (1 - q) ^ (U \ C).card else 0 := by
  by_cases hAC : A ⊆ C
  · rw [if_pos hAC]
    have hpres : C \ A ⊆ U := Finset.sdiff_subset.trans hCU
    have habs : U \ C ⊆ U := Finset.sdiff_subset
    have hdis : Disjoint (C \ A) (U \ C) := by
      rw [Finset.disjoint_left]
      intro x hx hx'
      exact (Finset.mem_sdiff.mp hx').2 (Finset.mem_sdiff.mp hx).1
    rw [eventMass_congr_on U q _ _ (fun B hB ↦ union_eq_iff_cylinder hAC hB)]
    exact eventMass_contains_disjoint hpres habs hdis q
  · rw [if_neg hAC]
    have hevent : (fun B ↦ A ∪ B = C) = (fun _ ↦ False) := by
      funext B
      apply propext
      exact ⟨fun h ↦ hAC (h ▸ Finset.subset_union_left), False.elim⟩
    rw [hevent, eventMass_false]

/-- Iterated probability in a product of two independent Bernoulli subset spaces. -/
def jointMass (U : Finset α) (p q : ℝ) (P : Finset α → Finset α → Prop) : ℝ :=
  ∑ A ∈ U.powerset, weight U p A * eventMass U q (P A)

theorem jointMass_union_eq {U C : Finset α} (hCU : C ⊆ U) (p q : ℝ) :
    jointMass U p q (fun A B ↦ A ∪ B = C) = weight U (p + (1 - p) * q) C := by
  unfold jointMass
  simp only [eventMass_union_eq hCU q, mul_ite, mul_zero]
  rw [← Finset.sum_filter]
  have hfilter : U.powerset.filter (fun A ↦ A ⊆ C) = C.powerset := by
    ext A
    simp only [Finset.mem_filter, Finset.mem_powerset]
    exact ⟨And.right, fun hA ↦ ⟨hA.trans hCU, hA⟩⟩
  rw [hfilter]
  have hCcard := Finset.card_le_card hCU
  calc
    _ = ∑ A ∈ C.powerset, ((1 - p) * (1 - q)) ^ (U.card - C.card) *
        (p ^ A.card * ((1 - p) * q) ^ (C.card - A.card)) := by
      apply Finset.sum_congr rfl
      intro A hA
      have hAC := Finset.mem_powerset.mp hA
      have hAcard := Finset.card_le_card hAC
      have hsub : U.card - A.card = (U.card - C.card) + (C.card - A.card) := by omega
      rw [weight, Finset.card_sdiff_of_subset hAC, Finset.card_sdiff_of_subset hCU,
        hsub, pow_add, mul_pow, mul_pow]
      ring
    _ = ((1 - p) * (1 - q)) ^ (U.card - C.card) *
        (p + (1 - p) * q) ^ C.card := by
      rw [← Finset.mul_sum, sum_powerset_powers]
    _ = _ := by
      unfold weight
      rw [show 1 - (p + (1 - p) * q) = (1 - p) * (1 - q) by ring]
      ring

/-- The union has the Bernoulli law with success probability `p + (1-p)q`,
for every event, not only for prescribed edge sets. -/
theorem jointMass_union_event (U : Finset α) (p q : ℝ) (P : Finset α → Prop) :
    jointMass U p q (fun A B ↦ P (A ∪ B)) = eventMass U (p + (1 - p) * q) P := by
  let I := U.powerset.filter P
  have hrow (A : Finset α) (hAU : A ⊆ U) :
      eventMass U q (fun B ↦ P (A ∪ B)) =
        ∑ C ∈ I, eventMass U q (fun B ↦ A ∪ B = C) := by
    rw [← eventMass_classifier_mem U q (fun B ↦ A ∪ B) I]
    apply eventMass_congr_on
    intro B hBU
    simp only [I, Finset.mem_filter, Finset.mem_powerset]
    exact ⟨fun h ↦ ⟨Finset.union_subset hAU hBU, h⟩, And.right⟩
  unfold jointMass
  calc
    _ = ∑ A ∈ U.powerset, weight U p A *
        ∑ C ∈ I, eventMass U q (fun B ↦ A ∪ B = C) := by
      apply Finset.sum_congr rfl
      intro A hA
      rw [hrow A (Finset.mem_powerset.mp hA)]
    _ = ∑ C ∈ I, jointMass U p q (fun A B ↦ A ∪ B = C) := by
      simp only [Finset.mul_sum, jointMass]
      exact Finset.sum_comm
    _ = ∑ C ∈ I, weight U (p + (1 - p) * q) C := by
      apply Finset.sum_congr rfl
      intro C hC
      exact jointMass_union_eq (Finset.mem_powerset.mp (Finset.mem_filter.mp hC).1) p q
    _ = _ := rfl

end

end Erdos745.BernoulliUnion
