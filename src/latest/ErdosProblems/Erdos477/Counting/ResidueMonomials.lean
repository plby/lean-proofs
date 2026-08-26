/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Monomial weight bounds for several residue classes in the determinant method.
Formal author: Codex.
-/

import ErdosProblems.Erdos477.Counting.Monomials

namespace Erdos477.Counting

open scoped BigOperators

variable {κ : Type*} [Fintype κ]

/-- Distinct residue classes supply separate copies of the two-variable
monomials. Their total possible deficit is the number of classes times the
deficit for one class. -/
lemma sum_labeled_deficit_le (S : Finset (κ × (ℕ × ℕ))) (m : ℕ) :
    ∑ e ∈ S, (m - (e.2.1 + e.2.2)) ≤ Fintype.card κ * monomialDeficit m := by
  classical
  let T : Finset (κ × (ℕ × ℕ)) := Finset.univ ×ˢ monomialsBelow m
  calc
    _ ≤ ∑ e ∈ S ∪ T, (m - (e.2.1 + e.2.2)) :=
      Finset.sum_le_sum_of_subset Finset.subset_union_left
    _ = ∑ e ∈ T, (m - (e.2.1 + e.2.2)) := by
      symm
      apply Finset.sum_subset Finset.subset_union_right
      intro e _ he
      have hge : m ≤ e.2.1 + e.2.2 := by
        simpa only [T, Finset.mem_product, Finset.mem_univ, true_and,
          mem_monomialsBelow, not_lt] using he
      exact Nat.sub_eq_zero_of_le hge
    _ = _ := by simp [T, Finset.sum_product, monomialDeficit]

lemma sum_labeled_weights_lower_bound (S : Finset (κ × (ℕ × ℕ))) (m : ℕ) :
    m * S.card ≤ (∑ e ∈ S, (e.2.1 + e.2.2)) + Fintype.card κ * monomialDeficit m := by
  calc
    m * S.card = ∑ _e ∈ S, m := by simp [mul_comm]
    _ ≤ ∑ e ∈ S, ((e.2.1 + e.2.2) + (m - (e.2.1 + e.2.2))) := by
      apply Finset.sum_le_sum
      intro e _
      omega
    _ = (∑ e ∈ S, (e.2.1 + e.2.2)) + (∑ e ∈ S, (m - (e.2.1 + e.2.2))) :=
      Finset.sum_add_distrib
    _ ≤ _ := Nat.add_le_add_left (sum_labeled_deficit_le S m) _

/-- The integer exponent for `s` columns lying in at most `q` residue classes. -/
def residueExponent (q s m : ℕ) : ℕ := m * s - q * (m * (m + 1) * (m + 2) / 6)

lemma residueExponent_antitone {q₁ q₂ : ℕ} (h : q₁ ≤ q₂) (s m : ℕ) :
    residueExponent q₂ s m ≤ residueExponent q₁ s m := by
  unfold residueExponent
  exact Nat.sub_le_sub_left (Nat.mul_le_mul_right _ h) _

theorem sum_labeled_weights_injective_lower_bound {ι : Type*} [Fintype ι]
    (f : ι → κ × (ℕ × ℕ)) (hf : Function.Injective f) (m : ℕ) :
    residueExponent (Fintype.card κ) (Fintype.card ι) m ≤
      ∑ i, ((f i).2.1 + (f i).2.2) := by
  classical
  have h := sum_labeled_weights_lower_bound (Finset.univ.image f) m
  rw [Finset.card_image_of_injective _ hf, Finset.card_univ,
    Finset.sum_image (fun i _ j _ hij => hf hij), monomialDeficit_eq] at h
  unfold residueExponent
  omega

#print axioms sum_labeled_weights_injective_lower_bound
-- 'Erdos477.Counting.sum_labeled_weights_injective_lower_bound' depends on axioms:
-- [propext, Classical.choice, Quot.sound]

end Erdos477.Counting
