import ErdosProblems.Erdos547.PrivateSets

/-!
# Private sets from separate and joint class capacities
-/

namespace Erdos547

open Finset
open scoped BigOperators

open scoped Classical in
theorem exists_private_sets_of_class_bounds {F V C : Type*} [Fintype F] [DecidableEq C]
    (col : F → C) (w : F → ℕ) (candidates : F → Finset V) (D : C → ℝ)
    (hsingle : ∀ x,
      ((∑ y ∈ (Finset.univ : Finset F).filter (fun y ↦ col y = col x), w y) : ℝ) ≤ D (col x))
    (hjoint : ∀ x y, col x ≠ col y → ((∑ z, w z) : ℝ) ≤ max (D (col x)) (D (col y)))
    (hsize : ∀ x, D (col x) ≤ ((candidates x).card : ℝ)) :
    ∃ R : F → Finset V, (∀ x, R x ⊆ candidates x) ∧
      (∀ x, (R x).card = w x) ∧ Pairwise (fun x y ↦ Disjoint (R x) (R y)) := by
  classical
  apply exists_disjoint_private_sets w candidates
  apply weighted_hall_of_two_class_bounds col w candidates
  · intro x
    exact_mod_cast (hsingle x).trans (hsize x)
  · intro x y hxy
    have hx : ((candidates x).card : ℝ) ≤ (candidates x ∪ candidates y).card := by
      exact_mod_cast Finset.card_le_card (Finset.subset_union_left : candidates x ⊆ _)
    have hy : ((candidates y).card : ℝ) ≤ (candidates x ∪ candidates y).card := by
      exact_mod_cast Finset.card_le_card (Finset.subset_union_right : candidates y ⊆ _)
    exact_mod_cast (hjoint x y hxy).trans (max_le ((hsize x).trans hx) ((hsize y).trans hy))

end Erdos547

#print axioms Erdos547.exists_private_sets_of_class_bounds
