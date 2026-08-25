import Mathlib.Data.Finset.Card

/-!
# Counting the three intrinsic pairs

Four two-element subsets of at most three types must use all three possible
pairs when one distinguished pair is unique and no pair occurs three times.
-/

namespace Puzzling139335.N8

private theorem not_two_values {β : Type*} (p : Fin 4 → β) (center : Fin 4)
    (hunique : ∀ j, j ≠ center → p j ≠ p center)
    (hnotThree : ∀ i j k, i ≠ j → i ≠ k → j ≠ k → ¬(p i = p j ∧ p i = p k))
    (x y : β) (hvalues : ∀ i, p i = x ∨ p i = y) : False := by
  have hothers : ∃ z, ∀ i, i ≠ center → p i = z := by
    rcases hvalues center with hx | hy
    · refine ⟨y, fun i hi => ?_⟩
      exact (hvalues i).resolve_left (fun hix => hunique i hi (hix.trans hx.symm))
    · refine ⟨x, fun i hi => ?_⟩
      exact (hvalues i).resolve_right (fun hiy => hunique i hi (hiy.trans hy.symm))
  obtain ⟨z, hz⟩ := hothers
  have hindices : ∀ r : Fin 4,
      r + 1 ≠ r ∧ r + 2 ≠ r ∧ r + 3 ≠ r ∧
      r + 1 ≠ r + 2 ∧ r + 1 ≠ r + 3 ∧ r + 2 ≠ r + 3 := by decide
  obtain ⟨hi, hj, hk, hij, hik, hjk⟩ := hindices center
  exact hnotThree (center + 1) (center + 2) (center + 3) hij hik hjk
    ⟨(hz _ hi).trans (hz _ hj).symm, (hz _ hi).trans (hz _ hk).symm⟩

/-- A two-element subset of a triple is one of its three pairs. This conclusion
does not require the displayed elements of the triple to be distinct. -/
theorem eq_pair_of_card_two_subset_triple {α : Type*} [DecidableEq α]
    {q : Finset α} {a b c : α}
    (hq : q.card = 2) (hsub : q ⊆ {a, b, c}) :
    q = {a, b} ∨ q = {b, c} ∨ q = {c, a} := by
  obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.mp hq
  have hx : x = a ∨ x = b ∨ x = c := by
    simpa using hsub (by simp : x ∈ ({x, y} : Finset α))
  have hy : y = a ∨ y = b ∨ y = c := by
    simpa using hsub (by simp : y ∈ ({x, y} : Finset α))
  rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;>
    simp_all [Finset.pair_comm]

/-- The intrinsic type set consists of three distinct elements, and all three
two-element subsets occur among the four prescribed pairs. -/
theorem exists_three_types_and_all_pairs {α : Type*} [DecidableEq α]
    (s : Finset α) (p : Fin 4 → Finset α) (center : Fin 4)
    (hs : s.card ≤ 3) (hcard : ∀ i, (p i).card = 2) (hsub : ∀ i, p i ⊆ s)
    (hunique : ∀ j, j ≠ center → p j ≠ p center)
    (hnotThree : ∀ i j k, i ≠ j → i ≠ k → j ≠ k → ¬(p i = p j ∧ p i = p k)) :
    ∃ a b c : α, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ s = {a, b, c} ∧
      (∃ i, p i = {a, b}) ∧ (∃ j, p j = {b, c}) ∧ (∃ k, p k = {c, a}) := by
  have hsThree : s.card = 3 := by
    by_contra hne
    have hsTwo : s.card ≤ 2 := by omega
    have heq (i : Fin 4) : p i = s :=
      Finset.eq_of_subset_of_card_le (hsub i) (by simpa only [hcard i] using hsTwo)
    have hj : center + 1 ≠ center := (by decide : ∀ r : Fin 4, r + 1 ≠ r) center
    exact hunique (center + 1) hj ((heq (center + 1)).trans (heq center).symm)
  obtain ⟨a, b, c, hab, hac, hbc, hsEq⟩ := Finset.card_eq_three.mp hsThree
  have hforms (i : Fin 4) : p i = {a, b} ∨ p i = {b, c} ∨ p i = {c, a} :=
    eq_pair_of_card_two_subset_triple (hcard i) (hsEq ▸ hsub i)
  refine ⟨a, b, c, hab, hac, hbc, hsEq, ?_, ?_, ?_⟩
  · by_contra hmissing
    apply not_two_values p center hunique hnotThree {b, c} {c, a}
    intro i
    rcases hforms i with hi | hi | hi
    · exact False.elim (hmissing ⟨i, hi⟩)
    · exact Or.inl hi
    · exact Or.inr hi
  · by_contra hmissing
    apply not_two_values p center hunique hnotThree {a, b} {c, a}
    intro i
    rcases hforms i with hi | hi | hi
    · exact Or.inl hi
    · exact False.elim (hmissing ⟨i, hi⟩)
    · exact Or.inr hi
  · by_contra hmissing
    apply not_two_values p center hunique hnotThree {a, b} {b, c}
    intro i
    rcases hforms i with hi | hi | hi
    · exact Or.inl hi
    · exact Or.inr hi
    · exact False.elim (hmissing ⟨i, hi⟩)

end Puzzling139335.N8
