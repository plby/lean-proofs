import StackExchange.Puzzling139335.N8.PairCounting
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Fin.VecNotation
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Tactic.FinCases

/-!
# Three two-element subsets of at most three types

This file concerns finite sets only.  It records the two possibilities used
for the three double-corner pieces in the seven-incidence case: three distinct
pairs use all three possible pairs, whereas a nonconstant repeated family can
be ordered as two copies of `{a, b}` followed by `{a, r}`.
-/

namespace Puzzling139335.N7

/-- Two different two-element subsets force a supporting set of cardinality
at most three to have exactly three elements. -/
theorem support_card_three_of_distinct_pairs {α : Type*}
    {s A B : Finset α} (hs : s.card ≤ 3)
    (hA : A.card = 2) (hB : B.card = 2)
    (hAs : A ⊆ s) (hBs : B ⊆ s) (hne : A ≠ B) : s.card = 3 := by
  by_contra hnot
  have hsTwo : s.card ≤ 2 := by omega
  have hAsEq : A = s :=
    Finset.eq_of_subset_of_card_le hAs (by omega)
  have hBsEq : B = s :=
    Finset.eq_of_subset_of_card_le hBs (by omega)
  exact hne (hAsEq.trans hBsEq.symm)

/-- Two distinct pairs drawn from at most three elements have a common
element, and their remaining elements are different. -/
theorem two_distinct_pairs_classification {α : Type*} [DecidableEq α]
    {s A B : Finset α} (hs : s.card ≤ 3)
    (hA : A.card = 2) (hB : B.card = 2)
    (hAs : A ⊆ s) (hBs : B ⊆ s) (hne : A ≠ B) :
    ∃ a b r : α, a ≠ b ∧ a ≠ r ∧ b ≠ r ∧
      s = {a, b, r} ∧ A = {a, b} ∧ B = {a, r} := by
  obtain ⟨a, b, c, hab, hac, hbc, hsEq⟩ := Finset.card_eq_three.mp
    (support_card_three_of_distinct_pairs hs hA hB hAs hBs hne)
  have hAF := N8.eq_pair_of_card_two_subset_triple hA (hsEq ▸ hAs)
  have hBF := N8.eq_pair_of_card_two_subset_triple hB (hsEq ▸ hBs)
  rcases hAF with hAa | hAb | hAc
  · rcases hBF with hBa | hBb | hBc
    · exact False.elim (hne (hAa.trans hBa.symm))
    · refine ⟨b, a, c, hab.symm, hbc, hac, ?_, ?_, hBb⟩
      · rw [hsEq]
        ext x
        simp [or_left_comm]
      · simpa [Finset.pair_comm] using hAa
    · refine ⟨a, b, c, hab, hac, hbc, hsEq, hAa, ?_⟩
      simpa [Finset.pair_comm] using hBc
  · rcases hBF with hBa | hBb | hBc
    · refine ⟨b, c, a, hbc, hab.symm, hac.symm, ?_, hAb, ?_⟩
      · rw [hsEq]
        ext x
        simp [or_left_comm, or_comm]
      · simpa [Finset.pair_comm] using hBa
    · exact False.elim (hne (hAb.trans hBb.symm))
    · refine ⟨c, b, a, hbc.symm, hac.symm, hab.symm, ?_, ?_, hBc⟩
      · rw [hsEq]
        ext x
        simp [or_left_comm, or_comm]
      · simpa [Finset.pair_comm] using hAb
  · rcases hBF with hBa | hBb | hBc
    · refine ⟨a, c, b, hac, hab, hbc.symm, ?_, ?_, hBa⟩
      · rw [hsEq]
        ext x
        simp [or_comm]
      · simpa [Finset.pair_comm] using hAc
    · refine ⟨c, a, b, hac.symm, hbc.symm, hab, ?_, hAc, ?_⟩
      · rw [hsEq]
        ext x
        simp [or_left_comm, or_comm]
      · simpa [Finset.pair_comm] using hBb
    · exact False.elim (hne (hAc.trans hBc.symm))

/-- A nonconstant, noninjective triple can be reordered so that its first two
values agree and its third value is different. -/
theorem repeated_pair_permutation {β : Type*} (p : Fin 3 → β)
    (hnotAll : ¬(p 0 = p 1 ∧ p 0 = p 2))
    (hnotInj : ¬Function.Injective p) :
    ∃ σ : Equiv.Perm (Fin 3),
      p (σ 0) = p (σ 1) ∧ p (σ 0) ≠ p (σ 2) := by
  classical
  by_cases h01 : p 0 = p 1
  · exact ⟨Equiv.refl _, h01, fun h02 => hnotAll ⟨h01, h02⟩⟩
  by_cases h02 : p 0 = p 2
  · refine ⟨Equiv.swap 1 2, ?_⟩
    simpa [Equiv.swap_apply_def] using And.intro h02 h01
  have h12 : p 1 = p 2 := by
    by_contra h12
    apply hnotInj
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  refine ⟨Equiv.swap 0 2, ?_⟩
  have h20 : p 2 ≠ p 0 := Ne.symm h02
  simpa [Equiv.swap_apply_def] using And.intro h12.symm h20

/-- The repeated-pair alternative, including a concrete permutation of the
three indices and three distinct intrinsic types. -/
theorem repeated_pairs_classification {α : Type*} [DecidableEq α]
    (s : Finset α) (p : Fin 3 → Finset α)
    (hs : s.card ≤ 3) (hcard : ∀ i, (p i).card = 2)
    (hsub : ∀ i, p i ⊆ s)
    (hnotAll : ¬(p 0 = p 1 ∧ p 0 = p 2))
    (hnotInj : ¬Function.Injective p) :
    ∃ a b r : α, ∃ σ : Equiv.Perm (Fin 3),
      a ≠ b ∧ a ≠ r ∧ b ≠ r ∧ s = {a, b, r} ∧
        p (σ 0) = {a, b} ∧ p (σ 1) = {a, b} ∧ p (σ 2) = {a, r} := by
  obtain ⟨σ, h01, h02⟩ := repeated_pair_permutation p hnotAll hnotInj
  obtain ⟨a, b, r, hab, har, hbr, hsEq, h0, h2⟩ :=
    two_distinct_pairs_classification hs (hcard (σ 0)) (hcard (σ 2))
      (hsub (σ 0)) (hsub (σ 2)) h02
  exact ⟨a, b, r, σ, hab, har, hbr, hsEq, h0, h01.symm.trans h0, h2⟩

private theorem not_injective_of_two_values {β : Type*} (p : Fin 3 → β)
    (x y : β) (hvalues : ∀ i, p i = x ∨ p i = y) :
    ¬Function.Injective p := by
  intro hinj
  have h01 : p 0 ≠ p 1 := fun h => (by decide : (0 : Fin 3) ≠ 1) (hinj h)
  have h02 : p 0 ≠ p 2 := fun h => (by decide : (0 : Fin 3) ≠ 2) (hinj h)
  have h12 : p 1 ≠ p 2 := fun h => (by decide : (1 : Fin 3) ≠ 2) (hinj h)
  rcases hvalues 0 with h0 | h0 <;>
    rcases hvalues 1 with h1 | h1 <;>
    rcases hvalues 2 with h2 | h2 <;> simp_all

/-- Three different pairs drawn from at most three types use every possible
pair of a three-element type set. -/
theorem distinct_pairs_use_all_three {α : Type*} [DecidableEq α]
    (s : Finset α) (p : Fin 3 → Finset α)
    (hs : s.card ≤ 3) (hcard : ∀ i, (p i).card = 2)
    (hsub : ∀ i, p i ⊆ s) (hinj : Function.Injective p) :
    ∃ a b r : α, a ≠ b ∧ a ≠ r ∧ b ≠ r ∧ s = {a, b, r} ∧
      (∃ i, p i = {a, b}) ∧ (∃ j, p j = {b, r}) ∧ (∃ k, p k = {r, a}) := by
  have h01 : p 0 ≠ p 1 := fun h => (by decide : (0 : Fin 3) ≠ 1) (hinj h)
  obtain ⟨a, b, r, hab, har, hbr, hsEq⟩ := Finset.card_eq_three.mp
    (support_card_three_of_distinct_pairs hs (hcard 0) (hcard 1)
      (hsub 0) (hsub 1) h01)
  have hforms (i : Fin 3) : p i = {a, b} ∨ p i = {b, r} ∨ p i = {r, a} :=
    N8.eq_pair_of_card_two_subset_triple (hcard i) (hsEq ▸ hsub i)
  refine ⟨a, b, r, hab, har, hbr, hsEq, ?_, ?_, ?_⟩
  · by_contra hmissing
    apply not_injective_of_two_values p {b, r} {r, a} ?_ hinj
    intro i
    rcases hforms i with hi | hi | hi
    · exact False.elim (hmissing ⟨i, hi⟩)
    · exact Or.inl hi
    · exact Or.inr hi
  · by_contra hmissing
    apply not_injective_of_two_values p {a, b} {r, a} ?_ hinj
    intro i
    rcases hforms i with hi | hi | hi
    · exact Or.inl hi
    · exact False.elim (hmissing ⟨i, hi⟩)
    · exact Or.inr hi
  · by_contra hmissing
    apply not_injective_of_two_values p {a, b} {b, r} ?_ hinj
    intro i
    rcases hforms i with hi | hi | hi
    · exact Or.inl hi
    · exact Or.inr hi
    · exact False.elim (hmissing ⟨i, hi⟩)

/-- Any three distinct indices give a permutation of `Fin 3`. -/
theorem exists_perm_fin_three (i j k : Fin 3)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    ∃ σ : Equiv.Perm (Fin 3), σ 0 = i ∧ σ 1 = j ∧ σ 2 = k := by
  classical
  have hf : Function.Injective (![i, j, k] : Fin 3 → Fin 3) := by
    intro x y hxy
    fin_cases x <;> fin_cases y <;> simp_all
  exact ⟨Equiv.ofBijective (![i, j, k])
    (Finite.injective_iff_bijective.mp hf), rfl, rfl, rfl⟩

/-- The all-distinct alternative, with the three pairs in cyclic order after
a permutation of the indices. -/
theorem distinct_pairs_classification {α : Type*} [DecidableEq α]
    (s : Finset α) (p : Fin 3 → Finset α)
    (hs : s.card ≤ 3) (hcard : ∀ i, (p i).card = 2)
    (hsub : ∀ i, p i ⊆ s) (hinj : Function.Injective p) :
    ∃ a b r : α, ∃ σ : Equiv.Perm (Fin 3),
      a ≠ b ∧ a ≠ r ∧ b ≠ r ∧ s = {a, b, r} ∧
        p (σ 0) = {a, b} ∧ p (σ 1) = {b, r} ∧ p (σ 2) = {r, a} := by
  obtain ⟨a, b, r, hab, har, hbr, hsEq, ⟨i, hi⟩, ⟨j, hj⟩, ⟨k, hk⟩⟩ :=
    distinct_pairs_use_all_three s p hs hcard hsub hinj
  have hij : i ≠ j := by
    intro heq
    subst j
    have ha : a ∈ ({b, r} : Finset α) := by rw [← hj, hi]; simp
    simp [hab, har] at ha
  have hik : i ≠ k := by
    intro heq
    subst k
    have hb : b ∈ ({r, a} : Finset α) := by rw [← hk, hi]; simp
    simp [hbr, hab.symm] at hb
  have hjk : j ≠ k := by
    intro heq
    subst k
    have hb : b ∈ ({r, a} : Finset α) := by rw [← hk, hj]; simp
    simp [hbr, hab.symm] at hb
  obtain ⟨σ, hσ0, hσ1, hσ2⟩ := exists_perm_fin_three i j k hij hik hjk
  exact ⟨a, b, r, σ, hab, har, hbr, hsEq,
    hσ0 ▸ hi, hσ1 ▸ hj, hσ2 ▸ hk⟩

end Puzzling139335.N7
