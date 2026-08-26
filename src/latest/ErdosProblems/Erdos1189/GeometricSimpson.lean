/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
The geometric Simpson bound, proved through Hall's theorem.
Informal result: R. J. Simpson; the finite-grid formulation appears in
Balister--Bollobás--Morris--Sahasrabudhe--Tiba, Theorem 2.4.
Formal author: OpenAI Codex.

Choose a subfamily maximizing the excess of its number of boxes over its
coordinate slots. Hall's theorem matches every remaining box to a slot outside
that subfamily's support. An avoiding assignment shows that the subfamily itself
covers. Minimality then forces the maximizing subfamily to be the whole cover.
-/

import ErdosProblems.Erdos1189.GridSlots

namespace Erdos1189.Grid

open Finset

variable {ι α : Type*} [Fintype ι] [DecidableEq ι] {q : ι → ℕ}

def deficiency (H : α → Box q) (A : Finset α) : ℤ :=
  (A.card : ℤ) - (slots q (familyFixed H A)).card

lemma remainder_hall [DecidableEq α] (H : α → Box q) {A T : Finset α}
    (hT : T ⊆ A) (hmax : ∀ B ⊆ A, deficiency H B ≤ deficiency H T) :
    ∀ U ⊆ A \ T,
      U.card ≤ (slots q (familyFixed H U \ familyFixed H T)).card := by
  intro U hU
  have hUA : U ⊆ A := fun u hu => (mem_sdiff.mp (hU hu)).1
  have hdisj : Disjoint T U := by
    apply disjoint_left.mpr
    intro u huT huU
    exact (mem_sdiff.mp (hU huU)).2 huT
  have hcard : (T ∪ U).card = T.card + U.card := card_union_of_disjoint hdisj
  have hslots : (slots q (familyFixed H (T ∪ U))).card =
      (slots q (familyFixed H T)).card +
        (slots q (familyFixed H U \ familyFixed H T)).card := by
    rw [familyFixed_union, slots_union, slots_sdiff]
    have := card_sdiff_add_card (slots q (familyFixed H U)) (slots q (familyFixed H T))
    rw [union_comm] at this
    omega
  have hbound := hmax (T ∪ U) (union_subset hT hUA)
  simp only [deficiency, hcard, hslots, Nat.cast_add] at hbound
  omega

lemma MinimalCoverOn.maximal_deficiency (H : α → Box q) (A : Finset α)
    (hq : ∀ i, 0 < q i) (hcover : MinimalCoverOn H A Set.univ) :
    ∀ B ⊆ A, deficiency H B ≤ deficiency H A := by
  classical
  obtain ⟨T, hT, hmax⟩ := exists_max_image A.powerset (deficiency H)
    ⟨∅, empty_mem_powerset A⟩
  have hTA : T ⊆ A := mem_powerset.mp hT
  have hmax' : ∀ B ⊆ A, deficiency H B ≤ deficiency H T :=
    fun B hB => hmax B (mem_powerset.mpr hB)
  have hHall := remainder_hall H hTA hmax'
  have hTcover : CoversOn H T Set.univ := by
    intro x hx
    obtain ⟨y, hyagree, hyavoid⟩ :=
      exists_avoiding_of_hall H (A \ T) (familyFixed H T) hq x hHall
    obtain ⟨a, haA, hay⟩ := hcover.1 y (Set.mem_univ _)
    have haT : a ∈ T := by
      by_contra haT
      exact hyavoid a (mem_sdiff.mpr ⟨haA, haT⟩) hay
    refine ⟨a, haT, ?_⟩
    intro i v hiv
    have hi : i ∈ familyFixed H T := mem_familyFixed.mpr ⟨a, haT, mem_fixed.mpr ⟨v, hiv⟩⟩
    exact (hyagree i hi).symm.trans (hay i v hiv)
  have hTeq : T = A := by
    by_contra hne
    exact hcover.2 T (Finset.ssubset_iff_subset_ne.mpr ⟨hTA, hne⟩) hTcover
  simpa only [hTeq] using hmax'

/-- Simpson's theorem for a minimal cover of a finite product by boxes:
the number of boxes is at least one plus the sum of `q i - 1` over every
coordinate fixed by at least one box. -/
theorem simpson_grid (H : α → Box q) (A : Finset α) (hq : ∀ i, 0 < q i)
    (hcover : MinimalCoverOn H A Set.univ) :
    (∑ i ∈ familyFixed H A, (q i - 1)) + 1 ≤ A.card := by
  classical
  rw [← card_slots]
  by_contra hbad
  have hmax := hcover.maximal_deficiency H A hq
  have hHall : ∀ B ⊆ A, B.card ≤ (slots q (familyFixed H B \ ∅)).card := by
    intro B hB
    have hb := hmax B hB
    simp only [deficiency] at hb
    rw [sdiff_empty]
    omega
  obtain ⟨x, _, hx⟩ := exists_avoiding_of_hall H A ∅ hq (fun i => ⟨0, hq i⟩) hHall
  obtain ⟨a, ha, hax⟩ := hcover.1 x (Set.mem_univ _)
  exact hx a ha hax

end Erdos1189.Grid
