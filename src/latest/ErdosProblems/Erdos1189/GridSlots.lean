/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Hall slots for the finite-grid version of Simpson's theorem.
Formal author: OpenAI Codex.
-/

import ErdosProblems.Erdos1189.Grid
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Data.Finset.Sigma

namespace Erdos1189.Grid

open Finset

variable {ι α : Type*} {q : ι → ℕ}

/-- Coordinate `i` has `q i - 1` slots, leaving one value available to avoid. -/
abbrev Slot (q : ι → ℕ) := (i : ι) × Fin (q i - 1)

def slots (q : ι → ℕ) (S : Finset ι) : Finset (Slot q) :=
  S.sigma fun i => (univ : Finset (Fin (q i - 1)))

lemma mem_slots {S : Finset ι} {v : Slot q} : v ∈ slots q S ↔ v.1 ∈ S := by
  simp [slots]

lemma card_slots (S : Finset ι) : (slots q S).card = ∑ i ∈ S, (q i - 1) := by
  simp [slots, card_sigma]

lemma slots_union [DecidableEq ι] (S T : Finset ι) :
    slots q (S ∪ T) = slots q S ∪ slots q T := by
  ext v
  simp only [mem_slots, mem_union]

lemma slots_sdiff [DecidableEq ι] (S T : Finset ι) :
    slots q (S \ T) = slots q S \ slots q T := by
  ext v
  simp only [mem_slots, mem_sdiff]

lemma slots_biUnion [DecidableEq ι] (S : α → Finset ι) (A : Finset α) :
    slots q (A.biUnion S) = A.biUnion fun a => slots q (S a) := by
  ext v
  simp only [mem_slots, mem_biUnion]

lemma familyFixed_union [Fintype ι] [DecidableEq ι] [DecidableEq α]
    (H : α → Box q) (A B : Finset α) :
    familyFixed H (A ∪ B) = familyFixed H A ∪ familyFixed H B := by
  simp only [familyFixed, union_biUnion]

/-- Hall's condition with a set of coordinates reserved from use. -/
lemma exists_slot_matching [Fintype ι] [DecidableEq ι]
    (H : α → Box q) (A : Finset α) (I : Finset ι)
    (hHall : ∀ B ⊆ A, B.card ≤ (slots q (familyFixed H B \ I)).card) :
    ∃ f : A → Slot q, Function.Injective f ∧
      ∀ a : A, (f a).1 ∈ fixed (H a) ∧ (f a).1 ∉ I := by
  classical
  let t : A → Finset (Slot q) := fun a => slots q (fixed (H a) \ I)
  have hcond : ∀ s : Finset A, s.card ≤ (s.biUnion t).card := by
    intro s
    have hs : s.image Subtype.val ⊆ A := by
      intro a ha
      obtain ⟨b, _, rfl⟩ := mem_image.mp ha
      exact b.property
    have hb := hHall (s.image Subtype.val) hs
    rw [card_image_of_injective _ Subtype.val_injective] at hb
    have heq : slots q (familyFixed H (s.image Subtype.val) \ I) = s.biUnion t := by
      ext v
      simp only [mem_slots, mem_sdiff, mem_familyFixed, mem_image, mem_biUnion, t]
      aesop
    rwa [heq] at hb
  obtain ⟨f, hf, hft⟩ := (all_card_le_biUnion_card_iff_existsInjective' t).mp hcond
  refine ⟨f, hf, ?_⟩
  intro a
  exact mem_sdiff.mp (mem_slots.mp (hft a))

/-- Match each box to one of the `q i - 1` slots of a coordinate it fixes.
Then choose a coordinate value avoided by all boxes assigned to that coordinate.
Coordinates in `I` can simultaneously retain any prescribed values. -/
theorem exists_avoiding_of_hall [Fintype ι] [DecidableEq ι]
    (H : α → Box q) (A : Finset α) (I : Finset ι) (hq : ∀ i, 0 < q i)
    (x₀ : Point q)
    (hHall : ∀ B ⊆ A, B.card ≤ (slots q (familyFixed H B \ I)).card) :
    ∃ x : Point q, (∀ i ∈ I, x i = x₀ i) ∧ ∀ a ∈ A, ¬ Contains (H a) x := by
  classical
  obtain ⟨f, hf, hfixed⟩ := exists_slot_matching H A I hHall
  let B : ι → Finset A := fun i => univ.filter fun a => (f a).1 = i
  have hBcard : ∀ i, (B i).card ≤ q i - 1 := by
    intro i
    have hsub : (B i).image f ⊆ slots q {i} := by
      intro v hv
      obtain ⟨a, ha, rfl⟩ := mem_image.mp hv
      exact mem_slots.mpr (mem_singleton.mpr (mem_filter.mp ha).2)
    calc
      (B i).card = ((B i).image f).card := (card_image_of_injective _ hf).symm
      _ ≤ (slots q {i}).card := card_le_card hsub
      _ = q i - 1 := by rw [card_slots, sum_singleton]
  let V : (i : ι) → Finset (Fin (q i)) := fun i =>
    (B i).image fun a : A => (H a i).getD ⟨0, hq i⟩
  have hVcard : ∀ i, (V i).card < q i := by
    intro i
    have hle : (V i).card ≤ (B i).card := card_image_le
    have := hBcard i
    have := hq i
    omega
  have hchoice : ∀ i, ∃ v : Fin (q i), v ∉ V i ∧ (i ∈ I → v = x₀ i) := by
    intro i
    by_cases hi : i ∈ I
    · have hBempty : B i = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro a ha
        have hfa : (f a).1 = i := (mem_filter.mp ha).2
        exact (hfixed a).2 (hfa ▸ hi)
      refine ⟨x₀ i, ?_, fun _ => rfl⟩
      simp [V, hBempty]
    · have hlt : (V i).card < (univ : Finset (Fin (q i))).card := by
        simpa using hVcard i
      obtain ⟨v, _, hv⟩ := exists_mem_notMem_of_card_lt_card hlt
      exact ⟨v, hv, fun h => False.elim (hi h)⟩
  choose x hxout hxI using hchoice
  refine ⟨x, hxI, ?_⟩
  intro a ha hax
  let a' : A := ⟨a, ha⟩
  let i := (f a').1
  obtain ⟨v, hv⟩ := mem_fixed.mp (hfixed a').1
  change H a i = some v at hv
  have haB : a' ∈ B i := by simp [B, i]
  have hmem : (H a i).getD ⟨0, hq i⟩ ∈ V i := mem_image.mpr ⟨a', haB, rfl⟩
  have hxi : x i = v := hax i v hv
  apply hxout i
  rw [hxi]
  simpa only [hv, Option.getD_some] using hmem

end Erdos1189.Grid
