/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Finite arithmetic slots and the tag-capacity argument for digit frames.
Informal source: Lemmas 5.1 and 5.2 of Pickhardt and Omniscience Research Agent,
"Irreducible Covering Sets: A Solution of Erdős Problem 1189".
Formal author: OpenAI Codex.
-/

import ErdosProblems.Erdos1189.Simpson

namespace Erdos1189

open Finset

/-- Prime, zero-based digit index, and zero-based nonzero-value label. -/
abbrev ArithmeticSlot := Sigma (fun _ : ℕ => ℕ × ℕ)

def arithmeticSlots (N : ℕ) : Finset ArithmeticSlot :=
  N.primeFactors.sigma fun p => (range (N.factorization p)) ×ˢ (range (p - 1))

lemma mem_arithmeticSlots {N : ℕ} {s : ArithmeticSlot} :
    s ∈ arithmeticSlots N ↔
      s.1 ∈ N.primeFactors ∧ s.2.1 < N.factorization s.1 ∧ s.2.2 < s.1 - 1 := by
  simp [arithmeticSlots, and_assoc]

lemma card_arithmeticSlots (N : ℕ) : (arithmeticSlots N).card = simpsonWeight N := by
  simp [arithmeticSlots, card_sigma, simpsonWeight]

/-- A tag fixes the stated prime-adic coordinate and has a valid label. -/
def ValidTag (s : ArithmeticSlot) (d : ℕ) : Prop :=
  s.1.Prime ∧ s.2.2 < s.1 - 1 ∧ s.1 ^ (s.2.1 + 1) ∣ d

lemma ValidTag.mem_arithmeticSlots {s : ArithmeticSlot} {d N : ℕ}
    (h : ValidTag s d) (hN : N ≠ 0) (hd : d ∣ N) : s ∈ arithmeticSlots N := by
  have hpdiv : s.1 ^ (s.2.1 + 1) ∣ N := h.2.2.trans hd
  have hfact : s.2.1 < N.factorization s.1 := by
    have := (h.1.pow_dvd_iff_le_factorization hN).mp hpdiv
    omega
  have hpN : s.1 ∈ N.factorization.support :=
    Finsupp.mem_support_iff.mpr (show N.factorization s.1 ≠ 0 by omega)
  exact Erdos1189.mem_arithmeticSlots.mpr ⟨hpN, hfact, h.2.1⟩

lemma tag_capacity_common_multiple {D : Finset ℕ} {N : ℕ}
    (tag : ℕ → ArithmeticSlot) (hN : N ≠ 0) (hdiv : ∀ d ∈ D, d ∣ N)
    (htags : ∀ d ∈ D, ValidTag (tag d) d) (hinj : Set.InjOn tag D) :
    D.card ≤ simpsonWeight N := by
  rw [← card_arithmeticSlots]
  exact card_le_card_of_injOn tag
    (fun d hd => (htags d hd).mem_arithmeticSlots hN (hdiv d hd)) hinj

/-- Lemma 5.1: tags never outnumber the slots of their own lcm. -/
theorem tag_capacity {D : Finset ℕ} (tag : ℕ → ArithmeticSlot)
    (hpos : ∀ d ∈ D, 0 < d) (htags : ∀ d ∈ D, ValidTag (tag d) d)
    (hinj : Set.InjOn tag D) : D.card ≤ simpsonWeight (D.lcm id) := by
  exact tag_capacity_common_multiple tag
    (lcm_ne_zero_iff.mpr (fun d hd => (hpos d hd).ne'))
    (fun _ hd => dvd_lcm hd) htags hinj

/-- Leaving one specified slot unused improves tag capacity by one. -/
lemma tag_capacity_with_free_slot {D : Finset ℕ} {N : ℕ}
    (tag : ℕ → ArithmeticSlot) (hN : N ≠ 0) (hdiv : ∀ d ∈ D, d ∣ N)
    (htags : ∀ d ∈ D, ValidTag (tag d) d) (hinj : Set.InjOn tag D)
    {s : ArithmeticSlot} (hs : s ∈ arithmeticSlots N) (hfree : ∀ d ∈ D, tag d ≠ s) :
    D.card + 1 ≤ simpsonWeight N := by
  have hi : D.image tag ⊆ (arithmeticSlots N).erase s := by
    intro t ht
    obtain ⟨d, hd, rfl⟩ := mem_image.mp ht
    exact mem_erase.mpr ⟨hfree d hd, (htags d hd).mem_arithmeticSlots hN (hdiv d hd)⟩
  have hc := card_le_card hi
  rw [card_image_of_injOn hinj] at hc
  have he := card_erase_add_one hs
  rw [card_arithmeticSlots] at he
  omega

end Erdos1189
