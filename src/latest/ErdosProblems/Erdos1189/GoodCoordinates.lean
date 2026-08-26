/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
The good coordinate families and the restriction excluding their witnesses.
Informal source: the two cases in the proof of BBMST Lemma 3.4.
Formal author: OpenAI Codex.
-/

import ErdosProblems.Erdos1189.RestrictionBounds

namespace Erdos1189.Grid

open Finset

variable {ι α : Type*} {q : ι → ℕ} [Fintype ι] [DecidableEq ι]

noncomputable def goodBoxFamily (H : α → Box q) (A : Finset α) (δ : ℝ) (i : ι) : Finset α := by
  classical
  exact A.filter fun a => i ∈ fixed (H a) ∧ δ < boxMeasureOn (univ.erase i) (H a)

noncomputable def specialValues (H : α → Box q) (A : Finset α) (δ : ℝ) (i : ι) :
    Finset (Fin (q i)) := by
  classical
  exact univ.filter fun v => ∃ a ∈ A, H a i = some v ∧ δ < boxMeasureOn (univ.erase i) (H a)

noncomputable def remainingValues (H : α → Box q) (A : Finset α) (δ : ℝ) (i : ι) :
    Finset (Fin (q i)) := univ \ specialValues H A δ i

lemma specialValues_card_le_goodBoxFamily (H : α → Box q) (A : Finset α) (δ : ℝ) (i : ι) :
    (specialValues H A δ i).card ≤ (goodBoxFamily H A δ i).card := by
  classical
  have hsub : (specialValues H A δ i).image some ⊆
      (goodBoxFamily H A δ i).image (fun a => H a i) := by
    intro w hw
    obtain ⟨v, hv, rfl⟩ := mem_image.mp hw
    obtain ⟨a, ha, hv, hμ⟩ := (mem_filter.mp hv).2
    exact mem_image.mpr ⟨a, mem_filter.mpr ⟨ha, mem_fixed.mpr ⟨v, hv⟩, hμ⟩, hv⟩
  have h := (card_le_card hsub).trans (card_image_le)
  rw [card_image_of_injective _ (Option.some_injective _)] at h
  exact h

lemma remainingValues_card_add (H : α → Box q) (A : Finset α) (δ : ℝ) (i : ι) :
    (remainingValues H A δ i).card + (specialValues H A δ i).card = q i := by
  have h := card_sdiff_add_card_eq_card (subset_univ (specialValues H A δ i))
  simpa only [remainingValues, card_univ, Fintype.card_fin] using h

lemma good_family_of_few_remaining (H : α → Box q) (A : Finset α) (δ ε : ℝ) {i : ι}
    (hi : ((remainingValues H A δ i).card : ℝ) < ε * ((q i : ℝ) - 1) + 1) :
    (1 - ε) * ((q i : ℝ) - 1) ≤ (goodBoxFamily H A δ i).card := by
  have hcard : ((remainingValues H A δ i).card : ℝ) +
      (specialValues H A δ i).card = q i := by
    exact_mod_cast remainingValues_card_add H A δ i
  have hgood : ((specialValues H A δ i).card : ℝ) ≤ (goodBoxFamily H A δ i).card := by
    exact_mod_cast specialValues_card_le_goodBoxFamily H A δ i
  nlinarith

lemma surviving_box_small (H : α → Box q) (A : Finset α) (δ : ℝ) {a : α}
    (ha : a ∈ restrictionFamily (remainingValues H A δ) H A) {i : ι}
    (hi : i ∈ fixed (H a)) : boxMeasureOn (univ.erase i) (H a) ≤ δ := by
  classical
  obtain ⟨ha, hcompat⟩ := mem_filter.mp ha
  obtain ⟨v, hv⟩ := mem_fixed.mp hi
  have hvR := hcompat i v hv
  by_contra hnot
  have hvSpecial : v ∈ specialValues H A δ i :=
    mem_filter.mpr ⟨mem_univ _, a, ha, hv, lt_of_not_ge hnot⟩
  exact (mem_sdiff.mp hvR).2 hvSpecial

lemma surviving_box_two_fixed (H : α → Box q) (A : Finset α) {δ : ℝ} (hδ : δ < 1)
    (hfixed : ∀ a ∈ A, (fixed (H a)).Nonempty) {a : α}
    (ha : a ∈ restrictionFamily (remainingValues H A δ) H A) : 2 ≤ (fixed (H a)).card := by
  classical
  have haA : a ∈ A := (mem_filter.mp ha).1
  have hpos := card_pos.mpr (hfixed a haA)
  by_contra hnot
  have hcard : (fixed (H a)).card = 1 := by omega
  obtain ⟨i, hF⟩ := card_eq_one.mp hcard
  have hi : i ∈ fixed (H a) := by rw [hF]; exact mem_singleton_self _
  have hsmall := surviving_box_small H A δ ha hi
  have hμ : boxMeasureOn (univ.erase i) (H a) = 1 := by
    rw [boxMeasureOn_eq_fixed, hF]
    simp
  linarith

end Erdos1189.Grid
