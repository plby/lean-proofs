/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Counting finite sets represented by labelled subfamilies and a remainder.
Informal source: the modulus encoding in BBMST Section 7.2.
Formal author: OpenAI Codex.
-/

import ErdosProblems.Erdos1189.BoundedProfiles
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Nat.Choose.Bounds

namespace Erdos1189

open Finset

variable {β α : Type*} [Fintype β] [DecidableEq β] [DecidableEq α]

noncomputable def familyUnionUniverse (allowed : β → Finset α) (sizes : β → ℕ)
    (remainder : Finset α) (x : ℕ) : Finset (Finset α) := by
  exact ((Fintype.piFinset (fun i => (allowed i).powersetCard (sizes i))).product
    (remainder.powersetCard x)).image (fun z => univ.biUnion z.1 ∪ z.2)

lemma mem_familyUnionUniverse (allowed : β → Finset α) (sizes : β → ℕ)
    (remainder : Finset α) (x : ℕ) (families : β → Finset α) (R : Finset α)
    (hfamilies : ∀ i, families i ⊆ allowed i ∧ (families i).card = sizes i)
    (hR : R ⊆ remainder) (hRx : R.card = x) :
    (univ.biUnion families ∪ R) ∈ familyUnionUniverse allowed sizes remainder x := by
  apply mem_image.mpr
  refine ⟨(families, R), mem_product.mpr ⟨?_, mem_powersetCard.mpr ⟨hR, hRx⟩⟩, rfl⟩
  exact Fintype.mem_piFinset.mpr fun i => mem_powersetCard.mpr (hfamilies i)

lemma familyUnionUniverse_card_le (allowed : β → Finset α) (sizes : β → ℕ)
    (remainder : Finset α) (x : ℕ) :
    (familyUnionUniverse allowed sizes remainder x).card ≤
      (∏ i, (allowed i).card ^ sizes i) * remainder.card ^ x := by
  calc
    _ ≤ ((Fintype.piFinset (fun i => (allowed i).powersetCard (sizes i))).product
        (remainder.powersetCard x)).card := card_image_le
    _ = (∏ i, (allowed i).card.choose (sizes i)) * remainder.card.choose x := by
      simpa only [Finset.product_eq_sprod, Fintype.card_piFinset, card_powersetCard] using
        Finset.card_product (Fintype.piFinset (fun i => (allowed i).powersetCard (sizes i)))
          (remainder.powersetCard x)
    _ ≤ _ := Nat.mul_le_mul (prod_le_prod' (fun i _ => Nat.choose_le_pow _ _))
      (Nat.choose_le_pow _ _)

lemma familyUnionUniverse_card_le_caps (allowed : β → Finset α) (sizes caps : β → ℕ)
    (remainder : Finset α) (x : ℕ) (hsize : ∀ i, sizes i ≤ caps i)
    (hpos : ∀ i, 0 < (allowed i).card) :
    (familyUnionUniverse allowed sizes remainder x).card ≤
      (∏ i, (allowed i).card ^ caps i) * remainder.card ^ x := by
  apply (familyUnionUniverse_card_le allowed sizes remainder x).trans
  apply Nat.mul_le_mul_right
  apply prod_le_prod'
  intro i _
  exact Nat.pow_le_pow_right (hpos i) (hsize i)

lemma familyUnionUniverse_card_le_exp (allowed : β → Finset α) (sizes caps : β → ℕ)
    (remainder : Finset α) (x : ℕ) (hsize : ∀ i, sizes i ≤ caps i)
    (hpos : ∀ i, 0 < (allowed i).card) (hRpos : 0 < remainder.card) :
    ((familyUnionUniverse allowed sizes remainder x).card : ℝ) ≤
      Real.exp ((∑ i, (caps i : ℝ) * Real.log (allowed i).card) +
        (x : ℝ) * Real.log remainder.card) := by
  have h := familyUnionUniverse_card_le_caps allowed sizes caps remainder x hsize hpos
  have heq : (((∏ i, (allowed i).card ^ caps i) * remainder.card ^ x : ℕ) : ℝ) =
      Real.exp ((∑ i, (caps i : ℝ) * Real.log (allowed i).card) +
        (x : ℝ) * Real.log remainder.card) := by
    have hp : (0 : ℝ) < ((∏ i, (allowed i).card ^ caps i) * remainder.card ^ x : ℕ) := by
      exact_mod_cast Nat.mul_pos (prod_pos fun i _ => Nat.pow_pos (hpos i)) (Nat.pow_pos hRpos)
    have hpA : (0 : ℝ) < (∏ i, (allowed i).card ^ caps i : ℕ) := by
      exact_mod_cast (prod_pos fun i _ => Nat.pow_pos (hpos i))
    have hpR : (0 : ℝ) < (remainder.card ^ x : ℕ) := by exact_mod_cast Nat.pow_pos hRpos
    rw [← Real.exp_log hp]
    congr 1
    rw [Nat.cast_mul, Real.log_mul hpA.ne' hpR.ne', Nat.cast_prod,
      Real.log_prod (fun i _ => by exact_mod_cast (Nat.pow_pos (hpos i) :
        0 < (allowed i).card ^ caps i).ne')]
    simp only [Nat.cast_pow, Real.log_pow]
  rw [← heq]
  exact_mod_cast h

end Erdos1189
