import ErdosProblems.Erdos157.FiniteDensity

/-! Conditioning with an exceptional set, without selecting parameters first. -/

namespace Erdos157.Binary

open Elementary

theorem finiteDensity_le_one {A : Type*} [Fintype A] [Nonempty A] (p : A → Prop) :
    finiteDensity p ≤ 1 := by
  have ha : (0 : ℝ) < Nat.card A := by exact_mod_cast Nat.card_pos
  unfold finiteDensity
  apply (div_le_iff₀ ha).mpr
  rw [one_mul]
  exact_mod_cast Nat.card_le_card_of_injective (Subtype.val : {a // p a} → A) Subtype.val_injective

theorem finiteDensity_prod_average {A B : Type*} [Fintype A] [Fintype B]
    (p : A → B → Prop) :
    finiteDensity (fun x : A × B => p x.1 x.2) =
      (∑ a : A, finiteDensity (p a)) / Fintype.card A := by
  classical
  have hc : Fintype.card {x : A × B // p x.1 x.2} =
      ∑ a : A, Fintype.card {b // p a b} := by
    rw [Fintype.card_congr (Equiv.subtypeProdEquivSigmaSubtype p), Fintype.card_sigma]
  simp only [finiteDensity, Nat.card_eq_fintype_card, hc, Fintype.card_prod,
    Nat.cast_mul, Nat.cast_sum, ← Finset.sum_div, div_div]
  rw [mul_comm]

/-- A bad first-stage choice costs its probability, while every good choice
has conditional failure at most `δ`. All second-stage choices stay independent. -/
theorem finiteDensity_prod_condition {A B : Type*} [Fintype A] [Fintype B]
    [Nonempty A] [Nonempty B] (good : A → Prop) (p : A → B → Prop) (δ : ℝ)
    (hδ : 0 ≤ δ) (h : ∀ a, good a → finiteDensity (p a) ≤ δ) :
    finiteDensity (fun x : A × B => p x.1 x.2) ≤ finiteDensity (fun a => ¬good a) + δ := by
  classical
  have ha : (0 : ℝ) < Fintype.card A := by exact_mod_cast Fintype.card_pos (α := A)
  have hs (a : A) : finiteDensity (p a) ≤ (if good a then (0 : ℝ) else 1) + δ := by
    by_cases hg : good a
    · simpa only [if_pos hg, zero_add] using h a hg
    · rw [if_neg hg]
      exact (finiteDensity_le_one (p a)).trans (by linarith)
  have hi : (∑ a : A, if good a then (0 : ℝ) else 1) = Nat.card {a : A // ¬good a} := by
    simp [Finset.sum_ite, Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [finiteDensity_prod_average]
  calc
    _ ≤ (∑ a : A, ((if good a then (0 : ℝ) else 1) + δ)) / Fintype.card A :=
      div_le_div_of_nonneg_right (Finset.sum_le_sum (fun a _ => hs a)) ha.le
    _ = finiteDensity (fun a => ¬good a) + δ := by
      rw [Finset.sum_add_distrib, hi, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      simp only [finiteDensity, Nat.card_eq_fintype_card]
      field_simp

end Erdos157.Binary
