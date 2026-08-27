import Arxiv.Arxiv2411_18291.CliqueFamilyBoundedness

/-! # Boundedness of singleton graphs and small clique families -/

open Finset

noncomputable section

namespace Arxiv2411_18291

variable {V : Type*} [Fintype V] [DecidableEq V] {q r : ℕ}

theorem graphBounded_singleton (e : Block V (r + 1)) {θ : ℝ}
    (hθ : 1 < θ * Fintype.card V) : IsGraphBounded {e} θ := by
  intro S
  have hc : ((({e} : Finset (Block V (r + 1))).filter fun f => S.val ⊆ f.val).card : ℝ) ≤ 1 := by
    exact_mod_cast (card_le_card (filter_subset _ ({e} : Finset (Block V (r + 1))))).trans_eq
      (card_singleton e)
  exact hc.trans_lt hθ

theorem cliqueFamilyBounded_of_card (D : Finset (Block V q)) {θ : ℝ}
    (hθ : ((q - r : ℕ) : ℝ) * D.card < θ * Fintype.card V) :
    IsCliqueFamilyBounded r D θ := by
  intro S
  have heq := degree_boundary (r := r + 1) (indicator D) S.val
    (by rw [S.property]; omega)
  rw [S.property, show r + 1 - r = 1 by omega, Nat.choose_one_right, degree_indicator] at heq
  rw [heq]
  have hc : ((D.filter fun Q => S.val ⊆ Q.val).card : ℝ) ≤ D.card := by
    exact_mod_cast card_le_card (filter_subset (fun Q => S.val ⊆ Q.val) D)
  have hbound := mul_le_mul_of_nonneg_left hc (Nat.cast_nonneg (q - r) : (0 : ℝ) ≤ _)
  push_cast
  exact hbound.trans_lt hθ

end Arxiv2411_18291
