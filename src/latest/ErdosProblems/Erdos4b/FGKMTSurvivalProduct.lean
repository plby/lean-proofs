/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTReweightedEdges

/-! # Finite survival products and the independent-intersection correction -/

namespace Erdos4b.FGKMT.FiniteEdgeFamily

noncomputable section

open scoped BigOperators

variable {α : Type*} [DecidableEq α]

theorem survivalProduct_union_inter (P : α → ℝ) (A B : Finset α) :
    survivalProduct P (A ∪ B) * survivalProduct P (A ∩ B) =
      survivalProduct P A * survivalProduct P B := Finset.prod_union_inter

theorem survivalProduct_union_ratio {P : α → ℝ} {V A B : Finset α}
    (hP : ∀ v ∈ V, 0 < P v) (hA : A ⊆ V) (hB : B ⊆ V) :
    survivalProduct P (A ∪ B) / (survivalProduct P A * survivalProduct P B) =
      1 / survivalProduct P (A ∩ B) := by
  have ha := survivalProduct_pos (fun v hv => hP v (hA hv))
  have hb := survivalProduct_pos (fun v hv => hP v (hB hv))
  have hi := survivalProduct_pos (A := A ∩ B)
    (fun v hv => hP v (hA (Finset.mem_inter.mp hv).1))
  apply (div_eq_div_iff (mul_ne_zero ha.ne' hb.ne') hi.ne').mpr
  simpa only [one_mul] using survivalProduct_union_inter P A B

omit [DecidableEq α] in
theorem survivalProduct_le_one {P : α → ℝ} {A : Finset α}
    (hP0 : ∀ v ∈ A, 0 ≤ P v) (hP1 : ∀ v ∈ A, P v ≤ 1) :
    survivalProduct P A ≤ 1 := Finset.prod_le_one hP0 hP1

omit [DecidableEq α] in
theorem survivalProduct_ge_pow {P : α → ℝ} {A : Finset α} {κ : ℝ} {r : ℕ}
    (hκ0 : 0 ≤ κ) (hκ1 : κ ≤ 1) (hP : ∀ v ∈ A, κ ≤ P v) (hcard : A.card ≤ r) :
    κ ^ r ≤ survivalProduct P A := by
  calc
    _ ≤ κ ^ A.card := pow_le_pow_of_le_one hκ0 hκ1 hcard
    _ = ∏ _v ∈ A, κ := by simp
    _ ≤ _ := Finset.prod_le_prod (fun _v _hv => hκ0) hP

theorem survivalProduct_inter_inv_le {P : α → ℝ} {V A B : Finset α}
    {κ : ℝ} {r : ℕ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1)
    (hP : ∀ v ∈ V, κ ≤ P v) (hA : A ⊆ V) (hcard : A.card ≤ r) :
    1 / survivalProduct P (A ∩ B) ≤
      1 + if (A ∩ B).Nonempty then 1 / κ ^ r else 0 := by
  by_cases h : (A ∩ B).Nonempty
  · rw [if_pos h]
    have hprod := survivalProduct_ge_pow (A := A ∩ B) hκ0.le hκ1
      (fun v hv => hP v (hA (Finset.mem_inter.mp hv).1))
      ((Finset.card_le_card Finset.inter_subset_left).trans hcard)
    have hle := one_div_le_one_div_of_le (pow_pos hκ0 r) hprod
    linarith
  · rw [if_neg h, Finset.not_nonempty_iff_eq_empty.mp h]
    simp [survivalProduct]

end

end Erdos4b.FGKMT.FiniteEdgeFamily
