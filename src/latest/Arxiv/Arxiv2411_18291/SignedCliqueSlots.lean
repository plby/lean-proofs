import Arxiv.Arxiv2411_18291.SplittingAlgebra
import Arxiv.Arxiv2411_18291.CoefficientReduction
import Mathlib.Data.Fintype.Fin

/-!
# Fixed positive and negative slots for bounded coefficients

Allocate `C` positive and `C` negative slots per clique. Any integer
coefficient of absolute value at most `C` selects some slots of its sign.
The resulting unit coefficients recover the original boundary exactly,
and each clique occurs in the fixed root family at most `2*C` times.
-/

open Finset
open scoped BigOperators

noncomputable section

namespace Arxiv2411_18291

def signedSlotWeight {C : ℕ} (a : ℤ) (s : Bool × Fin C) : ℤ :=
  if s.1 = decide (0 ≤ a) ∧ s.2.val < a.natAbs then a.sign else 0

theorem signedSlotWeight_sign {C : ℕ} (a : ℤ) (s : Bool × Fin C) :
    signedSlotWeight a s = 0 ∨
      (s.1 = true ∧ signedSlotWeight a s = 1) ∨
      (s.1 = false ∧ signedSlotWeight a s = -1) := by
  by_cases ha : a = 0
  · simp [signedSlotWeight, ha]
  rcases lt_or_gt_of_ne ha with hneg | hpos
  · have hn : ¬0 ≤ a := not_le_of_gt hneg
    simp only [signedSlotWeight, hn, decide_false, Int.sign_eq_neg_one_of_neg hneg]
    split_ifs with h
    · exact Or.inr (Or.inr ⟨h.1, rfl⟩)
    · exact Or.inl rfl
  · simp only [signedSlotWeight, hpos.le, decide_true, Int.sign_eq_one_of_pos hpos]
    split_ifs with h
    · exact Or.inr (Or.inl ⟨h.1, rfl⟩)
    · exact Or.inl rfl

theorem signedSlotWeight_abs_le {C : ℕ} (a : ℤ) (s : Bool × Fin C) :
    |signedSlotWeight a s| ≤ 1 := by
  rcases signedSlotWeight_sign a s with h | ⟨_, h⟩ | ⟨_, h⟩ <;> rw [h] <;> norm_num

theorem sum_signedSlotWeight {C : ℕ} (a : ℤ) (ha : |a| ≤ C) :
    ∑ s : Bool × Fin C, signedSlotWeight a s = a := by
  have hC : a.natAbs ≤ C := by
    have hcast : (a.natAbs : ℤ) ≤ C := by simpa only [Int.natCast_natAbs] using ha
    exact_mod_cast hcast
  rw [Fintype.sum_prod_type, sum_comm]
  have hbool (j : Fin C) : (∑ b : Bool, signedSlotWeight a (b, j)) =
      if j.val < a.natAbs then a.sign else 0 := by
    rw [Fintype.sum_bool]
    by_cases ha0 : 0 ≤ a <;> simp [signedSlotWeight, ha0]
  simp_rw [hbool]
  rw [← sum_filter, sum_const, Fin.card_filter_val_lt, min_eq_right hC, nsmul_eq_mul,
    mul_comm, Int.sign_mul_natAbs]

variable {V : Type*} [Fintype V] [DecidableEq V] {q r C : ℕ}

abbrev SignedCliqueSlots (D : Finset (Block V q)) (C : ℕ) := D × (Bool × Fin C)

omit [Fintype V] in
theorem signedCliqueSlots_root_count (D : Finset (Block V q)) (C : ℕ) (P : Block V q) :
    (univ.filter fun s : SignedCliqueSlots D C => s.1.val = P).card ≤ 2 * C := by
  classical
  let s := univ.filter fun s : SignedCliqueSlots D C => s.1.val = P
  let f : s → Bool × Fin C := fun x => x.val.2
  have hf : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    apply Prod.ext
    · exact Subtype.ext (((mem_filter.mp x.property).2).trans ((mem_filter.mp y.property).2).symm)
    · exact hxy
  simpa only [Fintype.card_coe, Fintype.card_prod, Fintype.card_bool, Fintype.card_fin] using
    Fintype.card_le_of_injective f hf

theorem signedCliqueSlots_boundary (D : Finset (Block V q)) (Φ : Block V q → ℤ)
    (hΦ : ∀ P, |Φ P| ≤ C) (hs : ∀ P, P ∉ D → Φ P = 0) :
    (∑ s : SignedCliqueSlots D C, fun e =>
      signedSlotWeight (Φ s.1.val) s.2 * indicator (cliqueEdges r s.1.val) e) = boundary r Φ := by
  funext e
  rw [Finset.sum_apply, Fintype.sum_prod_type]
  calc
    _ = ∑ P : D, Φ P.val * indicator (cliqueEdges r P.val) e := by
      apply sum_congr rfl
      intro P _
      dsimp only
      rw [← sum_mul, sum_signedSlotWeight _ (hΦ P.val)]
    _ = _ := by
      rw [Finset.sum_coe_sort D (fun P => Φ P * indicator (cliqueEdges r P) e),
        boundary_eq_sum_supported D Φ hs e, sum_filter]
      apply sum_congr rfl
      intro P _
      simp only [indicator, mem_cliqueEdges]
      split_ifs <;> simp only [mul_one, mul_zero]

end Arxiv2411_18291
