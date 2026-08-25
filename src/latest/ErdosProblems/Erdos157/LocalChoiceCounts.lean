import ErdosProblems.Erdos157.LocalEncoding
import ErdosProblems.Erdos157.MaskTargetCounts

/-! Finite counts for one polynomial's random tags, auxiliary digits, and top digit. -/

namespace Erdos157.Elementary

def blockChoiceEquiv (i : ℕ) : BlockChoice i ≃ TagField i × (BlockAuxIndex i → AuxiliaryDigit) where
  toFun c := (c.tag, c.auxiliary)
  invFun c := ⟨c.1, c.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable instance blockChoiceFintype (i : ℕ) : Fintype (BlockChoice i) :=
  Fintype.ofEquiv _ (blockChoiceEquiv i).symm

instance blockChoiceNonempty (i : ℕ) : Nonempty (BlockChoice i) :=
  ⟨⟨0, fun _ => ⟨10, by decide⟩⟩⟩

theorem card_blockAuxIndex (i : ℕ) : Fintype.card (BlockAuxIndex i) = 2 * i + 5 := by
  simp only [BlockAuxIndex, Fintype.card_sum, Fintype.card_unit, Fintype.card_fin]
  omega

theorem card_blockChoice (i : ℕ) :
    Fintype.card (BlockChoice i) = Fintype.card (TagField i) * 15 ^ (2 * i + 5) := by
  rw [Fintype.card_congr (blockChoiceEquiv i), Fintype.card_prod, Fintype.card_fun,
    auxiliaryDigit_card, card_blockAuxIndex]

theorem sum_blockAuxIndex (k : ℕ) : (∑ i : Fin k, (2 * i.1 + 5)) = k ^ 2 + 4 * k := by
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => 2 * i + 5) k]
  induction k with
  | zero => simp
  | succ k ih => rw [Finset.sum_range_succ, ih]; ring

open AuxiliaryModuli

variable (K : Type*) [Field K] [DecidableEq K] [Fintype K] [CharP K 2]

theorem card_localChoice_le (k : ℕ) :
    Fintype.card (LocalChoice K k) ≤
      (7 ^ (k * (k + 2)) * 15 ^ (k ^ 2 + 4 * k)) * Fintype.card K ^ (3 * k) := by
  classical
  change Fintype.card ((∀ i : Fin k, BlockChoice i) × Fin (Fintype.card K ^ (3 * k))) ≤ _
  rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_pi]
  simp_rw [card_blockChoice]
  rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, sum_blockAuxIndex]
  apply Nat.mul_le_mul_right
  apply Nat.mul_le_mul_right
  simpa only [Fintype.card_pi] using card_tagVector_le k

theorem card_localChoice_coefficientField_le (k : ℕ) :
    Fintype.card (LocalChoice CoefficientField k) ≤ 2 ^ (7 * k ^ 2 + 3094 * k) := by
  calc
    _ ≤ (7 ^ (k * (k + 2)) * 15 ^ (k ^ 2 + 4 * k)) *
        Fintype.card CoefficientField ^ (3 * k) := card_localChoice_le CoefficientField k
    _ ≤ ((2 ^ 3) ^ (k * (k + 2)) * (2 ^ 4) ^ (k ^ 2 + 4 * k)) *
        Fintype.card CoefficientField ^ (3 * k) :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul (Nat.pow_le_pow_left (by decide) _)
        (Nat.pow_le_pow_left (by decide) _))
    _ = _ := by
      rw [card_coefficientField, ← pow_mul, ← pow_mul, ← pow_mul, ← pow_add, ← pow_add]
      congr 1
      ring

end Erdos157.Elementary
