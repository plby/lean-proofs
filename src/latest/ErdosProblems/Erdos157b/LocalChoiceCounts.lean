import ErdosProblems.Erdos157b.LocalEncoding
import ErdosProblems.Erdos157.MaskTargetCounts

namespace Erdos157.Binary

open Erdos157.Elementary

def blockChoiceEquiv (i : ℕ) : BlockChoice i ≃ TagField i × (BlockAuxIndex i → AuxiliaryDigit) where
  toFun c := (c.tag, c.auxiliary)
  invFun c := ⟨c.1, c.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable instance blockChoiceFintype (i : ℕ) : Fintype (BlockChoice i) :=
  Fintype.ofEquiv _ (blockChoiceEquiv i).symm

instance blockChoiceNonempty (i : ℕ) : Nonempty (BlockChoice i) :=
  ⟨⟨0, fun _ => ⟨10, by decide⟩⟩⟩

theorem card_blockAuxIndex (i : ℕ) : Fintype.card (BlockAuxIndex i) = 1 + 2 * tagDimension i := by
  simp only [BlockAuxIndex, Fintype.card_sum, Fintype.card_unit, Fintype.card_fin]
  omega

theorem card_blockChoice (i : ℕ) :
    Fintype.card (BlockChoice i) = Fintype.card (TagField i) * 15 ^ (1 + 2 * tagDimension i) := by
  rw [Fintype.card_congr (blockChoiceEquiv i), Fintype.card_prod, Fintype.card_fun,
    auxiliaryDigit_card, card_blockAuxIndex]


def choiceExponent (k : ℕ) : ℕ := 11 * k * tagDimension k + 7 * k

theorem card_localChoice_binary_le (k : ℕ) :
    Fintype.card (LocalChoice CoefficientField k) ≤ 2 ^ choiceExponent k := by
  classical
  change Fintype.card ((∀ i : Fin k, BlockChoice i) × Fin (Fintype.card CoefficientField ^ (3 * k))) ≤ _
  rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_pi, card_coefficientField]
  have hb (i : Fin k) : Fintype.card (BlockChoice i) ≤ 2 ^ (11 * tagDimension k + 4) := by
    rw [card_blockChoice, card_tagField]
    calc
      _ ≤ (2 ^ 3) ^ tagDimension i * (2 ^ 4) ^ (1 + 2 * tagDimension i) :=
        Nat.mul_le_mul (Nat.pow_le_pow_left (by decide) _) (Nat.pow_le_pow_left (by decide) _)
      _ = 2 ^ (11 * tagDimension i + 4) := by
        rw [← pow_mul, ← pow_mul, ← pow_add]
        congr 1
        ring
      _ ≤ _ := Nat.pow_le_pow_right (by decide)
        (by have := tagDimension_mono i.2.le; omega)
  calc
    _ ≤ (∏ _i : Fin k, 2 ^ (11 * tagDimension k + 4)) * 2 ^ (3 * k) :=
      Nat.mul_le_mul_right _ (Finset.prod_le_prod (fun _ _ => Nat.zero_le _) (fun i _ => hb i))
    _ = _ := by
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      rw [← pow_mul, ← pow_add]
      congr 1
      unfold choiceExponent
      ring

end Erdos157.Binary
