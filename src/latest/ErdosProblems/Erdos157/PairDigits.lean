import ErdosProblems.Erdos157.Basic
import Mathlib.Data.ZMod.Basic

/-! A data digit followed by its auxiliary digit: normalization and separation. -/

namespace Erdos157.Elementary

open AuxiliaryDigits

abbrev AuxiliaryDigit := ↑auxiliaryDigitList.toFinset

theorem auxiliaryDigit_card : Fintype.card AuxiliaryDigit = 15 := by
  norm_num [AuxiliaryDigit, auxiliaryDigitList]

instance auxiliaryDigitNonempty : Nonempty AuxiliaryDigit := ⟨⟨10, by decide⟩⟩

theorem auxiliaryDigit_mem (a : AuxiliaryDigit) : (a : ℕ) ∈ auxiliaryDigitSet := a.2

theorem auxiliaryDigit_bounds (a : AuxiliaryDigit) : 1 ≤ (a : ℕ) ∧ (a : ℕ) ≤ 50 := by
  have h := explicitAuxiliarySet.1 (auxiliaryDigit_mem a)
  change 1 ≤ (a : ℕ) ∧ (a : ℕ) < 103 / 2 at h
  omega

namespace PairDigits

def pack (b x : ℕ) (a : AuxiliaryDigit) : ℕ := x + b * a.1

theorem pack_lt (b x : ℕ) (a : AuxiliaryDigit) (hx : x < b) : pack b x a < 51 * b := by
  have ha := (auxiliaryDigit_bounds a).2
  have hm := Nat.mul_le_mul_left b ha
  unfold pack
  omega

theorem pair_add_carry_lt (b x y κ : ℕ) (a c : AuxiliaryDigit)
    (hx : x < b) (hy : y < b) (hκ : κ ≤ 1) :
    pack b x a + pack b y c + κ < 103 * b := by
  have h1 := pack_lt b x a hx
  have h2 := pack_lt b y c hy
  omega

theorem pack_pair_decomposition (b x y κ : ℕ) (a c : AuxiliaryDigit) :
    pack b x a + pack b y c + κ =
      (x + y + κ) % b + b * (a.1 + c.1 + (x + y + κ) / b) := by
  have h := Nat.mod_add_div (x + y + κ) b
  unfold pack
  nlinarith

theorem pack_div (b x : ℕ) (a : AuxiliaryDigit) (hx : x < b) : pack b x a / b = a.1 := by
  unfold pack
  rw [Nat.add_mul_div_left _ _ (by omega : 0 < b), Nat.div_eq_of_lt hx, zero_add]

/-- A clean auxiliary position distinguishes one summand from two summands. -/
theorem single_ne_pair (b x y z κ : ℕ) (a c d : AuxiliaryDigit)
    (hx : x < b) (hy : y < b) (hz : z < b) (hκ : κ ≤ 1) :
    pack b x a ≠ pack b y c + pack b z d + κ := by
  intro heq
  have hb : 0 < b := lt_of_le_of_lt (Nat.zero_le _) hx
  have hcarry : (y + z + κ) / b ≤ 1 := MixedRadix.two_digit_carry_le_one hb hy hz hκ
  have hm := congrArg (fun n => n / b) heq
  rw [pack_div b x a hx, pack_pair_decomposition,
    Nat.add_mul_div_left _ _ hb, Nat.div_eq_of_lt (Nat.mod_lt _ hb), zero_add] at hm
  exact explicitAuxiliarySet.2.1 (auxiliaryDigit_mem a) (auxiliaryDigit_mem c)
    (auxiliaryDigit_mem d) hcarry hm

/-- Pair sums do not carry past the auxiliary radix. Their equality modulo
the pair radix is therefore an equality of ordinary natural numbers. -/
theorem pair_add_eq_of_modEq (b x₁ x₂ x₃ x₄ : ℕ) (a₁ a₂ a₃ a₄ : AuxiliaryDigit)
    (h₁ : x₁ < b) (h₂ : x₂ < b) (h₃ : x₃ < b) (h₄ : x₄ < b)
    (h : Nat.ModEq (103 * b) (pack b x₁ a₁ + pack b x₂ a₂) (pack b x₃ a₃ + pack b x₄ a₄)) :
    pack b x₁ a₁ + pack b x₂ a₂ = pack b x₃ a₃ + pack b x₄ a₄ := by
  have hleft := pair_add_carry_lt b x₁ x₂ 0 a₁ a₂ h₁ h₂ (by decide)
  have hright := pair_add_carry_lt b x₃ x₄ 0 a₃ a₄ h₃ h₄ (by decide)
  change (pack b x₁ a₁ + pack b x₂ a₂) % (103 * b) =
    (pack b x₃ a₃ + pack b x₄ a₄) % (103 * b) at h
  exact (Nat.mod_eq_of_lt (by simpa using hleft)).symm.trans
    (h.trans (Nat.mod_eq_of_lt (by simpa using hright)))

theorem data_pair_modEq_of_pack_pair_eq (b x₁ x₂ x₃ x₄ : ℕ) (a₁ a₂ a₃ a₄ : AuxiliaryDigit)
    (h : pack b x₁ a₁ + pack b x₂ a₂ = pack b x₃ a₃ + pack b x₄ a₄) :
    Nat.ModEq b (x₁ + x₂) (x₃ + x₄) := by
  have hp : (x₁ + x₂) + b * (a₁.1 + a₂.1) = (x₃ + x₄) + b * (a₃.1 + a₄.1) := by
    unfold pack at h
    nlinarith
  have hm := congrArg (fun n => n % b) hp
  exact_mod_cast (show (x₁ + x₂) % b = (x₃ + x₄) % b by
    simpa only [Nat.add_mul_mod_self_left] using hm)

theorem zmod_pair_eq_of_pack_pair_eq (b : ℕ) [NeZero b] (x₁ x₂ x₃ x₄ : ZMod b)
    (a₁ a₂ a₃ a₄ : AuxiliaryDigit)
    (h : pack b x₁.val a₁ + pack b x₂.val a₂ = pack b x₃.val a₃ + pack b x₄.val a₄) :
    x₁ + x₂ = x₃ + x₄ := by
  have hm := data_pair_modEq_of_pack_pair_eq b _ _ _ _ a₁ a₂ a₃ a₄ h
  have hc : ((x₁.val + x₂.val : ℕ) : ZMod b) = ((x₃.val + x₄.val : ℕ) : ZMod b) :=
    (ZMod.natCast_eq_natCast_iff _ _ _).mpr hm
  simpa only [Nat.cast_add, ZMod.natCast_zmod_val] using hc

theorem zmod_eq_of_pack_eq (b : ℕ) [NeZero b] (x y : ZMod b) (a c : AuxiliaryDigit)
    (h : pack b x.val a = pack b y.val c) : x = y := by
  have hm := congrArg (fun n => n % b) h
  have hv : x.val = y.val := by
    simpa only [pack, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (ZMod.val_lt x),
      Nat.mod_eq_of_lt (ZMod.val_lt y)] using hm
  exact ZMod.val_injective b hv

end PairDigits
end Erdos157.Elementary
