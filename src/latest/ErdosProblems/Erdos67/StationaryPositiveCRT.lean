import ErdosProblems.Erdos67.StationaryEulerLowerBound

/-!
# Positive CRT representatives for elementary counting

For one prescribed unit class modulo `q`, the units modulo a coprime modulus
`P` give `φ(P)` distinct positive integers below `2qP`. They remain coprime to
`P`, making them suitable for a finite union bound over omitted prime factors.
-/

open scoped BigOperators
open Finset

namespace Erdos67.StationaryModel

def positiveCRT (q P : ℕ+) (hcop : Nat.Coprime q.val P.val)
    (a : (ZMod q.val)ˣ) (b : (ZMod P.val)ˣ) : ℕ :=
  q.val * P.val + (Nat.chineseRemainder hcop (a : ZMod q.val).val (b : ZMod P.val).val).val

theorem positiveCRT_pos (q P : ℕ+) (hcop : Nat.Coprime q.val P.val)
    (a : (ZMod q.val)ˣ) (b : (ZMod P.val)ˣ) : 0 < positiveCRT q P hcop a b := by
  unfold positiveCRT
  exact lt_of_lt_of_le (Nat.mul_pos q.pos P.pos) (Nat.le_add_right _ _)

theorem positiveCRT_lt (q P : ℕ+) (hcop : Nat.Coprime q.val P.val)
    (a : (ZMod q.val)ˣ) (b : (ZMod P.val)ˣ) : positiveCRT q P hcop a b < 2 * (q.val * P.val) := by
  have ht := Nat.chineseRemainder_lt_mul hcop (a : ZMod q.val).val (b : ZMod P.val).val
    q.pos.ne' P.pos.ne'
  unfold positiveCRT
  omega

theorem positiveCRT_cast_left (q P : ℕ+) (hcop : Nat.Coprime q.val P.val)
    (a : (ZMod q.val)ˣ) (b : (ZMod P.val)ˣ) :
    (positiveCRT q P hcop a b : ZMod q.val) = a := by
  have ht := (Nat.chineseRemainder hcop (a : ZMod q.val).val (b : ZMod P.val).val).property.1
  have hc := (ZMod.natCast_eq_natCast_iff _ _ q.val).mpr ht
  simpa only [positiveCRT, Nat.cast_add, Nat.cast_mul, ZMod.natCast_self, zero_mul,
    zero_add, ZMod.natCast_zmod_val] using hc

theorem positiveCRT_cast_right (q P : ℕ+) (hcop : Nat.Coprime q.val P.val)
    (a : (ZMod q.val)ˣ) (b : (ZMod P.val)ˣ) :
    (positiveCRT q P hcop a b : ZMod P.val) = b := by
  have ht := (Nat.chineseRemainder hcop (a : ZMod q.val).val (b : ZMod P.val).val).property.2
  have hc := (ZMod.natCast_eq_natCast_iff _ _ P.val).mpr ht
  simpa only [positiveCRT, Nat.cast_add, Nat.cast_mul, ZMod.natCast_self, mul_zero,
    zero_add, ZMod.natCast_zmod_val] using hc

theorem positiveCRT_injective (q P : ℕ+) (hcop : Nat.Coprime q.val P.val)
    (a : (ZMod q.val)ˣ) : Function.Injective (positiveCRT q P hcop a) := by
  intro b c hbc
  apply Units.ext
  have ht := congrArg (fun n : ℕ ↦ (n : ZMod P.val)) hbc
  simpa only [positiveCRT_cast_right] using ht

theorem positiveCRT_coprime_left (q P : ℕ+) (hcop : Nat.Coprime q.val P.val)
    (a : (ZMod q.val)ˣ) (b : (ZMod P.val)ˣ) :
    Nat.Coprime (positiveCRT q P hcop a b) q.val := by
  apply (ZMod.isUnit_iff_coprime _ _).mp
  rw [positiveCRT_cast_left]
  exact a.isUnit

theorem positiveCRT_coprime_right (q P : ℕ+) (hcop : Nat.Coprime q.val P.val)
    (a : (ZMod q.val)ˣ) (b : (ZMod P.val)ˣ) :
    Nat.Coprime (positiveCRT q P hcop a b) P.val := by
  apply (ZMod.isUnit_iff_coprime _ _).mp
  rw [positiveCRT_cast_right]
  exact b.isUnit

theorem residueUnit_positiveCRT (q P : ℕ+) (hcop : Nat.Coprime q.val P.val)
    (a : (ZMod q.val)ˣ) (b : (ZMod P.val)ˣ) : residueUnit q (positiveCRT q P hcop a b) = a := by
  apply Units.ext
  rw [coe_residueUnit q _ (positiveCRT_coprime_left q P hcop a b), positiveCRT_cast_left]

theorem card_positiveCRT_image (q P : ℕ+) (hcop : Nat.Coprime q.val P.val)
    (a : (ZMod q.val)ˣ) : (univ.image (positiveCRT q P hcop a)).card = P.val.totient := by
  rw [card_image_of_injective _ (positiveCRT_injective q P hcop a), card_univ,
    ZMod.card_units_eq_totient]

end Erdos67.StationaryModel
