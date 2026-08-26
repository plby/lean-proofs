import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.Tactic

/-!
# The quadratic character associated with a negative radicand

The construction follows the periodic-Jacobi-symbol construction used for positive
radicands in `Erdos1148/QuadraticDirichletCharacter.lean`.
-/

namespace Erdos941

def negativeCharacterValue (n a : ℕ) : ℤ :=
  if Odd a then jacobiSym (-(n : ℤ)) a else 0

theorem negativeCharacterValue_one (n : ℕ) : negativeCharacterValue n 1 = 1 := by
  simp [negativeCharacterValue, jacobiSym.one_right]

theorem negativeCharacterValue_mul (n a b : ℕ) :
    negativeCharacterValue n (a * b) = negativeCharacterValue n a * negativeCharacterValue n b := by
  by_cases ha : Odd a
  · by_cases hb : Odd b
    · rw [negativeCharacterValue, if_pos (ha.mul hb), negativeCharacterValue, if_pos ha,
        negativeCharacterValue, if_pos hb, jacobiSym.mul_right' _ ha.pos.ne' hb.pos.ne']
    · simp only [negativeCharacterValue, Nat.odd_mul, ha, hb, and_false, if_false, mul_zero]
  · simp only [negativeCharacterValue, Nat.odd_mul, ha, false_and, if_false, zero_mul]

theorem negativeCharacterValue_mod (n a : ℕ) :
    negativeCharacterValue n a = negativeCharacterValue n (a % (4 * n)) := by
  have htwo : 2 ∣ 4 * n := ⟨2 * n, by ring⟩
  have hodd : Odd (a % (4 * n)) ↔ Odd a := by
    rw [Nat.odd_iff, Nat.odd_iff, Nat.mod_mod_of_dvd _ htwo]
  by_cases ha : Odd a
  · rw [negativeCharacterValue, if_pos ha, negativeCharacterValue, if_pos (hodd.mpr ha)]
    simpa using jacobiSym.mod_right (-(n : ℤ)) ha
  · simp only [negativeCharacterValue, ha, hodd, if_false]

theorem negativeCharacterValue_zero_of_not_coprime (n a : ℕ)
    (ha : ¬a.Coprime (4 * n)) : negativeCharacterValue n a = 0 := by
  by_cases hodd : Odd a
  · rw [negativeCharacterValue, if_pos hodd]
    have ha4 : a.Coprime 4 := by
      simpa only [show (2 : ℕ) ^ 2 = 4 by norm_num] using hodd.coprime_two_right.pow_right 2
    have han : ¬a.Coprime n := fun h => ha (ha4.mul_right h)
    apply jacobiSym.eq_zero_iff.mpr
    refine ⟨hodd.pos.ne', ?_⟩
    simpa only [Int.neg_gcd, Int.gcd_natCast_natCast, Nat.gcd_comm,
      Nat.coprime_iff_gcd_eq_one] using han
  · simp only [negativeCharacterValue, hodd, if_false]

def integralNegativeQuadraticCharacter (n : ℕ) [NeZero n] : DirichletCharacter ℤ (4 * n) where
  toFun x := negativeCharacterValue n x.val
  map_one' := by
    rw [ZMod.val_one'' (by nlinarith [NeZero.pos n] : 4 * n ≠ 1), negativeCharacterValue_one]
  map_mul' := by
    intro x y
    rw [ZMod.val_mul, ← negativeCharacterValue_mod, negativeCharacterValue_mul]
  map_nonunit' := by
    intro x hx
    apply negativeCharacterValue_zero_of_not_coprime
    intro h
    apply hx
    have hu := (ZMod.isUnit_iff_coprime x.val (4 * n)).mpr h
    simpa only [ZMod.natCast_zmod_val] using hu

def negativeQuadraticCharacter (n : ℕ) [NeZero n] : DirichletCharacter ℂ (4 * n) :=
  (integralNegativeQuadraticCharacter n).ringHomComp (Int.castRingHom ℂ)

theorem negativeQuadraticCharacter_apply_nat (n : ℕ) [NeZero n] (a : ℕ) :
    negativeQuadraticCharacter n a = (negativeCharacterValue n a : ℂ) := by
  change (negativeCharacterValue n ((a : ZMod (4 * n)).val) : ℂ) = _
  rw [ZMod.val_natCast, ← negativeCharacterValue_mod]

theorem negativeQuadraticCharacter_isQuadratic (n : ℕ) [NeZero n] :
    (negativeQuadraticCharacter n).IsQuadratic := by
  intro a
  change (negativeCharacterValue n a.val : ℂ) = 0 ∨
    (negativeCharacterValue n a.val : ℂ) = 1 ∨ (negativeCharacterValue n a.val : ℂ) = -1
  unfold negativeCharacterValue
  split_ifs with h
  · rcases jacobiSym.trichotomy (-(n : ℤ)) a.val with hz | hp | hm
    · exact Or.inl (by rw [hz]; norm_num)
    · exact Or.inr (Or.inl (by rw [hp]; norm_num))
    · exact Or.inr (Or.inr (by rw [hm]; norm_num))
  · exact Or.inl (by norm_num)

theorem negativeCharacterValue_modulus_sub_one (n : ℕ) [NeZero n] :
    negativeCharacterValue n (4 * n - 1) = -1 := by
  let m : ℕ := 4 * n - 1
  have hn : 0 < n := NeZero.pos n
  have hm4 : m % 4 = 3 := by dsimp [m]; omega
  have hmo : Odd m := Nat.odd_iff.mpr (by omega)
  have hcast : (m : ℤ) = 4 * (n : ℤ) - 1 := by
    dsimp [m]
    rw [Nat.cast_sub (by omega : 1 ≤ 4 * n)]
    push_cast
    rfl
  have h2g : Int.gcd (2 : ℤ) m = 1 := by
    change Int.gcd ((2 : ℕ) : ℤ) (m : ℤ) = 1
    rw [Int.gcd_natCast_natCast]
    exact hmo.coprime_two_left.gcd_eq_one
  have hfour : jacobiSym (4 : ℤ) m = 1 := by
    simpa using jacobiSym.sq_one' h2g
  have hmod : (4 * (-(n : ℤ))) % (m : ℤ) = (-1 : ℤ) % (m : ℤ) := by
    have heq : 4 * (-(n : ℤ)) = -1 - (m : ℤ) := by rw [hcast]; ring
    rw [heq, Int.sub_emod, Int.emod_self, sub_zero, Int.emod_emod]
  have hj : jacobiSym (4 * (-(n : ℤ))) m = -1 := by
    calc
      _ = jacobiSym (-1) m := by
        rw [jacobiSym.mod_left (4 * (-(n : ℤ))) m, jacobiSym.mod_left (-1) m, hmod]
      _ = -1 := by rw [jacobiSym.at_neg_one hmo, ZMod.χ₄_nat_three_mod_four hm4]
  rw [jacobiSym.mul_left, hfour, one_mul] at hj
  change negativeCharacterValue n m = -1
  rwa [negativeCharacterValue, if_pos hmo]

theorem negativeQuadraticCharacter_neg_one (n : ℕ) [NeZero n] :
    negativeQuadraticCharacter n (-1) = -1 := by
  have hn : 0 < n := NeZero.pos n
  have harg : ((4 * n - 1 : ℕ) : ZMod (4 * n)) = -1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ 4 * n), ZMod.natCast_self, Nat.cast_one, zero_sub]
  have h := negativeQuadraticCharacter_apply_nat n (4 * n - 1)
  rw [harg, negativeCharacterValue_modulus_sub_one] at h
  simpa using h

theorem negativeQuadraticCharacter_ne_one (n : ℕ) [NeZero n] :
    negativeQuadraticCharacter n ≠ 1 := by
  intro h
  have hh := negativeQuadraticCharacter_neg_one n
  rw [h, MulChar.one_apply isUnit_neg_one] at hh
  norm_num at hh

theorem negativeQuadraticCharacter_prime (n : ℕ) [NeZero n] {p : ℕ}
    [hp : Fact p.Prime] (hp2 : p ≠ 2) :
    negativeQuadraticCharacter n p = (legendreSym p (-(n : ℤ)) : ℂ) := by
  rw [negativeQuadraticCharacter_apply_nat, negativeCharacterValue,
    if_pos (hp.out.odd_of_ne_two hp2), ← jacobiSym.legendreSym.to_jacobiSym]

end Erdos941
