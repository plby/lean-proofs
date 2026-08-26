import ErdosProblems.Erdos1148.RealDirichletImprimitiveSiegel
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol

/-! # A quadratic Dirichlet character with modulus four times the radicand -/

namespace Erdos1148.DukeArithmetic

def quadraticCharacterValue (a n : ℕ) : ℤ :=
  if Odd n then jacobiSym (a : ℤ) n else 0

@[simp] lemma quadraticCharacterValue_one (a : ℕ) : quadraticCharacterValue a 1 = 1 := by
  simp [quadraticCharacterValue, jacobiSym.one_right]

lemma quadraticCharacterValue_mul (a n m : ℕ) :
    quadraticCharacterValue a (n * m) = quadraticCharacterValue a n * quadraticCharacterValue a m := by
  by_cases hn : Odd n
  · by_cases hm : Odd m
    · have hn0 : n ≠ 0 := by intro h; subst n; simpa using hn
      have hm0 : m ≠ 0 := by intro h; subst m; simpa using hm
      rw [quadraticCharacterValue, if_pos (hn.mul hm), quadraticCharacterValue, if_pos hn,
        quadraticCharacterValue, if_pos hm, jacobiSym.mul_right' _ hn0 hm0]
    · simp only [quadraticCharacterValue, Nat.odd_mul, hn, hm, and_false, if_false, mul_zero]
  · simp only [quadraticCharacterValue, Nat.odd_mul, hn, false_and, if_false, zero_mul]

lemma quadraticCharacterValue_mod (a n : ℕ) :
    quadraticCharacterValue a n = quadraticCharacterValue a (n % (4 * a)) := by
  have htwo : 2 ∣ 4 * a := ⟨2 * a, by ring⟩
  have hodd : Odd (n % (4 * a)) ↔ Odd n := by
    rw [Nat.odd_iff, Nat.odd_iff, Nat.mod_mod_of_dvd _ htwo]
  by_cases hn : Odd n
  · rw [quadraticCharacterValue, if_pos hn, quadraticCharacterValue, if_pos (hodd.mpr hn),
      jacobiSym.mod_right' a hn]
  · simp only [quadraticCharacterValue, hn, hodd, if_false]

lemma quadraticCharacterValue_eq_zero_of_not_coprime (a n : ℕ)
    (hn : ¬n.Coprime (4 * a)) : quadraticCharacterValue a n = 0 := by
  by_cases hodd : Odd n
  · rw [quadraticCharacterValue, if_pos hodd]
    have hn0 : n ≠ 0 := by intro h; subst n; simpa using hodd
    have hn4 : n.Coprime 4 := by
      simpa only [show (2 : ℕ) ^ 2 = 4 by norm_num] using hodd.coprime_two_right.pow_right 2
    have hna : ¬n.Coprime a := fun h => hn (hn4.mul_right h)
    apply jacobiSym.eq_zero_iff.mpr
    refine ⟨hn0, ?_⟩
    simpa only [Int.gcd_natCast_natCast, Nat.gcd_comm, Nat.coprime_iff_gcd_eq_one] using hna
  · simp only [quadraticCharacterValue, hodd, if_false]

def integralQuadraticDirichletCharacter (a : ℕ) [NeZero a] : DirichletCharacter ℤ (4 * a) where
  toFun x := quadraticCharacterValue a x.val
  map_one' := by
    rw [ZMod.val_one'' (by nlinarith [NeZero.pos a] : 4 * a ≠ 1), quadraticCharacterValue_one]
  map_mul' := by
    intro x y
    rw [ZMod.val_mul, ← quadraticCharacterValue_mod, quadraticCharacterValue_mul]
  map_nonunit' := by
    intro x hx
    apply quadraticCharacterValue_eq_zero_of_not_coprime
    intro h
    apply hx
    have hu := (ZMod.isUnit_iff_coprime x.val (4 * a)).mpr h
    simpa only [ZMod.natCast_zmod_val] using hu

def quadraticDirichletCharacter (a : ℕ) [NeZero a] : DirichletCharacter ℝ (4 * a) :=
  (integralQuadraticDirichletCharacter a).ringHomComp (Int.castRingHom ℝ)

theorem quadraticDirichletCharacter_apply_nat (a : ℕ) [NeZero a] (n : ℕ) :
    quadraticDirichletCharacter a n = (quadraticCharacterValue a n : ℝ) := by
  change (quadraticCharacterValue a ((n : ZMod (4 * a)).val) : ℝ) = _
  rw [ZMod.val_natCast, ← quadraticCharacterValue_mod]

end Erdos1148.DukeArithmetic
