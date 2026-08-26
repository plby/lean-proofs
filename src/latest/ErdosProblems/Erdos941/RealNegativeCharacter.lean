import ErdosProblems.Erdos941.NegativeLValue
import ErdosProblems.Erdos941.RealDirichletLFunction

/-! # The real negative quadratic character and its standard L-value -/

namespace Erdos941

def realNegativeQuadraticCharacter (n : ℕ) [NeZero n] : DirichletCharacter ℝ (4 * n) :=
  (integralNegativeQuadraticCharacter n).ringHomComp (Int.castRingHom ℝ)

theorem complexify_realNegativeQuadraticCharacter (n : ℕ) [NeZero n] :
    Analytic.complexDirichletCharacter (realNegativeQuadraticCharacter n) =
      negativeQuadraticCharacter n := by
  apply DFunLike.ext
  intro a
  change ((negativeCharacterValue n a.val : ℝ) : ℂ) =
    (negativeCharacterValue n a.val : ℂ)
  exact_mod_cast rfl

theorem realNegativeQuadraticCharacter_apply_nat (n : ℕ) [NeZero n] (a : ℕ) :
    realNegativeQuadraticCharacter n a = (negativeCharacterValue n a : ℝ) := by
  change (negativeCharacterValue n ((a : ZMod (4 * n)).val) : ℝ) = _
  rw [ZMod.val_natCast, ← negativeCharacterValue_mod]

theorem realNegativeQuadraticCharacter_ne_one (n : ℕ) [NeZero n] :
    realNegativeQuadraticCharacter n ≠ 1 := by
  intro h
  have hh := complexify_realNegativeQuadraticCharacter n
  rw [h, Analytic.complexDirichletCharacter, MulChar.ringHomComp_one] at hh
  exact negativeQuadraticCharacter_ne_one n hh.symm

theorem realNegativeQuadraticCharacter_prime (n : ℕ) [NeZero n] {p : ℕ}
    [hp : Fact p.Prime] (hp2 : p ≠ 2) :
    realNegativeQuadraticCharacter n p = (legendreSym p (-(n : ℤ)) : ℝ) := by
  rw [realNegativeQuadraticCharacter_apply_nat, negativeCharacterValue,
    if_pos (hp.out.odd_of_ne_two hp2), ← jacobiSym.legendreSym.to_jacobiSym]

theorem realNegativeDirichletValue_eq (n : ℕ) [NeZero n] :
    Analytic.realDirichletValue (realNegativeQuadraticCharacter n) 1 =
      ((negativeQuadraticCharacter n).LFunction 1).re := by
  have h := Analytic.realDirichletValue_one_eq_LFunction
    (realNegativeQuadraticCharacter n) (realNegativeQuadraticCharacter_ne_one n)
  rw [complexify_realNegativeQuadraticCharacter] at h
  exact congrArg Complex.re h

theorem exists_realNegativeDirichletValue_lower {δ : ℝ} (hδ : 0 < δ) :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, ∀ [NeZero n],
      c * (n : ℝ) ^ (-δ) ≤ Analytic.realDirichletValue (realNegativeQuadraticCharacter n) 1 := by
  obtain ⟨c, hc, hbound⟩ := exists_negative_LValue_lower hδ
  exact ⟨c, hc, fun n _ => by rw [realNegativeDirichletValue_eq]; exact hbound n⟩

end Erdos941
