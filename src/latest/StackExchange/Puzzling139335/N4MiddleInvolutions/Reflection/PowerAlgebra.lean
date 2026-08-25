import Mathlib.Analysis.Complex.Circle

/-!
# Small powers of a unit complex number

Unless one of the first three powers is `1` or `-1`, the first four powers
and their negatives give eight distinct complex numbers.  The only cubic
calculation needed below is the real part of a nonidentity cube root of one.
-/

namespace Puzzling139335.N4MiddleInvolutions.Reflection

open ComplexConjugate

/-- Equality up to sign between two powers gives the corresponding small
power equal to `1` or `-1`. -/
theorem pow_sub_eq_one_or_neg_one {a : ℂ} (ha : a ≠ 0)
    {i j : ℕ} (hij : i ≤ j)
    (heq : a ^ i = a ^ j ∨ a ^ i = -(a ^ j)) :
    a ^ (j - i) = 1 ∨ a ^ (j - i) = -1 := by
  have hj : a ^ j = a ^ (j - i) * a ^ i := by
    rw [← pow_add, Nat.sub_add_cancel hij]
  rcases heq with heq | heq
  · left
    apply (mul_eq_right₀ (pow_ne_zero i ha)).mp
    rw [← hj, heq]
  · right
    apply mul_right_cancel₀ (pow_ne_zero i ha)
    rw [← hj, neg_one_mul]
    simpa using (congrArg Neg.neg heq).symm

/-- Purely algebraic version of the eight distinct signed powers. -/
theorem signed_powers_injective_of_complex (a : ℂ) (ha : a ≠ 0)
    (hpow : ∀ n : ℕ, 0 < n → n ≤ 3 → a ^ n ≠ 1 ∧ a ^ n ≠ -1) :
    Function.Injective (fun kb : Fin 4 × Bool =>
      (if kb.2 then (-1 : ℂ) else 1) * a ^ kb.1.val) := by
  have hno : ∀ {i j : ℕ}, j ≤ 3 → i < j →
      ¬ (a ^ i = a ^ j ∨ a ^ i = -(a ^ j)) := by
    intro i j hj hij heq
    have hne := hpow (j - i) (Nat.sub_pos_of_lt hij) ((Nat.sub_le j i).trans hj)
    rcases pow_sub_eq_one_or_neg_one ha hij.le heq with h | h
    · exact hne.1 h
    · exact hne.2 h
  rintro ⟨i, b⟩ ⟨j, d⟩ h
  have hsign : a ^ i.val = a ^ j.val ∨ a ^ i.val = -(a ^ j.val) := by
    cases b <;> cases d <;>
      simp only [Bool.false_eq_true, ↓reduceIte, one_mul, neg_one_mul, neg_inj] at h
    · exact Or.inl h
    · exact Or.inr h
    · exact Or.inr (by simpa using congrArg Neg.neg h)
    · exact Or.inl h
  have hij : i = j := by
    rcases lt_trichotomy i.val j.val with hlt | heq | hgt
    · exact (hno (Nat.le_of_lt_succ j.isLt) hlt hsign).elim
    · exact Fin.ext heq
    · have hsign' : a ^ j.val = a ^ i.val ∨ a ^ j.val = -(a ^ i.val) := by
        rcases hsign with hsign | hsign
        · exact Or.inl hsign.symm
        · exact Or.inr (by simpa using (congrArg Neg.neg hsign).symm)
      exact (hno (Nat.le_of_lt_succ i.isLt) hgt hsign').elim
  subst j
  apply Prod.ext
  · rfl
  · have hs : (if b then (-1 : ℂ) else 1) = (if d then (-1 : ℂ) else 1) :=
      mul_right_cancel₀ (pow_ne_zero i.val ha) h
    cases b <;> cases d <;> first | rfl | norm_num at hs

/-- The first four powers of a unit complex number and their negatives
are distinct when its first three powers avoid both `1` and `-1`. -/
theorem signed_powers_injective (a : Circle)
    (hpow : ∀ n : ℕ, 0 < n → n ≤ 3 → a ^ n ≠ 1 ∧ a ^ n ≠ -1) :
    Function.Injective (fun kb : Fin 4 × Bool =>
      (if kb.2 then (-1 : ℂ) else 1) * (a : ℂ) ^ kb.1.val) := by
  apply signed_powers_injective_of_complex (a : ℂ) (Circle.coe_ne_zero a)
  intro n hn hn3
  constructor
  · intro he
    apply (hpow n hn hn3).1
    apply Circle.coe_injective
    simpa only [Circle.coe_pow, Circle.coe_one] using he
  · intro he
    apply (hpow n hn hn3).2
    apply Circle.coe_injective
    simpa only [Circle.coe_pow, Circle.coe_neg, Circle.coe_one] using he

/-- A nonidentity cube root of one on the unit circle has real part `-1/2`. -/
theorem re_eq_neg_half_of_cube_eq_one
    (a : Circle) (ha3 : a ^ 3 = 1) (ha : a ≠ 1) :
    (a : ℂ).re = -1 / 2 := by
  have h3 : (a : ℂ) ^ 3 = 1 := by
    simpa using congrArg (fun b : Circle => (b : ℂ)) ha3
  have hne : (a : ℂ) ≠ 1 := fun he => ha (Circle.coe_eq_one.mp he)
  have hfactor : ((a : ℂ) - 1) * ((a : ℂ) ^ 2 + (a : ℂ) + 1) = 0 := by
    calc
      _ = (a : ℂ) ^ 3 - 1 := by ring
      _ = 0 := by rw [h3, sub_self]
  have hquad : (a : ℂ) ^ 2 + (a : ℂ) + 1 = 0 :=
    (mul_eq_zero.mp hfactor).resolve_left (sub_ne_zero.mpr hne)
  have hsqA : a ^ 2 = a⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    simpa only [← pow_succ] using ha3
  have hsq : (a : ℂ) ^ 2 = conj (a : ℂ) := by
    simpa only [Circle.coe_pow, Circle.coe_inv_eq_conj] using
      congrArg (fun b : Circle => (b : ℂ)) hsqA
  rw [hsq] at hquad
  have hr := congrArg Complex.re hquad
  simp only [Complex.add_re, Complex.conj_re, Complex.one_re, Complex.zero_re] at hr
  linarith

end Puzzling139335.N4MiddleInvolutions.Reflection
