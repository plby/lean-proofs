import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

/-!
# Classifying quadratic characters on finite fields
-/

namespace Pollack17

theorem quadratic_apply_square_unit {R : Type*} [CommMonoid R]
    (χ : MulChar R ℂ) (hχ : χ.IsQuadratic) {x : R} (hx : IsUnit x) (hsq : IsSquare x) :
    χ x = 1 := by
  obtain ⟨r, rfl⟩ := hsq
  have hr : IsUnit r := (IsUnit.mul_iff.mp hx).1
  have hrnz : χ r ≠ 0 := MulChar.apply_ne_zero_iff.mpr hr
  rw [map_mul]
  rcases hχ r with h | h | h
  · exact (hrnz h).elim
  · simp [h]
  · simp [h]

theorem quadratic_field_eq_quadraticChar {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (χ : MulChar F ℂ) (hχ : χ.IsQuadratic) (hne : χ ≠ 1) :
    ∀ x : F, χ x = (quadraticChar F x : ℂ) := by
  classical
  obtain ⟨a, ha⟩ := MulChar.ne_one_iff.mp hne
  have ha0 : χ (a : F) ≠ 0 := MulChar.apply_ne_zero_iff.mpr a.isUnit
  have haχ : χ (a : F) = -1 := by
    rcases hχ a with h | h | h
    · exact (ha0 h).elim
    · exact (ha h).elim
    · exact h
  have hansq : ¬IsSquare (a : F) := fun h =>
    ha (quadratic_apply_square_unit χ hχ a.isUnit h)
  have haq : quadraticChar F (a : F) = -1 := quadraticChar_neg_one_iff_not_isSquare.mpr hansq
  intro x
  by_cases hx : x = 0
  · subst x
    simp only [quadraticChar_zero, Int.cast_zero]
    exact χ.map_nonunit not_isUnit_zero
  by_cases hxsq : IsSquare x
  · rw [quadratic_apply_square_unit χ hχ (isUnit_iff_ne_zero.mpr hx) hxsq,
      (quadraticChar_one_iff_isSquare hx).mpr hxsq]
    norm_num
  have hxq : quadraticChar F x = -1 := quadraticChar_neg_one_iff_not_isSquare.mpr hxsq
  have hxaq : quadraticChar F (x * a) = 1 := by rw [map_mul, hxq, haq]; norm_num
  have hxasq : IsSquare (x * (a : F)) :=
    (quadraticChar_one_iff_isSquare (mul_ne_zero hx a.ne_zero)).mp hxaq
  have hxachi := quadratic_apply_square_unit χ hχ
    ((isUnit_iff_ne_zero.mpr hx).mul a.isUnit) hxasq
  rw [map_mul, haχ] at hxachi
  rw [hxq]
  linear_combination -hxachi

end Pollack17
