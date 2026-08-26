import ErdosProblems.Erdos633.DirectionSigns
import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-!
# Global direction characters, extended by zero

An angle-coordinate sign descends to complex directions and is extended by
zero outside its direction subgroup. The extension is odd and transforms by
the required sign under every generated rotation. Thus boundary invariants do
not require a separate proof that every tile orientation lies in the subgroup.
-/

namespace Erdos633

noncomputable def coordinateDirection (α β : ℝ) (w : ℤ × ℤ) : ℂ :=
  Complex.exp ((angleFromCoordinates α β w : ℂ) * Complex.I)

theorem coordinateDirection_ne_zero (α β : ℝ) (w : ℤ × ℤ) :
    coordinateDirection α β w ≠ 0 := Complex.exp_ne_zero _

@[simp] theorem coordinateDirection_zero (α β : ℝ) : coordinateDirection α β 0 = 1 := by
  simp [coordinateDirection, angleFromCoordinates]

theorem coordinateDirection_add (α β : ℝ) (w z : ℤ × ℤ) :
    coordinateDirection α β (w + z) =
      coordinateDirection α β w * coordinateDirection α β z := by
  have h : angleFromCoordinates α β (w + z) =
      angleFromCoordinates α β w + angleFromCoordinates α β z := by
    dsimp [angleFromCoordinates]
    push_cast
    ring
  rw [coordinateDirection, h, Complex.ofReal_add, add_mul, Complex.exp_add]
  rfl

theorem directionSign_eq_of_coordinateDirection_eq {α β : ℝ}
    (hind : IntegerIndependentAngles α β) (πc : ℤ × ℤ)
    (hπ : Real.pi = angleFromCoordinates α β πc) (u v : ℤ) (w z : ℤ × ℤ)
    (h : coordinateDirection α β w = coordinateDirection α β z) :
    directionSign u v w = directionSign u v z := by
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp h
  have hi := congrArg Complex.im hn
  have hr : angleFromCoordinates α β w =
      angleFromCoordinates α β z + 2 * n * Real.pi := by
    norm_num [Complex.mul_re, Complex.mul_im] at hi
    linarith
  exact directionSign_full_turn hind πc.1 πc.2 n u v hπ w z hr

noncomputable def extendedDirectionSign (α β : ℝ) (u v : ℤ) (z : ℂ) : ℝ := by
  classical
  exact if h : ∃ w : ℤ × ℤ, coordinateDirection α β w = z then
    directionSign u v h.choose else 0

theorem extendedDirectionSign_of_not_range (α β : ℝ) (u v : ℤ) (z : ℂ)
    (hz : ¬ ∃ w : ℤ × ℤ, coordinateDirection α β w = z) :
    extendedDirectionSign α β u v z = 0 := by
  classical
  simp only [extendedDirectionSign, dif_neg hz]

theorem extendedDirectionSign_apply_direction {α β : ℝ}
    (hind : IntegerIndependentAngles α β) (πc : ℤ × ℤ)
    (hπ : Real.pi = angleFromCoordinates α β πc) (u v : ℤ) (w : ℤ × ℤ) :
    extendedDirectionSign α β u v (coordinateDirection α β w) = directionSign u v w := by
  classical
  have hex : ∃ z : ℤ × ℤ, coordinateDirection α β z = coordinateDirection α β w := ⟨w, rfl⟩
  rw [extendedDirectionSign, dif_pos hex]
  exact directionSign_eq_of_coordinateDirection_eq hind πc hπ u v hex.choose w hex.choose_spec

theorem extendedDirectionSign_cases (α β : ℝ) (u v : ℤ) (z : ℂ) :
    extendedDirectionSign α β u v z = 0 ∨
      extendedDirectionSign α β u v z = 1 ∨ extendedDirectionSign α β u v z = -1 := by
  classical
  unfold extendedDirectionSign
  split_ifs with h
  · exact Or.inr (directionSign_cases u v h.choose)
  · exact Or.inl rfl

theorem extendedDirectionSign_rotation {α β : ℝ}
    (hind : IntegerIndependentAngles α β) (πc : ℤ × ℤ)
    (hπ : Real.pi = angleFromCoordinates α β πc) (u v : ℤ) (w : ℤ × ℤ) (z : ℂ) :
    extendedDirectionSign α β u v (coordinateDirection α β w * z) =
      directionSign u v w * extendedDirectionSign α β u v z := by
  classical
  by_cases hz : ∃ a : ℤ × ℤ, coordinateDirection α β a = z
  · obtain ⟨a, rfl⟩ := hz
    rw [← coordinateDirection_add,
      extendedDirectionSign_apply_direction hind πc hπ,
      extendedDirectionSign_apply_direction hind πc hπ, directionSign_add]
  · have hp : ¬ ∃ a : ℤ × ℤ,
        coordinateDirection α β a = coordinateDirection α β w * z := by
      rintro ⟨a, ha⟩
      apply hz
      refine ⟨a - w, ?_⟩
      apply mul_left_cancel₀ (coordinateDirection_ne_zero α β w)
      rw [← coordinateDirection_add, show w + (a - w) = a by abel]
      exact ha
    rw [extendedDirectionSign_of_not_range α β u v _ hp,
      extendedDirectionSign_of_not_range α β u v z hz, mul_zero]

theorem coordinateDirection_pi {α β : ℝ} (πc : ℤ × ℤ)
    (hπ : Real.pi = angleFromCoordinates α β πc) : coordinateDirection α β πc = -1 := by
  rw [coordinateDirection, ← hπ, Complex.exp_pi_mul_I]

theorem extendedDirectionSign_odd {α β : ℝ}
    (hind : IntegerIndependentAngles α β) (πc : ℤ × ℤ)
    (hπ : Real.pi = angleFromCoordinates α β πc) (u v : ℤ)
    (hsign : directionSign u v πc = -1) (z : ℂ) :
    extendedDirectionSign α β u v (-z) = -extendedDirectionSign α β u v z := by
  have h := extendedDirectionSign_rotation hind πc hπ u v πc z
  simpa only [coordinateDirection_pi πc hπ, hsign, neg_one_mul] using h

theorem exists_odd_direction_character {α β : ℝ}
    (hind : IntegerIndependentAngles α β) (πc : ℤ × ℤ)
    (hπ : Real.pi = angleFromCoordinates α β πc) (u v : ℤ)
    (hsign : directionSign u v πc = -1) :
    ∃ φ : ℂ → ℝ,
      (∀ z, φ (-z) = -φ z) ∧
      (∀ w, φ (coordinateDirection α β w) = directionSign u v w) ∧
      (∀ w z, φ (coordinateDirection α β w * z) = directionSign u v w * φ z) ∧
      (∀ z, φ z = 0 ∨ φ z = 1 ∨ φ z = -1) :=
  ⟨extendedDirectionSign α β u v,
    extendedDirectionSign_odd hind πc hπ u v hsign,
    extendedDirectionSign_apply_direction hind πc hπ u v,
    extendedDirectionSign_rotation hind πc hπ u v,
    extendedDirectionSign_cases α β u v⟩

end Erdos633
