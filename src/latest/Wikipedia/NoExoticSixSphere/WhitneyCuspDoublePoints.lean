import Wikipedia.NoExoticSixSphere.WhitneyCuspSingularLocus
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Exact double-point birth in the cusp family

At nonpositive parameter the map is injective. At positive parameter its
only distinct equal-image pairs are the two orderings of the points on the
last coordinate axis with coordinates `sqrt t` and `-sqrt t`.
-/

noncomputable section

open Function

namespace NoExoticSixSphere.WhitneyCusp

open GLOrthonormalization

theorem axis_ne_neg {z : ℝ} (hz : z ≠ 0) : axis z ≠ axis (-z) := by
  intro h
  have he := axis_injective h
  exact hz (by linarith)

theorem map_eq_iff (t : ℝ) (x y : Vector 3) :
    map t x = map t y ↔ x = y ∨
      ∃ z : ℝ, z ≠ 0 ∧ z ^ 2 = t ∧ x = axis z ∧ y = axis (-z) := by
  constructor
  · intro h
    by_cases hxy : x = y
    · exact Or.inl hxy
    · have h₀ : x 0 = y 0 := congrArg (fun w : Vector 6 ↦ w 0) h
      have h₁ : x 1 = y 1 := congrArg (fun w : Vector 6 ↦ w 1) h
      have h₂ : x 2 ^ 2 = y 2 ^ 2 := congrArg (fun w : Vector 6 ↦ w 2) h
      have h₃ : x 0 * x 2 = y 0 * y 2 := congrArg (fun w : Vector 6 ↦ w 3) h
      have h₄ : x 1 * x 2 = y 1 * y 2 := congrArg (fun w : Vector 6 ↦ w 4) h
      have h₅ : x 2 ^ 3 - t * x 2 = y 2 ^ 3 - t * y 2 :=
        congrArg (fun w : Vector 6 ↦ w 5) h
      have hy₂ : y 2 = -x 2 := by
        rcases sq_eq_sq_iff_eq_or_eq_neg.mp h₂ with hz | hz
        · exact (hxy (by
            ext i
            fin_cases i
            · exact h₀
            · exact h₁
            · exact hz)).elim
        · linarith
      have hz : x 2 ≠ 0 := by
        intro hx₂
        apply hxy
        ext i
        fin_cases i
        · exact h₀
        · exact h₁
        · change x 2 = y 2
          rw [hy₂, hx₂, neg_zero]
      have hx₀ : x 0 = 0 := by
        rw [← h₀, hy₂] at h₃
        have hp : x 0 * x 2 = 0 := by nlinarith
        exact (mul_eq_zero.mp hp).resolve_right hz
      have hx₁ : x 1 = 0 := by
        rw [← h₁, hy₂] at h₄
        have hp : x 1 * x 2 = 0 := by nlinarith
        exact (mul_eq_zero.mp hp).resolve_right hz
      have ht : x 2 ^ 2 = t := by
        rw [hy₂] at h₅
        have hp : x 2 * (x 2 ^ 2 - t) = 0 := by nlinarith
        exact sub_eq_zero.mp ((mul_eq_zero.mp hp).resolve_left hz)
      refine Or.inr ⟨x 2, hz, ht, ?_, ?_⟩
      · ext i
        fin_cases i
        · exact hx₀
        · exact hx₁
        · rfl
      · ext i
        fin_cases i
        · exact h₀.symm.trans hx₀
        · exact h₁.symm.trans hx₁
        · exact hy₂
  · rintro (rfl | ⟨z, _, ht, rfl, rfl⟩)
    · rfl
    · rw [← ht]
      ext i
      fin_cases i <;> simp [map, axis]
      ring

theorem injective_map_iff (t : ℝ) : Injective (map t) ↔ t ≤ 0 := by
  constructor
  · intro hi
    by_contra ht
    have ht₀ : 0 < t := lt_of_not_ge ht
    have hz : Real.sqrt t ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr ht₀)
    have he : map t (axis (Real.sqrt t)) = map t (axis (-Real.sqrt t)) :=
      (map_eq_iff t _ _).mpr (Or.inr ⟨Real.sqrt t, hz, Real.sq_sqrt ht₀.le, rfl, rfl⟩)
    exact axis_ne_neg hz (hi he)
  · intro ht x y h
    rcases (map_eq_iff t x y).mp h with he | ⟨z, hz, hzt, _, _⟩
    · exact he
    · have hp : 0 < z ^ 2 := sq_pos_of_ne_zero hz
      exfalso
      linarith

theorem double_points_iff_of_pos (t : ℝ) (ht : 0 < t) (x y : Vector 3) :
    map t x = map t y ∧ x ≠ y ↔
      (x = axis (Real.sqrt t) ∧ y = axis (-Real.sqrt t)) ∨
      (x = axis (-Real.sqrt t) ∧ y = axis (Real.sqrt t)) := by
  have hz : Real.sqrt t ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr ht)
  have he : map t (axis (Real.sqrt t)) = map t (axis (-Real.sqrt t)) :=
    (map_eq_iff t _ _).mpr (Or.inr ⟨Real.sqrt t, hz, Real.sq_sqrt ht.le, rfl, rfl⟩)
  constructor
  · rintro ⟨h, hxy⟩
    rcases (map_eq_iff t x y).mp h with h' | ⟨z, _, hzt, hx, hy⟩
    · exact (hxy h').elim
    · have hs : z ^ 2 = Real.sqrt t ^ 2 := hzt.trans (Real.sq_sqrt ht.le).symm
      rcases sq_eq_sq_iff_eq_or_eq_neg.mp hs with rfl | hneg
      · exact Or.inl ⟨hx, hy⟩
      · right
        simpa only [hneg, neg_neg] using And.intro hx hy
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact ⟨he, axis_ne_neg hz⟩
    · exact ⟨he.symm, (axis_ne_neg hz).symm⟩

end NoExoticSixSphere.WhitneyCusp
