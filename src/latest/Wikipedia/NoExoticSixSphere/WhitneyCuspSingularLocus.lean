import Wikipedia.NoExoticSixSphere.WhitneyCusp

/-!
# The exact singular locus of the cusp family

The spatial derivative loses injectivity only at parameter zero and source
zero. Its kernel there is the last source-coordinate axis.
-/

noncomputable section

open Function

namespace NoExoticSixSphere.WhitneyCusp

open GLOrthonormalization

def axis (z : ℝ) : Vector 3 := WithLp.toLp 2 ![0, 0, z]

theorem axis_injective : Injective axis := by
  intro z w h
  exact congrArg (fun x : Vector 3 ↦ x 2) h

theorem axis_zero : axis 0 = 0 := by
  ext i
  fin_cases i <;> rfl

theorem differential_kernel_iff (t : ℝ) (x v : Vector 3) :
    differential t x v = 0 ↔ v 0 = 0 ∧ v 1 = 0 ∧ (v 2 = 0 ∨ t = 0 ∧ x = 0) := by
  constructor
  · intro hv
    have h₀ : v 0 = 0 := congrArg (fun w : Vector 6 ↦ w 0) hv
    have h₁ : v 1 = 0 := congrArg (fun w : Vector 6 ↦ w 1) hv
    have h₂ : 2 * x 2 * v 2 = 0 := congrArg (fun w : Vector 6 ↦ w 2) hv
    have h₃ : x 2 * v 0 + x 0 * v 2 = 0 := congrArg (fun w : Vector 6 ↦ w 3) hv
    have h₄ : x 2 * v 1 + x 1 * v 2 = 0 := congrArg (fun w : Vector 6 ↦ w 4) hv
    have h₅ : (3 * x 2 ^ 2 - t) * v 2 = 0 := congrArg (fun w : Vector 6 ↦ w 5) hv
    refine ⟨h₀, h₁, ?_⟩
    by_cases hz : v 2 = 0
    · exact Or.inl hz
    · have hx₂ : x 2 = 0 := by
        have h := (mul_eq_zero.mp h₂).resolve_right hz
        linarith
      have hx₀ : x 0 = 0 := by
        rw [h₀, mul_zero, zero_add] at h₃
        exact (mul_eq_zero.mp h₃).resolve_right hz
      have hx₁ : x 1 = 0 := by
        rw [h₁, mul_zero, zero_add] at h₄
        exact (mul_eq_zero.mp h₄).resolve_right hz
      have ht : t = 0 := by
        have h := (mul_eq_zero.mp h₅).resolve_right hz
        rw [hx₂] at h
        nlinarith
      refine Or.inr ⟨ht, ?_⟩
      ext i
      fin_cases i
      · exact hx₀
      · exact hx₁
      · exact hx₂
  · rintro ⟨h₀, h₁, h₂ | ⟨rfl, rfl⟩⟩
    · have hv : v = 0 := by
        ext i
        fin_cases i
        · exact h₀
        · exact h₁
        · exact h₂
      rw [hv, map_zero]
    · ext i
      fin_cases i <;> simp [differential_apply, h₀, h₁]

theorem injective_differential_iff (t : ℝ) (x : Vector 3) :
    Injective (differential t x) ↔ t ≠ 0 ∨ x ≠ 0 := by
  constructor
  · intro hi
    by_cases ht : t = 0
    · right
      intro hx
      subst t
      subst x
      have hv : differential 0 0 (axis 1) = 0 :=
        (differential_kernel_iff 0 0 (axis 1)).mpr ⟨rfl, rfl, Or.inr ⟨rfl, rfl⟩⟩
      have hz := (injective_iff_map_eq_zero _).mp hi _ hv
      exact one_ne_zero (congrArg (fun w : Vector 3 ↦ w 2) hz)
    · exact Or.inl ht
  · intro hi
    apply (injective_iff_map_eq_zero _).mpr
    intro v hv
    obtain ⟨h₀, h₁, h₂ | ⟨ht, hx⟩⟩ := (differential_kernel_iff t x v).mp hv
    · ext i
      fin_cases i
      · exact h₀
      · exact h₁
      · exact h₂
    · exact (hi.elim (fun h ↦ h ht) (fun h ↦ h hx)).elim

theorem injective_fderiv_iff (t : ℝ) (x : Vector 3) :
    Injective (fderiv ℝ (map t) x) ↔ t ≠ 0 ∨ x ≠ 0 := by
  rw [fderiv_map, injective_differential_iff]

end NoExoticSixSphere.WhitneyCusp
