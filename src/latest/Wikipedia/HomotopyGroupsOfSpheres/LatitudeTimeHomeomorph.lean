import Wikipedia.HomotopyGroupsOfSpheres.LatitudeDescent
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

/-! # Actual sphere homeomorphisms from reversing the latitude time coordinate -/

noncomputable section

open scoped unitInterval

namespace Wikipedia.HomotopyGroupsOfSpheres.LatitudeDescent

open Wikipedia.HopfProblem.SphereHomology

def reversedTimeMap (n : ℕ) (f : C(I, I)) (h0 : f 0 = 1) (h1 : f 1 = 0) :
    C(UnitSphere (n + 1), UnitSphere (n + 1)) :=
  sphereLift n ⟨fun p ↦ Latitude.point n (f p.1) p.2, by fun_prop⟩
    (fun x y ↦ by
      change Latitude.point n (f 0) x = Latitude.point n (f 0) y
      rw [h0]
      exact Latitude.point_one_eq n x y)
    (fun x y ↦ by
      change Latitude.point n (f 1) x = Latitude.point n (f 1) y
      rw [h1]
      exact Latitude.point_zero_eq n x y)

theorem reversedTimeMap_point (n : ℕ) (f : C(I, I)) (h0 : f 0 = 1) (h1 : f 1 = 0)
    (t : I) (z : UnitSphere n) :
    reversedTimeMap n f h0 h1 (Latitude.point n t z) = Latitude.point n (f t) z :=
  sphereLift_point n _ _ _ t z

theorem reversedTime_symm_zero (e : I ≃ₜ I) (h1 : e 1 = 0) : e.symm 0 = 1 := by
  apply e.injective
  rw [e.apply_symm_apply, h1]

theorem reversedTime_symm_one (e : I ≃ₜ I) (h0 : e 0 = 1) : e.symm 1 = 0 := by
  apply e.injective
  rw [e.apply_symm_apply, h0]

def reversedTimeHomeomorph (n : ℕ) (e : I ≃ₜ I) (h0 : e 0 = 1) (h1 : e 1 = 0) :
    UnitSphere (n + 1) ≃ₜ UnitSphere (n + 1) where
  toFun := reversedTimeMap n (e : C(I, I)) h0 h1
  invFun := reversedTimeMap n (e.symm : C(I, I))
    (reversedTime_symm_zero e h1) (reversedTime_symm_one e h0)
  left_inv w := by
    obtain ⟨⟨t, z⟩, rfl⟩ := Latitude.point_surjective n w
    rw [reversedTimeMap_point, reversedTimeMap_point]
    change Latitude.point n (e.symm (e t)) z = Latitude.point n t z
    rw [e.symm_apply_apply]
  right_inv w := by
    obtain ⟨⟨t, z⟩, rfl⟩ := Latitude.point_surjective n w
    rw [reversedTimeMap_point, reversedTimeMap_point]
    change Latitude.point n (e (e.symm t)) z = Latitude.point n t z
    rw [e.apply_symm_apply]
  continuous_toFun := (reversedTimeMap n _ _ _).continuous
  continuous_invFun := (reversedTimeMap n _ _ _).continuous

theorem reversedTimeHomeomorph_point (n : ℕ) (e : I ≃ₜ I)
    (h0 : e 0 = 1) (h1 : e 1 = 0) (t : I) (z : UnitSphere n) :
    reversedTimeHomeomorph n e h0 h1 (Latitude.point n t z) = Latitude.point n (e t) z :=
  reversedTimeMap_point n (e : C(I, I)) h0 h1 t z

def angularTime : C(I, I) where
  toFun t := ⟨(1 + Real.cos ((t : ℝ) * Real.pi)) / 2, by
    constructor <;> nlinarith [Real.neg_one_le_cos ((t : ℝ) * Real.pi),
      Real.cos_le_one ((t : ℝ) * Real.pi)]⟩
  continuous_toFun := by fun_prop

def literalTime : C(I, I) where
  toFun t := ⟨Real.arccos (2 * (t : ℝ) - 1) / Real.pi, by
    constructor
    · exact div_nonneg (Real.arccos_nonneg _) Real.pi_pos.le
    · exact (div_le_one Real.pi_pos).mpr (Real.arccos_le_pi _)⟩
  continuous_toFun := by fun_prop

theorem literalTime_angularTime (t : I) : literalTime (angularTime t) = t := by
  apply Subtype.ext
  change Real.arccos (2 * ((1 + Real.cos ((t : ℝ) * Real.pi)) / 2) - 1) / Real.pi = t
  have h : 2 * ((1 + Real.cos ((t : ℝ) * Real.pi)) / 2) - 1 =
      Real.cos ((t : ℝ) * Real.pi) := by ring
  rw [h, Real.arccos_cos (mul_nonneg t.property.1 Real.pi_pos.le)
    (by nlinarith [t.property.2, Real.pi_pos])]
  exact mul_div_cancel_right₀ _ Real.pi_ne_zero

theorem angularTime_literalTime (t : I) : angularTime (literalTime t) = t := by
  apply Subtype.ext
  change (1 + Real.cos ((Real.arccos (2 * (t : ℝ) - 1) / Real.pi) * Real.pi)) / 2 = t
  rw [div_mul_cancel₀ _ Real.pi_ne_zero,
    Real.cos_arccos (by linarith [t.property.1]) (by linarith [t.property.2])]
  ring

def angularTimeHomeomorph : I ≃ₜ I where
  toFun := angularTime
  invFun := literalTime
  left_inv := literalTime_angularTime
  right_inv := angularTime_literalTime
  continuous_toFun := angularTime.continuous
  continuous_invFun := literalTime.continuous

theorem angularTimeHomeomorph_zero : angularTimeHomeomorph 0 = 1 := by
  apply Subtype.ext
  change (1 + Real.cos ((0 : ℝ) * Real.pi)) / 2 = 1
  simp

theorem angularTimeHomeomorph_one : angularTimeHomeomorph 1 = 0 := by
  apply Subtype.ext
  change (1 + Real.cos ((1 : ℝ) * Real.pi)) / 2 = 0
  simp

theorem angularTimeHomeomorph_angle (t : I) :
    Real.arccos (Latitude.height (angularTimeHomeomorph t)) = (t : ℝ) * Real.pi := by
  change Real.arccos (2 * ((1 + Real.cos ((t : ℝ) * Real.pi)) / 2) - 1) = _
  have h : 2 * ((1 + Real.cos ((t : ℝ) * Real.pi)) / 2) - 1 =
      Real.cos ((t : ℝ) * Real.pi) := by ring
  rw [h]
  exact Real.arccos_cos (mul_nonneg t.property.1 Real.pi_pos.le)
    (by nlinarith [t.property.2, Real.pi_pos])

end Wikipedia.HomotopyGroupsOfSpheres.LatitudeDescent
