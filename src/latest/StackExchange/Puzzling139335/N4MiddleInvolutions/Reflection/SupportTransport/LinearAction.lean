import StackExchange.Puzzling139335.N4MiddleInvolutions.Reflection.SupportTransport.Defs
import StackExchange.Puzzling139335.N4MiddleInvolutions.Reflection.NormalForm
import StackExchange.Puzzling139335.ReflectionSeparation.Maps

/-! Linear complex actions derived from actual affine formulas. -/

namespace Puzzling139335.N4MiddleInvolutions.Reflection

noncomputable section

open PlaneIsometries ComplexConjugate

/-- The translation term disappears when passing to the linear part of a
direct complex affine formula. -/
theorem linear_complex_action_of_affine_direct
    (e : Plane ≃ᵃⁱ[ℝ] Plane) (a b : ℂ)
    (hform : ∀ p, complexEquiv (e p) = a * complexEquiv p + b) :
    ∀ p, complexEquiv (e.linearIsometryEquiv p) = a * complexEquiv p := by
  intro p
  have hp := hform p
  have hzero : complexEquiv (e 0) = b := by simpa using hform 0
  rw [affine_apply_eq_linear_add, map_add, hzero] at hp
  exact add_right_cancel hp

/-- The translation term disappears when passing to the linear part of a
conjugate-linear complex affine formula. -/
theorem linear_complex_action_of_affine_reversing
    (e : Plane ≃ᵃⁱ[ℝ] Plane) (a b : ℂ)
    (hform : ∀ p, complexEquiv (e p) = a * conj (complexEquiv p) + b) :
    ∀ p, complexEquiv (e.linearIsometryEquiv p) = a * conj (complexEquiv p) := by
  intro p
  have hp := hform p
  have hzero : complexEquiv (e 0) = b := by simpa using hform 0
  rw [affine_apply_eq_linear_add, map_add, hzero] at hp
  exact add_right_cancel hp

/-- Reflection in an affine axis of unit direction `u` acts on vectors by
conjugation followed by multiplication by `u ^ 2`. -/
theorem linear_complex_action_of_axis_form
    (e : Plane ≃ᵃⁱ[ℝ] Plane) (c : ℂ) (u : Circle)
    (hform : ∀ p, complexEquiv (e p) =
      c + (u : ℂ) * conj ((complexEquiv p - c) / (u : ℂ))) :
    ∀ p, complexEquiv (e.linearIsometryEquiv p) =
      ((u ^ 2 : Circle) : ℂ) * conj (complexEquiv p) := by
  apply linear_complex_action_of_affine_reversing e
    ((u ^ 2 : Circle) : ℂ) (c - ((u ^ 2 : Circle) : ℂ) * conj c)
  intro p
  rw [hform p, ← complexReflection_axis_form]
  simp only [complexReflection, map_sub, mul_sub]
  ring

/-- The square's horizontal reflection has ordinary complex conjugation
as its linear part. -/
theorem horizontal_linear_complex_action (p : Plane) :
    complexEquiv (ReflectionSeparation.horizontal.linearIsometryEquiv p) =
      conj (complexEquiv p) := by
  have hform : ∀ q, complexEquiv (ReflectionSeparation.horizontal q) =
      (1 : ℂ) * conj (complexEquiv q) + Complex.I := by
    intro q
    apply Complex.ext
    · simp
    · simp [sub_eq_add_neg, add_comm]
  simpa only [one_mul] using
    linear_complex_action_of_affine_reversing ReflectionSeparation.horizontal 1
      Complex.I hform p

end

end Puzzling139335.N4MiddleInvolutions.Reflection
