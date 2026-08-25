import StackExchange.Puzzling139335.N4MiddleInvolutions.Reflection.SupportTransport.LinearAction

/-!
# The common center of two nonparallel reflections

Composing an ordinary reflection with the square's horizontal reflection gives
a rotation.  Its unique fixed point is fixed by both reflections.
-/

namespace Puzzling139335.N4MiddleInvolutions.Reflection.Dynamics

noncomputable section

open PlaneIsometries ComplexConjugate ReflectionSeparation

/-- The explicit center of the composition with the horizontal reflection. -/
def rotationCenter (e : Plane ≃ᵃⁱ[ℝ] Plane) (u : Circle) : Plane :=
  complexEquiv.symm
    (complexRotationCenter (u ^ 2) (complexEquiv ((e * horizontal) 0)))

variable (e : Plane ≃ᵃⁱ[ℝ] Plane) (c : ℂ) (u : Circle)
  (hform : ∀ p, complexEquiv (e p) =
    c + (u : ℂ) * conj ((complexEquiv p - c) / (u : ℂ)))

include hform

/-- The composition acts on vectors by multiplication by the squared axis direction. -/
theorem composition_linear_complex_action (p : Plane) :
    complexEquiv ((e * horizontal).linearIsometryEquiv p) =
      ((u ^ 2 : Circle) : ℂ) * complexEquiv p := by
  change complexEquiv (e.linearIsometryEquiv (horizontal.linearIsometryEquiv p)) = _
  rw [linear_complex_action_of_axis_form e c u hform,
    horizontal_linear_complex_action, starRingEnd_self_apply]

/-- The actual affine composition has the direct complex-coordinate formula. -/
theorem composition_affine_complex_action (p : Plane) :
    complexEquiv ((e * horizontal) p) =
      ((u ^ 2 : Circle) : ℂ) * complexEquiv p +
        complexEquiv ((e * horizontal) 0) := by
  rw [affine_apply_eq_linear_add, map_add,
    composition_linear_complex_action e c u hform]

variable (hu : u ^ 2 ≠ 1)

include hu

/-- The composition rotates about its explicitly constructed center. -/
theorem rotation_complex_action (p : Plane) :
    complexEquiv ((e * horizontal) p) =
      complexEquiv (rotationCenter e u) +
        ((u ^ 2 : Circle) : ℂ) * (complexEquiv p - complexEquiv (rotationCenter e u)) :=
  (affine_direct_rotation (e * horizontal) (u ^ 2) hu
    (composition_affine_complex_action e c u hform)).1 p

/-- Nonparallel reflecting axes give a unique fixed point of their composition. -/
theorem composition_fixed_iff (p : Plane) :
    (e * horizontal) p = p ↔ p = rotationCenter e u :=
  (affine_direct_rotation (e * horizontal) (u ^ 2) hu
    (composition_affine_complex_action e c u hform)).2 p

/-- The constructed rotation center lies on the horizontal reflecting axis. -/
theorem horizontal_rotationCenter : horizontal (rotationCenter e u) = rotationCenter e u := by
  have hfixed : (e * horizontal) (rotationCenter e u) = rotationCenter e u :=
    (composition_fixed_iff e c u hform hu _).mpr rfl
  have hinvol := involutive_of_axis_form e c u hform
  have heC : e (rotationCenter e u) = horizontal (rotationCenter e u) := by
    have h := congrArg e hfixed
    change e (e (horizontal (rotationCenter e u))) = e (rotationCenter e u) at h
    rw [hinvol] at h
    exact h.symm
  apply (composition_fixed_iff e c u hform hu _).mp
  change e (horizontal (horizontal (rotationCenter e u))) = _
  rw [horizontal_involutive, heC]

/-- The constructed rotation center also lies on the original reflecting axis. -/
theorem reflection_rotationCenter : e (rotationCenter e u) = rotationCenter e u := by
  have hfixed := (composition_fixed_iff e c u hform hu (rotationCenter e u)).mpr rfl
  change e (horizontal (rotationCenter e u)) = rotationCenter e u at hfixed
  rwa [horizontal_rotationCenter e c u hform hu] at hfixed

/-- The second coordinate of the common fixed point is exactly one half. -/
theorem rotationCenter_one : rotationCenter e u 1 = (1 / 2 : ℝ) := by
  have h := congrArg (fun p : Plane => p 1) (horizontal_rotationCenter e c u hform hu)
  simp only [horizontal_apply_one] at h
  linarith

/-- All center data are derived from the two given actual reflections. -/
theorem exists_common_fixed_rotation_center :
    ∃ C : Plane, e C = C ∧ horizontal C = C ∧ C 1 = (1 / 2 : ℝ) ∧
      (∀ p, complexEquiv ((e * horizontal) p) =
        complexEquiv C + ((u ^ 2 : Circle) : ℂ) * (complexEquiv p - complexEquiv C)) ∧
      (∀ p, (e * horizontal) p = p ↔ p = C) :=
  ⟨rotationCenter e u, reflection_rotationCenter e c u hform hu,
    horizontal_rotationCenter e c u hform hu, rotationCenter_one e c u hform hu,
    rotation_complex_action e c u hform hu, composition_fixed_iff e c u hform hu⟩

end

end Puzzling139335.N4MiddleInvolutions.Reflection.Dynamics
