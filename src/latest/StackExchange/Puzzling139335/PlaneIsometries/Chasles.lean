import StackExchange.Puzzling139335.PlaneIsometries

/-!
# Translation, rotation, and reversing normal forms

This file refines the exhaustive complex-coordinate classification of affine
plane isometries.  The direct case has either identity linear part or the
unique center `b / (1 - a)`.  The square of a reversing isometry is translation
by `b + a * conj b`.  Its vanishing is equivalent both to involutivity and to
the existence of a fixed point.

The reversing normal form is a conjugated linear reflection followed by a
translation fixed by that reflection.  No regularity of a dissected region
and no orientation restriction on its congruences is assumed here.
-/

namespace Puzzling139335.PlaneIsometries

noncomputable section

open ComplexConjugate

/-- The center of `z ↦ a * z + b`, when `a ≠ 1`. -/
def complexRotationCenter (a : Circle) (b : ℂ) : ℂ := b / (1 - (a : ℂ))

/-- The displacement of the square of `z ↦ a * conj z + b`. -/
def complexReversingDisplacement (a : Circle) (b : ℂ) : ℂ :=
  b + (a : ℂ) * conj b

/-- The conjugate-linear reflection with coefficient `a` fixing `c`. -/
def complexReflection (a : Circle) (c z : ℂ) : ℂ :=
  c + (a : ℂ) * conj (z - c)

theorem circle_mul_conj (a : Circle) : (a : ℂ) * conj (a : ℂ) = 1 := by
  simp [Complex.mul_conj]

/-- A direct affine map with coefficient different from one is a rotation
about its explicitly computed center. -/
theorem complex_direct_rotation_form (a : Circle) (ha : a ≠ 1) (b z : ℂ) :
    (a : ℂ) * z + b =
      complexRotationCenter a b + (a : ℂ) * (z - complexRotationCenter a b) := by
  have hden : 1 - (a : ℂ) ≠ 0 := sub_ne_zero.mpr (Ne.symm (Circle.coe_eq_one.not.mpr ha))
  dsimp [complexRotationCenter]
  field_simp
  ring

/-- The rotation center is the only fixed point when the linear coefficient
is not one. -/
theorem complex_direct_fixed_iff (a : Circle) (ha : a ≠ 1) (b z : ℂ) :
    (a : ℂ) * z + b = z ↔ z = complexRotationCenter a b := by
  have hden : 1 - (a : ℂ) ≠ 0 := sub_ne_zero.mpr (Ne.symm (Circle.coe_eq_one.not.mpr ha))
  rw [complexRotationCenter, eq_div_iff hden]
  constructor <;> intro h <;> linear_combination -h

/-- The explicit translation produced by squaring a reversing affine map. -/
theorem complex_reversing_square (a : Circle) (b z : ℂ) :
    (a : ℂ) * conj ((a : ℂ) * conj z + b) + b =
      z + complexReversingDisplacement a b := by
  simp only [map_add, map_mul, starRingEnd_self_apply, mul_add]
  rw [← mul_assoc, circle_mul_conj, one_mul]
  simp [complexReversingDisplacement, add_comm, add_left_comm]

/-- The square displacement is parallel to the fixed direction of the
conjugate-linear part. -/
theorem complex_reversing_displacement_fixed (a : Circle) (b : ℂ) :
    (a : ℂ) * conj (complexReversingDisplacement a b) =
      complexReversingDisplacement a b := by
  simp only [complexReversingDisplacement, map_add, map_mul, starRingEnd_self_apply, mul_add]
  rw [← mul_assoc, circle_mul_conj, one_mul, add_comm]

theorem complexReflection_involutive (a : Circle) (c : ℂ) :
    Function.Involutive (complexReflection a c) := by
  intro z
  simp only [complexReflection, add_sub_cancel_left, map_mul, starRingEnd_self_apply]
  rw [← mul_assoc, circle_mul_conj, one_mul, add_sub_cancel]

@[simp] theorem complexReflection_center (a : Circle) (c : ℂ) :
    complexReflection a c c = c := by
  simp [complexReflection]

/-- Every reversing affine map is a reflection fixing `b / 2` followed by
translation through half the displacement of its square. -/
theorem complex_reversing_normal_form (a : Circle) (b z : ℂ) :
    (a : ℂ) * conj z + b =
      complexReflection a (b / 2) z + complexReversingDisplacement a b / 2 := by
  simp only [complexReflection, complexReversingDisplacement, map_sub, map_div₀, map_ofNat]
  ring

theorem complex_reversing_involutive_iff (a : Circle) (b : ℂ) :
    Function.Involutive (fun z : ℂ => (a : ℂ) * conj z + b) ↔
      complexReversingDisplacement a b = 0 := by
  constructor
  · intro h
    have hzero : (a : ℂ) * conj ((a : ℂ) * conj 0 + b) + b = 0 := h 0
    simpa only [complex_reversing_square, zero_add] using hzero
  · intro h z
    change (a : ℂ) * conj ((a : ℂ) * conj z + b) + b = z
    rw [complex_reversing_square, h, add_zero]

theorem complex_reversing_has_fixed_iff (a : Circle) (b : ℂ) :
    (∃ z : ℂ, (a : ℂ) * conj z + b = z) ↔
      complexReversingDisplacement a b = 0 := by
  constructor
  · rintro ⟨z, hz⟩
    have hsq := complex_reversing_square a b z
    rw [hz, hz] at hsq
    exact (add_eq_left.mp hsq.symm)
  · intro h
    refine ⟨b / 2, ?_⟩
    rw [complex_reversing_normal_form, complexReflection_center, h, zero_div, add_zero]

/-- Every unit complex number has a unit square root. -/
theorem circle_exists_sq (a : Circle) : ∃ u : Circle, u ^ 2 = a := by
  refine ⟨Circle.exp ((a : ℂ).arg / 2), ?_⟩
  rw [pow_two, ← Circle.exp_add, add_halves]
  apply Circle.coe_injective
  simpa only [Circle.coe_exp, Circle.norm_coe, Complex.ofReal_one, one_mul]
    using Complex.norm_mul_exp_arg_mul_I (a : ℂ)

/-- In coordinates whose unit direction is `u`, the reflection with
coefficient `u ^ 2` is ordinary complex conjugation. -/
theorem complexReflection_axis_form (u : Circle) (c z : ℂ) :
    complexReflection (u ^ 2) c z =
      c + (u : ℂ) * conj ((z - c) / (u : ℂ)) := by
  simp only [complexReflection, Circle.coe_pow, map_div₀]
  rw [← Circle.coe_inv_eq_conj, Circle.coe_inv, div_inv_eq_mul]
  ring

/-- The fixed vectors of the linear reflection form the real line in the
unit direction `u`. -/
theorem complex_reflection_direction_iff (u : Circle) (w : ℂ) :
    (u : ℂ) ^ 2 * conj w = w ↔ ∃ r : ℝ, w = (u : ℂ) * r := by
  have hform : (u : ℂ) * conj (w / (u : ℂ)) = (u : ℂ) ^ 2 * conj w := by
    rw [map_div₀, ← Circle.coe_inv_eq_conj, Circle.coe_inv, div_inv_eq_mul]
    ring
  constructor
  · intro h
    have hreal : conj (w / (u : ℂ)) = w / (u : ℂ) := by
      apply mul_left_cancel₀ (Circle.coe_ne_zero u)
      rw [hform, h, mul_div_cancel₀ _ (Circle.coe_ne_zero u)]
    obtain ⟨r, hr⟩ := Complex.conj_eq_iff_real.mp hreal
    refine ⟨r, ?_⟩
    rw [← hr, mul_div_cancel₀ _ (Circle.coe_ne_zero u)]
  · rintro ⟨r, rfl⟩
    simp only [map_mul, Complex.conj_ofReal]
    calc
      (u : ℂ) ^ 2 * (conj (u : ℂ) * r) =
          ((u : ℂ) * conj (u : ℂ)) * ((u : ℂ) * r) := by ring
      _ = (u : ℂ) * r := by rw [circle_mul_conj, one_mul]

/-- The fixed locus is exactly the affine line through `c` in direction `u`. -/
theorem complexReflection_fixed_axis (u : Circle) (c z : ℂ) :
    complexReflection (u ^ 2) c z = z ↔ ∃ r : ℝ, z = c + (u : ℂ) * r := by
  constructor
  · intro h
    have hlin : (u : ℂ) ^ 2 * conj (z - c) = z - c := by
      simp only [complexReflection, Circle.coe_pow] at h
      linear_combination h
    obtain ⟨r, hr⟩ := (complex_reflection_direction_iff u (z - c)).mp hlin
    exact ⟨r, by linear_combination hr⟩
  · rintro ⟨r, rfl⟩
    have hlin := (complex_reflection_direction_iff u ((u : ℂ) * r)).mpr ⟨r, rfl⟩
    simpa only [complexReflection, Circle.coe_pow, add_sub_cancel_left] using
      congrArg (c + ·) hlin

/-- A reversing map has unit-axis coordinates `w ↦ conj w + t`, with real
`t`.  Zero `t` is reflection in that axis; nonzero `t` is translation along
the same axis after reflection. -/
theorem complex_reversing_axis_normal_form (a : Circle) (b : ℂ) :
    ∃ u : Circle, ∃ t : ℝ, a = u ^ 2 ∧
      complexReversingDisplacement a b / 2 = (u : ℂ) * t ∧
      ∀ z : ℂ, (a : ℂ) * conj z + b =
        b / 2 + (u : ℂ) * (conj ((z - b / 2) / (u : ℂ)) + (t : ℂ)) := by
  obtain ⟨u, hu⟩ := circle_exists_sq a
  have hv : (u : ℂ) ^ 2 * conj (complexReversingDisplacement a b / 2) =
      complexReversingDisplacement a b / 2 := by
    rw [← Circle.coe_pow, hu, map_div₀, map_ofNat, ← mul_div_assoc,
      complex_reversing_displacement_fixed]
  obtain ⟨t, ht⟩ := (complex_reflection_direction_iff u _).mp hv
  refine ⟨u, t, hu.symm, ht, ?_⟩
  intro z
  calc
    (a : ℂ) * conj z + b =
        complexReflection a (b / 2) z + complexReversingDisplacement a b / 2 :=
      complex_reversing_normal_form a b z
    _ = complexReflection (u ^ 2) (b / 2) z + (u : ℂ) * t := by rw [hu, ht]
    _ = b / 2 + (u : ℂ) * (conj ((z - b / 2) / (u : ℂ)) + (t : ℂ)) := by
      rw [complexReflection_axis_form]
      ring

/-- The identity coefficient in the direct branch gives a translation. -/
theorem affine_direct_translation (e : Plane ≃ᵃⁱ[ℝ] Plane)
    (he : ∀ p, complexEquiv (e p) = complexEquiv p + complexEquiv (e 0)) :
    ∀ p, e p = p + e 0 := by
  intro p
  apply complexEquiv.injective
  simpa only [map_add] using he p

/-- The direct branch with nonidentity coefficient has an explicit rotation
normal form and exactly one fixed point. -/
theorem affine_direct_rotation (e : Plane ≃ᵃⁱ[ℝ] Plane) (a : Circle) (ha : a ≠ 1)
    (he : ∀ p, complexEquiv (e p) = (a : ℂ) * complexEquiv p + complexEquiv (e 0)) :
    let c := complexEquiv.symm (complexRotationCenter a (complexEquiv (e 0)))
    (∀ p, complexEquiv (e p) =
      complexEquiv c + (a : ℂ) * (complexEquiv p - complexEquiv c)) ∧
    (∀ p, e p = p ↔ p = c) := by
  dsimp only
  constructor
  · intro p
    rw [he, complexEquiv.apply_symm_apply]
    exact complex_direct_rotation_form a ha _ _
  · intro p
    rw [← complexEquiv.injective.eq_iff, he, complex_direct_fixed_iff a ha]
    exact (complexEquiv.eq_symm_apply).symm

/-- Squaring any member of the reversing branch gives the stated translation
in the original Euclidean plane. -/
theorem affine_reversing_square (e : Plane ≃ᵃⁱ[ℝ] Plane) (a : Circle)
    (he : ∀ p, complexEquiv (e p) =
      (a : ℂ) * conj (complexEquiv p) + complexEquiv (e 0)) :
    ∀ p, e (e p) =
      p + complexEquiv.symm (complexReversingDisplacement a (complexEquiv (e 0))) := by
  intro p
  apply complexEquiv.injective
  rw [map_add, complexEquiv.apply_symm_apply, he, he]
  exact complex_reversing_square a _ _

theorem affine_reversing_involutive_iff (e : Plane ≃ᵃⁱ[ℝ] Plane) (a : Circle)
    (he : ∀ p, complexEquiv (e p) =
      (a : ℂ) * conj (complexEquiv p) + complexEquiv (e 0)) :
    Function.Involutive e ↔ complexReversingDisplacement a (complexEquiv (e 0)) = 0 := by
  constructor
  · intro h
    have hz := affine_reversing_square e a he 0
    rw [h 0, zero_add] at hz
    have hc := congrArg complexEquiv hz
    simpa using hc.symm
  · intro h p
    rw [affine_reversing_square e a he, h, map_zero, add_zero]

theorem affine_reversing_has_fixed_iff (e : Plane ≃ᵃⁱ[ℝ] Plane) (a : Circle)
    (he : ∀ p, complexEquiv (e p) =
      (a : ℂ) * conj (complexEquiv p) + complexEquiv (e 0)) :
    (∃ p, e p = p) ↔ complexReversingDisplacement a (complexEquiv (e 0)) = 0 := by
  constructor
  · rintro ⟨p, hp⟩
    apply (complex_reversing_has_fixed_iff a (complexEquiv (e 0))).mp
    refine ⟨complexEquiv p, ?_⟩
    rw [← he, hp]
  · intro h
    obtain ⟨z, hz⟩ := (complex_reversing_has_fixed_iff a (complexEquiv (e 0))).mpr h
    refine ⟨complexEquiv.symm z, ?_⟩
    apply complexEquiv.injective
    rw [he, complexEquiv.apply_symm_apply]
    exact hz

/-- A nonzero square displacement rules out every fixed point. -/
theorem affine_reversing_no_fixed (e : Plane ≃ᵃⁱ[ℝ] Plane) (a : Circle)
    (he : ∀ p, complexEquiv (e p) =
      (a : ℂ) * conj (complexEquiv p) + complexEquiv (e 0))
    (hd : complexReversingDisplacement a (complexEquiv (e 0)) ≠ 0) :
    ∀ p, e p ≠ p := by
  intro p hp
  exact hd ((affine_reversing_has_fixed_iff e a he).mp ⟨p, hp⟩)

/-- Reversing normal form transported to the given plane isometry. -/
theorem affine_reversing_normal_form (e : Plane ≃ᵃⁱ[ℝ] Plane) (a : Circle)
    (he : ∀ p, complexEquiv (e p) =
      (a : ℂ) * conj (complexEquiv p) + complexEquiv (e 0)) :
    ∀ p, complexEquiv (e p) =
      complexReflection a (complexEquiv (e 0) / 2) (complexEquiv p) +
        complexReversingDisplacement a (complexEquiv (e 0)) / 2 := by
  intro p
  rw [he]
  exact complex_reversing_normal_form a _ _

/-- Exhaustive Chasles classification: translation, nonidentity rotation,
reflection in a line, or a reflection followed by a nonzero translation
along the same line.  The last two cases use unit-axis coordinates. -/
theorem affine_chasles_classification (e : Plane ≃ᵃⁱ[ℝ] Plane) :
    (∀ p, e p = p + e 0) ∨
    (∃ c : Plane, ∃ a : Circle, a ≠ 1 ∧
      (∀ p, complexEquiv (e p) =
        complexEquiv c + (a : ℂ) * (complexEquiv p - complexEquiv c)) ∧
      (∀ p, e p = p ↔ p = c)) ∨
    (∃ c : ℂ, ∃ u : Circle, ∀ p, complexEquiv (e p) =
      c + (u : ℂ) * conj ((complexEquiv p - c) / (u : ℂ))) ∨
    (∃ c : ℂ, ∃ u : Circle, ∃ t : ℝ, t ≠ 0 ∧ ∀ p, complexEquiv (e p) =
      c + (u : ℂ) * (conj ((complexEquiv p - c) / (u : ℂ)) + (t : ℂ))) := by
  obtain ⟨a, he | he⟩ := affine_complex_classification e
  · by_cases ha : a = 1
    · left
      apply affine_direct_translation e
      simpa only [ha, Circle.coe_one, one_mul] using he
    · right; left
      exact ⟨complexEquiv.symm (complexRotationCenter a (complexEquiv (e 0))),
        a, ha, affine_direct_rotation e a ha he⟩
  · obtain ⟨u, t, _, _, hform⟩ :=
      complex_reversing_axis_normal_form a (complexEquiv (e 0))
    by_cases ht : t = 0
    · right; right; left
      refine ⟨complexEquiv (e 0) / 2, u, ?_⟩
      intro p
      rw [he]
      simpa only [ht, Complex.ofReal_zero, add_zero] using hform (complexEquiv p)
    · right; right; right
      refine ⟨complexEquiv (e 0) / 2, u, t, ht, ?_⟩
      intro p
      rw [he]
      exact hform (complexEquiv p)

end

end Puzzling139335.PlaneIsometries
