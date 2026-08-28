import Wikipedia.NoExoticSixSphere.ArfInvariant

/-!
# Quadratic planes and the Arf invariant

On a symplectic pair of coordinates the quadratic form is
`a*x² + x*y + b*y²`. Its Gauss sum is `2 * (-1)^(a*b)`, so its Arf
invariant is `a*b`. The hyperbolic and anisotropic planes consequently have
invariants zero and one, respectively.
-/

namespace NoExoticSixSphere.Arf

def plane (a b : F₂) : QuadraticForm F₂ (F₂ × F₂) :=
  a • QuadraticMap.linMulLin (LinearMap.fst F₂ F₂ F₂) (LinearMap.fst F₂ F₂ F₂) +
    QuadraticMap.linMulLin (LinearMap.fst F₂ F₂ F₂) (LinearMap.snd F₂ F₂ F₂) +
      b • QuadraticMap.linMulLin (LinearMap.snd F₂ F₂ F₂) (LinearMap.snd F₂ F₂ F₂)

theorem plane_apply (a b : F₂) (p : F₂ × F₂) :
    plane a b p = a * (p.1 * p.1) + p.1 * p.2 + b * (p.2 * p.2) := rfl

theorem plane_polar (a b : F₂) (p q : F₂ × F₂) :
    (plane a b).polarBilin p q = p.1 * q.2 + p.2 * q.1 := by
  simp only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar, plane_apply,
    Prod.fst_add, Prod.snd_add]
  ring_nf
  have h₂ : (2 : F₂) = 0 := by decide
  simp only [h₂, mul_zero, zero_add, add_zero]

theorem plane_nondegenerate (a b : F₂) : (plane a b).polarBilin.Nondegenerate := by
  constructor
  · intro p hp
    have h₀ := hp (0, 1)
    have h₁ := hp (1, 0)
    simp only [plane_polar, mul_one, mul_zero, zero_add, add_zero] at h₀ h₁
    exact Prod.ext h₀ h₁
  · intro p hp
    have h₀ := hp (0, 1)
    have h₁ := hp (1, 0)
    simp only [plane_polar, one_mul, zero_mul, zero_add, add_zero] at h₀ h₁
    exact Prod.ext h₀ h₁

theorem gaussSum_plane (a b : F₂) : gaussSum (plane a b) = 2 * sign (a * b) := by
  fin_cases a <;> fin_cases b <;> decide

theorem invariant_plane (a b : F₂) :
    invariant (plane a b) (plane_nondegenerate a b) = a * b := by
  unfold invariant
  rw [gaussSum_plane]
  fin_cases a <;> fin_cases b <;> decide

abbrev hyperbolicPlane : QuadraticForm F₂ (F₂ × F₂) := plane 0 0

abbrev anisotropicPlane : QuadraticForm F₂ (F₂ × F₂) := plane 1 1

theorem invariant_hyperbolicPlane :
    invariant hyperbolicPlane (plane_nondegenerate 0 0) = 0 := by
  rw [invariant_plane, zero_mul]

theorem invariant_anisotropicPlane :
    invariant anisotropicPlane (plane_nondegenerate 1 1) = 1 := by
  rw [invariant_plane, one_mul]

theorem hyperbolic_anisotropic_not_isometric :
    ¬ Nonempty (hyperbolicPlane.IsometryEquiv anisotropicPlane) := by
  rintro ⟨e⟩
  have h := invariant_isometry hyperbolicPlane anisotropicPlane
    (plane_nondegenerate 0 0) (plane_nondegenerate 1 1) e
  rw [invariant_hyperbolicPlane, invariant_anisotropicPlane] at h
  exact zero_ne_one h

end NoExoticSixSphere.Arf
