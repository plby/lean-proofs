import Wikipedia.HopfProblem.OrbitPairSphereSineModes
import Wikipedia.NoExoticSixSphere.SkewRotationComplement

/-!
# Independent negative directions for nonminimal sphere great circles

The parameter space is two copies of the actual orthogonal complement of the
great-circle plane. A parameter gives an endpoint-zero sine field and an
actual smooth normalized sphere variation. Every nonzero parameter has
strictly negative second energy derivative when the speed has absolute value
at least `3π`. Its dimension is twice the sphere dimension minus two.

This is the negative-subspace estimate needed in a finite-path proof of
suspension connectivity. No global path deformation, suspension comparison,
stable fifth-stem vanishing, or framed filling is asserted here.
-/

noncomputable section

open scoped ContDiff

namespace Wikipedia.HopfProblem.OrbitPair.SphereNegativeDirections

open NoExoticSixSphere GLOrthonormalization SkewRotationComplement

variable {n : ℕ}

abbrev Parameters (x y : Vector n) := complement x y × complement x y

def fieldLinear (x y : Vector n) : Parameters x y →ₗ[ℝ] (ℝ → Vector n) where
  toFun p := SphereSineModes.field (p.1 : Vector n) (p.2 : Vector n)
  map_add' p q := by
    funext t
    change Real.sin (Real.pi * t) • ((p.1 : Vector n) + q.1) +
      Real.sin (2 * Real.pi * t) • ((p.2 : Vector n) + q.2) = _
    dsimp [SphereSineModes.field]
    module
  map_smul' a p := by
    funext t
    change Real.sin (Real.pi * t) • (a • (p.1 : Vector n)) +
      Real.sin (2 * Real.pi * t) • (a • (p.2 : Vector n)) = _
    dsimp [SphereSineModes.field]
    module

theorem fieldLinear_apply (x y : Vector n) (p : Parameters x y) (t : ℝ) :
    fieldLinear x y p t = SphereSineModes.field (p.1 : Vector n) (p.2 : Vector n) t := rfl

theorem fieldLinear_injective (x y : Vector n) : Function.Injective (fieldLinear x y) := by
  apply (injective_iff_map_eq_zero (fieldLinear x y)).mpr
  intro p hp
  have hhalf := congrFun hp (1 / 2)
  change SphereSineModes.field (p.1 : Vector n) (p.2 : Vector n) (1 / 2) = 0 at hhalf
  simp only [SphereSineModes.field, show Real.pi * (1 / 2) = Real.pi / 2 by ring,
    show 2 * Real.pi * (1 / 2) = Real.pi by ring, Real.sin_pi_div_two,
    Real.sin_pi, one_smul, zero_smul, add_zero] at hhalf
  have hquarter := congrFun hp (1 / 4)
  change SphereSineModes.field (p.1 : Vector n) (p.2 : Vector n) (1 / 4) = 0 at hquarter
  simp only [SphereSineModes.field, hhalf, smul_zero, zero_add,
    show 2 * Real.pi * (1 / 4) = Real.pi / 2 by ring, Real.sin_pi_div_two, one_smul] at hquarter
  exact Prod.ext (Subtype.ext hhalf) (Subtype.ext hquarter)

theorem field_orthogonal (x y : Vector n) (p : Parameters x y) (w t : ℝ) :
    inner ℝ (SphereGreatCircle.curve x y w t) (fieldLinear x y p t) = 0 := by
  obtain ⟨hx₁, hy₁⟩ := (mem_complement x y (p.1 : Vector n)).mp p.1.property
  obtain ⟨hx₂, hy₂⟩ := (mem_complement x y (p.2 : Vector n)).mp p.2.property
  simp only [fieldLinear_apply, SphereSineModes.field, inner_add_right,
    real_inner_smul_right, SphereGreatCircle.inner_curve_eq_zero hx₁ hy₁,
    SphereGreatCircle.inner_curve_eq_zero hx₂ hy₂, mul_zero, add_zero]

theorem dimension {x y : Vector n} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
    (hxy : inner ℝ x y = 0) : Module.finrank ℝ (Parameters x y) + 4 = 2 * n := by
  have h := finrank_complement hx hy hxy
  change Module.finrank ℝ (complement x y × complement x y) + 4 = 2 * n
  rw [Module.finrank_prod]
  omega

theorem negative_index {x y : Vector n} (p : Parameters x y) (hp : p ≠ 0)
    (w : ℝ) (hw : 3 * Real.pi ≤ |w|) :
    (Real.pi ^ 2 - w ^ 2) * ‖(p.1 : Vector n)‖ ^ 2 +
      (4 * Real.pi ^ 2 - w ^ 2) * ‖(p.2 : Vector n)‖ ^ 2 < 0 := by
  have hsq : 9 * Real.pi ^ 2 ≤ w ^ 2 := by
    have h := (sq_le_sq₀ (by positivity : 0 ≤ 3 * Real.pi) (abs_nonneg w)).mpr hw
    rw [sq_abs] at h
    nlinarith
  have h₁ : Real.pi ^ 2 - w ^ 2 < 0 := by nlinarith [Real.pi_pos]
  have h₂ : 4 * Real.pi ^ 2 - w ^ 2 < 0 := by nlinarith [Real.pi_pos]
  have hor : (p.1 : Vector n) ≠ 0 ∨ (p.2 : Vector n) ≠ 0 := by
    by_contra h
    push Not at h
    exact hp (Prod.ext (Subtype.ext h.1) (Subtype.ext h.2))
  rcases hor with h | h
  · exact add_neg_of_neg_of_nonpos
      (mul_neg_of_neg_of_pos h₁ (sq_pos_of_pos (norm_pos_iff.mpr h)))
      (mul_nonpos_of_nonpos_of_nonneg h₂.le (sq_nonneg _))
  · exact add_neg_of_nonpos_of_neg
      (mul_nonpos_of_nonpos_of_nonneg h₁.le (sq_nonneg _))
      (mul_neg_of_neg_of_pos h₂ (sq_pos_of_pos (norm_pos_iff.mpr h)))

theorem negative_secondDerivative {x y : Vector n}
    (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) (hxy : inner ℝ x y = 0)
    (w : ℝ) (hw : 3 * Real.pi ≤ |w|) (p : Parameters x y) (hp : p ≠ 0) :
    deriv (deriv (fun s => SpherePathEnergy.energy
      (fun t => SphereNormalVariation.family (SphereGreatCircle.curve x y w)
        (fieldLinear x y p) (s, t)) 0 1)) 0 < 0 := by
  have hd := SphereNormalVariation.hasDerivAt_deriv_energy
    (SphereGreatCircle.contDiff_curve x y w) (SphereSineModes.contDiff_field _ _)
    (SphereGreatCircle.norm_curve hx hy hxy w) (field_orthogonal x y p w) 0 1 w
    (SphereSineModes.field_zero _ _) (SphereSineModes.field_one _ _)
    (SphereGreatCircle.deriv_deriv_curve x y w)
  change HasDerivAt (deriv (fun s => SpherePathEnergy.energy
    (fun t => SphereNormalVariation.family (SphereGreatCircle.curve x y w)
      (fieldLinear x y p) (s, t)) 0 1)) _ 0 at hd
  rw [hd.deriv]
  change (2 * ∫ t : ℝ in 0..1,
    (‖deriv (SphereSineModes.field (p.1 : Vector n) (p.2 : Vector n)) t‖ ^ 2 -
      w ^ 2 * ‖SphereSineModes.field (p.1 : Vector n) (p.2 : Vector n) t‖ ^ 2)) < 0
  rw [SphereSineModes.index_field]
  exact negative_index p hp w hw

theorem exists_negative_fieldFamily {x y : Vector n}
    (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) (hxy : inner ℝ x y = 0)
    (w : ℝ) (hw : 3 * Real.pi ≤ |w|) :
    ∃ (d : ℕ) (F : (Fin d → ℝ) →ₗ[ℝ] (ℝ → Vector n)),
      d + 4 = 2 * n ∧ Function.Injective F ∧ ∀ c,
        ContDiff ℝ ∞ (F c) ∧ F c 0 = 0 ∧ F c 1 = 0 ∧
          (c ≠ 0 → deriv (deriv (fun s => SpherePathEnergy.energy
            (fun t => SphereNormalVariation.family (SphereGreatCircle.curve x y w)
              (F c) (s, t)) 0 1)) 0 < 0) := by
  let e := (Module.finBasis ℝ (Parameters x y)).equivFun.symm
  let F := (fieldLinear x y).comp e.toLinearMap
  refine ⟨Module.finrank ℝ (Parameters x y), F, dimension hx hy hxy,
    (fieldLinear_injective x y).comp e.injective, ?_⟩
  intro c
  refine ⟨SphereSineModes.contDiff_field _ _, SphereSineModes.field_zero _ _,
    SphereSineModes.field_one _ _, ?_⟩
  intro hc
  exact negative_secondDerivative hx hy hxy w hw (e c)
    (fun he => hc (e.injective (he.trans e.map_zero.symm)))

end Wikipedia.HopfProblem.OrbitPair.SphereNegativeDirections
