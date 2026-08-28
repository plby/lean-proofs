import Wikipedia.NoExoticSixSphere.SphereRadialRetraction
import Wikipedia.NoExoticSixSphere.AugmentedSurjection
import Mathlib.Analysis.InnerProductSpace.ProdL2

/-!
# Ambient equations for a regular level on the sphere

Extend a vector-valued sphere map radially and add the equation `‖x‖² = 1`.
At a regular sphere point, the augmented ambient differential is surjective.
The construction is smooth near the sphere and uses its original atlas.
-/

open scoped Manifold ContDiff InnerProductSpace

namespace NoExoticSixSphere.SphereLevelEquations

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {m : ℕ} [Fact (Module.finrank ℝ E = m + 1)]

noncomputable def extend (a : UnitSphere E) (g : UnitSphere E → F) : E → F :=
  g ∘ SphereRadialRetraction.retract a

omit [NormedAddCommGroup F] [NormedSpace ℝ F] in
theorem extend_coe (a : UnitSphere E) (g : UnitSphere E → F) (x : UnitSphere E) :
    extend a g (x : E) = g x := by
  change g (SphereRadialRetraction.retract a (x : E)) = g x
  rw [SphereRadialRetraction.retract_coe]

theorem contDiffAt_extend (a : UnitSphere E) {g : UnitSphere E → F} {x : UnitSphere E}
    (hg : ContMDiffAt (𝓡 m) 𝓘(ℝ, F) ∞ g x) : ContDiffAt ℝ ∞ (extend a g) (x : E) := by
  have hg' : ContMDiffAt (𝓡 m) 𝓘(ℝ, F) ∞ g
      (SphereRadialRetraction.retract a (x : E)) := by
    rw [SphereRadialRetraction.retract_coe]
    exact hg
  exact (hg'.comp (x : E) (SphereRadialRetraction.contMDiffAt_retract (n := m) a
    (ne_zero_of_mem_unit_sphere x))).contDiffAt

noncomputable def inclusionDifferential (x : UnitSphere E) :
    EuclideanSpace ℝ (Fin m) →L[ℝ] E :=
  mfderiv (𝓡 m) 𝓘(ℝ, E) (Subtype.val : UnitSphere E → E) x

theorem differential_extend_comp_inclusion (a : UnitSphere E) {g : UnitSphere E → F}
    {x : UnitSphere E} (hg : ContMDiffAt (𝓡 m) 𝓘(ℝ, F) ∞ g x) :
    (fderiv ℝ (extend a g) (x : E)).comp (inclusionDifferential (m := m) x) =
      mfderiv (𝓡 m) 𝓘(ℝ, F) g x := by
  have heq : extend a g ∘ (Subtype.val : UnitSphere E → E) = g := funext (extend_coe a g)
  have h := mfderiv_comp x
    ((contDiffAt_extend a hg).differentiableAt (by simp)).mdifferentiableAt
    ((contMDiff_coe_sphere (n := m) (m := ∞)).mdifferentiable (by simp) x)
  rw [heq, mfderiv_eq_fderiv] at h
  exact h.symm

theorem sphere_equation_comp_inclusion (x : UnitSphere E) :
    (fderiv ℝ (fun y : E ↦ ‖y‖ ^ 2 - 1) (x : E)).comp
      (inclusionDifferential (m := m) x) = 0 := by
  have heq : (fun y : E ↦ ‖y‖ ^ 2 - 1) ∘ (Subtype.val : UnitSphere E → E) =
      fun _ ↦ (0 : ℝ) := by
    funext y
    simp only [Function.comp_apply, ClosedHemisphere.unit_norm, one_pow, sub_self]
  have hs : ContDiff ℝ ∞ (fun y : E ↦ ‖y‖ ^ 2 - 1) :=
    (contDiff_id.norm_sq (𝕜 := ℝ)).sub contDiff_const
  have h := mfderiv_comp x (hs.differentiable (by simp) (x : E)).mdifferentiableAt
    ((contMDiff_coe_sphere (n := m) (m := ∞)).mdifferentiable (by simp) x)
  rw [heq, mfderiv_const, mfderiv_eq_fderiv] at h
  exact h.symm

noncomputable def rawEquations (a : UnitSphere E) (g : UnitSphere E → F) (y : E) : ℝ × F :=
  (‖y‖ ^ 2 - 1, extend a g y)

omit [NormedAddCommGroup F] [NormedSpace ℝ F] in
theorem rawEquations_coe (a : UnitSphere E) (g : UnitSphere E → F) (x : UnitSphere E) :
    rawEquations a g (x : E) = (0, g x) := by
  simp only [rawEquations, ClosedHemisphere.unit_norm, one_pow, sub_self, extend_coe]

theorem contDiffAt_rawEquations (a : UnitSphere E) {g : UnitSphere E → F} {x : UnitSphere E}
    (hg : ContMDiffAt (𝓡 m) 𝓘(ℝ, F) ∞ g x) :
    ContDiffAt ℝ ∞ (rawEquations a g) (x : E) :=
  ((contDiff_id.norm_sq (𝕜 := ℝ)).sub contDiff_const).contDiffAt.prodMk
    (contDiffAt_extend a hg)

theorem surjective_fderiv_rawEquations (a : UnitSphere E) {g : UnitSphere E → F}
    {x : UnitSphere E} (hg : ContMDiffAt (𝓡 m) 𝓘(ℝ, F) ∞ g x)
    (hreg : Function.Surjective (mfderiv (𝓡 m) 𝓘(ℝ, F) g x)) :
    Function.Surjective (fderiv ℝ (rawEquations a g) (x : E)) := by
  let L := fderiv ℝ (fun y : E ↦ ‖y‖ ^ 2 - 1) (x : E)
  let D := fderiv ℝ (extend a g) (x : E)
  have hs : ContDiff ℝ ∞ (fun y : E ↦ ‖y‖ ^ 2 - 1) :=
    (contDiff_id.norm_sq (𝕜 := ℝ)).sub contDiff_const
  have hL : HasFDerivAt (fun y : E ↦ ‖y‖ ^ 2 - 1) L (x : E) :=
    (hs.differentiable (by simp) _).hasFDerivAt
  have hD := ((contDiffAt_extend a hg).differentiableAt (by simp)).hasFDerivAt
  have hpair : fderiv ℝ (rawEquations a g) (x : E) = L.prod D := (hL.prodMk hD).fderiv
  rw [hpair]
  refine surjective_augmented_differential L D (inclusionDifferential (m := m) x) ?_ ?_ (x : E) ?_
  · intro v
    exact congrArg (fun T : EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ ↦ T v)
      (sphere_equation_comp_inclusion (m := m) x)
  · rw [show D.comp (inclusionDifferential (m := m) x) =
        mfderiv (𝓡 m) 𝓘(ℝ, F) g x from differential_extend_comp_inclusion a hg]
    exact hreg
  · have hnorm : L = 2 • innerSL ℝ (x : E) :=
      (hL.unique ((hasStrictFDerivAt_norm_sq (x : E)).hasFDerivAt.sub_const 1))
    rw [hnorm]
    simp

noncomputable def equations (a : UnitSphere E) (g : UnitSphere E → F) :
    E → WithLp 2 (ℝ × F) :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ ℝ F).symm ∘ rawEquations a g

theorem equations_coe (a : UnitSphere E) (g : UnitSphere E → F) (x : UnitSphere E) :
    equations a g (x : E) = WithLp.toLp 2 (0, g x) := by
  change (WithLp.prodContinuousLinearEquiv 2 ℝ ℝ F).symm (rawEquations a g (x : E)) = _
  rw [rawEquations_coe]
  rfl

theorem contDiffAt_equations (a : UnitSphere E) {g : UnitSphere E → F} {x : UnitSphere E}
    (hg : ContMDiffAt (𝓡 m) 𝓘(ℝ, F) ∞ g x) :
    ContDiffAt ℝ ∞ (equations a g) (x : E) :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ ℝ F).symm.contDiff.contDiffAt.comp (x : E)
    (contDiffAt_rawEquations a hg)

theorem surjective_fderiv_equations (a : UnitSphere E) {g : UnitSphere E → F}
    {x : UnitSphere E} (hg : ContMDiffAt (𝓡 m) 𝓘(ℝ, F) ∞ g x)
    (hreg : Function.Surjective (mfderiv (𝓡 m) 𝓘(ℝ, F) g x)) :
    Function.Surjective (fderiv ℝ (equations a g) (x : E)) := by
  rw [equations, fderiv_comp (x : E)
    (WithLp.prodContinuousLinearEquiv 2 ℝ ℝ F).symm.differentiableAt
    ((contDiffAt_rawEquations a hg).differentiableAt (by simp)),
    ContinuousLinearEquiv.fderiv]
  exact (WithLp.prodContinuousLinearEquiv 2 ℝ ℝ F).symm.surjective.comp
    (surjective_fderiv_rawEquations a hg hreg)

end NoExoticSixSphere.SphereLevelEquations
