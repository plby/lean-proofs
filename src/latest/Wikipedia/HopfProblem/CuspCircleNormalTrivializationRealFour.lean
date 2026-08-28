import Wikipedia.HopfProblem.CuspCircleNormalTrivializationRadius
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# The standard real four-dimensional normal fibre

The two complex normal coordinates identify with standard Euclidean four-space
by their real and imaginary parts. The source retains its original product norm
and native real manifold structure. The exact squared-norm identity identifies
the actual normal-radius disks and spheres with the usual round Euclidean ones.
-/

noncomputable section

open Set Metric
open scoped ContDiff Manifold Matrix

namespace Wikipedia.HopfProblem.CuspCircleNormalTrivialization.RealFour

/-- Standard Euclidean real four-space, with its usual Euclidean norm. -/
abbrev Space := EuclideanSpace ℝ (Fin 4)

/-- The literal real and imaginary coordinates, first in the finite product. -/
def coordinateFunctionEquiv : Fibre ≃L[ℝ] (Fin 4 → ℝ) :=
  (show Fibre ≃ₗ[ℝ] (Fin 4 → ℝ) from
    { toFun := fun v => ![v.1.re, v.1.im, v.2.re, v.2.im]
      invFun := fun x => (⟨x 0, x 1⟩, ⟨x 2, x 3⟩)
      left_inv := by
        rintro ⟨⟨a, b⟩, ⟨c, d⟩⟩
        rfl
      right_inv := by
        intro x
        ext i
        fin_cases i <;> rfl
      map_add' := by
        intro v w
        ext i
        fin_cases i <;> rfl
      map_smul' := by
        intro a v
        ext i
        fin_cases i
        · exact Complex.smul_re a v.1
        · exact Complex.smul_im a v.1
        · exact Complex.smul_re a v.2
        · exact Complex.smul_im a v.2 }).toContinuousLinearEquiv

/-- The genuine real-linear equivalence to the standard Euclidean space. -/
def coordinateEquiv : Fibre ≃L[ℝ] Space :=
  coordinateFunctionEquiv.trans (EuclideanSpace.equiv (Fin 4) ℝ).symm

@[simp] theorem coordinateEquiv_apply (v : Fibre) (i : Fin 4) :
    coordinateEquiv v i = ![v.1.re, v.1.im, v.2.re, v.2.im] i := rfl

@[simp] theorem coordinateEquiv_symm_apply (x : Space) :
    coordinateEquiv.symm x = (⟨x 0, x 1⟩, ⟨x 2, x 3⟩) := rfl

/-- The Euclidean norm is exactly the previously defined normal radius. -/
theorem coordinateEquiv_norm_sq (v : Fibre) :
    ‖coordinateEquiv v‖ ^ 2 = radiusSq v := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp [coordinateEquiv_apply, Fin.sum_univ_succ, radiusSq, Complex.normSq_apply,
    pow_two, add_assoc]

theorem coordinateEquiv_symm_radiusSq (x : Space) :
    radiusSq (coordinateEquiv.symm x) = ‖x‖ ^ 2 := by
  simpa only [coordinateEquiv.apply_symm_apply] using
    (coordinateEquiv_norm_sq (coordinateEquiv.symm x)).symm

/-- The same literal coordinate map is a native real-analytic diffeomorphism. -/
def diffeomorph : Diffeomorph 𝓘(ℝ, Fibre) 𝓘(ℝ, Space) Fibre Space ω where
  toEquiv := coordinateEquiv.toLinearEquiv.toEquiv
  contMDiff_toFun := (coordinateEquiv.contDiff (n := ω)).contMDiff
  contMDiff_invFun := (coordinateEquiv.symm.contDiff (n := ω)).contMDiff

@[simp] theorem diffeomorph_apply (v : Fibre) :
    diffeomorph v = coordinateEquiv v := rfl

@[simp] theorem diffeomorph_symm_apply (x : Space) :
    diffeomorph.symm x = coordinateEquiv.symm x := rfl

theorem radiusSq_le_iff_mem_closedBall (r : ℝ) (hr : 0 ≤ r) (v : Fibre) :
    radiusSq v ≤ r ^ 2 ↔ coordinateEquiv v ∈ closedBall (0 : Space) r := by
  rw [← coordinateEquiv_norm_sq, mem_closedBall, dist_zero_right]
  exact sq_le_sq₀ (norm_nonneg _) hr

theorem radiusSq_lt_iff_mem_ball (r : ℝ) (hr : 0 ≤ r) (v : Fibre) :
    radiusSq v < r ^ 2 ↔ coordinateEquiv v ∈ ball (0 : Space) r := by
  rw [← coordinateEquiv_norm_sq, mem_ball, dist_zero_right]
  exact sq_lt_sq₀ (norm_nonneg _) hr

theorem radiusSq_eq_iff_mem_sphere (r : ℝ) (hr : 0 ≤ r) (v : Fibre) :
    radiusSq v = r ^ 2 ↔ coordinateEquiv v ∈ sphere (0 : Space) r := by
  rw [← coordinateEquiv_norm_sq, mem_sphere, dist_zero_right]
  exact sq_eq_sq₀ (norm_nonneg _) hr

/-- The actual closed normal-radius disk is the standard round closed four-ball. -/
def closedBallHomeomorph (r : ℝ) (hr : 0 ≤ r) :
    {v : Fibre // radiusSq v ≤ r ^ 2} ≃ₜ closedBall (0 : Space) r :=
  coordinateEquiv.toHomeomorph.subtype (radiusSq_le_iff_mem_closedBall r hr)

@[simp] theorem closedBallHomeomorph_coe (r : ℝ) (hr : 0 ≤ r)
    (v : {v : Fibre // radiusSq v ≤ r ^ 2}) :
    (closedBallHomeomorph r hr v : Space) = coordinateEquiv v := rfl

@[simp] theorem closedBallHomeomorph_symm_coe (r : ℝ) (hr : 0 ≤ r)
    (x : closedBall (0 : Space) r) :
    (closedBallHomeomorph r hr |>.symm x : Fibre) = coordinateEquiv.symm x := rfl

/-- The actual open normal-radius disk is the standard round open four-ball. -/
def openBallHomeomorph (r : ℝ) (hr : 0 ≤ r) :
    {v : Fibre // radiusSq v < r ^ 2} ≃ₜ ball (0 : Space) r :=
  coordinateEquiv.toHomeomorph.subtype (radiusSq_lt_iff_mem_ball r hr)

@[simp] theorem openBallHomeomorph_coe (r : ℝ) (hr : 0 ≤ r)
    (v : {v : Fibre // radiusSq v < r ^ 2}) :
    (openBallHomeomorph r hr v : Space) = coordinateEquiv v := rfl

@[simp] theorem openBallHomeomorph_symm_coe (r : ℝ) (hr : 0 ≤ r)
    (x : ball (0 : Space) r) :
    (openBallHomeomorph r hr |>.symm x : Fibre) = coordinateEquiv.symm x := rfl

/-- The normal-radius boundary is the usual round Euclidean three-sphere. -/
def sphereHomeomorph (r : ℝ) (hr : 0 ≤ r) :
    {v : Fibre // radiusSq v = r ^ 2} ≃ₜ sphere (0 : Space) r :=
  coordinateEquiv.toHomeomorph.subtype (radiusSq_eq_iff_mem_sphere r hr)

@[simp] theorem sphereHomeomorph_coe (r : ℝ) (hr : 0 ≤ r)
    (v : {v : Fibre // radiusSq v = r ^ 2}) :
    (sphereHomeomorph r hr v : Space) = coordinateEquiv v := rfl

@[simp] theorem sphereHomeomorph_symm_coe (r : ℝ) (hr : 0 ≤ r)
    (x : sphere (0 : Space) r) :
    (sphereHomeomorph r hr |>.symm x : Fibre) = coordinateEquiv.symm x := rfl

end Wikipedia.HopfProblem.CuspCircleNormalTrivialization.RealFour
