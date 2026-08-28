import Wikipedia.HopfProblem.CuspCircleNormalTrivializationRealFour

/-!
# The explicit standard circle rotation of real four-space

Complex scalar multiplication on the two normal coordinates becomes two
identical real two-by-two rotation blocks. The formulas below define the map
directly in standard Euclidean coordinates. A unit scalar of norm one gives a
real linear isometry equivalence, with the actual scalar multiplication laws.
-/

noncomputable section

open scoped ContDiff Matrix

namespace Wikipedia.HopfProblem.CuspCircleNormalTrivialization.RealFour

/-- The literal two-block real matrix of a complex scalar. -/
def rotationMap (u : ℂ) (x : Space) : Space :=
  (EuclideanSpace.equiv (Fin 4) ℝ).symm
    ![u.re * x 0 - u.im * x 1, u.im * x 0 + u.re * x 1,
      u.re * x 2 - u.im * x 3, u.im * x 2 + u.re * x 3]

@[simp] theorem rotationMap_apply (u : ℂ) (x : Space) (i : Fin 4) :
    rotationMap u x i =
      ![u.re * x 0 - u.im * x 1, u.im * x 0 + u.re * x 1,
        u.re * x 2 - u.im * x 3, u.im * x 2 + u.re * x 3] i := rfl

/-- The explicit real blocks are exactly the original complex scalar action. -/
theorem rotationMap_coordinateEquiv (u : ℂ) (v : Fibre) :
    rotationMap u (coordinateEquiv v) = coordinateEquiv (u • v) := by
  ext i
  fin_cases i
  · change u.re * v.1.re - u.im * v.1.im = (u * v.1).re
    exact (Complex.mul_re u v.1).symm
  · change u.im * v.1.re + u.re * v.1.im = (u * v.1).im
    rw [Complex.mul_im]
    exact add_comm _ _
  · change u.re * v.2.re - u.im * v.2.im = (u * v.2).re
    exact (Complex.mul_re u v.2).symm
  · change u.im * v.2.re + u.re * v.2.im = (u * v.2).im
    rw [Complex.mul_im]
    exact add_comm _ _

theorem rotationMap_eq_coordinateEquiv (u : ℂ) (x : Space) :
    rotationMap u x = coordinateEquiv (u • coordinateEquiv.symm x) := by
  simpa only [coordinateEquiv.apply_symm_apply] using
    rotationMap_coordinateEquiv u (coordinateEquiv.symm x)

@[simp] theorem rotationMap_one (x : Space) : rotationMap 1 x = x := by
  rw [rotationMap_eq_coordinateEquiv, one_smul, coordinateEquiv.apply_symm_apply]

theorem rotationMap_mul (u v : ℂ) (x : Space) :
    rotationMap (u * v) x = rotationMap u (rotationMap v x) := by
  obtain ⟨w, rfl⟩ := coordinateEquiv.surjective x
  simp only [rotationMap_coordinateEquiv, mul_smul]

theorem rotationMap_add (u : ℂ) (x y : Space) :
    rotationMap u (x + y) = rotationMap u x + rotationMap u y := by
  simp only [rotationMap_eq_coordinateEquiv, map_add, smul_add]

theorem rotationMap_real_smul (u : ℂ) (a : ℝ) (x : Space) :
    rotationMap u (a • x) = a • rotationMap u x := by
  simp only [rotationMap_eq_coordinateEquiv, map_smul, smul_comm u a]

/-- The squared norm formula holds for all complex scalars, not only units. -/
theorem rotationMap_norm_sq (u : ℂ) (x : Space) :
    ‖rotationMap u x‖ ^ 2 = Complex.normSq u * ‖x‖ ^ 2 := by
  rw [rotationMap_eq_coordinateEquiv, coordinateEquiv_norm_sq, radiusSq_smul,
    coordinateEquiv_symm_radiusSq]

theorem rotationMap_norm (u : ℂ) (hu : ‖u‖ = 1) (x : Space) :
    ‖rotationMap u x‖ = ‖x‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [rotationMap_norm_sq, Complex.normSq_eq_norm_sq, hu, one_pow, one_mul]

/-- These real matrix blocks are jointly real analytic in scalar and vector. -/
theorem contDiff_rotationMap {n : ℕ∞ω} :
    ContDiff ℝ n (fun p : ℂ × Space => rotationMap p.1 p.2) := by
  simp_rw [rotationMap_eq_coordinateEquiv]
  exact coordinateEquiv.contDiff.comp
    (contDiff_fst.smul (coordinateEquiv.symm.contDiff.comp contDiff_snd))

theorem continuous_rotationMap :
    Continuous (fun p : ℂ × Space => rotationMap p.1 p.2) :=
  (contDiff_rotationMap (n := ω)).continuous

/-- A norm-one complex unit acts by the standard real linear rotation isometry. -/
def rotation (u : ℂˣ) (hu : ‖(u : ℂ)‖ = 1) : Space ≃ₗᵢ[ℝ] Space where
  toFun := rotationMap (u : ℂ)
  invFun := rotationMap ((u⁻¹ : ℂˣ) : ℂ)
  left_inv x := by
    rw [← rotationMap_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, rotationMap_one]
  right_inv x := by
    rw [← rotationMap_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, rotationMap_one]
  map_add' := rotationMap_add (u : ℂ)
  map_smul' := rotationMap_real_smul (u : ℂ)
  norm_map' := rotationMap_norm (u : ℂ) hu

theorem rotation_toFun (u : ℂˣ) (hu : ‖(u : ℂ)‖ = 1) :
    (rotation u hu : Space → Space) = rotationMap (u : ℂ) := rfl

@[simp] theorem rotation_apply (u : ℂˣ) (hu : ‖(u : ℂ)‖ = 1)
    (x : Space) (i : Fin 4) :
    rotation u hu x i =
      ![(u : ℂ).re * x 0 - (u : ℂ).im * x 1,
        (u : ℂ).im * x 0 + (u : ℂ).re * x 1,
        (u : ℂ).re * x 2 - (u : ℂ).im * x 3,
        (u : ℂ).im * x 2 + (u : ℂ).re * x 3] i := rfl

@[simp] theorem rotation_symm_apply (u : ℂˣ) (hu : ‖(u : ℂ)‖ = 1) (x : Space) :
    (rotation u hu).symm x = rotationMap ((u⁻¹ : ℂˣ) : ℂ) x := rfl

/-- Exact equivariance of the original two complex normal coordinates. -/
theorem coordinateEquiv_smul_rotation (u : ℂˣ) (hu : ‖(u : ℂ)‖ = 1) (v : Fibre) :
    coordinateEquiv ((u : ℂ) • v) = rotation u hu (coordinateEquiv v) :=
  (rotationMap_coordinateEquiv (u : ℂ) v).symm

theorem coordinateEquiv_symm_rotation (u : ℂˣ) (hu : ‖(u : ℂ)‖ = 1) (x : Space) :
    coordinateEquiv.symm (rotation u hu x) = (u : ℂ) • coordinateEquiv.symm x := by
  apply coordinateEquiv.injective
  rw [coordinateEquiv.apply_symm_apply, coordinateEquiv_smul_rotation,
    coordinateEquiv.apply_symm_apply]

@[simp] theorem rotation_one :
    rotation (1 : ℂˣ) (by simp) = (1 : Space ≃ₗᵢ[ℝ] Space) := by
  apply LinearIsometryEquiv.ext
  exact rotationMap_one

/-- Multiplication uses the ordinary left-action order on Euclidean vectors. -/
theorem rotation_mul (u v : ℂˣ) (hu : ‖(u : ℂ)‖ = 1) (hv : ‖(v : ℂ)‖ = 1) :
    rotation (u * v) (by simp only [Units.val_mul, norm_mul, hu, hv, mul_one]) =
      rotation u hu * rotation v hv := by
  apply LinearIsometryEquiv.ext
  exact rotationMap_mul (u : ℂ) (v : ℂ)

@[simp] theorem rotation_inv (u : ℂˣ) (hu : ‖(u : ℂ)‖ = 1) :
    rotation u⁻¹ (by simp only [Units.val_inv_eq_inv_val, norm_inv, hu, inv_one]) =
      (rotation u hu).symm := by
  apply LinearIsometryEquiv.ext
  intro x
  rfl

end Wikipedia.HopfProblem.CuspCircleNormalTrivialization.RealFour
