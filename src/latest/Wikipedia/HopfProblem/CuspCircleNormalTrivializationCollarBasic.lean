import Mathlib.Geometry.Manifold.Instances.Sphere

/-!
# The literal radial collar of the half-unit three-sphere

The forward map is positive radial scaling, and the inverse consists of
normalization and the affine radial coordinate. All topologies are the
original Euclidean, sphere, product, and open-subspace topologies.
-/

noncomputable section

open Set TopologicalSpace

namespace Wikipedia.HopfProblem.CuspCircleNormalTrivialization.Collar

/-- The original four-dimensional Euclidean space. -/
abbrev Space := EuclideanSpace ℝ (Fin 4)

/-- The unit three-sphere with its original subspace topology. -/
abbrev Sphere := Metric.sphere (0 : Space) 1

/-- The open interval of collar parameters. -/
def interval : Opens ℝ := ⟨Ioo (-(1 / 2 : ℝ)) (1 / 2), isOpen_Ioo⟩

/-- The actual Euclidean annulus around the half-unit sphere. -/
def annulus : Opens Space :=
  ⟨{x | (1 / 4 : ℝ) < ‖x‖ ∧ ‖x‖ < (3 / 4 : ℝ)},
    (isOpen_lt continuous_const continuous_norm).inter
      (isOpen_lt continuous_norm continuous_const)⟩

/-- The affine positive radial coordinate on the collar interval. -/
def radialScale (t : ℝ) : ℝ := (1 / 2 : ℝ) + t / 2

@[simp] theorem radialScale_zero : radialScale 0 = (1 / 2 : ℝ) := by
  simp [radialScale]

theorem radialScale_bounds (t : interval) :
    (1 / 4 : ℝ) < radialScale t ∧ radialScale t < (3 / 4 : ℝ) := by
  have ht : -(1 / 2 : ℝ) < (t : ℝ) ∧ (t : ℝ) < (1 / 2 : ℝ) := t.property
  dsimp [radialScale]
  constructor <;> linarith [ht.1, ht.2]

theorem radialScale_pos (t : interval) : 0 < radialScale t := by
  have ht := (radialScale_bounds t).1
  linarith

theorem radialScale_ne_zero (t : interval) : radialScale t ≠ 0 :=
  ne_of_gt (radialScale_pos t)

theorem radialScale_continuous : Continuous radialScale :=
  continuous_const.add (continuous_id.div_const 2)

/-- The center parameter of the collar. -/
def zeroParameter : interval := ⟨0, by norm_num [interval]⟩

@[simp] theorem zeroParameter_coe : (zeroParameter : ℝ) = 0 := rfl

theorem annulus_norm_bounds (x : annulus) :
    (1 / 4 : ℝ) < ‖(x : Space)‖ ∧ ‖(x : Space)‖ < (3 / 4 : ℝ) := x.property

theorem annulus_norm_pos (x : annulus) : 0 < ‖(x : Space)‖ := by
  have hx := (annulus_norm_bounds x).1
  linarith

theorem annulus_norm_ne_zero (x : annulus) : ‖(x : Space)‖ ≠ 0 :=
  ne_of_gt (annulus_norm_pos x)

theorem annulus_ne_zero (x : annulus) : (x : Space) ≠ 0 :=
  norm_pos_iff.mp (annulus_norm_pos x)

/-- Positive radial scaling into the actual annulus. -/
def forward (p : Sphere × interval) : annulus :=
  ⟨radialScale p.2 • (p.1 : Space), by
    change (1 / 4 : ℝ) < ‖radialScale p.2 • (p.1 : Space)‖ ∧
      ‖radialScale p.2 • (p.1 : Space)‖ < (3 / 4 : ℝ)
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (radialScale_pos p.2),
      norm_eq_of_mem_sphere p.1, mul_one]
    exact radialScale_bounds p.2⟩

@[simp] theorem forward_coe (p : Sphere × interval) :
    (forward p : Space) = radialScale p.2 • (p.1 : Space) := rfl

@[simp] theorem norm_forward (p : Sphere × interval) :
    ‖(forward p : Space)‖ = radialScale p.2 := by
  rw [forward_coe, norm_smul, Real.norm_eq_abs, abs_of_pos (radialScale_pos p.2),
    norm_eq_of_mem_sphere p.1, mul_one]

@[simp] theorem forward_zeroParameter_coe (u : Sphere) :
    (forward (u, zeroParameter) : Space) = (1 / 2 : ℝ) • (u : Space) := by
  rw [forward_coe, zeroParameter_coe, radialScale_zero]

/-- The actual normalized direction of a nonzero annulus point. -/
def unitDirection (x : annulus) : Sphere :=
  ⟨‖(x : Space)‖⁻¹ • (x : Space), by
    have hn : ‖‖(x : Space)‖⁻¹ • (x : Space)‖ = 1 := by
      rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (annulus_norm_ne_zero x)]
    simpa only [Metric.mem_sphere, dist_zero_right] using hn⟩

@[simp] theorem unitDirection_coe (x : annulus) :
    (unitDirection x : Space) = ‖(x : Space)‖⁻¹ • (x : Space) := rfl

/-- The affine radial parameter of an annulus point. -/
def inverseParameter (x : annulus) : interval :=
  ⟨2 * ‖(x : Space)‖ - 1, by
    change -(1 / 2 : ℝ) < 2 * ‖(x : Space)‖ - 1 ∧
      2 * ‖(x : Space)‖ - 1 < (1 / 2 : ℝ)
    have hx := annulus_norm_bounds x
    constructor <;> linarith [hx.1, hx.2]⟩

@[simp] theorem inverseParameter_coe (x : annulus) :
    (inverseParameter x : ℝ) = 2 * ‖(x : Space)‖ - 1 := rfl

@[simp] theorem radialScale_inverseParameter (x : annulus) :
    radialScale (inverseParameter x) = ‖(x : Space)‖ := by
  rw [inverseParameter_coe]
  dsimp [radialScale]
  ring

/-- The literal normalization and affine-radius inverse. -/
def inverse (x : annulus) : Sphere × interval := (unitDirection x, inverseParameter x)

@[simp] theorem inverse_fst_coe (x : annulus) :
    ((inverse x).1 : Space) = ‖(x : Space)‖⁻¹ • (x : Space) := rfl

@[simp] theorem inverse_snd_coe (x : annulus) :
    ((inverse x).2 : ℝ) = 2 * ‖(x : Space)‖ - 1 := rfl

@[simp] theorem inverse_forward (p : Sphere × interval) : inverse (forward p) = p := by
  apply Prod.ext
  · apply Subtype.ext
    change ‖(forward p : Space)‖⁻¹ • (forward p : Space) = (p.1 : Space)
    rw [norm_forward, forward_coe, smul_smul,
      inv_mul_cancel₀ (radialScale_ne_zero p.2), one_smul]
  · apply Subtype.ext
    change 2 * ‖(forward p : Space)‖ - 1 = (p.2 : ℝ)
    rw [norm_forward]
    dsimp [radialScale]
    ring

@[simp] theorem forward_inverse (x : annulus) : forward (inverse x) = x := by
  apply Subtype.ext
  change radialScale (inverseParameter x) • (‖(x : Space)‖⁻¹ • (x : Space)) = (x : Space)
  rw [radialScale_inverseParameter, smul_smul,
    mul_inv_cancel₀ (annulus_norm_ne_zero x), one_smul]

theorem forward_continuous : Continuous forward := by
  have ht : Continuous (fun p : Sphere × interval => (p.2 : ℝ)) :=
    continuous_subtype_val.comp continuous_snd
  have hu : Continuous (fun p : Sphere × interval => (p.1 : Space)) :=
    continuous_subtype_val.comp continuous_fst
  exact ((radialScale_continuous.comp ht).smul hu).subtype_mk _

theorem unitDirection_continuous : Continuous unitDirection := by
  have hx : Continuous (fun x : annulus => (x : Space)) := continuous_subtype_val
  exact ((hx.norm.inv₀ annulus_norm_ne_zero).smul hx).subtype_mk _

theorem inverseParameter_continuous : Continuous inverseParameter := by
  have h : Continuous (fun x : annulus => 2 * ‖(x : Space)‖ - 1) :=
    (continuous_const.mul continuous_subtype_val.norm).sub continuous_const
  exact h.subtype_mk _

theorem inverse_continuous : Continuous inverse :=
  unitDirection_continuous.prodMk inverseParameter_continuous

/-- The genuine radial collar homeomorphism, with the original topologies on both sides. -/
def radialHomeomorph : Sphere × interval ≃ₜ annulus where
  toEquiv := {
    toFun := forward
    invFun := inverse
    left_inv := inverse_forward
    right_inv := forward_inverse }
  continuous_toFun := forward_continuous
  continuous_invFun := inverse_continuous

@[simp] theorem radialHomeomorph_apply (p : Sphere × interval) :
    radialHomeomorph p = forward p := rfl

@[simp] theorem radialHomeomorph_symm_apply (x : annulus) :
    radialHomeomorph.symm x = inverse x := rfl

end Wikipedia.HopfProblem.CuspCircleNormalTrivialization.Collar
