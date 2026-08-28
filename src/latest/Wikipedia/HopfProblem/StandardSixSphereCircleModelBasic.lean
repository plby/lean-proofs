import Wikipedia.HopfProblem.StandardSixSphereCircleModelCoordinates
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Tactic.FieldSimp

/-!
# Explicit maps for the complement of the equatorial two-sphere

The domain is an open subset of the literal unit sphere in standard
Euclidean seven-space.  The maps below use only its existing subspace
topology.
-/

noncomputable section

namespace Wikipedia.HopfProblem.StandardSixSphereCircleModel

/-- The standard equatorial two-sphere, given by the last four coordinates. -/
def equator : Set Sphere := {p | normal p.val = 0}

/-- The actual open complement in the original unit sphere. -/
def complement : TopologicalSpace.Opens Sphere where
  carrier := {p | normal p.val ≠ 0}
  is_open' := isOpen_ne_fun (continuous_normal.comp continuous_subtype_val) continuous_const

abbrev Complement := ↥complement

@[simp] theorem coe_complement : (complement : Set Sphere) = equatorᶜ := rfl

theorem normal_ne_zero (p : Complement) : normal p.val.val ≠ 0 := p.property

def normalRadius (p : Complement) : ℝ := ‖normal p.val.val‖

theorem normalRadius_pos (p : Complement) : 0 < normalRadius p :=
  norm_pos_iff.mpr (normal_ne_zero p)

theorem normalRadius_ne_zero (p : Complement) : normalRadius p ≠ 0 :=
  (normalRadius_pos p).ne'

theorem normalRadius_le_one (p : Complement) : normalRadius p ≤ 1 := by
  have h := sphere_norm_sq p.val
  dsimp [normalRadius]
  nlinarith [sq_nonneg ‖base p.val.val‖, norm_nonneg (normal p.val.val)]

theorem continuous_normalRadius : Continuous normalRadius :=
  (continuous_normal.comp (continuous_subtype_val.comp continuous_subtype_val)).norm

theorem normalized_normal_mem_sphere (p : Complement) :
    (normalRadius p)⁻¹ • normal p.val.val ∈ NormalSphere := by
  simp only [Metric.mem_sphere, dist_zero_right, norm_smul, Real.norm_eq_abs,
    abs_inv, abs_of_pos (normalRadius_pos p)]
  exact inv_mul_cancel₀ (normalRadius_ne_zero p)

/-- `(x,y) ↦ (x/‖y‖, y/‖y‖)`, with the second component on the unit three-sphere. -/
def forward (p : Complement) : Base × NormalSphere :=
  ((normalRadius p)⁻¹ • base p.val.val,
    ⟨(normalRadius p)⁻¹ • normal p.val.val, normalized_normal_mem_sphere p⟩)

@[simp] theorem forward_fst (p : Complement) :
    (forward p).1 = (normalRadius p)⁻¹ • base p.val.val := rfl

@[simp] theorem forward_snd_val (p : Complement) :
    (forward p).2.val = (normalRadius p)⁻¹ • normal p.val.val := rfl

def denominator (a : Base) : ℝ := Real.sqrt (1 + ‖a‖ ^ 2)
def inverseScale (a : Base) : ℝ := (denominator a)⁻¹

theorem denominator_pos (a : Base) : 0 < denominator a := by
  exact Real.sqrt_pos.mpr (by nlinarith [sq_nonneg ‖a‖])

theorem denominator_ne_zero (a : Base) : denominator a ≠ 0 :=
  (denominator_pos a).ne'

theorem denominator_sq (a : Base) : denominator a ^ 2 = 1 + ‖a‖ ^ 2 :=
  Real.sq_sqrt (by nlinarith [sq_nonneg ‖a‖])

theorem inverseScale_pos (a : Base) : 0 < inverseScale a :=
  inv_pos.mpr (denominator_pos a)

theorem inverseScale_ne_zero (a : Base) : inverseScale a ≠ 0 :=
  (inverseScale_pos a).ne'

theorem continuous_denominator : Continuous denominator :=
  Real.continuous_sqrt.comp (continuous_const.add (continuous_norm.pow 2))

theorem continuous_inverseScale : Continuous inverseScale :=
  continuous_denominator.inv₀ denominator_ne_zero

/-- The inverse formula in the original Euclidean ambient space. -/
def inverseAmbient (a : Base) (u : NormalSphere) : Ambient :=
  inverseScale a • join a u.val

@[simp] theorem base_inverseAmbient (a : Base) (u : NormalSphere) :
    base (inverseAmbient a u) = inverseScale a • a := by
  simp only [inverseAmbient, base_smul, base_join]

@[simp] theorem normal_inverseAmbient (a : Base) (u : NormalSphere) :
    normal (inverseAmbient a u) = inverseScale a • u.val := by
  simp only [inverseAmbient, normal_smul, normal_join]

theorem inverseAmbient_mem_sphere (a : Base) (u : NormalSphere) :
    inverseAmbient a u ∈ Sphere := by
  apply mem_sphere_of_norm_sq
  rw [inverseAmbient, norm_smul, Real.norm_eq_abs, abs_of_pos (inverseScale_pos a),
    mul_pow, join_norm_sq, normalSphere_norm, one_pow]
  rw [add_comm (‖a‖ ^ 2) 1, ← denominator_sq, inverseScale]
  field_simp [denominator_ne_zero a]

theorem norm_normal_inverseAmbient (a : Base) (u : NormalSphere) :
    ‖normal (inverseAmbient a u)‖ = inverseScale a := by
  rw [normal_inverseAmbient, norm_smul, Real.norm_eq_abs,
    abs_of_pos (inverseScale_pos a), normalSphere_norm, mul_one]

theorem normal_inverseAmbient_ne_zero (a : Base) (u : NormalSphere) :
    normal (inverseAmbient a u) ≠ 0 := by
  apply norm_ne_zero_iff.mp
  rw [norm_normal_inverseAmbient]
  exact inverseScale_ne_zero a

/-- `(a,u) ↦ (a,u)/sqrt(1+‖a‖²)`, as a point of the actual complement. -/
def inverse (q : Base × NormalSphere) : Complement :=
  ⟨⟨inverseAmbient q.1 q.2, inverseAmbient_mem_sphere q.1 q.2⟩,
    normal_inverseAmbient_ne_zero q.1 q.2⟩

@[simp] theorem inverse_val_val (q : Base × NormalSphere) :
    (inverse q).val.val = inverseScale q.1 • join q.1 q.2.val := rfl

@[simp] theorem normalRadius_inverse (q : Base × NormalSphere) :
    normalRadius (inverse q) = inverseScale q.1 :=
  norm_normal_inverseAmbient q.1 q.2

theorem forward_inverse (q : Base × NormalSphere) : forward (inverse q) = q := by
  apply Prod.ext
  · change (normalRadius (inverse q))⁻¹ • base (inverseAmbient q.1 q.2) = q.1
    rw [normalRadius_inverse, base_inverseAmbient,
      inv_smul_smul₀ (inverseScale_ne_zero q.1)]
  · apply Subtype.ext
    change (normalRadius (inverse q))⁻¹ • normal (inverseAmbient q.1 q.2) = q.2.val
    rw [normalRadius_inverse, normal_inverseAmbient,
      inv_smul_smul₀ (inverseScale_ne_zero q.1)]

theorem denominator_forward (p : Complement) :
    denominator (forward p).1 = (normalRadius p)⁻¹ := by
  apply (sq_eq_sq₀ (denominator_pos _).le (inv_pos.mpr (normalRadius_pos p)).le).mp
  rw [denominator_sq, forward_fst, norm_smul, Real.norm_eq_abs, abs_inv,
    abs_of_pos (normalRadius_pos p), mul_pow]
  have h := sphere_norm_sq p.val
  change ‖base p.val.val‖ ^ 2 + normalRadius p ^ 2 = 1 at h
  field_simp [normalRadius_ne_zero p]
  nlinarith

@[simp] theorem inverseScale_forward (p : Complement) :
    inverseScale (forward p).1 = normalRadius p := by
  rw [inverseScale, denominator_forward, inv_inv]

theorem inverse_forward (p : Complement) : inverse (forward p) = p := by
  apply Subtype.ext
  apply Subtype.ext
  apply split.injective
  apply Prod.ext
  · change base (inverseAmbient (forward p).1 (forward p).2) = base p.val.val
    rw [base_inverseAmbient, inverseScale_forward, forward_fst,
      smul_inv_smul₀ (normalRadius_ne_zero p)]
  · change normal (inverseAmbient (forward p).1 (forward p).2) = normal p.val.val
    rw [normal_inverseAmbient, inverseScale_forward, forward_snd_val,
      smul_inv_smul₀ (normalRadius_ne_zero p)]

theorem continuous_forward : Continuous forward := by
  have hs := continuous_normalRadius.inv₀ normalRadius_ne_zero
  exact (hs.smul (continuous_base.comp
    (continuous_subtype_val.comp continuous_subtype_val))).prodMk
      ((hs.smul (continuous_normal.comp
        (continuous_subtype_val.comp continuous_subtype_val))).subtype_mk _)

theorem continuous_inverseAmbient :
    Continuous (fun q : Base × NormalSphere => inverseAmbient q.1 q.2) := by
  have hs : Continuous (fun q : Base × NormalSphere => inverseScale q.1) :=
    continuous_inverseScale.comp continuous_fst
  have hp : Continuous (fun q : Base × NormalSphere => (q.1, q.2.val)) :=
    continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)
  have hj : Continuous (fun q : Base × NormalSphere => join q.1 q.2.val) :=
    Continuous.comp (g := fun p : Base × Normal => join p.1 p.2)
      (f := fun q : Base × NormalSphere => (q.1, q.2.val)) continuous_join hp
  exact hs.smul hj

theorem continuous_inverse : Continuous inverse :=
  (continuous_inverseAmbient.subtype_mk _).subtype_mk _

/-- The explicit complement homeomorphism; all topologies are the original ones. -/
def homeomorph : Complement ≃ₜ Base × NormalSphere where
  toFun := forward
  invFun := inverse
  left_inv := inverse_forward
  right_inv := forward_inverse
  continuous_toFun := continuous_forward
  continuous_invFun := continuous_inverse

@[simp] theorem homeomorph_apply (p : Complement) : homeomorph p = forward p := rfl

@[simp] theorem homeomorph_symm_apply (q : Base × NormalSphere) :
    homeomorph.symm q = inverse q := rfl

end Wikipedia.HopfProblem.StandardSixSphereCircleModel
