import Wikipedia.HopfProblem.StandardSixSphereCircleModelBasic
import Mathlib.Topology.Homeomorph.Lemmas

/-!
# The marked normal-radius boundaries in the standard sphere complement

At normal radius `r`, the original sphere coordinates are
`(sqrt (1-r²) • v, r • u)` for unit vectors `v ∈ S²`, `u ∈ S³`.
The complement chart sends this to `(sqrt (1-r²)/r • v, u)`.
In particular the normal unit vector is preserved, with no conjugation
or sign change.
-/

noncomputable section

namespace Wikipedia.HopfProblem.StandardSixSphereCircleModel

def boundaryBaseRadius (r : ℝ) : ℝ := Real.sqrt (1 - r ^ 2)
def boundaryProductRadius (r : ℝ) : ℝ := boundaryBaseRadius r / r

theorem boundaryBaseRadius_nonneg (r : ℝ) : 0 ≤ boundaryBaseRadius r :=
  Real.sqrt_nonneg _

theorem boundaryBaseRadius_pos {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    0 < boundaryBaseRadius r := by
  apply Real.sqrt_pos.mpr
  nlinarith

theorem boundaryBaseRadius_sq {r : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1) :
    boundaryBaseRadius r ^ 2 = 1 - r ^ 2 :=
  Real.sq_sqrt (by nlinarith)

theorem boundaryProductRadius_pos {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    0 < boundaryProductRadius r :=
  div_pos (boundaryBaseRadius_pos hr hr1) hr

/-- The literal coordinates of a marked tube boundary on the standard sphere. -/
def boundaryAmbient (r : ℝ) (q : BaseSphere × NormalSphere) : Ambient :=
  join (boundaryBaseRadius r • q.1.val) (r • q.2.val)

@[simp] theorem base_boundaryAmbient (r : ℝ) (q : BaseSphere × NormalSphere) :
    base (boundaryAmbient r q) = boundaryBaseRadius r • q.1.val :=
  base_join _ _

@[simp] theorem normal_boundaryAmbient (r : ℝ) (q : BaseSphere × NormalSphere) :
    normal (boundaryAmbient r q) = r • q.2.val := normal_join _ _

theorem boundaryAmbient_mem_sphere {r : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (q : BaseSphere × NormalSphere) : boundaryAmbient r q ∈ Sphere := by
  apply mem_sphere_of_norm_sq
  rw [boundaryAmbient, join_norm_sq, norm_smul, norm_smul,
    Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (boundaryBaseRadius_nonneg r), abs_of_nonneg hr,
    baseSphere_norm, normalSphere_norm, mul_one, mul_one,
    boundaryBaseRadius_sq hr hr1]
  ring

theorem norm_normal_boundaryAmbient {r : ℝ} (hr : 0 ≤ r)
    (q : BaseSphere × NormalSphere) : ‖normal (boundaryAmbient r q)‖ = r := by
  rw [normal_boundaryAmbient, norm_smul, Real.norm_eq_abs, abs_of_nonneg hr,
    normalSphere_norm, mul_one]

def boundaryPoint (r : ℝ) (hr : 0 < r) (hr1 : r < 1)
    (q : BaseSphere × NormalSphere) : Complement :=
  ⟨⟨boundaryAmbient r q, boundaryAmbient_mem_sphere hr.le hr1.le q⟩,
    norm_ne_zero_iff.mp ((norm_normal_boundaryAmbient hr.le q).trans_ne hr.ne')⟩

@[simp] theorem boundaryPoint_val_val (r : ℝ) (hr : 0 < r) (hr1 : r < 1)
    (q : BaseSphere × NormalSphere) :
    (boundaryPoint r hr hr1 q).val.val =
      join (boundaryBaseRadius r • q.1.val) (r • q.2.val) := rfl

@[simp] theorem normalRadius_boundaryPoint (r : ℝ) (hr : 0 < r) (hr1 : r < 1)
    (q : BaseSphere × NormalSphere) : normalRadius (boundaryPoint r hr hr1 q) = r :=
  norm_normal_boundaryAmbient hr.le q

/-- The exact marked boundary formula; the normal unit vector is unchanged. -/
theorem forward_boundaryPoint (r : ℝ) (hr : 0 < r) (hr1 : r < 1)
    (q : BaseSphere × NormalSphere) :
    forward (boundaryPoint r hr hr1 q) = (boundaryProductRadius r • q.1.val, q.2) := by
  apply Prod.ext
  · change (normalRadius (boundaryPoint r hr hr1 q))⁻¹ •
      base (boundaryAmbient r q) = boundaryProductRadius r • q.1.val
    rw [normalRadius_boundaryPoint, base_boundaryAmbient, smul_smul]
    congr 1
    exact inv_mul_eq_div _ _
  · apply Subtype.ext
    change (normalRadius (boundaryPoint r hr hr1 q))⁻¹ •
      normal (boundaryAmbient r q) = q.2.val
    rw [normalRadius_boundaryPoint, normal_boundaryAmbient, inv_smul_smul₀ hr.ne']

theorem continuous_boundaryAmbient (r : ℝ) : Continuous (boundaryAmbient r) := by
  have hv : Continuous (fun q : BaseSphere × NormalSphere => q.1.val) :=
    continuous_subtype_val.comp continuous_fst
  have hu : Continuous (fun q : BaseSphere × NormalSphere => q.2.val) :=
    continuous_subtype_val.comp continuous_snd
  have hb : Continuous (fun q : BaseSphere × NormalSphere =>
      boundaryBaseRadius r • q.1.val) :=
    (continuous_const : Continuous
      (fun _ : BaseSphere × NormalSphere => boundaryBaseRadius r)).smul hv
  have hn : Continuous (fun q : BaseSphere × NormalSphere => r • q.2.val) :=
    (continuous_const : Continuous (fun _ : BaseSphere × NormalSphere => r)).smul hu
  exact Continuous.comp (g := fun p : Base × Normal => join p.1 p.2)
    (f := fun q : BaseSphere × NormalSphere =>
      (boundaryBaseRadius r • q.1.val, r • q.2.val)) continuous_join (hb.prodMk hn)

theorem continuous_boundaryPoint (r : ℝ) (hr : 0 < r) (hr1 : r < 1) :
    Continuous (boundaryPoint r hr hr1) :=
  ((continuous_boundaryAmbient r).subtype_mk _).subtype_mk _

theorem base_norm_of_normalRadius {r : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (p : Complement) (hp : normalRadius p = r) : ‖base p.val.val‖ = boundaryBaseRadius r := by
  apply (sq_eq_sq₀ (norm_nonneg _) (boundaryBaseRadius_nonneg r)).mp
  have h := sphere_norm_sq p.val
  change ‖base p.val.val‖ ^ 2 + normalRadius p ^ 2 = 1 at h
  rw [hp] at h
  rw [boundaryBaseRadius_sq hr hr1]
  linarith

theorem norm_forward_fst (p : Complement) :
    ‖(forward p).1‖ = ‖base p.val.val‖ / normalRadius p := by
  rw [forward_fst, norm_smul, Real.norm_eq_abs, abs_inv,
    abs_of_pos (normalRadius_pos p), inv_mul_eq_div]

theorem denominator_of_norm_boundaryProductRadius {r : ℝ} (hr : 0 < r) (hr1 : r < 1)
    (a : Base) (ha : ‖a‖ = boundaryProductRadius r) : denominator a = r⁻¹ := by
  apply (sq_eq_sq₀ (denominator_pos a).le (inv_pos.mpr hr).le).mp
  rw [denominator_sq, ha, boundaryProductRadius, div_pow,
    boundaryBaseRadius_sq hr.le hr1.le]
  field_simp
  ring

theorem inverseScale_of_norm_boundaryProductRadius {r : ℝ} (hr : 0 < r) (hr1 : r < 1)
    (a : Base) (ha : ‖a‖ = boundaryProductRadius r) : inverseScale a = r := by
  rw [inverseScale, denominator_of_norm_boundaryProductRadius hr hr1 a ha, inv_inv]

/-- A complete correspondence of level sets, not just an inclusion of markings. -/
theorem normalRadius_eq_iff_norm_forward {r : ℝ} (hr : 0 < r) (hr1 : r < 1)
    (p : Complement) :
    normalRadius p = r ↔ ‖(forward p).1‖ = boundaryProductRadius r := by
  constructor
  · intro hp
    rw [norm_forward_fst, base_norm_of_normalRadius hr.le hr1.le p hp, hp]
    rfl
  · intro hp
    rw [← inverseScale_forward p,
      inverseScale_of_norm_boundaryProductRadius hr hr1 (forward p).1 hp]

def normalLevel (r : ℝ) : Set Complement := {p | normalRadius p = r}
def productLevel (r : ℝ) : Set (Base × NormalSphere) :=
  {q | ‖q.1‖ = boundaryProductRadius r}

theorem homeomorph_preimage_productLevel {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    homeomorph ⁻¹' productLevel r = normalLevel r := by
  ext p
  exact (normalRadius_eq_iff_norm_forward hr hr1 p).symm

/-- Restriction of the same actual complement chart to its full radius level set. -/
def levelHomeomorph (r : ℝ) (hr : 0 < r) (hr1 : r < 1) :
    ↥(normalLevel r) ≃ₜ ↥(productLevel r) :=
  homeomorph.subtype (normalRadius_eq_iff_norm_forward hr hr1)

@[simp] theorem levelHomeomorph_val (r : ℝ) (hr : 0 < r) (hr1 : r < 1)
    (p : ↥(normalLevel r)) : (levelHomeomorph r hr hr1 p).val = forward p.val := rfl

end Wikipedia.HopfProblem.StandardSixSphereCircleModel
