import Wikipedia.NoExoticSixSphere.SmoothSphereRadialDerivative
import Wikipedia.NoExoticSixSphere.GLOrthonormalization

/-!
# The original sphere cylinder as a compact Euclidean annulus

The annulus has radii one and two. Its time coordinate is
`(‖x‖² - 1) / 3`, so polynomial time collars become globally smooth
functions of the ambient vector. The inverse uses the positive radius
`sqrt (1 + 3u)`. Both maps and both endpoint values are explicit.
-/

noncomputable section

open Set Metric
open scoped Manifold ContDiff Topology

namespace NoExoticSixSphere.SphereAnnulus

open GLOrthonormalization

def domain (n : ℕ) : Set (Vector (n + 1)) := {x | 1 ≤ ‖x‖ ∧ ‖x‖ ≤ 2}

theorem isClosed_domain (n : ℕ) : IsClosed (domain n) :=
  (isClosed_le continuous_const continuous_norm).inter
    (isClosed_le continuous_norm continuous_const)

theorem isCompact_domain (n : ℕ) : IsCompact (domain n) :=
  (isCompact_closedBall (0 : Vector (n + 1)) 2).of_isClosed_subset (isClosed_domain n)
    (fun _ hx ↦ mem_closedBall_zero_iff.mpr hx.2)

theorem ne_zero {n : ℕ} (x : domain n) : x.val ≠ 0 := by
  intro hx
  have h := x.property.1
  rw [hx, norm_zero] at h
  norm_num at h

def time {n : ℕ} (x : domain n) : unitInterval :=
  ⟨(‖x.val‖ ^ 2 - 1) / 3, by
    have h : 1 ≤ ‖x.val‖ ∧ ‖x.val‖ ≤ 2 := x.property
    constructor <;> nlinarith⟩

theorem time_val {n : ℕ} (x : domain n) :
    (time x : ℝ) = (‖x.val‖ ^ 2 - 1) / 3 := rfl

theorem continuous_time (n : ℕ) : Continuous (time (n := n)) :=
  (((continuous_norm.comp continuous_subtype_val).pow 2).sub continuous_const).div_const
    3 |>.subtype_mk _

def radius (u : unitInterval) : ℝ := Real.sqrt (1 + 3 * (u : ℝ))

theorem radius_sq (u : unitInterval) : radius u ^ 2 = 1 + 3 * (u : ℝ) :=
  Real.sq_sqrt (by have h := u.property.1; linarith)

theorem radius_bounds (u : unitInterval) : 1 ≤ radius u ∧ radius u ≤ 2 := by
  have hp : 0 ≤ radius u := Real.sqrt_nonneg _
  have hs := radius_sq u
  have hu : 0 ≤ (u : ℝ) ∧ (u : ℝ) ≤ 1 := u.property
  constructor <;> nlinarith

theorem radius_pos (u : unitInterval) : 0 < radius u :=
  lt_of_lt_of_le zero_lt_one (radius_bounds u).1

theorem continuous_radius : Continuous radius :=
  Real.continuous_sqrt.comp (continuous_const.add (continuous_const.mul continuous_subtype_val))

def fromCylinder (n : ℕ) : C(unitInterval × Sphere n, domain n) where
  toFun p := ⟨radius p.1 • p.2.val, by
    have hn : ‖radius p.1 • p.2.val‖ = radius p.1 := by
      rw [norm_smul, Real.norm_of_nonneg (radius_pos p.1).le,
        ClosedHemisphere.unit_norm, mul_one]
    change 1 ≤ ‖radius p.1 • p.2.val‖ ∧ ‖radius p.1 • p.2.val‖ ≤ 2
    rw [hn]
    exact radius_bounds p.1⟩
  continuous_toFun := ((continuous_radius.comp continuous_fst).smul
    (continuous_subtype_val.comp continuous_snd)).subtype_mk _

theorem fromCylinder_val {n : ℕ} (u : unitInterval) (q : Sphere n) :
    (fromCylinder n (u, q)).val = radius u • q.val := rfl

theorem norm_fromCylinder {n : ℕ} (u : unitInterval) (q : Sphere n) :
    ‖(fromCylinder n (u, q)).val‖ = radius u := by
  rw [fromCylinder_val, norm_smul, Real.norm_of_nonneg (radius_pos u).le,
    ClosedHemisphere.unit_norm, mul_one]

def toCylinder {n : ℕ} (b : Sphere n) : C(domain n, unitInterval × Sphere n) where
  toFun x := (time x, SphereRadialRetraction.retract b x.val)
  continuous_toFun := by
    let : Fact (Module.finrank ℝ (Vector (n + 1)) = n + 1) :=
      ⟨finrank_euclideanSpace_fin⟩
    apply (continuous_time n).prodMk
    apply continuous_iff_continuousAt.mpr
    intro x
    exact (SphereRadialRetraction.contMDiffAt_retract (n := n) b (ne_zero x)).continuousAt.comp
      continuous_subtype_val.continuousAt

theorem toCylinder_fromCylinder {n : ℕ} (b : Sphere n) (p : unitInterval × Sphere n) :
    toCylinder b (fromCylinder n p) = p := by
  rcases p with ⟨u, q⟩
  apply Prod.ext
  · apply Subtype.ext
    change (‖(fromCylinder n (u, q)).val‖ ^ 2 - 1) / 3 = (u : ℝ)
    rw [norm_fromCylinder, radius_sq]
    ring
  · exact SphereRadialRetraction.retract_pos_smul b q (radius_pos u)

theorem radius_time {n : ℕ} (x : domain n) : radius (time x) = ‖x.val‖ := by
  have hr := radius_sq (time x)
  rw [time_val] at hr
  have hp := radius_pos (time x)
  have hx := x.property.1
  nlinarith

theorem fromCylinder_toCylinder {n : ℕ} (b : Sphere n) (x : domain n) :
    fromCylinder n (toCylinder b x) = x := by
  apply Subtype.ext
  change radius (time x) • (SphereRadialRetraction.retract b x.val).val = x.val
  rw [radius_time, SphereRadialRetraction.retract, dif_neg (ne_zero x)]
  exact NormedSpace.norm_smul_normalize x.val

def homeomorph {n : ℕ} (b : Sphere n) : domain n ≃ₜ unitInterval × Sphere n where
  toFun := toCylinder b
  invFun := fromCylinder n
  left_inv := fromCylinder_toCylinder b
  right_inv := toCylinder_fromCylinder b
  continuous_toFun := (toCylinder b).continuous
  continuous_invFun := (fromCylinder n).continuous

theorem fromCylinder_zero_val {n : ℕ} (q : Sphere n) : (fromCylinder n (0, q)).val = q.val := by
  rw [fromCylinder_val]
  have hr : radius 0 = 1 := by norm_num [radius]
  rw [hr, one_smul]

theorem fromCylinder_one_val {n : ℕ} (q : Sphere n) :
    (fromCylinder n (1, q)).val = (2 : ℝ) • q.val := by
  rw [fromCylinder_val]
  have hr : radius 1 = 2 := by
    have hs := radius_sq (1 : unitInterval)
    have hp := radius_pos (1 : unitInterval)
    norm_num at hs
    nlinarith
  rw [hr]

theorem time_pos_iff {n : ℕ} (x : domain n) : 0 < (time x : ℝ) ↔ 1 < ‖x.val‖ := by
  rw [time_val]
  have hx : 1 ≤ ‖x.val‖ ∧ ‖x.val‖ ≤ 2 := x.property
  constructor <;> intro h <;> nlinarith

theorem time_lt_one_iff {n : ℕ} (x : domain n) : (time x : ℝ) < 1 ↔ ‖x.val‖ < 2 := by
  rw [time_val]
  have hx : 1 ≤ ‖x.val‖ ∧ ‖x.val‖ ≤ 2 := x.property
  constructor <;> intro h <;> nlinarith

theorem time_le_third_iff {n : ℕ} (x : domain n) :
    (time x : ℝ) ≤ 1 / 3 ↔ ‖x.val‖ ^ 2 ≤ 2 := by
  rw [time_val]
  constructor <;> intro h <;> linarith

theorem two_thirds_le_time_iff {n : ℕ} (x : domain n) :
    2 / 3 ≤ (time x : ℝ) ↔ 3 ≤ ‖x.val‖ ^ 2 := by
  rw [time_val]
  constructor <;> intro h <;> linarith

end NoExoticSixSphere.SphereAnnulus
