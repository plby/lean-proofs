import Wikipedia.NoExoticSixSphere.SphereRadialRetraction
import Wikipedia.NoExoticSixSphere.GLOrthonormalization
import Wikipedia.SmoothSixDPoincare.SphereBoundaryKernel
import Mathlib.Geometry.Manifold.LocalDiffeomorph

/-!
# Smooth signed-height coordinates around the unit three-sphere

The radius is `sqrt (1 + t)` and its inverse height is `‖x‖² - 1`.
These are actual inverse smooth maps on `t > -1` and `x ≠ 0`, including
both sides of the unit sphere. No radial smoothness at zero is asserted.
-/

noncomputable section

open Set Function Metric
open scoped Manifold ContDiff
open Wikipedia.SmoothSixDPoincare.SphereBoundary

namespace NoExoticSixSphere.RadialHeightCoordinates

open GLOrthonormalization

local instance : Fact (Module.finrank ℝ (Vector 4) = 3 + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

def point (p : Sphere 3 × ℝ) : Vector 4 := Real.sqrt (1 + p.2) • p.1.val

def inverse (b : Sphere 3) (x : Vector 4) : Sphere 3 × ℝ :=
  (SphereRadialRetraction.retract b x, definingFunction x)

theorem norm_point (p : Sphere 3 × ℝ) : ‖point p‖ = Real.sqrt (1 + p.2) := by
  rw [point, norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
    ClosedHemisphere.unit_norm, mul_one]

theorem point_ne_zero {p : Sphere 3 × ℝ} (hp : -1 < p.2) : point p ≠ 0 := by
  apply norm_pos_iff.mp
  rw [norm_point]
  exact Real.sqrt_pos.2 (by linarith)

theorem retract_point (b : Sphere 3) {p : Sphere 3 × ℝ} (hp : -1 < p.2) :
    SphereRadialRetraction.retract b (point p) = p.1 := by
  apply Subtype.ext
  rw [SphereRadialRetraction.retract, dif_neg (point_ne_zero hp)]
  change NormedSpace.normalize (Real.sqrt (1 + p.2) • p.1.val) = p.1.val
  rw [NormedSpace.normalize_smul_of_pos (Real.sqrt_pos.2 (by linarith))]
  exact NormedSpace.normalize_eq_self_of_norm_eq_one (ClosedHemisphere.unit_norm p.1)

theorem definingFunction_point {p : Sphere 3 × ℝ} (hp : -1 < p.2) :
    definingFunction (point p) = p.2 := by
  rw [definingFunction, norm_point, Real.sq_sqrt (by linarith)]
  ring

theorem inverse_point (b : Sphere 3) {p : Sphere 3 × ℝ} (hp : -1 < p.2) :
    inverse b (point p) = p :=
  Prod.ext (retract_point b hp) (definingFunction_point hp)

theorem point_inverse (b : Sphere 3) {x : Vector 4} (hx : x ≠ 0) :
    point (inverse b x) = x := by
  have hρ : 1 + definingFunction x = ‖x‖ ^ 2 := by dsimp [definingFunction]; ring
  change Real.sqrt (1 + definingFunction x) •
    (SphereRadialRetraction.retract b x).val = x
  rw [hρ, Real.sqrt_sq (norm_nonneg x), SphereRadialRetraction.retract, dif_neg hx]
  exact NormedSpace.norm_smul_normalize x

theorem inverse_height_gt (b : Sphere 3) {x : Vector 4} (hx : x ≠ 0) :
    -1 < (inverse b x).2 := by
  change -1 < ‖x‖ ^ 2 - 1
  nlinarith [norm_pos_iff.mpr hx]

theorem contMDiffAt_point {p : Sphere 3 × ℝ} (hp : -1 < p.2) :
    ContMDiffAt ((𝓡 3).prod 𝓘(ℝ, ℝ)) (𝓡 4) ∞ point p := by
  have hr : ContDiffAt ℝ ∞ (fun t : ℝ ↦ Real.sqrt (1 + t)) p.2 :=
    (contDiffAt_const.add contDiffAt_id).sqrt (by change 1 + p.2 ≠ 0; linarith)
  have ht : ContMDiffAt ((𝓡 3).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (Prod.snd : Sphere 3 × ℝ → ℝ) p := contMDiff_snd.contMDiffAt
  have hs : ContMDiffAt ((𝓡 3).prod 𝓘(ℝ, ℝ)) (𝓡 4) ∞
      (fun q : Sphere 3 × ℝ ↦ q.1.val) p :=
    ((show ContMDiff (𝓡 3) (𝓡 4) ∞ (fun s : Sphere 3 ↦ s.val) from
      contMDiff_coe_sphere).comp contMDiff_fst).contMDiffAt
  exact (hr.comp_contMDiffAt ht).smul hs

theorem contMDiffAt_inverse (b : Sphere 3) {x : Vector 4} (hx : x ≠ 0) :
    ContMDiffAt (𝓡 4) ((𝓡 3).prod 𝓘(ℝ, ℝ)) ∞ (inverse b) x :=
  (SphereRadialRetraction.contMDiffAt_retract (E := Vector 4) (n := 3) b hx).prodMk
    contDiff_definingFunction.contMDiff.contMDiffAt

def chart (b : Sphere 3) : PartialDiffeomorph ((𝓡 3).prod 𝓘(ℝ, ℝ)) (𝓡 4)
    (Sphere 3 × ℝ) (Vector 4) ∞ where
  toFun := point
  invFun := inverse b
  source := {p | -1 < p.2}
  target := {x | x ≠ 0}
  map_source' _ hp := point_ne_zero hp
  map_target' _ hx := inverse_height_gt b hx
  left_inv' _ hp := inverse_point b hp
  right_inv' _ hx := point_inverse b hx
  open_source := isOpen_lt continuous_const continuous_snd
  open_target := isOpen_ne
  contMDiffOn_toFun _ hp := (contMDiffAt_point hp).contMDiffWithinAt
  contMDiffOn_invFun _ hx := (contMDiffAt_inverse b hx).contMDiffWithinAt

theorem point_zero (s : Sphere 3) : point (s, 0) = s.val := by simp [point]

end NoExoticSixSphere.RadialHeightCoordinates
