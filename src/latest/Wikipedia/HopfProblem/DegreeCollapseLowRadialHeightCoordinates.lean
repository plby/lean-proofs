import Wikipedia.NoExoticSixSphere.SphereRadialRetraction
import Wikipedia.NoExoticSixSphere.GLOrthonormalization
import Wikipedia.SmoothSixDPoincare.SphereBoundaryKernel
import Mathlib.Geometry.Manifold.LocalDiffeomorph

/-!

# Actual smooth signed-height coordinates around every standard sphere

The radius is sqrt(1+t) and the inverse height is the actual sphere defining
function. These maps are smooth inverses on t greater than -1 and nonzero
vectors. The statement applies on both sides of the original unit sphere,
without asserting radial smoothness at zero.
-/

noncomputable section

open Set Function Metric
open scoped Manifold ContDiff
open Wikipedia.SmoothSixDPoincare.SphereBoundary

namespace Wikipedia.HopfProblem.DegreeCollapse.LowRadialHeightCoordinates

open NoExoticSixSphere GLOrthonormalization

variable {d : ℕ}

local instance : Fact (Module.finrank ℝ (Vector (d + 1)) = d + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

def point (p : NoExoticSixSphere.Sphere d × ℝ) : Vector (d + 1) := Real.sqrt (1 + p.2) • p.1.val

def inverse (b : NoExoticSixSphere.Sphere d) (x : Vector (d + 1)) :
    NoExoticSixSphere.Sphere d × ℝ :=
  (SphereRadialRetraction.retract b x, definingFunction x)

theorem norm_point (p : NoExoticSixSphere.Sphere d × ℝ) : ‖point p‖ = Real.sqrt (1 + p.2) := by
  rw [point, norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
    ClosedHemisphere.unit_norm, mul_one]

theorem point_ne_zero {p : NoExoticSixSphere.Sphere d × ℝ} (hp : -1 < p.2) : point p ≠ 0 := by
  apply norm_pos_iff.mp
  rw [norm_point]
  exact Real.sqrt_pos.2 (by linarith)

theorem retract_point (b : NoExoticSixSphere.Sphere d)
    {p : NoExoticSixSphere.Sphere d × ℝ} (hp : -1 < p.2) :
    SphereRadialRetraction.retract b (point p) = p.1 := by
  apply Subtype.ext
  rw [SphereRadialRetraction.retract, dif_neg (point_ne_zero hp)]
  change NormedSpace.normalize (Real.sqrt (1 + p.2) • p.1.val) = p.1.val
  rw [NormedSpace.normalize_smul_of_pos (Real.sqrt_pos.2 (by linarith))]
  exact NormedSpace.normalize_eq_self_of_norm_eq_one (ClosedHemisphere.unit_norm p.1)

theorem definingFunction_point {p : NoExoticSixSphere.Sphere d × ℝ} (hp : -1 < p.2) :
    definingFunction (point p) = p.2 := by
  rw [definingFunction, norm_point, Real.sq_sqrt (by linarith)]
  ring

theorem inverse_point (b : NoExoticSixSphere.Sphere d)
    {p : NoExoticSixSphere.Sphere d × ℝ} (hp : -1 < p.2) :
    inverse b (point p) = p :=
  Prod.ext (retract_point b hp) (definingFunction_point hp)

theorem point_inverse (b : NoExoticSixSphere.Sphere d) {x : Vector (d + 1)} (hx : x ≠ 0) :
    point (inverse b x) = x := by
  have hρ : 1 + definingFunction x = ‖x‖ ^ 2 := by dsimp [definingFunction]; ring
  change Real.sqrt (1 + definingFunction x) •
    (SphereRadialRetraction.retract b x).val = x
  rw [hρ, Real.sqrt_sq (norm_nonneg x), SphereRadialRetraction.retract, dif_neg hx]
  exact NormedSpace.norm_smul_normalize x

theorem inverse_height_gt (b : NoExoticSixSphere.Sphere d) {x : Vector (d + 1)} (hx : x ≠ 0) :
    -1 < (inverse b x).2 := by
  change -1 < ‖x‖ ^ 2 - 1
  nlinarith [norm_pos_iff.mpr hx]

theorem contMDiffAt_point {p : NoExoticSixSphere.Sphere d × ℝ} (hp : -1 < p.2) :
    ContMDiffAt ((𝓡 d).prod 𝓘(ℝ, ℝ)) (𝓡 (d + 1)) ∞ point p := by
  have hr : ContDiffAt ℝ ∞ (fun t : ℝ ↦ Real.sqrt (1 + t)) p.2 :=
    (contDiffAt_const.add contDiffAt_id).sqrt (by change 1 + p.2 ≠ 0; linarith)
  have ht : ContMDiffAt ((𝓡 d).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (Prod.snd : NoExoticSixSphere.Sphere d × ℝ → ℝ) p := contMDiff_snd.contMDiffAt
  have hs : ContMDiffAt ((𝓡 d).prod 𝓘(ℝ, ℝ)) (𝓡 (d + 1)) ∞
      (fun q : NoExoticSixSphere.Sphere d × ℝ ↦ q.1.val) p :=
    ((show ContMDiff (𝓡 d) (𝓡 (d + 1)) ∞ (fun s : NoExoticSixSphere.Sphere d ↦ s.val) from
      contMDiff_coe_sphere).comp contMDiff_fst).contMDiffAt
  exact (hr.comp_contMDiffAt ht).smul hs

theorem contMDiffAt_inverse (b : NoExoticSixSphere.Sphere d) {x : Vector (d + 1)} (hx : x ≠ 0) :
    ContMDiffAt (𝓡 (d + 1)) ((𝓡 d).prod 𝓘(ℝ, ℝ)) ∞ (inverse b) x :=
  (SphereRadialRetraction.contMDiffAt_retract (E := Vector (d + 1)) (n := d) b hx).prodMk
    contDiff_definingFunction.contMDiff.contMDiffAt

def chart (b : NoExoticSixSphere.Sphere d) :
    PartialDiffeomorph ((𝓡 d).prod 𝓘(ℝ, ℝ)) (𝓡 (d + 1))
    (NoExoticSixSphere.Sphere d × ℝ) (Vector (d + 1)) ∞ where
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

theorem point_zero (s : NoExoticSixSphere.Sphere d) : point (s, 0) = s.val := by simp [point]

end Wikipedia.HopfProblem.DegreeCollapse.LowRadialHeightCoordinates
