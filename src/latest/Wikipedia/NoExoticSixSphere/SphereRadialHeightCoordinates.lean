import Wikipedia.NoExoticSixSphere.SphereRadialRetraction
import Wikipedia.SmoothSixDPoincare.SphereBoundaryKernel
import Mathlib.Geometry.Manifold.LocalDiffeomorph

/-!
# Signed radial-height coordinates in an arbitrary sphere dimension

The actual maps are `sqrt (1 + t) • s` and `(normalize x, ‖x‖² - 1)`.
They are mutually inverse and smooth precisely on `t > -1` and `x ≠ 0`.
This version also supplies the transverse two-sphere coordinates of surgery.
-/

noncomputable section

open Set Function Metric
open scoped Manifold ContDiff
open Wikipedia.SmoothSixDPoincare.SphereBoundary

namespace NoExoticSixSphere.SphereRadialHeightCoordinates

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def point (p : UnitSphere E × ℝ) : E := Real.sqrt (1 + p.2) • p.1.val

def inverse (b : UnitSphere E) (x : E) : UnitSphere E × ℝ :=
  (SphereRadialRetraction.retract b x, definingFunction x)

theorem norm_point (p : UnitSphere E × ℝ) : ‖point p‖ = Real.sqrt (1 + p.2) := by
  rw [point, norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
    ClosedHemisphere.unit_norm, mul_one]

theorem point_ne_zero {p : UnitSphere E × ℝ} (hp : -1 < p.2) : point p ≠ 0 := by
  apply norm_pos_iff.mp
  rw [norm_point]
  exact Real.sqrt_pos.mpr (by linarith)

theorem inverse_point (b : UnitSphere E) {p : UnitSphere E × ℝ} (hp : -1 < p.2) :
    inverse b (point p) = p := by
  apply Prod.ext
  · apply Subtype.ext
    rw [inverse, SphereRadialRetraction.retract, dif_neg (point_ne_zero hp)]
    change NormedSpace.normalize (Real.sqrt (1 + p.2) • p.1.val) = p.1.val
    rw [NormedSpace.normalize_smul_of_pos (Real.sqrt_pos.mpr (by linarith))]
    exact NormedSpace.normalize_eq_self_of_norm_eq_one (ClosedHemisphere.unit_norm p.1)
  · change definingFunction (point p) = p.2
    rw [definingFunction, norm_point, Real.sq_sqrt (by linarith)]
    ring

theorem point_inverse (b : UnitSphere E) {x : E} (hx : x ≠ 0) :
    point (inverse b x) = x := by
  have hρ : 1 + definingFunction x = ‖x‖ ^ 2 := by dsimp [definingFunction]; ring
  change Real.sqrt (1 + definingFunction x) • (SphereRadialRetraction.retract b x).val = x
  rw [hρ, Real.sqrt_sq (norm_nonneg x), SphereRadialRetraction.retract, dif_neg hx]
  exact NormedSpace.norm_smul_normalize x

theorem inverse_height_gt (b : UnitSphere E) {x : E} (hx : x ≠ 0) :
    -1 < (inverse b x).2 := by
  change -1 < ‖x‖ ^ 2 - 1
  nlinarith [norm_pos_iff.mpr hx]

variable {n : ℕ} [Fact (Module.finrank ℝ E = n + 1)]

theorem contMDiffAt_point {p : UnitSphere E × ℝ} (hp : -1 < p.2) :
    ContMDiffAt ((𝓡 n).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) ∞ point p := by
  have hr : ContDiffAt ℝ ∞ (fun t : ℝ ↦ Real.sqrt (1 + t)) p.2 :=
    (contDiffAt_const.add contDiffAt_id).sqrt (by change 1 + p.2 ≠ 0; linarith)
  have ht : ContMDiffAt ((𝓡 n).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (Prod.snd : UnitSphere E × ℝ → ℝ) p := contMDiff_snd.contMDiffAt
  have hs : ContMDiffAt ((𝓡 n).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) ∞
      (fun q : UnitSphere E × ℝ ↦ q.1.val) p :=
    ((contMDiff_coe_sphere (E := E) (n := n)).comp contMDiff_fst).contMDiffAt
  exact (hr.comp_contMDiffAt ht).smul hs

theorem contMDiffAt_inverse (b : UnitSphere E) {x : E} (hx : x ≠ 0) :
    ContMDiffAt 𝓘(ℝ, E) ((𝓡 n).prod 𝓘(ℝ, ℝ)) ∞ (inverse b) x :=
  (SphereRadialRetraction.contMDiffAt_retract (n := n) b hx).prodMk
    contDiff_definingFunction.contMDiff.contMDiffAt

def chart (b : UnitSphere E) : PartialDiffeomorph ((𝓡 n).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E)
    (UnitSphere E × ℝ) E ∞ where
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

end NoExoticSixSphere.SphereRadialHeightCoordinates
