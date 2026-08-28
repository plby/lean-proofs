import Wikipedia.NoExoticSixSphere.DiskRadialFlattening
import Wikipedia.SmoothSixDPoincare.SphereBoundaryKernel

/-!
# The flattened disk with a normal height is embedded and immersive

The height distinguishes radii; positive radial scaling retains directions.
At the derivative level the height detects the radial direction and the
positive scalar factor detects tangent directions. No immersion of the
radially flattened map alone is asserted.
-/

noncomputable section

open Function
open scoped ContDiff
open Wikipedia.SmoothSixDPoincare.SphereBoundary

namespace NoExoticSixSphere.DiskRadialFlattening

open GLOrthonormalization

theorem normalize_map (n : ℕ) (x : Vector (n + 1)) :
    NormedSpace.normalize (map n x) = NormedSpace.normalize x :=
  NormedSpace.normalize_smul_of_pos (scalar_pos n x) x

def heightMap (n : ℕ) (x : Vector (n + 1)) : Vector (n + 1) × ℝ :=
  (map n x, definingFunction x)

theorem contDiff_heightMap (n : ℕ) : ContDiff ℝ ∞ (heightMap n) :=
  (contDiff_map n).prodMk contDiff_definingFunction

theorem injective_heightMap (n : ℕ) : Injective (heightMap n) := by
  intro x y h
  have hρ : ‖x‖ ^ 2 - 1 = ‖y‖ ^ 2 - 1 := congrArg Prod.snd h
  have hn : ‖x‖ = ‖y‖ := (sq_eq_sq₀ (norm_nonneg x) (norm_nonneg y)).mp (by linarith)
  have hd := congrArg NormedSpace.normalize (congrArg Prod.fst h)
  change NormedSpace.normalize (map n x) = NormedSpace.normalize (map n y) at hd
  rw [normalize_map, normalize_map] at hd
  calc
    x = ‖x‖ • NormedSpace.normalize x := (NormedSpace.norm_smul_normalize x).symm
    _ = ‖y‖ • NormedSpace.normalize y := by rw [hn, hd]
    _ = y := NormedSpace.norm_smul_normalize y

theorem fderiv_map_apply (n : ℕ) (x v : Vector (n + 1)) :
    fderiv ℝ (map n) x v = scalar n x • v + fderiv ℝ (scalar n) x v • x := by
  have hs := ((contDiff_scalar n).differentiable (by simp) x).hasFDerivAt
  have hd := hs.smul (hasFDerivAt_id x)
  rw [show fderiv ℝ (map n) x = _ from hd.fderiv]
  rfl

theorem common_kernel (n : ℕ) (x v : Vector (n + 1))
    (hψ : fderiv ℝ (map n) x v = 0)
    (hρ : fderiv ℝ (definingFunction (E := Vector (n + 1))) x v = 0) : v = 0 := by
  have hinner := (fderiv_definingFunction_eq_zero_iff x v).mp hρ
  have h := congrArg (fun w : Vector (n + 1) ↦ inner ℝ w v) hψ
  rw [fderiv_map_apply, inner_add_left, real_inner_smul_left, real_inner_smul_left,
    hinner, mul_zero, add_zero, inner_zero_left, real_inner_self_eq_norm_sq] at h
  have hn : ‖v‖ ^ 2 = 0 := (mul_eq_zero.mp h).resolve_left (ne_of_gt (scalar_pos n x))
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp hn)

theorem injective_fderiv_heightMap (n : ℕ) (x : Vector (n + 1)) :
    Injective (fderiv ℝ (heightMap n) x) := by
  have hψ := ((contDiff_map n).differentiable (by simp) x).hasFDerivAt
  have hρ := ((contDiff_definingFunction (E := Vector (n + 1))).differentiable
    (by simp) x).hasFDerivAt
  have hd := hψ.prodMk hρ
  apply (injective_iff_map_eq_zero _).mpr
  intro v hv
  rw [show fderiv ℝ (heightMap n) x = _ from hd.fderiv] at hv
  exact common_kernel n x v (congrArg Prod.fst hv) (congrArg Prod.snd hv)

end NoExoticSixSphere.DiskRadialFlattening
