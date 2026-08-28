import Wikipedia.NoExoticSixSphere.SphereSumNeckProfile
import Wikipedia.NoExoticSixSphere.SphereRadialRetraction
import Wikipedia.NoExoticSixSphere.PartialFrames
import Wikipedia.NoExoticSixSphere.PartialFrameConnectivity
import Mathlib.Geometry.Manifold.LocalDiffeomorph

/-!
# Actual radial partial diffeomorphism for one neck projection

On the positive-profile region, radial size recovers the original time
and normalization recovers the original two-sphere point. These explicit
inverse maps are smooth on the actual open regions. Thus either positive
projection supplies genuine local coordinates for the neck.
-/

noncomputable section

open Set Function Topology
open scoped Manifold ContDiff

namespace NoExoticSixSphere.SphereSumNeck

open GLOrthonormalization

abbrev Parameter := ℝ × Sphere 2

abbrev Model := (𝓘(ℝ, ℝ)).prod (𝓡 2)

def radialMap (q : Parameter) : Vector 3 := profile q.1 • q.2.val

def radialInverse (x : Vector 3) : Parameter :=
  (radialTime ‖x‖, SphereRadialRetraction.retract (Stiefel.pole 2) x)

theorem norm_radialMap (q : Parameter) : ‖radialMap q‖ = profile q.1 := by
  rw [radialMap, norm_smul, Real.norm_eq_abs, abs_of_nonneg (profile_nonneg q.1),
    ClosedHemisphere.unit_norm, mul_one]

theorem radial_retract_smul (s : Sphere 2) {r : ℝ} (hr : 0 < r) :
    SphereRadialRetraction.retract (Stiefel.pole 2) (r • s.val) = s := by
  have hx : r • s.val ≠ 0 := smul_ne_zero hr.ne' (ne_zero_of_mem_unit_sphere s)
  apply Subtype.ext
  simp only [SphereRadialRetraction.retract, dif_neg hx]
  rw [NormedSpace.normalize_smul_of_pos hr,
    NormedSpace.normalize_eq_self_of_norm_eq_one (ClosedHemisphere.unit_norm s)]

theorem radialInverse_radialMap (q : Parameter) (hq : -1 < q.1) :
    radialInverse (radialMap q) = q := by
  apply Prod.ext
  · change radialTime ‖radialMap q‖ = q.1
    rw [norm_radialMap, radialTime_profile hq]
  · exact radial_retract_smul q.2 ((profile_pos_iff q.1).mpr hq)

theorem radialMap_radialInverse (x : Vector 3) (hx : ‖x‖ ∈ Ioo (0 : ℝ) 1) :
    radialMap (radialInverse x) = x := by
  have hne : x ≠ 0 := norm_pos_iff.mp hx.1
  change profile (radialTime ‖x‖) • (SphereRadialRetraction.retract (Stiefel.pole 2) x).val = x
  rw [profile_radialTime hx]
  simp only [SphereRadialRetraction.retract, dif_neg hne]
  exact NormedSpace.norm_smul_normalize x

theorem contMDiff_radialMap : ContMDiff Model (𝓡 3) ∞ radialMap := by
  let : Fact (Module.finrank ℝ (Vector 3) = 2 + 1) := ⟨finrank_euclideanSpace_fin⟩
  have hS : ContMDiff Model (𝓡 3) ∞ (fun q : Parameter ↦ q.2.val) :=
    contMDiff_coe_sphere.comp contMDiff_snd
  exact (contDiff_profile.contMDiff.comp contMDiff_fst).smul hS

theorem contMDiffAt_radialInverse (x : Vector 3) (hx : ‖x‖ ∈ Ioo (0 : ℝ) 1) :
    ContMDiffAt (𝓡 3) Model ∞ radialInverse x := by
  let : Fact (Module.finrank ℝ (Vector 3) = 2 + 1) := ⟨finrank_euclideanSpace_fin⟩
  have hne : x ≠ 0 := norm_pos_iff.mp hx.1
  have hn : ContDiffAt ℝ ∞ (norm : Vector 3 → ℝ) x := contDiffAt_norm ℝ hne
  exact ((contDiffAt_radialTime hx).comp x hn).contMDiffAt.prodMk
    (SphereRadialRetraction.contMDiffAt_retract (n := 2) (Stiefel.pole 2) hne)

def radialCoordinates : PartialDiffeomorph Model (𝓡 3) Parameter (Vector 3) ∞ where
  toFun := radialMap
  invFun := radialInverse
  source := {q | -1 < q.1}
  target := {x | ‖x‖ ∈ Ioo (0 : ℝ) 1}
  map_source' q hq := by
    change ‖radialMap q‖ ∈ Ioo (0 : ℝ) 1
    rw [norm_radialMap]
    exact profile_mem_Ioo hq
  map_target' x hx := radialTime_gt hx
  left_inv' := radialInverse_radialMap
  right_inv' := radialMap_radialInverse
  open_source := isOpen_lt continuous_const continuous_fst
  open_target := isOpen_Ioo.preimage continuous_norm
  contMDiffOn_toFun := contMDiff_radialMap.contMDiffOn
  contMDiffOn_invFun := fun x hx ↦ (contMDiffAt_radialInverse x hx).contMDiffWithinAt

end NoExoticSixSphere.SphereSumNeck
