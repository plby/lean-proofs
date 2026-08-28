import Wikipedia.NoExoticSixSphere.HandleSuperlevel
import Wikipedia.NoExoticSixSphere.SphereRadialRetraction
import Wikipedia.NoExoticSixSphere.RegularLevelManifold

/-! # Actual four-space times two-sphere coordinates on the handle zero set -/

noncomputable section

open Function Set Metric
open scoped Manifold ContDiff

namespace NoExoticSixSphere.HandleSuperlevel

open GLOrthonormalization

local instance : Fact (Module.finrank ℝ (Vector 3) = 2 + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

variable {r : ℝ} (hr : 0 < r)

def zeroPoint (r : ℝ) (p : Vector 4 × Sphere 2) : Vector 4 × Vector 3 :=
  (p.1, r • p.2.val)

include hr in
theorem norm_zeroPoint_snd (p : Vector 4 × Sphere 2) : ‖(zeroPoint r p).2‖ = r := by
  rw [zeroPoint, norm_smul, Real.norm_eq_abs, abs_of_pos hr,
    ClosedHemisphere.unit_norm, mul_one]

include hr in
theorem level_zeroPoint (p : Vector 4 × Sphere 2) : level r (zeroPoint r p) = 0 := by
  apply (zero_iff hr _).mpr
  simpa only [mem_sphere, dist_zero_right] using norm_zeroPoint_snd hr p

def zeroInverse (b : Sphere 2) (p : Vector 4 × Vector 3) : Vector 4 × Sphere 2 :=
  (p.1, SphereRadialRetraction.retract b p.2)

include hr in
theorem zeroInverse_zeroPoint (b : Sphere 2) (p : Vector 4 × Sphere 2) :
    zeroInverse b (zeroPoint r p) = p := by
  apply Prod.ext
  · rfl
  apply Subtype.ext
  have hn : (zeroPoint r p).2 ≠ 0 := by
    apply norm_pos_iff.mp
    rw [norm_zeroPoint_snd hr]
    exact hr
  change (SphereRadialRetraction.retract b (zeroPoint r p).2).val = p.2.val
  rw [SphereRadialRetraction.retract, dif_neg hn]
  change NormedSpace.normalize (r • p.2.val) = p.2.val
  rw [NormedSpace.normalize_smul_of_pos hr]
  exact NormedSpace.normalize_eq_self_of_norm_eq_one (ClosedHemisphere.unit_norm p.2)

include hr in
theorem zeroPoint_zeroInverse (b : Sphere 2) {p : Vector 4 × Vector 3}
    (hp : level r p = 0) : zeroPoint r (zeroInverse b p) = p := by
  have hn : ‖p.2‖ = r := by
    simpa only [mem_sphere, dist_zero_right] using (zero_iff hr p).mp hp
  have hne : p.2 ≠ 0 := norm_pos_iff.mp (by rw [hn]; exact hr)
  apply Prod.ext
  · rfl
  change r • (SphereRadialRetraction.retract b p.2).val = p.2
  rw [SphereRadialRetraction.retract, dif_neg hne, ← hn]
  exact NormedSpace.norm_smul_normalize p.2

theorem contMDiff_zeroPoint (r : ℝ) :
    ContMDiff ((𝓡 4).prod (𝓡 2)) 𝓘(ℝ, Vector 4 × Vector 3) ∞ (zeroPoint r) := by
  have hs : ContMDiff ((𝓡 4).prod (𝓡 2)) (𝓡 3) ∞
      (fun p : Vector 4 × Sphere 2 ↦ p.2.val) :=
    (contMDiff_coe_sphere (E := Vector 3) (n := 2)).comp contMDiff_snd
  have hc : ContMDiff ((𝓡 4).prod (𝓡 2)) 𝓘(ℝ, ℝ) ∞
      (fun _ : Vector 4 × Sphere 2 ↦ r) := contMDiff_const
  exact contMDiff_fst.prodMk_space (hc.smul hs)

theorem contMDiffAt_zeroInverse (b : Sphere 2) {p : Vector 4 × Vector 3} (hp : p.2 ≠ 0) :
    ContMDiffAt 𝓘(ℝ, Vector 4 × Vector 3) ((𝓡 4).prod (𝓡 2)) ∞ (zeroInverse b) p :=
  contDiff_fst.contMDiff.contMDiffAt.prodMk
    ((SphereRadialRetraction.contMDiffAt_retract (E := Vector 3) (n := 2) b hp).comp p
      contDiff_snd.contMDiff.contMDiffAt)

def zeroEquiv (b : Sphere 2) : (Vector 4 × Sphere 2) ≃
    {p : Vector 4 × Vector 3 // level r p = 0} where
  toFun p := ⟨zeroPoint r p, level_zeroPoint hr p⟩
  invFun p := zeroInverse b p.val
  left_inv := zeroInverse_zeroPoint hr b
  right_inv p := Subtype.ext (zeroPoint_zeroInverse hr b p.property)

def zeroDiffeomorph (b : Sphere 2)
    (R : RegularLevelAtlas (K := Vector 6) 𝓘(ℝ, Vector 4 × Vector 3)
      (level (d := 3) r)) :
    letI := R.chartedSpace;
    (Vector 4 × Sphere 2) ≃ₘ⟮(𝓡 4).prod (𝓡 2), 𝓡 6⟯
      {p : Vector 4 × Vector 3 // level r p = 0} := by
  let := R.chartedSpace
  refine
    { toEquiv := zeroEquiv hr b
      contMDiff_toFun := ?_
      contMDiff_invFun := ?_ }
  · exact (R.contMDiff_iff_ambient _).mpr (contMDiff_zeroPoint r)
  · intro p
    have hn : ‖p.val.2‖ = r := by
      simpa only [mem_sphere, dist_zero_right] using (zero_iff hr p.val).mp p.property
    exact (contMDiffAt_zeroInverse b (norm_pos_iff.mp (by rw [hn]; exact hr))).comp p
      R.contMDiff_subtype_val.contMDiffAt

end NoExoticSixSphere.HandleSuperlevel
