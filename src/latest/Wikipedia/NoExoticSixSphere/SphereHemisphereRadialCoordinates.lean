import Wikipedia.NoExoticSixSphere.SphereCylinderPoles
import Wikipedia.NoExoticSixSphere.PartialFrames

/-!
# Native radial coordinates on the open northern hemisphere

Dividing the tail by the positive first coordinate gives a genuine smooth
chart, including the north pole. Its inverse normalizes the vector `(1,x)`.
On the existing cylinder chart this is exactly the reciprocal radial map,
which will match the complementary sphere chart at a neck's infinite end.
-/

noncomputable section

open Set Function Topology
open scoped Manifold ContDiff

namespace NoExoticSixSphere.SphereSumNeck

open GLOrthonormalization

def gnomonic (x : Sphere 3) : Vector 3 := (x.val 0)⁻¹ • SphereCylinder.tail 2 x.val

def capVector (v : Vector 3) : Vector 4 := SphereCylinder.join 2 (1, v)

theorem capVector_ne_zero (v : Vector 3) : capVector v ≠ 0 := by
  intro h
  have he := congrArg (fun x : Vector 4 ↦ x 0) h
  change (1 : ℝ) = 0 at he
  exact one_ne_zero he

def gnomonicInverse (v : Vector 3) : Sphere 3 :=
  SphereRadialRetraction.retract (SphereCylinder.endPole 2 true) (capVector v)

theorem gnomonicInverse_val (v : Vector 3) :
    (gnomonicInverse v).val = ‖capVector v‖⁻¹ • capVector v := by
  simp only [gnomonicInverse, SphereRadialRetraction.retract,
    dif_neg (capVector_ne_zero v), NormedSpace.normalize]

theorem gnomonicInverse_head (v : Vector 3) :
    (gnomonicInverse v).val 0 = ‖capVector v‖⁻¹ := by
  rw [gnomonicInverse_val]
  change ‖capVector v‖⁻¹ * 1 = ‖capVector v‖⁻¹
  exact mul_one _

theorem gnomonicInverse_head_pos (v : Vector 3) : 0 < (gnomonicInverse v).val 0 := by
  rw [gnomonicInverse_head]
  exact inv_pos.mpr (norm_pos_iff.mpr (capVector_ne_zero v))

theorem gnomonic_gnomonicInverse (v : Vector 3) : gnomonic (gnomonicInverse v) = v := by
  rw [gnomonic, gnomonicInverse_head, gnomonicInverse_val, map_smul]
  change (‖capVector v‖⁻¹)⁻¹ • (‖capVector v‖⁻¹ • v) = v
  rw [inv_inv, smul_inv_smul₀ (norm_ne_zero_iff.mpr (capVector_ne_zero v))]

theorem capVector_gnomonic (x : Sphere 3) (hx : 0 < x.val 0) :
    capVector (gnomonic x) = (x.val 0)⁻¹ • x.val := by
  ext i
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · change 1 = (x.val 0)⁻¹ * x.val 0
    exact (inv_mul_cancel₀ hx.ne').symm
  · rfl

theorem gnomonicInverse_gnomonic (x : Sphere 3) (hx : 0 < x.val 0) :
    gnomonicInverse (gnomonic x) = x := by
  apply Subtype.ext
  rw [gnomonicInverse_val, capVector_gnomonic x hx]
  change NormedSpace.normalize ((x.val 0)⁻¹ • x.val) = x.val
  rw [NormedSpace.normalize_smul_of_pos (inv_pos.mpr hx)]
  exact NormedSpace.normalize_eq_self_of_norm_eq_one (ClosedHemisphere.unit_norm x)

theorem contMDiff_gnomonicInverse : ContMDiff (𝓡 3) (𝓡 3) ∞ gnomonicInverse := by
  let : Fact (Module.finrank ℝ (Vector 4) = 3 + 1) := ⟨finrank_euclideanSpace_fin⟩
  have hv : ContDiff ℝ ∞ capVector :=
    (SphereCylinder.join 2).contDiff.comp (contDiff_const.prodMk contDiff_id)
  intro v
  exact (SphereRadialRetraction.contMDiffAt_retract (n := 3)
    (SphereCylinder.endPole 2 true) (capVector_ne_zero v)).comp v (hv.contMDiff v)

theorem contMDiffAt_gnomonic {x : Sphere 3} (hx : 0 < x.val 0) :
    ContMDiffAt (𝓡 3) (𝓡 3) ∞ gnomonic x := by
  let : Fact (Module.finrank ℝ (Vector 4) = 3 + 1) := ⟨finrank_euclideanSpace_fin⟩
  have hc : ContMDiff (𝓡 3) (𝓡 4) ∞ (fun x : Sphere 3 ↦ x.val) :=
    contMDiff_coe_sphere
  have hh : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ (fun x : Sphere 3 ↦ x.val 0) :=
    (contDiff_piLp_apply (𝕜 := ℝ) (n := ∞) 2).contMDiff.comp hc
  exact ((hh x).inv₀ hx.ne').smul
    (((SphereCylinder.tail 2).contDiff.contMDiff.comp hc) x)

def gnomonicChart : PartialDiffeomorph (𝓡 3) (𝓡 3) (Sphere 3) (Vector 3) ∞ where
  toFun := gnomonic
  invFun := gnomonicInverse
  source := {x | 0 < x.val 0}
  target := univ
  map_source' _ _ := mem_univ _
  map_target' v _ := gnomonicInverse_head_pos v
  left_inv' := gnomonicInverse_gnomonic
  right_inv' v _ := gnomonic_gnomonicInverse v
  open_source := isOpen_lt continuous_const
    ((PiLp.continuous_apply 2 _ 0).comp continuous_subtype_val)
  open_target := isOpen_univ
  contMDiffOn_toFun _ hx := (contMDiffAt_gnomonic hx).contMDiffWithinAt
  contMDiffOn_invFun := contMDiff_gnomonicInverse.contMDiffOn

theorem gnomonic_cylinder (t : ℝ) (s : Sphere 2) :
    gnomonic (SphereCylinder.point 2 (t, s)) = t⁻¹ • s.val := by
  have hn := norm_ne_zero_iff.mpr (SphereCylinder.vector_ne_zero 2 (t, s))
  rw [gnomonic, SphereCylinder.point_head, SphereCylinder.tail_point, smul_smul]
  congr 1
  rw [mul_inv_rev, inv_inv, mul_assoc, mul_inv_cancel₀ hn, mul_one]

end NoExoticSixSphere.SphereSumNeck
