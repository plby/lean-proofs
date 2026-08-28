import Wikipedia.HopfProblem.DegreeCollapseGeneralRoundedHandleCorner
import Wikipedia.NoExoticSixSphere.RoundedCornerGraph
import Wikipedia.NoExoticSixSphere.SphereRadialRetraction
import Wikipedia.NoExoticSixSphere.RegularLevelManifold

/-!
# The actual transverse rounded boundary is a sphere times a line

Use the positive transverse radius and the difference coordinate on the
planar zero curve. The maps below are actual inverse maps, and their
diffeomorphism is checked against any regular-level atlas on the zero set.
-/

noncomputable section

open Set Function Metric
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.SevenRoundedHandleCorner

open NoExoticSixSphere GLOrthonormalization SmoothCornerRounding

local instance : Fact (Module.finrank ℝ (Vector 4) = 3 + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

variable (χ : ContDiffBump (0 : ℝ)) {r : ℝ} (hr : 0 < r)

def zeroPoint (r : ℝ) (p : Sphere 3 × ℝ) : Vector 4 × ℝ :=
  (graphRadius χ r p.2 • p.1.val, graphHeight χ p.2)

theorem norm_zeroPoint_fst (r : ℝ) (p : Sphere 3 × ℝ) :
    ‖(zeroPoint χ r p).1‖ = graphRadius χ r p.2 := by
  rw [zeroPoint, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (show 0 ≤ graphRadius χ r p.2 from Real.sqrt_nonneg _),
    ClosedHemisphere.unit_norm, mul_one]

theorem coordinates_zeroPoint (r : ℝ) (p : Sphere 3 × ℝ) :
    GeneralRoundedHandleCorner.coordinates r (zeroPoint χ r p) = graph χ p.2 := by
  apply Prod.ext
  · rfl
  · change r ^ 2 - ‖(zeroPoint χ r p).1‖ ^ 2 = graphRadial χ p.2
    rw [norm_zeroPoint_fst, graphRadius_sq]
    ring

theorem level_zeroPoint (r : ℝ) (p : Sphere 3 × ℝ) : GeneralRoundedHandleCorner.level χ r (zeroPoint χ r p) = 0 := by
  change SmoothCornerRounding.level χ (GeneralRoundedHandleCorner.coordinates r (zeroPoint χ r p)) = 0
  rw [coordinates_zeroPoint, level_graph]

def zeroInverse (r : ℝ) (b : Sphere 3) (p : Vector 4 × ℝ) : Sphere 3 × ℝ :=
  (SphereRadialRetraction.retract b p.1, p.2 - (r ^ 2 - ‖p.1‖ ^ 2))

include hr in
theorem zeroInverse_zeroPoint (b : Sphere 3) (p : Sphere 3 × ℝ) :
    zeroInverse r b (zeroPoint χ r p) = p := by
  apply Prod.ext
  · apply Subtype.ext
    have hn : (zeroPoint χ r p).1 ≠ 0 := by
      apply norm_pos_iff.mp
      rw [norm_zeroPoint_fst]
      exact graphRadius_pos χ hr p.2
    change (SphereRadialRetraction.retract b (zeroPoint χ r p).1).val = p.1.val
    rw [SphereRadialRetraction.retract, dif_neg hn]
    change NormedSpace.normalize (graphRadius χ r p.2 • p.1.val) = p.1.val
    rw [NormedSpace.normalize_smul_of_pos (graphRadius_pos χ hr p.2)]
    exact NormedSpace.normalize_eq_self_of_norm_eq_one (ClosedHemisphere.unit_norm p.1)
  · change (GeneralRoundedHandleCorner.coordinates r (zeroPoint χ r p)).1 -
      (GeneralRoundedHandleCorner.coordinates r (zeroPoint χ r p)).2 = p.2
    rw [coordinates_zeroPoint, graph_difference]

include hr in
theorem zeroPoint_zeroInverse (b : Sphere 3) {p : Vector 4 × ℝ}
    (hp : GeneralRoundedHandleCorner.level χ r p = 0) : zeroPoint χ r (zeroInverse r b p) = p := by
  have hg := graph_of_level_zero χ hp
  have hq : graphRadial χ (p.2 - (r ^ 2 - ‖p.1‖ ^ 2)) = r ^ 2 - ‖p.1‖ ^ 2 :=
    congrArg Prod.snd hg
  have ht : graphHeight χ (p.2 - (r ^ 2 - ‖p.1‖ ^ 2)) = p.2 := congrArg Prod.fst hg
  have hR : graphRadius χ r (p.2 - (r ^ 2 - ‖p.1‖ ^ 2)) = ‖p.1‖ := by
    rw [graphRadius, hq, sub_sub_cancel, Real.sqrt_sq (norm_nonneg p.1)]
  apply Prod.ext
  · change graphRadius χ r (p.2 - (r ^ 2 - ‖p.1‖ ^ 2)) •
      (SphereRadialRetraction.retract b p.1).val = p.1
    rw [hR, SphereRadialRetraction.retract,
      dif_neg (GeneralRoundedHandleCorner.transverse_ne_zero_of_level_zero χ hr hp)]
    exact NormedSpace.norm_smul_normalize p.1
  · exact ht

include hr in
theorem contMDiff_zeroPoint :
    ContMDiff ((𝓡 3).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Vector 4 × ℝ) ∞ (zeroPoint χ r) := by
  have hs : ContMDiff ((𝓡 3).prod 𝓘(ℝ, ℝ)) (𝓡 4) ∞
      (fun p : Sphere 3 × ℝ ↦ p.1.val) :=
    (contMDiff_coe_sphere (E := Vector 4) (n := 3)).comp contMDiff_fst
  exact (((contDiff_graphRadius χ hr).contMDiff.comp contMDiff_snd).smul hs).prodMk_space
    ((contDiff_graphHeight χ).contMDiff.comp contMDiff_snd)

theorem contMDiffAt_zeroInverse (b : Sphere 3) {p : Vector 4 × ℝ} (hp : p.1 ≠ 0) :
    ContMDiffAt 𝓘(ℝ, Vector 4 × ℝ) ((𝓡 3).prod 𝓘(ℝ, ℝ)) ∞ (zeroInverse r b) p := by
  have hs := (SphereRadialRetraction.contMDiffAt_retract (E := Vector 4) (n := 3)
    b hp).comp p contDiff_fst.contMDiff.contMDiffAt
  have ht : ContDiff ℝ ∞ (fun q : Vector 4 × ℝ ↦ q.2 - (r ^ 2 - ‖q.1‖ ^ 2)) :=
    contDiff_snd.sub (contDiff_const.sub (contDiff_fst.norm_sq ℝ))
  exact hs.prodMk ht.contMDiff.contMDiffAt

def zeroEquiv (b : Sphere 3) : (Sphere 3 × ℝ) ≃ {p : Vector 4 × ℝ // GeneralRoundedHandleCorner.level χ r p = 0} where
  toFun p := ⟨zeroPoint χ r p, level_zeroPoint χ r p⟩
  invFun p := zeroInverse r b p.val
  left_inv := zeroInverse_zeroPoint χ hr b
  right_inv p := Subtype.ext (zeroPoint_zeroInverse χ hr b p.property)

def zeroDiffeomorph (b : Sphere 3)
    (R : RegularLevelAtlas (K := Vector 4) 𝓘(ℝ, Vector 4 × ℝ)
      (GeneralRoundedHandleCorner.level (d := 4) χ r)) :
    letI := R.chartedSpace;
    (Sphere 3 × ℝ) ≃ₘ⟮(𝓡 3).prod 𝓘(ℝ, ℝ), 𝓡 4⟯
      {p : Vector 4 × ℝ // GeneralRoundedHandleCorner.level χ r p = 0} := by
  let := R.chartedSpace
  refine
    { toEquiv := zeroEquiv χ hr b
      contMDiff_toFun := ?_
      contMDiff_invFun := ?_ }
  · exact (R.contMDiff_iff_ambient _).mpr (contMDiff_zeroPoint χ hr)
  · intro p
    exact (contMDiffAt_zeroInverse b
      (GeneralRoundedHandleCorner.transverse_ne_zero_of_level_zero χ hr p.property)).comp p
        R.contMDiff_subtype_val.contMDiffAt

end Wikipedia.HopfProblem.DegreeCollapse.SevenRoundedHandleCorner
