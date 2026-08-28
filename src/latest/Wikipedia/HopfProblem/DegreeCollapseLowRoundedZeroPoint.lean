import Wikipedia.HopfProblem.DegreeCollapseGeneralRoundedHandleCorner
import Wikipedia.NoExoticSixSphere.RoundedCornerGraphEnds

/-!

# Literal transverse-sphere coordinates on the rounded zero level

The difference coordinate and the actual unit transverse vector parametrize
the whole zero level. These are topological coordinates, so they require no
choice of an atlas or dimension reindexing on the transverse sphere.
-/

noncomputable section

open Function Set Metric

namespace Wikipedia.HopfProblem.DegreeCollapse.LowRoundedZeroPoint

open NoExoticSixSphere GLOrthonormalization SmoothCornerRounding

variable {q : ℕ} (χ : ContDiffBump (0 : ℝ))

def point (r : ℝ) (p : sphere (0 : Vector q) 1 × ℝ) : Vector q × ℝ :=
  (graphRadius χ r p.2 • p.1.val, graphHeight χ p.2)

theorem norm_point (r : ℝ) (p : sphere (0 : Vector q) 1 × ℝ) :
    ‖(point χ r p).1‖ = graphRadius χ r p.2 := by
  have hrad : 0 ≤ graphRadius χ r p.2 := Real.sqrt_nonneg _
  change ‖graphRadius χ r p.2 • p.1.val‖ = _
  rw [norm_smul, Real.norm_eq_abs,
    abs_of_nonneg hrad, mem_sphere_zero_iff_norm.mp p.1.property,
    mul_one]

theorem coordinates_point (r : ℝ) (p : sphere (0 : Vector q) 1 × ℝ) :
    GeneralRoundedHandleCorner.coordinates r (point χ r p) = graph χ p.2 := by
  apply Prod.ext
  · rfl
  · change r ^ 2 - ‖(point χ r p).1‖ ^ 2 = graphRadial χ p.2
    rw [norm_point, graphRadius_sq]
    ring

theorem level_point (r : ℝ) (p : sphere (0 : Vector q) 1 × ℝ) :
    GeneralRoundedHandleCorner.level χ r (point χ r p) = 0 := by
  change SmoothCornerRounding.level χ
    (GeneralRoundedHandleCorner.coordinates r (point χ r p)) = 0
  rw [coordinates_point, level_graph]

theorem point_difference (r : ℝ) (p : sphere (0 : Vector q) 1 × ℝ) :
    (point χ r p).2 - (r ^ 2 - ‖(point χ r p).1‖ ^ 2) = p.2 := by
  change (GeneralRoundedHandleCorner.coordinates r (point χ r p)).1 -
    (GeneralRoundedHandleCorner.coordinates r (point χ r p)).2 = p.2
  rw [coordinates_point, graph_difference]

theorem point_fst_ne_zero {r : ℝ} (hr : 0 < r)
    (p : sphere (0 : Vector q) 1 × ℝ) : (point χ r p).1 ≠ 0 := by
  apply norm_pos_iff.mp
  rw [norm_point]
  exact graphRadius_pos χ hr p.2

theorem continuous_point {r : ℝ} (hr : 0 < r) : Continuous (point (q := q) χ r) :=
  (((contDiff_graphRadius χ hr).continuous.comp continuous_snd).smul
    (continuous_subtype_val.comp continuous_fst)).prodMk
      ((contDiff_graphHeight χ).continuous.comp continuous_snd)

theorem point_of_left {r : ℝ} (hr : 0 < r)
    (p : sphere (0 : Vector q) 1 × ℝ) (hp : p.2 ≤ -χ.rOut) :
    point χ r p = (r • p.1.val, p.2) := by
  rw [point, graphRadius_of_left χ hr hp, graphHeight_of_left χ hp]

theorem point_of_right (r : ℝ) (p : sphere (0 : Vector q) 1 × ℝ)
    (hp : χ.rOut ≤ p.2) :
    point χ r p = (Real.sqrt (r ^ 2 + p.2) • p.1.val, 0) := by
  rw [point, graphRadius, graphRadial_of_right χ hp, sub_neg_eq_add,
    graphHeight_of_right χ hp]

theorem point_injective {r : ℝ} (hr : 0 < r) : Injective (point (q := q) χ r) := by
  intro p p' h
  have hu : p.2 = p'.2 := by
    rw [← point_difference χ r p, h, point_difference]
  apply Prod.ext _ hu
  apply Subtype.ext
  have hv := congrArg Prod.fst h
  change graphRadius χ r p.2 • p.1.val = graphRadius χ r p'.2 • p'.1.val at hv
  rw [hu] at hv
  exact (smul_right_injective _ (graphRadius_pos χ hr p'.2).ne') hv

def parameters {r : ℝ} (hr : 0 < r)
    (p : {p : Vector q × ℝ // GeneralRoundedHandleCorner.level χ r p = 0}) :
    sphere (0 : Vector q) 1 × ℝ := by
  have hn : ‖p.val.1‖ ≠ 0 := norm_ne_zero_iff.mpr
    (GeneralRoundedHandleCorner.transverse_ne_zero_of_level_zero χ hr p.property)
  refine (⟨‖p.val.1‖⁻¹ • p.val.1, ?_⟩, p.val.2 - (r ^ 2 - ‖p.val.1‖ ^ 2))
  apply mem_sphere_zero_iff_norm.mpr
  rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn]

theorem point_parameters {r : ℝ} (hr : 0 < r)
    (p : {p : Vector q × ℝ // GeneralRoundedHandleCorner.level χ r p = 0}) :
    point χ r (parameters χ hr p) = p.val := by
  have hg := graph_of_level_zero χ p.property
  have hh : graphHeight χ (parameters χ hr p).2 = p.val.2 := congrArg Prod.fst hg
  have hq : graphRadial χ (parameters χ hr p).2 = r ^ 2 - ‖p.val.1‖ ^ 2 :=
    congrArg Prod.snd hg
  have hn : ‖p.val.1‖ ≠ 0 := norm_ne_zero_iff.mpr
    (GeneralRoundedHandleCorner.transverse_ne_zero_of_level_zero χ hr p.property)
  have hrad : graphRadius χ r (parameters χ hr p).2 = ‖p.val.1‖ := by
    rw [graphRadius, hq]
    have he : r ^ 2 - (r ^ 2 - ‖p.val.1‖ ^ 2) = ‖p.val.1‖ ^ 2 := by ring
    rw [he, Real.sqrt_sq (norm_nonneg _)]
  apply Prod.ext
  · change graphRadius χ r (parameters χ hr p).2 • (‖p.val.1‖⁻¹ • p.val.1) = _
    rw [hrad, smul_inv_smul₀ hn]
  · exact hh

theorem parameters_point {r : ℝ} (hr : 0 < r)
    (p : sphere (0 : Vector q) 1 × ℝ) :
    parameters χ hr ⟨point χ r p, level_point χ r p⟩ = p :=
  point_injective χ hr (point_parameters χ hr _)

theorem continuous_parameters {r : ℝ} (hr : 0 < r) :
    Continuous (parameters (q := q) χ hr) := by
  have hn (p : {p : Vector q × ℝ // GeneralRoundedHandleCorner.level χ r p = 0}) :
      ‖p.val.1‖ ≠ 0 := norm_ne_zero_iff.mpr
    (GeneralRoundedHandleCorner.transverse_ne_zero_of_level_zero χ hr p.property)
  exact (((continuous_subtype_val.fst.norm.inv₀ hn).smul
      continuous_subtype_val.fst).subtype_mk _).prodMk
    (continuous_subtype_val.snd.sub
      (continuous_const.sub (continuous_subtype_val.fst.norm.pow 2)))

def zeroHomeomorph {r : ℝ} (hr : 0 < r) :
    (sphere (0 : Vector q) 1 × ℝ) ≃ₜ
      {p : Vector q × ℝ // GeneralRoundedHandleCorner.level χ r p = 0} where
  toFun p := ⟨point χ r p, level_point χ r p⟩
  invFun := parameters χ hr
  left_inv := parameters_point χ hr
  right_inv p := Subtype.ext (point_parameters χ hr p)
  continuous_toFun := (continuous_point χ hr).subtype_mk _
  continuous_invFun := continuous_parameters χ hr

end Wikipedia.HopfProblem.DegreeCollapse.LowRoundedZeroPoint
