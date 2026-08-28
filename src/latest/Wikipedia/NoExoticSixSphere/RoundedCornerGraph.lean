import Wikipedia.NoExoticSixSphere.RoundedHandleCorner

/-!
# Global graph coordinates on the rounded corner's zero level

The difference coordinate `u = t - q` parametrizes the whole planar zero
curve. Neither monotonicity of the bump nor a graph over height is assumed.
Both coordinates are nonpositive; the transverse radius is always positive.
-/

noncomputable section

open Set Function
open scoped ContDiff

namespace NoExoticSixSphere.SmoothCornerRounding

variable (χ : ContDiffBump (0 : ℝ))

def graphHeight (u : ℝ) : ℝ := (u - roundedAbs χ u) / 2

def graphRadial (u : ℝ) : ℝ := (-u - roundedAbs χ u) / 2

def graph (u : ℝ) : ℝ × ℝ := (graphHeight χ u, graphRadial χ u)

theorem contDiff_graphHeight : ContDiff ℝ ∞ (graphHeight χ) :=
  (contDiff_id.sub (contDiff_roundedAbs χ)).div_const 2

theorem contDiff_graphRadial : ContDiff ℝ ∞ (graphRadial χ) :=
  (contDiff_id.neg.sub (contDiff_roundedAbs χ)).div_const 2

theorem contDiff_graph : ContDiff ℝ ∞ (graph χ) :=
  (contDiff_graphHeight χ).prodMk (contDiff_graphRadial χ)

theorem graph_difference (u : ℝ) : (graph χ u).1 - (graph χ u).2 = u := by
  dsimp [graph, graphHeight, graphRadial]
  ring

theorem level_graph (u : ℝ) : level χ (graph χ u) = 0 := by
  rw [level, graph_difference]
  change (u - roundedAbs χ u) / 2 + (-u - roundedAbs χ u) / 2 + roundedAbs χ u = 0
  ring

theorem graph_of_level_zero {p : ℝ × ℝ} (hp : level χ p = 0) :
    graph χ (p.1 - p.2) = p := by
  change p.1 + p.2 + roundedAbs χ (p.1 - p.2) = 0 at hp
  apply Prod.ext <;> dsimp [graph, graphHeight, graphRadial] <;> linarith

theorem graphHeight_nonpos (u : ℝ) : graphHeight χ u ≤ 0 := by
  have h := (le_abs_self u).trans (abs_le_roundedAbs χ u)
  dsimp [graphHeight]
  linarith

theorem graphRadial_nonpos (u : ℝ) : graphRadial χ u ≤ 0 := by
  have h := (neg_le_abs u).trans (abs_le_roundedAbs χ u)
  dsimp [graphRadial]
  linarith

def zeroHomeomorph : ℝ ≃ₜ {p : ℝ × ℝ // level χ p = 0} where
  toFun u := ⟨graph χ u, level_graph χ u⟩
  invFun p := p.val.1 - p.val.2
  left_inv := graph_difference χ
  right_inv p := Subtype.ext (graph_of_level_zero χ p.property)
  continuous_toFun := (contDiff_graph χ).continuous.subtype_mk _
  continuous_invFun := continuous_subtype_val.fst.sub continuous_subtype_val.snd

theorem graphHeight_of_right {u : ℝ} (hu : χ.rOut ≤ u) : graphHeight χ u = 0 := by
  have hu0 : 0 ≤ u := χ.rOut_pos.le.trans hu
  rw [graphHeight, roundedAbs_eq_abs χ (by simpa only [abs_of_nonneg hu0] using hu),
    abs_of_nonneg hu0, sub_self, zero_div]

theorem graphRadial_of_right {u : ℝ} (hu : χ.rOut ≤ u) : graphRadial χ u = -u := by
  have hu0 : 0 ≤ u := χ.rOut_pos.le.trans hu
  rw [graphRadial, roundedAbs_eq_abs χ (by simpa only [abs_of_nonneg hu0] using hu),
    abs_of_nonneg hu0]
  ring

theorem graphHeight_of_left {u : ℝ} (hu : u ≤ -χ.rOut) : graphHeight χ u = u := by
  have hu0 : u ≤ 0 := hu.trans (neg_nonpos.mpr χ.rOut_pos.le)
  have ha : χ.rOut ≤ |u| := by rw [abs_of_nonpos hu0]; linarith
  rw [graphHeight, roundedAbs_eq_abs χ ha, abs_of_nonpos hu0]
  ring

theorem graphRadial_of_left {u : ℝ} (hu : u ≤ -χ.rOut) : graphRadial χ u = 0 := by
  have hu0 : u ≤ 0 := hu.trans (neg_nonpos.mpr χ.rOut_pos.le)
  have ha : χ.rOut ≤ |u| := by rw [abs_of_nonpos hu0]; linarith
  rw [graphRadial, roundedAbs_eq_abs χ ha, abs_of_nonpos hu0, sub_self, zero_div]

def graphRadius (r u : ℝ) : ℝ := Real.sqrt (r ^ 2 - graphRadial χ u)

theorem graphRadius_pos {r : ℝ} (hr : 0 < r) (u : ℝ) : 0 < graphRadius χ r u := by
  apply Real.sqrt_pos.mpr
  nlinarith [graphRadial_nonpos χ u]

theorem graphRadius_sq (r u : ℝ) :
    (graphRadius χ r u) ^ 2 = r ^ 2 - graphRadial χ u :=
  Real.sq_sqrt (by nlinarith [graphRadial_nonpos χ u])

theorem contDiff_graphRadius {r : ℝ} (hr : 0 < r) :
    ContDiff ℝ ∞ (graphRadius χ r) :=
  (contDiff_const.sub (contDiff_graphRadial χ)).sqrt
    (fun u ↦ by nlinarith [graphRadial_nonpos χ u])

theorem graphRadius_of_left {r u : ℝ} (hr : 0 < r) (hu : u ≤ -χ.rOut) :
    graphRadius χ r u = r := by
  rw [graphRadius, graphRadial_of_left χ hu, sub_zero, Real.sqrt_sq hr.le]

end NoExoticSixSphere.SmoothCornerRounding
