import Wikipedia.HopfProblem.CuspQuotient
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCircleCrossProduct
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCircleHomotopy

/-!
# An actual extension across the disc kills the positive-circle cross class

Radial interpolation takes place in the original open complex disc with
its inherited topology.  For any continuous disc-product extension, its
restriction along a circle map is genuinely homotopic to the central
slice composed with projection.  Actual singular-homology functoriality
and the proved projection formula for the positive-circle cross product
then give vanishing in every degree.
-/

noncomputable section

open Set Topology
open scoped ContinuousMap

namespace Wikipedia.HopfProblem.CuspBoundaryToricExtension

open CuspQuotient SingularMayerVietoris PeriodTorusHigherHomology

/-- The actual origin of a positive-radius open cusp disc. -/
def discOrigin (r : ℝ) (hr : 0 < r) : disc r :=
  ⟨0, by
    change (0 : ℂ) ∈ Metric.ball 0 r
    simpa only [Metric.mem_ball, dist_self] using hr⟩

@[simp] theorem discOrigin_coe (r : ℝ) (hr : 0 < r) :
    (discOrigin r hr : ℂ) = 0 := rfl

/-- The radial coefficient on the unit interval never increases the norm. -/
theorem radial_smul_norm_le (s : unitInterval) (z : ℂ) :
    ‖(1 - (s : ℝ)) • z‖ ≤ ‖z‖ := by
  have ha : 0 ≤ 1 - (s : ℝ) := sub_nonneg.mpr s.property.2
  have ha1 : 1 - (s : ℝ) ≤ 1 := by linarith [s.property.1]
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ha]
  exact mul_le_of_le_one_left (norm_nonneg z) ha1

/-- Literal radial interpolation in the same open disc, from a point to zero. -/
def radialDiscPoint (r : ℝ) (s : unitInterval) (z : disc r) : disc r :=
  ⟨(1 - (s : ℝ)) • (z : ℂ), by
    change (1 - (s : ℝ)) • (z : ℂ) ∈ Metric.ball 0 r
    have hz : (z : ℂ) ∈ Metric.ball 0 r := z.property
    have hzr : ‖(z : ℂ)‖ < r := by
      simpa only [Metric.mem_ball, dist_zero_right] using hz
    simpa only [Metric.mem_ball, dist_zero_right] using
      (radial_smul_norm_le s (z : ℂ)).trans_lt hzr⟩

@[simp] theorem radialDiscPoint_coe (r : ℝ) (s : unitInterval) (z : disc r) :
    (radialDiscPoint r s z : ℂ) = (1 - (s : ℝ)) • (z : ℂ) := rfl

theorem radialDiscPoint_continuous (r : ℝ) :
    Continuous (fun p : unitInterval × disc r => radialDiscPoint r p.1 p.2) :=
  ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).smul
    (continuous_subtype_val.comp continuous_snd)).subtype_mk _

@[simp] theorem radialDiscPoint_zero (r : ℝ) (z : disc r) :
    radialDiscPoint r 0 z = z := by
  apply Subtype.ext
  change (1 - (0 : ℝ)) • (z : ℂ) = (z : ℂ)
  rw [sub_zero, one_smul]

@[simp] theorem radialDiscPoint_one (r : ℝ) (hr : 0 < r) (z : disc r) :
    radialDiscPoint r 1 z = discOrigin r hr := by
  apply Subtype.ext
  change (1 - (1 : ℝ)) • (z : ℂ) = (0 : ℂ)
  rw [sub_self, zero_smul]

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (r : ℝ) (hr : 0 < r) (F : C(disc r × X, Y))
    (b : C(AddCircle (1 : ℝ), disc r))

/-- Restriction of the given extension to the literal central slice. -/
def centerSlice : C(X, Y) :=
  F.comp ((ContinuousMap.const X (discOrigin r hr)).prodMk (ContinuousMap.id X))

@[simp] theorem centerSlice_apply (x : X) : centerSlice r hr F x = F (discOrigin r hr, x) := rfl

/-- The explicit radial homotopy; it is constructed from the extension,
not supplied as a nullhomotopy assumption. -/
def extensionRadialHomotopy :
    (F.comp (b.prodMap (ContinuousMap.id X))).Homotopy
      ((centerSlice r hr F).comp
        (ContinuousMap.snd : C(AddCircle (1 : ℝ) × X, X))) where
  toFun p := F (radialDiscPoint r p.1 (b p.2.1), p.2.2)
  continuous_toFun := by
    have hb : Continuous (fun p : unitInterval × (AddCircle (1 : ℝ) × X) =>
        (p.1, b p.2.1)) :=
      continuous_fst.prodMk (b.continuous.comp continuous_snd.fst)
    have hz := (radialDiscPoint_continuous r).comp hb
    exact F.continuous.comp (hz.prodMk continuous_snd.snd)
  map_zero_left p := by
    change F (radialDiscPoint r 0 (b p.1), p.2) = F (b p.1, p.2)
    rw [radialDiscPoint_zero]
  map_one_left p := by
    change F (radialDiscPoint r 1 (b p.1), p.2) = F (discOrigin r hr, p.2)
    rw [radialDiscPoint_one r hr]

/-- Exact pointwise formula in the original open-disc subtype. -/
@[simp] theorem extensionRadialHomotopy_apply (s : unitInterval)
    (p : AddCircle (1 : ℝ) × X) :
    extensionRadialHomotopy r hr F b (s, p) =
      F (radialDiscPoint r s (b p.1), p.2) := rfl

theorem discExtension_homotopic_center :
    (F.comp (b.prodMap (ContinuousMap.id X))).Homotopic
      ((centerSlice r hr F).comp
        (ContinuousMap.snd : C(AddCircle (1 : ℝ) × X, X))) :=
  ⟨extensionRadialHomotopy r hr F b⟩

/-- The actual induced homology map factors through the unchanged-factor
projection in every degree. -/
theorem discExtension_homologyMap (n : ℕ) :
    singularHomologyMap (F.comp (b.prodMap (ContinuousMap.id X))) n =
      (singularHomologyMap (centerSlice r hr F) n).comp (circleProjectionHomology X n) := by
  rw [homotopy_homologyMap (extensionRadialHomotopy r hr F b) n,
    singularHomologyMap_comp]
  rfl

include hr in
/-- Every actual positive-circle cross class dies under a map that
extends continuously across the actual open disc product. -/
theorem discExtension_positiveCircleCross_eq_zero (n : ℕ) (a : SingularHomology X n) :
    singularHomologyMap (F.comp (b.prodMap (ContinuousMap.id X))) (n + 1)
      (positiveCircleCross X n a) = 0 := by
  rw [discExtension_homologyMap r hr F b, LinearMap.comp_apply,
    circleProjection_positiveCircleCross, map_zero]

end Wikipedia.HopfProblem.CuspBoundaryToricExtension
