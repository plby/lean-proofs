import Wikipedia.SmoothSixDPoincare.SmoothMorseSurgery
import Wikipedia.SmoothSixDPoincare.RegularLevelTangent

/-!
# The original negative Morse coordinates define the actual belt sphere

On the upper regular level inside the original Morse chart, the negative
coordinate vanishes exactly on the actual belt. This gives one fixed normal
coordinate map along the whole belt, rather than unrelated local choices.
-/

noncomputable section

open Set Function Metric Topology
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.ManifoldMorse.MorseSurgeryData

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]
  {f : M → ℝ} {p : M} (d : MorseSurgeryData E f p)

open Classical in
def beltNormalDomain : Set d.UpperLevel :=
  (Subtype.val : d.UpperLevel → M) ⁻¹' d.chart.splitChart.source

open Classical in
/-- The fixed original negative Morse coordinate on the actual upper level. -/
def beltNormal : d.UpperLevel → d.chart.NegativeCoordinates :=
  fun x => (d.chart.splitChart (x : M)).1

open Classical in
theorem isOpen_beltNormalDomain : IsOpen d.beltNormalDomain :=
  d.chart.splitChart.open_source.preimage continuous_subtype_val

open Classical in
theorem belt_model_mem_target (v : PuncturedHandle.UnitSphere d.chart.PositiveCoordinates) :
    (0, d.radius • (v : d.chart.PositiveCoordinates)) ∈ d.chart.splitChart.target := by
  apply d.block
  constructor
  · simpa only [mem_closedBall, dist_self] using
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) d.radius_pos.le)
  · have hv : ‖(v : d.chart.PositiveCoordinates)‖ = 1 := mem_sphere_zero_iff_norm.mp v.property
    simp only [mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_of_pos d.radius_pos, hv, mul_one]
    linarith [d.radius_pos]

open Classical in
theorem belt_mem_normalDomain (v : PuncturedHandle.UnitSphere d.chart.PositiveCoordinates) :
    d.surgery.beltSphere v ∈ d.beltNormalDomain := by
  change (d.surgery.beltSphere v : M) ∈ d.chart.splitChart.source
  rw [d.belt_eq, d.chart.beltCoreMap_coe]
  exact d.chart.splitChart.map_target' (d.belt_model_mem_target v)

open Classical in
theorem belt_split_coordinates (v : PuncturedHandle.UnitSphere d.chart.PositiveCoordinates) :
    d.chart.splitChart (d.surgery.beltSphere v : M) =
      (0, d.radius • (v : d.chart.PositiveCoordinates)) := by
  rw [d.belt_eq, d.chart.beltCoreMap_coe]
  exact d.chart.splitChart.right_inv' (d.belt_model_mem_target v)

open Classical in
theorem beltNormal_belt (v : PuncturedHandle.UnitSphere d.chart.PositiveCoordinates) :
    d.beltNormal (d.surgery.beltSphere v) = 0 := by
  change (d.chart.splitChart (d.surgery.beltSphere v : M)).1 = 0
  rw [d.belt_split_coordinates]

open Classical in
/-- The zero set in the genuine chart domain is exactly the full actual belt sphere. -/
theorem beltNormal_eq_zero_iff {x : d.UpperLevel} (hx : x ∈ d.beltNormalDomain) :
    d.beltNormal x = 0 ↔ x ∈ range d.surgery.beltSphere := by
  constructor
  · intro hzero
    let z := d.chart.splitChart (x : M)
    have hz₁ : z.1 = 0 := hzero
    have heq := d.chart.splitChart_equation hx
    change f (x : M) = f p - ‖z.1‖ ^ 2 + ‖z.2‖ ^ 2 at heq
    rw [hz₁, norm_zero, zero_pow (by decide : 2 ≠ 0), sub_zero, x.property] at heq
    have hnorm : ‖z.2‖ = d.radius := by
      nlinarith [norm_nonneg z.2, d.radius_pos]
    let v : PuncturedHandle.UnitSphere d.chart.PositiveCoordinates :=
      ⟨d.radius⁻¹ • z.2, by
        rw [mem_sphere_zero_iff_norm, norm_smul, Real.norm_eq_abs,
          abs_of_pos (inv_pos.mpr d.radius_pos), hnorm, inv_mul_cancel₀ d.radius_pos.ne']⟩
    refine ⟨v, Subtype.ext ?_⟩
    rw [d.belt_eq, d.chart.beltCoreMap_coe]
    change d.chart.splitChart.symm (0, d.radius • (d.radius⁻¹ • z.2)) = (x : M)
    rw [smul_smul, mul_inv_cancel₀ d.radius_pos.ne', one_smul]
    have hz : (0, z.2) = z := Prod.ext hz₁.symm rfl
    rw [hz]
    exact d.chart.splitChart.left_inv' hx
  · rintro ⟨v, rfl⟩
    exact d.beltNormal_belt v

variable [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M]
  (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)

open Classical in
theorem contMDiffOn_beltNormal :
    letI := RegularLevel.chartedSpace hf d.upper_regular
    ContMDiffOn 𝓘(ℝ, RegularLevel.Model E) 𝓘(ℝ, d.chart.NegativeCoordinates) ∞
      d.beltNormal d.beltNormalDomain := by
  let _ := RegularLevel.chartedSpace hf d.upper_regular
  have hcoords : ContMDiffOn 𝓘(ℝ, RegularLevel.Model E)
      𝓘(ℝ, d.chart.NegativeCoordinates × d.chart.PositiveCoordinates) ∞
      (d.chart.splitChart ∘ (Subtype.val : d.UpperLevel → M)) d.beltNormalDomain :=
    d.chart.splitChart.contMDiffOn_toFun.comp
      (RegularLevel.contMDiff_inclusion hf d.upper_regular).contMDiffOn (fun _ hx => hx)
  exact contDiff_fst.contMDiff.comp_contMDiffOn hcoords

open Classical in
/-- The fixed normal coordinate annihilates every native belt tangent vector. -/
theorem beltNormal_derivative_comp_belt (n : ℕ)
    [Fact (Module.finrank ℝ d.chart.PositiveCoordinates = n + 1)]
    (v : PuncturedHandle.UnitSphere d.chart.PositiveCoordinates) :
    letI := RegularLevel.chartedSpace hf d.upper_regular
    (mfderiv 𝓘(ℝ, RegularLevel.Model E) 𝓘(ℝ, d.chart.NegativeCoordinates)
      d.beltNormal (d.surgery.beltSphere v)).comp
        (mfderiv (𝓡 n) 𝓘(ℝ, RegularLevel.Model E) d.surgery.beltSphere v) = 0 := by
  let _ := RegularLevel.chartedSpace hf d.upper_regular
  have hnormal := (d.contMDiffOn_beltNormal hf).contMDiffAt
    (d.isOpen_beltNormalDomain.mem_nhds (d.belt_mem_normalDomain v))
  have heq : d.beltNormal ∘ d.surgery.beltSphere = fun _ => 0 := funext d.beltNormal_belt
  have hzero : mfderiv (𝓡 n) 𝓘(ℝ, d.chart.NegativeCoordinates)
      (d.beltNormal ∘ d.surgery.beltSphere) v = 0 := by
    rw [heq, mfderiv_const]
  have hchain := mfderiv_comp v (hnormal.mdifferentiableAt (by simp))
    ((d.belt_smooth hf n).mdifferentiableAt (by simp))
  exact hchain.symm.trans hzero

end Wikipedia.SmoothSixDPoincare.ManifoldMorse.MorseSurgeryData
