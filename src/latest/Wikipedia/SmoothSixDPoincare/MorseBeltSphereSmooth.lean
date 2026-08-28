import Wikipedia.SmoothSixDPoincare.MorseAttachingSphereSmooth
import Wikipedia.SmoothSixDPoincare.MorseLevelSurgery

/-!
# The actual belt sphere is the explicit smooth positive-coordinate sphere

The positive core already lies on the original upper level. The constructed
attachment homeomorphism fixes it, so transporting the new surgery piece does
not change its belt map. Smoothness follows from the inverse Morse chart and
the proved lifting criterion for the actual upper-level atlas.
-/

noncomputable section

open Set Metric ContinuousMap
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.ManifoldMorse.SignedMorseChart

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]
  {f : M → ℝ} {p : M} (c : SignedMorseChart (E := E) f p)

open Classical in
theorem normHandleMap_belt_height (ρ : ℝ) (hρ : 0 < ρ)
    (hblock : closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
      closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆ c.splitChart.target)
    (v : PuncturedHandle.UnitSphere c.PositiveCoordinates) :
    f (c.normHandleMap ρ hρ hblock
      (PuncturedHandle.ballZero, PuncturedHandle.sphereToBall v)) = f p + ρ ^ 2 := by
  change f (c.attachingHandleMap ρ hρ hblock
    (⟨0, by simp⟩, ⟨(v : c.PositiveCoordinates), sphere_subset_closedBall v.property⟩)) = _
  rw [c.attachingHandleMap_quadratic]
  have hv : ‖(v : c.PositiveCoordinates)‖ = 1 := mem_sphere_zero_iff_norm.mp v.property
  simp [MorseHandle.modelMap, norm_smul, Real.norm_eq_abs, abs_of_pos hρ, hv]

open Classical in
/-- The original positive core, as a map into the actual upper level. -/
def beltCoreMap (ρ : ℝ) (hρ : 0 < ρ)
    (hblock : closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
      closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆ c.splitChart.target) :
    C(PuncturedHandle.UnitSphere c.PositiveCoordinates, {y : M // f y = f p + ρ ^ 2}) where
  toFun v := ⟨c.normHandleMap ρ hρ hblock
    (PuncturedHandle.ballZero, PuncturedHandle.sphereToBall v),
    c.normHandleMap_belt_height ρ hρ hblock v⟩
  continuous_toFun := ((c.normHandleMap ρ hρ hblock).continuous.comp
    (continuous_const.prodMk (continuous_subtype_val.subtype_mk _))).subtype_mk _

open Classical in
theorem beltCoreMap_coe (ρ : ℝ) (hρ : 0 < ρ)
    (hblock : closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
      closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆ c.splitChart.target)
    (v : PuncturedHandle.UnitSphere c.PositiveCoordinates) :
    (c.beltCoreMap ρ hρ hblock v : M) =
      c.splitChart.symm (0, ρ • (v : c.PositiveCoordinates)) := by
  change c.splitChart.symm
    ((ρ * Real.sqrt (1 + ‖(v : c.PositiveCoordinates)‖ ^ 2)) • (0 : c.NegativeCoordinates),
      ρ • (v : c.PositiveCoordinates)) = _
  simp only [smul_zero]

open Classical in
theorem contMDiff_beltCoreMap_ambient (n : ℕ)
    [Fact (Module.finrank ℝ c.PositiveCoordinates = n + 1)]
    (ρ : ℝ) (hρ : 0 < ρ)
    (hblock : closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
      closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆ c.splitChart.target) :
    ContMDiff (𝓡 n) 𝓘(ℝ, E) ∞ (Subtype.val ∘ c.beltCoreMap ρ hρ hblock) := by
  have heq : Subtype.val ∘ c.beltCoreMap ρ hρ hblock =
      fun v : PuncturedHandle.UnitSphere c.PositiveCoordinates =>
        c.splitChart.symm (0, ρ • (v : c.PositiveCoordinates)) :=
    funext (c.beltCoreMap_coe ρ hρ hblock)
  rw [heq]
  have hcoe : ContMDiff (𝓡 n) 𝓘(ℝ, c.PositiveCoordinates) ∞
      (Subtype.val : PuncturedHandle.UnitSphere c.PositiveCoordinates → c.PositiveCoordinates) :=
    contMDiff_coe_sphere (E := c.PositiveCoordinates) (n := n)
  have hscalar : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞
      (fun _ : PuncturedHandle.UnitSphere c.PositiveCoordinates => ρ) := contMDiff_const
  have hpositive : ContMDiff (𝓡 n) 𝓘(ℝ, c.PositiveCoordinates) ∞
      (fun v : PuncturedHandle.UnitSphere c.PositiveCoordinates =>
        ρ • (v : c.PositiveCoordinates)) := hscalar.smul hcoe
  have hcoords : ContMDiff (𝓡 n) 𝓘(ℝ, c.NegativeCoordinates × c.PositiveCoordinates) ∞
      (fun v : PuncturedHandle.UnitSphere c.PositiveCoordinates =>
        ((0 : c.NegativeCoordinates), ρ • (v : c.PositiveCoordinates))) :=
    contMDiff_const.prodMk_space hpositive
  apply c.splitChart.contMDiffOn_invFun.comp_contMDiff hcoords
  intro v
  have hh := hblock (MorseHandle.modelMap_mem_product hρ
    ((⟨0, by simp⟩ : MorseHandle.UnitDisk c.NegativeCoordinates),
      ⟨(v : c.PositiveCoordinates), sphere_subset_closedBall v.property⟩))
  simpa [MorseHandle.modelMap] using hh

variable [T2Space M]

open Classical in
/-- The transported belt map is exactly the original positive core, not an arbitrary image. -/
theorem beltSphere_eq_beltCoreMap (hf : Continuous f) (ρ : ℝ) (hρ : 0 < ρ)
    (hblock : closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
      closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆ c.splitChart.target)
    (hlevel : frontier {x | f x ≤ f p - ρ ^ 2} = {x | f x = f p - ρ ^ 2})
    (e : ↥({x | f x ≤ f p - ρ ^ 2} ∪ range (c.attachingHandleMap ρ hρ hblock)) ≃ₜ
      {x : M // f x ≤ f p + ρ ^ 2})
    (he : ∀ x, f (e x) = f p + ρ ^ 2 ↔ x.val ∈
      frontier ({y | f y ≤ f p - ρ ^ 2} ∪ range (c.attachingHandleMap ρ hρ hblock)))
    (hfixed : ∀ x, f x.val = f p + ρ ^ 2 → (e x).val = x.val) :
    (c.levelSurgeryBoundaryPair hf ρ hρ hblock hlevel e he).beltSphere =
      c.beltCoreMap ρ hρ hblock := by
  apply ContinuousMap.ext
  intro v
  apply Subtype.ext
  exact hfixed _ (c.normHandleMap_belt_height ρ hρ hblock v)

variable [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M]

omit [T2Space M] in
open Classical in
/-- Smoothness of the belt in the actual upper-level atlas. -/
theorem contMDiff_beltCoreMap (n : ℕ)
    [Fact (Module.finrank ℝ c.PositiveCoordinates = n + 1)]
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (ρ : ℝ) (hρ : 0 < ρ)
    (hblock : closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
      closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆ c.splitChart.target)
    (hreg : ∀ x, f x = f p + ρ ^ 2 → x ∉ criticalPoints E f) :
    letI := RegularLevel.chartedSpace hf hreg
    ContMDiff (𝓡 n) 𝓘(ℝ, RegularLevel.Model E) ∞ (c.beltCoreMap ρ hρ hblock) := by
  let _ := RegularLevel.chartedSpace hf hreg
  exact (RegularLevel.contMDiff_iff_inclusion hf hreg (𝓡 n)
    (c.beltCoreMap ρ hρ hblock)).mpr (c.contMDiff_beltCoreMap_ambient n ρ hρ hblock)

end Wikipedia.SmoothSixDPoincare.ManifoldMorse.SignedMorseChart
