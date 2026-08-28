import Wikipedia.SmoothSixDPoincare.RegularLevelSmoothMaps
import Wikipedia.SmoothSixDPoincare.NativeMorseBoundaryPair
import Mathlib.Geometry.Manifold.Instances.Sphere

/-! # Smoothness of the original Morse attaching sphere in the actual lower level -/

noncomputable section

open Set Metric ContinuousMap
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.ManifoldMorse.SignedMorseChart

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]
  {f : M → ℝ} {p : M} (c : SignedMorseChart (E := E) f p)

open Classical in
/-- The actual zero-positive-coordinate sphere in the old attaching piece. -/
def attachingCoreMap (ρ : ℝ) (hρ : 0 < ρ)
    (hblock : closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
      closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆ c.splitChart.target) :
    C(PuncturedHandle.UnitSphere c.NegativeCoordinates, {y : M // f y = f p - ρ ^ 2}) :=
  (c.attachingBoundaryMap ρ hρ hblock).comp
    ⟨fun u => (u, ⟨0, by simp⟩), continuous_id.prodMk continuous_const⟩

open Classical in
theorem attachingCoreMap_coe (ρ : ℝ) (hρ : 0 < ρ)
    (hblock : closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
      closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆ c.splitChart.target)
    (u : PuncturedHandle.UnitSphere c.NegativeCoordinates) :
    (c.attachingCoreMap ρ hρ hblock u : M) =
      c.splitChart.symm (ρ • (u : c.NegativeCoordinates), 0) := by
  change c.splitChart.symm
    ((ρ * Real.sqrt (1 + ‖(0 : c.PositiveCoordinates)‖ ^ 2)) • (u : c.NegativeCoordinates),
      ρ • (0 : c.PositiveCoordinates)) = _
  simp

open Classical in
theorem contMDiff_attachingCoreMap_ambient (n : ℕ)
    [Fact (Module.finrank ℝ c.NegativeCoordinates = n + 1)]
    (ρ : ℝ) (hρ : 0 < ρ)
    (hblock : closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
      closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆ c.splitChart.target) :
    ContMDiff (𝓡 n) 𝓘(ℝ, E) ∞ (Subtype.val ∘ c.attachingCoreMap ρ hρ hblock) := by
  have heq : Subtype.val ∘ c.attachingCoreMap ρ hρ hblock =
      fun u : PuncturedHandle.UnitSphere c.NegativeCoordinates =>
        c.splitChart.symm (ρ • (u : c.NegativeCoordinates), 0) :=
    funext (c.attachingCoreMap_coe ρ hρ hblock)
  rw [heq]
  have hcoe : ContMDiff (𝓡 n) 𝓘(ℝ, c.NegativeCoordinates) ∞
      (Subtype.val : PuncturedHandle.UnitSphere c.NegativeCoordinates → c.NegativeCoordinates) :=
    contMDiff_coe_sphere (E := c.NegativeCoordinates) (n := n)
  have hscalar : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞
      (fun _ : PuncturedHandle.UnitSphere c.NegativeCoordinates => ρ) := contMDiff_const
  have hnegative : ContMDiff (𝓡 n) 𝓘(ℝ, c.NegativeCoordinates) ∞
      (fun u : PuncturedHandle.UnitSphere c.NegativeCoordinates =>
        ρ • (u : c.NegativeCoordinates)) :=
    hscalar.smul hcoe
  have hcoords : ContMDiff (𝓡 n) 𝓘(ℝ, c.NegativeCoordinates × c.PositiveCoordinates) ∞
      (fun u : PuncturedHandle.UnitSphere c.NegativeCoordinates =>
        (ρ • (u : c.NegativeCoordinates), (0 : c.PositiveCoordinates))) :=
    hnegative.prodMk_space contMDiff_const
  apply c.splitChart.contMDiffOn_invFun.comp_contMDiff hcoords
  intro u
  have hh := hblock (MorseHandle.modelMap_mem_product hρ
    (⟨(u : c.NegativeCoordinates), sphere_subset_closedBall u.property⟩,
      (⟨0, by simp⟩ : MorseHandle.UnitDisk c.PositiveCoordinates)))
  simpa [MorseHandle.modelMap] using hh

variable [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M]

open Classical in
/-- Smoothness is proved in the constructed native lower-level atlas, not merely in the ambient. -/
theorem contMDiff_attachingCoreMap (n : ℕ)
    [Fact (Module.finrank ℝ c.NegativeCoordinates = n + 1)]
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (ρ : ℝ) (hρ : 0 < ρ)
    (hblock : closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
      closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆ c.splitChart.target)
    (hreg : ∀ x, f x = f p - ρ ^ 2 → x ∉ criticalPoints E f) :
    letI := RegularLevel.chartedSpace hf hreg
    ContMDiff (𝓡 n) 𝓘(ℝ, RegularLevel.Model E) ∞ (c.attachingCoreMap ρ hρ hblock) := by
  let _ := RegularLevel.chartedSpace hf hreg
  exact (RegularLevel.contMDiff_iff_inclusion hf hreg (𝓡 n)
    (c.attachingCoreMap ρ hρ hblock)).mpr (c.contMDiff_attachingCoreMap_ambient n ρ hρ hblock)

end Wikipedia.SmoothSixDPoincare.ManifoldMorse.SignedMorseChart
