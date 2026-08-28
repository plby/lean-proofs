import Wikipedia.SmoothSixDPoincare.ChartDisk
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

/-!
# Smoothness of the constructed coordinate disks

The compatibility condition refers to Mathlib's native maximal smooth atlas.
The existence proofs choose actual atlas charts and therefore establish the
condition, rather than adding it as an assumption on the original manifold.
-/

noncomputable section

open Set Metric
open scoped Manifold ContDiff

namespace Wikipedia.SmoothSixDPoincare

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

/-- The coordinate disk's chart belongs to the native maximal smooth atlas. -/
def ChartDisk.IsSmooth (d : ChartDisk E M) : Prop :=
  d.chart ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M

omit [IsManifold 𝓘(ℝ, E) ∞ M] in
/-- The disk parametrization is smooth on its entire closed model disk. -/
theorem ChartDisk.contMDiffOn_map (d : ChartDisk E M) (hd : d.IsSmooth) :
    ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E) ∞
      (fun x : E => d.chart.symm (d.radius • x + d.center)) (closedBall (0 : E) 1) := by
  have hf : ContDiff ℝ ∞ (fun x : E => d.radius • x + d.center) := by fun_prop
  exact (contMDiffOn_symm_of_mem_maximalAtlas hd).comp hf.contMDiff.contMDiffOn
    (fun x hx => d.modelMap_mem_target ⟨x, hx⟩)

/-- Every open neighborhood contains a smooth closed coordinate disk centered at the point. -/
theorem exists_smooth_chartDisk (p : M) {U : Set M} (hU : IsOpen U) (hp : p ∈ U) :
    ∃ d : ChartDisk E M,
      d.IsSmooth ∧ d.map ⟨0, by simp⟩ = p ∧ p ∈ d.core ∧ range d.map ⊆ U := by
  obtain ⟨d, hd, _, hp₀, hp', hU'⟩ := exists_chartDisk E M p hU hp
  refine ⟨d, ?_, hp₀, hp', hU'⟩
  change d.chart ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M
  rw [hd]
  exact IsManifold.chart_mem_maximalAtlas p

/-- The two initial disks in the Smale construction can be chosen smooth and disjoint. -/
theorem exists_disjoint_smooth_chartDisks [T2Space M] {p q : M} (hpq : p ≠ q) :
    ∃ d₁ d₂ : ChartDisk E M,
      d₁.IsSmooth ∧ d₂.IsSmooth ∧ p ∈ d₁.core ∧ q ∈ d₂.core ∧
      Disjoint (range d₁.map) (range d₂.map) := by
  obtain ⟨U, V, hU, hV, hp, hq, hUV⟩ := t2_separation hpq
  obtain ⟨d₁, hs₁, _, hp₁, hd₁⟩ := exists_smooth_chartDisk (E := E) p hU hp
  obtain ⟨d₂, hs₂, _, hq₂, hd₂⟩ := exists_smooth_chartDisk (E := E) q hV hq
  exact ⟨d₁, d₂, hs₁, hs₂, hp₁, hq₂, hUV.mono hd₁ hd₂⟩

end Wikipedia.SmoothSixDPoincare
