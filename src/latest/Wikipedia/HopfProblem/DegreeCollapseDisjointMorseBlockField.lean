import Wikipedia.HopfProblem.DegreeCollapseNativeMorseClosedBlocks
import Wikipedia.SmoothSixDPoincare.CompactFlow

/-!
# One complete native descending flow adapted to disjoint Morse blocks

Disjoint original height intervals separate the actual compact Morse
blocks. The prescribed closed-patch field agrees with every model on a
full neighborhood of each strictly interior point, and compactness
constructs its actual complete native flow.
-/

noncomputable section

open Set Function Filter Metric Manifold
open scoped ContDiff Topology
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M]

open Classical in
theorem exists_disjoint_morse_block_field {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hm : IsMorse E f)
    {ι : Type*} [Finite ι] (p : ι → M) (hp : ∀ i, p i ∈ criticalPoints E f)
    (c : ∀ i, SignedMorseChart (E := E) f (p i)) (R : ι → ℝ)
    (hblock : ∀ i, closedBall (0 : (c i).NegativeCoordinates) (R i) ×ˢ
      closedBall (0 : (c i).PositiveCoordinates) (R i) ⊆ (c i).splitChart.target)
    (hintervals : Pairwise (fun i j =>
      Disjoint (Icc (f (p i) - R i ^ 2) (f (p i) + R i ^ 2))
        (Icc (f (p j) - R j ^ 2) (f (p j) + R j ^ 2)))) :
    ∃ (V : (x : M) → TangentSpace 𝓘(ℝ, E) x) (F : Flow ℝ M),
      ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞
        (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)) ∧
      (∀ x, IsMIntegralCurve (fun t => F t x) V) ∧
      (∀ x ∈ criticalPoints E f, V x = 0) ∧
      (∀ x, x ∉ criticalPoints E f → mvfderiv 𝓘(ℝ, E) f x (V x) < 0) ∧
      ∀ i (z : (c i).NegativeCoordinates × (c i).PositiveCoordinates),
        ‖z.1‖ < R i → ‖z.2‖ < R i →
        ∀ᶠ y in 𝓝 ((c i).splitChart.symm z), V y = (c i).descentField y := by
  let K := fun i => morseClosedBlock (c i) (R i)
  have hK (i : ι) : IsClosed (K i) := (isCompact_morseClosedBlock (c i) (R i) (hblock i)).isClosed
  have hKsource (i : ι) : K i ⊆ (c i).splitChart.source :=
    morseClosedBlock_subset_source (c i) (R i) (hblock i)
  have hdisj : Pairwise (fun i j => Disjoint (K i) (K j)) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro x hxi hxj
    exact Set.disjoint_left.mp (hintervals hij)
      (morseClosedBlock_height (c i) (R i) (hblock i) hxi)
      (morseClosedBlock_height (c j) (R j) (hblock j) hxj)
  obtain ⟨V, hV, hzero, hdesc, hmatch⟩ :=
    exists_prescribed_morse_patch_field hf hm p hp c K hK hKsource hdisj
  have hV₁ := hV.of_le (show (1 : WithTop ℕ∞) ≤ ∞ by simp)
  let F := FlowConstruction.compactFlow hV₁
  refine ⟨V, F, hV, FlowConstruction.isMIntegralCurve_compactFlow hV₁, hzero, hdesc, ?_⟩
  intro i z hn hp
  filter_upwards [morseClosedBlock_mem_nhds (c i) (R i) (hblock i) hn hp] with y hy
  exact hmatch i y hy

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
