import Wikipedia.HopfProblem.DegreeCollapseDisjointMorseBlockField
import Wikipedia.HopfProblem.DegreeCollapseMorseBlockEnlargement

/-!
# A common complete field with germs on the full surgery blocks

Enlarge the closed radius-2r blocks without changing the radius-r
attaching or belt levels. Separated radius-3r height windows then give
one global descending field with full model germs at every point of
each original closed surgery block.
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
theorem exists_disjoint_surgery_block_field {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hm : IsMorse E f)
    {ι : Type*} [Finite ι] (p : ι → M) (hp : ∀ i, p i ∈ criticalPoints E f)
    (c : ∀ i, SignedMorseChart (E := E) f (p i)) (r : ι → ℝ) (hr : ∀ i, 0 < r i)
    (hblock : ∀ i, closedBall (0 : (c i).NegativeCoordinates) (2 * r i) ×ˢ
      closedBall (0 : (c i).PositiveCoordinates) (2 * r i) ⊆ (c i).splitChart.target)
    (hintervals : Pairwise (fun i j =>
      Disjoint (Icc (f (p i) - 9 * r i ^ 2) (f (p i) + 9 * r i ^ 2))
        (Icc (f (p j) - 9 * r j ^ 2) (f (p j) + 9 * r j ^ 2)))) :
    ∃ (V : (x : M) → TangentSpace 𝓘(ℝ, E) x) (F : Flow ℝ M),
      ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞
        (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)) ∧
      (∀ x, IsMIntegralCurve (fun t => F t x) V) ∧
      (∀ x ∈ criticalPoints E f, V x = 0) ∧
      (∀ x, x ∉ criticalPoints E f → mvfderiv 𝓘(ℝ, E) f x (V x) < 0) ∧
      ∀ i z, z ∈ closedBall (0 : (c i).NegativeCoordinates) (2 * r i) ×ˢ
        closedBall (0 : (c i).PositiveCoordinates) (2 * r i) →
        ∀ᶠ y in 𝓝 ((c i).splitChart.symm z), V y = (c i).descentField y := by
  choose R hR hR' hlarge using fun i => exists_morse_block_enlargement (c i) (hr i) (hblock i)
  have hRpos (i : ι) : 0 < R i :=
    (mul_pos (show (0 : ℝ) < 2 by norm_num) (hr i)).trans (hR i)
  have hsq (i : ι) : R i ^ 2 < 9 * r i ^ 2 := by
    have hh := mul_pos (sub_pos.mpr (hR' i))
      (add_pos (mul_pos (show (0 : ℝ) < 3 by norm_num) (hr i)) (hRpos i))
    nlinarith
  have hsub (i : ι) : Icc (f (p i) - R i ^ 2) (f (p i) + R i ^ 2) ⊆
      Icc (f (p i) - 9 * r i ^ 2) (f (p i) + 9 * r i ^ 2) := by
    intro v hv
    constructor <;> linarith [hv.1, hv.2, hsq i]
  obtain ⟨V, F, hV, hF, hzero, hdesc, hmatch⟩ :=
    exists_disjoint_morse_block_field hf hm p hp c R hlarge
      (fun i j hij => (hintervals hij).mono (hsub i) (hsub j))
  refine ⟨V, F, hV, hF, hzero, hdesc, ?_⟩
  intro i z hz
  exact hmatch i z ((mem_closedBall_zero_iff.mp hz.1).trans_lt (hR i))
    ((mem_closedBall_zero_iff.mp hz.2).trans_lt (hR i))

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
