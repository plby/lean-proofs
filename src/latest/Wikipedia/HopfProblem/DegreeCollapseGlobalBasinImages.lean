import Wikipedia.HopfProblem.DegreeCollapseSmoothBallParametrization
import Wikipedia.HopfProblem.DegreeCollapseClosedEndpointBasins

/-!
# A common Euclidean source for every endpoint-basin obstruction piece

Smooth open-ball parametrizations remove all partial-domain conditions.
The actual Morse dimensions determine when a fixed Euclidean dimension is
large enough. The forward and backward families then cover the closed
level-crossing obstruction exactly, indexed by actual critical endpoints
and integer times.
-/

noncomputable section

open Set Function Filter Manifold
open scoped ContDiff Topology
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] {f : M → ℝ}

theorem AdaptedSurgeryWindows.exists_forward_basin_global_images
    (S : AdaptedSurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (p : criticalPoints E f) {d : ℕ}
    (hd : Module.finrank ℝ E - nativeMorseIndex E f p ≤ d) :
    ∃ g : ℕ → EuclideanSpace ℝ (Fin d) → M,
      (∀ n, ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) 𝓘(ℝ, E) ∞ (g n)) ∧
      {x : M | Tendsto (fun t => S.flow t x) atTop (𝓝 p.val)} = ⋃ n, range (g n) := by
  obtain ⟨r, hr, hsmooth, hcover⟩ := S.exists_forward_basin_smooth_images hf p
  have hdim : Module.finrank ℝ (S.data p).chart.PositiveCoordinates ≤ d := by
    have hh := (S.data p).chart.finrank_negative_add_positive
    rw [nativeMorseIndex_eq_chart (S.data p).chart] at hd
    omega
  choose g hg hrange using (fun n => exists_global_smooth_image_of_ball hdim hr (hsmooth n))
  refine ⟨g, hg, ?_⟩
  rw [hcover]
  exact iUnion_congr (fun n => (hrange n).symm)

theorem AdaptedSurgeryWindows.exists_backward_basin_global_images
    (S : AdaptedSurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (p : criticalPoints E f) {d : ℕ} (hd : nativeMorseIndex E f p ≤ d) :
    ∃ g : ℕ → EuclideanSpace ℝ (Fin d) → M,
      (∀ n, ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) 𝓘(ℝ, E) ∞ (g n)) ∧
      {x : M | Tendsto (fun t => S.flow t x) atBot (𝓝 p.val)} = ⋃ n, range (g n) := by
  obtain ⟨r, hr, hsmooth, hcover⟩ := S.exists_backward_basin_smooth_images hf p
  have hdim : Module.finrank ℝ (S.data p).chart.NegativeCoordinates ≤ d := by
    rwa [nativeMorseIndex_eq_chart (S.data p).chart] at hd
  choose g hg hrange using (fun n => exists_global_smooth_image_of_ball hdim hr (hsmooth n))
  refine ⟨g, hg, ?_⟩
  rw [hcover]
  exact iUnion_congr (fun n => (hrange n).symm)

abbrev EndpointBasinIndex (S : AdaptedSurgeryWindows E f) (a : ℝ) :=
  ({p : criticalPoints E f // a ≤ f p.val} × ℕ) ⊕
    ({p : criticalPoints E f // f p.val ≤ a} × ℕ)

theorem endpointBasinIndex_countable (S : AdaptedSurgeryWindows E f) (a : ℝ) :
    Countable (EndpointBasinIndex S a) := by
  let _ := S.finite.fintype
  unfold EndpointBasinIndex
  infer_instance

theorem AdaptedSurgeryWindows.exists_endpoint_obstruction_global_images
    (S : AdaptedSurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (a : ℝ) {d : ℕ}
    (hhigh : ∀ p : criticalPoints E f, a ≤ f p → Module.finrank ℝ E - nativeMorseIndex E f p ≤ d)
    (hlow : ∀ p : criticalPoints E f, f p ≤ a → nativeMorseIndex E f p ≤ d) :
    ∃ g : EndpointBasinIndex S a → EuclideanSpace ℝ (Fin d) → M,
      (∀ i, ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) 𝓘(ℝ, E) ∞ (g i)) ∧
      forwardHighBasins S a ∪ backwardLowBasins S a = ⋃ i, range (g i) := by
  choose gF hgF hF using (fun p : {p : criticalPoints E f // a ≤ f p.val} =>
    S.exists_forward_basin_global_images hf p.val (hhigh p.val p.property))
  choose gB hgB hB using (fun p : {p : criticalPoints E f // f p.val ≤ a} =>
    S.exists_backward_basin_global_images hf p.val (hlow p.val p.property))
  let g : EndpointBasinIndex S a → EuclideanSpace ℝ (Fin d) → M :=
    Sum.elim (fun i => gF i.1 i.2) (fun i => gB i.1 i.2)
  refine ⟨g, ?_, ?_⟩
  · intro i
    rcases i with ⟨p, n⟩ | ⟨p, n⟩
    · exact hgF p n
    · exact hgB p n
  · ext x
    constructor
    · rintro (⟨p, hp, hx⟩ | ⟨p, hp, hx⟩)
      · have hh : x ∈ ⋃ n, range (gF ⟨p, hp⟩ n) := (hF ⟨p, hp⟩) ▸ hx
        obtain ⟨n, hn⟩ := mem_iUnion.mp hh
        exact mem_iUnion.mpr ⟨Sum.inl (⟨p, hp⟩, n), hn⟩
      · have hh : x ∈ ⋃ n, range (gB ⟨p, hp⟩ n) := (hB ⟨p, hp⟩) ▸ hx
        obtain ⟨n, hn⟩ := mem_iUnion.mp hh
        exact mem_iUnion.mpr ⟨Sum.inr (⟨p, hp⟩, n), hn⟩
    · intro hx
      obtain ⟨i, hi⟩ := mem_iUnion.mp hx
      rcases i with ⟨p, n⟩ | ⟨p, n⟩
      · have hh : x ∈ {x : M | Tendsto (fun t => S.flow t x) atTop (𝓝 p.val.val)} := by
          rw [hF p]
          exact mem_iUnion.mpr ⟨n, hi⟩
        exact Or.inl ⟨p.val, p.property, hh⟩
      · have hh : x ∈ {x : M | Tendsto (fun t => S.flow t x) atBot (𝓝 p.val.val)} := by
          rw [hB p]
          exact mem_iUnion.mpr ⟨n, hi⟩
        exact Or.inr ⟨p.val, p.property, hh⟩

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
