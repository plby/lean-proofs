import Wikipedia.HopfProblem.DegreeCollapseBackwardBasinObstacle

/-!
# The actual backward obstruction between two cuts

Only critical endpoints strictly above the lower cut can obstruct a
trajectory that crosses that regular cut. Their exact native basin images
therefore suffice inside the whole lower-level crossing basin, even when
an intermediate path passes below the lower cut. No index hypothesis on
the negative critical points is used.
-/

noncomputable section

open Set Function Filter Manifold
open scoped ContDiff Topology
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] {f : M → ℝ}

def backwardBetweenBasins (S : AdaptedSurgeryWindows E f) (b a : ℝ) : Set M :=
  {x | ∃ p : criticalPoints E f, b < f p ∧ f p ≤ a ∧
    Tendsto (fun t => S.flow t x) atBot (𝓝 p.val)}

abbrev BetweenBackwardBasinIndex (_S : AdaptedSurgeryWindows E f) (b a : ℝ) :=
  {p : criticalPoints E f // b < f p.val ∧ f p.val ≤ a} × ℕ

omit [FiniteDimensional ℝ E] [T2Space M] [CompactSpace M] in
theorem betweenBackwardBasinIndex_countable (S : AdaptedSurgeryWindows E f) (b a : ℝ) :
    Countable (BetweenBackwardBasinIndex S b a) := by
  let _ := S.finite.fintype
  unfold BetweenBackwardBasinIndex
  infer_instance

theorem AdaptedSurgeryWindows.exists_between_backward_obstruction_images
    (S : AdaptedSurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (b a : ℝ) {d : ℕ}
    (hlow : ∀ p : criticalPoints E f, b < f p → f p ≤ a → nativeMorseIndex E f p ≤ d) :
    ∃ g : BetweenBackwardBasinIndex S b a → EuclideanSpace ℝ (Fin d) → M,
      (∀ i, ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) 𝓘(ℝ, E) ∞ (g i)) ∧
      backwardBetweenBasins S b a = ⋃ i, range (g i) := by
  choose g hg hcover using
    (fun p : {p : criticalPoints E f // b < f p.val ∧ f p.val ≤ a} =>
      S.exists_backward_basin_global_images hf p.val (hlow p.val p.property.1 p.property.2))
  refine ⟨fun i => g i.1 i.2, fun i => hg i.1 i.2, ?_⟩
  ext x
  constructor
  · rintro ⟨p, hbp, hpa, hx⟩
    have hh : x ∈ ⋃ n, range (g ⟨p, hbp, hpa⟩ n) := (hcover ⟨p, hbp, hpa⟩) ▸ hx
    obtain ⟨n, hn⟩ := mem_iUnion.mp hh
    exact mem_iUnion.mpr ⟨(⟨p, hbp, hpa⟩, n), hn⟩
  · intro hx
    obtain ⟨⟨p, n⟩, hn⟩ := mem_iUnion.mp hx
    have hh : x ∈ {x : M | Tendsto (fun t => S.flow t x) atBot (𝓝 p.val.val)} := by
      rw [hcover p]
      exact mem_iUnion.mpr ⟨n, hn⟩
    exact ⟨p.val, p.property.1, p.property.2, hh⟩

omit [FiniteDimensional ℝ E] [T2Space M] [CompactSpace M] in
theorem AdaptedSurgeryWindows.endpoint_values_straddle_crossed_level
    (S : AdaptedSurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    {b : ℝ} (hb : ∀ y, f y = b → y ∉ criticalPoints E f)
    {x : M} (hx : x ∈ FlowCancellation.levelBasin S.flow f b)
    (p q : criticalPoints E f)
    (hback : Tendsto (fun t => S.flow t x) atBot (𝓝 p.val))
    (hforward : Tendsto (fun t => S.flow t x) atTop (𝓝 q.val)) :
    b < f p ∧ f q < b := by
  obtain ⟨t, ht⟩ := hx
  have hmono := FlowConstruction.antitone_flow_height hf S.flow S.integral S.zero S.descent x
  have hp : b ≤ f p := ht ▸
    hmono.ge_of_tendsto (hf.continuous.continuousAt.tendsto.comp hback) t
  have hq : f q ≤ b := ht ▸
    hmono.le_of_tendsto (hf.continuous.continuousAt.tendsto.comp hforward) t
  exact ⟨lt_of_le_of_ne hp (fun h => hb p h.symm p.property),
    lt_of_le_of_ne hq (fun h => hb q h q.property)⟩

omit [FiniteDimensional ℝ E] in
theorem AdaptedSurgeryWindows.backward_obstruction_on_crossing_basin
    (S : AdaptedSurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    {b a : ℝ} (hb : ∀ y, f y = b → y ∉ criticalPoints E f)
    {x : M} (hx : x ∈ FlowCancellation.levelBasin S.flow f b) :
    x ∈ backwardLowBasins S a ↔ x ∈ backwardBetweenBasins S b a := by
  constructor
  · rintro ⟨p, hp, hback⟩
    obtain ⟨_, _, q, hq, _, hforward, _⟩ := FlowCancellation.exists_native_descent_endpoints
      hf S.smooth S.flow S.integral S.zero S.descent S.distinct x
    have hbp := (S.endpoint_values_straddle_crossed_level hf hb hx p ⟨q, hq⟩
      hback hforward).1
    exact ⟨p, hbp, hp, hback⟩
  · rintro ⟨p, _, hp, hback⟩
    exact ⟨p, hp, hback⟩

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
