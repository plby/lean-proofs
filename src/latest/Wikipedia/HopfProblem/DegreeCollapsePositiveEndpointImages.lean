import Wikipedia.HopfProblem.DegreeCollapseGlobalBasinImages

/-!
# Endpoint obstacles above an untouched lower cut

Inside the strict superlevel of a lower cut, a backward endpoint must itself
lie strictly above that cut: the original Morse value decreases along the
actual flow. Thus the low endpoint obstruction needs dimension bounds only
for critical points above the lower cut. The negative half can retain all
its original critical points and indices.

The constructed countable smooth family agrees with the entire original
level-crossing obstruction on this open superlevel, point for point.
-/

noncomputable section

open Set Function Filter Manifold
open scoped ContDiff Topology
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] {f : M → ℝ}

abbrev EndpointBasinIndexAbove (_S : AdaptedSurgeryWindows E f) (b a : ℝ) :=
  ({p : criticalPoints E f // a ≤ f p.val} × ℕ) ⊕
    ({p : criticalPoints E f // b < f p.val ∧ f p.val ≤ a} × ℕ)

omit [FiniteDimensional ℝ E] [T2Space M] [CompactSpace M] in
theorem endpointBasinIndexAbove_countable (S : AdaptedSurgeryWindows E f) (b a : ℝ) :
    Countable (EndpointBasinIndexAbove S b a) := by
  let _ := S.finite.fintype
  unfold EndpointBasinIndexAbove
  infer_instance

theorem AdaptedSurgeryWindows.exists_endpoint_obstruction_images_above_cut
    (S : AdaptedSurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (b a : ℝ) {d : ℕ}
    (hhigh : ∀ p : criticalPoints E f, a ≤ f p →
      Module.finrank ℝ E - nativeMorseIndex E f p ≤ d)
    (hlow : ∀ p : criticalPoints E f, b < f p → f p ≤ a → nativeMorseIndex E f p ≤ d) :
    ∃ g : EndpointBasinIndexAbove S b a → EuclideanSpace ℝ (Fin d) → M,
      (∀ i, ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) 𝓘(ℝ, E) ∞ (g i)) ∧
      ∀ x, b < f x →
        (x ∈ forwardHighBasins S a ∪ backwardLowBasins S a ↔ x ∈ ⋃ i, range (g i)) := by
  choose gF hgF hF using (fun p : {p : criticalPoints E f // a ≤ f p.val} =>
    S.exists_forward_basin_global_images hf p.val (hhigh p.val p.property))
  choose gB hgB hB using (fun p : {p : criticalPoints E f // b < f p.val ∧ f p.val ≤ a} =>
    S.exists_backward_basin_global_images hf p.val (hlow p.val p.property.1 p.property.2))
  let g : EndpointBasinIndexAbove S b a → EuclideanSpace ℝ (Fin d) → M :=
    Sum.elim (fun i => gF i.1 i.2) (fun i => gB i.1 i.2)
  refine ⟨g, ?_, ?_⟩
  · intro i
    rcases i with ⟨p, n⟩ | ⟨p, n⟩
    · exact hgF p n
    · exact hgB p n
  · intro x hx
    constructor
    · rintro (⟨p, hp, hlim⟩ | ⟨p, hp, hlim⟩)
      · have hh : x ∈ ⋃ n, range (gF ⟨p, hp⟩ n) := (hF ⟨p, hp⟩) ▸ hlim
        obtain ⟨n, hn⟩ := mem_iUnion.mp hh
        exact mem_iUnion.mpr ⟨Sum.inl (⟨p, hp⟩, n), hn⟩
      · have hmono := FlowConstruction.antitone_flow_height hf S.flow
          S.integral S.zero S.descent x
        have hxp : f x ≤ f p := by
          simpa only [S.flow.map_zero_apply] using
            hmono.ge_of_tendsto (hf.continuous.continuousAt.tendsto.comp hlim) 0
        have hbp : b < f p := hx.trans_le hxp
        have hh : x ∈ ⋃ n, range (gB ⟨p, hbp, hp⟩ n) := (hB ⟨p, hbp, hp⟩) ▸ hlim
        obtain ⟨n, hn⟩ := mem_iUnion.mp hh
        exact mem_iUnion.mpr ⟨Sum.inr (⟨p, hbp, hp⟩, n), hn⟩
    · intro hmem
      obtain ⟨i, hi⟩ := mem_iUnion.mp hmem
      rcases i with ⟨p, n⟩ | ⟨p, n⟩
      · have hh : Tendsto (fun t => S.flow t x) atTop (𝓝 p.val.val) := by
          change x ∈ {x : M | Tendsto (fun t => S.flow t x) atTop (𝓝 p.val.val)}
          rw [hF p]
          exact mem_iUnion.mpr ⟨n, hi⟩
        exact Or.inl ⟨p.val, p.property, hh⟩
      · have hh : Tendsto (fun t => S.flow t x) atBot (𝓝 p.val.val) := by
          change x ∈ {x : M | Tendsto (fun t => S.flow t x) atBot (𝓝 p.val.val)}
          rw [hB p]
          exact mem_iUnion.mpr ⟨n, hi⟩
        exact Or.inr ⟨p.val, p.property.2, hh⟩

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
