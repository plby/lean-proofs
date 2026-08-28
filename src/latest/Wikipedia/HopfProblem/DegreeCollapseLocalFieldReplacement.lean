import Wikipedia.HopfProblem.DegreeCollapseLocalFunctionReplacement

/-!
# A compact supported replacement of a native tangent vector field

The local replacement agrees with the original field outside a compact
subset of the actual chart target. Its piecewise definition is smooth
across that target boundary, and retains every exterior germ. Zero removal
is a statement about the vector field; no Lyapunov function is inferred.
-/

noncomputable section

open Set Filter
open scoped ContDiff Manifold Topology

namespace Wikipedia.HopfProblem.DegreeCollapse.LocalFieldReplacement

variable {D E H X M : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] [TopologicalSpace X] [ChartedSpace H X]
  {I : ModelWithCorners ℝ D H}
  [TopologicalSpace M] [ChartedSpace E M]
  (Φ : PartialDiffeomorph I 𝓘(ℝ, E) X M ∞)

def replace (V W : (x : M) → TangentSpace 𝓘(ℝ, E) x)
    (x : M) : TangentSpace 𝓘(ℝ, E) x := by
  classical
  exact if x ∈ Φ.target then W x else V x

theorem replace_of_mem (V W : (x : M) → TangentSpace 𝓘(ℝ, E) x)
    {x : M} (hx : x ∈ Φ.target) : replace Φ V W x = W x := by simp [replace, hx]

theorem replace_of_notMem (V W : (x : M) → TangentSpace 𝓘(ℝ, E) x)
    {x : M} (hx : x ∉ Φ.target) : replace Φ V W x = V x := by simp [replace, hx]

variable [T2Space M] [IsManifold 𝓘(ℝ, E) ∞ M]

/-- Smoothness is proved at the chart boundary using the compact support image. -/
theorem exists_smooth_field_replacement
    (V W : (x : M) → TangentSpace 𝓘(ℝ, E) x)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞
      (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hW : ContMDiffOn 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞
      (fun x => (⟨x, W x⟩ : TangentBundle 𝓘(ℝ, E) M)) Φ.target)
    {K : Set X} (hK : IsCompact K) (hKΦ : K ⊆ Φ.source)
    (hfix : ∀ x ∈ Φ.target, x ∉ Φ '' K → W x = V x)
    (hreg : ∀ x ∈ Φ.target, W x ≠ 0) :
    ∃ V' : (x : M) → TangentSpace 𝓘(ℝ, E) x,
      ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞
        (fun x => (⟨x, V' x⟩ : TangentBundle 𝓘(ℝ, E) M)) ∧
      (∀ x ∈ Φ.target, V' x = W x) ∧
      (∀ x, V' x = 0 ↔ V x = 0 ∧ x ∉ Φ.target) ∧
      ∀ x ∉ Φ '' K, ∀ᶠ y in 𝓝 x, V' y = V y := by
  let V' := replace Φ V W
  have hclosed : IsClosed (Φ '' K) :=
    (hK.image_of_continuousOn (Φ.contMDiffOn_toFun.continuousOn.mono hKΦ)).isClosed
  have hoff (x : M) (hx : x ∉ Φ '' K) : ∀ᶠ y in 𝓝 x, V' y = V y := by
    filter_upwards [hclosed.isOpen_compl.mem_nhds hx] with y hy
    by_cases hyt : y ∈ Φ.target
    · exact (replace_of_mem Φ V W hyt).trans (hfix y hyt hy)
    · exact replace_of_notMem Φ V W hyt
  have hsmooth : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞
      (fun x => (⟨x, V' x⟩ : TangentBundle 𝓘(ℝ, E) M)) := by
    intro x
    by_cases hx : x ∈ Φ.target
    · apply (hW.contMDiffAt (Φ.open_target.mem_nhds hx)).congr_of_eventuallyEq
      filter_upwards [Φ.open_target.mem_nhds hx] with y hy
      exact congrArg (fun v => (⟨y, v⟩ : TangentBundle 𝓘(ℝ, E) M))
        (replace_of_mem Φ V W hy)
    · have hnot : x ∉ Φ '' K := by
        rintro ⟨p, hp, rfl⟩
        exact hx (Φ.map_source' (hKΦ hp))
      apply hV.contMDiffAt.congr_of_eventuallyEq
      filter_upwards [hoff x hnot] with y hy
      exact congrArg (fun v => (⟨y, v⟩ : TangentBundle 𝓘(ℝ, E) M)) hy
  refine ⟨V', hsmooth, fun x hx => replace_of_mem Φ V W hx, ?_, hoff⟩
  intro x
  by_cases hx : x ∈ Φ.target
  · rw [show V' x = W x from replace_of_mem Φ V W hx]
    simp only [hreg x hx, hx, not_true_eq_false, and_false]
  · rw [show V' x = V x from replace_of_notMem Φ V W hx]
    simp only [hx, not_false_eq_true, and_true]

end Wikipedia.HopfProblem.DegreeCollapse.LocalFieldReplacement
