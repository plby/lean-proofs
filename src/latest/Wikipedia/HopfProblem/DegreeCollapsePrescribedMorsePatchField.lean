import Wikipedia.HopfProblem.DegreeCollapseClosedPatchDescentField
import Wikipedia.SmoothSixDPoincare.AdaptedMorseField

/-!
# One original descending field with prescribed native Morse patches

The native Morse field vanishes at every critical point of its chart.
An existing adapted global field and closed-patch gluing therefore give
one smooth descending field agreeing with finitely many disjoint
prescribed Morse patches, with all original critical points stationary.
-/

noncomputable section

open Set Function Filter Manifold
open scoped ContDiff Topology
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]

theorem morse_descentField_zero_at_critical {f : M → ℝ} {p : M}
    (c : SignedMorseChart (E := E) f p) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    {x : M} (hx : x ∈ c.splitChart.source) (hcrit : x ∈ criticalPoints E f) :
    c.descentField x = 0 := by
  by_cases hxp : x = p
  · subst x
    exact c.descentField_center
  · have hneg := c.mvfderiv_descentField_neg hf hx hxp
    have hc : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) f x = 0 := hcrit
    have hz : mvfderiv 𝓘(ℝ, E) f x (c.descentField x) = 0 := by
      unfold mvfderiv
      rw [hc]
      rfl
    rw [hz] at hneg
    exact False.elim (lt_irrefl (0 : ℝ) hneg)

variable [CompactSpace M]

theorem exists_prescribed_morse_patch_field {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hm : IsMorse E f)
    {ι : Type*} [Finite ι] (p : ι → M) (hp : ∀ i, p i ∈ criticalPoints E f)
    (c : ∀ i, SignedMorseChart (E := E) f (p i)) (K : ι → Set M)
    (hK : ∀ i, IsClosed (K i)) (hKchart : ∀ i, K i ⊆ (c i).splitChart.source)
    (hdisj : Pairwise (fun i j => Disjoint (K i) (K j))) :
    ∃ V : (x : M) → TangentSpace 𝓘(ℝ, E) x,
      ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞
        (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)) ∧
      (∀ x ∈ criticalPoints E f, V x = 0) ∧
      (∀ x, x ∉ criticalPoints E f → mvfderiv 𝓘(ℝ, E) f x (V x) < 0) ∧
      ∀ i x, x ∈ K i → V x = (c i).descentField x := by
  obtain ⟨V₀, hV₀, hzero₀, hdesc₀, -⟩ := exists_adaptedDescentField hf hm
  apply exists_closed_patch_descent_field hf V₀ hV₀ hzero₀ hdesc₀ K
    (fun i => (c i).splitChart.source) hK (fun i => (c i).splitChart.open_source)
    hKchart hdisj (fun i => (c i).descentField) (fun i => (c i).contMDiffOn_descentField)
  · exact fun i x hx hc => morse_descentField_zero_at_critical (c i) hf hx hc
  · intro i x hx hreg
    exact (c i).mvfderiv_descentField_neg hf hx (fun h => hreg (h.symm ▸ hp i))

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
