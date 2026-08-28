import Wikipedia.SmoothSixDPoincare.MorseDescentField
import Wikipedia.SmoothSixDPoincare.DescentFieldGluing
import Mathlib.Topology.Separation.Regular

/-!
# A global descending field adapted to the genuine Morse charts

The finite native critical set is separated by disjoint open neighborhoods.
Closed neighborhood patches inside the Morse charts allow convex smooth
gluing to preserve the exact local descending field near every critical
point, while strictly decreasing the original function everywhere else.
-/

noncomputable section

open Set Manifold Filter
open scoped ContDiff Topology

namespace Wikipedia.SmoothSixDPoincare.ManifoldMorse

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]

/-- Every smooth Morse function on a compact manifold has a genuine adapted descending field. -/
theorem exists_adaptedDescentField {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hm : IsMorse E f) :
    ∃ V : (x : M) → TangentSpace 𝓘(ℝ, E) x,
      ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞
        (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)) ∧
      (∀ x ∈ criticalPoints E f, V x = 0) ∧
      (∀ x, x ∉ criticalPoints E f → mvfderiv 𝓘(ℝ, E) f x (V x) < 0) ∧
      ∀ p ∈ criticalPoints E f, ∃ c : SignedMorseChart (E := E) f p,
        ∀ᶠ x in 𝓝 p, V x = c.descentField x := by
  classical
  let S := criticalPoints E f
  have hS : S.Finite := finite_criticalPoints hf hm
  let : Fintype S := hS.fintype
  let c (p : S) : SignedMorseChart (E := E) f (p : M) :=
    Classical.choice (nonempty_signedMorseChart hf hm p.1 p.2)
  obtain ⟨U₀, hU₀, hdisj₀⟩ := hS.t2_separation
  let U (p : S) : Set M := U₀ p ∩ (c p).splitChart.source
  have hU (p : S) : IsOpen (U p) := (hU₀ p).2.inter (c p).splitChart.open_source
  have hpU (p : S) : (p : M) ∈ U p := ⟨(hU₀ p).1, (c p).splitChart_mem_source⟩
  have hdisj : Pairwise (fun p q : S => Disjoint (U p) (U q)) := by
    intro p q hpq
    exact (hdisj₀ p.2 q.2 (fun h => hpq (Subtype.ext h))).mono
      inter_subset_left inter_subset_left
  choose K hKnhds hKclosed hKU using
    (fun p : S => exists_mem_nhds_isClosed_subset ((hU p).mem_nhds (hpU p)))
  have hcover : criticalPoints E f ⊆ ⋃ p : S, K p := by
    intro p hp
    exact mem_iUnion.mpr ⟨⟨p, hp⟩, mem_of_mem_nhds (hKnhds ⟨p, hp⟩)⟩
  have hVloc (p : S) : ContMDiffOn 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞
      (fun x => (⟨x, (c p).descentField x⟩ : TangentBundle 𝓘(ℝ, E) M)) (U p) :=
    (c p).contMDiffOn_descentField.mono inter_subset_right
  have hdesc (p : S) (x : M) (hx : x ∈ U p) (hreg : x ∉ criticalPoints E f) :
      mvfderiv 𝓘(ℝ, E) f x ((c p).descentField x) < 0 :=
    (c p).mvfderiv_descentField_neg hf hx.2 (fun h => hreg (h.symm ▸ p.2))
  obtain ⟨V, hV, hstrict, hmatch⟩ := FlowConstruction.exists_gluedDescentField hf
    U K hU hKclosed hKU hdisj hcover (fun p => (c p).descentField) hVloc hdesc
  refine ⟨V, hV, ?_, hstrict, ?_⟩
  · intro p hp
    rw [hmatch ⟨p, hp⟩ p (mem_of_mem_nhds (hKnhds ⟨p, hp⟩))]
    exact (c ⟨p, hp⟩).descentField_center
  · intro p hp
    refine ⟨c ⟨p, hp⟩, ?_⟩
    filter_upwards [hKnhds ⟨p, hp⟩] with x hx
    exact hmatch ⟨p, hp⟩ x hx

end Wikipedia.SmoothSixDPoincare.ManifoldMorse
