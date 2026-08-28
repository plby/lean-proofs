import Wikipedia.NoExoticSixSphere.IntersectionTraceTransverseEndpoint
import Wikipedia.NoExoticSixSphere.IntersectionTraceTimeReverse

/-!
# Both actual transverse time ends have half-line charts

Time reversal transports the constructed initial endpoint chart to the
terminal endpoint. Neither endpoint needs a constant time collar.
-/

noncomputable section

open Set Function Topology
open scoped Manifold ContDiff

namespace NoExoticSixSphere.IntersectionTrace

open GLOrthonormalization MapIntersections InvolutionQuotient

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  (f g : ℝ → Sphere 3 → M)
  (hf : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 6) ∞ (uncurry f))
  (hg : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 6) ∞ (uncurry g))

include hf in
theorem contMDiff_reverse_family :
    ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 6) ∞ (uncurry (fun t ↦ f (1 - t))) := by
  have htime : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓘(ℝ, ℝ).prod (𝓡 3)) ∞
      (fun q : ℝ × Sphere 3 ↦ (1 - q.1, q.2)) :=
    (((contDiff_const.sub contDiff_id).contMDiff).comp contMDiff_fst).prodMk contMDiff_snd
  exact hf.comp htime

include hf hg in
theorem exists_one_halfLine_chart_of_transverse [IsManifold (𝓡 6) ∞ M]
    (p : pairs (f 1) (g 1))
    (ht : Surjective ((mfderiv (𝓡 3) (𝓡 6) (f 1) p.val.1).coprod
      (mfderiv (𝓡 3) (𝓡 6) (g 1) p.val.2))) :
    ∃ d : OpenPartialHomeomorph (space f g) HalfLine,
      endpoint f g 1 p ∈ d.source ∧
      (∀ q ∈ d.source, (d q).val = 1 - q.val.1) ∧
      ∀ q ∈ d.source, (d q).val = 0 ↔ q ∈ ends f g := by
  let f' : ℝ → Sphere 3 → M := fun t ↦ f (1 - t)
  let g' : ℝ → Sphere 3 → M := fun t ↦ g (1 - t)
  have hfe : f' 0 = f 1 := by simp only [f', sub_zero]
  have hge : g' 0 = g 1 := by simp only [g', sub_zero]
  let p' : pairs (f' 0) (g' 0) := ⟨p.val, by
    rw [hfe, hge]
    exact p.property⟩
  have ht' : Surjective ((mfderiv (𝓡 3) (𝓡 6) (f' 0) p'.val.1).coprod
      (mfderiv (𝓡 3) (𝓡 6) (g' 0) p'.val.2)) := by
    change Surjective ((mfderiv (𝓡 3) (𝓡 6) (f' 0) p.val.1).coprod
      (mfderiv (𝓡 3) (𝓡 6) (g' 0) p.val.2))
    rw [hfe, hge]
    exact ht
  obtain ⟨d, hdp, hdtime, hdB⟩ := exists_zero_halfLine_chart_of_transverse f' g'
    (contMDiff_reverse_family f hf) (contMDiff_reverse_family g hg) p' ht'
  let e := reverseHomeomorph f g
  have hep : e (endpoint f g 1 p) = endpoint f' g' 0 p' := by
    apply Subtype.ext
    exact Prod.ext (by change (1 : ℝ) - 1 = 0; ring) rfl
  refine ⟨e.toOpenPartialHomeomorph.trans d, ⟨mem_univ _, ?_⟩, ?_, ?_⟩
  · change d.source (e (endpoint f g 1 p))
    rw [hep]
    exact hdp
  · intro q hq
    exact hdtime (e q) hq.2
  · intro q hq
    exact (hdB (e q) hq.2).trans (reverseHomeomorph_mem_ends_iff f g q)

end NoExoticSixSphere.IntersectionTrace
