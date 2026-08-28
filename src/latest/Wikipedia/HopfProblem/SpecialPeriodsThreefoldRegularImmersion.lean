import Mathlib.Geometry.Manifold.Immersion
import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Analysis.Complex.Basic

/-!
# Fixed-complement immersions through local biholomorphisms

Postcomposition by a local biholomorphism transports the actual target
chart of an immersion. The continuous linear normal form, and hence its
specified complement, is unchanged. Only a local inverse near the image
point is needed; neither global injectivity nor a covering action is assumed.
-/

noncomputable section

open Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem

variable {E V F A M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup V] [NormedSpace ℂ V]
  [NormedAddCommGroup F] [NormedSpace ℂ F]
  [TopologicalSpace A] [ChartedSpace E A]
  [TopologicalSpace M] [ChartedSpace V M]
  [TopologicalSpace N] [ChartedSpace V N]
  [IsManifold (modelWithCornersSelf ℂ V) ω N]

/-- Postcomposition by a local biholomorphism preserves the specified
complement in the immersion normal form. -/
theorem immersionAt_postcomp_localDiffeomorph {f : A → M} {q : M → N} {x : A}
    (hf : Manifold.IsImmersionAtOfComplement F (modelWithCornersSelf ℂ E)
      (modelWithCornersSelf ℂ V) ω f x)
    (hq : IsLocalDiffeomorphAt (modelWithCornersSelf ℂ V)
      (modelWithCornersSelf ℂ V) ω q (f x)) :
    Manifold.IsImmersionAtOfComplement F (modelWithCornersSelf ℂ E)
      (modelWithCornersSelf ℂ V) ω (q ∘ f) x := by
  let e := hq.localInverse.toOpenPartialHomeomorph
  have hUmem : f ⁻¹' e.target ∈ 𝓝 x :=
    hf.continuousAt (e.open_target.mem_nhds hq.localInverse_mem_target)
  obtain ⟨U, hUsub, hU, hxU⟩ := mem_nhds_iff.mp hUmem
  let d := hf.domChart.restr U
  let c := e.trans hf.codChart
  have hself : e (q (f x)) = f x :=
    hq.localInverse_left_inv hq.localInverse_mem_target
  refine Manifold.IsImmersionAtOfComplement.mk_of_continuousAt
    (hq.contMDiffAt.continuousAt.comp hf.continuousAt) hf.equiv d c ?_ ?_ ?_ ?_ ?_
  · change x ∈ (hf.domChart.restr U).source
    rw [OpenPartialHomeomorph.restr_source' _ _ hU]
    exact ⟨hf.mem_domChart_source, hxU⟩
  · refine ⟨hq.localInverse_mem_source, ?_⟩
    change e (q (f x)) ∈ hf.codChart.source
    rw [hself]
    exact hf.mem_codChart_source
  · exact restr_mem_maximalAtlas _ hf.domChart_mem_maximalAtlas hU
  · apply c.mem_maximalAtlas_of_contMDiffOn
    · exact (contMDiffOn_of_mem_maximalAtlas hf.codChart_mem_maximalAtlas).comp
        (hq.localInverse.contMDiffOn_toFun.mono inter_subset_left) (fun _ hy => hy.2)
    · exact hq.localInverse.contMDiffOn_invFun.comp
        ((contMDiffOn_symm_of_mem_maximalAtlas hf.codChart_mem_maximalAtlas).mono
          inter_subset_left) (fun _ hy => hy.2)
  · intro z hz
    have hz' : z ∈ d.target := by simpa [OpenPartialHomeomorph.extend] using hz
    have hz0 : z ∈ hf.domChart.target := hz'.1
    have hfz : f (hf.domChart.symm z) ∈ e.target := by
      have hmem := d.map_target hz'
      change (hf.domChart.restr U).symm z ∈ (hf.domChart.restr U).source at hmem
      rw [OpenPartialHomeomorph.restr_source' _ _ hU] at hmem
      exact hUsub hmem.2
    have heq : e (q (f (hf.domChart.symm z))) = f (hf.domChart.symm z) :=
      hq.localInverse_left_inv hfz
    change hf.codChart (e (q (f (hf.domChart.symm z)))) = hf.equiv (z, 0)
    rw [heq]
    exact hf.writtenInCharts (by simpa [OpenPartialHomeomorph.extend] using hz0)

/-- The same fixed complement is preserved at every point when the
postcomposed map is a local biholomorphism everywhere. -/
theorem immersion_postcomp_localDiffeomorph {f : A → M} {q : M → N}
    (hf : Manifold.IsImmersionOfComplement F (modelWithCornersSelf ℂ E)
      (modelWithCornersSelf ℂ V) ω f)
    (hq : IsLocalDiffeomorph (modelWithCornersSelf ℂ V)
      (modelWithCornersSelf ℂ V) ω q) :
    Manifold.IsImmersionOfComplement F (modelWithCornersSelf ℂ E)
      (modelWithCornersSelf ℂ V) ω (q ∘ f) :=
  fun x => immersionAt_postcomp_localDiffeomorph (hf x) (hq (f x))

end Wikipedia.HopfProblem
