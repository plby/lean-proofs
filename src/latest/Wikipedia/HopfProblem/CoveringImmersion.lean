import Wikipedia.HopfProblem.CoveringManifold
import Mathlib.Geometry.Manifold.Immersion

/-!+# Immersions through the constructed holomorphic covering quotient

A local inverse of the quotient map transports the target chart of an
immersion. Restricting its source chart ensures that the chosen inverse
recovers the original lift on the whole coordinate neighbourhood.
-/

noncomputable section

open Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.CoveringQuotient

variable {E E' F M A Q G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup E'] [NormedSpace ℂ E']
  [NormedAddCommGroup F] [NormedSpace ℂ F]
  [TopologicalSpace M] [ChartedSpace E M]
  [TopologicalSpace A] [ChartedSpace E' A]
  [TopologicalSpace Q] [Group G] [MulAction G M]
  [IsManifold (modelWithCornersSelf ℂ E) ω M]
  {q : M → Q} (hq : IsQuotientCoveringMap q G)
  (hG : ∀ g : G, ContMDiff (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E) ω
    (fun x : M => g • x))

include hG in
theorem immersionAt_project {f : A → M} {x : A} (hf : Continuous f)
    (hi : Manifold.IsImmersionAtOfComplement F (modelWithCornersSelf ℂ E')
      (modelWithCornersSelf ℂ E) ω f x) :
    letI := chartedSpace (E := E) hq
    Manifold.IsImmersionAtOfComplement F (modelWithCornersSelf ℂ E')
      (modelWithCornersSelf ℂ E) ω (q ∘ f) x := by
  let := chartedSpace (E := E) hq
  let := isManifold (E := E) hq ω hG
  let e := localInverse hq (f x)
  let U := f ⁻¹' e.target
  have hU : IsOpen U := e.open_target.preimage hf
  let d := hi.domChart.restr U
  let c := e.trans hi.codChart
  have hself : e (q (f x)) = f x :=
    hq.isCoveringMap.isLocalHomeomorph.localInverseAt_apply_self
  have hs : (c.symm : E → Q) = q ∘ hi.codChart.symm := by
    change (localInverse hq (f x)).symm ∘ hi.codChart.symm = _
    rw [localInverse_symm]
  refine Manifold.IsImmersionAtOfComplement.mk_of_continuousAt
    (hq.continuous.comp hf).continuousAt hi.equiv d c ?_ ?_ ?_ ?_ ?_
  · change x ∈ (hi.domChart.restr U).source
    rw [OpenPartialHomeomorph.restr_source' _ _ hU]
    exact ⟨hi.mem_domChart_source,
      hq.isCoveringMap.isLocalHomeomorph.self_mem_localInverseAt_target⟩
  · refine ⟨hq.isCoveringMap.isLocalHomeomorph.apply_self_mem_localInverseAt_source, ?_⟩
    change e (q (f x)) ∈ hi.codChart.source
    rw [hself]
    exact hi.mem_codChart_source
  · exact restr_mem_maximalAtlas _ hi.domChart_mem_maximalAtlas hU
  · apply c.mem_maximalAtlas_of_contMDiffOn
    · exact (contMDiffOn_of_mem_maximalAtlas hi.codChart_mem_maximalAtlas).comp
        ((localInverse_holomorphic hq ω hG (f x)).mono inter_subset_left) (fun _ hy => hy.2)
    · rw [hs]
      exact (contMDiff_project hq ω hG).comp_contMDiffOn
        ((contMDiffOn_symm_of_mem_maximalAtlas hi.codChart_mem_maximalAtlas).mono inter_subset_left)
  · intro z hz
    have hz' : z ∈ d.target := by simpa [OpenPartialHomeomorph.extend] using hz
    have hz0 : z ∈ hi.domChart.target := hz'.1
    have hfz : f (hi.domChart.symm z) ∈ e.target := by
      have hmem := d.map_target hz'
      change (hi.domChart.restr U).symm z ∈ (hi.domChart.restr U).source at hmem
      rw [OpenPartialHomeomorph.restr_source' _ _ hU] at hmem
      exact hmem.2
    have heq : e (q (f (hi.domChart.symm z))) = f (hi.domChart.symm z) := by
      simpa only [e, localInverse_symm] using e.right_inv hfz
    change hi.codChart (e (q (f (hi.domChart.symm z)))) = hi.equiv (z, 0)
    rw [heq]
    exact hi.writtenInCharts (by simpa [OpenPartialHomeomorph.extend] using hz0)

include hG in
theorem immersion_project {f : A → M} (hf : Continuous f)
    (hi : Manifold.IsImmersionOfComplement F (modelWithCornersSelf ℂ E')
      (modelWithCornersSelf ℂ E) ω f) :
    letI := chartedSpace (E := E) hq
    Manifold.IsImmersionOfComplement F (modelWithCornersSelf ℂ E')
      (modelWithCornersSelf ℂ E) ω (q ∘ f) := by
  let := chartedSpace (E := E) hq
  intro x
  exact immersionAt_project hq hG hf (hi x)

end Wikipedia.HopfProblem.CoveringQuotient
