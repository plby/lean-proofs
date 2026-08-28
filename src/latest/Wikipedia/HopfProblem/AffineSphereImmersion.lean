import Wikipedia.HopfProblem.AffineSphereManifold
import Mathlib.Geometry.Manifold.Immersion

/-!+# Checking immersions on the two affine sphere charts
-/

noncomputable section

open Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.TwoAffineCharts

variable {Y E F N : Type*} [TopologicalSpace Y] [T2Space Y]
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]
  [TopologicalSpace N] [ChartedSpace E N]
  (A : TwoAffineCharts Y)

theorem immersion_of_comp_affineMaps (f : Y → N) (hc : Continuous f)
    (hf : ∀ b, Manifold.IsImmersionOfComplement F (modelWithCornersSelf ℂ ℂ)
      (modelWithCornersSelf ℂ E) ω (f ∘ A.affineMap b)) :
    letI := A.chartedSpace
    Manifold.IsImmersionOfComplement F (modelWithCornersSelf ℂ ℂ)
      (modelWithCornersSelf ℂ E) ω f := by
  let := A.chartedSpace
  let := A.isManifold
  intro y
  let b := A.preferredChart y
  obtain ⟨z, hz⟩ := A.preferred_mem y
  let hi := hf b z
  let p := A.parametrization b
  let d := p.symm.trans hi.domChart
  have hp : p.symm ∈ IsManifold.maximalAtlas (modelWithCornersSelf ℂ ℂ) ω Y :=
    IsManifold.subset_maximalAtlas (mem_range_self b)
  have hy : y ∈ p.target := by
    rw [parametrization_target]
    exact ⟨z, hz⟩
  have hpy : p.symm y = z := by
    rw [← hz]
    exact A.parametrization_symm_apply b z
  refine Manifold.IsImmersionAtOfComplement.mk_of_continuousAt hc.continuousAt hi.equiv d
    hi.codChart ⟨hy, ?_⟩ ?_ ?_ hi.codChart_mem_maximalAtlas ?_
  · change p.symm y ∈ hi.domChart.source
    rw [hpy]
    exact hi.mem_domChart_source
  · rw [← hz]
    exact hi.mem_codChart_source
  · apply d.mem_maximalAtlas_of_contMDiffOn
    · exact (contMDiffOn_of_mem_maximalAtlas hi.domChart_mem_maximalAtlas).comp
        ((contMDiffOn_of_mem_maximalAtlas hp).mono inter_subset_left) (fun _ hw => hw.2)
    · exact (contMDiffOn_symm_of_mem_maximalAtlas hp).comp
        ((contMDiffOn_symm_of_mem_maximalAtlas hi.domChart_mem_maximalAtlas).mono inter_subset_left)
        (fun _ hw => hw.2)
  · intro w hw
    have hw' : w ∈ d.target := by simpa [OpenPartialHomeomorph.extend] using hw
    change hi.codChart (f (p (hi.domChart.symm w))) = hi.equiv (w, 0)
    exact hi.writtenInCharts (by simpa [OpenPartialHomeomorph.extend] using hw'.1)

end Wikipedia.HopfProblem.TwoAffineCharts
