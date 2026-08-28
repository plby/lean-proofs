import Mathlib.Geometry.Manifold.Submersion
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Analysis.Complex.Basic

/-! # The differential of a holomorphic submersion

The local normal-form definition of a submersion implies that its manifold
differential is surjective.  For boundaryless complex manifolds, the proof
transports the surjective linear projection through the derivatives of the
actual normal-form charts.
-/

noncomputable section

open Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.SubmersionDifferential

variable {E F C M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]
  [NormedAddCommGroup C] [NormedSpace ℂ C]
  [TopologicalSpace M] [ChartedSpace E M]
  [TopologicalSpace N] [ChartedSpace F N]

/-- A holomorphic submersion's differential is surjective.  This follows from
its chart normal form, without any additional differential assumption. -/
theorem mfderiv_surjective {f : M → N} {x : M}
    (h : Manifold.IsSubmersionAtOfComplement C (modelWithCornersSelf ℂ E)
      (modelWithCornersSelf ℂ F) ω f x) :
    Function.Surjective (mfderiv (modelWithCornersSelf ℂ E)
      (modelWithCornersSelf ℂ F) f x) := by
  let L : E →L[ℂ] F :=
    (ContinuousLinearMap.fst ℂ F C).comp h.equiv.toContinuousLinearMap
  have hL : Function.Surjective L := by
    intro v
    refine ⟨h.equiv.symm (v, 0), ?_⟩
    change (h.equiv (h.equiv.symm (v, 0))).1 = v
    rw [h.equiv.apply_symm_apply]
  have hdom : h.domChart.MDifferentiable (modelWithCornersSelf ℂ E)
      (modelWithCornersSelf ℂ E) := by
    exact ⟨(contMDiffOn_of_mem_maximalAtlas h.domChart_mem_maximalAtlas).mdifferentiableOn
      (by simp),
      (contMDiffOn_symm_of_mem_maximalAtlas h.domChart_mem_maximalAtlas).mdifferentiableOn
      (by simp)⟩
  have hcod : h.codChart.MDifferentiable (modelWithCornersSelf ℂ F)
      (modelWithCornersSelf ℂ F) := by
    exact ⟨(contMDiffOn_of_mem_maximalAtlas h.codChart_mem_maximalAtlas).mdifferentiableOn
      (by simp),
      (contMDiffOn_symm_of_mem_maximalAtlas h.codChart_mem_maximalAtlas).mdifferentiableOn
      (by simp)⟩
  have hf : MDifferentiableAt (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ F) f x :=
    h.contMDiffAt.mdifferentiableAt (by simp)
  have heq : (h.codChart ∘ f) =ᶠ[𝓝 x] (L ∘ h.domChart) := by
    filter_upwards [h.domChart.open_source.mem_nhds h.mem_domChart_source] with y hy
    have hnormal := h.writtenInCharts (by
      simpa [OpenPartialHomeomorph.extend] using h.domChart.map_source hy)
    change h.codChart (f (h.domChart.symm (h.domChart y))) =
      (h.equiv (h.domChart y)).1 at hnormal
    change h.codChart (f y) = (h.equiv (h.domChart y)).1
    simpa only [h.domChart.left_inv hy] using hnormal
  have hd := heq.mfderiv_eq (I := modelWithCornersSelf ℂ E)
    (I' := modelWithCornersSelf ℂ F)
  rw [mfderiv_comp x (hcod.mdifferentiableAt h.mem_codChart_source) hf,
    mfderiv_comp x L.mdifferentiableAt (hdom.mdifferentiableAt h.mem_domChart_source),
    L.mfderiv_eq] at hd
  intro v
  obtain ⟨u, hu⟩ := (hL.comp (hdom.mfderiv_surjective h.mem_domChart_source))
    (mfderiv (modelWithCornersSelf ℂ F) (modelWithCornersSelf ℂ F) h.codChart (f x) v)
  refine ⟨u, hcod.mfderiv_injective h.mem_codChart_source ?_⟩
  change ((mfderiv (modelWithCornersSelf ℂ F) (modelWithCornersSelf ℂ F)
    h.codChart (f x)).comp (mfderiv (modelWithCornersSelf ℂ E)
    (modelWithCornersSelf ℂ F) f x)) u = _
  rw [hd]
  exact hu

/-- The complement-free spelling of differential surjectivity. -/
theorem mfderiv_surjective_of_isSubmersionAt {f : M → N} {x : M}
    (h : Manifold.IsSubmersionAt (modelWithCornersSelf ℂ E)
      (modelWithCornersSelf ℂ F) ω f x) :
    Function.Surjective (mfderiv (modelWithCornersSelf ℂ E)
      (modelWithCornersSelf ℂ F) f x) := by
  exact mfderiv_surjective h.isSubmersionAtOfComplement_complement

end Wikipedia.HopfProblem.SubmersionDifferential
