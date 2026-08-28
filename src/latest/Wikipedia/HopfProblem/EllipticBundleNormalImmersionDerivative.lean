import Mathlib.Geometry.Manifold.Immersion
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Analysis.Complex.Basic

/-! # The differential of a holomorphic immersion

The local normal-form definition of an immersion implies that its manifold
differential is injective.  We prove this for boundaryless complex manifolds,
using the actual normal-form charts and the chain rule.  In particular, this
does not add differential injectivity to the definition of an immersion.
-/

noncomputable section

open Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.Elliptic.NormalImmersion

variable {E F C M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]
  [NormedAddCommGroup C] [NormedSpace ℂ C]
  [TopologicalSpace M] [ChartedSpace E M]
  [TopologicalSpace N] [ChartedSpace F N]

/-- A holomorphic immersion's differential is injective.  The proof transfers
the injective linear normal form through the derivatives of its charts. -/
theorem mfderiv_injective {f : M → N} {x : M}
    (h : Manifold.IsImmersionAtOfComplement C (modelWithCornersSelf ℂ E)
      (modelWithCornersSelf ℂ F) ω f x) :
    Function.Injective (mfderiv (modelWithCornersSelf ℂ E)
      (modelWithCornersSelf ℂ F) f x) := by
  let L : E →L[ℂ] F :=
    h.equiv.toContinuousLinearMap.comp (ContinuousLinearMap.inl ℂ E C)
  have hL : Function.Injective L := by
    intro u v huv
    exact congrArg Prod.fst (h.equiv.injective huv)
  have hdom : h.domChart.MDifferentiable (modelWithCornersSelf ℂ E)
      (modelWithCornersSelf ℂ E) := by
    exact ⟨(contMDiffOn_of_mem_maximalAtlas h.domChart_mem_maximalAtlas).mdifferentiableOn
      (by simp),
      (contMDiffOn_symm_of_mem_maximalAtlas h.domChart_mem_maximalAtlas).mdifferentiableOn
      (by simp)⟩
  have hcod : MDifferentiableAt (modelWithCornersSelf ℂ F) (modelWithCornersSelf ℂ F)
      h.codChart (f x) :=
    (contMDiffAt_of_mem_maximalAtlas h.codChart_mem_maximalAtlas
      h.mem_codChart_source).mdifferentiableAt (by simp)
  have hf : MDifferentiableAt (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ F) f x :=
    h.contMDiffAt.mdifferentiableAt (by simp)
  have heq : (h.codChart ∘ f) =ᶠ[𝓝 x] (L ∘ h.domChart) := by
    filter_upwards [h.domChart.open_source.mem_nhds h.mem_domChart_source] with y hy
    have hnormal := h.writtenInCharts (by
      simpa [OpenPartialHomeomorph.extend] using h.domChart.map_source hy)
    change h.codChart (f (h.domChart.symm (h.domChart y))) =
      h.equiv (h.domChart y, 0) at hnormal
    change h.codChart (f y) = h.equiv (h.domChart y, 0)
    simpa only [h.domChart.left_inv hy] using hnormal
  have hd := heq.mfderiv_eq (I := modelWithCornersSelf ℂ E)
    (I' := modelWithCornersSelf ℂ F)
  rw [mfderiv_comp x hcod hf,
    mfderiv_comp x L.mdifferentiableAt (hdom.mdifferentiableAt h.mem_domChart_source),
    L.mfderiv_eq] at hd
  intro u v huv
  apply hdom.mfderiv_injective h.mem_domChart_source
  apply hL
  have he := congrArg (mfderiv (modelWithCornersSelf ℂ F)
    (modelWithCornersSelf ℂ F) h.codChart (f x)) huv
  change ((mfderiv (modelWithCornersSelf ℂ F) (modelWithCornersSelf ℂ F)
    h.codChart (f x)).comp (mfderiv (modelWithCornersSelf ℂ E)
    (modelWithCornersSelf ℂ F) f x)) u =
    ((mfderiv (modelWithCornersSelf ℂ F) (modelWithCornersSelf ℂ F)
    h.codChart (f x)).comp (mfderiv (modelWithCornersSelf ℂ E)
    (modelWithCornersSelf ℂ F) f x)) v at he
  rw [hd] at he
  exact he

/-- The complement-free spelling of differential injectivity. -/
theorem mfderiv_injective_of_isImmersionAt {f : M → N} {x : M}
    (h : Manifold.IsImmersionAt (modelWithCornersSelf ℂ E)
      (modelWithCornersSelf ℂ F) ω f x) :
    Function.Injective (mfderiv (modelWithCornersSelf ℂ E)
      (modelWithCornersSelf ℂ F) f x) := by
  exact mfderiv_injective h.isImmersionAtOfComplement_complement

end Wikipedia.HopfProblem.Elliptic.NormalImmersion
