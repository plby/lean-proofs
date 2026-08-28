import Wikipedia.HopfProblem.TriangleUniformizationGluingRemovablePoints

/-!
# Removing finitely many punctures from maps between complex curves

A continuous map between complex one-dimensional manifolds that is
holomorphic away from a finite set is holomorphic everywhere. The
complex charted-space structure supplies the required T1 separation;
no additional separation assumption is imposed on either manifold.
-/

noncomputable section

open Filter Set
open scoped Topology ContDiff Manifold

namespace Wikipedia.HopfProblem.TriangleUniformizationGluing

variable {M N : Type*}
  [TopologicalSpace M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ) ω M]
  [TopologicalSpace N] [ChartedSpace ℂ N] [IsManifold 𝓘(ℂ) ω N]

/-- A continuous map between complex curves is holomorphic if it is
holomorphic away from finitely many points. -/
theorem contMDiff_of_continuous_of_finite {f : M → N} {S : Set M}
    (hf : Continuous f) (hS : S.Finite)
    (hd : ∀ z ∉ S, ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω f z) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f := by
  have : T1Space M := ChartedSpace.t1Space ℂ M
  intro x
  apply contMDiffAt_of_continuousAt_of_punctured hf.continuousAt
  have hclosed : IsClosed (S \ {x}) := (hS.subset sdiff_subset).isClosed
  have haway : (S \ {x})ᶜ ∈ 𝓝 x :=
    hclosed.isOpen_compl.mem_nhds (by simp)
  filter_upwards [eventually_nhdsWithin_of_eventually_nhds haway,
    self_mem_nhdsWithin] with z hz hzx
  exact hd z (fun hzS => hz ⟨hzS, hzx⟩)

/-- The same finite-puncture theorem with holomorphicity stated on the
open complement of the exceptional set. -/
theorem contMDiff_of_continuous_of_contMDiffOn_compl_finite
    {f : M → N} {S : Set M} (hf : Continuous f) (hS : S.Finite)
    (hd : ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω f Sᶜ) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f := by
  have : T1Space M := ChartedSpace.t1Space ℂ M
  apply contMDiff_of_continuous_of_finite hf hS
  intro z hz
  exact hd.contMDiffAt (hS.isClosed.isOpen_compl.mem_nhds hz)

end Wikipedia.HopfProblem.TriangleUniformizationGluing
