import Wikipedia.NoExoticSixSphere.OpenSubsetDifferential

/-!
# Smoothness on an open set and on its inherited manifold

Restriction to an open subset does not change smoothness. The reverse
direction uses the actual smooth local inverse of the subtype inclusion.
-/

open scoped Manifold ContDiff Topology
open Set Filter TopologicalSpace

namespace NoExoticSixSphere

variable {B H M C H' N : Type*}
  [NormedAddCommGroup B] [NormedSpace ℝ B] [TopologicalSpace H]
  {I : ModelWithCorners ℝ B H} [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup C] [NormedSpace ℝ C] [TopologicalSpace H']
  {J : ModelWithCorners ℝ C H'} [TopologicalSpace N] [ChartedSpace H' N]

theorem contMDiffOn_iff_openSubset (U : Opens M) (f : M → N) :
    ContMDiffOn I J ∞ f U ↔ ContMDiff I J ∞ (fun x : U ↦ f x.val) := by
  constructor
  · intro hf
    exact hf.comp_contMDiff contMDiff_subtype_val (fun x ↦ x.property)
  · intro hf x hx
    let e := openSubsetPartialDiffeomorph (I := I) U ⟨⟨x, hx⟩⟩
    have hxt : x ∈ e.target := by
      change x ∈ (U.openPartialHomeomorphSubtypeCoe ⟨⟨x, hx⟩⟩).target
      rwa [Opens.openPartialHomeomorphSubtypeCoe_target]
    have he := e.contMDiffOn_invFun.contMDiffAt (e.open_target.mem_nhds hxt)
    have heq : f =ᶠ[𝓝 x] (fun y ↦ f (e.symm y).val) := by
      filter_upwards [e.open_target.mem_nhds hxt] with y hy
      exact (congrArg f (e.right_inv' hy)).symm
    exact ((hf.contMDiffAt.comp x he).congr_of_eventuallyEq heq).contMDiffWithinAt

end NoExoticSixSphere
