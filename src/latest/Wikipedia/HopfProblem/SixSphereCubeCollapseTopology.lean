import Wikipedia.HopfProblem.SixSphereCubeCollapseBasic

/-!
# Continuity and the quotient property of the actual collapse map

The open-complement part uses the original subtype topology. At the added
point, compact complements have closed images in the Hausdorff source.
For a compact source and a nonempty closed subset this is a genuine
quotient map onto Mathlib's native one-point compactification.
-/

noncomputable section

open Set Topology
open scoped OnePoint

namespace Wikipedia.HopfProblem.SixSphereCube

variable {K : Type*} [TopologicalSpace K] [T2Space K] (F : Set K)

/-- The literal collapse is continuous for every closed subset of a Hausdorff space. -/
theorem continuous_collapse (hF : IsClosed F) : Continuous (collapse F) := by
  classical
  apply continuous_def.mpr
  intro s hs
  by_cases hinf : ∞ ∈ s
  · apply isClosed_compl_iff.mp
    rw [collapse_preimage_compl_of_mem F s hinf]
    exact (((OnePoint.isOpen_def.mp hs).1 hinf).image continuous_subtype_val).isClosed
  · rw [collapse_preimage_of_not_mem F s hinf]
    exact hF.isOpen_compl.isOpenMap_subtype_val _ (OnePoint.isOpen_def.mp hs).2

/-- The actual continuous collapse to the one-point compactification of the complement. -/
def collapseMap (hF : IsClosed F) : C(K, OnePoint ↥Fᶜ) :=
  ⟨collapse F, continuous_collapse F hF⟩

@[simp] theorem collapseMap_apply (hF : IsClosed F) (a : K) :
    collapseMap F hF a = collapse F a := rfl

/-- Compactness makes the actual continuous surjection a quotient map. -/
theorem isQuotientMap_collapse [CompactSpace K] (hF : IsClosed F) (hne : F.Nonempty) :
    IsQuotientMap (collapse F) := by
  let : LocallyCompactSpace ↥Fᶜ := hF.isOpen_compl.locallyCompactSpace
  exact IsQuotientMap.of_surjective_continuous
    (collapse_surjective F hne) (continuous_collapse F hF)

end Wikipedia.HopfProblem.SixSphereCube
