import Wikipedia.NoExoticSixSphere.OpenSubsetDifferential

/-! # Restrict the target of a local diffeomorphism to an actual open subset -/

noncomputable section

open Set TopologicalSpace
open scoped Manifold ContDiff

namespace NoExoticSixSphere

variable {B H M C K N : Type*}
  [NormedAddCommGroup B] [NormedSpace ℝ B] [TopologicalSpace H]
  {I : ModelWithCorners ℝ B H} [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup C] [NormedSpace ℝ C] [TopologicalSpace K]
  {J : ModelWithCorners ℝ C K} [TopologicalSpace N] [ChartedSpace K N]
  {f : M → N} {x : M} (U : Opens N) (hU : ∀ y, f y ∈ U)

theorem isLocalDiffeomorphAt_codRestrict (hf : IsLocalDiffeomorphAt I J ∞ f x) :
    IsLocalDiffeomorphAt I J ∞ (fun y ↦ (⟨f y, hU y⟩ : U)) x := by
  obtain ⟨φ, hx, he⟩ := hf
  let q := openSubsetPartialDiffeomorph (I := J) U ⟨⟨f x, hU x⟩⟩
  have htarget : q.target = (U : Set N) :=
    Opens.openPartialHomeomorphSubtypeCoe_target U ⟨⟨f x, hU x⟩⟩
  refine ⟨φ.trans q.symm, ⟨hx, ?_⟩, ?_⟩
  · change φ x ∈ q.target
    rw [htarget, ← he hx]
    exact hU x
  · intro y hy
    apply Subtype.ext
    exact (he hy.1).trans (q.right_inv hy.2).symm

end NoExoticSixSphere
