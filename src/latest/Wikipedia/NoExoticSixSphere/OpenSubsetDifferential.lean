import Mathlib.Geometry.Manifold.LocalDiffeomorph

/-!
# The smooth local inverse of an open-subset inclusion

The inherited atlas on an open subset makes its inclusion a local
diffeomorphism. In particular, restricting a domain to an open chart preimage
preserves regularity of a differential.
-/

open scoped Manifold ContDiff
open Set Topology TopologicalSpace

namespace NoExoticSixSphere

variable {B H M : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
  [TopologicalSpace H] {I : ModelWithCorners ℝ B H}
  [TopologicalSpace M] [ChartedSpace H M]

noncomputable def openSubsetPartialDiffeomorph (U : Opens M) (hU : Nonempty U) :
    PartialDiffeomorph I I U M ∞ where
  toPartialEquiv := (U.openPartialHomeomorphSubtypeCoe hU).toPartialEquiv
  open_source := (U.openPartialHomeomorphSubtypeCoe hU).open_source
  open_target := (U.openPartialHomeomorphSubtypeCoe hU).open_target
  contMDiffOn_toFun := contMDiff_subtype_val.contMDiffOn
  contMDiffOn_invFun := by
    let e := U.openPartialHomeomorphSubtypeCoe hU
    have h : ContMDiffOn I I ∞ (Subtype.val ∘ e.symm) e.target :=
      contMDiffOn_id.congr (fun y hy ↦ e.right_inv hy)
    intro y hy
    exact (ContMDiffWithinAt.subtypeVal_comp_iff U e.symm e.target y).mp (h y hy)

theorem isLocalDiffeomorphAt_openSubset_val (U : Opens M) (x : U) :
    IsLocalDiffeomorphAt I I ∞ (Subtype.val : U → M) x := by
  refine ⟨openSubsetPartialDiffeomorph (I := I) U ⟨x⟩, ?_, fun _ _ ↦ rfl⟩
  change x ∈ (U.openPartialHomeomorphSubtypeCoe ⟨x⟩).source
  rw [Opens.openPartialHomeomorphSubtypeCoe_source]
  trivial

theorem mfderiv_openSubset_val_bijective (U : Opens M) (x : U) :
    Function.Bijective (mfderiv I I (Subtype.val : U → M) x) :=
  ((isLocalDiffeomorphAt_openSubset_val (I := I) U x).mfderivToContinuousLinearEquiv
    (by simp)).bijective

end NoExoticSixSphere
