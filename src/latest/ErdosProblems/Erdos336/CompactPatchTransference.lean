import Mathlib
import ErdosProblems.Erdos336.MasterTransference
import ErdosProblems.Erdos336.DenseExactPower

/- Ported from Lean 4.31.0 to 4.33.0; imports, helper namespaces, and elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Compact power plus a piecewise patch implies eventual exact coverage
-/

namespace Erdos336

open PiecewiseBohrTransfer
open scoped Pointwise

/-- Complete elementary/topological transference after the two deep inputs
have been supplied: a piecewise patch in `2hD` and a full compact `M`-fold
power of the closed image. -/
theorem eventuallyExactlyZ_of_compact_power_and_patch
    {K : Type*} [TopologicalSpace K] [AddCommGroup K]
    [IsTopologicalAddGroup K] [CompactSpace K]
    (φ : ℤ →+ K)
    {U : Set K} {T P D : Set ℤ} {c : ℤ} {h M : ℕ}
    (hUopen : IsOpen U) (hUne : U.Nonempty)
    (hzero : 0 ∈ D)
    (hparent : EventuallyWithOneExtra D c h)
    (hT : ThickZ T)
    (hpatch : ∀ n : ℤ, φ n ∈ U → n ∈ T → n ∈ P)
    (hPrep : ∀ p ∈ P, ZRepExactly D (2 * h) p)
    (hpower : M • closure (φ '' D) = (Set.univ : Set K)) :
    EventuallyExactlyZ D (M + 3 * h) := by
  obtain ⟨S, hSrep, hcover⟩ :=
    finite_patch_cover_of_closed_power φ hUopen hUne hpower
  exact eventuallyExactlyZ_of_piecewise_patch hzero hparent hT hpatch
    hcover hPrep hSrep

end Erdos336
