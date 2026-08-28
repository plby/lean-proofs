import Mathlib.Geometry.Manifold.ContMDiff.Basic
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions

/-!
# The native derivative of an open-submanifold inclusion

A local smooth inverse is constructed from the actual open subset. The chain
rule gives injectivity of the inclusion's native derivative, so an immersion
into the open complement remains an immersion into the original manifold.
-/

noncomputable section

open Set Function Filter Topology TopologicalSpace
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.NativeOpenSubmanifold

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M]

/-- The native tangent map of the inclusion of an actual open submanifold is injective. -/
theorem injective_mfderiv_subtype_val (U : Opens M) (p : U) :
    Injective (mfderiv I I (Subtype.val : U → M) p) := by
  classical
  let g : M → U := fun x => if hx : x ∈ U then ⟨x, hx⟩ else p
  have hval : (Subtype.val ∘ g) =ᶠ[𝓝 (p : M)] id := by
    apply mem_of_superset (U.isOpen.mem_nhds p.property)
    intro x hx
    change x ∈ U at hx
    change (g x : M) = x
    dsimp [g]
    rw [dif_pos hx]
  have hg : ContMDiffAt I I ∞ g (p : M) := by
    apply (ContMDiffAt.subtypeVal_comp_iff U g (p : M)).mp
    exact contMDiffAt_id.congr_of_eventuallyEq hval
  have hv : ContMDiff I I ∞ (Subtype.val : U → M) := contMDiff_subtype_val
  have hleft : g ∘ (Subtype.val : U → M) = id := by
    funext x
    apply Subtype.ext
    simp only [Function.comp_apply, g, dif_pos x.property, id_eq]
  have heq := mfderiv_comp p (hg.mdifferentiableAt (by simp))
    (hv.mdifferentiableAt (by simp))
  rw [hleft, mfderiv_id] at heq
  intro v w hvw
  have hh := congrArg (mfderiv I I g (p : M)) hvw
  have hv' := congrArg (fun L => L v) heq
  have hw' := congrArg (fun L => L w) heq
  exact hv'.trans (hh.trans hw'.symm)

end Wikipedia.SmoothSixDPoincare.NativeOpenSubmanifold
