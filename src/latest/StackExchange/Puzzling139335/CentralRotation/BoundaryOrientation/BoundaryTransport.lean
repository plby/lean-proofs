import Mathlib.Topology.Instances.AddCircle.Real
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Separation.Hausdorff

/-!
# Transport of boundary parameters

An ambient homeomorphism taking the image of one embedded parameter circle
onto another induces a homeomorphism of the parameter circles themselves.
This construction does not assume any orientation for that homeomorphism.
-/

open Set

namespace Puzzling139335.CentralRotation.BoundaryOrientation

/-- Transport the parameters of two embedded circles along an ambient
homeomorphism that maps the first circle's image onto the second's. -/
theorem exists_boundary_transport
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y]
    (fA : AddCircle (1 : ℝ) → X) (fB : AddCircle (1 : ℝ) → Y)
    (hfA : Continuous fA) (hiA : Function.Injective fA)
    (hfB : Continuous fB) (hiB : Function.Injective fB)
    (g : X ≃ₜ Y) (hset : g '' range fA = range fB) :
    ∃ e : AddCircle (1 : ℝ) ≃ₜ AddCircle (1 : ℝ),
      ∀ t, fB (e t) = g (fA t) := by
  let eA : AddCircle (1 : ℝ) ≃ₜ range (g ∘ fA) :=
    ((g.continuous.comp hfA).isClosedEmbedding
      (g.injective.comp hiA)).isEmbedding.toHomeomorph
  let eB : AddCircle (1 : ℝ) ≃ₜ range fB :=
    (hfB.isClosedEmbedding hiB).isEmbedding.toHomeomorph
  have hrange : range (g ∘ fA) = range fB := by
    rw [range_comp, hset]
  let e : AddCircle (1 : ℝ) ≃ₜ AddCircle (1 : ℝ) :=
    eA.trans ((Homeomorph.setCongr hrange).trans eB.symm)
  refine ⟨e, fun t => ?_⟩
  have he : eB (e t) = Homeomorph.setCongr hrange (eA t) := by
    simp only [e, Homeomorph.trans_apply, Homeomorph.apply_symm_apply]
  exact congrArg Subtype.val he

end Puzzling139335.CentralRotation.BoundaryOrientation
