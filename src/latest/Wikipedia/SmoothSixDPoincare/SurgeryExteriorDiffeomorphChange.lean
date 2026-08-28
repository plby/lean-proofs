import Wikipedia.SmoothSixDPoincare.SurgeryBoundaryTransport
import Wikipedia.SmoothSixDPoincare.OpenSurgeryExterior
import Wikipedia.SmoothSixDPoincare.OpenDiffeomorphCongr

/-!
# A native boundary diffeomorphism retains the exact smooth surgery exterior

The changed new exterior is the actual image of the original one. The
restriction retains the original point map, and composition gives precisely
the common-exterior homeomorphism of the changed surgery presentation.
-/

noncomputable section

open Set Function Topology
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.SurgeryBoundaryPair

variable {N P R X Y Z : Type*} [NormedAddCommGroup N] [NormedAddCommGroup P]
  [TopologicalSpace R] [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
  (d : SurgeryBoundaryPair N P R X Y)
  {E F G H K L : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace K]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace L]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F K}
  {Q : ModelWithCorners ℝ G L} [ChartedSpace K Y] [ChartedSpace L Z]
  (e : Diffeomorph J Q Y Z ∞)

theorem image_newOpenExterior :
    e '' (d.newOpenExterior : Set Y) = (d.changeNewBoundary e.toHomeomorph).newOpenExterior := by
  ext z
  constructor
  · rintro ⟨y, hy, rfl⟩ ⟨p, hp⟩
    exact hy ⟨p, e.injective hp⟩
  · intro hz
    refine ⟨e.symm z, ?_, e.apply_symm_apply z⟩
    rintro ⟨p, hp⟩
    apply hz
    exact ⟨p, (congrArg e hp).trans (e.apply_symm_apply z)⟩

def newExteriorChange : Diffeomorph J Q d.newOpenExterior
    (d.changeNewBoundary e.toHomeomorph).newOpenExterior ∞ :=
  (OpenDiffeomorph.imageDiffeomorph e d.newOpenExterior).trans
    (OpenDiffeomorph.setCongr (OpenDiffeomorph.imageOpen e d.newOpenExterior)
      (d.changeNewBoundary e.toHomeomorph).newOpenExterior (d.image_newOpenExterior e))

theorem newExteriorChange_coe (y : d.newOpenExterior) :
    (d.newExteriorChange e y).val = e y.val := rfl

theorem newExteriorChange_symm_coe (z : (d.changeNewBoundary e.toHomeomorph).newOpenExterior) :
    ((d.newExteriorChange e).symm z).val = e.symm z.val := rfl

variable [ChartedSpace H X]
  (D : Diffeomorph I J d.oldOpenExterior d.newOpenExterior ∞)

def changeOpenExteriorDiffeomorph : Diffeomorph I Q
    (d.changeNewBoundary e.toHomeomorph).oldOpenExterior
    (d.changeNewBoundary e.toHomeomorph).newOpenExterior ∞ :=
  D.trans (d.newExteriorChange e)

theorem changeOpenExteriorDiffeomorph_toHomeomorph
    (hD : D.toHomeomorph = d.openExteriorHomeomorph) :
    (d.changeOpenExteriorDiffeomorph e D).toHomeomorph =
      (d.changeNewBoundary e.toHomeomorph).openExteriorHomeomorph := by
  ext x
  change e (D x).val = e (d.openExteriorHomeomorph x).val
  exact congrArg (fun h : d.oldOpenExterior ≃ₜ d.newOpenExterior => e (h x).val) hD

end Wikipedia.SmoothSixDPoincare.SurgeryBoundaryPair
