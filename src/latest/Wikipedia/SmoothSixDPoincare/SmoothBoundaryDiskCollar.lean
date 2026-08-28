import Wikipedia.SmoothSixDPoincare.RadialDiskInwardCollar
import Wikipedia.SmoothSixDPoincare.SmoothBoundaryDisk
import Wikipedia.SmoothSixDPoincare.NativeInwardBoundaryCollar

/-! # Exact disk coordinates construct a collar for every disk birth -/

noncomputable section

open Set Function Topology ContinuousMap
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.SmoothBoundaryDisk

variable {G H : Type} [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace H]
  {J : ModelWithCorners ℝ G H} {N : Type} [NormedAddCommGroup N] [NormedSpace ℝ N]
  [FiniteDimensional ℝ N] (D : SmoothBoundaryDisk J N)

def inwardCollar : InwardBoundaryCollar D.space.inclusion :=
  RadialDiskInwardCollar.collar.transport D.boundaryCoordinates.symm D.bodyCoordinates.symm (by
    intro u
    apply D.bodyCoordinates.injective
    have h : D.bodyCoordinates (D.space.inclusion (D.boundaryCoordinates.symm u)) =
        OuterDisk.sphereDisk u :=
      (D.inclusion_coordinates (D.boundaryCoordinates.symm u)).trans
        (congrArg OuterDisk.sphereDisk (D.boundaryCoordinates.apply_symm_apply u))
    exact (D.bodyCoordinates.apply_symm_apply _).trans h.symm)

theorem hasInwardCollar : D.space.HasInwardCollar := ⟨D.inwardCollar⟩

end Wikipedia.SmoothSixDPoincare.SmoothBoundaryDisk
