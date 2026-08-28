import Wikipedia.HopfProblem.DegreeCollapseTimeCollarInterior
import Wikipedia.NoExoticSixSphere.DiskBoundaryNullhomotopy

/-!
# Exact interior disk extensions from a collared half

A sphere already in the positive interior that extends over the closed
half also extends over the positive interior, with exactly the same boundary.
The actual collar supplies the inward homotopy, and disk homotopy extension
repairs the boundary after the push. No smoothness of the collar is used.
-/

noncomputable section

namespace NoExoticSixSphere

open Wikipedia.HopfProblem.DegreeCollapse
open DiskCylinder TimeCollar

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M B : Type} [TopologicalSpace M] [TopologicalSpace B] {t : M → ℝ}

theorem exists_interior_disk_extension (C : TimeCollar t B)
    (f : C(DiskCylinder.Sphere (E := E), C.positiveInterior))
    (F : C(Disk (E := E), NonnegativeHalf t))
    (hb : ∀ s, F (boundaryToDisk s) = C.interiorToHalf (f s)) :
    ∃ G : C(Disk (E := E), C.positiveInterior), ∀ s, G (boundaryToDisk s) = f s := by
  let H := C.interiorHalfSlide.symm.compContinuousMap f
  apply DiskBoundary.exists_extension_of_homotopic ⟨H⟩ (C.halfToInterior.comp F)
  intro s
  change C.halfToInterior (F (boundaryToDisk s)) =
    C.halfToInterior (C.interiorToHalf (f s))
  rw [hb]

end NoExoticSixSphere
