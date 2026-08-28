import Wikipedia.HopfProblem.DegreeCollapseDiskHomotopyExtension
import Wikipedia.HopfProblem.DegreeCollapseMappingPaths

/-!
# Transport of actual disk maps along boundary paths

The disk HEP lifts an entire path in the boundary mapping space, starting
at a prescribed disk map. The resulting path lies in the original disk
mapping space and agrees with the specified boundary path at every time.
-/

noncomputable section

open scoped unitInterval

namespace Wikipedia.HopfProblem.DegreeCollapse.BoundaryPathTransport

open DiskCylinder MappingPaths

variable {V Y : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] [TopologicalSpace Y]

/-- Exact path transport through restriction from the original disk to its full sphere boundary. -/
theorem exists_transport (f : C(Disk (E := V), Y))
    {a b : C(Sphere (E := V), Y)} (A : Path a b) (ha : f.comp boundaryToDisk = a) :
    ∃ g : C(Disk (E := V), Y), ∃ P : Path f g,
      Over (fun v : C(Disk (E := V), Y) => v.comp boundaryToDisk) P A ∧
      g.comp boundaryToDisk = b := by
  let H : C(I × Sphere (E := V), Y) := A.toContinuousMap.uncurry
  have h0 : ∀ s, H (0, s) = f (boundaryToDisk s) := by
    intro s
    exact (ContinuousMap.congr_fun A.source s).trans (ContinuousMap.congr_fun ha.symm s)
  let g := extensionEndpoint f H h0
  let P := ofHomotopy (extensionHomotopy f H h0)
  have hP : Over (fun v : C(Disk (E := V), Y) => v.comp boundaryToDisk) P A := by
    intro t
    apply ContinuousMap.ext
    intro s
    exact extend_side f H h0 t s
  refine ⟨g, P, hP, ?_⟩
  simpa using hP 1

end Wikipedia.HopfProblem.DegreeCollapse.BoundaryPathTransport
