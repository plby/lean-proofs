import Wikipedia.NoExoticSixSphere.FatWedgeCofibration
import Wikipedia.HopfProblem.OrbitPairIntervalBoundaryDeformation

/-!
# Neighborhood deformation data for the boundary of a finite cube

Split off the leading interval and use the actual two-endpoint data.
The union of its endpoint faces and the remaining cube's boundary is
exactly the original finite-cube boundary. The product construction
fixes that entire union pointwise and supplies its homotopy extension.
-/

noncomputable section

open Set
open scoped Topology unitInterval
open Wikipedia.HopfProblem.OrbitPair

namespace NoExoticSixSphere.CubeBoundaryCofibration

theorem boundary_zero : Cube.boundary (Fin 0) = ∅ := by
  ext u
  simp only [Cube.boundary, Set.mem_ofPred_eq, IsEmpty.exists_iff, Set.mem_empty_iff_false]

theorem split_mem (k : ℕ) (p : I × (Fin k → I)) :
    p ∈ NeighborhoodProduct.boundary IntervalBoundary.inclusion
      (SubspaceCofibration.inclusion (Cube.boundary (Fin k))) ↔
        (FatWedge.split k).symm p ∈ Cube.boundary (Fin (k + 1)) := by
  change (p.1 ∈ Set.range IntervalBoundary.inclusion ∨
    p.2 ∈ Set.range (SubspaceCofibration.inclusion (Cube.boundary (Fin k)))) ↔ _
  change (p.1 ∈ Set.range (SubspaceCofibration.inclusion IntervalBoundary.endpoints) ∨
    p.2 ∈ Set.range (SubspaceCofibration.inclusion (Cube.boundary (Fin k)))) ↔ _
  rw [SubspaceCofibration.mem_range, SubspaceCofibration.mem_range]
  change ((p.1 = 0 ∨ p.1 = 1) ∨ ∃ i, p.2 i = 0 ∨ p.2 i = 1) ↔
    ∃ i, (Fin.cons p.1 p.2 : Fin (k + 1) → I) i = 0 ∨
      (Fin.cons p.1 p.2 : Fin (k + 1) → I) i = 1
  simp only [Fin.exists_fin_succ, Fin.cons_zero, Fin.cons_succ]

def data : (k : ℕ) →
    NeighborhoodDeformation.Data (SubspaceCofibration.inclusion (Cube.boundary (Fin k)))
  | 0 => by
      rw [boundary_zero]
      exact SubspaceCofibration.emptyData
  | k + 1 =>
      SubspaceCofibration.transport (FatWedge.split k).symm (split_mem k)
        (NeighborhoodProduct.data IntervalBoundary.data (data k))

theorem hasHomotopyExtension (k : ℕ) :
    HomotopyExtension.HasHomotopyExtension
      (SubspaceCofibration.inclusion (Cube.boundary (Fin k))) :=
  SubspaceCofibration.hasHomotopyExtension (data k)

end NoExoticSixSphere.CubeBoundaryCofibration
