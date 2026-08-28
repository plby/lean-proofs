import Wikipedia.HopfProblem.OrbitPairSphereStationaryRealization
import Wikipedia.HopfProblem.OrbitPairSpherePolygonFamilyHomotopy
import Wikipedia.HopfProblem.OrbitPairSphereMinimumFamilies

/-!
# Actual path homotopies from polygon families to semicircle families

Realize the checked relative polygon deformation and identify its endpoint
with the literal trigonometric semicircle family. Path endpoints and all
parameters initially representing minimum polygons are fixed. Arbitrary
continuous path replacement and uniform refinement are not assumed here.
-/

noncomputable section

open Set Module
open scoped ContDiff Manifold Topology

namespace Wikipedia.HopfProblem.OrbitPair.SpherePolygonEnergy

open NoExoticSixSphere SphereVertexSpace SphereSemicircle

variable {M : Type*} [TopologicalSpace M] {n m : ℕ}

theorem realized_semicircleFamily_eq (a b : Sphere n) (τ : Fin (m + 2) → ℝ)
    (hτ : StrictMono τ) (hzero : τ 0 = 0) (hone : τ (Fin.last (m + 1)) = 1)
    (hanti : b.val = -a.val)
    (hmesh : ∀ i : Fin (m + 1), Real.pi ^ 2 * (τ i.succ - τ i.castSucc) < Real.pi ^ 2)
    (j : Fin m) (Y : C(M, Direction a))
    (hY : ∀ x, semicircleFamilyVertices a τ Y x ∈ admissible (costDomain n) a b m) :
    realizedFamily a b τ hτ (semicircleFamilyVertices a τ Y) hY = semicirclePathFamily a Y := by
  apply ContinuousMap.ext
  intro p
  apply Subtype.ext
  exact path_semicircleVertices a b τ hτ hzero hone hanti hmesh j (Y p.2) p.1.2

variable {B H : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
  [FiniteDimensional ℝ B] [TopologicalSpace H] {I : ModelWithCorners ℝ B H}
  [I.Boundaryless] [ChartedSpace H M] [IsManifold I ∞ M] [CompactSpace M] [T2Space M]

include I

theorem exists_realized_homotopy_to_semicircles (a b : Sphere n)
    (τ : Fin (m + 2) → ℝ) (hτ : StrictMono τ)
    (hzero : τ 0 = 0) (hone : τ (Fin.last (m + 1)) = 1)
    (hanti : b.val = -a.val) (cap : ℝ) (hcap : Real.pi ^ 2 < cap)
    (hmesh : ∀ i : Fin (m + 1), cap * (τ i.succ - τ i.castSucc) < Real.pi ^ 2)
    (j : Fin m) (hd : finrank ℝ B + 2 < 2 * n)
    (p : C(M, Space n m)) (hp : ∀ x, p x ∈ admissible (costDomain n) a b m)
    (start : ℝ) (hstart : start < cap) (hpstart : ∀ x, energy a b τ (p x) ≤ start) :
    ∃ Y : C(M, Direction a),
      Nonempty ((realizedFamily a b τ hτ p hp).HomotopyRel (semicirclePathFamily a Y)
        {z | z.1 = 0 ∨ z.1 = 1 ∨ p z.2 ∈ minimumSet a b τ}) := by
  obtain ⟨Y, G, hG⟩ := exists_homotopy_to_direction_family (I := I)
    a b τ hτ hzero hone hanti cap hcap hmesh j hd p start hstart hpstart
  have hminmesh := minimum_mesh_of_cap τ hτ cap hcap.le hmesh
  have hY : ∀ x, semicircleFamilyVertices a τ Y x ∈ admissible (costDomain n) a b m :=
    fun x => (semicircleVertices_mem_minimumSet a b τ hτ hzero hone hanti hminmesh (Y x)).1
  let J := realizedFamilyHomotopy a b τ hτ hzero hone p (semicircleFamilyVertices a τ Y)
    hp hY (p ⁻¹' minimumSet a b τ) G (fun t x => (hG t x).1)
  have hend := realized_semicircleFamily_eq a b τ hτ hzero hone hanti hminmesh j Y hY
  exact ⟨Y, ⟨J.cast rfl hend⟩⟩

end Wikipedia.HopfProblem.OrbitPair.SpherePolygonEnergy
