import Wikipedia.HomotopyGroupsOfSpheres.SymmetricUnitaryCompactPathReplacement
import Wikipedia.HomotopyGroupsOfSpheres.SymmetricUnitaryUniformRefinement
import Wikipedia.HomotopyGroupsOfSpheres.BalancedRotationPathFamilies
import Wikipedia.HomotopyGroupsOfSpheres.BalancedEventualMinimumPartition
import Wikipedia.HomotopyGroupsOfSpheres.SymmetricUnitaryPolygonFamilyHomotopy

/-!
# Relative minimum deformation for arbitrary constrained path families

First replace the continuous paths by polygons, then bound their energy.
Exact refinement supplies the mesh needed for controlled minimum deformation.
The resulting homotopy fixes both endpoints and every original minimum path.
No smoothness or energy bound on the original paths is assumed.
-/

open Set Module
open scoped Matrix.Norms.Frobenius ContDiff Manifold Topology

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicSymmetricMatrices.Polygon

open VertexSpace BalancedRealInvolutions NoExoticSixSphere.UniformTimePartition

variable {B H M : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
  [FiniteDimensional ℝ B] [TopologicalSpace H] {I : ModelWithCorners ℝ B H}
  [I.Boundaryless] [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [T2Space M]

include I

theorem exists_homotopy_to_minimum_path_family (n : ℕ) (hd : finrank ℝ B < n)
    (F : C(unitInterval × M, SpecialSpace (Index n)))
    (ha : ∀ x, F (0, x) = specialIdentity) (hb : ∀ x, F (1, x) = antipode n) :
    ∃ P : C(M, BalancedRealInvolutions.Space n),
      Nonempty (F.HomotopyRel (rotationPathFamily P)
        {z | z.1 = 0 ∨ z.1 = 1 ∨ z.2 ∈ minimumPathParameters F}) := by
  obtain ⟨m, _, p, hp, E, _, hpE, ⟨G⟩⟩ :=
    exists_bounded_polygon_replacement_fixing_minima n F ha hb 0
  let cap := max E ((4 * n : ℝ) * Real.pi ^ 2) + 1
  have hcap : (4 * n : ℝ) * Real.pi ^ 2 < cap := by
    dsimp only [cap]
    linarith [le_max_right E ((4 * n : ℝ) * Real.pi ^ 2)]
  have hEcap : E < cap := by
    dsimp only [cap]
    linarith [le_max_left E ((4 * n : ℝ) * Real.pi ^ 2)]
  obtain ⟨lower, hlower⟩ := exists_eventual_minimum_partition n cap
  obtain ⟨k, hk, q, hq, hpath, henergy⟩ :=
    exists_uniform_family_refinement specialIdentity (antipode n) p hp lower
  obtain ⟨hsmall, hlevels⟩ := hlower k hk
  have hcompact := hlevels cap (le_max_left _ _)
  let S := minimumPathParameters F
  let G₁ : F.HomotopyRel
      (realizedFamily specialIdentity (antipode n) (time k) (strictMono_time k) q hq)
      {z | z.1 = 0 ∨ z.1 = 1 ∨ z.2 ∈ S} := G.cast rfl hpath.symm
  have hprotected (x : M) (hx : x ∈ S) : q x ∈ minimumSet n (time k) := by
    obtain ⟨P, hP⟩ := hx
    apply uniform_mem_minimumSet_of_path n hsmall (q x) (hq x) P
    intro u
    have he : F (u, x) =
        realizedFamily specialIdentity (antipode n) (time k) (strictMono_time k) q hq (u, x) :=
      G₁.fst_eq_snd (Or.inr (Or.inr (show x ∈ S from ⟨P, hP⟩)))
    exact he.symm.trans (hP u)
  have hqE (x : M) : energy specialIdentity (antipode n) (time k) (q x) ≤ E := by
    rw [henergy x]
    exact hpE x
  obtain ⟨P, K, hK⟩ := exists_homotopy_to_rotation_family (I := I)
    n (time k) (strictMono_time k) (time_zero k) (time_last k) hsmall
    cap hcap hcompact hd q hq E hEcap hqE
  have hP (x : M) : rotationFamilyVertices (time k) P x ∈
      admissible specialIdentity (antipode n) k := by
    simpa only [K.apply_one] using (hK 1 x).1
  let Kfixed : q.HomotopyRel (rotationFamilyVertices (time k) P) S :=
    { toHomotopy := K.toHomotopy
      prop' := fun r x hx ↦ K.eq_fst r (hprotected x hx) }
  let G₂ := realizedFamilyHomotopy specialIdentity (antipode n) (time k)
    (strictMono_time k) (time_zero k) (time_last k)
    q (rotationFamilyVertices (time k) P) hq hP S Kfixed (fun r x ↦ (hK r x).1)
  have hend := realizedFamily_rotation n (time k) (strictMono_time k)
    (time_zero k) (time_last k) hsmall P hP
  exact ⟨P, ⟨G₁.trans (G₂.cast rfl hend)⟩⟩

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicSymmetricMatrices.Polygon
