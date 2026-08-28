import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicComplexStructureCompactPathReplacement
import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicComplexStructureUniformRefinement
import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicSecondRotationPathFamilies
import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicComplexStructurePolygonFamilyHomotopy

/-!
# Relative minimum deformation for continuous complex-structure path families

Replace by coarse polygons before bounding energy, then refine without
changing the path or energy. The controlled polygon deformation reaches
the original rotation family and fixes every parameter already following
a minimum rotation. No regularity of the initial continuous paths is assumed.
-/

open Set Module
open scoped ContDiff Manifold Topology

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns.ComplexStructurePolygon

open ComplexStructures ComplexStructureVertices NoExoticSixSphere.GLOrthonormalization
open NoExoticSixSphere.UniformTimePartition

variable {B H M : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
  [FiniteDimensional ℝ B] [TopologicalSpace H] {I : ModelWithCorners ℝ B H}
  [I.Boundaryless] [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [T2Space M] {n : ℕ}

include I

theorem exists_homotopy_to_minimum_path_family (a b : ComplexStructures.Space n)
    (hanti : (Cayley.relative a b).val.val.val =
      -(1 : Vector (4 * n + 4) →L[ℝ] Vector (4 * n + 4)))
    (hd : finrank ℝ B < n) (F : C(unitInterval × M, ComplexStructures.Space n))
    (ha : ∀ x, F (0, x) = a) (hb : ∀ x, F (1, x) = b) :
    ∃ P : C(M, AnticommutingStructures.Space a),
      Nonempty (F.HomotopyRel (rotationPathFamily P)
        {z | z.1 = 0 ∨ z.1 = 1 ∨ z.2 ∈ minimumPathParameters F a}) := by
  obtain ⟨m, _, p, hp, E, _, hpE, ⟨G⟩⟩ :=
    exists_bounded_polygon_replacement_fixing_minima F a b ha hb 0
  let cap := max E (((4 * n + 4 : ℕ) : ℝ) * Real.pi ^ 2) + 1
  have hcap : ((4 * n + 4 : ℕ) : ℝ) * Real.pi ^ 2 < cap := by
    dsimp only [cap]
    linarith [le_max_right E (((4 * n + 4 : ℕ) : ℝ) * Real.pi ^ 2)]
  have hEcap : E < cap := by
    dsimp only [cap]
    linarith [le_max_left E (((4 * n + 4 : ℕ) : ℝ) * Real.pi ^ 2)]
  obtain ⟨N, hN⟩ := exists_eventual_minimum_partition n cap
  obtain ⟨k, hk, q, hq, hpath, henergy⟩ := exists_uniform_family_refinement a b p hp N
  obtain ⟨hlevels, hsmall⟩ := hN k hk
  have hcompact := hlevels a b cap le_rfl
  let S := minimumPathParameters F a
  let G₁ : F.HomotopyRel (realizedFamily a b (time k) (strictMono_time k) q hq)
      {z | z.1 = 0 ∨ z.1 = 1 ∨ z.2 ∈ S} := G.cast rfl hpath.symm
  have hprotected (x : M) (hx : x ∈ S) : q x ∈ minimumSet a b (time k) := by
    obtain ⟨P, hP⟩ := hx
    apply uniform_mem_minimumSet_of_path a b hanti (hsmall a) (q x) (hq x) P
    intro u
    have he : F (u, x) = realizedFamily a b (time k) (strictMono_time k) q hq (u, x) :=
      G₁.fst_eq_snd (Or.inr (Or.inr (show x ∈ S from ⟨P, hP⟩)))
    exact he.symm.trans (hP u)
  have hqE (x : M) : energy a b (time k) (q x) ≤ E := by
    rw [henergy x]
    exact hpE x
  obtain ⟨P, K, hK⟩ := exists_homotopy_to_rotation_family (I := I)
    a b (time k) (strictMono_time k) (time_zero k) (time_last k) hanti (hsmall a)
    cap hcap hcompact hd q hq E hEcap hqE
  have hP (x : M) : rotationFamilyVertices (time k) P x ∈ admissible a b k := by
    simpa only [K.apply_one] using (hK 1 x).1
  let Kfixed : q.HomotopyRel (rotationFamilyVertices (time k) P) S :=
    { toHomotopy := K.toHomotopy
      prop' := fun r x hx ↦ K.eq_fst r (hprotected x hx) }
  let G₂ := realizedFamilyHomotopy a b (time k) (strictMono_time k) (time_zero k) (time_last k)
    q (rotationFamilyVertices (time k) P) hq hP S Kfixed (fun r x ↦ (hK r x).1)
  have hend := realizedFamily_rotation a b (time k) (strictMono_time k)
    (time_zero k) (time_last k) hanti (hsmall a) P hP
  exact ⟨P, ⟨G₁.trans (G₂.cast rfl hend)⟩⟩

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns.ComplexStructurePolygon
