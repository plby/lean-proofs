import Wikipedia.NoExoticSixSphere.CompactPathPolygonReplacement
import Wikipedia.NoExoticSixSphere.OrthogonalUniformRefinement
import Wikipedia.NoExoticSixSphere.ComplexStructurePathFamilies
import Wikipedia.NoExoticSixSphere.OrthogonalPolygonFamilyHomotopy

/-!
# Relative minimum deformation for arbitrary continuous orthogonal path families

A coarse polygon replacement is chosen first, and compactness then bounds its
energy. After choosing a larger cap, energy-preserving refinement gives a mesh
with all geometric controls. The verified polygon minimum deformation can then
be applied and realized as a homotopy of the original path family.

The parameter manifold is compact and boundaryless, and its dimension plus two
is less than the orthogonal rank. Every parameter already following a minimum
exponential remains fixed. No regularity or energy bound on the original
continuous family is assumed.
-/

open Set Module
open scoped ContDiff Manifold Topology

namespace NoExoticSixSphere.OrthogonalPolygon

open GLOrthonormalization CayleyTransform OrthogonalExponential OrthogonalVertexSpace
  UniformTimePartition

variable {B H M : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
  [FiniteDimensional ℝ B] [TopologicalSpace H] {I : ModelWithCorners ℝ B H}
  [I.Boundaryless] [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [T2Space M] {n : ℕ}

include I

theorem exists_homotopy_to_minimum_path_family
    (a b : OrthogonalOperators n)
    (hanti : (a⁻¹ * b).1.1 = -(1 : Vector n →L[ℝ] Vector n))
    (hd : finrank ℝ B + 2 < n)
    (F : C(unitInterval × M, OrthogonalOperators n))
    (ha : ∀ x, F (0, x) = a) (hb : ∀ x, F (1, x) = b) :
    ∃ J : C(M, OrthogonalComplexStructures.Space n),
      Nonempty (F.HomotopyRel (complexStructurePathFamily a J)
        {z | z.1 = 0 ∨ z.1 = 1 ∨ z.2 ∈ minimumPathParameters F a}) := by
  obtain ⟨m, _, p, hp, E, _, hpE, ⟨G⟩⟩ :=
    exists_bounded_polygon_replacement_fixing_minima F a b ha hb 0
  let cap := max E ((n : ℝ) * Real.pi ^ 2) + 1
  have hcap : (n : ℝ) * Real.pi ^ 2 < cap := by
    dsimp only [cap]
    linarith [le_max_right E ((n : ℝ) * Real.pi ^ 2)]
  have hEcap : E < cap := by
    dsimp only [cap]
    linarith [le_max_left E ((n : ℝ) * Real.pi ^ 2)]
  obtain ⟨N, hN⟩ := exists_eventual_minimumPolygon_control n cap
  obtain ⟨k, hk, q, hq, hpath, henergy⟩ := exists_uniform_family_refinement a b p hp N
  obtain ⟨hlevels, _, hsmall⟩ := hN k hk
  obtain ⟨hcompact, hshort⟩ := hlevels a b cap le_rfl
  let S := minimumPathParameters F a
  let G₁ : F.HomotopyRel (realizedFamily a b (time k) q hq)
      {z | z.1 = 0 ∨ z.1 = 1 ∨ z.2 ∈ S} := G.cast rfl hpath.symm
  have hprotected (x : M) (hx : x ∈ S) : q x ∈ minimumSet a b (time k) := by
    obtain ⟨J, hJ⟩ := hx
    apply uniform_mem_minimumSet_of_path a b hanti hsmall (q x) (hq x) J
    intro u
    have he : F (u, x) = realizedFamily a b (time k) q hq (u, x) :=
      G₁.fst_eq_snd (Or.inr (Or.inr (show x ∈ S from ⟨J, hJ⟩)))
    exact he.symm.trans (hJ u)
  have hqE (x : M) : energy a b (time k) (q x) ≤ E := by
    rw [henergy x]
    exact hpE x
  obtain ⟨J, K, hK⟩ := exists_homotopy_to_complexStructure_family (I := I)
    a b (time k) (strictMono_time k) (time_zero k) (time_last k) hanti hsmall
    cap hcap hcompact hshort hd q hq E hEcap hqE
  have hJ (x : M) : complexStructureFamilyVertices a (time k) J x ∈ admissible a b k := by
    simpa only [K.apply_one] using (hK 1 x).1
  let Kfixed : q.HomotopyRel (complexStructureFamilyVertices a (time k) J) S :=
    { toHomotopy := K.toHomotopy
      prop' := fun r x hx ↦ K.eq_fst r (hprotected x hx) }
  let G₂ := realizedFamilyHomotopy a b (time k) (strictMono_time k) (time_zero k) (time_last k)
    q (complexStructureFamilyVertices a (time k) J) hq hJ S Kfixed
    (fun r x ↦ (hK r x).1)
  have hend := realizedFamily_complexStructure a b (time k) (strictMono_time k)
    (time_zero k) (time_last k) hanti hsmall J hJ
  exact ⟨J, ⟨G₁.trans (G₂.cast rfl hend)⟩⟩

end NoExoticSixSphere.OrthogonalPolygon
