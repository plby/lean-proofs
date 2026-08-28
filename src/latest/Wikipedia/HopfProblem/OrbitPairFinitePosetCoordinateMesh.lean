import Wikipedia.HopfProblem.OrbitPairFinitePosetIterationMesh

/-!
# Shrinking native simplices in a faithful coordinate embedding

The vertex assignment is now fixed to the standard coordinate vectors.
It gives a closed embedding of the initial native realization, not an
arbitrary possibly constant affine map. The mesh estimate therefore
controls the actual subdivided space in these faithful coordinates.
-/

noncomputable section

universe u

open CategoryTheory Simplicial PartialOrder Topology
open scoped BigOperators

namespace Wikipedia.HopfProblem.OrbitPair.FinitePoset

open FirstHurewicz RealizationSimplex Subdivision

def coordinateVertex (P : Type u) (p : P) : P → ℝ := by
  classical
  exact Pi.single p 1

theorem affineValue_coordinateVertex (P : Type u) [Fintype P] (t : stdSimplex ℝ P) :
    affineValue (coordinateVertex P) t = t.val := by
  classical
  funext p
  simp [affineValue, coordinateVertex, Finset.sum_apply, Pi.single_apply]
  rfl

theorem coordinateVertex_dist_le (P : Type u) [Fintype P] (p q : P) :
    dist (coordinateVertex P p) (coordinateVertex P q) ≤ 1 := by
  classical
  apply (dist_pi_le_iff (by norm_num : (0 : ℝ) ≤ 1)).mpr
  intro i
  simp only [coordinateVertex, Pi.single_apply]
  split_ifs <;> norm_num

def coordinateMap (P : PartOrd.{u}) [Finite P] :
    C(SSet.toTop.obj (nerve P), P → ℝ) := by
  letI : Fintype P := Fintype.ofFinite P
  exact ⟨fun z ↦ (coordinates P z).val, continuous_subtype_val.comp (coordinates P).continuous⟩

theorem coordinateMap_isClosedEmbedding (P : PartOrd.{u}) [Finite P] :
    IsClosedEmbedding (coordinateMap P) := by
  letI : Fintype P := Fintype.ofFinite P
  apply (coordinateMap P).continuous.isClosedEmbedding
  intro z w h
  exact coordinates_injective P (Subtype.ext h)

def iteratedCoordinateMap (P : PartOrd.{u}) [Finite P] (r : ℕ) :
    C(SSet.toTop.obj (nerve ((iteratedChains r).obj P)), P → ℝ) := by
  letI : Fintype P := Fintype.ofFinite P
  exact (coordinateMap P).comp
    ⟨iterationHomeomorph P r, (iterationHomeomorph P r).continuous⟩

theorem iteratedCoordinateMap_apply (P : PartOrd.{u}) [Fintype P] (r : ℕ)
    (z : SSet.toTop.obj (nerve ((iteratedChains r).obj P))) :
    iteratedCoordinateMap P r z = coordinateMap P (iterationHomeomorph P r z) := rfl

theorem iterationAffineMap_coordinateVertex (P : PartOrd.{u}) [Fintype P] (r : ℕ)
    (z : SSet.toTop.obj (nerve ((iteratedChains r).obj P))) :
    iterationAffineMap P (coordinateVertex P) r z = iteratedCoordinateMap P r z := by
  letI : Fintype P := Fintype.ofFinite P
  exact affineValue_coordinateVertex P (coordinates P (iterationHomeomorph P r z))

theorem iteratedCoordinateMap_isClosedEmbedding (P : PartOrd.{u}) [Finite P] (r : ℕ) :
    IsClosedEmbedding (iteratedCoordinateMap P r) := by
  letI : Fintype P := Fintype.ofFinite P
  exact (coordinateMap_isClosedEmbedding P).comp (iterationHomeomorph P r).isClosedEmbedding

theorem iteratedCoordinateMap_mesh (P : PartOrd.{u}) [Fintype P] (r k : ℕ)
    (x : (nerve ((iteratedChains r).obj P)) _⦋k⦌) (t s : Simplex k) :
    dist (iteratedCoordinateMap P r
      (characteristic (nerve ((iteratedChains r).obj P)) k x t))
      (iteratedCoordinateMap P r
        (characteristic (nerve ((iteratedChains r).obj P)) k x s)) ≤
          ((Fintype.card P : ℝ) / (Fintype.card P + 1)) ^ r := by
  have h := iterationAffineMap_mesh P (coordinateVertex P) (Fintype.card P)
    (chainCardBound_finite P) 1 (by norm_num) (coordinateVertex_dist_le P) r k x t s
  have he := congrArg₂ dist (iterationAffineMap_coordinateVertex P r
    (characteristic (nerve ((iteratedChains r).obj P)) k x t))
    (iterationAffineMap_coordinateVertex P r
      (characteristic (nerve ((iteratedChains r).obj P)) k x s))
  exact he.symm.le.trans (by simpa only [mul_one] using h)

theorem exists_iteratedCoordinateMap_mesh_lt (P : PartOrd.{u}) [Fintype P]
    (ε : ℝ) (hε : 0 < ε) :
    ∃ R : ℕ, ∀ r ≥ R, ∀ k : ℕ, ∀ x : (nerve ((iteratedChains r).obj P)) _⦋k⦌,
      ∀ t s : Simplex k,
        dist (iteratedCoordinateMap P r
          (characteristic (nerve ((iteratedChains r).obj P)) k x t))
          (iteratedCoordinateMap P r
            (characteristic (nerve ((iteratedChains r).obj P)) k x s)) < ε := by
  obtain ⟨R, hR⟩ := exists_iterationAffineMap_mesh_lt P (coordinateVertex P) (Fintype.card P)
    (chainCardBound_finite P) 1 (by norm_num) (coordinateVertex_dist_le P) ε hε
  refine ⟨R, fun r hr k x t s ↦ ?_⟩
  have he := congrArg₂ dist (iterationAffineMap_coordinateVertex P r
    (characteristic (nerve ((iteratedChains r).obj P)) k x t))
    (iterationAffineMap_coordinateVertex P r
      (characteristic (nerve ((iteratedChains r).obj P)) k x s))
  exact he.symm.trans_lt (hR r hr k x t s)

end Wikipedia.HopfProblem.OrbitPair.FinitePoset
