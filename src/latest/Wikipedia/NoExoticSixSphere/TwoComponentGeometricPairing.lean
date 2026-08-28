import Wikipedia.NoExoticSixSphere.OpenEmbeddingCapPairing
import Wikipedia.NoExoticSixSphere.GeometricCapPairingComparison

/-!
# The original geometric pairings on two disjoint open components

The actual global cap pairing of the target, evaluated on sums of the
two original inclusion images, is the sum of the original geometric
intersection pairings. This follows from the diagonal cap comparison,
the vanishing cross terms, and the previously proved framed geometric
comparison on each component. No connectedness of the target is assumed.
-/

noncomputable section

open Wikipedia.HopfProblem SphereHomologyCoefficients SingularMayerVietoris
open scoped Manifold ContDiff Topology

namespace NoExoticSixSphere.ZeroSecondHomologyCap

open GLOrthonormalization

attribute [local instance] modHomologyModule

variable {M N B : Type} [TopologicalSpace M] [TopologicalSpace N] [TopologicalSpace B]
  [T2Space M] [T2Space N] [T2Space B]
  [ChartedSpace (Vector 6) M] [ChartedSpace (Vector 6) N] [ChartedSpace (Vector 6) B]
  [IsManifold (𝓡 6) ∞ M] [IsManifold (𝓡 6) ∞ N]
  [CompactSpace M] [CompactSpace N] [CompactSpace B]
  [SimplyConnectedSpace M] [SimplyConnectedSpace N]
  (m : M) (n : N) [Subsingleton (π_ 2 M m)] [Subsingleton (π_ 2 N n)]
  [Subsingleton (SingularHomology B 2)]
  (eM : EuclideanEmbedding 6 M) (eN : EuclideanEmbedding 6 N)
  (νM : SmoothRangeFrame (𝓡 6) eM.normalProjection eM.NormalModel)
  (νN : SmoothRangeFrame (𝓡 6) eN.normalProjection eN.NormalModel)
  (rM : EuclideanEmbedding.TubularRetraction eM) (rN : EuclideanEmbedding.TubularRetraction eN)
  (i : C(M, B)) (j : C(N, B))
  (hi : Topology.IsOpenEmbedding i) (hj : Topology.IsOpenEmbedding j)
  (hd : Disjoint (Set.range i) (Set.range j))

include νM νN hi hj hd in
theorem pairing_sum_eq_geometric (a b : ModHomology 2 M 3) (c d : ModHomology 2 N 3) :
    letI : Fact (Module.finrank ℝ (Vector 6) = (3 + 2) + 1) := ⟨finrank_euclideanSpace_fin⟩
    pairing (E := Vector 6) B (modHomologyMap 2 i 3 a + modHomologyMap 2 j 3 c)
        (modHomologyMap 2 i 3 b + modHomologyMap 2 j 3 d) =
      eM.modTwoHomologyIntersection rM m a b + eN.modTwoHomologyIntersection rN n c d := by
  let : Fact (Module.finrank ℝ (Vector 6) = (3 + 2) + 1) := ⟨finrank_euclideanSpace_fin⟩
  let := TwoConnectedCoefficients.secondHomology_subsingleton m
  let := TwoConnectedCoefficients.secondHomology_subsingleton n
  simp only [map_add, LinearMap.add_apply]
  rw [pairing_openEmbedding i hi, pairing_disjoint_openEmbeddings i hi j hd,
    pairing_disjoint_openEmbeddings j hj i hd.symm, pairing_openEmbedding j hj,
    add_zero, zero_add, pairing_eq_connected M m, pairing_eq_connected N n]
  rw [eM.cap_pairing_eq_geometric νM rM m, eN.cap_pairing_eq_geometric νN rN n]

include hi hj hd in
theorem pairing_sum_eq_quadratic_polar (a b : ModHomology 2 M 3) (c d : ModHomology 2 N 3) :
    letI : Fact (Module.finrank ℝ (Vector 6) = (3 + 2) + 1) := ⟨finrank_euclideanSpace_fin⟩
    pairing (E := Vector 6) B (modHomologyMap 2 i 3 a + modHomologyMap 2 j 3 c)
        (modHomologyMap 2 i 3 b + modHomologyMap 2 j 3 d) =
      (eM.modTwoHomologyQuadraticForm νM rM m).polarBilin a b +
        (eN.modTwoHomologyQuadraticForm νN rN n).polarBilin c d := by
  let : Fact (Module.finrank ℝ (Vector 6) = (3 + 2) + 1) := ⟨finrank_euclideanSpace_fin⟩
  rw [eM.modTwoHomologyQuadraticForm_polar, eN.modTwoHomologyQuadraticForm_polar]
  exact pairing_sum_eq_geometric m n eM eN νM νN rM rN i j hi hj hd a b c d

end NoExoticSixSphere.ZeroSecondHomologyCap
