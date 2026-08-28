import Wikipedia.NoExoticSixSphere.GeometricCapPairingComparison
import Wikipedia.NoExoticSixSphere.CompactMiddleHomologyFinite
import Wikipedia.NoExoticSixSphere.ArfInvariant
import Wikipedia.NoExoticSixSphere.SphereHomologyGroups

/-!
# The original geometric Arf invariant and its value on a candidate six-sphere

Actual middle-homology finiteness and proved geometric polar
nondegeneracy define the Arf invariant of the original geometric
quadratic form, with neither property assumed. The original middle
homology of a topological six-sphere is zero, so this actual invariant
vanishes. No framed nullbordism or filling is inferred from that value;
the dimension-six detection theorem still has to be proved.
-/

noncomputable section

open scoped Manifold ContDiff Topology
open Wikipedia.HopfProblem SphereHomologyCoefficients

namespace NoExoticSixSphere.GeometricArf

open GLOrthonormalization EuclideanEmbedding

attribute [local instance] modHomologyModule

variable {M : Type} [TopologicalSpace M] [T2Space M] [ChartedSpace (Vector 6) M]
  [IsManifold (𝓡 6) ∞ M] [CompactSpace M] [SimplyConnectedSpace M]
  (e : EuclideanEmbedding 6 M)
  (a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel)
  (r : TubularRetraction e) (m : M) [Subsingleton (π_ 2 M m)]

/-- Arf of the original geometric form, with actual finiteness and nondegeneracy supplied. -/
def invariant : ZMod 2 := by
  let : Finite (ModHomology 2 M 3) := compactManifold_modTwoMiddleHomology_finiteType (Vector 6) M m
  let : Fintype (ModHomology 2 M 3) := Fintype.ofFinite _
  exact Arf.invariant (e.modTwoHomologyQuadraticForm a r m)
    (e.modTwoHomologyQuadraticForm_nondegenerate a r m)

/-- Vanishing uses the actual native middle group, not a substituted zero-dimensional model. -/
theorem invariant_eq_zero_of_middle_subsingleton [Subsingleton (ModHomology 2 M 3)] :
    invariant e a r m = 0 := by
  let : Finite (ModHomology 2 M 3) := compactManifold_modTwoMiddleHomology_finiteType (Vector 6) M m
  let : Fintype (ModHomology 2 M 3) := Fintype.ofFinite _
  exact Arf.invariant_subsingleton (e.modTwoHomologyQuadraticForm a r m)
    (e.modTwoHomologyQuadraticForm_nondegenerate a r m)

/-- A candidate six-sphere has zero Arf invariant for its original geometric quadratic form. -/
theorem invariant_eq_zero_of_homeomorph_sixSphere (h : M ≃ₜ Sphere 6) :
    invariant e a r m = 0 := by
  let : Subsingleton (ModHomology 2 M 3) := sixSphere_middleModTwoHomology_subsingleton h
  exact invariant_eq_zero_of_middle_subsingleton e a r m

end NoExoticSixSphere.GeometricArf
