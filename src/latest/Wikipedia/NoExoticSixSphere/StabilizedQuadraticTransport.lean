import Wikipedia.NoExoticSixSphere.StabilizedSphereParity
import Wikipedia.NoExoticSixSphere.GeometricArfInvariant

/-!
# Quadratic and Arf transport through the actual stabilized framed diffeomorphism

The equivalence is the homology map induced by the given native
diffeomorphism, with its existing additive equivalence viewed over
`ZMod 2`. Actual embedded sphere representatives and their original
parities prove that this equivalence is a quadratic isometry. Genuine
middle-homology finiteness and polar nondegeneracy give Arf invariance.
This is not a framed-bordism detection theorem.
-/

noncomputable section

open Function
open scoped Manifold ContDiff Topology
open Wikipedia.HopfProblem SphereHomologyCoefficients

namespace NoExoticSixSphere.StabilizedFramedDiffeomorph

open GLOrthonormalization EuclideanEmbedding

attribute [local instance] modHomologyModule

variable {M M' : Type} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  [TopologicalSpace M'] [ChartedSpace (Vector 6) M']
  {e : EuclideanEmbedding 6 M} {e' : EuclideanEmbedding 6 M'}
  {a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel}
  {a' : SmoothRangeFrame (𝓡 6) e'.normalProjection e'.NormalModel}
  (F : StabilizedFramedDiffeomorph e a e' a')

def middleModTwoEquiv : ModHomology 2 M 3 ≃ₗ[ZMod 2] ModHomology 2 M' 3 :=
  { (modHomologyHomeomorphEquiv 2 F.diffeomorph.toHomeomorph 3).toAddEquiv with
    map_smul' := ZMod.map_smul (modHomologyHomeomorphEquiv 2 F.diffeomorph.toHomeomorph 3) }

theorem middleModTwoEquiv_apply (b : ModHomology 2 M 3) :
    F.middleModTwoEquiv b =
      modHomologyMap 2 (F.diffeomorph.toHomeomorph : C(M, M')) 3 b := rfl

theorem middleModTwoEquiv_sphereClass (f : C(Sphere 3, M)) :
    F.middleModTwoEquiv (SixSphereMiddleParity.sphereClass f) =
      SixSphereMiddleParity.sphereClass ((F.diffeomorph.toHomeomorph : C(M, M')).comp f) := by
  rw [middleModTwoEquiv_apply, SixSphereMiddleParity.sphereClass,
    SixSphereMiddleParity.sphereClass, modHomologyMap_comp]
  rfl

variable [IsManifold (𝓡 6) ∞ M] [T2Space M] [CompactSpace M] [SimplyConnectedSpace M]
  [IsManifold (𝓡 6) ∞ M'] [T2Space M'] [CompactSpace M'] [SimplyConnectedSpace M']
  (r : TubularRetraction e) (r' : TubularRetraction e') (m : M) (m' : M')
  [Subsingleton (π_ 2 M m)] [Subsingleton (π_ 2 M' m')]

theorem quadraticForm_map (b : ModHomology 2 M 3) :
    e'.modTwoHomologyQuadraticForm a' r' m' (F.middleModTwoEquiv b) =
      e.modTwoHomologyQuadraticForm a r m b := by
  obtain ⟨f, hf, hi, hd, rfl⟩ := e.exists_embedded_modTwoMiddle_representative r m b
  rw [middleModTwoEquiv_sphereClass, e'.modTwoHomologyQuadraticForm_sphereClass,
    e.modTwoHomologyQuadraticForm_sphereClass]
  have hs := F.sphere_comp_smooth f hf
  have hd' := F.sphere_comp_mfderiv_injective f hf hd
  have hi' := F.sphere_comp_injective f hi.injective
  rw [e'.geometricSphereParity_eq_of_embedding a' r' _ hs hi' hd',
    e.geometricSphereParity_eq_of_embedding a r f hf hi.injective hd]
  exact F.sphereParity_comp f hf hd hi.injective

def quadraticFormIsometry :
    (e.modTwoHomologyQuadraticForm a r m).IsometryEquiv
      (e'.modTwoHomologyQuadraticForm a' r' m') where
  toLinearEquiv := F.middleModTwoEquiv
  map_app' := F.quadraticForm_map r r' m m'

include F in
theorem geometricArf_eq :
    GeometricArf.invariant e a r m = GeometricArf.invariant e' a' r' m' := by
  let : Finite (ModHomology 2 M 3) :=
    compactManifold_modTwoMiddleHomology_finiteType (Vector 6) M m
  let : Fintype (ModHomology 2 M 3) := Fintype.ofFinite _
  let : Finite (ModHomology 2 M' 3) :=
    compactManifold_modTwoMiddleHomology_finiteType (Vector 6) M' m'
  let : Fintype (ModHomology 2 M' 3) := Fintype.ofFinite _
  exact Arf.invariant_isometry (e.modTwoHomologyQuadraticForm a r m)
    (e'.modTwoHomologyQuadraticForm a' r' m')
    (e.modTwoHomologyQuadraticForm_nondegenerate a r m)
    (e'.modTwoHomologyQuadraticForm_nondegenerate a' r' m')
    (F.quadraticFormIsometry r r' m m')

end NoExoticSixSphere.StabilizedFramedDiffeomorph
