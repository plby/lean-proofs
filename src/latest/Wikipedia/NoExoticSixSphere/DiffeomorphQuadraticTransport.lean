import Wikipedia.NoExoticSixSphere.DiffeomorphSphereComposition
import Wikipedia.NoExoticSixSphere.GeometricArfInvariant

/-!
# Quadratic transport from original sphere parity along a native diffeomorphism

The linear equivalence is the actual induced map on middle mod-two
homology. Equality of the original parities of embedded sphere
representatives proves that this map is a quadratic isometry. No
arbitrary identification of homology or replacement quadratic form is used.
-/

noncomputable section

open Function
open scoped Manifold ContDiff Topology
open Wikipedia.HopfProblem SphereHomologyCoefficients

namespace NoExoticSixSphere.DiffeomorphQuadraticTransport

open GLOrthonormalization EuclideanEmbedding DiffeomorphSphereComposition

attribute [local instance] modHomologyModule

variable {M M' : Type} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  [TopologicalSpace M'] [ChartedSpace (Vector 6) M']
  (D : M ≃ₘ⟮𝓡 6, 𝓡 6⟯ M')

def middleModTwoEquiv : ModHomology 2 M 3 ≃ₗ[ZMod 2] ModHomology 2 M' 3 :=
  { (modHomologyHomeomorphEquiv 2 D.toHomeomorph 3).toAddEquiv with
    map_smul' := ZMod.map_smul (modHomologyHomeomorphEquiv 2 D.toHomeomorph 3) }

theorem middleModTwoEquiv_apply (c : ModHomology 2 M 3) :
    middleModTwoEquiv D c = modHomologyMap 2 (D.toHomeomorph : C(M, M')) 3 c := rfl

theorem middleModTwoEquiv_sphereClass (f : C(Sphere 3, M)) :
    middleModTwoEquiv D (SixSphereMiddleParity.sphereClass f) =
      SixSphereMiddleParity.sphereClass ((D.toHomeomorph : C(M, M')).comp f) := by
  rw [middleModTwoEquiv_apply, SixSphereMiddleParity.sphereClass,
    SixSphereMiddleParity.sphereClass, modHomologyMap_comp]
  rfl

variable [IsManifold (𝓡 6) ∞ M] [T2Space M] [CompactSpace M] [SimplyConnectedSpace M]
  [IsManifold (𝓡 6) ∞ M'] [T2Space M'] [CompactSpace M'] [SimplyConnectedSpace M']
  (e : EuclideanEmbedding 6 M) (e' : EuclideanEmbedding 6 M')
  (a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel)
  (a' : SmoothRangeFrame (𝓡 6) e'.normalProjection e'.NormalModel)
  (hP : ∀ (f : Sphere 3 → M) (hf : ContMDiff (𝓡 3) (𝓡 6) ∞ f) (hi : Injective f)
    (hd : ∀ s, Injective (mfderiv (𝓡 3) (𝓡 6) f s)),
      e'.sphereParity a' (D ∘ f) (DiffeomorphSphereComposition.smooth D f hf)
        (DiffeomorphSphereComposition.injective D f hi)
        (DiffeomorphSphereComposition.mfderiv_injective D f hf hd) = e.sphereParity a f hf hi hd)
  (r : TubularRetraction e) (r' : TubularRetraction e') (m : M) (m' : M')
  [Subsingleton (π_ 2 M m)] [Subsingleton (π_ 2 M' m')]

include hP in
theorem quadraticForm_map (c : ModHomology 2 M 3) :
    e'.modTwoHomologyQuadraticForm a' r' m' (middleModTwoEquiv D c) =
      e.modTwoHomologyQuadraticForm a r m c := by
  obtain ⟨f, hf, hi, hd, rfl⟩ := e.exists_embedded_modTwoMiddle_representative r m c
  rw [middleModTwoEquiv_sphereClass, e'.modTwoHomologyQuadraticForm_sphereClass,
    e.modTwoHomologyQuadraticForm_sphereClass]
  rw [e'.geometricSphereParity_eq_of_embedding a' r' _
      (DiffeomorphSphereComposition.smooth D f hf)
      (DiffeomorphSphereComposition.injective D f hi.injective)
      (DiffeomorphSphereComposition.mfderiv_injective D f hf hd),
    e.geometricSphereParity_eq_of_embedding a r f hf hi.injective hd]
  exact hP f hf hi.injective hd

def quadraticFormIsometry :
    (e.modTwoHomologyQuadraticForm a r m).IsometryEquiv
      (e'.modTwoHomologyQuadraticForm a' r' m') where
  toLinearEquiv := middleModTwoEquiv D
  map_app' := quadraticForm_map D e e' a a' hP r r' m m'

include hP in
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
    (quadraticFormIsometry D e e' a a' hP r r' m m')

end NoExoticSixSphere.DiffeomorphQuadraticTransport
