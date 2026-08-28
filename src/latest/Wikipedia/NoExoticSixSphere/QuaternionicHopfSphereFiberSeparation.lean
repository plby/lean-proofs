import Wikipedia.NoExoticSixSphere.StableSixSphereArfSeparationAligned
import Wikipedia.NoExoticSixSphere.StableSixSphereMapLiftClass
import Wikipedia.NoExoticSixSphere.QuaternionicHopfArfInvariant
import Wikipedia.NoExoticSixSphere.CompactifiedCollapseArfTransport
import Wikipedia.NoExoticSixSphere.SphereCollapseRegularValue

/-!
# The original Hopf-product stable map class excludes a topological six-sphere fiber

The retained Hopf-product collapse is the actual map from S16 to S10.
Its smooth fiber-preserving representative has the original native fiber
and the original geometric Arf invariant one. Stable Arf separation thus
excludes every smooth same-stage map with a topological six-sphere fiber,
even when its specified regular value differs from the Hopf value.
-/

noncomputable section

open Function
open scoped Manifold ContDiff Topology

namespace NoExoticSixSphere.QuaternionicHopf

open StableSixSphereMaps

local instance sphereFiberSeparationAtlas : ChartedSpace (V 6) (Sphere 3 × Sphere 3) :=
  southPairEuclideanAtlas
local instance sphereFiberSeparationIsManifold : IsManifold (𝓡 6) ∞ (Sphere 3 × Sphere 3) :=
  southPairEuclideanIsManifold

theorem southPairStableMapClass_ne_regular_sixSphere
    (g : StageMap 8) (hg : ContMDiff (𝓡 16) (𝓡 10) ∞ g) (c : Sphere 10)
    (hregg : ∀ x, g x = c → Surjective (mfderiv (𝓡 16) (𝓡 10) g x))
    (hX : {x : Sphere 16 // g x = c} ≃ₜ Sphere 6) :
    ofMap (k := 8) southPairSmoothCollapseData.sphereMap ≠ ofMap g := by
  let : SimplyConnectedSpace (Sphere 3 × Sphere 3) := arfProductSimplyConnected
  let p := (spherePole 3, spherePole 3)
  let : Subsingleton (π_ 2 (Sphere 3 × Sphere 3) p) := arfProductPiTwo p
  obtain ⟨f, hf, H, hfiber, hregf, hgerm⟩ :=
    southPairSmoothCollapseData.exists_smoothSphereMap_regular
  have hN : southPairEuclideanEmbedding.ambientDimension =
      (southPairEuclideanEmbedding.ambientDimension - 6) + 6 := by decide
  let := regularFiberAtlas f hf (sphereZero (southPairEuclideanEmbedding.ambientDimension - 6))
    hregf 6 (by simpa using hN)
  let := regularFiber_isManifold f hf
    (sphereZero (southPairEuclideanEmbedding.ambientDimension - 6)) hregf 6 (by simpa using hN)
  let := RegularSphereFiber.fiber_compact f
    (sphereZero (southPairEuclideanEmbedding.ambientDimension - 6))
  let := regularFiberAtlas f hf (sphereZero 10) hregf 6 (by simpa using hN)
  let := regularFiber_isManifold f hf (sphereZero 10) hregf 6 (by simpa using hN)
  let := RegularSphereFiber.fiber_compact f (sphereZero 10)
  let D := southPairEuclideanEmbedding.diffeomorphToCompactifiedFiber f hf hregf hN hfiber
  let x := D p
  let : SimplyConnectedSpace {y : Sphere southPairEuclideanEmbedding.ambientDimension //
      f y = sphereZero (southPairEuclideanEmbedding.ambientDimension - 6)} :=
    D.symm.toHomeomorph.toHomotopyEquiv.simplyConnectedSpace
  let : Subsingleton (π_ 2 {y : Sphere southPairEuclideanEmbedding.ambientDimension //
      f y = sphereZero (southPairEuclideanEmbedding.ambientDimension - 6)} x) :=
    SphereMapSuspension.piTwo_subsingleton_of_homeomorph D.toHomeomorph p x
  let hSC16 : SimplyConnectedSpace {y : Sphere 16 // f y = sphereZero 10} :=
    D.symm.toHomeomorph.toHomotopyEquiv.simplyConnectedSpace
  let hπ16 : Subsingleton (π_ 2 {y : Sphere 16 // f y = sphereZero 10} x) :=
    SphereMapSuspension.piTwo_subsingleton_of_homeomorph D.toHomeomorph p x
  let : SimplyConnectedSpace {y // f y = sphereZero 10} :=
    D.symm.toHomeomorph.toHomotopyEquiv.simplyConnectedSpace
  let : Subsingleton (π_ 2 {y // f y = sphereZero 10} x) :=
    SphereMapSuspension.piTwo_subsingleton_of_homeomorph D.toHomeomorph p x
  let : Nonempty {y // f y = sphereZero 10} := ⟨x⟩
  let eF := RegularSphereFiber.embedding f hf (sphereZero 10) hregf 6 hN
  let aF := RegularSphereFiber.frame f hf (sphereZero 10) hregf 6 hN (spherePole 16)
  obtain ⟨rF⟩ := eF.nonempty_tubularRetraction aF
  have he := southPairSmoothCollapseData.geometricArf_compactified
    f hf hregf hN hfiber hgerm (spherePole 16) southPairTubularRetraction p x rF
  have hArf : GeometricArf.invariant eF aF rF x ≠ 0 := by
    intro hz
    have hzero := he.symm.trans hz
    rw [geometricArf_southPair] at hzero
    exact one_ne_zero hzero
  have hsep := @ofMap_ne_of_geometricArf_ne_zero_sixSphere_fiber_at 8
    f g hf hg (sphereZero 10) c hregf hregg (spherePole 16) hSC16 x hπ16 hX rF hArf
  intro h
  exact hsep ((ofMap_homotopic (k := 8) H).symm.trans h)

end NoExoticSixSphere.QuaternionicHopf
