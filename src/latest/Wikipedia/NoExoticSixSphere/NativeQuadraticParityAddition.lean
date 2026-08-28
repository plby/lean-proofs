import Wikipedia.NoExoticSixSphere.IntegralHomologyQuadraticParity

/-!
# The quadratic identity for actual native sphere concatenation

The native cubical multiplication law and the genuine Hurewicz isomorphism
give the integral class of concatenation. The constructed integral quadratic
parity then proves the geometric identity for that original concatenation.
The target is an actual two-connected framed compact six-manifold.
-/

noncomputable section

open scoped Topology Manifold ContDiff

namespace NoExoticSixSphere.SmoothCube

open Wikipedia.HopfProblem.ThirdHurewicz

variable {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]
  {x : X} [Subsingleton (π_ 2 X x)]

theorem integralSphereClass_concatenate (f g : BasedMap 3 X x) :
    integralSphereClass (concatenate f g).val =
      integralSphereClass f.val + integralSphereClass g.val := by
  rw [← hurewiczSphereClass_eq_integralSphereClass x (concatenate f g),
    ← hurewiczSphereClass_eq_integralSphereClass x f,
    ← hurewiczSphereClass_eq_integralSphereClass x g]
  unfold hurewiczSphereClass
  rw [sphereClass_concatenate]
  exact (hurewiczLinearEquiv x).map_add (Additive.ofMul (sphereClass f))
    (Additive.ofMul (sphereClass g))

end NoExoticSixSphere.SmoothCube

namespace NoExoticSixSphere.EuclideanEmbedding

open GLOrthonormalization SmoothCube

variable {M : Type} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  [IsManifold (𝓡 6) ∞ M] [T2Space M] [CompactSpace M] [SimplyConnectedSpace M]
  (e : EuclideanEmbedding 6 M)
  (ν : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel) (r : TubularRetraction e)
  {m : M} [Subsingleton (π_ 2 M m)]

theorem geometricSphereParity_concatenate (f g : BasedMap 3 M m) :
    e.geometricSphereParity ν r (concatenate f g).val =
      e.geometricSphereParity ν r f.val + e.geometricSphereParity ν r g.val +
        e.sphereIntersectionNumber r f.val g.val := by
  rw [← integralHomologyParity_sphereClass e ν r m (concatenate f g).val,
    integralSphereClass_concatenate, integralHomologyParity_add,
    integralHomologyParity_sphereClass, integralHomologyParity_sphereClass,
    integralHomologyIntersection_integralSphereClass]

end NoExoticSixSphere.EuclideanEmbedding
