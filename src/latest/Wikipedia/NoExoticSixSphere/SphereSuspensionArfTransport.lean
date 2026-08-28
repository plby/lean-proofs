import Wikipedia.NoExoticSixSphere.SphereSuspensionFramedComparison
import Wikipedia.NoExoticSixSphere.StabilizedQuadraticTransport

/-!
# The original geometric Arf invariant survives smooth suspension

The actual framed comparison in cylinder target coordinates transports
the quadratic form. The two proved target-chart comparisons then recover
both original defining-equation frames, with independent retractions and
basepoints. This is a statement about the original native regular fibers.
-/

noncomputable section

open scoped Manifold ContDiff Topology

namespace NoExoticSixSphere.SphereMapSuspension

open GLOrthonormalization RegularSphereFiber

variable {m n : ℕ} (f : C(Sphere m, Sphere n))
  (hf : ContMDiff (𝓡 m) (𝓡 n) ∞ f) (b : Sphere n)
  (hreg : ∀ x, f x = b → Function.Surjective (mfderiv (𝓡 m) (𝓡 n) f x))
  (hd : m = n + 6) (a₀ : Sphere m)
  (g : C(Sphere (m + 1), Sphere (n + 1)))
  (hg : ContMDiff (𝓡 (m + 1)) (𝓡 (n + 1)) ∞ g)
  (hgreg : ∀ y, g y = equator n b → Function.Surjective
    (mfderiv (𝓡 (m + 1)) (𝓡 (n + 1)) g y))
  (hgfiber : ∀ y, g y = equator n b ↔ ∃ x : Sphere m, y = equator m x ∧ f x = b)
  (hgerm : ∀ x, f x = b →
    (g : Sphere (m + 1) → Sphere (n + 1)) =ᶠ[𝓝 (equator m x)] map f)
  (a : Sphere (m + 1))
  [SimplyConnectedSpace {x : Sphere m // f x = b}]
  [SimplyConnectedSpace {y : Sphere (m + 1) // g y = equator n b}]
  (x : {x : Sphere m // f x = b}) (y : {y : Sphere (m + 1) // g y = equator n b})
  [Subsingleton (π_ 2 {x : Sphere m // f x = b} x)]
  [Subsingleton (π_ 2 {y : Sphere (m + 1) // g y = equator n b} y)]

include hgfiber hgerm in
theorem geometricArf_smoothSuspension :
    letI := regularFiberAtlas f hf b hreg 6 (by simpa using hd);
    letI := regularFiber_isManifold f hf b hreg 6 _;
    letI := fiber_compact f b;
    letI := regularFiberAtlas g hg (equator n b) hgreg 6 (by
      simp only [finrank_euclideanSpace_fin]; omega);
    letI := regularFiber_isManifold g hg (equator n b) hgreg 6 (by
      simp only [finrank_euclideanSpace_fin]; omega);
    letI := fiber_compact g (equator n b);
    ∀ r : (embedding f hf b hreg 6 hd).TubularRetraction,
      ∀ r' : (embedding g hg (equator n b) hgreg 6 (by omega)).TubularRetraction,
        GeometricArf.invariant (embedding f hf b hreg 6 hd) (frame f hf b hreg 6 hd a₀) r x =
          GeometricArf.invariant (embedding g hg (equator n b) hgreg 6 (by omega))
            (frame g hg (equator n b) hgreg 6 (by omega) a) r' y := by
  let := regularFiberAtlas f hf b hreg 6 (by simpa using hd)
  let := regularFiber_isManifold f hf b hreg 6 (by simpa using hd)
  let := fiber_compact f b
  let := regularFiberAtlas g hg (equator n b) hgreg 6 (by
    simp only [finrank_euclideanSpace_fin]; omega)
  let := regularFiber_isManifold g hg (equator n b) hgreg 6 (by
    simp only [finrank_euclideanSpace_fin]; omega)
  let := fiber_compact g (equator n b)
  intro r r'
  let c := modelChartPartialDiffeomorph (I := 𝓡 n) b
  have hb : b ∈ c.source := mem_extChartAt_source b
  let F := fiberFramedDiffeomorph f hf b hreg 6 hd a₀ c hb g hg hgreg hgfiber hgerm a
  have hF := F.geometricArf_eq r r' x y
  have hsource := geometricArf_frameWithTargetChart f hf b hreg hd a₀ c hb x x r r
  have htarget := geometricArf_frameWithTargetChart g hg (equator n b) hgreg (by omega) a
    (targetCylinderChart c) (equator_mem_targetCylinderChart c b hb) y y r' r'
  exact hsource.symm.trans (hF.trans htarget)

end NoExoticSixSphere.SphereMapSuspension
