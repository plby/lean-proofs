import Wikipedia.NoExoticSixSphere.RegularEndpointArfVanishing
import Wikipedia.HopfProblem.DegreeCollapseNativeNullCylinder

/-!
# The original Arf invariant of a two-connected regular fiber obstructs nullhomotopy

An ordinary nullhomotopy constructs a genuine regular collared cylinder
whose left endpoint is literally the original smooth map and whose right
fiber is empty. The endpoint Arf-vanishing theorem therefore applies to
the original native fiber atlas and original defining-equation normal
frame. This proves an obstruction to ordinary nullhomotopy, not stable
sixth-stem generation or completeness of the Arf obstruction.
-/

noncomputable section

open Function
open scoped Manifold ContDiff Topology

namespace NoExoticSixSphere.RegularSphereFiber

open GLOrthonormalization EuclideanEmbedding Wikipedia.HopfProblem.DegreeCollapse

variable {m n : ℕ} (f : C(Sphere m, Sphere n))
  (hf : ContMDiff (𝓡 m) (𝓡 n) ∞ f) (b : Sphere n)
  (hreg : ∀ x, f x = b → Surjective (mfderiv (𝓡 m) (𝓡 n) f x))
  (hd : m = n + 6) (hn : 0 < n) (a : Sphere m)
  [SimplyConnectedSpace {x : Sphere m // f x = b}] (x : {x : Sphere m // f x = b})
  [Subsingleton (π_ 2 {x : Sphere m // f x = b} x)]

include hn in
theorem geometricArf_eq_zero_of_nullhomotopic (hnull : f.Nullhomotopic) :
    letI := regularFiberAtlas f hf b hreg 6 (by simpa using hd);
    letI := regularFiber_isManifold f hf b hreg 6 _;
    letI := fiber_compact f b;
    ∀ r : (embedding f hf b hreg 6 hd).TubularRetraction,
      GeometricArf.invariant (embedding f hf b hreg 6 hd) (frame f hf b hreg 6 hd a) r x = 0 := by
  obtain ⟨d, hleft, hmiss⟩ := exists_regular_filling_cylinder_of_nullhomotopic
    f hf b hreg hn hnull
  subst f
  exact ReflectedSeam.endpointGeometricArf_eq_zero d hmiss hd a x

include hn in
theorem not_nullhomotopic_of_geometricArf_ne_zero :
    letI := regularFiberAtlas f hf b hreg 6 (by simpa using hd);
    letI := regularFiber_isManifold f hf b hreg 6 _;
    letI := fiber_compact f b;
    ∀ r : (embedding f hf b hreg 6 hd).TubularRetraction,
      GeometricArf.invariant (embedding f hf b hreg 6 hd) (frame f hf b hreg 6 hd a) r x ≠ 0 →
        ¬ f.Nullhomotopic := by
  let := regularFiberAtlas f hf b hreg 6 (by simpa using hd)
  let := regularFiber_isManifold f hf b hreg 6 (by simpa using hd)
  let := fiber_compact f b
  intro r hArf hnull
  exact hArf (geometricArf_eq_zero_of_nullhomotopic f hf b hreg hd hn a x hnull r)

end NoExoticSixSphere.RegularSphereFiber
