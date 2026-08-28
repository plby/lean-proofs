import Wikipedia.NoExoticSixSphere.CircleCylinderEndpointArfVanishing
import Wikipedia.NoExoticSixSphere.RelativeRegularCylinder

/-!
# An actual homotopy to a map with six-sphere fiber forces original Arf vanishing

Relative smoothing and the endpoint-preserving regular-cylinder theorem
construct the cylinder from the given continuous homotopy. Both smooth
endpoint maps remain literally unchanged. Thus the two-ended boundary
theorem applies to the original left native atlas and unnormalized frame.
Only a homeomorphism of the right fiber with the standard sphere is needed.
-/

noncomputable section

open Function
open scoped Manifold ContDiff Topology

namespace NoExoticSixSphere.RegularSphereFiber

variable {m n : ℕ} (f g : C(Sphere m, Sphere n))
  (hf : ContMDiff (𝓡 m) (𝓡 n) ∞ f) (hg : ContMDiff (𝓡 m) (𝓡 n) ∞ g)
  (b : Sphere n)
  (hregf : ∀ x, f x = b → Surjective (mfderiv (𝓡 m) (𝓡 n) f x))
  (hregg : ∀ x, g x = b → Surjective (mfderiv (𝓡 m) (𝓡 n) g x))
  (hd : m = n + 6) (a : Sphere m)
  [SimplyConnectedSpace {x : Sphere m // f x = b}]
  (x : {x : Sphere m // f x = b}) [Subsingleton (π_ 2 {x : Sphere m // f x = b} x)]

include hg hregg

theorem geometricArf_eq_zero_of_homotopic_sixSphere_fiber
    (hX : {x : Sphere m // g x = b} ≃ₜ Sphere 6) (hH : f.Homotopic g) :
    letI := regularFiberAtlas f hf b hregf 6 (by simpa using hd);
    letI := regularFiber_isManifold f hf b hregf 6 _;
    letI := fiber_compact f b;
    ∀ r : (embedding f hf b hregf 6 hd).TubularRetraction,
      GeometricArf.invariant (embedding f hf b hregf 6 hd) (frame f hf b hregf 6 hd a) r x = 0 := by
  obtain ⟨H⟩ := hH
  obtain ⟨d, hleft, hright, _⟩ := exists_regularCollaredCylinder hf hg H b hregf hregg
  subst f
  subst g
  exact CircleCylinder.leftEndpointArf_eq_zero_of_right_sixSphere d hd
    (Classical.choice (inferInstance : Nonempty (Sphere 1)), a) x hX

theorem not_homotopic_sixSphere_fiber_of_geometricArf_ne_zero
    (hX : {x : Sphere m // g x = b} ≃ₜ Sphere 6) :
    letI := regularFiberAtlas f hf b hregf 6 (by simpa using hd);
    letI := regularFiber_isManifold f hf b hregf 6 _;
    letI := fiber_compact f b;
    ∀ r : (embedding f hf b hregf 6 hd).TubularRetraction,
      GeometricArf.invariant (embedding f hf b hregf 6 hd) (frame f hf b hregf 6 hd a) r x ≠ 0 →
        ¬ f.Homotopic g := by
  let := regularFiberAtlas f hf b hregf 6 (by simpa using hd)
  let := regularFiber_isManifold f hf b hregf 6 (by simpa using hd)
  let := fiber_compact f b
  intro r hArf hH
  exact hArf (geometricArf_eq_zero_of_homotopic_sixSphere_fiber
    f g hf hg b hregf hregg hd a x hX hH r)

end NoExoticSixSphere.RegularSphereFiber
