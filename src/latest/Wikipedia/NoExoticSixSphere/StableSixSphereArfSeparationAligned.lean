import Wikipedia.NoExoticSixSphere.RegularFiberAlignedSphereArfObstruction
import Wikipedia.NoExoticSixSphere.StableSixSphereMapEquality

/-!
# Stable Arf separation with independently specified regular values

Equality in the actual same-stage direct limit supplies the finite
homotopy. The constructed target-value alignment makes the two-ended
Arf obstruction apply without any equality assumption on the original
regular values. Original left Arf and original right fiber topology are
retained throughout.
-/

noncomputable section

open Function
open scoped Manifold ContDiff Topology

namespace NoExoticSixSphere.StableSixSphereMaps

open RegularSphereFiber

variable {k : ℕ} (f g : StageMap k)
  (hf : ContMDiff (𝓡 (k + 8)) (𝓡 (k + 2)) ∞ f)
  (hg : ContMDiff (𝓡 (k + 8)) (𝓡 (k + 2)) ∞ g)
  (b c : Sphere (k + 2))
  (hregf : ∀ x, f x = b → Surjective (mfderiv (𝓡 (k + 8)) (𝓡 (k + 2)) f x))
  (hregg : ∀ x, g x = c → Surjective (mfderiv (𝓡 (k + 8)) (𝓡 (k + 2)) g x))
  (a : Sphere (k + 8)) [SimplyConnectedSpace {x : Sphere (k + 8) // f x = b}]
  (x : {x : Sphere (k + 8) // f x = b})
  [Subsingleton (π_ 2 {x : Sphere (k + 8) // f x = b} x)]

include hg hregg

theorem geometricArf_eq_zero_of_stable_eq_sixSphere_fiber_at
    (hX : {x : Sphere (k + 8) // g x = c} ≃ₜ Sphere 6) (h : ofMap f = ofMap g) :
    letI := regularFiberAtlas f hf b hregf 6 (by simp only [finrank_euclideanSpace_fin]);
    letI := regularFiber_isManifold f hf b hregf 6 (by simp only [finrank_euclideanSpace_fin]);
    letI := fiber_compact f b;
    ∀ r : (embedding f hf b hregf 6 (by omega)).TubularRetraction,
      GeometricArf.invariant (embedding f hf b hregf 6 (by omega))
        (frame f hf b hregf 6 (by omega) a) r x = 0 := by
  obtain ⟨j, hH⟩ := (ofMap_eq_iff_finite_homotopic f g).mp h
  exact geometricArf_eq_zero_of_suspended_homotopy_sixSphere_at
    f g hf hg b c hregf hregg (by omega) (by omega) a x hX j hH

theorem ofMap_ne_of_geometricArf_ne_zero_sixSphere_fiber_at
    (hX : {x : Sphere (k + 8) // g x = c} ≃ₜ Sphere 6) :
    letI := regularFiberAtlas f hf b hregf 6 (by simp only [finrank_euclideanSpace_fin]);
    letI := regularFiber_isManifold f hf b hregf 6 (by simp only [finrank_euclideanSpace_fin]);
    letI := fiber_compact f b;
    ∀ r : (embedding f hf b hregf 6 (by omega)).TubularRetraction,
      GeometricArf.invariant (embedding f hf b hregf 6 (by omega))
        (frame f hf b hregf 6 (by omega) a) r x ≠ 0 → ofMap f ≠ ofMap g := by
  let := regularFiberAtlas f hf b hregf 6 (by simp only [finrank_euclideanSpace_fin])
  let := regularFiber_isManifold f hf b hregf 6 (by simp only [finrank_euclideanSpace_fin])
  let := fiber_compact f b
  intro r hArf h
  exact hArf (geometricArf_eq_zero_of_stable_eq_sixSphere_fiber_at
    f g hf hg b c hregf hregg a x hX h r)

end NoExoticSixSphere.StableSixSphereMaps
