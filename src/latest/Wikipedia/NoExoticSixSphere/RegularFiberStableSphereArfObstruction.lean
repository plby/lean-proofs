import Wikipedia.NoExoticSixSphere.RegularFiberHomotopyArf
import Wikipedia.NoExoticSixSphere.IteratedSphereSuspensionArf

/-!
# Nonzero original Arf excludes finite stable homotopy to a six-sphere fiber

At the given finite stage, construct smooth representatives of both
suspended maps with their original native fibers retained. The left
representative also retains the original Arf invariant. The actual
homotopy between the smooth representatives constructs a regular collared
cylinder, so the six-sphere endpoint theorem forces the original Arf to
vanish. There is no assumed bordism or Arf-invariance principle here.

Both original maps have the same specified regular value. Alignment of
different regular values and conversion of stable group equalities into
the displayed finite ordinary homotopies are separate steps.
-/

noncomputable section

open Function
open scoped Manifold ContDiff Topology

namespace NoExoticSixSphere.RegularSphereFiber

open SphereMapSuspension

variable {m n : ℕ} (f g : C(Sphere m, Sphere n))
  (hf : ContMDiff (𝓡 m) (𝓡 n) ∞ f) (hg : ContMDiff (𝓡 m) (𝓡 n) ∞ g)
  (b : Sphere n)
  (hregf : ∀ x, f x = b → Surjective (mfderiv (𝓡 m) (𝓡 n) f x))
  (hregg : ∀ x, g x = b → Surjective (mfderiv (𝓡 m) (𝓡 n) g x))
  (hd : m = n + 6) (a : Sphere m)
  [SimplyConnectedSpace {x : Sphere m // f x = b}]
  (x : {x : Sphere m // f x = b}) [Subsingleton (π_ 2 {x : Sphere m // f x = b} x)]

include hg hregg

theorem geometricArf_eq_zero_of_suspended_homotopy_sixSphere
    (hX : {x : Sphere m // g x = b} ≃ₜ Sphere 6) (j : ℕ)
    (hH : (iterate f j).Homotopic (iterate g j)) :
    letI := regularFiberAtlas f hf b hregf 6 (by simpa using hd);
    letI := regularFiber_isManifold f hf b hregf 6 _;
    letI := fiber_compact f b;
    ∀ r : (embedding f hf b hregf 6 hd).TubularRetraction,
      GeometricArf.invariant (embedding f hf b hregf 6 hd) (frame f hf b hregf 6 hd a) r x = 0 := by
  let := regularFiberAtlas f hf b hregf 6 (by simpa using hd)
  let := regularFiber_isManifold f hf b hregf 6 (by simpa using hd)
  let := fiber_compact f b
  let := regularFiberAtlas g hg b hregg 6 (by simpa using hd)
  obtain ⟨F, hF, hregF, hHF, DF, _, hSC, hπ, hArf⟩ :=
    exists_smooth_iterate_with_original_arf f hf b hregf hd a x j
  have hdj : m + j = (n + j) + 6 := by omega
  let := regularFiberAtlas F hF (equators n j b) hregF 6 (by simpa using hdj)
  let := regularFiber_isManifold F hF (equators n j b) hregF 6 (by simpa using hdj)
  let := fiber_compact F (equators n j b)
  let := hSC
  let := hπ
  obtain ⟨G, hG, hregG, hHG, DG, _⟩ :=
    exists_smooth_iterate_with_fiber g hg b hregg 6 hd j
  let := regularFiberAtlas G hG (equators n j b) hregG 6 (by simpa using hdj)
  have hHFG : F.Homotopic G := hHF.symm.trans (hH.trans hHG)
  obtain ⟨rF⟩ := (embedding F hF (equators n j b) hregF 6 hdj).nonempty_tubularRetraction
    (frame F hF (equators n j b) hregF 6 hdj (equators m j a))
  have hz := geometricArf_eq_zero_of_homotopic_sixSphere_fiber F G hF hG
    (equators n j b) hregF hregG hdj (equators m j a) (DF x)
    (DG.symm.toHomeomorph.trans hX) hHFG rF
  intro r
  exact (hArf r rF).trans hz

theorem not_finitely_stably_homotopic_sixSphere_fiber_of_geometricArf_ne_zero
    (hX : {x : Sphere m // g x = b} ≃ₜ Sphere 6) :
    letI := regularFiberAtlas f hf b hregf 6 (by simpa using hd);
    letI := regularFiber_isManifold f hf b hregf 6 _;
    letI := fiber_compact f b;
    ∀ r : (embedding f hf b hregf 6 hd).TubularRetraction,
      GeometricArf.invariant (embedding f hf b hregf 6 hd) (frame f hf b hregf 6 hd a) r x ≠ 0 →
        ¬ ∃ j : ℕ, (iterate f j).Homotopic (iterate g j) := by
  let := regularFiberAtlas f hf b hregf 6 (by simpa using hd)
  let := regularFiber_isManifold f hf b hregf 6 (by simpa using hd)
  let := fiber_compact f b
  intro r hArf
  rintro ⟨j, hH⟩
  exact hArf (geometricArf_eq_zero_of_suspended_homotopy_sixSphere
    f g hf hg b hregf hregg hd a x hX j hH r)

end NoExoticSixSphere.RegularSphereFiber
