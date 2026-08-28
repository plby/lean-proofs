import Wikipedia.NoExoticSixSphere.IteratedSphereSuspensionArf
import Wikipedia.NoExoticSixSphere.RegularFiberNullhomotopyArf

/-!
# Nonzero original regular-fiber Arf obstructs every finite suspension nullhomotopy

For a specified finite suspension, construct its smooth representative
with the original regular-fiber Arf invariant. An ordinary nullhomotopy
of that representative forces this invariant to vanish. Thus nonzero
Arf obstructs actual nullhomotopy after every finite number of suspensions.
This is the nonvanishing direction, not a generation or completeness theorem.
-/

noncomputable section

open scoped Manifold ContDiff Topology

namespace NoExoticSixSphere.RegularSphereFiber

open GLOrthonormalization SphereMapSuspension

variable {m n : ℕ} (f : C(Sphere m, Sphere n))
  (hf : ContMDiff (𝓡 m) (𝓡 n) ∞ f) (b : Sphere n)
  (hreg : ∀ x, f x = b → Function.Surjective (mfderiv (𝓡 m) (𝓡 n) f x))
  (hd : m = n + 6) (hn : 0 < n) (a₀ : Sphere m)
  [SimplyConnectedSpace {x : Sphere m // f x = b}]
  (x : {x : Sphere m // f x = b}) [Subsingleton (π_ 2 {x : Sphere m // f x = b} x)]

include hn in
theorem geometricArf_eq_zero_of_finite_suspension_nullhomotopic
    (j : ℕ) (hnull : (iterate f j).Nullhomotopic) :
    letI := regularFiberAtlas f hf b hreg 6 (by simpa using hd);
    letI := regularFiber_isManifold f hf b hreg 6 _;
    letI := fiber_compact f b;
    ∀ r : (embedding f hf b hreg 6 hd).TubularRetraction,
      GeometricArf.invariant (embedding f hf b hreg 6 hd) (frame f hf b hreg 6 hd a₀) r x = 0 := by
  let := regularFiberAtlas f hf b hreg 6 (by simpa using hd)
  let := regularFiber_isManifold f hf b hreg 6 (by simpa using hd)
  let := fiber_compact f b
  obtain ⟨g, hg, hgreg, H, D, _, hSC, hπ, hArf⟩ :=
    exists_smooth_iterate_with_original_arf f hf b hreg hd a₀ x j
  have hdg : m + j = (n + j) + 6 := by omega
  let := regularFiberAtlas g hg (equators n j b) hgreg 6 (by simpa using hdg)
  let := regularFiber_isManifold g hg (equators n j b) hgreg 6 (by simpa using hdg)
  let := fiber_compact g (equators n j b)
  let := hSC
  let := hπ
  have hgnull : g.Nullhomotopic := by
    obtain ⟨c, hc⟩ := hnull
    exact ⟨c, H.symm.trans hc⟩
  obtain ⟨rg⟩ := (embedding g hg (equators n j b) hgreg 6 hdg).nonempty_tubularRetraction
    (frame g hg (equators n j b) hgreg 6 hdg (equators m j a₀))
  have hz := geometricArf_eq_zero_of_nullhomotopic g hg (equators n j b) hgreg hdg
    (by omega) (equators m j a₀) (D x) hgnull rg
  intro r
  exact (hArf r rg).trans hz

include hn in
theorem not_finitely_stably_nullhomotopic_of_geometricArf_ne_zero :
    letI := regularFiberAtlas f hf b hreg 6 (by simpa using hd);
    letI := regularFiber_isManifold f hf b hreg 6 _;
    letI := fiber_compact f b;
    ∀ r : (embedding f hf b hreg 6 hd).TubularRetraction,
      GeometricArf.invariant (embedding f hf b hreg 6 hd) (frame f hf b hreg 6 hd a₀) r x ≠ 0 →
        ¬ ∃ j : ℕ, (iterate f j).Nullhomotopic := by
  let := regularFiberAtlas f hf b hreg 6 (by simpa using hd)
  let := regularFiber_isManifold f hf b hreg 6 (by simpa using hd)
  let := fiber_compact f b
  intro r hArf
  rintro ⟨j, hnull⟩
  exact hArf (geometricArf_eq_zero_of_finite_suspension_nullhomotopic
    f hf b hreg hd hn a₀ x j hnull r)

end NoExoticSixSphere.RegularSphereFiber
