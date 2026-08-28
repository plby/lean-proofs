import Wikipedia.NoExoticSixSphere.IteratedSphereSuspension
import Wikipedia.NoExoticSixSphere.NullhomotopyFramedFilling

/-!
# A finite suspension nullhomotopy fills the original smooth fiber

An actual nullhomotopy after a specified finite number of suspensions gives a
compact normally framed manifold whose entire actual boundary is diffeomorphic
to the original regular fiber, in its original atlas. The boundary inclusion
is exactly the zero-time lift of the iterated equatorial inclusion.

The suspension nullhomotopy remains an explicit hypothesis. This theorem does
not prove the dimension-six stable computation, and it does not identify the
resulting boundary frame with a separately prescribed original framing.
-/

open scoped Manifold ContDiff

namespace NoExoticSixSphere.SphereMapSuspension

theorem exists_framedFilling_of_nullhomotopic_iterate {m n : ℕ}
    (f : C(Sphere m, Sphere n)) (hf : ContMDiff (𝓡 m) (𝓡 n) ∞ f) (b : Sphere n)
    (hreg : ∀ x, f x = b → Function.Surjective (mfderiv (𝓡 m) (𝓡 n) f x))
    (k : ℕ) (hd : m = n + k) (a : Sphere m) (r : ℕ) (hn : 0 < n + r)
    (hnull : (iterate f r).Nullhomotopic) :
    ∃ g : C(Sphere (m + r), Sphere (n + r)),
      ∃ hg : ContMDiff (𝓡 (m + r)) (𝓡 (n + r)) ∞ g,
      ∃ hgreg : ∀ y, g y = equators n r b → Function.Surjective
        (mfderiv (𝓡 (m + r)) (𝓡 (n + r)) g y),
      ∃ A : SphereFiberFramedFilling g hg (equators n r b) hgreg k
        (by omega) (equators m r a),
      letI := regularFiberAtlas f hf b hreg k (by simpa using hd)
      letI := A.topology
      letI := A.atlas
      letI := A.boundaryAtlas
      ∃ D : {x : Sphere m // f x = b} ≃ₘ⟮𝓡 k, 𝓡 k⟯
          {w : A.W // ((𝓡∂ 1).prod (𝓡 k)).IsBoundaryPoint w},
        ∀ x, A.inclusion (D x).val = WithLp.toLp 2 (0, (equators m r x.val).val) := by
  obtain ⟨g, hg, hgreg, H, D, hD⟩ := exists_smooth_iterate_with_fiber f hf b hreg k hd r
  have hgn : g.Nullhomotopic := by
    obtain ⟨c, hc⟩ := hnull
    exact ⟨c, H.symm.trans hc⟩
  have hdr : m + r = (n + r) + k := by omega
  obtain ⟨A⟩ := nonempty_sphereFiberFramedFilling_of_nullhomotopic g hg
    (equators n r b) hgreg k hdr (equators m r a) hn hgn
  refine ⟨g, hg, hgreg, A, ?_⟩
  let := regularFiberAtlas f hf b hreg k (by simpa using hd)
  let := regularFiberAtlas g hg (equators n r b) hgreg k (by simpa using hdr)
  let := A.topology
  let := A.atlas
  let := A.boundaryAtlas
  refine ⟨D.trans A.boundaryDiffeomorph, ?_⟩
  intro x
  change A.inclusion (A.boundaryDiffeomorph (D x)).val = _
  rw [A.boundary_value, hD]

end NoExoticSixSphere.SphereMapSuspension
