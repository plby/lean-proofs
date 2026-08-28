import Wikipedia.NoExoticSixSphere.SphereSuspensionFiber
import Wikipedia.NoExoticSixSphere.SphereSuspensionHomotopyMap

/-!
# Finite stabilization with the original smooth fiber retained

Any specified finite number of suspensions has a globally smooth homotopic
representative whose actual regular fiber is diffeomorphic to the original
one. The underlying fiber map is the iterated equatorial inclusion.

No vanishing of a stable homotopy class is asserted by this construction.
-/

noncomputable section

open scoped Manifold ContDiff

namespace NoExoticSixSphere.SphereMapSuspension

variable {m n : ℕ}

def iterate (f : C(Sphere m, Sphere n)) : (r : ℕ) → C(Sphere (m + r), Sphere (n + r))
  | 0 => f
  | r + 1 => map (iterate f r)

def equators (n : ℕ) : (r : ℕ) → C(Sphere n, Sphere (n + r))
  | 0 => ContinuousMap.id _
  | r + 1 => (equator (n + r)).comp (equators n r)

theorem iterate_homotopic {f g : C(Sphere m, Sphere n)} (H : f.Homotopic g) (r : ℕ) :
    (iterate f r).Homotopic (iterate g r) := by
  induction r with
  | zero => exact H
  | succ r ih => exact map_homotopic ih

theorem exists_smooth_iterate_with_fiber (f : C(Sphere m, Sphere n))
    (hf : ContMDiff (𝓡 m) (𝓡 n) ∞ f) (b : Sphere n)
    (hreg : ∀ x, f x = b → Function.Surjective (mfderiv (𝓡 m) (𝓡 n) f x))
    (k : ℕ) (hd : m = n + k) (r : ℕ) :
    ∃ g : C(Sphere (m + r), Sphere (n + r)),
      ∃ hg : ContMDiff (𝓡 (m + r)) (𝓡 (n + r)) ∞ g,
      ∃ hgreg : ∀ y, g y = equators n r b → Function.Surjective
        (mfderiv (𝓡 (m + r)) (𝓡 (n + r)) g y),
      (iterate f r).Homotopic g ∧
      letI := regularFiberAtlas f hf b hreg k (by simpa using hd)
      letI := regularFiberAtlas g hg (equators n r b) hgreg k (by
        simp only [finrank_euclideanSpace_fin]; omega)
      ∃ D : {x : Sphere m // f x = b} ≃ₘ⟮𝓡 k, 𝓡 k⟯
          {y : Sphere (m + r) // g y = equators n r b},
        ∀ x, (D x).val = equators m r x.val := by
  induction r with
  | zero =>
    refine ⟨f, hf, hreg, ContinuousMap.Homotopic.refl f, ?_⟩
    let := regularFiberAtlas f hf b hreg k (by simpa using hd)
    exact ⟨Diffeomorph.refl (𝓡 k) _ ∞, fun _ ↦ rfl⟩
  | succ r ih =>
    obtain ⟨g, hg, hgreg, H, D, hD⟩ := ih
    have hdr : m + r = (n + r) + k := by omega
    obtain ⟨G, hG, hGreg, HG, E, hE⟩ :=
      exists_smooth_suspension_with_fiber g hg (equators n r b) hgreg k hdr
    refine ⟨G, hG, hGreg, (map_homotopic H).trans HG, ?_⟩
    let := regularFiberAtlas f hf b hreg k (by simpa using hd)
    let := regularFiberAtlas g hg (equators n r b) hgreg k (by simpa using hdr)
    let := regularFiberAtlas G hG (equators n (r + 1) b) hGreg k (by
      simp only [finrank_euclideanSpace_fin]; omega)
    refine ⟨D.trans E, ?_⟩
    intro x
    change (E (D x)).val = equator (m + r) (equators m r x.val)
    rw [hE, hD]

end NoExoticSixSphere.SphereMapSuspension
