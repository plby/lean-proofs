import Wikipedia.NoExoticSixSphere.SpanningDiskDimension

/-!
# The radial-extension fallback does not change the spanning-disk problem

The raw retraction can use any sphere point at zero. The smooth cutoff kills
that value, so the ambient extension and prescribed collar are independent of
it everywhere. Reindexing disk data therefore retains the exact same map,
derivative, boundary frame and parity.
-/

noncomputable section

open Metric
open scoped Manifold ContDiff

namespace NoExoticSixSphere

namespace SphereRadialRetraction

theorem retract_eq_of_ne_zero {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (b₀ b₁ : UnitSphere E) {x : E} (hx : x ≠ 0) : retract b₀ x = retract b₁ x := by
  simp only [retract, dif_neg hx]

end SphereRadialRetraction

namespace SmoothSphereAmbient

theorem extension_independent_fallback {n : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] (b₀ b₁ : Sphere n) (f : Sphere n → F) :
    extension b₀ f = extension b₁ f := by
  funext x
  by_cases hx : x = 0
  · subst x
    have hχ : cutoff n 0 = 1 :=
      (cutoff n).one_of_mem_closedBall (by simp [cutoff])
    simp only [extension, hχ, sub_self, zero_smul]
  · rw [extension, extension, SphereRadialRetraction.retract_eq_of_ne_zero b₀ b₁ hx]

end SmoothSphereAmbient

namespace SphereExtensionWithHeight

theorem map_independent_fallback {n : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] (b₀ b₁ : Sphere n) (f : Sphere n → F) :
    map b₀ f = map b₁ f := by
  funext x
  simp only [map, SmoothSphereAmbient.extension_independent_fallback b₀ b₁ f]

end SphereExtensionWithHeight

namespace StabilizedSpanningDisk

open GLOrthonormalization Stiefel

theorem collar_independent_fallback {n N : ℕ} (b₀ b₁ : Sphere n)
    (f : Sphere n → Vector N) : collar b₀ f = collar b₁ f := by
  funext x
  simp only [collar, SphereExtensionWithHeight.map_independent_fallback b₀ b₁ f]

namespace DiskData

def changeFallback {N : ℕ} {b : Sphere 3} {f : Sphere 3 → Vector N}
    (D : DiskData b f) (b' : Sphere 3) : DiskData b' f where
  toFun := D.toFun
  smooth := D.smooth
  embedded := D.embedded
  immersive := D.immersive
  boundary := D.boundary
  avoids := D.avoids
  collar_eq := by
    obtain ⟨V, hV, hSV, heq⟩ := D.collar_eq
    refine ⟨V, hV, hSV, ?_⟩
    simpa only [collar_independent_fallback b b' f] using heq

theorem parity_changeFallback {k : ℕ} {b : Sphere 3} {f : Sphere 3 → Vector (k + 6)}
    (D : DiskData b f) (b' : Sphere 3) (hf : ContMDiff (𝓡 3) (𝓡 (k + 6)) ∞ f)
    (a : Sphere 3 → Space (k + 6) k)
    (has : ContMDiff (𝓡 3) 𝓘(ℝ, Vector k →L[ℝ] Vector (k + 6)) ∞ (fun s ↦ (a s).val))
    (ha : ∀ s, (a s).val.range ≤ (mfderiv (𝓡 3) (𝓡 (k + 6)) f s).rangeᗮ) :
    (D.changeFallback b').parity hf a has ha = D.parity hf a has ha := rfl

theorem parityOfDimension_changeFallback {N k : ℕ} {b : Sphere 3}
    {f : Sphere 3 → Vector N} (D : DiskData b f) (b' : Sphere 3) (hN : N = k + 6)
    (hf : ContMDiff (𝓡 3) (𝓡 N) ∞ f) (a : Sphere 3 → Space N k)
    (has : ContMDiff (𝓡 3) 𝓘(ℝ, Vector k →L[ℝ] Vector N) ∞ (fun s ↦ (a s).val))
    (ha : ∀ s, (a s).val.range ≤ (mfderiv (𝓡 3) (𝓡 N) f s).rangeᗮ) :
    (D.changeFallback b').parityOfDimension hN hf a has ha =
      D.parityOfDimension hN hf a has ha := by
  subst N
  exact D.parity_changeFallback b' hf a has ha

end DiskData

end StabilizedSpanningDisk

end NoExoticSixSphere
