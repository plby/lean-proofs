import Wikipedia.NoExoticSixSphere.SphereFiberFramedFilling
import Wikipedia.NoExoticSixSphere.HomotopyFramedSlab
import Wikipedia.NoExoticSixSphere.Topology.SimplyConnectedSphere

/-!
# A nullhomotopy supplies a geometric framed filling

A homotopy to a constant distinct from the regular value produces a compact
framed manifold with exactly the original regular fiber as its boundary.
All atlases, embeddings, and frame identities are constructed, not assumed.

The existence of the nullhomotopy is an explicit hypothesis here. In particular,
this theorem alone does not prove that a homotopy six-sphere bounds.
-/

open scoped Manifold ContDiff

namespace NoExoticSixSphere

theorem nonempty_sphereFiberFramedFilling_of_nullhomotopy {m n : ℕ}
    (f : C(Sphere m, Sphere n)) (hf : ContMDiff (𝓡 m) (𝓡 n) ∞ f)
    (b : Sphere n)
    (hreg : ∀ x, f x = b → Function.Surjective (mfderiv (𝓡 m) (𝓡 n) f x))
    (k : ℕ) (hd : m = n + k) (a : Sphere m) (c : Sphere n) (hc : c ≠ b)
    (H : f.Homotopy (ContinuousMap.const (Sphere m) c)) :
    Nonempty (SphereFiberFramedFilling f hf b hreg k hd a) := by
  have hconst : ContMDiff (𝓡 m) (𝓡 n) ∞ (ContinuousMap.const (Sphere m) c) := contMDiff_const
  have hregconst : ∀ x, (ContinuousMap.const (Sphere m) c) x = b →
      Function.Surjective (mfderiv (𝓡 m) (𝓡 n) (ContinuousMap.const (Sphere m) c) x) := by
    intro x hx
    exact (hc hx).elim
  obtain ⟨d, hd₀, hd₁, _, ⟨A⟩, _, _⟩ :=
    exists_framedCollaredCylinder hf hconst H b hreg hregconst k hd a
  have hmiss : ∀ x, d.rightMap x ≠ b := by
    intro x
    simpa only [hd₁, ContinuousMap.const_apply] using hc
  subst f
  exact ⟨A.toSphereFiberFramedFilling hmiss⟩

/-- The usual, unbased nullhomotopy predicate suffices for positive-dimensional targets. -/
theorem nonempty_sphereFiberFramedFilling_of_nullhomotopic {m n : ℕ}
    (f : C(Sphere m, Sphere n)) (hf : ContMDiff (𝓡 m) (𝓡 n) ∞ f)
    (b : Sphere n)
    (hreg : ∀ x, f x = b → Function.Surjective (mfderiv (𝓡 m) (𝓡 n) f x))
    (k : ℕ) (hd : m = n + k) (a : Sphere m) (hn : 0 < n)
    (hnull : f.Nullhomotopic) :
    Nonempty (SphereFiberFramedFilling f hf b hreg k hd a) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  obtain ⟨c, ⟨H⟩⟩ := hnull
  obtain ⟨c', hc'⟩ := exists_ne b
  let p := PathConnectedSpace.somePath c c'
  exact nonempty_sphereFiberFramedFilling_of_nullhomotopy f hf b hreg k hd a c' hc'
    (H.trans p.toHomotopyConst)

end NoExoticSixSphere
