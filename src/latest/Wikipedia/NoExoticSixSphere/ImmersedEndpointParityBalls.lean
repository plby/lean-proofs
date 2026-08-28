import Wikipedia.NoExoticSixSphere.ManifoldAffineDoublePointBoundaryCount
import Wikipedia.NoExoticSixSphere.ManifoldAffineParityBallSystem

/-!
# Generic parity balls with self-transverse immersed endpoints

The compact unordered window supplies finiteness of actual singularities
without exterior injectivity. The existing arbitrarily small local parity
balls therefore assemble into a disjoint system. The small-parameter
construction preserves every exterior slice and retains the actual
singularity-versus-double-point count identity.
-/

noncomputable section

open Set Function Topology
open scoped Manifold ContDiff

namespace NoExoticSixSphere.ManifoldAffineSphereFamily

open GLOrthonormalization EuclideanEmbedding SphereFamily

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  [IsManifold (𝓡 6) ∞ M]
  (e : EuclideanEmbedding 6 M) (r : TubularRetraction e) (f : ℝ → Sphere 3 → M)
  (hf : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 6) ∞ (uncurry f))

theorem exists_parityBallSystem_of_selfTransverse_ends (p : Parameters e)
    (hg : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 6) ∞ (uncurry (map e r f p)))
    (S : Set SourceChart) (C : Set (TargetChart 6 M))
    (hS : ∀ x : Sphere 3, ∃ s ∈ S, x ∈ s.source)
    (hC : ∀ x : M, ∃ c ∈ C, x ∈ c.source)
    (hp : ∀ t x, ambient e f p t x ∈ r.domain)
    (hgen : GenericInCharts e r f hf S C p)
    (hext : ∀ t, t ≤ 0 ∨ 1 ≤ t → ∀ x,
      Injective (mfderiv (𝓡 3) (𝓡 6) (f t) x))
    (ht : ∀ t, t = 0 ∨ t = 1 → ∀ x y, x ≠ y → f t x = f t y → Surjective
      ((mfderiv (𝓡 3) (𝓡 6) (f t) x).coprod (mfderiv (𝓡 3) (𝓡 6) (f t) y))) :
    Nonempty (ParityBallSystem (map e r f p)) := by
  refine ParityBallSystem.exists_of_small_balls (map e r f p)
    (finite_singularParameters_of_selfTransverse_ends e r f hf p hg S C hS hC hp hgen hext ht) ?_
  intro q hq N hN hqN
  exact exists_parityBall_in_neighborhood e r f hf p S C hgen hg hS hC hp q
    (singularParameters_time_mem_Ioo e r f p hext hq) hq N hN hqN

include hf in
theorem exists_small_family_with_immersed_parityBalls [CompactSpace M]
    (hext : ∀ t, t ≤ 0 ∨ 1 ≤ t → ∀ x,
      Injective (mfderiv (𝓡 3) (𝓡 6) (f t) x))
    (ht : ∀ t, t = 0 ∨ t = 1 → ∀ x y, x ≠ y → f t x = f t y → Surjective
      ((mfderiv (𝓡 3) (𝓡 6) (f t) x).coprod (mfderiv (𝓡 3) (𝓡 6) (f t) y)))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ p : Parameters e, ‖p‖ < ε ∧
      ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 6) ∞ (uncurry (map e r f p)) ∧
      (∀ t x, ambient e f p t x ∈ r.domain) ∧
      (∀ t, t ≤ 0 ∨ 1 ≤ t → ∀ x, map e r f p t x = f t x) ∧
      Nonempty (ParityBallSystem (map e r f p)) ∧
      SphereSelfIntersections.unorderedParity (map e r f p 0) +
        SphereSelfIntersections.unorderedParity (map e r f p 1) =
          (Nat.card (singularParameters (n := 6) (map e r f p)) : ZMod 2) := by
  obtain ⟨S, C, p, _, hS, _, hC, hsmall, hgen, hp, hg, heq⟩ :=
    exists_small_generic_manifold_family e r f hf rfl hε
  exact ⟨p, hsmall, hg, hp, heq,
    exists_parityBallSystem_of_selfTransverse_ends e r f hf p hg S C hS hC hp hgen hext ht,
    unorderedParity_endpoint_sum e r f hf p hg S C hS hC hp hgen hext ht⟩

end NoExoticSixSphere.ManifoldAffineSphereFamily
