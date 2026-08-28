import Wikipedia.NoExoticSixSphere.ManifoldParityBallSystem
import Wikipedia.NoExoticSixSphere.ManifoldAffineChartedParityBall
import Wikipedia.NoExoticSixSphere.ManifoldAffineEvenSingularCount

/-!
# Disjoint parity balls for an actual small generic manifold family

Both the finiteness of the intrinsic singular set and the arbitrarily small
local balls are supplied by proved constructions. The final existence theorem
also chooses the actual small perturbation parameter and retains every
exterior slice exactly. The exterior slices are required to be embeddings at
the level of injectivity and intrinsic immersion.
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

theorem exists_parityBallSystem (p : Parameters e)
    (hg : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 6) ∞ (uncurry (map e r f p)))
    (S : Set SourceChart) (C : Set (TargetChart 6 M))
    (hS : ∀ x : Sphere 3, ∃ s ∈ S, x ∈ s.source)
    (hC : ∀ x : M, ∃ c ∈ C, x ∈ c.source)
    (hp : ∀ t x, ambient e f p t x ∈ r.domain)
    (hgen : GenericInCharts e r f hf S C p)
    (hext : ∀ t, t ≤ 0 ∨ 1 ≤ t → ∀ x : Sphere 3,
      Injective (mfderiv (𝓡 3) (𝓡 6) (f t) x))
    (hinj : ∀ t, t ≤ 0 ∨ 1 ≤ t → Injective (f t)) :
    Nonempty (ParityBallSystem (map e r f p)) := by
  refine ParityBallSystem.exists_of_small_balls (map e r f p)
    (finite_singularParameters e r f hf p hg S C hS hC hp hgen hext hinj) ?_
  intro q hq N hN hqN
  exact exists_parityBall_in_neighborhood e r f hf p S C hgen hg hS hC hp q
    (singularParameters_time_mem_Ioo e r f p hext hq) hq N hN hqN

include hf in
theorem exists_small_family_with_parityBalls [CompactSpace M]
    (hext : ∀ t, t ≤ 0 ∨ 1 ≤ t → ∀ x : Sphere 3,
      Injective (mfderiv (𝓡 3) (𝓡 6) (f t) x))
    (hinj : ∀ t, t ≤ 0 ∨ 1 ≤ t → Injective (f t))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ p : Parameters e, ‖p‖ < ε ∧
      ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 6) ∞ (uncurry (map e r f p)) ∧
      (∀ t x, ambient e f p t x ∈ r.domain) ∧
      (∀ t, t ≤ 0 ∨ 1 ≤ t → ∀ x, map e r f p t x = f t x) ∧
      Nonempty (ParityBallSystem (map e r f p)) ∧
      Even (Nat.card (singularParameters (n := 6) (map e r f p))) := by
  obtain ⟨S, C, p, _, hS, _, hC, hsmall, hgen, hp, hg, heq⟩ :=
    exists_small_generic_manifold_family e r f hf rfl hε
  exact ⟨p, hsmall, hg, hp, heq,
    exists_parityBallSystem e r f hf p hg S C hS hC hp hgen hext hinj,
    (finite_even_singularParameters e r f hf p hg S C hS hC hp hgen hext hinj rfl).2⟩

end NoExoticSixSphere.ManifoldAffineSphereFamily
