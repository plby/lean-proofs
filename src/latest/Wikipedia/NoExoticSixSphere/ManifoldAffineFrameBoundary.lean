import Wikipedia.NoExoticSixSphere.ManifoldAffineParityBallSystem
import Wikipedia.NoExoticSixSphere.ManifoldFamilyLinkParity

/-!
# A chosen small generic family has equal constructed endpoint obstructions

The perturbation parameter, the finite parity-ball system, the even
singularity count, and all local linking values are supplied by proved
constructions. The exterior slices are retained exactly. These are the
constructed global-frame values, not yet the geometric normal-disk parity.
-/

noncomputable section

open Function
open scoped Manifold ContDiff

namespace NoExoticSixSphere.ManifoldAffineSphereFamily

open GLOrthonormalization EuclideanEmbedding SphereFamily

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  [IsManifold (𝓡 6) ∞ M] [CompactSpace M]
  (e : EuclideanEmbedding 6 M) (r : TubularRetraction e)
  (a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel)
  (f : ℝ → Sphere 3 → M)
  (hf : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 6) ∞ (uncurry f))

include hf in
theorem exists_small_family_equal_frame_endpoints
    (hext : ∀ t, t ≤ 0 ∨ 1 ≤ t → ∀ x : Sphere 3,
      Injective (mfderiv (𝓡 3) (𝓡 6) (f t) x))
    (hinj : ∀ t, t ≤ 0 ∨ 1 ≤ t → Injective (f t))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ p : Parameters e, ‖p‖ < ε ∧
      ∃ hg : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 6) ∞ (uncurry (map e r f p)),
        (∀ t x, ambient e f p t x ∈ r.domain) ∧
        (∀ t, t ≤ 0 ∨ 1 ≤ t → ∀ x, map e r f p t x = f t x) ∧
        ∃ P : ParityBallSystem (map e r f p),
          Even (Nat.card (singularParameters (n := 6) (map e r f p))) ∧
          (∀ q : singularParameters (n := 6) (map e r f p),
            e.familyBoundaryObstruction a (map e r f p) hg P (.inr q) = 1) ∧
          e.familyBoundaryObstruction a (map e r f p) hg P (.inl false) =
            e.familyBoundaryObstruction a (map e r f p) hg P (.inl true) := by
  obtain ⟨p, hsmall, hg, hp, heq, ⟨P⟩, heven⟩ :=
    exists_small_family_with_parityBalls e r f hf hext hinj hε
  exact ⟨p, hsmall, hg, hp, heq, P, heven,
    e.familyBoundaryObstruction_link a (map e r f p) hg P,
    e.endpoint_familyBoundaryObstruction_eq a (map e r f p) hg P heven⟩

end NoExoticSixSphere.ManifoldAffineSphereFamily
