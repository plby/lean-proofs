import Wikipedia.NoExoticSixSphere.ManifoldAffineUnorderedAtlas
import Wikipedia.NoExoticSixSphere.ManifoldAffineSingularBoundary
import Wikipedia.NoExoticSixSphere.CompactHalfLineBoundary

/-!
# Even intrinsic singularity count for an actual small manifold perturbation

The constructed compact quotient, genuine half-line atlas, and actual
singular-boundary bijection give an even finite singular set. The existence
theorem chooses the common generic parameter; genericity and a compact
container are not assumptions of that existence result.

The original exterior slices must be injective and immersive. This count does
not yet give the global geometric parity comparison or a sphere classification.
-/

noncomputable section

open Set Function Topology
open scoped Manifold ContDiff

namespace NoExoticSixSphere.ManifoldAffineSphereFamily

open GLOrthonormalization EuclideanEmbedding SphereFamily FamilyEmbedding CurveDecomposition

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector n) M]
  [IsManifold (𝓡 n) ∞ M]
  (e : EuclideanEmbedding n M) (r : TubularRetraction e) (f : ℝ → Sphere 3 → M)
  (hf : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 n) ∞ (uncurry f))

theorem finite_even_singularParameters (p : Parameters e)
    (hg : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 n) ∞ (uncurry (map e r f p)))
    (S : Set SourceChart) (C : Set (TargetChart n M))
    (hS : ∀ x : Sphere 3, ∃ s ∈ S, x ∈ s.source)
    (hC : ∀ x : M, ∃ c ∈ C, x ∈ c.source)
    (hp : ∀ t x, ambient e f p t x ∈ r.domain)
    (hgen : GenericInCharts e r f hf S C p)
    (hext : ∀ t, t ≤ 0 ∨ 1 ≤ t → ∀ x : Sphere 3,
      Injective (mfderiv (𝓡 3) (𝓡 n) (f t) x))
    (hinj : ∀ t, t ≤ 0 ∨ 1 ≤ t → Injective (f t)) (hn : n = 6) :
    (singularParameters (n := n) (map e r f p)).Finite ∧
      Even (Nat.card (singularParameters (n := n) (map e r f p))) := by
  let := t2Space_unordered (map e r f p)
  let := compactSpace_unordered_map e r f p hinj
  have hb := finite_even_boundary_of_compact_atlas (diagonalOrbits (map e r f p))
    (unorderedChart e r f hf p hg S C hS hC hp hgen hext hinj hn)
    (unorderedChart_mem_source e r f hf p hg S C hS hC hp hgen hext hinj hn)
    (unorderedChart_zero_iff e r f hf p hg S C hS hC hp hgen hext hinj hn)
  refine ⟨finite_singularParameters e r f hf p hg S C hS hC hp hgen hext hinj, ?_⟩
  rw [singularBoundary_card e r f hf p hg S C hS hC hp hgen hext, Nat.card_coe_set_eq]
  exact hb.2

include hf in
theorem exists_small_family_even_singularities [CompactSpace M]
    (hext : ∀ t, t ≤ 0 ∨ 1 ≤ t → ∀ x : Sphere 3,
      Injective (mfderiv (𝓡 3) (𝓡 n) (f t) x))
    (hinj : ∀ t, t ≤ 0 ∨ 1 ≤ t → Injective (f t)) (hn : n = 6)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ p : Parameters e, ‖p‖ < ε ∧
      ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 n) ∞ (uncurry (map e r f p)) ∧
      (∀ t x, ambient e f p t x ∈ r.domain) ∧
      (∀ t, t ≤ 0 ∨ 1 ≤ t → ∀ x, map e r f p t x = f t x) ∧
      (singularParameters (n := n) (map e r f p)).Finite ∧
      Even (Nat.card (singularParameters (n := n) (map e r f p))) := by
  obtain ⟨S, C, p, _, hS, _, hC, hsmall, hgen, hp, hg, heq⟩ :=
    exists_small_generic_manifold_family e r f hf hn hε
  exact ⟨p, hsmall, hg, hp, heq,
    finite_even_singularParameters e r f hf p hg S C hS hC hp hgen hext hinj hn⟩

end NoExoticSixSphere.ManifoldAffineSphereFamily
