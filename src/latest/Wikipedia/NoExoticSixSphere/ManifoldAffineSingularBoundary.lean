import Wikipedia.NoExoticSixSphere.ManifoldAffineBoundaryAtlas
import Wikipedia.NoExoticSixSphere.CompactSphereDoublePoints

/-!
# Actual intrinsic singularities and diagonal boundary orbits

The diagonal inclusion gives a bijection, not merely a cardinality comparison.
No singularity is duplicated or lost when passing to unordered pairs. With
injective exterior slices, the previously constructed compact quotient and the
proved discrete boundary imply finiteness of the actual intrinsic singular set.
-/

noncomputable section

open Set Function Topology
open scoped Manifold ContDiff

namespace NoExoticSixSphere.ManifoldAffineSphereFamily

open GLOrthonormalization EuclideanEmbedding SphereFamily FamilyEmbedding

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector n) M]
  [IsManifold (𝓡 n) ∞ M]
  (e : EuclideanEmbedding n M) (r : TubularRetraction e) (f : ℝ → Sphere 3 → M)
  (hf : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 n) ∞ (uncurry f))
  (p : Parameters e)
  (hg : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 n) ∞ (uncurry (map e r f p)))
  (S : Set SourceChart) (C : Set (TargetChart n M))
  (hS : ∀ x : Sphere 3, ∃ s ∈ S, x ∈ s.source)
  (hC : ∀ x : M, ∃ c ∈ C, x ∈ c.source)
  (hp : ∀ t x, ambient e f p t x ∈ r.domain)
  (hgen : GenericInCharts e r f hf S C p)
  (hext : ∀ t, t ≤ 0 ∨ 1 ≤ t → ∀ x : Sphere 3,
    Injective (mfderiv (𝓡 3) (𝓡 n) (f t) x))

def singularOrbit (q : singularParameters (n := n) (map e r f p)) :
    diagonalOrbits (map e r f p) :=
  ⟨unorderedProj (map e r f p) ⟨(q.val.1, (q.val.2, q.val.2)),
    singular_diagonal_mem_closure e r f hf p hg S C hS hC hp hgen q.val
      (singularParameters_time_mem_Ioo e r f p hext q.property) q.property⟩,
    (mem_diagonalOrbits_iff (map e r f p) _).mpr rfl⟩

omit [IsManifold (𝓡 n) ∞ M] in
theorem injective_singularOrbit :
    Injective (singularOrbit e r f hf p hg S C hS hC hp hgen hext) := by
  intro a b he
  have heq := congrArg Subtype.val he
  rcases (unorderedProj_eq_iff (map e r f p) _ _).mp heq with heq | heq
  · exact Subtype.ext
      (congrArg (fun q : ℝ × (Sphere 3 × Sphere 3) ↦ (q.1, q.2.1)) heq)
  · exact Subtype.ext
      (congrArg (fun q : ℝ × (Sphere 3 × Sphere 3) ↦ (q.1, q.2.1)) heq)

theorem surjective_singularOrbit :
    Surjective (singularOrbit e r f hf p hg S C hS hC hp hgen hext) := by
  rintro ⟨q, hq⟩
  obtain ⟨a, hdiag, rfl⟩ := hq
  rcases a with ⟨⟨t, x, y⟩, hcl⟩
  change x = y at hdiag
  subst y
  have hsing : (t, x) ∈ singularParameters (n := n) (map e r f p) :=
    SphereFamily.singular_of_diagonal_mem_closure (map e r f p) hg (t, x) hcl
  exact ⟨⟨(t, x), hsing⟩, rfl⟩

def singularBoundaryEquiv : singularParameters (n := n) (map e r f p) ≃
    diagonalOrbits (map e r f p) :=
  Equiv.ofBijective (singularOrbit e r f hf p hg S C hS hC hp hgen hext)
    ⟨injective_singularOrbit e r f hf p hg S C hS hC hp hgen hext,
      surjective_singularOrbit e r f hf p hg S C hS hC hp hgen hext⟩

include hg hS hC hp hgen hext

theorem singularBoundary_card : Nat.card (singularParameters (n := n) (map e r f p)) =
    Nat.card (diagonalOrbits (map e r f p)) :=
  Nat.card_congr (singularBoundaryEquiv e r f hf p hg S C hS hC hp hgen hext)

theorem finite_diagonalOrbits
    (hinj : ∀ t, t ≤ 0 ∨ 1 ≤ t → Injective (f t)) :
    (diagonalOrbits (map e r f p)).Finite := by
  let := compactSpace_unordered_map e r f p hinj
  exact (FamilyEmbedding.isClosed_diagonalOrbits (map e r f p)).isCompact.finite
    (isDiscrete_diagonalOrbits e r f hf p hg S C hS hC hp hgen hext)

theorem finite_singularParameters
    (hinj : ∀ t, t ≤ 0 ∨ 1 ≤ t → Injective (f t)) :
    (singularParameters (n := n) (map e r f p)).Finite := by
  have hb := finite_diagonalOrbits e r f hf p hg S C hS hC hp hgen hext hinj
  let := hb.to_subtype
  have hfin : Finite (singularParameters (n := n) (map e r f p)) :=
    Finite.of_equiv (diagonalOrbits (map e r f p))
      (singularBoundaryEquiv e r f hf p hg S C hS hC hp hgen hext).symm
  exact finite_coe_iff.mp hfin

end NoExoticSixSphere.ManifoldAffineSphereFamily
