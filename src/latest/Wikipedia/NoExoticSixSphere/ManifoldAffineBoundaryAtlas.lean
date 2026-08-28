import Wikipedia.NoExoticSixSphere.ManifoldAffineBoundaryCurve
import Wikipedia.NoExoticSixSphere.SphereFamilyDiagonalClosure

/-!
# Boundary charts for every diagonal orbit of the actual manifold quotient

Every diagonal accumulation is intrinsically singular. The unchanged exterior
slices are assumed immersive, so such singularities are at interior times,
where the proved genericity gives the reflection charts. These produce genuine
half-line charts on the original quotient and isolate its diagonal boundary.
-/

noncomputable section

open Set Function Topology
open scoped Manifold ContDiff

namespace NoExoticSixSphere.ManifoldAffineSphereFamily

open GLOrthonormalization EuclideanEmbedding SphereFamily FamilyEmbedding InvolutionQuotient

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

include hS hC hp hgen hg hext

theorem exists_unordered_boundary_chart (q : UnorderedClosedDoublePoints (map e r f p))
    (hq : q ∈ diagonalOrbits (map e r f p)) :
    ∃ d : OpenPartialHomeomorph (UnorderedClosedDoublePoints (map e r f p)) HalfLine,
      q ∈ d.source ∧ d q = ⟨0, le_rfl⟩ ∧
      ∀ y ∈ d.source, (d y).val = 0 ↔ y ∈ diagonalOrbits (map e r f p) := by
  obtain ⟨a, hdiag, rfl⟩ := hq
  rcases a with ⟨⟨t, x, y⟩, hcl⟩
  change x = y at hdiag
  subst y
  have hsing : (t, x) ∈ singularParameters (n := n) (map e r f p) :=
    SphereFamily.singular_of_diagonal_mem_closure (map e r f p) hg (t, x) hcl
  have ht := singularParameters_time_mem_Ioo e r f p hext hsing
  obtain ⟨ha, d, hdq, hdz, hiff⟩ :=
    exists_unordered_chart_at_singular e r f hf p hg S C hS hC hp hgen (t, x) ht hsing
  exact ⟨d, hdq, hdz, hiff⟩

theorem isDiscrete_diagonalOrbits : IsDiscrete (diagonalOrbits (map e r f p)) := by
  apply isDiscrete_iff_forall_mem_exists_isOpen.mpr
  intro q hq
  obtain ⟨d, hdq, hdz, hiff⟩ :=
    exists_unordered_boundary_chart e r f hf p hg S C hS hC hp hgen hext q hq
  refine ⟨d.source, d.open_source, ?_⟩
  ext y
  constructor
  · rintro ⟨hy, hyb⟩
    have he : d y = d q := (Subtype.ext ((hiff y hy).mpr hyb)).trans hdz.symm
    exact mem_singleton_iff.mpr (d.injOn hy hdq he)
  · rintro rfl
    exact ⟨hdq, hq⟩

end NoExoticSixSphere.ManifoldAffineSphereFamily
