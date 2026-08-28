import Wikipedia.NoExoticSixSphere.ManifoldAffineBoundaryAtlas
import Wikipedia.NoExoticSixSphere.ManifoldAffineInteriorCurve
import Wikipedia.NoExoticSixSphere.HalfLineInteriorChart

/-!
# A half-line atlas on the original unordered manifold-family double-point closure

The actual off-diagonal and diagonal charts cover the quotient with its
unchanged topology. Every chart identifies coordinate zero exactly with its
actual diagonal boundary. Only a topological atlas is asserted here.
-/

noncomputable section

open Set Function Topology
open scoped Manifold ContDiff

namespace NoExoticSixSphere.ManifoldAffineSphereFamily

open GLOrthonormalization EuclideanEmbedding FamilyEmbedding InvolutionQuotient

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
  (hinj : ∀ t, t ≤ 0 ∨ 1 ≤ t → Injective (f t)) (hn : n = 6)

include hg hS hC hp hgen hext hinj hn

theorem exists_unordered_halfLine_chart (q : UnorderedClosedDoublePoints (map e r f p)) :
    ∃ d : OpenPartialHomeomorph (UnorderedClosedDoublePoints (map e r f p)) HalfLine,
      q ∈ d.source ∧ ∀ y ∈ d.source, (d y).val = 0 ↔ y ∈ diagonalOrbits (map e r f p) := by
  by_cases hq : q ∈ diagonalOrbits (map e r f p)
  · obtain ⟨d, hdq, _, hiff⟩ :=
      exists_unordered_boundary_chart e r f hf p hg S C hS hC hp hgen hext q hq
    exact ⟨d, hdq, hiff⟩
  · obtain ⟨a, rfl⟩ := (isOpenQuotientMap_unorderedProj (map e r f p)).surjective q
    have hne : a.val.2.1 ≠ a.val.2.2 :=
      fun he ↦ hq ((mem_diagonalOrbits_iff (map e r f p) a).mpr he)
    obtain ⟨c, hca, hdis⟩ :=
      exists_unordered_interior_chart e r f hf p hg S C hS hC hp hgen hinj hn a hne
    refine ⟨c.trans positiveHalfLine, ⟨hca, mem_univ _⟩, ?_⟩
    intro y hy
    change Real.exp (c y) = 0 ↔ y ∈ diagonalOrbits (map e r f p)
    exact iff_of_false (Real.exp_ne_zero _) ((disjoint_left.mp hdis) hy.1)

def unorderedChart (q : UnorderedClosedDoublePoints (map e r f p)) :
    OpenPartialHomeomorph (UnorderedClosedDoublePoints (map e r f p)) HalfLine :=
  (exists_unordered_halfLine_chart e r f hf p hg S C hS hC hp hgen hext hinj hn q).choose

theorem unorderedChart_mem_source (q : UnorderedClosedDoublePoints (map e r f p)) :
    q ∈ (unorderedChart e r f hf p hg S C hS hC hp hgen hext hinj hn q).source :=
  (exists_unordered_halfLine_chart e r f hf p hg S C hS hC hp hgen hext hinj hn q).choose_spec.1

theorem unorderedChart_zero_iff (q y : UnorderedClosedDoublePoints (map e r f p))
    (hy : y ∈ (unorderedChart e r f hf p hg S C hS hC hp hgen hext hinj hn q).source) :
    (unorderedChart e r f hf p hg S C hS hC hp hgen hext hinj hn q y).val = 0 ↔
      y ∈ diagonalOrbits (map e r f p) :=
  (exists_unordered_halfLine_chart e r f hf p hg S C hS hC hp hgen
    hext hinj hn q).choose_spec.2 y hy

@[instance_reducible]
def unorderedChartedSpace : ChartedSpace HalfLine (UnorderedClosedDoublePoints (map e r f p)) where
  atlas := range (unorderedChart e r f hf p hg S C hS hC hp hgen hext hinj hn)
  chartAt := unorderedChart e r f hf p hg S C hS hC hp hgen hext hinj hn
  mem_chart_source := unorderedChart_mem_source e r f hf p hg S C hS hC hp hgen hext hinj hn
  chart_mem_atlas q := ⟨q, rfl⟩

end NoExoticSixSphere.ManifoldAffineSphereFamily
