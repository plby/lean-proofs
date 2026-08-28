import Wikipedia.NoExoticSixSphere.FamilyDoublePointCompactness
import Wikipedia.NoExoticSixSphere.ManifoldAffineGenericParameter

/-!
# A constructed compact container for the actual manifold-family double points

For compact source, injectivity of every exterior-time slice puts all actual
double points in the compact unit-time cylinder. Their original closure and
unordered quotient are therefore compact. Endpoint-relative perturbations
inherit the exterior injectivity exactly; no container is assumed.
-/

open Set Function

namespace NoExoticSixSphere.FamilyEmbedding

variable {X Y : Type*}

theorem doublePoints_time_mem_Ioo (f : ℝ → X → Y)
    (hext : ∀ t, t ≤ 0 ∨ 1 ≤ t → Injective (f t))
    {q : ℝ × (X × X)} (hq : q ∈ doublePoints f) : q.1 ∈ Ioo (0 : ℝ) 1 := by
  by_contra ht
  have hout : q.1 ≤ 0 ∨ 1 ≤ q.1 := by
    simpa only [mem_Ioo, not_and_or, not_lt] using ht
  exact hq.1 (hext q.1 hout hq.2)

theorem doublePoints_subset_time_cylinder (f : ℝ → X → Y)
    (hext : ∀ t, t ≤ 0 ∨ 1 ≤ t → Injective (f t)) :
    doublePoints f ⊆ Icc (0 : ℝ) 1 ×ˢ (univ : Set (X × X)) := by
  intro q hq
  exact ⟨Ioo_subset_Icc_self (doublePoints_time_mem_Ioo f hext hq), mem_univ _⟩

variable [TopologicalSpace X] [T2Space X] [CompactSpace X]

theorem isCompact_closure_doublePoints_of_exterior_injective (f : ℝ → X → Y)
    (hext : ∀ t, t ≤ 0 ∨ 1 ≤ t → Injective (f t)) :
    IsCompact (closure (doublePoints f)) := by
  have hK : IsCompact (Icc (0 : ℝ) 1 ×ˢ (univ : Set (X × X))) :=
    isCompact_Icc.prod isCompact_univ
  exact hK.of_isClosed_subset isClosed_closure
    (closure_minimal (doublePoints_subset_time_cylinder f hext) hK.isClosed)

theorem compactSpace_unordered_of_exterior_injective (f : ℝ → X → Y)
    (hext : ∀ t, t ≤ 0 ∨ 1 ≤ t → Injective (f t)) :
    CompactSpace (UnorderedClosedDoublePoints f) :=
  compactSpace_unordered_of_compact_container f (isCompact_Icc.prod isCompact_univ)
    (doublePoints_subset_time_cylinder f hext)

end NoExoticSixSphere.FamilyEmbedding

open scoped Manifold ContDiff

namespace NoExoticSixSphere.ManifoldAffineSphereFamily

open GLOrthonormalization EuclideanEmbedding FamilyEmbedding

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector n) M]
  (e : EuclideanEmbedding n M) (r : TubularRetraction e) (f : ℝ → Sphere 3 → M)

theorem injective_map_outside (p : Parameters e)
    (hext : ∀ t, t ≤ 0 ∨ 1 ≤ t → Injective (f t)) {t : ℝ} (ht : t ≤ 0 ∨ 1 ≤ t) :
    Injective (map e r f p t) := by
  intro x y hxy
  apply hext t ht
  simpa only [map_eq_outside e r f p ht] using hxy

theorem compactSpace_unordered_map (p : Parameters e)
    (hext : ∀ t, t ≤ 0 ∨ 1 ≤ t → Injective (f t)) :
    CompactSpace (UnorderedClosedDoublePoints (map e r f p)) :=
  compactSpace_unordered_of_exterior_injective (map e r f p)
    (fun _ ht ↦ injective_map_outside e r f p hext ht)

end NoExoticSixSphere.ManifoldAffineSphereFamily
