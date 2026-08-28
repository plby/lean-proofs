import Wikipedia.NoExoticSixSphere.ManifoldAffineWindowBoundary
import Wikipedia.NoExoticSixSphere.ManifoldAffineSingularBoundary
import Wikipedia.NoExoticSixSphere.ClosedTimeWindowBoundaryCount
import Wikipedia.NoExoticSixSphere.SphereFamilyUnorderedTimeFiber

/-!
# Actual endpoint double-point counts differ by the singularity count

The compact unordered window boundary is the disjoint sum of actual
singular diagonal orbits and the two endpoint double-point orbit sets.
Its even cardinality gives the mod-two relation for self-transverse
immersed endpoints. Exterior slices need only be immersive.
-/

noncomputable section

open Set Function Topology
open scoped Manifold ContDiff

namespace NoExoticSixSphere.ManifoldAffineSphereFamily

open GLOrthonormalization EuclideanEmbedding FamilyEmbedding SphereFamily

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  [IsManifold (𝓡 6) ∞ M]
  (e : EuclideanEmbedding 6 M) (r : TubularRetraction e) (f : ℝ → Sphere 3 → M)
  (hf : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 6) ∞ (uncurry f)) (p : Parameters e)
  (hg : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 6) ∞ (uncurry (map e r f p)))
  (S : Set SourceChart) (C : Set (TargetChart 6 M))
  (hS : ∀ x : Sphere 3, ∃ s ∈ S, x ∈ s.source)
  (hC : ∀ x : M, ∃ c ∈ C, x ∈ c.source)
  (hp : ∀ t x, ambient e f p t x ∈ r.domain)
  (hgen : GenericInCharts e r f hf S C p)
  (hext : ∀ t, t ≤ 0 ∨ 1 ≤ t → ∀ x,
    Injective (mfderiv (𝓡 3) (𝓡 6) (f t) x))
  (ht : ∀ t, t = 0 ∨ t = 1 → ∀ x y, x ≠ y → f t x = f t y → Surjective
    ((mfderiv (𝓡 3) (𝓡 6) (f t) x).coprod (mfderiv (𝓡 3) (𝓡 6) (f t) y)))

include hext in
theorem injective_mfderiv_map_at_ends (t : ℝ) (ht : t = 0 ∨ t = 1) (x : Sphere 3) :
    Injective (mfderiv (𝓡 3) (𝓡 6) (map e r f p t) x) := by
  apply injective_mfderiv_map_outside e r f p hext
  rcases ht with rfl | rfl
  · exact Or.inl le_rfl
  · exact Or.inr le_rfl

include ht in
theorem selfTransverse_map_at_ends (t : ℝ) (htime : t = 0 ∨ t = 1)
    (x y : Sphere 3) (hne : x ≠ y) (heq : map e r f p t x = map e r f p t y) :
    Surjective ((mfderiv (𝓡 3) (𝓡 6) (map e r f p t) x).coprod
      (mfderiv (𝓡 3) (𝓡 6) (map e r f p t) y)) := by
  have hout : t ≤ 0 ∨ 1 ≤ t := by
    rcases htime with rfl | rfl
    · exact Or.inl le_rfl
    · exact Or.inr le_rfl
  have he : map e r f p t = f t := funext (map_eq_outside e r f p hout)
  rw [he] at heq ⊢
  exact ht t htime x y hne heq

include hg hext in
theorem diagonalOrbits_time_mem_Ioo (q : UnorderedClosedDoublePoints (map e r f p))
    (hq : q ∈ diagonalOrbits (map e r f p)) :
    unorderedTime (map e r f p) q ∈ Ioo (0 : ℝ) 1 := by
  obtain ⟨a, hdiag, rfl⟩ := hq
  rcases a with ⟨⟨t, x, y⟩, hcl⟩
  change x = y at hdiag
  subst y
  exact singularParameters_time_mem_Ioo e r f p hext
    (SphereFamily.singular_of_diagonal_mem_closure (map e r f p) hg (t, x) hcl)

include hg hS hC hp hgen hext ht in
theorem finite_singularParameters_of_selfTransverse_ends :
    (singularParameters (n := 6) (map e r f p)).Finite := by
  have hb := finite_even_unordered_window_boundary e r f hf p hg S C hS hC hp hgen
    (injective_mfderiv_map_at_ends e r f p hext) (selfTransverse_map_at_ends e r f p ht)
  let := hb.1.to_subtype
  let T := ClosedTimeWindow.partsToBoundary (unorderedTime (map e r f p))
    (diagonalOrbits (map e r f p)) (diagonalOrbits_time_mem_Ioo e r f p hg hext)
  have hT := ClosedTimeWindow.partsToBoundary_injective (unorderedTime (map e r f p))
    (diagonalOrbits (map e r f p)) (diagonalOrbits_time_mem_Ioo e r f p hg hext)
  have hfin : Finite (singularParameters (n := 6) (map e r f p)) := Finite.of_injective
    (T ∘ Sum.inl ∘ singularOrbit e r f hf p hg S C hS hC hp hgen hext)
    (hT.comp (Sum.inl_injective.comp
      (injective_singularOrbit e r f hf p hg S C hS hC hp hgen hext)))
  exact finite_coe_iff.mp hfin

include hg hS hC hp hgen hext ht in
theorem unorderedParity_endpoint_sum :
    SphereSelfIntersections.unorderedParity (map e r f p 0) +
      SphereSelfIntersections.unorderedParity (map e r f p 1) =
        (Nat.card (singularParameters (n := 6) (map e r f p)) : ZMod 2) := by
  let : T2Space M := e.closedEmbedding.isEmbedding.t2Space
  have hd := injective_mfderiv_map_at_ends e r f p hext
  have hb := finite_even_unordered_window_boundary e r f hf p hg S C hS hC hp hgen
    hd (selfTransverse_map_at_ends e r f p ht)
  have hcard := ClosedTimeWindow.boundary_ncard (unorderedTime (map e r f p))
    (diagonalOrbits (map e r f p)) (diagonalOrbits_time_mem_Ioo e r f p hg hext) hb.1
  rw [← singularBoundary_card e r f hf p hg S C hS hC hp hgen hext,
    unorderedTimeFiber_card (map e r f p) 0 hg (hd 0 (.inl rfl)),
    unorderedTimeFiber_card (map e r f p) 1 hg (hd 1 (.inr rfl))] at hcard
  have hz := ZMod.natCast_eq_zero_iff_even.mpr hb.2
  rw [hcard, Nat.cast_add, Nat.cast_add] at hz
  have he := eq_neg_of_add_eq_zero_right hz
  rw [ZMod.neg_eq_self_mod_two] at he
  exact he

end NoExoticSixSphere.ManifoldAffineSphereFamily
