import Wikipedia.NoExoticSixSphere.IntersectionTraceTransverseEnds
import Wikipedia.NoExoticSixSphere.IntersectionTraceInteriorChart

/-!
# Actual intersection parity for regular families without time collars

The constructed endpoint charts and regular interior charts cover the actual
compact trace. Evenness of its actual boundary gives finiteness and equality
of the endpoint intersection counts. No finite endpoint count, endpoint
injectivity, constant collar, or atlas on the trace is assumed.
-/

noncomputable section

open Set Function Topology
open scoped Manifold ContDiff

namespace NoExoticSixSphere.IntersectionTrace

open GLOrthonormalization MapIntersections InvolutionQuotient

variable {X Y Z : Type*} (f₀ : ℝ → X → Z) (g₀ : ℝ → Y → Z)

theorem finite_pairs_of_finite_ends (hfin : (ends f₀ g₀).Finite)
    (t : unitInterval) (ht : t = 0 ∨ t = 1) : (pairs (f₀ t) (g₀ t)).Finite := by
  let e : pairs (f₀ t) (g₀ t) → ends f₀ g₀ :=
    fun p ↦ ⟨endpoint f₀ g₀ t p, endpoint_mem_ends f₀ g₀ t ht p⟩
  have he : Injective e := fun p q h ↦
    endpoint_injective f₀ g₀ t (congrArg Subtype.val h)
  let := hfin.to_subtype
  exact finite_coe_iff.mp (Finite.of_injective e he)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  [IsManifold (𝓡 6) ∞ M]
  (f g : ℝ → Sphere 3 → M)
  (hf : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 6) ∞ (uncurry f))
  (hg : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 6) ∞ (uncurry g))
  (hreg : ChartRegular f g)
  (ht : ∀ t : unitInterval, t = 0 ∨ t = 1 → ∀ x y, f t x = g t y →
    Surjective ((mfderiv (𝓡 3) (𝓡 6) (f t) x).coprod
      (mfderiv (𝓡 3) (𝓡 6) (g t) y)))

include hf hg hreg ht in
theorem exists_regular_halfLine_chart (a : space f g) :
    ∃ d : OpenPartialHomeomorph (space f g) HalfLine,
      a ∈ d.source ∧ ∀ b ∈ d.source, (d b).val = 0 ↔ b ∈ ends f g := by
  by_cases ha0 : a.val.1 = 0
  · let p : pairs (f 0) (g 0) := ⟨a.val.2, by
      change f 0 a.val.2.1 = g 0 a.val.2.2
      simpa only [ha0] using a.property.2⟩
    have he : endpoint f g 0 p = a := Subtype.ext (Prod.ext ha0.symm rfl)
    obtain ⟨d, hda, _, hdB⟩ := exists_zero_halfLine_chart_of_transverse f g hf hg p
      (ht 0 (Or.inl rfl) _ _ p.property)
    exact ⟨d, he ▸ hda, hdB⟩
  · by_cases ha1 : a.val.1 = 1
    · let p : pairs (f 1) (g 1) := ⟨a.val.2, by
        change f 1 a.val.2.1 = g 1 a.val.2.2
        simpa only [ha1] using a.property.2⟩
      have he : endpoint f g 1 p = a := Subtype.ext (Prod.ext ha1.symm rfl)
      obtain ⟨d, hda, _, hdB⟩ := exists_one_halfLine_chart_of_transverse f g hf hg p
        (ht 1 (Or.inr rfl) _ _ p.property)
      exact ⟨d, he ▸ hda, hdB⟩
    · exact exists_interior_halfLine_chart f g hf hg hreg a (fun h ↦ h.elim ha0 ha1)

include hf hg hreg ht in
theorem finite_even_ends_of_regular_family [T2Space M] :
    (ends f g).Finite ∧ Even (ends f g).ncard := by
  let e (a : space f g) := (exists_regular_halfLine_chart f g hf hg hreg ht a).choose
  have he (a : space f g) : a ∈ (e a).source :=
    (exists_regular_halfLine_chart f g hf hg hreg ht a).choose_spec.1
  have hB (a : space f g) : ∀ b ∈ (e a).source, (e a b).val = 0 ↔ b ∈ ends f g :=
    (exists_regular_halfLine_chart f g hf hg hreg ht a).choose_spec.2
  let := compactSpace_space f g hf.continuous hg.continuous
  exact CurveDecomposition.finite_even_boundary_of_compact_atlas (ends f g) e he hB

include hf hg hreg ht in
theorem parity_eq_of_regular_family [T2Space M] :
    (pairs (f 0) (g 0)).Finite ∧ (pairs (f 1) (g 1)).Finite ∧
      parity (f 0) (g 0) = parity (f 1) (g 1) := by
  have h := finite_even_ends_of_regular_family f g hf hg hreg ht
  have h0 := finite_pairs_of_finite_ends f g h.1 0 (Or.inl rfl)
  have h1 := finite_pairs_of_finite_ends f g h.1 1 (Or.inr rfl)
  exact ⟨h0, h1, parity_eq_of_even_ends f g h0 h1 h.2⟩

end NoExoticSixSphere.IntersectionTrace
