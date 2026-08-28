import Wikipedia.NoExoticSixSphere.IntersectionTraceInteriorChart
import Wikipedia.NoExoticSixSphere.IntersectionTraceTimeReverse

/-!
# Intersection-count invariance for an actual regular collared family

The half-line atlas is assembled from constructed endpoint and interior
charts on the original compact trace. Its boundary is precisely the two
time ends. Evenness of that actual boundary proves equality of the endpoint
intersection counts. The chart-derivative regularity hypothesis is explicit;
existence of a suitable perturbation of an arbitrary homotopy is not asserted.
-/

noncomputable section

open Set Function Topology
open scoped Manifold ContDiff

namespace NoExoticSixSphere.IntersectionTrace

open GLOrthonormalization MapIntersections InvolutionQuotient

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  (f g : ℝ → Sphere 3 → M)
  (hf : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 6) ∞ (uncurry f))
  (hg : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 6) ∞ (uncurry g))
  (hreg : ChartRegular f g) (c : ℝ) (hc : c ≤ 1) (hcpos : 0 < c)
  (hcoll0 : ∀ t ∈ Icc 0 c, pairs (f t) (g t) = pairs (f 0) (g 0))
  (hcoll1 : ∀ t ∈ Icc 0 c, pairs (f (1 - t)) (g (1 - t)) = pairs (f 1) (g 1))
  (h0 : (pairs (f 0) (g 0)).Finite) (h1 : (pairs (f 1) (g 1)).Finite)

include hf hg hreg hc hcpos hcoll0 hcoll1 h0 h1 in
theorem exists_halfLine_chart (a : space f g) :
    ∃ d : OpenPartialHomeomorph (space f g) HalfLine,
      a ∈ d.source ∧ ∀ b ∈ d.source, (d b).val = 0 ↔ b ∈ ends f g := by
  by_cases ha0 : a.val.1 = 0
  · let p : pairs (f 0) (g 0) := ⟨a.val.2, by
      change f 0 a.val.2.1 = g 0 a.val.2.2
      simpa only [ha0] using a.property.2⟩
    have he : endpoint f g 0 p = a := Subtype.ext (Prod.ext ha0.symm rfl)
    obtain ⟨d, hda, _, hdB⟩ := exists_zero_halfLine_chart f g p c hc hcoll0 hcpos h0
    exact ⟨d, he ▸ hda, hdB⟩
  · by_cases ha1 : a.val.1 = 1
    · let p : pairs (f 1) (g 1) := ⟨a.val.2, by
        change f 1 a.val.2.1 = g 1 a.val.2.2
        simpa only [ha1] using a.property.2⟩
      have he : endpoint f g 1 p = a := Subtype.ext (Prod.ext ha1.symm rfl)
      obtain ⟨d, hda, _, hdB⟩ := exists_one_halfLine_chart f g p c hc hcpos hcoll1 h1
      exact ⟨d, he ▸ hda, hdB⟩
    · exact exists_interior_halfLine_chart f g hf hg hreg a (fun h ↦ h.elim ha0 ha1)

include hf hg hreg hc hcpos hcoll0 hcoll1 h0 h1 in
/-- Regularity and actual endpoint collars construct the atlas used in this
parity theorem; neither an atlas nor an evenness hypothesis is supplied. -/
theorem parity_eq_of_regular_collared_family [T2Space M] :
    parity (f 0) (g 0) = parity (f 1) (g 1) := by
  let e (a : space f g) :=
    (exists_halfLine_chart f g hf hg hreg c hc hcpos hcoll0 hcoll1 h0 h1 a).choose
  have he (a : space f g) : a ∈ (e a).source :=
    (exists_halfLine_chart f g hf hg hreg c hc hcpos hcoll0 hcoll1 h0 h1 a).choose_spec.1
  have hB (a : space f g) : ∀ b ∈ (e a).source, (e a b).val = 0 ↔ b ∈ ends f g :=
    (exists_halfLine_chart f g hf hg hreg c hc hcpos hcoll0 hcoll1 h0 h1 a).choose_spec.2
  exact parity_eq_of_halfLine_atlas f g hf.continuous hg.continuous h0 h1 e he hB

include hf hg hreg hc hcpos hcoll0 hcoll1 in
/-- Native transversality of the embedded endpoint spheres discharges the
finiteness hypotheses. Only interior regularity and the genuine collars remain. -/
theorem parity_eq_of_transverse_collared_family [T2Space M] [CompactSpace M]
    [IsManifold (𝓡 6) ∞ M]
    (hi : ∀ t : unitInterval, t = 0 ∨ t = 1 → Injective (f t))
    (hj : ∀ t : unitInterval, t = 0 ∨ t = 1 → Injective (g t))
    (ht : ∀ t : unitInterval, t = 0 ∨ t = 1 → ∀ x y, f t x = g t y →
      Surjective ((mfderiv (𝓡 3) (𝓡 6) (f t) x).coprod
        (mfderiv (𝓡 3) (𝓡 6) (g t) y))) :
    parity (f 0) (g 0) = parity (f 1) (g 1) := by
  have hfin (t : unitInterval) (he : t = 0 ∨ t = 1) : (pairs (f t) (g t)).Finite :=
    finite_transverse_sphere_pairs
      (hf.comp (contMDiff_const.prodMk contMDiff_id))
      (hg.comp (contMDiff_const.prodMk contMDiff_id)) (hi t he) (hj t he) (ht t he)
  exact parity_eq_of_regular_collared_family f g hf hg hreg c hc hcpos hcoll0 hcoll1
    (hfin 0 (Or.inl rfl)) (hfin 1 (Or.inr rfl))

end NoExoticSixSphere.IntersectionTrace
