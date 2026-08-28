import Wikipedia.SmoothSixDPoincare.FiniteMorseWhitneyReduction

/-!
# Zero and unit signed counts give actual geometric intersection reduction

The finite Whitney reduction removes all crossings when the original signed
count is zero, and leaves exactly one transverse crossing when its absolute
value is one. The original lower-level contraction hypothesis remains explicit;
no homological value of the signed count is postulated.
-/

noncomputable section

open Set Function Topology ContinuousMap
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.ManifoldMorse.MorseSurgeryData

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]
  {f : M → ℝ} {p : M} (D : MorseSurgeryData E f p)
  (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)

open Classical in
/-- An actual zero signed count gives a constructed disjoint sphere in the same isotopy class. -/
theorem exists_disjoint_belt_sphere_of_zero_count
    (hdim : Module.finrank ℝ E = 6)
    (hindex : Module.finrank ℝ D.chart.NegativeCoordinates = 2)
    (hnull : ∀ γ : C(Hemisphere.Sphere 1, D.LowerLevel),
      ∃ q, γ.Homotopic (ContinuousMap.const _ q))
    (r : (ℝ × D.chart.NegativeCoordinates) ≃L[ℝ] Hemisphere.Ambient 3)
    (g : C(Hemisphere.Sphere 2, D.UpperLevel))
    (hgood : D.IsTransverseBeltSphere hf hdim hindex g)
    (hcount : D.beltIntersectionCount 2 r g
      (D.finite_points_of_isTransverseBeltSphere hf hdim hindex hgood) = 0) :
    letI := RegularLevel.chartedSpace hf D.upper_regular
    ∃ e : Diffeomorph 𝓘(ℝ, RegularLevel.Model E) 𝓘(ℝ, RegularLevel.Model E)
        D.UpperLevel D.UpperLevel ∞,
      ∃ g' : C(Hemisphere.Sphere 2, D.UpperLevel),
        SupportedDiffeomorph.IsotopicToIdentity e ∧ (∀ x, g' x = e (g x)) ∧
        D.IsTransverseBeltSphere hf hdim hindex g' ∧
        Disjoint (range g') (range D.surgery.beltSphere) := by
  let _ := RegularLevel.chartedSpace hf D.upper_regular
  obtain ⟨e, g', hiso, heq, hgood', _, _, _, hsize⟩ :=
    D.exists_minimal_signed_belt_sphere hf hdim hindex hnull r g hgood
  have hz : (D.beltIntersectionPoints 2 g').ncard = 0 := by
    rw [hsize, hcount]
    rfl
  have hempty : D.beltIntersectionPoints 2 g' = ∅ :=
    (Set.ncard_eq_zero (D.finite_points_of_isTransverseBeltSphere hf hdim hindex hgood')).mp hz
  refine ⟨e, g', hiso, heq, hgood', Set.disjoint_left.mpr ?_⟩
  rintro z ⟨x, rfl⟩ hx
  have hp : x ∈ D.beltIntersectionPoints 2 g' := hx
  rw [hempty] at hp
  exact hp

open Classical in
/-- An actual unit signed count gives exactly one transverse geometric crossing. -/
theorem exists_single_belt_intersection_of_unit_count
    (hdim : Module.finrank ℝ E = 6)
    (hindex : Module.finrank ℝ D.chart.NegativeCoordinates = 2)
    (hnull : ∀ γ : C(Hemisphere.Sphere 1, D.LowerLevel),
      ∃ q, γ.Homotopic (ContinuousMap.const _ q))
    (r : (ℝ × D.chart.NegativeCoordinates) ≃L[ℝ] Hemisphere.Ambient 3)
    (g : C(Hemisphere.Sphere 2, D.UpperLevel))
    (hgood : D.IsTransverseBeltSphere hf hdim hindex g)
    (hcount : (D.beltIntersectionCount 2 r g
      (D.finite_points_of_isTransverseBeltSphere hf hdim hindex hgood)).natAbs = 1) :
    letI := RegularLevel.chartedSpace hf D.upper_regular
    ∃ e : Diffeomorph 𝓘(ℝ, RegularLevel.Model E) 𝓘(ℝ, RegularLevel.Model E)
        D.UpperLevel D.UpperLevel ∞,
      ∃ g' : C(Hemisphere.Sphere 2, D.UpperLevel), ∃ x : Hemisphere.Sphere 2,
        SupportedDiffeomorph.IsotopicToIdentity e ∧ (∀ y, g' y = e (g y)) ∧
        D.IsTransverseBeltSphere hf hdim hindex g' ∧
        D.beltIntersectionPoints 2 g' = {x} ∧
        range g' ∩ range D.surgery.beltSphere = {g' x} := by
  let _ := RegularLevel.chartedSpace hf D.upper_regular
  obtain ⟨e, g', hiso, heq, hgood', _, _, _, hsize⟩ :=
    D.exists_minimal_signed_belt_sphere hf hdim hindex hnull r g hgood
  have hone : (D.beltIntersectionPoints 2 g').ncard = 1 := hsize.trans hcount
  obtain ⟨x, hx⟩ := Set.ncard_eq_one.mp hone
  refine ⟨e, g', x, hiso, heq, hgood', hx, ?_⟩
  have himage : g' '' D.beltIntersectionPoints 2 g' =
      range g' ∩ range D.surgery.beltSphere := by
    change g' '' (g' ⁻¹' range D.surgery.beltSphere) = _
    rw [Set.image_preimage_eq_inter_range, inter_comm]
  rw [← himage, hx, Set.image_singleton]

end Wikipedia.SmoothSixDPoincare.ManifoldMorse.MorseSurgeryData
