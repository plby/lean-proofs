import Wikipedia.HopfProblem.DegreeCollapseFiniteThreeBeltReduction

/-!
# Zero and unit three-belt signed counts give actual geometric reduction

The finite native Whitney sequence removes every intersection for count zero
and leaves exactly one transverse intersection for absolute count one.
-/

noncomputable section

open Set Function Topology ContinuousMap
open scoped ContDiff Manifold
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} {p : M}
  (D : MorseSurgeryData E f p) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
  (hdim : Module.finrank ℝ E = 7)
  [Fact (Module.finrank ℝ D.chart.PositiveCoordinates = 3 + 1)]
  (hindex : Module.finrank ℝ D.chart.NegativeCoordinates = 3)
  (hnull : ∀ γ : C(Hemisphere.Sphere 1, D.LowerLevel),
    ∃ q, γ.Homotopic (ContinuousMap.const _ q))
  (r : (ℝ × D.chart.NegativeCoordinates) ≃L[ℝ] Hemisphere.Ambient 4)

include hdim hindex hnull

theorem exists_disjoint_three_belt_sphere_of_zero_count
    (g : C(Hemisphere.Sphere 3, D.UpperLevel))
    (hgood : IsNativeTransverseBeltSphere D hf 3 3 g)
    (hcount : D.beltIntersectionCount 3 r g
      (finite_native_transverse_belt_points D hf 3 3 hindex hgood) = 0) :
    letI := RegularLevel.chartedSpace hf D.upper_regular
    ∃ e : Diffeomorph 𝓘(ℝ, RegularLevel.Model E) 𝓘(ℝ, RegularLevel.Model E)
        D.UpperLevel D.UpperLevel ∞,
      ∃ g' : C(Hemisphere.Sphere 3, D.UpperLevel),
        SupportedDiffeomorph.IsotopicToIdentity e ∧ (∀ x, g' x = e (g x)) ∧
        IsNativeTransverseBeltSphere D hf 3 3 g' ∧
        Disjoint (range g') (range D.surgery.beltSphere) := by
  let _ := RegularLevel.chartedSpace hf D.upper_regular
  obtain ⟨e, g', hiso, heq, hgood', _, _, _, hsize⟩ :=
    exists_minimal_signed_three_belt_sphere D hf hdim hindex hnull r g hgood
  have hz : (D.beltIntersectionPoints 3 g').ncard = 0 := by
    rw [hsize, hcount]
    rfl
  have hempty : D.beltIntersectionPoints 3 g' = ∅ :=
    (Set.ncard_eq_zero (finite_native_transverse_belt_points D hf 3 3 hindex hgood')).mp hz
  refine ⟨e, g', hiso, heq, hgood', Set.disjoint_left.mpr ?_⟩
  rintro z ⟨x, rfl⟩ hx
  have hp : x ∈ D.beltIntersectionPoints 3 g' := hx
  rw [hempty] at hp
  exact hp

theorem exists_single_three_belt_intersection_of_unit_count
    (g : C(Hemisphere.Sphere 3, D.UpperLevel))
    (hgood : IsNativeTransverseBeltSphere D hf 3 3 g)
    (hcount : (D.beltIntersectionCount 3 r g
      (finite_native_transverse_belt_points D hf 3 3 hindex hgood)).natAbs = 1) :
    letI := RegularLevel.chartedSpace hf D.upper_regular
    ∃ e : Diffeomorph 𝓘(ℝ, RegularLevel.Model E) 𝓘(ℝ, RegularLevel.Model E)
        D.UpperLevel D.UpperLevel ∞,
      ∃ g' : C(Hemisphere.Sphere 3, D.UpperLevel), ∃ x : Hemisphere.Sphere 3,
        SupportedDiffeomorph.IsotopicToIdentity e ∧ (∀ y, g' y = e (g y)) ∧
        IsNativeTransverseBeltSphere D hf 3 3 g' ∧
        D.beltIntersectionPoints 3 g' = {x} ∧
        range g' ∩ range D.surgery.beltSphere = {g' x} := by
  let _ := RegularLevel.chartedSpace hf D.upper_regular
  obtain ⟨e, g', hiso, heq, hgood', _, _, _, hsize⟩ :=
    exists_minimal_signed_three_belt_sphere D hf hdim hindex hnull r g hgood
  have hone : (D.beltIntersectionPoints 3 g').ncard = 1 := hsize.trans hcount
  obtain ⟨x, hx⟩ := Set.ncard_eq_one.mp hone
  refine ⟨e, g', x, hiso, heq, hgood', hx, ?_⟩
  have himage : g' '' D.beltIntersectionPoints 3 g' =
      range g' ∩ range D.surgery.beltSphere := by
    change g' '' (g' ⁻¹' range D.surgery.beltSphere) = _
    rw [Set.image_preimage_eq_inter_range, inter_comm]
  rw [← himage, hx, Set.image_singleton]

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
