import Wikipedia.HopfProblem.DegreeCollapseThreeBeltIntersectionReduction
import Wikipedia.HopfProblem.DegreeCollapseIndexFourSectionClass

/-!
# Actual three-handle collapse coordinates give geometric belt reduction

First construct transversality by a native ambient isotopy. The actual sphere
class in the literal sublevel is unchanged. Its original collapse coordinate
equals the signed count in absolute value. The finite Whitney construction
therefore reduces the geometric count to the absolute original coordinate.
In particular, a unit coordinate gives one actual transverse crossing, with
no transverse representative, intersection count, or Whitney data supplied.
-/

noncomputable section

open Set Function Topology ContinuousMap
open scoped ContDiff Manifold
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

open SingularMayerVietoris

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} {p : M}
  (D : MorseSurgeryData E f p) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
  (hdim : Module.finrank ℝ E = 7)
  [Fact (Module.finrank ℝ D.chart.PositiveCoordinates = 3 + 1)]
  (hindex : Module.finrank ℝ D.chart.NegativeCoordinates = 3)
  (hnull : ∀ γ : C(Hemisphere.Sphere 1, D.LowerLevel),
    ∃ q, γ.Homotopic (ContinuousMap.const _ q))

include hdim hindex hnull

theorem exists_three_belt_reduction_of_original_coordinate
    (g : C(Hemisphere.Sphere 3, D.UpperLevel)) :
    letI := RegularLevel.chartedSpace hf D.upper_regular
    ContMDiff (𝓡 3) 𝓘(ℝ, RegularLevel.Model E) ∞ g → Injective g →
    (∀ x, Injective (mfderiv (𝓡 3) 𝓘(ℝ, RegularLevel.Model E) g x)) →
    ∃ e : Diffeomorph 𝓘(ℝ, RegularLevel.Model E) 𝓘(ℝ, RegularLevel.Model E)
        D.UpperLevel D.UpperLevel ∞,
      ∃ g' : C(Hemisphere.Sphere 3, D.UpperLevel),
        SupportedDiffeomorph.IsotopicToIdentity e ∧ (∀ x, g' x = e (g x)) ∧
        IsNativeTransverseBeltSphere D hf 3 3 g' ∧
        (D.beltIntersectionPoints 3 g').ncard =
          (MiddleBasis.collapseCoordinate D 1 hf.continuous hindex
            (threeSectionClass g)).natAbs := by
  let _ := RegularLevel.chartedSpace hf D.upper_regular
  intro hg hinj hi
  obtain ⟨e₀, g₀, hiso₀, heq₀, hgood₀, hhom⟩ :=
    exists_native_transverse_belt_representative D hf 3 3 hindex g hg hinj hi
  let r : (ℝ × D.chart.NegativeCoordinates) ≃L[ℝ] Hemisphere.Ambient 4 :=
    ContinuousLinearEquiv.ofFinrankEq (by simp [Module.finrank_prod, hindex])
  obtain ⟨e₁, g', hiso₁, heq₁, hgood', _, _, _, hsize⟩ :=
    exists_minimal_signed_three_belt_sphere D hf hdim hindex hnull r g₀ hgood₀
  have hclass : threeSectionClass g = threeSectionClass g₀ := threeSectionClass_homotopic hhom
  have hcoordinate := MiddleBasis.coordinate_native_transverse_natAbs D hf 3 1 hindex r g₀ hgood₀
  change (MiddleBasis.collapseCoordinate D 1 hf.continuous hindex (threeSectionClass g₀)).natAbs =
    (D.beltIntersectionCount 3 r g₀
      (finite_native_transverse_belt_points D hf 3 3 hindex hgood₀)).natAbs at hcoordinate
  refine ⟨e₀.trans e₁, g', hiso₀.trans hiso₁, ?_, hgood', ?_⟩
  · intro x
    change g' x = e₁ (e₀ (g x))
    rw [heq₁, heq₀]
  · exact hsize.trans (hcoordinate.symm.trans
      (congrArg (fun v => (MiddleBasis.collapseCoordinate D 1 hf.continuous hindex v).natAbs)
        hclass.symm))

theorem exists_single_three_belt_intersection_of_unit_coordinate
    (g : C(Hemisphere.Sphere 3, D.UpperLevel))
    (hunit : (MiddleBasis.collapseCoordinate D 1 hf.continuous hindex
      (threeSectionClass g)).natAbs = 1) :
    letI := RegularLevel.chartedSpace hf D.upper_regular
    ContMDiff (𝓡 3) 𝓘(ℝ, RegularLevel.Model E) ∞ g → Injective g →
    (∀ x, Injective (mfderiv (𝓡 3) 𝓘(ℝ, RegularLevel.Model E) g x)) →
    ∃ e : Diffeomorph 𝓘(ℝ, RegularLevel.Model E) 𝓘(ℝ, RegularLevel.Model E)
        D.UpperLevel D.UpperLevel ∞,
      ∃ g' : C(Hemisphere.Sphere 3, D.UpperLevel), ∃ x : Hemisphere.Sphere 3,
        SupportedDiffeomorph.IsotopicToIdentity e ∧ (∀ y, g' y = e (g y)) ∧
        IsNativeTransverseBeltSphere D hf 3 3 g' ∧
        D.beltIntersectionPoints 3 g' = {x} ∧
        range g' ∩ range D.surgery.beltSphere = {g' x} := by
  let _ := RegularLevel.chartedSpace hf D.upper_regular
  intro hg hinj hi
  obtain ⟨e, g', hiso, heq, hgood', hsize⟩ :=
    exists_three_belt_reduction_of_original_coordinate D hf hdim hindex hnull g hg hinj hi
  obtain ⟨x, hx⟩ := Set.ncard_eq_one.mp (hsize.trans hunit)
  refine ⟨e, g', x, hiso, heq, hgood', hx, ?_⟩
  have himage : g' '' D.beltIntersectionPoints 3 g' =
      range g' ∩ range D.surgery.beltSphere := by
    change g' '' (g' ⁻¹' range D.surgery.beltSphere) = _
    rw [Set.image_preimage_eq_inter_range, inter_comm]
  rw [← himage, hx, Set.image_singleton]

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
