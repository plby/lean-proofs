import Wikipedia.HopfProblem.DegreeCollapseNativeBeltCutFamily
import Wikipedia.SmoothSixDPoincare.MorseTransverseRepresentative
import Wikipedia.SmoothSixDPoincare.MorseBeltIntersectionReduction

/-!
# A unit native collapse coordinate gives one actual transverse belt intersection

Prepare the specified sphere by an actual level isotopy. Its homology
class is unchanged, so the native signed-count formula gives a unit count.
Finite Whitney reduction removes the cancelling pairs and retains the
composite isotopy from the original parametrized sphere.
-/

noncomputable section

open Set Function Manifold ContinuousMap Topology
open scoped ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse SupportedDiffeomorph

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

open SingularMayerVietoris PeriodTorusHigherHomology SphereHomology

local notation "S₂" => Hemisphere.Sphere 2

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] {f : M → ℝ} {p : M}

theorem exists_single_intersection_of_unit_coordinate
    (d : MorseSurgeryData E f p) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hdim : Module.finrank ℝ E = 6)
    (hindex : Module.finrank ℝ d.chart.NegativeCoordinates = 2)
    (hnull : ∀ δ : C(Hemisphere.Sphere 1, d.LowerLevel),
      ∃ z, δ.Homotopic (ContinuousMap.const _ z))
    (γ : C(S₂, d.UpperLevel)) :
    letI := RegularLevel.chartedSpace hf d.upper_regular
    ∀ (hγ : ContMDiff (𝓡 2) 𝓘(ℝ, RegularLevel.Model E) ∞ γ)
      (hinj : Injective γ)
      (himm : ∀ x, Injective (mfderiv (𝓡 2) 𝓘(ℝ, RegularLevel.Model E) γ x)),
      (d.indexTwoCollapseCoordinate hf.continuous hindex
        (middleSectionClass (f := f) (a := f p + d.radius ^ 2) γ)).natAbs = 1 →
      ∃ D : Diffeomorph 𝓘(ℝ, RegularLevel.Model E) 𝓘(ℝ, RegularLevel.Model E)
          d.UpperLevel d.UpperLevel ∞,
        ∃ δ : C(S₂, d.UpperLevel),
          IsotopicToIdentity D ∧ (∀ x, δ x = D (γ x)) ∧
          d.IsTransverseBeltSphere hf hdim hindex δ ∧
          (range δ ∩ range d.surgery.beltSphere).ncard = 1 := by
  let _ := RegularLevel.chartedSpace hf d.upper_regular
  intro hγ hinj himm hunit
  obtain ⟨D₀, γ₀, hD₀, hγ₀, hgood₀, hhom⟩ :=
    d.exists_transverse_representative hf hdim hindex γ hγ hinj himm
  have hmaps := homotopic_homologyMap hhom 2
  have hclass : middleSectionClass (f := f) (a := f p + d.radius ^ 2) γ₀ =
      middleSectionClass (f := f) (a := f p + d.radius ^ 2) γ := by
    simp only [middleSectionClass, singularHomologyMap_comp, LinearMap.comp_apply]
    rw [← hmaps]
  have hcount : (d.beltIntersectionCount 2 (d.beltNormalReference 2 hindex) γ₀
      (d.finite_points_of_isTransverseBeltSphere hf hdim hindex hgood₀)).natAbs = 1 := by
    rw [← d.indexTwoCoordinate_transverse_natAbs hf hdim hindex
      (d.beltNormalReference 2 hindex) γ₀ hgood₀]
    change (d.indexTwoCollapseCoordinate hf.continuous hindex
      (middleSectionClass (f := f) (a := f p + d.radius ^ 2) γ₀)).natAbs = 1
    rw [hclass]
    exact hunit
  obtain ⟨D₁, δ, x, hD₁, hδ, hgood, -, hinter⟩ :=
    d.exists_single_belt_intersection_of_unit_count hf hdim hindex hnull
      (d.beltNormalReference 2 hindex) γ₀ hgood₀ hcount
  refine ⟨D₀.trans D₁, δ, hD₀.trans hD₁,
    (fun x => (hδ x).trans (congrArg D₁ (hγ₀ x))), hgood, ?_⟩
  rw [hinter, Set.ncard_singleton]

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
