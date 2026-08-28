import Wikipedia.HopfProblem.DegreeCollapseIndexCoordinateCount
import Wikipedia.SmoothSixDPoincare.MorseTransverseRepresentative

/-!
# Native transverse belt representatives in the actual complementary dimensions

Ambient transversality constructs an isotopic representative of the
original embedded immersive sphere. The original native regular-level
atlas remains fixed. Smoothness, embedding, immersion, and the continuous
homotopy are retained, and the actual intersection set is finite. This
applies in particular to three-spheres and three-belts in dimension six.
-/

noncomputable section

open Set Function ContinuousMap
open scoped ContDiff Manifold
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

open SingularMayerVietoris SphereHomology

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ} {p : M}
  (d : MorseSurgeryData E f p) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)

def IsNativeTransverseBeltSphere (q m : ℕ)
    [Fact (Module.finrank ℝ d.chart.PositiveCoordinates = q + 1)]
    (γ : C(Hemisphere.Sphere m, d.UpperLevel)) : Prop :=
  letI := RegularLevel.chartedSpace hf d.upper_regular
  ContMDiff (𝓡 m) 𝓘(ℝ, RegularLevel.Model E) ∞ γ ∧ Injective γ ∧
    (∀ x, Injective (mfderiv (𝓡 m) 𝓘(ℝ, RegularLevel.Model E) γ x)) ∧
    ∀ x y, NativeTransversality.At (𝓡 m) (𝓡 q) 𝓘(ℝ, RegularLevel.Model E)
      γ d.surgery.beltSphere x y

variable [T2Space M] [CompactSpace M]

theorem finite_native_transverse_belt_points (q m : ℕ)
    [Fact (Module.finrank ℝ d.chart.PositiveCoordinates = q + 1)]
    (hindex : Module.finrank ℝ d.chart.NegativeCoordinates = m)
    {γ : C(Hemisphere.Sphere m, d.UpperLevel)}
    (hγ : IsNativeTransverseBeltSphere d hf q m γ) :
    (d.beltIntersectionPoints m γ).Finite := by
  let _ := RegularLevel.chartedSpace hf d.upper_regular
  obtain ⟨hs, hinj, _, ht⟩ := hγ
  exact d.finite_beltIntersectionPoints hf q m hindex γ hs hinj ht

theorem exists_native_transverse_belt_representative (q m : ℕ)
    [Fact (Module.finrank ℝ d.chart.PositiveCoordinates = q + 1)]
    (hindex : Module.finrank ℝ d.chart.NegativeCoordinates = m)
    (γ₀ : C(Hemisphere.Sphere m, d.UpperLevel)) :
    letI := RegularLevel.chartedSpace hf d.upper_regular
    ∀ (_hγ₀ : ContMDiff (𝓡 m) 𝓘(ℝ, RegularLevel.Model E) ∞ γ₀)
      (_hinj : Injective γ₀)
      (_himm : ∀ x, Injective (mfderiv (𝓡 m) 𝓘(ℝ, RegularLevel.Model E) γ₀ x)),
      ∃ D : Diffeomorph 𝓘(ℝ, RegularLevel.Model E) 𝓘(ℝ, RegularLevel.Model E)
          d.UpperLevel d.UpperLevel ∞,
        ∃ γ : C(Hemisphere.Sphere m, d.UpperLevel),
          SupportedDiffeomorph.IsotopicToIdentity D ∧
          (∀ x, γ x = D (γ₀ x)) ∧ IsNativeTransverseBeltSphere d hf q m γ ∧
          γ₀.Homotopic γ := by
  let _ := RegularLevel.chartedSpace hf d.upper_regular
  let _ := RegularLevel.isManifold hf d.upper_regular
  let _ : CompactSpace d.UpperLevel :=
    isCompact_iff_compactSpace.mp (isClosed_eq hf.continuous continuous_const).isCompact
  intro hγ₀ hinj himm
  have hsum := d.chart.finrank_negative_add_positive
  have hp := Fact.out (p := Module.finrank ℝ d.chart.PositiveCoordinates = q + 1)
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin m)) +
      Module.finrank ℝ (EuclideanSpace ℝ (Fin q)) =
        Module.finrank ℝ (RegularLevel.Model E) := by
    simp only [RegularLevel.Model, finrank_euclideanSpace_fin]
    omega
  obtain ⟨D, hD, ht⟩ := NativeTransversality.exists_ambient_transverse_diffeomorph
    hγ₀ (d.belt_smooth hf q) hdim
  let γ := D.toHomeomorph.toHomotopyEquiv.toFun.comp γ₀
  have hγ : ContMDiff (𝓡 m) 𝓘(ℝ, RegularLevel.Model E) ∞ γ := D.contMDiff.comp hγ₀
  have hi (x : Hemisphere.Sphere m) :
      Injective (mfderiv (𝓡 m) 𝓘(ℝ, RegularLevel.Model E) γ x) := by
    change Injective (mfderiv (𝓡 m) 𝓘(ℝ, RegularLevel.Model E) (D ∘ γ₀) x)
    rw [mfderiv_comp x (D.mdifferentiable (by simp) _) (hγ₀.mdifferentiable (by simp) x)]
    exact ((D.toOpenPartialHomeomorph_mdifferentiable (by simp)).mfderiv_injective
      (by trivial)).comp (himm x)
  exact ⟨D, γ, hD, fun _ => rfl, ⟨hγ, D.injective.comp hinj, hi, ht⟩,
    hD.comp_homotopic γ₀⟩

theorem MiddleBasis.coordinate_native_transverse_natAbs (q k : ℕ)
    [Fact (Module.finrank ℝ d.chart.PositiveCoordinates = q + 1)]
    (hindex : Module.finrank ℝ d.chart.NegativeCoordinates = k + 2)
    (j : (ℝ × d.chart.NegativeCoordinates) ≃L[ℝ] Hemisphere.Ambient ((k + 2) + 1))
    (γ : C(Hemisphere.Sphere (k + 2), d.UpperLevel))
    (hγ : IsNativeTransverseBeltSphere d hf q (k + 2) γ) :
    (MiddleBasis.collapseCoordinate d k hf.continuous hindex
      (singularHomologyMap (d.upperLevelInclusion.comp γ) (k + 2)
        (unitSphereTopClass (k + 1)))).natAbs =
    (d.beltIntersectionCount (k + 2) j γ
      (finite_native_transverse_belt_points d hf q (k + 2) hindex hγ)).natAbs := by
  let _ := RegularLevel.chartedSpace hf d.upper_regular
  obtain ⟨hs, hinj, _, ht⟩ := hγ
  exact MiddleBasis.coordinate_topClass_natAbs d hf q k hindex j γ hs hinj ht

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
