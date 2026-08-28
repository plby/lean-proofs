import Wikipedia.SmoothSixDPoincare.MorseTransverseAttaching
import Wikipedia.SmoothSixDPoincare.TransverseBeltSphere
import Wikipedia.SmoothSixDPoincare.AmbientIsotopyHomology

/-!
# A transverse representative retaining the original level homotopy class

Apply native ambient transversality to a specified embedded immersed sphere,
retaining its actual ambient isotopy and the induced continuous homotopy.
In particular, this does not replace an already fixed band identification.
-/

noncomputable section

open Set Function ContinuousMap
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.ManifoldMorse.MorseSurgeryData

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]
  {f : M → ℝ} {p : M} (d : MorseSurgeryData E f p)
  (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)

theorem exists_transverse_representative (hdim : Module.finrank ℝ E = 6)
    (hindex : Module.finrank ℝ d.chart.NegativeCoordinates = 2)
    (g₀ : C(Hemisphere.Sphere 2, d.UpperLevel)) :
    letI := RegularLevel.chartedSpace hf d.upper_regular
    ∀ (_hg₀ : ContMDiff (𝓡 2) 𝓘(ℝ, RegularLevel.Model E) ∞ g₀)
      (_hinj : Injective g₀)
      (_himm : ∀ x, Injective (mfderiv (𝓡 2) 𝓘(ℝ, RegularLevel.Model E) g₀ x)),
      ∃ e : Diffeomorph 𝓘(ℝ, RegularLevel.Model E) 𝓘(ℝ, RegularLevel.Model E)
          d.UpperLevel d.UpperLevel ∞,
        ∃ g : C(Hemisphere.Sphere 2, d.UpperLevel),
          SupportedDiffeomorph.IsotopicToIdentity e ∧
          (∀ x, g x = e (g₀ x)) ∧ d.IsTransverseBeltSphere hf hdim hindex g ∧
          g₀.Homotopic g := by
  let _ := RegularLevel.chartedSpace hf d.upper_regular
  let _ := RegularLevel.isManifold hf d.upper_regular
  let _ : CompactSpace d.UpperLevel :=
    isCompact_iff_compactSpace.mp (isClosed_eq hf.continuous continuous_const).isCompact
  let _ : Fact (Module.finrank ℝ d.chart.PositiveCoordinates = 3 + 1) :=
    ⟨by have h := d.chart.finrank_negative_add_positive; omega⟩
  intro hg₀ hinj himm
  have hdim' : Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) +
      Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) =
        Module.finrank ℝ (RegularLevel.Model E) := by
    simp [RegularLevel.Model, hdim]
  obtain ⟨e, hiso, ht⟩ := NativeTransversality.exists_ambient_transverse_diffeomorph
    hg₀ (d.belt_smooth hf 3) hdim'
  let g := e.toHomeomorph.toHomotopyEquiv.toFun.comp g₀
  have hg : ContMDiff (𝓡 2) 𝓘(ℝ, RegularLevel.Model E) ∞ g := e.contMDiff.comp hg₀
  have hi : ∀ x, Injective (mfderiv (𝓡 2) 𝓘(ℝ, RegularLevel.Model E) g x) := by
    intro x
    change Injective (mfderiv (𝓡 2) 𝓘(ℝ, RegularLevel.Model E) (e ∘ g₀) x)
    rw [mfderiv_comp x (e.mdifferentiable (by simp) _) (hg₀.mdifferentiable (by simp) x)]
    exact ((e.toOpenPartialHomeomorph_mdifferentiable (by simp)).mfderiv_injective
      (by trivial)).comp (himm x)
  exact ⟨e, g, hiso, fun _ => rfl, ⟨hg, e.injective.comp hinj, hi, ht⟩,
    hiso.comp_homotopic g₀⟩

end Wikipedia.SmoothSixDPoincare.ManifoldMorse.MorseSurgeryData
