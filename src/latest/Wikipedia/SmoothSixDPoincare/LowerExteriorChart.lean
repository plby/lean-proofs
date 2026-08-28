import Wikipedia.SmoothSixDPoincare.SmoothOpenSurgeryExterior
import Wikipedia.SmoothSixDPoincare.OpenDiffeomorphPartial

/-!
# Smooth chart neighborhoods of whole faces transported through the exterior

An original open chart is composed with the exact exterior diffeomorphism.
Every prescribed face point outside the closed belt tube remains in its open
source. The whole-sublevel identity identifies its value with the given lower
face, including boundary points of the closed disk parameters.
-/

noncomputable section

open Set Function
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.ManifoldMorse.MorseSurgeryData
namespace ShrunkSurgeryRealization

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [FiniteDimensional ℝ E]
  [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ} {p : M}
  {d : MorseSurgeryData E f p} {s : ℝ} (R : d.ShrunkSurgeryRealization s)
  (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hR : R.HasSmoothExterior hf)
  {G H X : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
  [TopologicalSpace H] (I : ModelWithCorners ℝ G H)
  [TopologicalSpace X] [ChartedSpace H X]

def lowerExteriorChart :
    letI := RegularLevel.chartedSpace hf d.lower_regular
    letI := RegularLevel.chartedSpace hf d.upper_regular
    PartialDiffeomorph I 𝓘(ℝ, RegularLevel.Model E) X d.UpperLevel ∞ →
      R.surgery.newOpenExterior →
        PartialDiffeomorph I 𝓘(ℝ, RegularLevel.Model E) X d.LowerLevel ∞ := by
  let _ := RegularLevel.chartedSpace hf d.lower_regular
  let _ := RegularLevel.chartedSpace hf d.upper_regular
  intro Θ y₀
  exact Θ.trans (OpenDiffeomorph.partialDiffeomorph (R.openExteriorDiffeomorph hf hR).symm y₀)

theorem lowerExteriorChart_source :
    letI := RegularLevel.chartedSpace hf d.lower_regular
    letI := RegularLevel.chartedSpace hf d.upper_regular
    ∀ (Θ : PartialDiffeomorph I 𝓘(ℝ, RegularLevel.Model E) X d.UpperLevel ∞)
      (y₀ : R.surgery.newOpenExterior),
      (R.lowerExteriorChart hf hR I Θ y₀).source =
        Θ.source ∩ {x | Θ x ∉ range R.surgery.newPiece} := by
  let _ := RegularLevel.chartedSpace hf d.lower_regular
  let _ := RegularLevel.chartedSpace hf d.upper_regular
  intro Θ y₀
  rfl

include hR in
theorem exists_lowerExteriorChart {Z : Type*} (j : Z → X) (z₀ : Z) (L : Z → d.LowerLevel) :
    letI := RegularLevel.chartedSpace hf d.lower_regular
    letI := RegularLevel.chartedSpace hf d.upper_regular
    ∀ Θ : PartialDiffeomorph I 𝓘(ℝ, RegularLevel.Model E) X d.UpperLevel ∞,
      (∀ z, j z ∈ Θ.source) →
      (∀ z, Θ (j z) ∉ d.closedBeltTube s) →
      (∀ z, (R.attachmentHomeomorph ⟨(L z).val, Or.inl (L z).property.le⟩).val =
        (Θ (j z)).val) →
      ∃ Ψ : PartialDiffeomorph I 𝓘(ℝ, RegularLevel.Model E) X d.LowerLevel ∞,
        (∀ z, j z ∈ Ψ.source) ∧ (∀ z, Ψ (j z) = L z) ∧
          Ψ.target ⊆ (range d.surgery.oldPiece)ᶜ := by
  let _ := RegularLevel.chartedSpace hf d.lower_regular
  let _ := RegularLevel.chartedSpace hf d.upper_regular
  intro Θ hsource havoid hmap
  have hnew (z : Z) : Θ (j z) ∉ range R.surgery.newPiece := by
    rw [R.newPiece_range]
    exact havoid z
  let y₀ : R.surgery.newOpenExterior := ⟨Θ (j z₀), hnew z₀⟩
  let Ψ := R.lowerExteriorChart hf hR I Θ y₀
  refine ⟨Ψ, fun z => ⟨hsource z, hnew z⟩, ?_, ?_⟩
  · intro z
    let y : R.surgery.newOpenExterior := ⟨Θ (j z), hnew z⟩
    have hp := OpenDiffeomorph.partialDiffeomorph_apply
      (R.openExteriorDiffeomorph hf hR).symm y₀ y
    apply Subtype.ext
    calc
      (Ψ (j z)).val = (R.surgery.openExteriorHomeomorph.symm y).val.val :=
        congrArg Subtype.val hp
      _ = R.exteriorBackward (Θ (j z)) := (R.exteriorBackward_openExterior y).symm
      _ = (L z).val := R.exteriorBackward_eq_of_attachment (L z) (Θ (j z)) (hmap z)
  · intro y hy
    exact hy.1

end ShrunkSurgeryRealization
end Wikipedia.SmoothSixDPoincare.ManifoldMorse.MorseSurgeryData
