import Wikipedia.SmoothSixDPoincare.ShrunkAmbientExtension
import Wikipedia.SmoothSixDPoincare.RegularLevelSmoothMaps

/-!
# Smoothness of the exact exterior maps after shrinking

The retained ambient extension makes the original shrunk boundary map a
native diffeomorphism. Its exact inverse formula identifies the new backward
exterior with the original backward exterior after that diffeomorphism.
Thus smoothness transfers in both directions on the actual exterior domains.
-/

noncomputable section

open Set Manifold
open scoped ContDiff

namespace Wikipedia.SmoothSixDPoincare.ManifoldMorse.MorseSurgeryData
namespace ShrunkSurgeryRealization.AmbientExtension

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [FiniteDimensional ℝ E]
  [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ} {p : M}
  {d : MorseSurgeryData E f p} {a : ℝ} {R : d.ShrunkSurgeryRealization a}
  (H : R.AmbientExtension) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)

def boundaryDiffeomorph :
    letI := RegularLevel.chartedSpace hf d.upper_regular
    Diffeomorph 𝓘(ℝ, RegularLevel.Model E) 𝓘(ℝ, RegularLevel.Model E)
      d.UpperLevel d.UpperLevel ∞ := by
  let _ := RegularLevel.chartedSpace hf d.upper_regular
  refine {
    toEquiv := R.boundaryHomeomorph.toEquiv
    contMDiff_toFun := ?_
    contMDiff_invFun := ?_ }
  · apply (RegularLevel.contMDiff_iff_inclusion hf d.upper_regular
      𝓘(ℝ, RegularLevel.Model E) R.boundaryHomeomorph).mpr
    exact (H.ambient.contMDiff.comp
      (RegularLevel.contMDiff_inclusion hf d.upper_regular)).congr H.boundary_eq
  · apply (RegularLevel.contMDiff_iff_inclusion hf d.upper_regular
      𝓘(ℝ, RegularLevel.Model E) R.boundaryHomeomorph.symm).mpr
    exact (H.ambient.symm.contMDiff.comp
      (RegularLevel.contMDiff_inclusion hf d.upper_regular)).congr H.boundary_symm_eq

theorem boundaryDiffeomorph_toHomeomorph :
    letI := RegularLevel.chartedSpace hf d.upper_regular
    (H.boundaryDiffeomorph hf).toHomeomorph = R.boundaryHomeomorph := rfl

include H in
theorem hasSmoothExterior (hd : d.HasSmoothExterior hf) : R.HasSmoothExterior hf := by
  let _ := RegularLevel.chartedSpace hf d.lower_regular
  let _ := RegularLevel.chartedSpace hf d.upper_regular
  constructor
  · exact (H.ambient.contMDiff.comp_contMDiffOn hd.forward).congr
      (fun x _ => H.exteriorForward_eq x)
  · have hmaps : MapsTo R.boundaryHomeomorph.symm
        {x | R.exteriorBackward x ∉
          range (d.chart.attachingHandleMap d.radius d.radius_pos d.block)}
        {x | d.exteriorBackward x ∉
          range (d.chart.attachingHandleMap d.radius d.radius_pos d.block)} := by
      intro x hx
      change d.exteriorBackward (R.boundaryHomeomorph.symm x) ∉ _
      rw [← H.exteriorBackward_eq x]
      exact hx
    have h := hd.backward.comp (H.boundaryDiffeomorph hf).symm.contMDiff.contMDiffOn hmaps
    exact h.congr (fun x _ => H.exteriorBackward_eq x)

end ShrunkSurgeryRealization.AmbientExtension
end Wikipedia.SmoothSixDPoincare.ManifoldMorse.MorseSurgeryData
