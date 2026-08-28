import Wikipedia.SmoothSixDPoincare.FaceDescentFramedBoundary
import Wikipedia.SmoothSixDPoincare.SmoothOpenSurgeryExterior
import Wikipedia.SmoothSixDPoincare.SurgeryExteriorDiffeomorphChange

/-!
# The corrected native face-descent realization has its exact smooth open exterior

The actual ambient boundary correction is the retained inverse native
isotopy. Composing it with the recorded smooth shrunk exterior gives
precisely the exterior map of the corrected surgery presentation.
-/

noncomputable section

open Set Function Topology
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.ManifoldMorse.MorseSurgeryData.FaceDescent.Realization

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ} {p : M} {d : MorseSurgeryData E f p}
  {hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f}
  {G H X N : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace H]
  {I : ModelWithCorners ℝ G H} [TopologicalSpace X] [ChartedSpace H X]
  [NormedAddCommGroup N] [InnerProductSpace ℝ N]
  {g : d.UpperSmoothFace hf I X N} {T : d.FaceDescent hf I X N g} (A : T.Realization)

def boundaryCorrectionDiffeomorph :
    letI := RegularLevel.chartedSpace hf d.upper_regular
    Diffeomorph 𝓘(ℝ, RegularLevel.Model E) 𝓘(ℝ, RegularLevel.Model E)
      d.UpperLevel d.UpperLevel ∞ := by
  let _ := RegularLevel.chartedSpace hf d.upper_regular
  exact {
    toEquiv := A.boundaryCorrection.toEquiv
    contMDiff_toFun := T.upperMap.symm.contMDiff.congr (fun x =>
      congrArg (fun h : d.UpperLevel ≃ₜ d.UpperLevel => h x) A.boundaryCorrection_eq_upperMap)
    contMDiff_invFun := T.upperMap.contMDiff.congr (fun x =>
      congrArg (fun h : d.UpperLevel ≃ₜ d.UpperLevel => h.symm x)
        A.boundaryCorrection_eq_upperMap) }

theorem boundaryCorrectionDiffeomorph_toHomeomorph :
    letI := RegularLevel.chartedSpace hf d.upper_regular
    A.boundaryCorrectionDiffeomorph.toHomeomorph = A.boundaryCorrection := rfl

def surgery := T.shrunk.surgery.changeNewBoundary A.boundaryCorrection

def openExteriorDiffeomorph :
    letI := RegularLevel.chartedSpace hf d.lower_regular
    letI := RegularLevel.chartedSpace hf d.upper_regular
    Diffeomorph 𝓘(ℝ, RegularLevel.Model E) 𝓘(ℝ, RegularLevel.Model E)
      A.surgery.oldOpenExterior A.surgery.newOpenExterior ∞ := by
  let _ := RegularLevel.chartedSpace hf d.lower_regular
  let _ := RegularLevel.chartedSpace hf d.upper_regular
  exact T.shrunk.surgery.changeOpenExteriorDiffeomorph A.boundaryCorrectionDiffeomorph
    (T.shrunk.openExteriorDiffeomorph hf T.smooth_exterior)

theorem openExteriorDiffeomorph_toHomeomorph :
    letI := RegularLevel.chartedSpace hf d.lower_regular
    letI := RegularLevel.chartedSpace hf d.upper_regular
    A.openExteriorDiffeomorph.toHomeomorph = A.surgery.openExteriorHomeomorph := by
  let _ := RegularLevel.chartedSpace hf d.lower_regular
  let _ := RegularLevel.chartedSpace hf d.upper_regular
  exact T.shrunk.surgery.changeOpenExteriorDiffeomorph_toHomeomorph
    A.boundaryCorrectionDiffeomorph (T.shrunk.openExteriorDiffeomorph hf T.smooth_exterior)
      (T.shrunk.openExteriorDiffeomorph_toHomeomorph hf T.smooth_exterior)

end Wikipedia.SmoothSixDPoincare.ManifoldMorse.MorseSurgeryData.FaceDescent.Realization
