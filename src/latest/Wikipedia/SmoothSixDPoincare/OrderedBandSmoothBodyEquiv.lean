import Wikipedia.SmoothSixDPoincare.NativeSmoothFramedRealization
import Wikipedia.SmoothSixDPoincare.OrderedBandSmooth
import Wikipedia.SmoothSixDPoincare.OrderedIsotopedSublevelBridge

/-!
# The retained regular band as an exact smooth boundary/body equivalence

The body map is the original retained band sublevel homeomorphism. Its
boundary diffeomorphism has exactly the recorded band level homeomorphism,
so consecutive native stages can use the same point maps throughout.
-/

noncomputable section

open Set Function Topology ContinuousMap
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.ManifoldMorse.SurgeryWindows.BandData

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ}
  {S : SurgeryWindows E f} {i j : Fin S.count} (B : S.BandData i j)
  (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)

def smoothBoundaryBodyEquiv :
    letI := RegularLevel.chartedSpace hf (S.data (S.point i)).upper_regular
    letI := RegularLevel.chartedSpace hf (S.data (S.point j)).lower_regular
    SmoothBoundaryBodyEquiv (J := 𝓘(ℝ, RegularLevel.Model E))
      (S.data (S.point i)).upperBodyInclusion (S.data (S.point j)).lowerBodyInclusion := by
  let _ := RegularLevel.chartedSpace hf (S.data (S.point i)).upper_regular
  let _ := RegularLevel.chartedSpace hf (S.data (S.point j)).lower_regular
  let b := Classical.choose (B.exists_levelDiffeomorph hf)
  have hb := Classical.choose_spec (B.exists_levelDiffeomorph hf)
  refine {
    body := B.sublevelHomeomorph
    boundary := b
    boundary_point := ?_ }
  intro x
  apply Subtype.ext
  exact (B.sublevelHomeomorph_on_level x).trans
    (congrArg (fun e : (S.data (S.point i)).UpperLevel ≃ₜ
        (S.data (S.point j)).LowerLevel => (e x).val) hb).symm

theorem smoothBoundaryBodyEquiv_body :
    letI := RegularLevel.chartedSpace hf (S.data (S.point i)).upper_regular
    letI := RegularLevel.chartedSpace hf (S.data (S.point j)).lower_regular
    (B.smoothBoundaryBodyEquiv hf).body = B.sublevelHomeomorph := rfl

theorem smoothBoundaryBodyEquiv_boundary :
    letI := RegularLevel.chartedSpace hf (S.data (S.point i)).upper_regular
    letI := RegularLevel.chartedSpace hf (S.data (S.point j)).lower_regular
    (B.smoothBoundaryBodyEquiv hf).boundary.toHomeomorph = B.level := by
  let _ := RegularLevel.chartedSpace hf (S.data (S.point i)).upper_regular
  let _ := RegularLevel.chartedSpace hf (S.data (S.point j)).lower_regular
  apply Homeomorph.ext
  intro x
  apply Subtype.ext
  have he := congrArg
    (fun y : {x : M // f x ≤ S.lower (S.point j)} => y.val)
      ((B.smoothBoundaryBodyEquiv hf).boundary_point x)
  exact he.symm.trans (B.sublevelHomeomorph_on_level x)

end Wikipedia.SmoothSixDPoincare.ManifoldMorse.SurgeryWindows.BandData
