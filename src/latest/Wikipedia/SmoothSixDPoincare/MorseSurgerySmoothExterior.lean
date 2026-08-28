import Wikipedia.SmoothSixDPoincare.SmoothMorseSurgery

/-!
# Smooth exterior data for the same native Morse surgery realization

The maps are restrictions of the recorded whole-sublevel homeomorphism and
its inverse. The predicate adds smoothness only outside the actual closed
handle piece, using the recorded regular levels' native smooth atlases.
It does not change the underlying surgery or assert that every topological
surgery realization has this property.
-/

noncomputable section

open Set Manifold
open scoped ContDiff

namespace Wikipedia.SmoothSixDPoincare.ManifoldMorse.MorseSurgeryData

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
  (d : MorseSurgeryData E f p)

def exteriorForward (x : d.LowerLevel) : M :=
  (d.attachmentHomeomorph ⟨x.val, Or.inl x.property.le⟩).val

def exteriorBackward (x : d.UpperLevel) : M :=
  (d.attachmentHomeomorph.symm ⟨x.val, x.property.le⟩).val

theorem exteriorForward_newExterior
    (r : {x : M // f x = f p - d.radius ^ 2 ∧ x ∈
      frontier ({y | f y ≤ f p - d.radius ^ 2} ∪
        range (d.chart.normHandleMap d.radius d.radius_pos d.block))}) :
    d.exteriorForward ⟨r.val, r.property.1⟩ = (d.surgery.newExterior r).val :=
  (d.newExterior_eq r).symm

variable [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M]
  (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)

structure HasSmoothExterior : Prop where
  forward :
    letI := RegularLevel.chartedSpace hf d.lower_regular
    ContMDiffOn 𝓘(ℝ, RegularLevel.Model E) 𝓘(ℝ, E) ∞ d.exteriorForward
      {x | x.val ∉ range (d.chart.attachingHandleMap d.radius d.radius_pos d.block)}
  backward :
    letI := RegularLevel.chartedSpace hf d.upper_regular
    ContMDiffOn 𝓘(ℝ, RegularLevel.Model E) 𝓘(ℝ, E) ∞ d.exteriorBackward
      {x | d.exteriorBackward x ∉
        range (d.chart.attachingHandleMap d.radius d.radius_pos d.block)}

end Wikipedia.SmoothSixDPoincare.ManifoldMorse.MorseSurgeryData
