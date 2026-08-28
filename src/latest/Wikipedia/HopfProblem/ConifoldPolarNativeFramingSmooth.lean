import Wikipedia.HopfProblem.ConifoldPolarNativeFramingComplement

/-!
# Native smooth interfaces for the corrected complement formula

The corrected comparison carries every genuinely smooth matrix-valued map
into the standard complement with its original sphere atlas.  Its reverse
formula is smooth as a map to the original ambient matrix space.  The
canonical ambient matrix instances are reused; no atlas is put on `SL(2, ℂ)`.
-/

noncomputable section

open scoped ContDiff Manifold Matrix.Norms.Elementwise

namespace Wikipedia.HopfProblem.ConifoldPolar.NativeFraming

open ConifoldStandardBoundary

local instance : TopologicalSpace MatrixSpace := ConifoldPolar.matrixTopology

local instance : ChartedSpace MatrixSpace MatrixSpace := ConifoldPolar.matrixChartedSpace

variable {E H X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] [TopologicalSpace X] [ChartedSpace H X]
  {I : ModelWithCorners ℝ E H} {n : ℕ∞ω} [IsManifold I n X]

/-- A genuine `C^n` matrix-valued map has corrected coordinates in the native sphere complement. -/
theorem contMDiff_correctedComplement_of_matrix (hn : n ≤ ∞) (f : X → SpecialLinear)
    (hf : ContMDiff I 𝓘(ℝ, MatrixSpace) n (fun x => (f x).val)) :
    ContMDiff I (𝓡 6) n (fun x => correctedComplementHomeomorph (f x)) := by
  have hp := ConifoldPolar.contMDiff_forward_of_matrix f hf
  have hc := (correctedProductDiffeomorph.contMDiff.of_le hn).comp hp
  have hs := (StandardSixSphereCircleModel.diffeomorph.symm.contMDiff.of_le hn).comp hc
  exact hs

/-- The reverse corrected formula is `C^n` into the original ambient matrix space. -/
theorem contMDiff_correctedComplement_symm_val {n : ℕ∞ω} (hn : n ≤ ∞) :
    ContMDiff (𝓡 6) 𝓘(ℝ, MatrixSpace) n
      (fun q : StandardSixSphereCircleModel.Complement =>
        (correctedComplementHomeomorph.symm q).val) := by
  have hp := (correctedProductDiffeomorph.symm.contMDiff.of_le hn).comp
    (StandardSixSphereCircleModel.diffeomorph.contMDiff.of_le hn)
  have hi := (ConifoldPolar.contMDiff_inverse_val (n := n)).comp hp
  exact hi

end Wikipedia.HopfProblem.ConifoldPolar.NativeFraming
