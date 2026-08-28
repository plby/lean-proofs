import Wikipedia.SmoothSixDPoincare.OrderedMiddleMatrixIndependence
import Wikipedia.SmoothSixDPoincare.IntegerMatrixUnimodular

/-!
# Equal middle-handle counts and an actual unimodular relation matrix

For an actual homotopy-six-sphere surgery sequence whose interior handles
form the prescribed two/three blocks, the constructed relation matrix is
bijective. The two counts are therefore equal; in that square indexing its
actual determinant has absolute value one. Global ordering and the geometric
realization of matrix operations are not assumed to follow from this result.
-/

noncomputable section

open Set Function Topology ContinuousMap
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.ManifoldMorse.SurgeryWindows

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
  (S : SurgeryWindows E f)

theorem middle_counts_equal
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hdim : Module.finrank ℝ E = 6)
    (hM : M ≃ₕ SixSphere) (r c : ℕ)
    (htwo : S.HasIndexTwoPrefix r) (hc : r + c < S.count)
    (hthree : S.HasIndexThreeBlock r c) (hcount : r + c + 2 = S.count) : r = c :=
  (HomologyTransport.matrix_sizes_eq_of_bijective (S.middleMatrix hf r c htwo hc hthree)
    (S.middleMatrix_bijective_of_complete_blocks hf hdim hM r c htwo hc hthree hcount)).symm

theorem middleMatrix_det_natAbs_one
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hdim : Module.finrank ℝ E = 6)
    (hM : M ≃ₕ SixSphere) (n : ℕ)
    (htwo : S.HasIndexTwoPrefix n) (hc : n + n < S.count)
    (hthree : S.HasIndexThreeBlock n n) (hcount : n + n + 2 = S.count) :
    (S.middleMatrix hf n n htwo hc hthree).det.natAbs = 1 :=
  HomologyTransport.integer_matrix_det_natAbs_one (S.middleMatrix hf n n htwo hc hthree)
    (S.middleMatrix_surjective_of_complete_blocks hf hdim hM n n htwo hc hthree hcount)

end Wikipedia.SmoothSixDPoincare.ManifoldMorse.SurgeryWindows
