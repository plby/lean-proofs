import Wikipedia.SmoothSixDPoincare.OrderedMiddlePresentation
import Wikipedia.SmoothSixDPoincare.IntegerPresentationMatrix
import Wikipedia.SmoothSixDPoincare.OrderedMorseHomologyVanishing

/-!
# The retained middle matrix is surjective from the original sphere homology

The entries are the coordinates of the constructed lifted attaching columns.
Its image is exactly the kernel of the original composite presentation map.
Terminal homotopy-sphere homology, propagated through the later actual
handles, makes this integer matrix surjective. The block ordering remains
explicit and no geometric realization of matrix operations is assumed.
-/

noncomputable section

open Set Function Topology ContinuousMap
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.ManifoldMorse.SurgeryWindows

open Wikipedia.HopfProblem.SingularMayerVietoris

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
  (S : SurgeryWindows E f)

def middleMatrix (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (r c : ℕ)
    (htwo : S.HasIndexTwoPrefix r) (hc : r + c < S.count)
    (hthree : S.HasIndexThreeBlock r c) : Matrix (Fin r) (Fin c) ℤ :=
  (S.middlePresentation hf r htwo c hc hthree).matrix

theorem middleMatrix_image_eq_kernel
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (r c : ℕ)
    (htwo : S.HasIndexTwoPrefix r) (hc : r + c < S.count)
    (hthree : S.HasIndexThreeBlock r c) :
    range (S.middleMatrix hf r c htwo hc hthree).mulVec =
      (LinearMap.ker (S.middlePresentation hf r htwo c hc hthree).map : Set (Fin r → ℤ)) :=
  (S.middlePresentation hf r htwo c hc hthree).matrix_image_eq_kernel

theorem middleMatrix_surjective_of_homotopySphere
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hdim : Module.finrank ℝ E = 6)
    (hM : M ≃ₕ SixSphere) (r c : ℕ)
    (htwo : S.HasIndexTwoPrefix r) (hc : r + c < S.count)
    (hthree : S.HasIndexThreeBlock r c) (hj : r + c + 1 < S.count)
    (hafter : ∀ i : Fin S.count, r + c < i.val → i.val + 1 < S.count →
      2 ≤ Module.finrank ℝ (S.data (S.point i)).chart.NegativeCoordinates ∧
      Module.finrank ℝ (S.data (S.point i)).chart.NegativeCoordinates ≠ 3) :
    Surjective (S.middleMatrix hf r c htwo hc hthree).mulVec := by
  let : Subsingleton (SingularHomology
      {x : M // f x ≤ S.upper (S.point ⟨r + c, hc⟩)} 2) :=
    S.upper_homology_subsingleton_of_later_indices hf hdim hM ⟨r + c, hc⟩ hj 2
      (by norm_num) (by norm_num) hafter
  exact (S.middlePresentation hf r htwo c hc hthree).matrix_surjective_of_subsingleton

theorem middleMatrix_surjective_of_complete_blocks
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hdim : Module.finrank ℝ E = 6)
    (hM : M ≃ₕ SixSphere) (r c : ℕ)
    (htwo : S.HasIndexTwoPrefix r) (hc : r + c < S.count)
    (hthree : S.HasIndexThreeBlock r c) (hcount : r + c + 2 = S.count) :
    Surjective (S.middleMatrix hf r c htwo hc hthree).mulVec := by
  apply S.middleMatrix_surjective_of_homotopySphere hf hdim hM r c htwo hc hthree (by omega)
  intro i hi hi'
  omega

end Wikipedia.SmoothSixDPoincare.ManifoldMorse.SurgeryWindows
