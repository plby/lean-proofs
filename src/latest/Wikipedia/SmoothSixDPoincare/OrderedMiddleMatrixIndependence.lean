import Wikipedia.SmoothSixDPoincare.OrderedMiddleMatrix
import Wikipedia.SmoothSixDPoincare.MorseIndexThreePresentationIndependence

/-!
# The original middle matrix is bijective when the two/three blocks exhaust the interior

The original homotopy-sphere third homology propagates backward through
the later index-three handles. Each actual attaching relation therefore
has infinite order, so the constructed column matrix remains injective.
Together with the proved surjectivity this gives a bijective integer matrix.
Constructing the required global handle ordering is still separate work.
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

theorem middleMatrix_injective_of_upper_third
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (r : ℕ) (htwo : S.HasIndexTwoPrefix r) :
    ∀ (c : ℕ) (hc : r + c < S.count) (hthree : S.HasIndexThreeBlock r c),
      (∀ i : Fin S.count, r < i.val → i.val ≤ r + c →
        Subsingleton (SingularHomology {x : M // f x ≤ S.upper (S.point i)} 3)) →
      Injective (S.middleMatrix hf r c htwo hc hthree).mulVec := by
  intro c
  induction c with
  | zero =>
    intro hc hthree _
    exact IntegerPresentation.ofEquiv_matrix_injective (S.indexTwoBasis hf r hc htwo)
  | succ c ih =>
    intro hc hthree hvan
    let P := S.middlePresentation hf r htwo c (Nat.lt_of_succ_lt hc)
      (S.indexThreeBlock_mono (Nat.le_succ c) hthree)
    let B := S.consecutiveBandData hf ⟨r + c, Nat.lt_of_succ_lt hc⟩
      ⟨r + (c + 1), hc⟩ rfl
    have hP : Injective P.matrix.mulVec :=
      ih (Nat.lt_of_succ_lt hc) (S.indexThreeBlock_mono (Nat.le_succ c) hthree)
        (fun i hi him => hvan i hi (him.trans (Nat.le_succ (r + c))))
    let : Subsingleton (SingularHomology
        {x : M // f x ≤ f (S.point ⟨r + (c + 1), hc⟩) +
          (S.data (S.point ⟨r + (c + 1), hc⟩)).radius ^ 2} 3) :=
      hvan ⟨r + (c + 1), hc⟩ (by change r < r + (c + 1); omega) le_rfl
    exact (S.data (S.point ⟨r + (c + 1), hc⟩)).indexThreePresentation_matrix_injective
      hf.continuous (S.indexThreeBlock_last r c hc hthree) (P.transport (B.homologyEquiv 2)) hP

theorem middleMatrix_injective_of_complete_blocks
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hdim : Module.finrank ℝ E = 6)
    (hM : M ≃ₕ SixSphere) (r c : ℕ)
    (htwo : S.HasIndexTwoPrefix r) (hc : r + c < S.count)
    (hthree : S.HasIndexThreeBlock r c) (hcount : r + c + 2 = S.count) :
    Injective (S.middleMatrix hf r c htwo hc hthree).mulVec := by
  apply S.middleMatrix_injective_of_upper_third hf r htwo c hc hthree
  intro i hri hic
  have hi : i.val + 1 < S.count := by omega
  apply S.upper_homology_subsingleton_of_later_indices hf hdim hM i hi 3
    (by norm_num) (by norm_num)
  intro j hij hj
  have h3 := hthree j (hri.trans hij) (by omega)
  exact ⟨by omega, by omega⟩

theorem middleMatrix_bijective_of_complete_blocks
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hdim : Module.finrank ℝ E = 6)
    (hM : M ≃ₕ SixSphere) (r c : ℕ)
    (htwo : S.HasIndexTwoPrefix r) (hc : r + c < S.count)
    (hthree : S.HasIndexThreeBlock r c) (hcount : r + c + 2 = S.count) :
    Bijective (S.middleMatrix hf r c htwo hc hthree).mulVec :=
  ⟨S.middleMatrix_injective_of_complete_blocks hf hdim hM r c htwo hc hthree hcount,
    S.middleMatrix_surjective_of_complete_blocks hf hdim hM r c htwo hc hthree hcount⟩

end Wikipedia.SmoothSixDPoincare.ManifoldMorse.SurgeryWindows
