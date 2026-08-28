import Wikipedia.HopfProblem.DegreeCollapseOrderedMiddleBlocks

/-!
# The constructed middle blocks have a surjective actual attaching matrix

The original homotopy-sphere homology vanishes at the end of the index-three
block: all later nonterminal handles have index at least four. The retained
native attaching presentation therefore has a surjective integer matrix.
No matrix, block decomposition, or homological-surjectivity input is needed.
-/

noncomputable section

open Set Function Manifold ContinuousMap
open scoped Topology ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] [Nonempty M] {f : M → ℝ}

theorem exists_surjective_middle_matrix_of_ordered_indices
    (S : SurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hdim : Module.finrank ℝ E = 6) (e : M ≃ₕ SixSphere)
    (horder : ∀ p q : criticalPoints E f, f p < f q →
      nativeMorseIndex E f p ≤ nativeMorseIndex E f q)
    (hzero : nativeMorseCount E f 0 = 1) (hone : nativeMorseCount E f 1 = 0) :
    ∃ r c : ℕ, ∃ htwo : S.HasIndexTwoPrefix r,
      ∃ hc : r + c < S.count, ∃ hthree : S.HasIndexThreeBlock r c,
        r + c + 1 < S.count ∧
        (∀ i : Fin S.count, r + c < i.val →
          4 ≤ Module.finrank ℝ (S.data (S.point i)).chart.NegativeCoordinates) ∧
        Surjective (S.middleMatrix hf r c htwo hc hthree).mulVec ∧ r ≤ c := by
  obtain ⟨r, c, htwo, hc, hthree, hj, hafter⟩ :=
    exists_middle_index_blocks S hf hdim horder hzero hone
  have hsurj : Surjective (S.middleMatrix hf r c htwo hc hthree).mulVec :=
    S.middleMatrix_surjective_of_homotopySphere hf hdim e r c htwo hc hthree hj
      (fun i hi _ => by have hh := hafter i hi; exact ⟨by omega, by omega⟩)
  refine ⟨r, c, htwo, hc, hthree, hj, hafter, hsurj, ?_⟩
  have hrank := LinearMap.finrank_le_finrank_of_surjective
    (f := (S.middleMatrix hf r c htwo hc hthree).mulVecLin) hsurj
  simpa only [Module.finrank_pi, Module.finrank_self, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul, mul_one] using hrank

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
