import Wikipedia.HopfProblem.DegreeCollapseThreeFourLevelContractions

/-!
# The last native three-handle coordinate is primitive

The original coherent three-handle basis has exactly the actual collapse
coordinate as its first coordinate at the final step. It therefore supplies
every integer value. The original lower level has the proved circle
contractions, using only the preceding three-handle prefix.
-/

noncomputable section

open Set Function ContinuousMap
open scoped ContDiff Manifold
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] {f : M → ℝ}

theorem last_index_three_collapse_is_primitive
    (S : SurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hdim : Module.finrank ℝ E = 7) (r : ℕ) (hr : r < S.count) (hrpos : 0 < r)
    (hthree : S.HasIndexThreeBlock 0 r) :
    let q := S.point ⟨r, hr⟩
    ∃ hindex : Module.finrank ℝ (S.data q).chart.NegativeCoordinates = 3,
      Surjective (MiddleBasis.collapseCoordinate (S.data q) 1 hf.continuous hindex) ∧
      ∀ γ : C(Hemisphere.Sphere 1, (S.data q).LowerLevel),
        ∃ z, γ.Homotopic (ContinuousMap.const _ z) := by
  have hindex : Module.finrank ℝ (S.data (S.point ⟨r, hr⟩)).chart.NegativeCoordinates = 3 :=
    hthree ⟨r, hr⟩ hrpos (by dsimp; omega)
  refine ⟨hindex, ?_, ?_⟩
  · intro z
    cases r with
    | zero => omega
    | succ k =>
      refine ⟨MiddleBasis.middleBasis S hf (k + 1) hr hthree (fun _ => z), ?_⟩
      exact MiddleBasis.middleBasis_succ_coordinate S hf k hr hthree (fun _ => z)
  · exact S.lower_circle_nullhomotopies_of_three_four_prefix hf hdim ⟨r, hr⟩ hrpos
      (fun i hi hir => Or.inl (hthree i hi (by dsimp at hir; omega)))

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
