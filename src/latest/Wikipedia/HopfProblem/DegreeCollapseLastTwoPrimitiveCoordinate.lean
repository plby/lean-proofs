import Wikipedia.HopfProblem.DegreeCollapseMiddleBlockCompleteness
import Wikipedia.SmoothSixDPoincare.MorseIndexTwoCoordinateCount
import Wikipedia.HopfProblem.DegreeCollapseNativeOrderedLevelContractions

/-!
# The last index-two handle has an actual primitive collapse coordinate

The ordered initial block gives vanishing first homology below this
handle. Its native collapse coordinate on the common sublevel is therefore
surjective, and the original lower level has the circle contractions needed
for the verified Whitney and Morse cancellation theorems.
-/

noncomputable section

open Set Function Manifold ContinuousMap
open scoped ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

open SingularMayerVietoris

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] [Nonempty M] {f : M → ℝ}

theorem last_index_two_collapse_is_primitive
    (S : AdaptedSurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hdim : Module.finrank ℝ E = 6)
    (horder : ∀ x y : criticalPoints E f, f x < f y →
      nativeMorseIndex E f x ≤ nativeMorseIndex E f y)
    (hzero : nativeMorseCount E f 0 = 1) (hone : nativeMorseCount E f 1 = 0)
    (r n : ℕ) (hr : nativeMorseCount E f 2 = r) (hrpos : 0 < r)
    (hrc : r + n < S.toSurgeryWindows.count) :
    let q := S.toSurgeryWindows.point ⟨r, by omega⟩
    ∃ hindex : Module.finrank ℝ (S.data q).chart.NegativeCoordinates = 2,
      Surjective ((S.data q).indexTwoCollapseCoordinate hf.continuous hindex) ∧
      ∀ γ : C(Hemisphere.Sphere 1, (S.data q).LowerLevel),
        ∃ z, γ.Homotopic (ContinuousMap.const _ z) := by
  obtain ⟨r', n', htwo, hrc', hthree, -, hafter⟩ :=
    exists_middle_index_blocks S.toSurgeryWindows hf hdim horder hzero hone
  obtain ⟨hr', -⟩ :=
    native_middle_block_counts S.toSurgeryWindows hf r' n' htwo hrc' hthree hafter
  have hrr : r' = r := hr'.symm.trans hr
  rw [hrr] at htwo
  let q := S.toSurgeryWindows.point ⟨r, by omega⟩
  have hindex : Module.finrank ℝ (S.data q).chart.NegativeCoordinates = 2 :=
    htwo ⟨r, by omega⟩ hrpos le_rfl
  let _ : Subsingleton (SingularHomology
      {y : M // f y ≤ f q - (S.data q).radius ^ 2} 1) :=
    S.toSurgeryWindows.lower_homologyOne_subsingleton_of_indices hf ⟨r, by omega⟩ hrpos
      (fun i hi hir => by have hh := htwo i hi hir.le; omega)
  have hnidx : nativeMorseIndex E f q = 2 :=
    (nativeMorseIndex_eq_chart (S.data q).chart).trans hindex
  exact ⟨hindex, (S.data q).indexTwoCoordinate_surjective hf.continuous hindex,
    lower_circle_nullhomotopies_of_ordered_native_indices S.toSurgeryWindows hf hdim q hnidx
      hzero hone (fun z hz => (horder z q hz).trans_eq hnidx)⟩

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
