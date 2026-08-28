import Wikipedia.HopfProblem.DegreeCollapseSublevelThreeFourBlocks
import Wikipedia.HopfProblem.DegreeCollapseRegularInclusionHomology

/-!
# The actual below-cut three/four matrix is surjective from zero terminal H3

Construct the entire block arrangement from the below-cut index ordering.
The final regular band identifies the homology of the last upper sublevel
with that of the actual cut sublevel. Its vanishing makes the retained
integer presentation matrix surjective. All matrix columns still represent
the original index-four attaching classes through their actual band maps.
-/

noncomputable section

open Set Function Filter Manifold
open scoped Topology ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

open SingularMayerVietoris

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] {f : M → ℝ}

theorem AdaptedSurgeryWindows.exists_surjective_three_four_matrix_below_cut
    (A : AdaptedSurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    {b : ℝ} (hreg : ∀ y, f y = b → y ∉ criticalPoints E f)
    [Subsingleton (SingularHomology {y : M // f y ≤ b} 3)]
    (horder : ∀ p q : criticalPoints E f, f q < b → f p < f q →
      nativeMorseIndex E f p ≤ nativeMorseIndex E f q)
    (hcut : ∀ p : criticalPoints E f, f p < b → A.toSurgeryWindows.upper p < b)
    (m : criticalPoints E f) (hmb : f m < b)
    (hminimum : ∀ p : criticalPoints E f, f p < b → nativeMorseIndex E f p = 0 → p = m)
    (hindices : ∀ p : criticalPoints E f, f p < b →
      nativeMorseIndex E f p = 0 ∨ nativeMorseIndex E f p = 3 ∨
        nativeMorseIndex E f p = 4) :
    ∃ r c : ℕ, ∃ hc : r + c < A.toSurgeryWindows.count,
      ∃ hthree : A.toSurgeryWindows.HasIndexThreeBlock 0 r,
      ∃ hfour : ThreeFourPresentation.HasIndexFourBlock A.toSurgeryWindows r c,
        A.toSurgeryWindows.upper (A.toSurgeryWindows.point ⟨r + c, hc⟩) < b ∧
        (∀ i : Fin A.toSurgeryWindows.count,
          f (A.toSurgeryWindows.point i) < b ↔ i.val ≤ r + c) ∧
        Surjective
          (ThreeFourPresentation.matrix A.toSurgeryWindows hf r c hthree hc hfour).mulVec := by
  obtain ⟨r, c, hc, hthree, hfour, hab, hwhich, hband⟩ :=
    A.exists_three_four_blocks_below_cut hf hreg horder hcut m hmb hminimum hindices
  let : Subsingleton (SingularHomology {y : M //
      f y ≤ A.toSurgeryWindows.upper (A.toSurgeryWindows.point ⟨r + c, hc⟩)} 3) :=
    (regular_sublevel_inclusion_bijective hf hab.le hband 3).injective.subsingleton
  exact ⟨r, c, hc, hthree, hfour, hab, hwhich,
    ThreeFourPresentation.matrix_surjective_of_upper_third_zero
      A.toSurgeryWindows hf r c hthree hc hfour⟩

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
