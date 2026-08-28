import Wikipedia.HopfProblem.DegreeCollapseSublevelThreeFourMatrix
import Wikipedia.HopfProblem.DegreeCollapseNegatedMorseOrder
import Wikipedia.HopfProblem.DegreeCollapseSublevelFlowWindows
import Wikipedia.HopfProblem.DegreeCollapseCollaredSevenMorseSublevel
import Wikipedia.HopfProblem.DegreeCollapsePositiveIndexFiveElimination

/-!
# The actual remaining three/four matrix for the original collared half

Negate the ordered presentation with only middle handles and its unique
positive maximum. The literal zero sublevel is the same original half,
so its actual H3 vanishing applies. Construct native windows, the first
minimum, both consecutive middle blocks, and their surjective integral
matrix without supplying any block or matrix as extra geometric data.
-/

noncomputable section

open Set Function Filter Manifold
open scoped ContDiff Topology
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.CollaredSevenState.ExcellentMorsePresentation

open NoExoticSixSphere GLOrthonormalization MorseCancellation SingularMayerVietoris
  PeriodTorusHigherHomology

variable {B : Type} [TopologicalSpace B] {S : CollaredSevenState B}
  [Subsingleton (SingularHomology S.Half 3)] (P : S.ExcellentMorsePresentation)

theorem exists_negated_three_four_matrix
    (horder : ∀ p q : criticalPoints (Vector 7) P.function,
      0 < P.function p → P.function p < P.function q →
        nativeMorseIndex (Vector 7) P.function p ≤ nativeMorseIndex (Vector 7) P.function q)
    (m : criticalPoints (Vector 7) P.function) (hmpos : 0 < P.function m)
    (hmindex : nativeMorseIndex (Vector 7) P.function m = 7)
    (hindices : ∀ p : criticalPoints (Vector 7) P.function, 0 < P.function p →
      p = m ∨ nativeMorseIndex (Vector 7) P.function p = 3 ∨
        nativeMorseIndex (Vector 7) P.function p = 4) :
    ∃ A : AdaptedSurgeryWindows (Vector 7) P.sublevelFunction,
      ∃ r c : ℕ, ∃ hc : r + c < A.toSurgeryWindows.count,
      ∃ hthree : A.toSurgeryWindows.HasIndexThreeBlock 0 r,
      ∃ hfour : ThreeFourPresentation.HasIndexFourBlock A.toSurgeryWindows r c,
        A.toSurgeryWindows.upper (A.toSurgeryWindows.point ⟨r + c, hc⟩) < 0 ∧
        (∀ i : Fin A.toSurgeryWindows.count,
          P.sublevelFunction (A.toSurgeryWindows.point i) < 0 ↔ i.val ≤ r + c) ∧
        Surjective (ThreeFourPresentation.matrix A.toSurgeryWindows
          P.sublevelFunction_smooth r c hthree hc hfour).mulVec := by
  let : Subsingleton (SingularHomology {y : S.Space // P.sublevelFunction y ≤ 0} 3) :=
    (homotopyEquivHomologyEquiv P.halfSublevelHomeomorph.toHomotopyEquiv 3).surjective.subsingleton
  have hcrit : criticalPoints (Vector 7) P.sublevelFunction =
      criticalPoints (Vector 7) P.function := criticalPoints_neg P.function
  let mN : criticalPoints (Vector 7) P.sublevelFunction := ⟨m.val, hcrit.symm ▸ m.property⟩
  have hminimum (p : criticalPoints (Vector 7) P.sublevelFunction)
      (hp : P.sublevelFunction p < 0)
      (hpzero : nativeMorseIndex (Vector 7) P.sublevelFunction p = 0) :
      p = mN := by
    let pP : criticalPoints (Vector 7) P.function := ⟨p.val, hcrit ▸ p.property⟩
    have hs : nativeMorseIndex (Vector 7) P.sublevelFunction p +
        nativeMorseIndex (Vector 7) P.function pP = 7 := P.negated_native_index_add p
    rcases hindices pP (neg_neg_iff_pos.mp hp) with he | hthree | hfour
    · exact Subtype.ext (congrArg (fun x : criticalPoints (Vector 7) P.function => x.val) he)
    · omega
    · omega
  have hnegativeIndices (p : criticalPoints (Vector 7) P.sublevelFunction)
      (hp : P.sublevelFunction p < 0) :
      nativeMorseIndex (Vector 7) P.sublevelFunction p = 0 ∨
      nativeMorseIndex (Vector 7) P.sublevelFunction p = 3 ∨
        nativeMorseIndex (Vector 7) P.sublevelFunction p = 4 := by
    let pP : criticalPoints (Vector 7) P.function := ⟨p.val, hcrit ▸ p.property⟩
    have hs : nativeMorseIndex (Vector 7) P.sublevelFunction p +
        nativeMorseIndex (Vector 7) P.function pP = 7 := P.negated_native_index_add p
    rcases hindices pP (neg_neg_iff_pos.mp hp) with he | hthree | hfour
    · rw [he, hmindex] at hs
      exact Or.inl (by omega)
    · exact Or.inr (Or.inr (by omega))
    · exact Or.inr (Or.inl (by omega))
  obtain ⟨T⟩ := nonempty_adaptedSurgeryWindows P.sublevelFunction_smooth
    P.sublevelFunction_morse P.sublevelFunction_distinct
  obtain ⟨A, _, _, _, hupper⟩ := T.exists_same_flow_windows_below_cut
    P.sublevelFunction_smooth P.sublevelFunction_morse 0
  refine ⟨A, ?_⟩
  exact A.exists_surjective_three_four_matrix_below_cut P.sublevelFunction_smooth
    (RegularTimeMorse.regular_zero_not_critical P.sublevelFunction_regular)
    (P.negated_index_order_below_zero horder) hupper mN (neg_neg_of_pos hmpos)
    hminimum hnegativeIndices

end Wikipedia.HopfProblem.DegreeCollapse.CollaredSevenState.ExcellentMorsePresentation

namespace Wikipedia.HopfProblem.DegreeCollapse.CollaredSevenState

open NoExoticSixSphere GLOrthonormalization MorseCancellation SingularMayerVietoris

variable {B : Type} [TopologicalSpace B]

theorem exists_minimal_positive_presentation_with_surjective_middle_matrix
    (S : CollaredSevenState B) (eBoundary : B ≃ₜ Sphere 6)
    [Subsingleton (SingularHomology S.Half 3)] :
    ∃ P : S.ExcellentMorsePresentation,
      (∀ p q : criticalPoints (Vector 7) P.function,
        0 < P.function p → P.function p < P.function q →
          nativeMorseIndex (Vector 7) P.function p ≤ nativeMorseIndex (Vector 7) P.function q) ∧
      (∀ Q : S.ExcellentMorsePresentation,
        (criticalPoints (Vector 7) P.function).ncard ≤
          (criticalPoints (Vector 7) Q.function).ncard) ∧
      ∃ m : criticalPoints (Vector 7) P.function,
        0 < P.function m ∧ nativeMorseIndex (Vector 7) P.function m = 7 ∧
        (∀ x : S.Space, P.function x ≤ P.function m) ∧
        (∀ p : criticalPoints (Vector 7) P.function, 0 < P.function p →
          p = m ∨ nativeMorseIndex (Vector 7) P.function p = 3 ∨
            nativeMorseIndex (Vector 7) P.function p = 4) ∧
        ∃ A : AdaptedSurgeryWindows (Vector 7) P.sublevelFunction,
          ∃ r c : ℕ, ∃ hc : r + c < A.toSurgeryWindows.count,
          ∃ hthree : A.toSurgeryWindows.HasIndexThreeBlock 0 r,
          ∃ hfour : ThreeFourPresentation.HasIndexFourBlock A.toSurgeryWindows r c,
            A.toSurgeryWindows.upper (A.toSurgeryWindows.point ⟨r + c, hc⟩) < 0 ∧
            (∀ i : Fin A.toSurgeryWindows.count,
              P.sublevelFunction (A.toSurgeryWindows.point i) < 0 ↔ i.val ≤ r + c) ∧
            Surjective (ThreeFourPresentation.matrix A.toSurgeryWindows
              P.sublevelFunction_smooth r c hthree hc hfour).mulVec := by
  obtain ⟨P, horder, hminimal, _, m, hmpos, hmindex, hmax, hindices⟩ :=
    S.exists_minimal_positive_presentation_with_indices_three_and_four eBoundary
  exact ⟨P, horder, hminimal, m, hmpos, hmindex, hmax, hindices,
    P.exists_negated_three_four_matrix horder m hmpos hmindex hindices⟩

end Wikipedia.HopfProblem.DegreeCollapse.CollaredSevenState
