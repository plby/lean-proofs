import Wikipedia.HopfProblem.DegreeCollapseThreeFourBlockCancellation
import Wikipedia.HopfProblem.DegreeCollapseFourBlockExhaustion
import Wikipedia.HopfProblem.DegreeCollapseNegatedThreeFourMatrix
import Wikipedia.HopfProblem.DegreeCollapseNegatedPresentation
import Wikipedia.HopfProblem.DegreeCollapseCollaredSevenSingleMaximum

/-!

# Complete middle-handle elimination for the supplied original collared filling

Actual bounded three/four cancellation contradicts minimal total critical
count whenever the negated three-block is nonempty. Vanishing H4 excludes
the residual pure four-block. Thus exactly one positive critical point
remains. The existing native terminal criterion constructs the smooth
disk and the standard-sphere diffeomorphism of the original zero atlas.
This still requires the original collared state and the stated homology
vanishing; it does not construct the initial filling of the threefold.
-/

noncomputable section

open Set Function Filter Manifold
open scoped ContDiff Topology
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.CollaredSevenState

open NoExoticSixSphere GLOrthonormalization MorseCancellation SingularMayerVietoris
  PeriodTorusHigherHomology

variable {B : Type} [TopologicalSpace B] {S : CollaredSevenState B}

theorem ExcellentMorsePresentation.negated_three_block_empty_of_minimal
    [Subsingleton (SingularHomology S.Half 3)] (P : S.ExcellentMorsePresentation)
    (hminimal : ∀ Q : S.ExcellentMorsePresentation,
      (criticalPoints (Vector 7) P.function).ncard ≤
        (criticalPoints (Vector 7) Q.function).ncard)
    (A : AdaptedSurgeryWindows (Vector 7) P.sublevelFunction)
    (r n : ℕ) (hn : r + n < A.toSurgeryWindows.count)
    (hthree : A.toSurgeryWindows.HasIndexThreeBlock 0 r)
    (hfour : ThreeFourPresentation.HasIndexFourBlock A.toSurgeryWindows r n)
    (hcut : A.toSurgeryWindows.upper (A.toSurgeryWindows.point ⟨r + n, hn⟩) < 0)
    (hwhich : ∀ i : Fin A.toSurgeryWindows.count,
      P.sublevelFunction (A.toSurgeryWindows.point i) < 0 ↔ i.val ≤ r + n) : r = 0 := by
  by_contra hr
  have hrpos : 0 < r := by omega
  let _ : Subsingleton (SingularHomology {y : S.Space // P.sublevelFunction y ≤ 0} 3) :=
    (homotopyEquivHomologyEquiv P.halfSublevelHomeomorph.toHomotopyEquiv 3).surjective.subsingleton
  obtain ⟨i, v, hv, hmv, hinjv, hcard, _, _, hkeep, hcutv⟩ :=
    A.cancel_three_four_block_below_cut P.sublevelFunction_smooth P.sublevelFunction_morse
      (by simp) (RegularTimeMorse.regular_zero_not_critical P.sublevelFunction_regular)
      r n hn hrpos hthree hfour hcut hwhich
  let Q := P.replaceByNegatedSublevel v hv hmv hinjv hkeep hcutv
  have heQ : criticalPoints (Vector 7) Q.function = criticalPoints (Vector 7) v :=
    criticalPoints_neg v
  have heP : criticalPoints (Vector 7) P.sublevelFunction =
      criticalPoints (Vector 7) P.function := criticalPoints_neg P.function
  have hcardQ : (criticalPoints (Vector 7) Q.function).ncard + 2 =
      (criticalPoints (Vector 7) P.function).ncard := by
    rw [heQ]
    exact hcard.trans (congrArg Set.ncard heP)
  have hmin := hminimal Q
  omega

theorem exists_presentation_with_single_positive_critical
    (S : CollaredSevenState B) (eBoundary : B ≃ₜ Sphere 6)
    [Subsingleton (SingularHomology S.Half 3)]
    [Subsingleton (SingularHomology S.Half 4)] :
    ∃ P : S.ExcellentMorsePresentation, ∃ m : criticalPoints (Vector 7) P.function,
      0 < P.function m ∧
      ∀ x ∈ criticalPoints (Vector 7) P.function, 0 < P.function x → x = m.val := by
  obtain ⟨P, _, hminimal, m, hmpos, _, _, _, A, r, n, hn, hthree, hfour, hcut, hwhich, _⟩ :=
    S.exists_minimal_positive_presentation_with_surjective_middle_matrix eBoundary
  have hr := P.negated_three_block_empty_of_minimal hminimal A r n hn hthree hfour hcut hwhich
  subst r
  simp only [zero_add] at hn hcut hwhich
  let _ : Subsingleton (SingularHomology {y : S.Space // P.sublevelFunction y ≤ 0} 4) :=
    (homotopyEquivHomologyEquiv P.halfSublevelHomeomorph.toHomotopyEquiv 4).surjective.subsingleton
  have hnzero := MorseCancellation.SurgeryWindows.four_block_empty_of_upper_fourth_zero
    A.toSurgeryWindows P.sublevelFunction_smooth
      (RegularTimeMorse.regular_zero_not_critical P.sublevelFunction_regular)
      n hn hfour hcut hwhich
  subst n
  have hcrit : criticalPoints (Vector 7) P.sublevelFunction =
      criticalPoints (Vector 7) P.function := criticalPoints_neg P.function
  let mN : criticalPoints (Vector 7) P.sublevelFunction := ⟨m.val, hcrit.symm ▸ m.property⟩
  have hfirst (z : criticalPoints (Vector 7) P.sublevelFunction)
      (hz : P.sublevelFunction z < 0) : z = A.toSurgeryWindows.point ⟨0, hn⟩ := by
    obtain ⟨i, rfl⟩ := A.toSurgeryWindows.point.surjective z
    have hi := (hwhich i).mp hz
    apply congrArg A.toSurgeryWindows.point
    apply Fin.ext
    change i.val = 0
    omega
  have hmfirst := hfirst mN (neg_neg_of_pos hmpos)
  refine ⟨P, m, hmpos, ?_⟩
  intro x hx hpos
  let xN : criticalPoints (Vector 7) P.sublevelFunction := ⟨x, hcrit.symm ▸ hx⟩
  exact congrArg (fun z : criticalPoints (Vector 7) P.sublevelFunction => z.val)
    ((hfirst xN (neg_neg_of_pos hpos)).trans hmfirst.symm)

theorem nonempty_native_half_disk_of_middle_homology_zero
    (S : CollaredSevenState B) (eBoundary : B ≃ₜ Sphere 6)
    [Subsingleton (SingularHomology S.Half 3)]
    [Subsingleton (SingularHomology S.Half 4)] :
    Nonempty (NativeSublevelDisk 7 (Vector 7) (fun x => -S.time x) 0) := by
  obtain ⟨P, m, hm, hunique⟩ := S.exists_presentation_with_single_positive_critical eBoundary
  exact P.nonempty_native_half_disk_of_single_positive_critical m.val m.property hm hunique

theorem nonempty_zero_sphere_diffeomorph_of_middle_homology_zero
    (S : CollaredSevenState B) (eBoundary : B ≃ₜ Sphere 6)
    [Subsingleton (SingularHomology S.Half 3)]
    [Subsingleton (SingularHomology S.Half 4)] :
    letI := S.zeroAtlas;
    Nonempty (Diffeomorph (𝓡 6) (𝓡 6) (Sphere 6) S.Zero ∞) := by
  let _ := S.zeroAtlas
  obtain ⟨d⟩ := S.nonempty_native_half_disk_of_middle_homology_zero eBoundary
  exact ⟨nativeHalfDiskBoundaryDiffeomorph d⟩

end Wikipedia.HopfProblem.DegreeCollapse.CollaredSevenState
