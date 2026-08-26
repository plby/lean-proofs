import ErdosProblems.Erdos1038.OneCutLocalConvexCover20Chunk0
import ErdosProblems.Erdos1038.OneCutLocalConvexCover20Chunk1
import ErdosProblems.Erdos1038.OneCutLocalConvexCover20Chunk2
import ErdosProblems.Erdos1038.OneCutLocalConvexCover20Chunk3

set_option warningAsError false

open Set

namespace Erdos1038

noncomputable section

namespace OneCutLocalConvexCover20

private theorem cover_mono_start {terms shift : Nat}
    {finish start start' : Rat} {boxes : List NewtonBulkBox}
    (hstart : start ≤ start')
    (hcover : NewtonBulkBox.SecondPositiveCoverCertified
      terms shift finish start boxes) :
    NewtonBulkBox.SecondPositiveCoverCertified
      terms shift finish start' boxes := by
  cases boxes with
  | nil => simp [NewtonBulkBox.SecondPositiveCoverCertified] at hcover
  | cons B Bs =>
      cases Bs with
      | nil =>
          simp only [NewtonBulkBox.SecondPositiveCoverCertified] at hcover ⊢
          exact ⟨hcover.1.trans hstart, hcover.2⟩
      | cons B' Bs =>
          simp only [NewtonBulkBox.SecondPositiveCoverCertified] at hcover ⊢
          exact ⟨hcover.1.trans hstart, hcover.2⟩

private theorem cover_append {terms shift : Nat}
    {finish mid start : Rat} {left right : List NewtonBulkBox}
    (hleft : NewtonBulkBox.SecondPositiveCoverCertified
      terms shift mid start left)
    (hright : NewtonBulkBox.SecondPositiveCoverCertified
      terms shift finish mid right) :
    NewtonBulkBox.SecondPositiveCoverCertified
      terms shift finish start (left ++ right) := by
  induction left generalizing start with
  | nil =>
      simp [NewtonBulkBox.SecondPositiveCoverCertified] at hleft
  | cons B Bs ih =>
      cases Bs with
      | nil =>
          cases right with
          | nil =>
              simp [NewtonBulkBox.SecondPositiveCoverCertified] at hright
          | cons C Cs =>
              simp only [List.cons_append, List.nil_append,
                NewtonBulkBox.SecondPositiveCoverCertified] at hleft ⊢
              exact ⟨hleft.1, hleft.2.1,
                cover_mono_start hleft.2.2 hright⟩
      | cons B' Bs =>
          simp only [List.cons_append,
            NewtonBulkBox.SecondPositiveCoverCertified] at hleft ⊢
          exact ⟨hleft.1, hleft.2.1, ih hleft.2.2⟩

theorem localCover_certified :
    NewtonBulkBox.SecondPositiveCoverCertified 80 6
      localFinish localStart localBoxes := by
  have h01 := cover_append localCoverChunk0_certified
    localCoverChunk1_certified
  have h012 := cover_append h01 localCoverChunk2_certified
  have h0123 := cover_append h012 localCoverChunk3_certified
  simpa [localBoxes] using! h0123

theorem continuousOn_lambdaDerivativeFormula_local :
    ContinuousOn LambdaDerivativeFormula
      (Set.Icc (localStart : ℝ) (localFinish : ℝ)) := by
  intro q hq
  exact (NewtonBulkBox.lambdaDerivativeFormula_continuousAt_of_cover
    localCover_certified hq).continuousWithinAt

theorem strictMonoOn_lambdaDerivativeFormula_local :
    StrictMonoOn LambdaDerivativeFormula
      (Set.Icc (localStart : ℝ) (localFinish : ℝ)) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
    continuousOn_lambdaDerivativeFormula_local
  intro q hq
  have hq' : q ∈ Icc (localStart : ℝ) (localFinish : ℝ) :=
    interior_subset hq
  exact NewtonBulkBox.lambdaDerivativeFormula_deriv_pos_of_cover
    localCover_certified hq'

end OneCutLocalConvexCover20

end

end Erdos1038
