import ErdosProblems.Erdos1038.OneCutTailQNegativeChunk0
import ErdosProblems.Erdos1038.OneCutTailQNegativeChunk1
import ErdosProblems.Erdos1038.OneCutTailQNegativeChunk2
import ErdosProblems.Erdos1038.OneCutTailQNegativeChunk3
import ErdosProblems.Erdos1038.OneCutTailQNegativeChunk4
import ErdosProblems.Erdos1038.OneCutTailQNegativeChunk5
import ErdosProblems.Erdos1038.OneCutTailQNegativeChunk6
import ErdosProblems.Erdos1038.OneCutTailQNegativeChunk7
import ErdosProblems.Erdos1038.OneCutTailQNegativeChunk8
import ErdosProblems.Erdos1038.OneCutTailQNegativeChunk9
import ErdosProblems.Erdos1038.OneCutTailQNegativeChunk10
import ErdosProblems.Erdos1038.OneCutTailQNegativeChunk11
import ErdosProblems.Erdos1038.OneCutTailQNegativeChunk12
import ErdosProblems.Erdos1038.OneCutTailQNegativeChunk13
import ErdosProblems.Erdos1038.OneCutTailQPositiveChunk0
import ErdosProblems.Erdos1038.OneCutTailQPositiveChunk1
import ErdosProblems.Erdos1038.OneCutTailQPositiveChunk2
import ErdosProblems.Erdos1038.OneCutTailQPositiveChunk3
import ErdosProblems.Erdos1038.OneCutTailQPositiveChunk4
import ErdosProblems.Erdos1038.OneCutTailQPositiveChunk5
import ErdosProblems.Erdos1038.OneCutTailQPositiveChunk6
import ErdosProblems.Erdos1038.OneCutTailQPositiveChunk7
import ErdosProblems.Erdos1038.OneCutTailQPositiveChunk8
import ErdosProblems.Erdos1038.OneCutTailQPositiveChunk9
import ErdosProblems.Erdos1038.OneCutTailQPositiveChunk10
import ErdosProblems.Erdos1038.OneCutTailQPositiveChunk11
import ErdosProblems.Erdos1038.OneCutTailQPositiveChunk12
import ErdosProblems.Erdos1038.OneCutTailQPositiveChunk13
import ErdosProblems.Erdos1038.OneCutTailQPositiveChunk14
import ErdosProblems.Erdos1038.OneCutTailQPositiveChunk15

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038
noncomputable section
namespace OneCutTailCertificate
namespace OneCutTailQCandidates

private theorem negative_cover_mono_start {terms : Nat}
    {finish start start' : Rat} {boxes : List TailQBox}
    (hstart : start ≤ start')
    (hcover : TailQBox.NegativeCoverCertified terms finish start boxes) :
    TailQBox.NegativeCoverCertified terms finish start' boxes := by
  cases boxes with
  | nil => simp [TailQBox.NegativeCoverCertified] at hcover
  | cons B Bs =>
      cases Bs with
      | nil =>
          simp only [TailQBox.NegativeCoverCertified] at hcover ⊢
          exact ⟨hcover.1.trans hstart, hcover.2⟩
      | cons B' Bs =>
          simp only [TailQBox.NegativeCoverCertified] at hcover ⊢
          exact ⟨hcover.1.trans hstart, hcover.2⟩

private theorem negative_cover_append {terms : Nat}
    {finish mid start : Rat} {left right : List TailQBox}
    (hleft : TailQBox.NegativeCoverCertified terms mid start left)
    (hright : TailQBox.NegativeCoverCertified terms finish mid right) :
    TailQBox.NegativeCoverCertified terms finish start (left ++ right) := by
  induction left generalizing start with
  | nil => simp [TailQBox.NegativeCoverCertified] at hleft
  | cons B Bs ih =>
      cases Bs with
      | nil =>
          cases right with
          | nil => simp [TailQBox.NegativeCoverCertified] at hright
          | cons C Cs =>
              simp only [List.cons_append, List.nil_append,
                TailQBox.NegativeCoverCertified] at hleft ⊢
              exact ⟨hleft.1, hleft.2.1,
                negative_cover_mono_start hleft.2.2 hright⟩
      | cons B' Bs =>
          simp only [List.cons_append,
            TailQBox.NegativeCoverCertified] at hleft ⊢
          exact ⟨hleft.1, hleft.2.1, ih hleft.2.2⟩

private theorem positive_cover_mono_start {terms : Nat}
    {finish start start' : Rat} {boxes : List TailQBox}
    (hstart : start ≤ start')
    (hcover : TailQBox.PositiveCoverCertified terms finish start boxes) :
    TailQBox.PositiveCoverCertified terms finish start' boxes := by
  cases boxes with
  | nil => simp [TailQBox.PositiveCoverCertified] at hcover
  | cons B Bs =>
      cases Bs with
      | nil =>
          simp only [TailQBox.PositiveCoverCertified] at hcover ⊢
          exact ⟨hcover.1.trans hstart, hcover.2⟩
      | cons B' Bs =>
          simp only [TailQBox.PositiveCoverCertified] at hcover ⊢
          exact ⟨hcover.1.trans hstart, hcover.2⟩

private theorem positive_cover_append {terms : Nat}
    {finish mid start : Rat} {left right : List TailQBox}
    (hleft : TailQBox.PositiveCoverCertified terms mid start left)
    (hright : TailQBox.PositiveCoverCertified terms finish mid right) :
    TailQBox.PositiveCoverCertified terms finish start (left ++ right) := by
  induction left generalizing start with
  | nil => simp [TailQBox.PositiveCoverCertified] at hleft
  | cons B Bs ih =>
      cases Bs with
      | nil =>
          cases right with
          | nil => simp [TailQBox.PositiveCoverCertified] at hright
          | cons C Cs =>
              simp only [List.cons_append, List.nil_append,
                TailQBox.PositiveCoverCertified] at hleft ⊢
              exact ⟨hleft.1, hleft.2.1,
                positive_cover_mono_start hleft.2.2 hright⟩
      | cons B' Bs =>
          simp only [List.cons_append,
            TailQBox.PositiveCoverCertified] at hleft ⊢
          exact ⟨hleft.1, hleft.2.1, ih hleft.2.2⟩

theorem negativeCover_certified :
    TailQBox.NegativeCoverCertified 80
      (240189709838717 / 10 ^ 16) tailQ negativeBoxes := by
  have h := negative_cover_append negativeCoverChunk0_certified
      (negative_cover_append negativeCoverChunk1_certified
      (negative_cover_append negativeCoverChunk2_certified
      (negative_cover_append negativeCoverChunk3_certified
      (negative_cover_append negativeCoverChunk4_certified
      (negative_cover_append negativeCoverChunk5_certified
      (negative_cover_append negativeCoverChunk6_certified
      (negative_cover_append negativeCoverChunk7_certified
      (negative_cover_append negativeCoverChunk8_certified
      (negative_cover_append negativeCoverChunk9_certified
      (negative_cover_append negativeCoverChunk10_certified
      (negative_cover_append negativeCoverChunk11_certified
      (negative_cover_append negativeCoverChunk12_certified
      (negativeCoverChunk13_certified)))))))))))))
  simpa [negativeBoxes] using! h

theorem positiveCover_certified :
    TailQBox.PositiveCoverCertified 80 (1 / 10)
      (274644706879705 / 10 ^ 16) positiveBoxes := by
  have h := positive_cover_append positiveCoverChunk0_certified
      (positive_cover_append positiveCoverChunk1_certified
      (positive_cover_append positiveCoverChunk2_certified
      (positive_cover_append positiveCoverChunk3_certified
      (positive_cover_append positiveCoverChunk4_certified
      (positive_cover_append positiveCoverChunk5_certified
      (positive_cover_append positiveCoverChunk6_certified
      (positive_cover_append positiveCoverChunk7_certified
      (positive_cover_append positiveCoverChunk8_certified
      (positive_cover_append positiveCoverChunk9_certified
      (positive_cover_append positiveCoverChunk10_certified
      (positive_cover_append positiveCoverChunk11_certified
      (positive_cover_append positiveCoverChunk12_certified
      (positive_cover_append positiveCoverChunk13_certified
      (positive_cover_append positiveCoverChunk14_certified
      (positiveCoverChunk15_certified)))))))))))))))
  simpa [positiveBoxes] using! h

end OneCutTailQCandidates
end OneCutTailCertificate
end
end Erdos1038
