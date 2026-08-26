import ErdosProblems.Erdos1038.OneCutSoftCandidatesChunk0
import ErdosProblems.Erdos1038.OneCutSoftCandidatesChunk1
import ErdosProblems.Erdos1038.OneCutSoftCandidatesChunk2
import ErdosProblems.Erdos1038.OneCutSoftCandidatesChunk3
import ErdosProblems.Erdos1038.OneCutSoftCandidatesChunk4
import ErdosProblems.Erdos1038.OneCutSoftCandidatesChunk5
import ErdosProblems.Erdos1038.OneCutSoftCandidatesChunk6
import ErdosProblems.Erdos1038.OneCutSoftCandidatesChunk7
import ErdosProblems.Erdos1038.OneCutSoftCandidatesChunk8
import ErdosProblems.Erdos1038.OneCutSoftCandidatesChunk9
import ErdosProblems.Erdos1038.OneCutSoftCandidatesChunk10
import ErdosProblems.Erdos1038.OneCutSoftCandidatesChunk11
import ErdosProblems.Erdos1038.OneCutSoftCandidatesChunk12
import ErdosProblems.Erdos1038.OneCutSoftCandidatesChunk13
import ErdosProblems.Erdos1038.OneCutSoftCandidatesChunk14
import ErdosProblems.Erdos1038.OneCutSoftCandidatesChunk15
import ErdosProblems.Erdos1038.OneCutSoftCandidatesChunk16
import ErdosProblems.Erdos1038.OneCutSoftCandidatesChunk17
import ErdosProblems.Erdos1038.OneCutSoftCandidatesChunk18
import ErdosProblems.Erdos1038.OneCutSoftCandidatesChunk19
import ErdosProblems.Erdos1038.OneCutSoftCandidatesChunk20
import ErdosProblems.Erdos1038.OneCutSoftCandidatesChunk21
import ErdosProblems.Erdos1038.OneCutSoftCandidatesChunk22
import ErdosProblems.Erdos1038.OneCutSoftCandidatesChunk23
import ErdosProblems.Erdos1038.OneCutSoftCandidatesChunk24
import ErdosProblems.Erdos1038.OneCutSoftCandidatesChunk25
import ErdosProblems.Erdos1038.OneCutSoftCandidatesChunk26
import ErdosProblems.Erdos1038.OneCutSoftCandidatesChunk27
import ErdosProblems.Erdos1038.OneCutSoftCandidatesChunk28
import ErdosProblems.Erdos1038.OneCutSoftCandidatesChunk29
import ErdosProblems.Erdos1038.OneCutSoftCandidatesChunk30
import ErdosProblems.Erdos1038.OneCutSoftCandidatesChunk31
import ErdosProblems.Erdos1038.OneCutSoftCandidatesChunk32
import ErdosProblems.Erdos1038.OneCutSoftCandidatesChunk33
import ErdosProblems.Erdos1038.OneCutSoftCandidatesChunk34
import ErdosProblems.Erdos1038.OneCutSoftCandidatesChunk35

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038
noncomputable section
namespace OneCutSoftCandidates

private theorem positive_cover_mono_start {terms : Nat}
    {finish start start' : Rat} {boxes : List SoftBox}
    (hstart : start ≤ start')
    (hcover : SoftBox.PositiveCoverCertified terms finish start boxes) :
    SoftBox.PositiveCoverCertified terms finish start' boxes := by
  cases boxes with
  | nil => simp [SoftBox.PositiveCoverCertified] at hcover
  | cons B Bs =>
      cases Bs with
      | nil =>
          simp only [SoftBox.PositiveCoverCertified] at hcover ⊢
          exact ⟨hcover.1.trans hstart, hcover.2⟩
      | cons B' Bs =>
          simp only [SoftBox.PositiveCoverCertified] at hcover ⊢
          exact ⟨hcover.1.trans hstart, hcover.2⟩

private theorem positive_cover_append {terms : Nat}
    {finish mid start : Rat} {left right : List SoftBox}
    (hleft : SoftBox.PositiveCoverCertified terms mid start left)
    (hright : SoftBox.PositiveCoverCertified terms finish mid right) :
    SoftBox.PositiveCoverCertified terms finish start (left ++ right) := by
  induction left generalizing start with
  | nil => simp [SoftBox.PositiveCoverCertified] at hleft
  | cons B Bs ih =>
      cases Bs with
      | nil =>
          cases right with
          | nil => simp [SoftBox.PositiveCoverCertified] at hright
          | cons C Cs =>
              simp only [List.cons_append, List.nil_append,
                SoftBox.PositiveCoverCertified] at hleft ⊢
              exact ⟨hleft.1, hleft.2.1,
                positive_cover_mono_start hleft.2.2 hright⟩
      | cons B' Bs =>
          simp only [List.cons_append,
            SoftBox.PositiveCoverCertified] at hleft ⊢
          exact ⟨hleft.1, hleft.2.1, ih hleft.2.2⟩

theorem positiveCover_certified :
    SoftBox.PositiveCoverCertified 32 qSoftUpperRat (1 / 10) boxes := by
  have h35 := positiveCoverChunk35_certified
  have h34 := positive_cover_append positiveCoverChunk34_certified h35
  have h33 := positive_cover_append positiveCoverChunk33_certified h34
  have h32 := positive_cover_append positiveCoverChunk32_certified h33
  have h31 := positive_cover_append positiveCoverChunk31_certified h32
  have h30 := positive_cover_append positiveCoverChunk30_certified h31
  have h29 := positive_cover_append positiveCoverChunk29_certified h30
  have h28 := positive_cover_append positiveCoverChunk28_certified h29
  have h27 := positive_cover_append positiveCoverChunk27_certified h28
  have h26 := positive_cover_append positiveCoverChunk26_certified h27
  have h25 := positive_cover_append positiveCoverChunk25_certified h26
  have h24 := positive_cover_append positiveCoverChunk24_certified h25
  have h23 := positive_cover_append positiveCoverChunk23_certified h24
  have h22 := positive_cover_append positiveCoverChunk22_certified h23
  have h21 := positive_cover_append positiveCoverChunk21_certified h22
  have h20 := positive_cover_append positiveCoverChunk20_certified h21
  have h19 := positive_cover_append positiveCoverChunk19_certified h20
  have h18 := positive_cover_append positiveCoverChunk18_certified h19
  have h17 := positive_cover_append positiveCoverChunk17_certified h18
  have h16 := positive_cover_append positiveCoverChunk16_certified h17
  have h15 := positive_cover_append positiveCoverChunk15_certified h16
  have h14 := positive_cover_append positiveCoverChunk14_certified h15
  have h13 := positive_cover_append positiveCoverChunk13_certified h14
  have h12 := positive_cover_append positiveCoverChunk12_certified h13
  have h11 := positive_cover_append positiveCoverChunk11_certified h12
  have h10 := positive_cover_append positiveCoverChunk10_certified h11
  have h9 := positive_cover_append positiveCoverChunk9_certified h10
  have h8 := positive_cover_append positiveCoverChunk8_certified h9
  have h7 := positive_cover_append positiveCoverChunk7_certified h8
  have h6 := positive_cover_append positiveCoverChunk6_certified h7
  have h5 := positive_cover_append positiveCoverChunk5_certified h6
  have h4 := positive_cover_append positiveCoverChunk4_certified h5
  have h3 := positive_cover_append positiveCoverChunk3_certified h4
  have h2 := positive_cover_append positiveCoverChunk2_certified h3
  have h1 := positive_cover_append positiveCoverChunk1_certified h2
  have h0 := positive_cover_append positiveCoverChunk0_certified h1
  simpa [boxes] using! h0

end OneCutSoftCandidates
end
end Erdos1038

