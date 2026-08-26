import ErdosProblems.Erdos1038.TaoUpperCaseOneInitialChunk0
import ErdosProblems.Erdos1038.TaoUpperCaseOneInitialChunk1
import ErdosProblems.Erdos1038.TaoUpperCaseOneInitialChunk2
import ErdosProblems.Erdos1038.TaoUpperCaseOneInitialChunk3
import ErdosProblems.Erdos1038.TaoUpperCaseOneInitialChunk4
import ErdosProblems.Erdos1038.TaoUpperCaseOneDirectChunk0
import ErdosProblems.Erdos1038.TaoUpperCaseOneDirectChunk1
import ErdosProblems.Erdos1038.TaoUpperCaseOneDirectChunk2
import ErdosProblems.Erdos1038.TaoUpperCaseOneDirectChunk3
import ErdosProblems.Erdos1038.TaoUpperCaseOneDirectChunk4
import ErdosProblems.Erdos1038.TaoUpperCaseOneDirectChunk5
import ErdosProblems.Erdos1038.TaoUpperCaseOneDirectChunk6
import ErdosProblems.Erdos1038.TaoUpperCaseOneDirectChunk7
import ErdosProblems.Erdos1038.TaoUpperCaseOneDirectChunk8
import ErdosProblems.Erdos1038.TaoUpperCaseOneDirectChunk9
import ErdosProblems.Erdos1038.TaoUpperCaseOneDirectChunk10
import ErdosProblems.Erdos1038.TaoUpperCaseOneDirectChunk11
import ErdosProblems.Erdos1038.TaoUpperCaseOneDirectChunk12
import ErdosProblems.Erdos1038.TaoUpperCaseOneDirectChunk13
import ErdosProblems.Erdos1038.TaoUpperCaseOneDirectChunk14
import ErdosProblems.Erdos1038.TaoUpperCaseOneDirectChunk15
import ErdosProblems.Erdos1038.TaoUpperCaseOneDirectChunk16
import ErdosProblems.Erdos1038.TaoUpperCaseOneDirectChunk17
import ErdosProblems.Erdos1038.TaoUpperCaseOneDirectChunk18
import ErdosProblems.Erdos1038.TaoUpperCaseOneDirectChunk19
import ErdosProblems.Erdos1038.TaoUpperCaseOneDirectChunk20
import ErdosProblems.Erdos1038.TaoUpperCaseOneDirectChunk21
import ErdosProblems.Erdos1038.TaoUpperCaseOneDirectChunk22
import ErdosProblems.Erdos1038.TaoUpperCaseOneDirectChunk23
import ErdosProblems.Erdos1038.TaoUpperCaseOneDirectChunk24
import ErdosProblems.Erdos1038.TaoUpperCaseOneDirectChunk25
import ErdosProblems.Erdos1038.TaoUpperCaseOneDirectChunk26
import ErdosProblems.Erdos1038.TaoUpperCaseOneDirectChunk27
import ErdosProblems.Erdos1038.TaoUpperCaseOneDirectChunk28
import ErdosProblems.Erdos1038.TaoUpperCaseOneDirectChunk29
import ErdosProblems.Erdos1038.TaoUpperCaseOneInitialCover
import ErdosProblems.Erdos1038.TaoUpperCaseOneDirectCover

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038

private theorem all_of_take_drop {α : Type*}
    (p : α → Bool) (n : Nat) (xs : List α)
    (htake : (xs.take n).all p = true)
    (hdrop : (xs.drop n).all p = true) :
    xs.all p = true := by
  rw [← List.take_append_drop n xs, List.all_append, htake, hdrop]
  rfl

theorem taoCaseOneInitialIntervals_certify :
    taoCaseOneInitialIntervals.all
      (taoCaseOneSecondDerivativePositive 80) = true := by
  have h80 : (taoCaseOneInitialIntervals.drop 80).all (taoCaseOneSecondDerivativePositive 80) = true :=
    taoCaseOneInitialChunk4_certify
  have h60 : (taoCaseOneInitialIntervals.drop 60).all (taoCaseOneSecondDerivativePositive 80) = true :=
    all_of_take_drop (taoCaseOneSecondDerivativePositive 80) 20 (taoCaseOneInitialIntervals.drop 60)
      taoCaseOneInitialChunk3_certify (by
        simpa [List.drop_drop] using! h80)
  have h40 : (taoCaseOneInitialIntervals.drop 40).all (taoCaseOneSecondDerivativePositive 80) = true :=
    all_of_take_drop (taoCaseOneSecondDerivativePositive 80) 20 (taoCaseOneInitialIntervals.drop 40)
      taoCaseOneInitialChunk2_certify (by
        simpa [List.drop_drop] using! h60)
  have h20 : (taoCaseOneInitialIntervals.drop 20).all (taoCaseOneSecondDerivativePositive 80) = true :=
    all_of_take_drop (taoCaseOneSecondDerivativePositive 80) 20 (taoCaseOneInitialIntervals.drop 20)
      taoCaseOneInitialChunk1_certify (by
        simpa [List.drop_drop] using! h40)
  exact all_of_take_drop (taoCaseOneSecondDerivativePositive 80) 20 taoCaseOneInitialIntervals
    taoCaseOneInitialChunk0_certify (by simpa using! h20)

theorem taoCaseOneDirectIntervals_certify :
    taoCaseOneDirectIntervals.all (taoCaseOneGapPositive 100) = true := by
  have h580 : (taoCaseOneDirectIntervals.drop 580).all (taoCaseOneGapPositive 100) = true :=
    taoCaseOneDirectChunk29_certify
  have h560 : (taoCaseOneDirectIntervals.drop 560).all (taoCaseOneGapPositive 100) = true :=
    all_of_take_drop (taoCaseOneGapPositive 100) 20 (taoCaseOneDirectIntervals.drop 560)
      taoCaseOneDirectChunk28_certify (by
        simpa [List.drop_drop] using! h580)
  have h540 : (taoCaseOneDirectIntervals.drop 540).all (taoCaseOneGapPositive 100) = true :=
    all_of_take_drop (taoCaseOneGapPositive 100) 20 (taoCaseOneDirectIntervals.drop 540)
      taoCaseOneDirectChunk27_certify (by
        simpa [List.drop_drop] using! h560)
  have h520 : (taoCaseOneDirectIntervals.drop 520).all (taoCaseOneGapPositive 100) = true :=
    all_of_take_drop (taoCaseOneGapPositive 100) 20 (taoCaseOneDirectIntervals.drop 520)
      taoCaseOneDirectChunk26_certify (by
        simpa [List.drop_drop] using! h540)
  have h500 : (taoCaseOneDirectIntervals.drop 500).all (taoCaseOneGapPositive 100) = true :=
    all_of_take_drop (taoCaseOneGapPositive 100) 20 (taoCaseOneDirectIntervals.drop 500)
      taoCaseOneDirectChunk25_certify (by
        simpa [List.drop_drop] using! h520)
  have h480 : (taoCaseOneDirectIntervals.drop 480).all (taoCaseOneGapPositive 100) = true :=
    all_of_take_drop (taoCaseOneGapPositive 100) 20 (taoCaseOneDirectIntervals.drop 480)
      taoCaseOneDirectChunk24_certify (by
        simpa [List.drop_drop] using! h500)
  have h460 : (taoCaseOneDirectIntervals.drop 460).all (taoCaseOneGapPositive 100) = true :=
    all_of_take_drop (taoCaseOneGapPositive 100) 20 (taoCaseOneDirectIntervals.drop 460)
      taoCaseOneDirectChunk23_certify (by
        simpa [List.drop_drop] using! h480)
  have h440 : (taoCaseOneDirectIntervals.drop 440).all (taoCaseOneGapPositive 100) = true :=
    all_of_take_drop (taoCaseOneGapPositive 100) 20 (taoCaseOneDirectIntervals.drop 440)
      taoCaseOneDirectChunk22_certify (by
        simpa [List.drop_drop] using! h460)
  have h420 : (taoCaseOneDirectIntervals.drop 420).all (taoCaseOneGapPositive 100) = true :=
    all_of_take_drop (taoCaseOneGapPositive 100) 20 (taoCaseOneDirectIntervals.drop 420)
      taoCaseOneDirectChunk21_certify (by
        simpa [List.drop_drop] using! h440)
  have h400 : (taoCaseOneDirectIntervals.drop 400).all (taoCaseOneGapPositive 100) = true :=
    all_of_take_drop (taoCaseOneGapPositive 100) 20 (taoCaseOneDirectIntervals.drop 400)
      taoCaseOneDirectChunk20_certify (by
        simpa [List.drop_drop] using! h420)
  have h380 : (taoCaseOneDirectIntervals.drop 380).all (taoCaseOneGapPositive 100) = true :=
    all_of_take_drop (taoCaseOneGapPositive 100) 20 (taoCaseOneDirectIntervals.drop 380)
      taoCaseOneDirectChunk19_certify (by
        simpa [List.drop_drop] using! h400)
  have h360 : (taoCaseOneDirectIntervals.drop 360).all (taoCaseOneGapPositive 100) = true :=
    all_of_take_drop (taoCaseOneGapPositive 100) 20 (taoCaseOneDirectIntervals.drop 360)
      taoCaseOneDirectChunk18_certify (by
        simpa [List.drop_drop] using! h380)
  have h340 : (taoCaseOneDirectIntervals.drop 340).all (taoCaseOneGapPositive 100) = true :=
    all_of_take_drop (taoCaseOneGapPositive 100) 20 (taoCaseOneDirectIntervals.drop 340)
      taoCaseOneDirectChunk17_certify (by
        simpa [List.drop_drop] using! h360)
  have h320 : (taoCaseOneDirectIntervals.drop 320).all (taoCaseOneGapPositive 100) = true :=
    all_of_take_drop (taoCaseOneGapPositive 100) 20 (taoCaseOneDirectIntervals.drop 320)
      taoCaseOneDirectChunk16_certify (by
        simpa [List.drop_drop] using! h340)
  have h300 : (taoCaseOneDirectIntervals.drop 300).all (taoCaseOneGapPositive 100) = true :=
    all_of_take_drop (taoCaseOneGapPositive 100) 20 (taoCaseOneDirectIntervals.drop 300)
      taoCaseOneDirectChunk15_certify (by
        simpa [List.drop_drop] using! h320)
  have h280 : (taoCaseOneDirectIntervals.drop 280).all (taoCaseOneGapPositive 100) = true :=
    all_of_take_drop (taoCaseOneGapPositive 100) 20 (taoCaseOneDirectIntervals.drop 280)
      taoCaseOneDirectChunk14_certify (by
        simpa [List.drop_drop] using! h300)
  have h260 : (taoCaseOneDirectIntervals.drop 260).all (taoCaseOneGapPositive 100) = true :=
    all_of_take_drop (taoCaseOneGapPositive 100) 20 (taoCaseOneDirectIntervals.drop 260)
      taoCaseOneDirectChunk13_certify (by
        simpa [List.drop_drop] using! h280)
  have h240 : (taoCaseOneDirectIntervals.drop 240).all (taoCaseOneGapPositive 100) = true :=
    all_of_take_drop (taoCaseOneGapPositive 100) 20 (taoCaseOneDirectIntervals.drop 240)
      taoCaseOneDirectChunk12_certify (by
        simpa [List.drop_drop] using! h260)
  have h220 : (taoCaseOneDirectIntervals.drop 220).all (taoCaseOneGapPositive 100) = true :=
    all_of_take_drop (taoCaseOneGapPositive 100) 20 (taoCaseOneDirectIntervals.drop 220)
      taoCaseOneDirectChunk11_certify (by
        simpa [List.drop_drop] using! h240)
  have h200 : (taoCaseOneDirectIntervals.drop 200).all (taoCaseOneGapPositive 100) = true :=
    all_of_take_drop (taoCaseOneGapPositive 100) 20 (taoCaseOneDirectIntervals.drop 200)
      taoCaseOneDirectChunk10_certify (by
        simpa [List.drop_drop] using! h220)
  have h180 : (taoCaseOneDirectIntervals.drop 180).all (taoCaseOneGapPositive 100) = true :=
    all_of_take_drop (taoCaseOneGapPositive 100) 20 (taoCaseOneDirectIntervals.drop 180)
      taoCaseOneDirectChunk9_certify (by
        simpa [List.drop_drop] using! h200)
  have h160 : (taoCaseOneDirectIntervals.drop 160).all (taoCaseOneGapPositive 100) = true :=
    all_of_take_drop (taoCaseOneGapPositive 100) 20 (taoCaseOneDirectIntervals.drop 160)
      taoCaseOneDirectChunk8_certify (by
        simpa [List.drop_drop] using! h180)
  have h140 : (taoCaseOneDirectIntervals.drop 140).all (taoCaseOneGapPositive 100) = true :=
    all_of_take_drop (taoCaseOneGapPositive 100) 20 (taoCaseOneDirectIntervals.drop 140)
      taoCaseOneDirectChunk7_certify (by
        simpa [List.drop_drop] using! h160)
  have h120 : (taoCaseOneDirectIntervals.drop 120).all (taoCaseOneGapPositive 100) = true :=
    all_of_take_drop (taoCaseOneGapPositive 100) 20 (taoCaseOneDirectIntervals.drop 120)
      taoCaseOneDirectChunk6_certify (by
        simpa [List.drop_drop] using! h140)
  have h100 : (taoCaseOneDirectIntervals.drop 100).all (taoCaseOneGapPositive 100) = true :=
    all_of_take_drop (taoCaseOneGapPositive 100) 20 (taoCaseOneDirectIntervals.drop 100)
      taoCaseOneDirectChunk5_certify (by
        simpa [List.drop_drop] using! h120)
  have h80 : (taoCaseOneDirectIntervals.drop 80).all (taoCaseOneGapPositive 100) = true :=
    all_of_take_drop (taoCaseOneGapPositive 100) 20 (taoCaseOneDirectIntervals.drop 80)
      taoCaseOneDirectChunk4_certify (by
        simpa [List.drop_drop] using! h100)
  have h60 : (taoCaseOneDirectIntervals.drop 60).all (taoCaseOneGapPositive 100) = true :=
    all_of_take_drop (taoCaseOneGapPositive 100) 20 (taoCaseOneDirectIntervals.drop 60)
      taoCaseOneDirectChunk3_certify (by
        simpa [List.drop_drop] using! h80)
  have h40 : (taoCaseOneDirectIntervals.drop 40).all (taoCaseOneGapPositive 100) = true :=
    all_of_take_drop (taoCaseOneGapPositive 100) 20 (taoCaseOneDirectIntervals.drop 40)
      taoCaseOneDirectChunk2_certify (by
        simpa [List.drop_drop] using! h60)
  have h20 : (taoCaseOneDirectIntervals.drop 20).all (taoCaseOneGapPositive 100) = true :=
    all_of_take_drop (taoCaseOneGapPositive 100) 20 (taoCaseOneDirectIntervals.drop 20)
      taoCaseOneDirectChunk1_certify (by
        simpa [List.drop_drop] using! h40)
  exact all_of_take_drop (taoCaseOneGapPositive 100) 20 taoCaseOneDirectIntervals
    taoCaseOneDirectChunk0_certify (by simpa using! h20)

end Erdos1038
