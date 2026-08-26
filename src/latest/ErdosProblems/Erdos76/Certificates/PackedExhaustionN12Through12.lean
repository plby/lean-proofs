/-
Copyright 2026 The Lean-Proofs Authors.
Licensed under the Apache License, Version 2.0.
-/
import ErdosProblems.Erdos76.Certificates.PackedExhaustionN12Through11
import ErdosProblems.Erdos76.Certificates.PackedExhaustionN12Step11
import ErdosProblems.Erdos76.ExhaustionDataExtend

/-! The reusable n=12 exhaustion prefix through twelve missing edges. -/
namespace Erdos76.CertificateExhaustion.Certificates.PackedExhaustionN12Through12

open PackedExhaustionN12

private def prefix0 : ExhaustionData 12 := {
  levels := #[level0.toArray]
  steps := #[]
}

private theorem prefix0Valid : prefix0.Valid := by decide

private theorem prefix0Last :
    prefix0.level prefix0.steps.size = level0.toArray := by
  rfl

private def prefix1 : ExhaustionData 12 :=
  ExhaustionData.extend prefix0 level1.toArray Step0.table

private theorem prefix1Valid : prefix1.Valid := by
  unfold prefix1
  apply prefix0Valid.extend
  rw [prefix0Last]
  exact Step0.stepValid

private theorem prefix1Last :
    prefix1.level prefix1.steps.size = level1.toArray := by
  unfold prefix1
  exact prefix0Valid.extend_lastLevel

private def prefix2 : ExhaustionData 12 :=
  ExhaustionData.extend prefix1 level2.toArray Step1.table

private theorem prefix2Valid : prefix2.Valid := by
  unfold prefix2
  apply prefix1Valid.extend
  rw [prefix1Last]
  exact Step1.stepValid

private theorem prefix2Last :
    prefix2.level prefix2.steps.size = level2.toArray := by
  unfold prefix2
  exact prefix1Valid.extend_lastLevel

private def prefix3 : ExhaustionData 12 :=
  ExhaustionData.extend prefix2 level3.toArray Step2.table

private theorem prefix3Valid : prefix3.Valid := by
  unfold prefix3
  apply prefix2Valid.extend
  rw [prefix2Last]
  exact Step2.stepValid

private theorem prefix3Last :
    prefix3.level prefix3.steps.size = level3.toArray := by
  unfold prefix3
  exact prefix2Valid.extend_lastLevel

private def prefix4 : ExhaustionData 12 :=
  ExhaustionData.extend prefix3 level4.toArray Step3.table

private theorem prefix4Valid : prefix4.Valid := by
  unfold prefix4
  apply prefix3Valid.extend
  rw [prefix3Last]
  exact Step3.stepValid

private theorem prefix4Last :
    prefix4.level prefix4.steps.size = level4.toArray := by
  unfold prefix4
  exact prefix3Valid.extend_lastLevel

private def prefix5 : ExhaustionData 12 :=
  ExhaustionData.extend prefix4 level5.toArray Step4.table

private theorem prefix5Valid : prefix5.Valid := by
  unfold prefix5
  apply prefix4Valid.extend
  rw [prefix4Last]
  exact Step4.stepValid

private theorem prefix5Last :
    prefix5.level prefix5.steps.size = level5.toArray := by
  unfold prefix5
  exact prefix4Valid.extend_lastLevel

private def prefix6 : ExhaustionData 12 :=
  ExhaustionData.extend prefix5 level6.toArray Step5.table

private theorem prefix6Valid : prefix6.Valid := by
  unfold prefix6
  apply prefix5Valid.extend
  rw [prefix5Last]
  exact Step5.stepValid

private theorem prefix6Last :
    prefix6.level prefix6.steps.size = level6.toArray := by
  unfold prefix6
  exact prefix5Valid.extend_lastLevel

private def prefix7 : ExhaustionData 12 :=
  ExhaustionData.extend prefix6 level7.toArray Step6.table

private theorem prefix7Valid : prefix7.Valid := by
  unfold prefix7
  apply prefix6Valid.extend
  rw [prefix6Last]
  exact Step6.stepValid

private theorem prefix7Last :
    prefix7.level prefix7.steps.size = level7.toArray := by
  unfold prefix7
  exact prefix6Valid.extend_lastLevel

private def prefix8 : ExhaustionData 12 :=
  ExhaustionData.extend prefix7 level8.toArray Step7.table

private theorem prefix8Valid : prefix8.Valid := by
  unfold prefix8
  apply prefix7Valid.extend
  rw [prefix7Last]
  exact Step7.stepValid

private theorem prefix8Last :
    prefix8.level prefix8.steps.size = level8.toArray := by
  unfold prefix8
  exact prefix7Valid.extend_lastLevel

private def prefix9 : ExhaustionData 12 :=
  ExhaustionData.extend prefix8 level9.toArray Step8.table

private theorem prefix9Valid : prefix9.Valid := by
  unfold prefix9
  apply prefix8Valid.extend
  rw [prefix8Last]
  exact Step8.stepValid

private theorem prefix9Last :
    prefix9.level prefix9.steps.size = level9.toArray := by
  unfold prefix9
  exact prefix8Valid.extend_lastLevel

private def prefix10 : ExhaustionData 12 :=
  ExhaustionData.extend prefix9 level10.toArray Step9.table

private theorem prefix10Valid : prefix10.Valid := by
  unfold prefix10
  apply prefix9Valid.extend
  rw [prefix9Last]
  exact Step9.stepValid

private theorem prefix10Last :
    prefix10.level prefix10.steps.size = level10.toArray := by
  unfold prefix10
  exact prefix9Valid.extend_lastLevel

private def prefix11 : ExhaustionData 12 :=
  ExhaustionData.extend prefix10 level11.toArray Step10.table

private theorem prefix11Valid : prefix11.Valid := by
  unfold prefix11
  apply prefix10Valid.extend
  rw [prefix10Last]
  exact Step10.stepValid

private theorem prefix11Last :
    prefix11.level prefix11.steps.size = level11.toArray := by
  unfold prefix11
  exact prefix10Valid.extend_lastLevel

def data : ExhaustionData 12 :=
  ExhaustionData.extend prefix11 level12.toArray Step11.table

theorem valid : data.Valid := by
  unfold data
  apply prefix11Valid.extend
  rw [prefix11Last]
  exact Step11.stepValid

end Erdos76.CertificateExhaustion.Certificates.PackedExhaustionN12Through12
