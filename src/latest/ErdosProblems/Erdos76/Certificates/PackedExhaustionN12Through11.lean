/-
Copyright 2026 The Lean-Proofs Authors.
Licensed under the Apache License, Version 2.0.
-/
import ErdosProblems.Erdos76.Certificates.PackedExhaustionN12Through10
import ErdosProblems.Erdos76.Certificates.PackedExhaustionN12Step10

/-! The reusable n=12 exhaustion prefix through eleven missing edges. -/
namespace Erdos76.CertificateExhaustion.Certificates.PackedExhaustionN12Through11

open PackedExhaustionN12

def data : ExhaustionData 12 := {
  levels := #[level0.toArray, level1.toArray, level2.toArray,
    level3.toArray, level4.toArray, level5.toArray, level6.toArray,
    level7.toArray, level8.toArray, level9.toArray, level10.toArray,
    level11.toArray]
  steps := #[Step0.table, Step1.table, Step2.table, Step3.table,
    Step4.table, Step5.table, Step6.table, Step7.table, Step8.table,
    Step9.table, Step10.table]
}

theorem valid : data.Valid := by
  refine ⟨by decide, by decide, by decide, ?_⟩
  intro k
  fin_cases k
  · simpa [data, ExhaustionData.level, ExhaustionData.step] using Step0.stepValid
  · simpa [data, ExhaustionData.level, ExhaustionData.step] using Step1.stepValid
  · simpa [data, ExhaustionData.level, ExhaustionData.step] using Step2.stepValid
  · simpa [data, ExhaustionData.level, ExhaustionData.step] using Step3.stepValid
  · simpa [data, ExhaustionData.level, ExhaustionData.step] using Step4.stepValid
  · simpa [data, ExhaustionData.level, ExhaustionData.step] using Step5.stepValid
  · simpa [data, ExhaustionData.level, ExhaustionData.step] using Step6.stepValid
  · simpa [data, ExhaustionData.level, ExhaustionData.step] using Step7.stepValid
  · simpa [data, ExhaustionData.level, ExhaustionData.step] using Step8.stepValid
  · simpa [data, ExhaustionData.level, ExhaustionData.step] using Step9.stepValid
  · simpa [data, ExhaustionData.level, ExhaustionData.step] using Step10.stepValid

end Erdos76.CertificateExhaustion.Certificates.PackedExhaustionN12Through11
