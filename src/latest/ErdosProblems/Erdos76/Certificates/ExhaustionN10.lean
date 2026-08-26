/-
Copyright 2026 The Lean-Proofs Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
import ErdosProblems.Erdos76.Certificates.ExhaustionN10Step0
import ErdosProblems.Erdos76.Certificates.ExhaustionN10Step1
import ErdosProblems.Erdos76.Certificates.ExhaustionN10Step2
import ErdosProblems.Erdos76.Certificates.ExhaustionN10Step3
import ErdosProblems.Erdos76.Certificates.ExhaustionN10Step4
import ErdosProblems.Erdos76.Certificates.ExhaustionN10Step5

namespace Erdos76.CertificateExhaustion.Certificates.ExhaustionN10

def data : ExhaustionData 10 := {
  levels := #[
      Erdos76.CertificateExhaustion.Certificates.ExhaustionN10.level0,
      Erdos76.CertificateExhaustion.Certificates.ExhaustionN10.level1,
      Erdos76.CertificateExhaustion.Certificates.ExhaustionN10.level2,
      Erdos76.CertificateExhaustion.Certificates.ExhaustionN10.level3,
      Erdos76.CertificateExhaustion.Certificates.ExhaustionN10.level4,
      Erdos76.CertificateExhaustion.Certificates.ExhaustionN10.level5,
      Erdos76.CertificateExhaustion.Certificates.ExhaustionN10.level6]
  steps := #[
      Erdos76.CertificateExhaustion.Certificates.ExhaustionN10.Step0.table,
      Erdos76.CertificateExhaustion.Certificates.ExhaustionN10.Step1.table,
      Erdos76.CertificateExhaustion.Certificates.ExhaustionN10.Step2.table,
      Erdos76.CertificateExhaustion.Certificates.ExhaustionN10.Step3.table,
      Erdos76.CertificateExhaustion.Certificates.ExhaustionN10.Step4.table,
      Erdos76.CertificateExhaustion.Certificates.ExhaustionN10.Step5.table]
}

theorem valid : data.Valid := by
  refine ⟨by decide, by decide, by decide, ?_⟩
  intro k
  fin_cases k
  · exact Step0.valid
  · exact Step1.valid
  · exact Step2.valid
  · exact Step3.valid
  · exact Step4.valid
  · exact Step5.valid

theorem checks : data.check = true :=
  (ExhaustionData.check_eq_true_iff data).mpr valid

theorem represents_target_edges (G : SimpleGraph (Fin 10))
    (hcard : G.edgeSet.ncard = 6) : IsRepresented level6 G := by
  have hrep := data.check_representsGraph_atTarget checks G (by
    simpa [data] using hcard)
  simpa [data, ExhaustionData.level] using hrep

end Erdos76.CertificateExhaustion.Certificates.ExhaustionN10
