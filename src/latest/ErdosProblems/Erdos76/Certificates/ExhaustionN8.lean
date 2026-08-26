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
import ErdosProblems.Erdos76.Certificates.ExhaustionN8Step0
import ErdosProblems.Erdos76.Certificates.ExhaustionN8Step1
import ErdosProblems.Erdos76.Certificates.ExhaustionN8Step2
import ErdosProblems.Erdos76.Certificates.ExhaustionN8Step3

namespace Erdos76.CertificateExhaustion.Certificates.ExhaustionN8

def data : ExhaustionData 8 := {
  levels := #[
      Erdos76.CertificateExhaustion.Certificates.ExhaustionN8.level0,
      Erdos76.CertificateExhaustion.Certificates.ExhaustionN8.level1,
      Erdos76.CertificateExhaustion.Certificates.ExhaustionN8.level2,
      Erdos76.CertificateExhaustion.Certificates.ExhaustionN8.level3,
      Erdos76.CertificateExhaustion.Certificates.ExhaustionN8.level4]
  steps := #[
      Erdos76.CertificateExhaustion.Certificates.ExhaustionN8.Step0.table,
      Erdos76.CertificateExhaustion.Certificates.ExhaustionN8.Step1.table,
      Erdos76.CertificateExhaustion.Certificates.ExhaustionN8.Step2.table,
      Erdos76.CertificateExhaustion.Certificates.ExhaustionN8.Step3.table]
}

theorem checks : data.check = true := by
  decide

theorem represents_target_edges (G : SimpleGraph (Fin 8))
    (hcard : G.edgeSet.ncard = 4) : IsRepresented level4 G := by
  have hrep := data.check_representsGraph_atTarget checks G (by
    simpa [data] using hcard)
  simpa [data, ExhaustionData.level] using hrep

end Erdos76.CertificateExhaustion.Certificates.ExhaustionN8
