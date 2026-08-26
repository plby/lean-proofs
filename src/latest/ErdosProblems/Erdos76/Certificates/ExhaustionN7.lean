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
import ErdosProblems.Erdos76.Certificates.ExhaustionN7Step0
import ErdosProblems.Erdos76.Certificates.ExhaustionN7Step1
import ErdosProblems.Erdos76.Certificates.ExhaustionN7Step2

namespace Erdos76.CertificateExhaustion.Certificates.ExhaustionN7

def data : ExhaustionData 7 := {
  levels := #[
      Erdos76.CertificateExhaustion.Certificates.ExhaustionN7.level0,
      Erdos76.CertificateExhaustion.Certificates.ExhaustionN7.level1,
      Erdos76.CertificateExhaustion.Certificates.ExhaustionN7.level2,
      Erdos76.CertificateExhaustion.Certificates.ExhaustionN7.level3]
  steps := #[
      Erdos76.CertificateExhaustion.Certificates.ExhaustionN7.Step0.table,
      Erdos76.CertificateExhaustion.Certificates.ExhaustionN7.Step1.table,
      Erdos76.CertificateExhaustion.Certificates.ExhaustionN7.Step2.table]
}

theorem checks : data.check = true := by
  decide

/-- Every labeled seven-vertex graph with three edges is isomorphic to one of
the five representatives in `level3`. -/
theorem represents_three_edges (G : SimpleGraph (Fin 7))
    (hcard : G.edgeSet.ncard = 3) : IsRepresented level3 G := by
  have hrep := data.check_representsGraph_atTarget checks G (by
    simpa [data] using hcard)
  simpa [data, ExhaustionData.level] using hrep

end Erdos76.CertificateExhaustion.Certificates.ExhaustionN7
