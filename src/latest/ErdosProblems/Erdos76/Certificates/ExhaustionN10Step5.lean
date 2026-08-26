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
import ErdosProblems.Erdos76.Certificates.ExhaustionN10Step5Chunk0
import ErdosProblems.Erdos76.Certificates.ExhaustionN10Step5Chunk1
import ErdosProblems.Erdos76.Certificates.ExhaustionN10Step5Chunk2
import ErdosProblems.Erdos76.Certificates.ExhaustionN10Step5Chunk3
import ErdosProblems.Erdos76.Certificates.ExhaustionN10Step5Chunk4
import ErdosProblems.Erdos76.Certificates.ExhaustionN10Step5Chunk5
import ErdosProblems.Erdos76.Certificates.ExhaustionN10Step5Chunk6

namespace Erdos76.CertificateExhaustion.Certificates.ExhaustionN10.Step5

def table : Array (Array (Option (Transition 10))) :=
    Chunk0.rows ++
    Chunk1.rows ++
    Chunk2.rows ++
    Chunk3.rows ++
    Chunk4.rows ++
    Chunk5.rows ++
    Chunk6.rows

theorem rowsValid : RowsValidFrom Erdos76.CertificateExhaustion.Certificates.ExhaustionN10.level5
    Erdos76.CertificateExhaustion.Certificates.ExhaustionN10.level6 0 table := by
  have h0 := Chunk0.valid
  have h1 := h0.append Chunk1.valid
  have h2 := h1.append Chunk2.valid
  have h3 := h2.append Chunk3.valid
  have h4 := h3.append Chunk4.valid
  have h5 := h4.append Chunk5.valid
  have h6 := h5.append Chunk6.valid
  simpa [table] using h6

theorem valid : StepValid Erdos76.CertificateExhaustion.Certificates.ExhaustionN10.level5
    Erdos76.CertificateExhaustion.Certificates.ExhaustionN10.level6 table :=
  StepValid.of_rowsValidFrom (by decide) rowsValid

theorem checks : checkStep Erdos76.CertificateExhaustion.Certificates.ExhaustionN10.level5
    Erdos76.CertificateExhaustion.Certificates.ExhaustionN10.level6 table = true :=
  (checkStep_eq_true_iff _ _ _).mpr valid

end Erdos76.CertificateExhaustion.Certificates.ExhaustionN10.Step5
