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
import ErdosProblems.Erdos76.Certificates.ExhaustionN10Step4Chunk0
import ErdosProblems.Erdos76.Certificates.ExhaustionN10Step4Chunk1
import ErdosProblems.Erdos76.Certificates.ExhaustionN10Step4Chunk2

namespace Erdos76.CertificateExhaustion.Certificates.ExhaustionN10.Step4

def table : Array (Array (Option (Transition 10))) :=
    Chunk0.rows ++
    Chunk1.rows ++
    Chunk2.rows

theorem rowsValid : RowsValidFrom Erdos76.CertificateExhaustion.Certificates.ExhaustionN10.level4
    Erdos76.CertificateExhaustion.Certificates.ExhaustionN10.level5 0 table := by
  have h0 := Chunk0.valid
  have h1 := h0.append Chunk1.valid
  have h2 := h1.append Chunk2.valid
  simpa [table] using h2

theorem valid : StepValid Erdos76.CertificateExhaustion.Certificates.ExhaustionN10.level4
    Erdos76.CertificateExhaustion.Certificates.ExhaustionN10.level5 table :=
  StepValid.of_rowsValidFrom (by decide) rowsValid

theorem checks : checkStep Erdos76.CertificateExhaustion.Certificates.ExhaustionN10.level4
    Erdos76.CertificateExhaustion.Certificates.ExhaustionN10.level5 table = true :=
  (checkStep_eq_true_iff _ _ _).mpr valid

end Erdos76.CertificateExhaustion.Certificates.ExhaustionN10.Step4
