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
import ErdosProblems.Erdos76.LinearCertificateChecker

/-!
# Checked unordered-edge indexing at order eleven

Each first-vertex row is reduced as a separate ordinary `decide` goal.  This
keeps the proof under the stock kernel limits while the assembly theorem is
independent of the implementation of `edgeIndex`.
-/

namespace Erdos76.CertificateChecker.PackingCert

/-- The canonical flat edge index classifies unordered non-loop pairs on
`Fin 11`. -/
theorem pairIndexValid_11 : PairIndexValid 11 := by
  apply pairIndexValid_of_rows
  intro i
  fin_cases i <;> decide

end Erdos76.CertificateChecker.PackingCert
