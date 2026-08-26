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
# Checked unordered-edge indexing at order thirteen

The thirteen rows are separate declarations because their combined kernel
reduction exceeds the stock per-command heartbeat budget.  The final theorem
only dispatches on the first vertex and therefore performs no large search.
-/

namespace Erdos76.CertificateChecker.PackingCert

private theorem pairIndexRowValid_13_0 :
    PairIndexRowValid 13 (0 : Fin 13) := by decide
private theorem pairIndexRowValid_13_1 :
    PairIndexRowValid 13 (1 : Fin 13) := by decide
private theorem pairIndexRowValid_13_2 :
    PairIndexRowValid 13 (2 : Fin 13) := by decide
private theorem pairIndexRowValid_13_3 :
    PairIndexRowValid 13 (3 : Fin 13) := by decide
private theorem pairIndexRowValid_13_4 :
    PairIndexRowValid 13 (4 : Fin 13) := by decide
private theorem pairIndexRowValid_13_5 :
    PairIndexRowValid 13 (5 : Fin 13) := by decide
private theorem pairIndexRowValid_13_6 :
    PairIndexRowValid 13 (6 : Fin 13) := by decide
private theorem pairIndexRowValid_13_7 :
    PairIndexRowValid 13 (7 : Fin 13) := by decide
private theorem pairIndexRowValid_13_8 :
    PairIndexRowValid 13 (8 : Fin 13) := by decide
private theorem pairIndexRowValid_13_9 :
    PairIndexRowValid 13 (9 : Fin 13) := by decide
private theorem pairIndexRowValid_13_10 :
    PairIndexRowValid 13 (10 : Fin 13) := by decide
private theorem pairIndexRowValid_13_11 :
    PairIndexRowValid 13 (11 : Fin 13) := by decide
private theorem pairIndexRowValid_13_12 :
    PairIndexRowValid 13 (12 : Fin 13) := by decide

theorem pairIndexValid_13 : PairIndexValid 13 := by
  apply pairIndexValid_of_rows
  intro i
  fin_cases i <;> first
    | exact pairIndexRowValid_13_0
    | exact pairIndexRowValid_13_1
    | exact pairIndexRowValid_13_2
    | exact pairIndexRowValid_13_3
    | exact pairIndexRowValid_13_4
    | exact pairIndexRowValid_13_5
    | exact pairIndexRowValid_13_6
    | exact pairIndexRowValid_13_7
    | exact pairIndexRowValid_13_8
    | exact pairIndexRowValid_13_9
    | exact pairIndexRowValid_13_10
    | exact pairIndexRowValid_13_11
    | exact pairIndexRowValid_13_12

end Erdos76.CertificateChecker.PackingCert
