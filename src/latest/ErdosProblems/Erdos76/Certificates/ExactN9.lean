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
import ErdosProblems.Erdos76.Certificates.ExactN9_0
import ErdosProblems.Erdos76.Certificates.ExactN9_1
import ErdosProblems.Erdos76.Certificates.ExactN9_2
import ErdosProblems.Erdos76.Certificates.ExactN9_3
import ErdosProblems.Erdos76.Certificates.ExactN9_4
import ErdosProblems.Erdos76.Certificates.ExactN9_5
import ErdosProblems.Erdos76.Certificates.ExactN9_6
import ErdosProblems.Erdos76.Certificates.ExactN9_7
import ErdosProblems.Erdos76.Certificates.ExactN9_8
import ErdosProblems.Erdos76.Certificates.ExactN9_9
import ErdosProblems.Erdos76.Certificates.ExactN9_10
import ErdosProblems.Erdos76.Certificates.ExactN9_11
import ErdosProblems.Erdos76.Certificates.ExactN9_12

namespace Erdos76.CertificateChecker.Certificates.ExactN9

def entries :=
    ExactN9_0.entries ++
    ExactN9_1.entries ++
    ExactN9_2.entries ++
    ExactN9_3.entries ++
    ExactN9_4.entries ++
    ExactN9_5.entries ++
    ExactN9_6.entries ++
    ExactN9_7.entries ++
    ExactN9_8.entries ++
    ExactN9_9.entries ++
    ExactN9_10.entries ++
    ExactN9_11.entries ++
    ExactN9_12.entries

theorem checks :
    entries.all (fun entry ↦ entry.2.checkExact (graphOfBits entry.1)) = true := by
  simp only [entries, List.all_append, ExactN9_0.checks, ExactN9_1.checks,
    ExactN9_2.checks, ExactN9_3.checks, ExactN9_4.checks, ExactN9_5.checks,
    ExactN9_6.checks, ExactN9_7.checks, ExactN9_8.checks, ExactN9_9.checks,
    ExactN9_10.checks, ExactN9_11.checks, ExactN9_12.checks, Bool.and_self]

end Erdos76.CertificateChecker.Certificates.ExactN9
