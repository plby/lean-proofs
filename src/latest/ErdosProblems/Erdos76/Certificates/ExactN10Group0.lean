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
import ErdosProblems.Erdos76.Certificates.ExactN10_0
import ErdosProblems.Erdos76.Certificates.ExactN10_1
import ErdosProblems.Erdos76.Certificates.ExactN10_2
import ErdosProblems.Erdos76.Certificates.ExactN10_3
import ErdosProblems.Erdos76.Certificates.ExactN10_4
import ErdosProblems.Erdos76.Certificates.ExactN10_5
import ErdosProblems.Erdos76.Certificates.ExactN10_6
import ErdosProblems.Erdos76.Certificates.ExactN10_7

namespace Erdos76.CertificateChecker.Certificates.ExactN10Group0

def entries :=
    ExactN10_0.entries ++
    ExactN10_1.entries ++
    ExactN10_2.entries ++
    ExactN10_3.entries ++
    ExactN10_4.entries ++
    ExactN10_5.entries ++
    ExactN10_6.entries ++
    ExactN10_7.entries

theorem checks :
    entries.all (fun entry ↦ entry.2.checkExact (graphOfBits entry.1)) = true := by
  simp only [entries, List.all_append, ExactN10_0.checks,
    ExactN10_1.checks,
    ExactN10_2.checks,
    ExactN10_3.checks,
    ExactN10_4.checks,
    ExactN10_5.checks,
    ExactN10_6.checks,
    ExactN10_7.checks, Bool.and_self]

end Erdos76.CertificateChecker.Certificates.ExactN10Group0
