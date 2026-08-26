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
import ErdosProblems.Erdos76.Certificates.ExactN10Group0
import ErdosProblems.Erdos76.Certificates.ExactN10Group1
import ErdosProblems.Erdos76.Certificates.ExactN10Group2
import ErdosProblems.Erdos76.Certificates.ExactN10Group3
import ErdosProblems.Erdos76.Certificates.ExactN10Group4
import ErdosProblems.Erdos76.Certificates.ExactN10Group5
import ErdosProblems.Erdos76.Certificates.ExactN10Group6
import ErdosProblems.Erdos76.Certificates.ExactN10Group7
import ErdosProblems.Erdos76.Certificates.ExactN10Group8

namespace Erdos76.CertificateChecker.Certificates.ExactN10

def entries :=
    ExactN10Group0.entries ++
    ExactN10Group1.entries ++
    ExactN10Group2.entries ++
    ExactN10Group3.entries ++
    ExactN10Group4.entries ++
    ExactN10Group5.entries ++
    ExactN10Group6.entries ++
    ExactN10Group7.entries ++
    ExactN10Group8.entries

theorem checks :
    entries.all (fun entry ↦ entry.2.checkExact (graphOfBits entry.1)) = true := by
  simp only [entries, List.all_append, ExactN10Group0.checks,
    ExactN10Group1.checks,
    ExactN10Group2.checks,
    ExactN10Group3.checks,
    ExactN10Group4.checks,
    ExactN10Group5.checks,
    ExactN10Group6.checks,
    ExactN10Group7.checks,
    ExactN10Group8.checks, Bool.and_self]

end Erdos76.CertificateChecker.Certificates.ExactN10
