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
import ErdosProblems.Erdos76.Certificates.ExactN10_16
import ErdosProblems.Erdos76.Certificates.ExactN10_17
import ErdosProblems.Erdos76.Certificates.ExactN10_18
import ErdosProblems.Erdos76.Certificates.ExactN10_19
import ErdosProblems.Erdos76.Certificates.ExactN10_20
import ErdosProblems.Erdos76.Certificates.ExactN10_21
import ErdosProblems.Erdos76.Certificates.ExactN10_22
import ErdosProblems.Erdos76.Certificates.ExactN10_23

namespace Erdos76.CertificateChecker.Certificates.ExactN10Group2

def entries :=
    ExactN10_16.entries ++
    ExactN10_17.entries ++
    ExactN10_18.entries ++
    ExactN10_19.entries ++
    ExactN10_20.entries ++
    ExactN10_21.entries ++
    ExactN10_22.entries ++
    ExactN10_23.entries

theorem checks :
    entries.all (fun entry ↦ entry.2.checkExact (graphOfBits entry.1)) = true := by
  simp only [entries, List.all_append, ExactN10_16.checks,
    ExactN10_17.checks,
    ExactN10_18.checks,
    ExactN10_19.checks,
    ExactN10_20.checks,
    ExactN10_21.checks,
    ExactN10_22.checks,
    ExactN10_23.checks, Bool.and_self]

end Erdos76.CertificateChecker.Certificates.ExactN10Group2
