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
import ErdosProblems.Erdos76.Certificates.ExactN10_8
import ErdosProblems.Erdos76.Certificates.ExactN10_9
import ErdosProblems.Erdos76.Certificates.ExactN10_10
import ErdosProblems.Erdos76.Certificates.ExactN10_11
import ErdosProblems.Erdos76.Certificates.ExactN10_12
import ErdosProblems.Erdos76.Certificates.ExactN10_13
import ErdosProblems.Erdos76.Certificates.ExactN10_14
import ErdosProblems.Erdos76.Certificates.ExactN10_15

namespace Erdos76.CertificateChecker.Certificates.ExactN10Group1

def entries :=
    ExactN10_8.entries ++
    ExactN10_9.entries ++
    ExactN10_10.entries ++
    ExactN10_11.entries ++
    ExactN10_12.entries ++
    ExactN10_13.entries ++
    ExactN10_14.entries ++
    ExactN10_15.entries

theorem checks :
    entries.all (fun entry ↦ entry.2.checkExact (graphOfBits entry.1)) = true := by
  simp only [entries, List.all_append, ExactN10_8.checks,
    ExactN10_9.checks,
    ExactN10_10.checks,
    ExactN10_11.checks,
    ExactN10_12.checks,
    ExactN10_13.checks,
    ExactN10_14.checks,
    ExactN10_15.checks, Bool.and_self]

end Erdos76.CertificateChecker.Certificates.ExactN10Group1
