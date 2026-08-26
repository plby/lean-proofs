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
import ErdosProblems.Erdos76.Certificates.ExactN10_24
import ErdosProblems.Erdos76.Certificates.ExactN10_25
import ErdosProblems.Erdos76.Certificates.ExactN10_26
import ErdosProblems.Erdos76.Certificates.ExactN10_27
import ErdosProblems.Erdos76.Certificates.ExactN10_28
import ErdosProblems.Erdos76.Certificates.ExactN10_29
import ErdosProblems.Erdos76.Certificates.ExactN10_30
import ErdosProblems.Erdos76.Certificates.ExactN10_31

namespace Erdos76.CertificateChecker.Certificates.ExactN10Group3

def entries :=
    ExactN10_24.entries ++
    ExactN10_25.entries ++
    ExactN10_26.entries ++
    ExactN10_27.entries ++
    ExactN10_28.entries ++
    ExactN10_29.entries ++
    ExactN10_30.entries ++
    ExactN10_31.entries

theorem checks :
    entries.all (fun entry ↦ entry.2.checkExact (graphOfBits entry.1)) = true := by
  simp only [entries, List.all_append, ExactN10_24.checks,
    ExactN10_25.checks,
    ExactN10_26.checks,
    ExactN10_27.checks,
    ExactN10_28.checks,
    ExactN10_29.checks,
    ExactN10_30.checks,
    ExactN10_31.checks, Bool.and_self]

end Erdos76.CertificateChecker.Certificates.ExactN10Group3
