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
import ErdosProblems.Erdos76.Certificates.ExactN10_32
import ErdosProblems.Erdos76.Certificates.ExactN10_33
import ErdosProblems.Erdos76.Certificates.ExactN10_34
import ErdosProblems.Erdos76.Certificates.ExactN10_35
import ErdosProblems.Erdos76.Certificates.ExactN10_36
import ErdosProblems.Erdos76.Certificates.ExactN10_37
import ErdosProblems.Erdos76.Certificates.ExactN10_38
import ErdosProblems.Erdos76.Certificates.ExactN10_39

namespace Erdos76.CertificateChecker.Certificates.ExactN10Group4

def entries :=
    ExactN10_32.entries ++
    ExactN10_33.entries ++
    ExactN10_34.entries ++
    ExactN10_35.entries ++
    ExactN10_36.entries ++
    ExactN10_37.entries ++
    ExactN10_38.entries ++
    ExactN10_39.entries

theorem checks :
    entries.all (fun entry ↦ entry.2.checkExact (graphOfBits entry.1)) = true := by
  simp only [entries, List.all_append, ExactN10_32.checks,
    ExactN10_33.checks,
    ExactN10_34.checks,
    ExactN10_35.checks,
    ExactN10_36.checks,
    ExactN10_37.checks,
    ExactN10_38.checks,
    ExactN10_39.checks, Bool.and_self]

end Erdos76.CertificateChecker.Certificates.ExactN10Group4
