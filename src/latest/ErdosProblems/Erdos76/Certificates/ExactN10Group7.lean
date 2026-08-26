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
import ErdosProblems.Erdos76.Certificates.ExactN10_56
import ErdosProblems.Erdos76.Certificates.ExactN10_57
import ErdosProblems.Erdos76.Certificates.ExactN10_58
import ErdosProblems.Erdos76.Certificates.ExactN10_59
import ErdosProblems.Erdos76.Certificates.ExactN10_60
import ErdosProblems.Erdos76.Certificates.ExactN10_61
import ErdosProblems.Erdos76.Certificates.ExactN10_62
import ErdosProblems.Erdos76.Certificates.ExactN10_63

namespace Erdos76.CertificateChecker.Certificates.ExactN10Group7

def entries :=
    ExactN10_56.entries ++
    ExactN10_57.entries ++
    ExactN10_58.entries ++
    ExactN10_59.entries ++
    ExactN10_60.entries ++
    ExactN10_61.entries ++
    ExactN10_62.entries ++
    ExactN10_63.entries

theorem checks :
    entries.all (fun entry ↦ entry.2.checkExact (graphOfBits entry.1)) = true := by
  simp only [entries, List.all_append, ExactN10_56.checks,
    ExactN10_57.checks,
    ExactN10_58.checks,
    ExactN10_59.checks,
    ExactN10_60.checks,
    ExactN10_61.checks,
    ExactN10_62.checks,
    ExactN10_63.checks, Bool.and_self]

end Erdos76.CertificateChecker.Certificates.ExactN10Group7
