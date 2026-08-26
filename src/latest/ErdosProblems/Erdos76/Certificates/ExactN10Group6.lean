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
import ErdosProblems.Erdos76.Certificates.ExactN10_48
import ErdosProblems.Erdos76.Certificates.ExactN10_49
import ErdosProblems.Erdos76.Certificates.ExactN10_50
import ErdosProblems.Erdos76.Certificates.ExactN10_51
import ErdosProblems.Erdos76.Certificates.ExactN10_52
import ErdosProblems.Erdos76.Certificates.ExactN10_53
import ErdosProblems.Erdos76.Certificates.ExactN10_54
import ErdosProblems.Erdos76.Certificates.ExactN10_55

namespace Erdos76.CertificateChecker.Certificates.ExactN10Group6

def entries :=
    ExactN10_48.entries ++
    ExactN10_49.entries ++
    ExactN10_50.entries ++
    ExactN10_51.entries ++
    ExactN10_52.entries ++
    ExactN10_53.entries ++
    ExactN10_54.entries ++
    ExactN10_55.entries

theorem checks :
    entries.all (fun entry ↦ entry.2.checkExact (graphOfBits entry.1)) = true := by
  simp only [entries, List.all_append, ExactN10_48.checks,
    ExactN10_49.checks,
    ExactN10_50.checks,
    ExactN10_51.checks,
    ExactN10_52.checks,
    ExactN10_53.checks,
    ExactN10_54.checks,
    ExactN10_55.checks, Bool.and_self]

end Erdos76.CertificateChecker.Certificates.ExactN10Group6
