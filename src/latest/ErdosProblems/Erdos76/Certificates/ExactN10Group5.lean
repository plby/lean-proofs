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
import ErdosProblems.Erdos76.Certificates.ExactN10_40
import ErdosProblems.Erdos76.Certificates.ExactN10_41
import ErdosProblems.Erdos76.Certificates.ExactN10_42
import ErdosProblems.Erdos76.Certificates.ExactN10_43
import ErdosProblems.Erdos76.Certificates.ExactN10_44
import ErdosProblems.Erdos76.Certificates.ExactN10_45
import ErdosProblems.Erdos76.Certificates.ExactN10_46
import ErdosProblems.Erdos76.Certificates.ExactN10_47

namespace Erdos76.CertificateChecker.Certificates.ExactN10Group5

def entries :=
    ExactN10_40.entries ++
    ExactN10_41.entries ++
    ExactN10_42.entries ++
    ExactN10_43.entries ++
    ExactN10_44.entries ++
    ExactN10_45.entries ++
    ExactN10_46.entries ++
    ExactN10_47.entries

theorem checks :
    entries.all (fun entry ↦ entry.2.checkExact (graphOfBits entry.1)) = true := by
  simp only [entries, List.all_append, ExactN10_40.checks,
    ExactN10_41.checks,
    ExactN10_42.checks,
    ExactN10_43.checks,
    ExactN10_44.checks,
    ExactN10_45.checks,
    ExactN10_46.checks,
    ExactN10_47.checks, Bool.and_self]

end Erdos76.CertificateChecker.Certificates.ExactN10Group5
