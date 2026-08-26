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
import ErdosProblems.Erdos76.Certificates.ExactN7_0

namespace Erdos76.CertificateChecker.Certificates.ExactN7

def entries :=
    ExactN7_0.entries

theorem checks :
    entries.all (fun entry ↦ entry.2.checkExact (graphOfBits entry.1)) = true := by
  exact ExactN7_0.checks

end Erdos76.CertificateChecker.Certificates.ExactN7
