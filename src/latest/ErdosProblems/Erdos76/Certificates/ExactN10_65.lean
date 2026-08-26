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
import ErdosProblems.Erdos76.CertificateChecker

/-! Automatically generated exact-decomposition certificate for one `n = 10`
base of the Gruslys--Letzter almost-complete theorem.  The generator is
untrusted; `checks` is an ordinary kernel reduction via `by decide`. -/

namespace Erdos76.CertificateChecker.Certificates.ExactN10_65

def entries : List (BitVec (edgeCount 10) × PackingCert 10) := [
    (0x1def7f7efbff#45, {
      denominator := 4
      terms := [
        ⟨0, 1, 2, 3⟩,
        ⟨0, 1, 3, 1⟩,
        ⟨0, 2, 3, 1⟩,
        ⟨0, 3, 4, 2⟩,
        ⟨0, 4, 6, 1⟩,
        ⟨0, 4, 7, 1⟩,
        ⟨0, 6, 7, 1⟩,
        ⟨0, 6, 8, 2⟩,
        ⟨0, 7, 8, 2⟩,
        ⟨1, 2, 3, 1⟩,
        ⟨1, 3, 4, 2⟩,
        ⟨1, 4, 9, 2⟩,
        ⟨1, 5, 7, 3⟩,
        ⟨1, 5, 8, 1⟩,
        ⟨1, 7, 8, 1⟩,
        ⟨1, 8, 9, 2⟩,
        ⟨2, 3, 5, 2⟩,
        ⟨2, 4, 8, 2⟩,
        ⟨2, 4, 9, 2⟩,
        ⟨2, 5, 6, 1⟩,
        ⟨2, 5, 8, 1⟩,
        ⟨2, 6, 8, 1⟩,
        ⟨2, 6, 9, 2⟩,
        ⟨3, 5, 6, 2⟩,
        ⟨3, 6, 7, 1⟩,
        ⟨3, 6, 9, 1⟩,
        ⟨3, 7, 9, 3⟩,
        ⟨4, 5, 6, 1⟩,
        ⟨4, 5, 7, 1⟩,
        ⟨4, 5, 8, 2⟩,
        ⟨4, 6, 7, 2⟩,
        ⟨6, 8, 9, 1⟩,
        ⟨7, 8, 9, 1⟩]
    })]

theorem checks :
    entries.all (fun entry ↦ entry.2.checkExact (graphOfBits entry.1)) = true := by
  decide

end Erdos76.CertificateChecker.Certificates.ExactN10_65
