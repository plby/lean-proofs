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

/-! Automatically generated exact-decomposition certificates for the
`n = 9` base of the Gruslys--Letzter almost-complete theorem.  The generator
is untrusted; `checks` is an ordinary kernel reduction via `by decide`. -/

namespace Erdos76.CertificateChecker.Certificates.ExactN9_0

def entries : List (BitVec (edgeCount 9) × PackingCert 9) := [
    (0xe0fffffff#36, {
      denominator := 6
      terms := [
        ⟨0, 1, 4, 1⟩,
        ⟨0, 1, 7, 5⟩,
        ⟨0, 2, 4, 2⟩,
        ⟨0, 2, 6, 4⟩,
        ⟨0, 3, 5, 4⟩,
        ⟨0, 3, 6, 2⟩,
        ⟨0, 4, 5, 2⟩,
        ⟨0, 4, 7, 1⟩,
        ⟨1, 2, 5, 4⟩,
        ⟨1, 2, 6, 2⟩,
        ⟨1, 3, 4, 2⟩,
        ⟨1, 3, 5, 2⟩,
        ⟨1, 3, 6, 2⟩,
        ⟨1, 4, 6, 2⟩,
        ⟨1, 4, 7, 1⟩,
        ⟨2, 3, 4, 1⟩,
        ⟨2, 3, 7, 5⟩,
        ⟨2, 4, 5, 2⟩,
        ⟨2, 4, 7, 1⟩,
        ⟨3, 4, 6, 2⟩,
        ⟨3, 4, 7, 1⟩,
        ⟨4, 5, 6, 1⟩,
        ⟨4, 5, 7, 1⟩,
        ⟨4, 6, 7, 1⟩,
        ⟨5, 6, 7, 2⟩,
        ⟨5, 6, 8, 3⟩,
        ⟨5, 7, 8, 3⟩,
        ⟨6, 7, 8, 3⟩]
    }),
    (0xf0fdfffff#36, {
      denominator := 6
      terms := [
        ⟨0, 1, 2, 4⟩,
        ⟨0, 1, 4, 1⟩,
        ⟨0, 1, 5, 1⟩,
        ⟨0, 2, 3, 1⟩,
        ⟨0, 2, 6, 1⟩,
        ⟨0, 3, 4, 5⟩,
        ⟨0, 5, 6, 5⟩,
        ⟨1, 2, 5, 2⟩,
        ⟨1, 3, 5, 1⟩,
        ⟨1, 3, 6, 5⟩,
        ⟨1, 4, 7, 5⟩,
        ⟨1, 5, 6, 1⟩,
        ⟨1, 5, 7, 1⟩,
        ⟨2, 3, 5, 2⟩,
        ⟨2, 3, 7, 3⟩,
        ⟨2, 4, 6, 5⟩,
        ⟨2, 4, 7, 1⟩,
        ⟨2, 5, 7, 2⟩,
        ⟨3, 4, 6, 1⟩,
        ⟨3, 5, 7, 3⟩,
        ⟨4, 5, 8, 6⟩,
        ⟨6, 7, 8, 6⟩]
    })]

theorem checks :
    entries.all (fun entry ↦ entry.2.checkExact (graphOfBits entry.1)) = true := by
  decide

end Erdos76.CertificateChecker.Certificates.ExactN9_0
