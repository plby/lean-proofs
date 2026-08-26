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

namespace Erdos76.CertificateChecker.Certificates.ExactN9_10

def entries : List (BitVec (edgeCount 9) × PackingCert 9) := [
    (0xbef3f7fff#36, {
      denominator := 12
      terms := [
        ⟨0, 1, 2, 8⟩,
        ⟨0, 1, 3, 4⟩,
        ⟨0, 2, 3, 4⟩,
        ⟨0, 3, 5, 4⟩,
        ⟨0, 4, 5, 4⟩,
        ⟨0, 4, 7, 8⟩,
        ⟨0, 5, 7, 4⟩,
        ⟨1, 2, 6, 4⟩,
        ⟨1, 3, 4, 3⟩,
        ⟨1, 3, 6, 5⟩,
        ⟨1, 4, 5, 3⟩,
        ⟨1, 4, 6, 3⟩,
        ⟨1, 4, 8, 3⟩,
        ⟨1, 5, 8, 9⟩,
        ⟨2, 3, 4, 1⟩,
        ⟨2, 3, 5, 4⟩,
        ⟨2, 3, 8, 3⟩,
        ⟨2, 4, 5, 1⟩,
        ⟨2, 4, 6, 1⟩,
        ⟨2, 4, 8, 9⟩,
        ⟨2, 5, 6, 7⟩,
        ⟨3, 4, 5, 4⟩,
        ⟨3, 4, 6, 4⟩,
        ⟨3, 6, 7, 3⟩,
        ⟨3, 7, 8, 9⟩,
        ⟨4, 6, 7, 4⟩,
        ⟨5, 6, 7, 5⟩,
        ⟨5, 7, 8, 3⟩]
    }),
    (0xfcf7efbff#36, {
      denominator := 12
      terms := [
        ⟨0, 1, 2, 7⟩,
        ⟨0, 1, 3, 5⟩,
        ⟨0, 2, 3, 5⟩,
        ⟨0, 3, 4, 1⟩,
        ⟨0, 3, 7, 1⟩,
        ⟨0, 4, 6, 6⟩,
        ⟨0, 4, 7, 5⟩,
        ⟨0, 6, 7, 6⟩,
        ⟨1, 2, 3, 5⟩,
        ⟨1, 3, 7, 2⟩,
        ⟨1, 4, 5, 7⟩,
        ⟨1, 4, 7, 5⟩,
        ⟨1, 5, 7, 5⟩,
        ⟨2, 3, 6, 2⟩,
        ⟨2, 4, 5, 4⟩,
        ⟨2, 4, 6, 5⟩,
        ⟨2, 4, 8, 3⟩,
        ⟨2, 5, 6, 2⟩,
        ⟨2, 5, 8, 6⟩,
        ⟨2, 6, 8, 3⟩,
        ⟨3, 4, 6, 1⟩,
        ⟨3, 4, 7, 2⟩,
        ⟨3, 4, 8, 8⟩,
        ⟨3, 5, 6, 8⟩,
        ⟨3, 5, 7, 4⟩,
        ⟨3, 6, 8, 1⟩,
        ⟨3, 7, 8, 3⟩,
        ⟨4, 5, 8, 1⟩,
        ⟨5, 6, 8, 2⟩,
        ⟨5, 7, 8, 3⟩,
        ⟨6, 7, 8, 6⟩]
    })]

theorem checks :
    entries.all (fun entry ↦ entry.2.checkExact (graphOfBits entry.1)) = true := by
  decide

end Erdos76.CertificateChecker.Certificates.ExactN9_10
