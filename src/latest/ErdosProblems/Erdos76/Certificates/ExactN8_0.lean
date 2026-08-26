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
`n = 8` base of the Gruslys--Letzter almost-complete theorem.  The generator
is untrusted; `checks` is an ordinary kernel reduction via `by decide`. -/

namespace Erdos76.CertificateChecker.Certificates.ExactN8_0

def entries : List (BitVec (edgeCount 8) × PackingCert 8) := [
    (0xe1fffff#28, {
      denominator := 2
      terms := [
        ⟨0, 1, 4, 2⟩,
        ⟨0, 2, 5, 2⟩,
        ⟨0, 3, 6, 2⟩,
        ⟨1, 2, 6, 2⟩,
        ⟨1, 3, 5, 2⟩,
        ⟨2, 3, 4, 2⟩,
        ⟨4, 5, 6, 1⟩,
        ⟨4, 5, 7, 1⟩,
        ⟨4, 6, 7, 1⟩,
        ⟨5, 6, 7, 1⟩]
    }),
    (0xf1f7fff#28, {
      denominator := 2
      terms := [
        ⟨0, 1, 2, 1⟩,
        ⟨0, 1, 3, 1⟩,
        ⟨0, 2, 4, 1⟩,
        ⟨0, 3, 5, 1⟩,
        ⟨0, 4, 5, 1⟩,
        ⟨1, 2, 5, 1⟩,
        ⟨1, 3, 5, 1⟩,
        ⟨1, 4, 6, 2⟩,
        ⟨2, 3, 6, 2⟩,
        ⟨2, 4, 5, 1⟩,
        ⟨3, 4, 7, 2⟩,
        ⟨5, 6, 7, 2⟩]
    }),
    (0xe3f7fff#28, {
      denominator := 2
      terms := [
        ⟨0, 1, 3, 1⟩,
        ⟨0, 1, 4, 1⟩,
        ⟨0, 2, 3, 1⟩,
        ⟨0, 2, 4, 1⟩,
        ⟨0, 5, 7, 2⟩,
        ⟨1, 2, 4, 1⟩,
        ⟨1, 2, 5, 1⟩,
        ⟨1, 3, 6, 1⟩,
        ⟨1, 5, 6, 1⟩,
        ⟨2, 3, 6, 1⟩,
        ⟨2, 5, 6, 1⟩,
        ⟨3, 4, 5, 2⟩,
        ⟨4, 6, 7, 2⟩]
    }),
    (0x79f7fff#28, {
      denominator := 2
      terms := [
        ⟨0, 1, 2, 1⟩,
        ⟨0, 1, 3, 1⟩,
        ⟨0, 2, 4, 1⟩,
        ⟨0, 3, 5, 1⟩,
        ⟨0, 4, 5, 1⟩,
        ⟨1, 2, 4, 1⟩,
        ⟨1, 3, 5, 1⟩,
        ⟨1, 4, 6, 1⟩,
        ⟨1, 5, 6, 1⟩,
        ⟨2, 3, 6, 1⟩,
        ⟨2, 3, 7, 1⟩,
        ⟨2, 5, 6, 1⟩,
        ⟨2, 5, 7, 1⟩,
        ⟨3, 4, 6, 1⟩,
        ⟨3, 4, 7, 1⟩,
        ⟨4, 5, 7, 1⟩]
    }),
    (0xf9e7fff#28, {
      denominator := 2
      terms := [
        ⟨0, 1, 2, 1⟩,
        ⟨0, 1, 3, 1⟩,
        ⟨0, 2, 5, 1⟩,
        ⟨0, 3, 4, 1⟩,
        ⟨0, 4, 5, 1⟩,
        ⟨1, 2, 4, 1⟩,
        ⟨1, 3, 5, 1⟩,
        ⟨1, 4, 5, 1⟩,
        ⟨2, 3, 6, 1⟩,
        ⟨2, 3, 7, 1⟩,
        ⟨2, 4, 7, 1⟩,
        ⟨2, 5, 6, 1⟩,
        ⟨3, 4, 6, 1⟩,
        ⟨3, 5, 7, 1⟩,
        ⟨4, 6, 7, 1⟩,
        ⟨5, 6, 7, 1⟩]
    })]

theorem checks :
    entries.all (fun entry ↦ entry.2.checkExact (graphOfBits entry.1)) = true := by
  decide

end Erdos76.CertificateChecker.Certificates.ExactN8_0
