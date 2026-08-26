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

namespace Erdos76.CertificateChecker.Certificates.ExactN10_21

def entries : List (BitVec (edgeCount 10) × PackingCert 10) := [
    (0x1f1fcfdfffff#45, {
      denominator := 8
      terms := [
        ⟨0, 1, 2, 6⟩,
        ⟨0, 1, 3, 2⟩,
        ⟨0, 2, 3, 2⟩,
        ⟨0, 3, 4, 4⟩,
        ⟨0, 4, 5, 1⟩,
        ⟨0, 4, 6, 3⟩,
        ⟨0, 5, 6, 2⟩,
        ⟨0, 5, 9, 5⟩,
        ⟨0, 6, 9, 3⟩,
        ⟨1, 2, 4, 2⟩,
        ⟨1, 3, 4, 4⟩,
        ⟨1, 3, 5, 2⟩,
        ⟨1, 4, 7, 2⟩,
        ⟨1, 5, 6, 4⟩,
        ⟨1, 5, 7, 2⟩,
        ⟨1, 6, 7, 4⟩,
        ⟨2, 3, 5, 3⟩,
        ⟨2, 3, 6, 1⟩,
        ⟨2, 3, 8, 2⟩,
        ⟨2, 4, 7, 4⟩,
        ⟨2, 4, 8, 2⟩,
        ⟨2, 5, 6, 2⟩,
        ⟨2, 5, 7, 3⟩,
        ⟨2, 6, 7, 1⟩,
        ⟨2, 6, 8, 4⟩,
        ⟨3, 5, 7, 3⟩,
        ⟨3, 6, 7, 3⟩,
        ⟨3, 6, 8, 4⟩,
        ⟨3, 7, 8, 2⟩,
        ⟨4, 5, 8, 6⟩,
        ⟨4, 5, 9, 1⟩,
        ⟨4, 6, 9, 5⟩,
        ⟨4, 7, 9, 2⟩,
        ⟨5, 8, 9, 2⟩,
        ⟨7, 8, 9, 6⟩]
    })]

theorem checks :
    entries.all (fun entry ↦ entry.2.checkExact (graphOfBits entry.1)) = true := by
  decide

end Erdos76.CertificateChecker.Certificates.ExactN10_21
