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

namespace Erdos76.CertificateChecker.Certificates.ExactN10_57

def entries : List (BitVec (edgeCount 10) × PackingCert 10) := [
    (0x1faf3fbf7fff#45, {
      denominator := 18
      terms := [
        ⟨0, 1, 2, 10⟩,
        ⟨0, 1, 3, 8⟩,
        ⟨0, 2, 3, 7⟩,
        ⟨0, 2, 4, 1⟩,
        ⟨0, 3, 4, 3⟩,
        ⟨0, 4, 5, 3⟩,
        ⟨0, 4, 7, 11⟩,
        ⟨0, 5, 7, 2⟩,
        ⟨0, 5, 8, 13⟩,
        ⟨0, 7, 8, 5⟩,
        ⟨1, 2, 3, 1⟩,
        ⟨1, 2, 4, 7⟩,
        ⟨1, 3, 4, 3⟩,
        ⟨1, 3, 5, 6⟩,
        ⟨1, 4, 8, 4⟩,
        ⟨1, 4, 9, 4⟩,
        ⟨1, 5, 6, 6⟩,
        ⟨1, 5, 8, 4⟩,
        ⟨1, 5, 9, 2⟩,
        ⟨1, 6, 8, 5⟩,
        ⟨1, 6, 9, 7⟩,
        ⟨1, 8, 9, 5⟩,
        ⟨2, 3, 4, 10⟩,
        ⟨2, 5, 6, 9⟩,
        ⟨2, 5, 7, 9⟩,
        ⟨2, 6, 7, 9⟩,
        ⟨3, 4, 7, 2⟩,
        ⟨3, 5, 6, 3⟩,
        ⟨3, 5, 7, 7⟩,
        ⟨3, 5, 9, 2⟩,
        ⟨3, 6, 7, 4⟩,
        ⟨3, 6, 9, 11⟩,
        ⟨3, 7, 9, 5⟩,
        ⟨4, 5, 8, 1⟩,
        ⟨4, 5, 9, 14⟩,
        ⟨4, 6, 7, 5⟩,
        ⟨4, 6, 8, 13⟩,
        ⟨7, 8, 9, 13⟩]
    })]

theorem checks :
    entries.all (fun entry ↦ entry.2.checkExact (graphOfBits entry.1)) = true := by
  decide

end Erdos76.CertificateChecker.Certificates.ExactN10_57
