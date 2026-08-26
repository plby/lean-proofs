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
import ErdosProblems.Erdos76.Certificates.ExhaustionN10Levels

namespace Erdos76.CertificateExhaustion.Certificates.ExhaustionN10.Step3.Chunk1

def rows : Array (Array (Option (Transition 10))) := #[
    #[some { child := 7, perm := { images := #[9, 0, 1, 3, 4, 5, 6, 2, 7, 8] } },
        some { child := 7, perm := { images := #[9, 1, 0, 3, 4, 5, 6, 2, 8, 7] } },
        some { child := 7, perm := { images := #[1, 9, 0, 3, 4, 5, 6, 8, 2, 7] } },
        some { child := 8, perm := { images := #[9, 0, 1, 2, 4, 5, 6, 3, 7, 8] } },
        some { child := 8, perm := { images := #[0, 9, 1, 2, 4, 5, 6, 7, 3, 8] } },
        some { child := 8, perm := { images := #[0, 1, 9, 2, 4, 5, 6, 7, 8, 3] } },
        some { child := 8, perm := { images := #[9, 0, 1, 4, 2, 5, 6, 3, 7, 8] } },
        some { child := 8, perm := { images := #[0, 9, 1, 4, 2, 5, 6, 7, 3, 8] } },
        some { child := 8, perm := { images := #[0, 1, 9, 4, 2, 5, 6, 7, 8, 3] } },
        some { child := 10, perm := { images := #[0, 1, 2, 3, 9, 4, 5, 6, 7, 8] } },
        some { child := 8, perm := { images := #[9, 0, 1, 4, 5, 2, 6, 3, 7, 8] } },
        some { child := 8, perm := { images := #[0, 9, 1, 4, 5, 2, 6, 7, 3, 8] } },
        some { child := 8, perm := { images := #[0, 1, 9, 4, 5, 2, 6, 7, 8, 3] } },
        some { child := 10, perm := { images := #[0, 1, 2, 3, 4, 9, 5, 6, 7, 8] } },
        some { child := 10, perm := { images := #[0, 1, 2, 4, 3, 9, 5, 6, 7, 8] } },
        some { child := 8, perm := { images := #[9, 0, 1, 4, 5, 6, 2, 3, 7, 8] } },
        some { child := 8, perm := { images := #[0, 9, 1, 4, 5, 6, 2, 7, 3, 8] } },
        some { child := 8, perm := { images := #[0, 1, 9, 4, 5, 6, 2, 7, 8, 3] } },
        some { child := 10, perm := { images := #[0, 1, 2, 3, 4, 5, 9, 6, 7, 8] } },
        some { child := 10, perm := { images := #[0, 1, 2, 4, 3, 5, 9, 6, 7, 8] } },
        some { child := 10, perm := { images := #[0, 1, 2, 4, 5, 3, 9, 6, 7, 8] } },
        none,
        some { child := 7, perm := { images := #[2, 0, 1, 3, 4, 5, 6, 9, 7, 8] } },
        some { child := 7, perm := { images := #[2, 1, 0, 3, 4, 5, 6, 9, 8, 7] } },
        some { child := 8, perm := { images := #[2, 0, 1, 3, 4, 5, 6, 9, 7, 8] } },
        some { child := 8, perm := { images := #[2, 0, 1, 4, 3, 5, 6, 9, 7, 8] } },
        some { child := 8, perm := { images := #[2, 0, 1, 4, 5, 3, 6, 9, 7, 8] } },
        some { child := 8, perm := { images := #[2, 0, 1, 4, 5, 6, 3, 9, 7, 8] } },
        some { child := 7, perm := { images := #[0, 2, 1, 3, 4, 5, 6, 7, 9, 8] } },
        none,
        some { child := 7, perm := { images := #[1, 2, 0, 3, 4, 5, 6, 8, 9, 7] } },
        some { child := 8, perm := { images := #[0, 2, 1, 3, 4, 5, 6, 7, 9, 8] } },
        some { child := 8, perm := { images := #[0, 2, 1, 4, 3, 5, 6, 7, 9, 8] } },
        some { child := 8, perm := { images := #[0, 2, 1, 4, 5, 3, 6, 7, 9, 8] } },
        some { child := 8, perm := { images := #[0, 2, 1, 4, 5, 6, 3, 7, 9, 8] } },
        some { child := 7, perm := { images := #[2, 7, 1, 3, 4, 5, 6, 9, 0, 8] } },
        some { child := 7, perm := { images := #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9] } },
        some { child := 7, perm := { images := #[1, 0, 2, 3, 4, 5, 6, 8, 7, 9] } },
        none,
        some { child := 8, perm := { images := #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9] } },
        some { child := 8, perm := { images := #[0, 1, 2, 4, 3, 5, 6, 7, 8, 9] } },
        some { child := 8, perm := { images := #[0, 1, 2, 4, 5, 3, 6, 7, 8, 9] } },
        some { child := 8, perm := { images := #[0, 1, 2, 4, 5, 6, 3, 7, 8, 9] } },
        some { child := 7, perm := { images := #[2, 1, 7, 3, 4, 5, 6, 9, 8, 0] } },
        some { child := 7, perm := { images := #[1, 2, 7, 3, 4, 5, 6, 8, 9, 0] } }]]

theorem checks : checkRows Erdos76.CertificateExhaustion.Certificates.ExhaustionN10.level3
    Erdos76.CertificateExhaustion.Certificates.ExhaustionN10.level4 4 rows = true := by
  decide

theorem valid : RowsValidFrom Erdos76.CertificateExhaustion.Certificates.ExhaustionN10.level3
    Erdos76.CertificateExhaustion.Certificates.ExhaustionN10.level4 4 rows :=
  (checkRows_eq_true_iff _ _ _ _).mp checks

end Erdos76.CertificateExhaustion.Certificates.ExhaustionN10.Step3.Chunk1
