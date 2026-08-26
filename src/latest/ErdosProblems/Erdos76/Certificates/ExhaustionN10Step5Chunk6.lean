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

namespace Erdos76.CertificateExhaustion.Certificates.ExhaustionN10.Step5.Chunk6

def rows : Array (Array (Option (Transition 10))) := #[
    #[some { child := 50, perm := { images := #[9, 1, 2, 3, 4, 5, 0, 7, 8, 6] } },
        some { child := 50, perm := { images := #[9, 2, 1, 3, 4, 5, 0, 8, 7, 6] } },
        some { child := 55, perm := { images := #[1, 8, 0, 3, 4, 5, 7, 2, 6, 9] } },
        some { child := 51, perm := { images := #[9, 1, 2, 3, 4, 5, 0, 7, 8, 6] } },
        some { child := 61, perm := { images := #[0, 8, 1, 2, 4, 5, 6, 3, 7, 9] } },
        some { child := 61, perm := { images := #[0, 1, 8, 2, 4, 5, 6, 7, 3, 9] } },
        some { child := 51, perm := { images := #[9, 1, 2, 4, 3, 5, 0, 7, 8, 6] } },
        some { child := 61, perm := { images := #[0, 8, 1, 4, 2, 5, 6, 3, 7, 9] } },
        some { child := 61, perm := { images := #[0, 1, 8, 4, 2, 5, 6, 7, 3, 9] } },
        some { child := 65, perm := { images := #[0, 1, 2, 3, 8, 4, 5, 6, 7, 9] } },
        some { child := 51, perm := { images := #[9, 1, 2, 4, 5, 3, 0, 7, 8, 6] } },
        some { child := 61, perm := { images := #[0, 8, 1, 4, 5, 2, 6, 3, 7, 9] } },
        some { child := 61, perm := { images := #[0, 1, 8, 4, 5, 2, 6, 7, 3, 9] } },
        some { child := 65, perm := { images := #[0, 1, 2, 3, 4, 8, 5, 6, 7, 9] } },
        some { child := 65, perm := { images := #[0, 1, 2, 4, 3, 8, 5, 6, 7, 9] } },
        none,
        some { child := 50, perm := { images := #[0, 1, 2, 3, 4, 5, 9, 7, 8, 6] } },
        some { child := 50, perm := { images := #[0, 2, 1, 3, 4, 5, 9, 8, 7, 6] } },
        some { child := 51, perm := { images := #[0, 1, 2, 3, 4, 5, 9, 7, 8, 6] } },
        some { child := 51, perm := { images := #[0, 1, 2, 4, 3, 5, 9, 7, 8, 6] } },
        some { child := 51, perm := { images := #[0, 1, 2, 4, 5, 3, 9, 7, 8, 6] } },
        some { child := 50, perm := { images := #[9, 7, 2, 3, 4, 5, 0, 1, 8, 6] } },
        none,
        some { child := 55, perm := { images := #[1, 2, 0, 3, 4, 5, 7, 8, 6, 9] } },
        some { child := 61, perm := { images := #[0, 2, 1, 3, 4, 5, 6, 8, 7, 9] } },
        some { child := 61, perm := { images := #[0, 2, 1, 4, 3, 5, 6, 8, 7, 9] } },
        some { child := 61, perm := { images := #[0, 2, 1, 4, 5, 3, 6, 8, 7, 9] } },
        some { child := 50, perm := { images := #[0, 7, 2, 3, 4, 5, 9, 1, 8, 6] } },
        some { child := 50, perm := { images := #[9, 2, 7, 3, 4, 5, 0, 8, 1, 6] } },
        some { child := 55, perm := { images := #[1, 0, 2, 3, 4, 5, 7, 6, 8, 9] } },
        none,
        some { child := 61, perm := { images := #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9] } },
        some { child := 61, perm := { images := #[0, 1, 2, 4, 3, 5, 6, 7, 8, 9] } },
        some { child := 61, perm := { images := #[0, 1, 2, 4, 5, 3, 6, 7, 8, 9] } },
        some { child := 50, perm := { images := #[0, 2, 7, 3, 4, 5, 9, 8, 1, 6] } },
        some { child := 55, perm := { images := #[1, 2, 6, 3, 4, 5, 7, 8, 0, 9] } },
        none,
        some { child := 50, perm := { images := #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9] } },
        some { child := 50, perm := { images := #[0, 2, 1, 3, 4, 5, 6, 8, 7, 9] } },
        some { child := 51, perm := { images := #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9] } },
        some { child := 51, perm := { images := #[0, 1, 2, 4, 3, 5, 6, 7, 8, 9] } },
        some { child := 51, perm := { images := #[0, 1, 2, 4, 5, 3, 6, 7, 8, 9] } },
        none,
        some { child := 50, perm := { images := #[0, 7, 2, 3, 4, 5, 6, 1, 8, 9] } },
        some { child := 50, perm := { images := #[0, 2, 7, 3, 4, 5, 6, 8, 1, 9] } }],
    #[some { child := 64, perm := { images := #[9, 0, 1, 2, 3, 4, 5, 6, 7, 8] } },
        some { child := 64, perm := { images := #[9, 1, 0, 2, 3, 4, 6, 5, 7, 8] } },
        some { child := 64, perm := { images := #[1, 9, 0, 2, 3, 6, 4, 5, 7, 8] } },
        some { child := 64, perm := { images := #[9, 1, 2, 0, 3, 4, 6, 7, 5, 8] } },
        some { child := 64, perm := { images := #[1, 9, 2, 0, 3, 6, 4, 7, 5, 8] } },
        some { child := 64, perm := { images := #[1, 2, 9, 0, 3, 6, 7, 4, 5, 8] } },
        some { child := 64, perm := { images := #[9, 1, 2, 3, 0, 4, 6, 7, 8, 5] } },
        some { child := 64, perm := { images := #[1, 9, 2, 3, 0, 6, 4, 7, 8, 5] } },
        some { child := 64, perm := { images := #[1, 2, 9, 3, 0, 6, 7, 4, 8, 5] } },
        some { child := 64, perm := { images := #[1, 2, 3, 9, 0, 6, 7, 8, 4, 5] } },
        none,
        some { child := 64, perm := { images := #[4, 0, 1, 2, 3, 9, 5, 6, 7, 8] } },
        some { child := 64, perm := { images := #[4, 1, 0, 2, 3, 9, 6, 5, 7, 8] } },
        some { child := 64, perm := { images := #[4, 1, 2, 0, 3, 9, 6, 7, 5, 8] } },
        some { child := 64, perm := { images := #[4, 1, 2, 3, 0, 9, 6, 7, 8, 5] } },
        some { child := 64, perm := { images := #[0, 4, 1, 2, 3, 5, 9, 6, 7, 8] } },
        none,
        some { child := 64, perm := { images := #[1, 4, 0, 2, 3, 6, 9, 5, 7, 8] } },
        some { child := 64, perm := { images := #[1, 4, 2, 0, 3, 6, 9, 7, 5, 8] } },
        some { child := 64, perm := { images := #[1, 4, 2, 3, 0, 6, 9, 7, 8, 5] } },
        some { child := 64, perm := { images := #[4, 5, 1, 2, 3, 9, 0, 6, 7, 8] } },
        some { child := 64, perm := { images := #[0, 1, 4, 2, 3, 5, 6, 9, 7, 8] } },
        some { child := 64, perm := { images := #[1, 0, 4, 2, 3, 6, 5, 9, 7, 8] } },
        none,
        some { child := 64, perm := { images := #[1, 2, 4, 0, 3, 6, 7, 9, 5, 8] } },
        some { child := 64, perm := { images := #[1, 2, 4, 3, 0, 6, 7, 9, 8, 5] } },
        some { child := 64, perm := { images := #[4, 1, 5, 2, 3, 9, 6, 0, 7, 8] } },
        some { child := 64, perm := { images := #[1, 4, 5, 2, 3, 6, 9, 0, 7, 8] } },
        some { child := 64, perm := { images := #[0, 1, 2, 4, 3, 5, 6, 7, 9, 8] } },
        some { child := 64, perm := { images := #[1, 0, 2, 4, 3, 6, 5, 7, 9, 8] } },
        some { child := 64, perm := { images := #[1, 2, 0, 4, 3, 6, 7, 5, 9, 8] } },
        none,
        some { child := 64, perm := { images := #[1, 2, 3, 4, 0, 6, 7, 8, 9, 5] } },
        some { child := 64, perm := { images := #[4, 1, 2, 5, 3, 9, 6, 7, 0, 8] } },
        some { child := 64, perm := { images := #[1, 4, 2, 5, 3, 6, 9, 7, 0, 8] } },
        some { child := 64, perm := { images := #[1, 2, 4, 5, 3, 6, 7, 9, 0, 8] } },
        some { child := 64, perm := { images := #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9] } },
        some { child := 64, perm := { images := #[1, 0, 2, 3, 4, 6, 5, 7, 8, 9] } },
        some { child := 64, perm := { images := #[1, 2, 0, 3, 4, 6, 7, 5, 8, 9] } },
        some { child := 64, perm := { images := #[1, 2, 3, 0, 4, 6, 7, 8, 5, 9] } },
        none,
        some { child := 64, perm := { images := #[4, 1, 2, 3, 5, 9, 6, 7, 8, 0] } },
        some { child := 64, perm := { images := #[1, 4, 2, 3, 5, 6, 9, 7, 8, 0] } },
        some { child := 64, perm := { images := #[1, 2, 4, 3, 5, 6, 7, 9, 8, 0] } },
        some { child := 64, perm := { images := #[1, 2, 3, 4, 5, 6, 7, 8, 9, 0] } }]]

theorem checks : checkRows Erdos76.CertificateExhaustion.Certificates.ExhaustionN10.level5
    Erdos76.CertificateExhaustion.Certificates.ExhaustionN10.level6 24 rows = true := by
  decide

theorem valid : RowsValidFrom Erdos76.CertificateExhaustion.Certificates.ExhaustionN10.level5
    Erdos76.CertificateExhaustion.Certificates.ExhaustionN10.level6 24 rows :=
  (checkRows_eq_true_iff _ _ _ _).mp checks

end Erdos76.CertificateExhaustion.Certificates.ExhaustionN10.Step5.Chunk6
