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
import ErdosProblems.Erdos76.Certificates.ExhaustionN9Levels

namespace Erdos76.CertificateExhaustion.Certificates.ExhaustionN9.Step4.Chunk2

def rows : Array (Array (Option (Transition 9))) := #[
    #[some { child := 18, perm := { images := #[8, 0, 1, 2, 4, 5, 3, 6, 7] } },
        some { child := 21, perm := { images := #[1, 2, 8, 5, 3, 4, 6, 7, 0] } },
        some { child := 21, perm := { images := #[2, 1, 8, 5, 3, 4, 7, 6, 0] } },
        some { child := 21, perm := { images := #[1, 2, 5, 8, 3, 4, 6, 7, 0] } },
        some { child := 21, perm := { images := #[2, 1, 5, 8, 3, 4, 7, 6, 0] } },
        some { child := 24, perm := { images := #[1, 2, 0, 5, 3, 4, 6, 7, 8] } },
        some { child := 19, perm := { images := #[8, 0, 1, 2, 3, 5, 4, 6, 7] } },
        some { child := 19, perm := { images := #[0, 8, 1, 2, 3, 5, 6, 4, 7] } },
        some { child := 22, perm := { images := #[1, 2, 0, 3, 5, 4, 6, 7, 8] } },
        some { child := 22, perm := { images := #[1, 2, 3, 0, 5, 4, 6, 7, 8] } },
        some { child := 19, perm := { images := #[8, 0, 1, 2, 5, 3, 4, 6, 7] } },
        some { child := 19, perm := { images := #[0, 8, 1, 2, 5, 3, 6, 4, 7] } },
        some { child := 22, perm := { images := #[1, 2, 0, 3, 4, 5, 6, 7, 8] } },
        some { child := 22, perm := { images := #[1, 2, 3, 0, 4, 5, 6, 7, 8] } },
        some { child := 23, perm := { images := #[0, 1, 3, 4, 2, 7, 5, 6, 8] } },
        none,
        some { child := 18, perm := { images := #[3, 0, 1, 2, 4, 5, 8, 6, 7] } },
        some { child := 21, perm := { images := #[5, 2, 8, 6, 3, 4, 0, 7, 1] } },
        some { child := 21, perm := { images := #[5, 2, 6, 8, 3, 4, 0, 7, 1] } },
        some { child := 19, perm := { images := #[1, 0, 3, 4, 2, 5, 7, 6, 8] } },
        some { child := 19, perm := { images := #[1, 0, 3, 4, 5, 2, 7, 6, 8] } },
        some { child := 18, perm := { images := #[0, 3, 1, 2, 4, 5, 6, 8, 7] } },
        none,
        some { child := 21, perm := { images := #[2, 5, 8, 6, 3, 4, 7, 0, 1] } },
        some { child := 21, perm := { images := #[2, 5, 6, 8, 3, 4, 7, 0, 1] } },
        some { child := 19, perm := { images := #[0, 1, 3, 4, 2, 5, 6, 7, 8] } },
        some { child := 19, perm := { images := #[0, 1, 3, 4, 5, 2, 6, 7, 8] } },
        some { child := 18, perm := { images := #[3, 6, 1, 2, 4, 5, 8, 0, 7] } },
        some { child := 11, perm := { images := #[0, 1, 2, 3, 4, 5, 6, 7, 8] } },
        some { child := 11, perm := { images := #[1, 0, 2, 3, 4, 5, 7, 6, 8] } },
        none,
        none,
        some { child := 12, perm := { images := #[0, 1, 2, 3, 4, 5, 6, 7, 8] } },
        some { child := 12, perm := { images := #[0, 1, 2, 3, 5, 4, 6, 7, 8] } },
        some { child := 11, perm := { images := #[6, 1, 2, 3, 4, 5, 0, 7, 8] } },
        some { child := 11, perm := { images := #[1, 6, 2, 3, 4, 5, 7, 0, 8] } }],
    #[some { child := 13, perm := { images := #[8, 1, 2, 3, 4, 5, 0, 7, 6] } },
        some { child := 14, perm := { images := #[8, 1, 2, 3, 4, 5, 0, 7, 6] } },
        some { child := 20, perm := { images := #[0, 7, 1, 3, 4, 5, 6, 2, 8] } },
        some { child := 14, perm := { images := #[8, 1, 3, 2, 4, 5, 0, 7, 6] } },
        some { child := 20, perm := { images := #[0, 7, 3, 1, 4, 5, 6, 2, 8] } },
        some { child := 24, perm := { images := #[0, 1, 2, 7, 3, 4, 5, 6, 8] } },
        some { child := 14, perm := { images := #[8, 1, 3, 4, 2, 5, 0, 7, 6] } },
        some { child := 20, perm := { images := #[0, 7, 3, 4, 1, 5, 6, 2, 8] } },
        some { child := 24, perm := { images := #[0, 1, 2, 3, 7, 4, 5, 6, 8] } },
        some { child := 24, perm := { images := #[0, 1, 3, 2, 7, 4, 5, 6, 8] } },
        some { child := 14, perm := { images := #[8, 1, 3, 4, 5, 2, 0, 7, 6] } },
        some { child := 20, perm := { images := #[0, 7, 3, 4, 5, 1, 6, 2, 8] } },
        some { child := 24, perm := { images := #[0, 1, 2, 3, 4, 7, 5, 6, 8] } },
        some { child := 24, perm := { images := #[0, 1, 3, 2, 4, 7, 5, 6, 8] } },
        some { child := 24, perm := { images := #[0, 1, 3, 4, 2, 7, 5, 6, 8] } },
        none,
        some { child := 13, perm := { images := #[0, 1, 2, 3, 4, 5, 8, 7, 6] } },
        some { child := 14, perm := { images := #[0, 1, 2, 3, 4, 5, 8, 7, 6] } },
        some { child := 14, perm := { images := #[0, 1, 3, 2, 4, 5, 8, 7, 6] } },
        some { child := 14, perm := { images := #[0, 1, 3, 4, 2, 5, 8, 7, 6] } },
        some { child := 14, perm := { images := #[0, 1, 3, 4, 5, 2, 8, 7, 6] } },
        some { child := 13, perm := { images := #[8, 7, 2, 3, 4, 5, 0, 1, 6] } },
        none,
        some { child := 20, perm := { images := #[0, 1, 2, 3, 4, 5, 6, 7, 8] } },
        some { child := 20, perm := { images := #[0, 1, 3, 2, 4, 5, 6, 7, 8] } },
        some { child := 20, perm := { images := #[0, 1, 3, 4, 2, 5, 6, 7, 8] } },
        some { child := 20, perm := { images := #[0, 1, 3, 4, 5, 2, 6, 7, 8] } },
        some { child := 13, perm := { images := #[0, 7, 2, 3, 4, 5, 8, 1, 6] } },
        none,
        some { child := 13, perm := { images := #[0, 1, 2, 3, 4, 5, 6, 7, 8] } },
        some { child := 14, perm := { images := #[0, 1, 2, 3, 4, 5, 6, 7, 8] } },
        some { child := 14, perm := { images := #[0, 1, 3, 2, 4, 5, 6, 7, 8] } },
        some { child := 14, perm := { images := #[0, 1, 3, 4, 2, 5, 6, 7, 8] } },
        some { child := 14, perm := { images := #[0, 1, 3, 4, 5, 2, 6, 7, 8] } },
        none,
        some { child := 13, perm := { images := #[0, 7, 2, 3, 4, 5, 6, 1, 8] } }],
    #[some { child := 22, perm := { images := #[8, 0, 1, 2, 4, 3, 5, 6, 7] } },
        some { child := 22, perm := { images := #[8, 1, 0, 2, 4, 3, 6, 5, 7] } },
        some { child := 22, perm := { images := #[1, 8, 0, 2, 4, 6, 3, 5, 7] } },
        some { child := 22, perm := { images := #[8, 1, 2, 0, 4, 3, 6, 7, 5] } },
        some { child := 22, perm := { images := #[1, 8, 2, 0, 4, 6, 3, 7, 5] } },
        some { child := 22, perm := { images := #[1, 2, 8, 0, 4, 6, 7, 3, 5] } },
        some { child := 23, perm := { images := #[8, 0, 1, 2, 3, 4, 5, 6, 7] } },
        some { child := 23, perm := { images := #[0, 8, 1, 2, 3, 5, 4, 6, 7] } },
        some { child := 23, perm := { images := #[0, 1, 8, 2, 3, 5, 6, 4, 7] } },
        some { child := 23, perm := { images := #[0, 1, 2, 8, 3, 5, 6, 7, 4] } },
        none,
        some { child := 22, perm := { images := #[3, 0, 1, 2, 4, 8, 5, 6, 7] } },
        some { child := 22, perm := { images := #[3, 1, 0, 2, 4, 8, 6, 5, 7] } },
        some { child := 22, perm := { images := #[3, 1, 2, 0, 4, 8, 6, 7, 5] } },
        some { child := 23, perm := { images := #[3, 0, 1, 2, 4, 8, 5, 6, 7] } },
        some { child := 22, perm := { images := #[0, 3, 1, 2, 4, 5, 8, 6, 7] } },
        none,
        some { child := 22, perm := { images := #[1, 3, 0, 2, 4, 6, 8, 5, 7] } },
        some { child := 22, perm := { images := #[1, 3, 2, 0, 4, 6, 8, 7, 5] } },
        some { child := 23, perm := { images := #[0, 3, 1, 2, 4, 5, 8, 6, 7] } },
        some { child := 22, perm := { images := #[3, 5, 1, 2, 4, 8, 0, 6, 7] } },
        some { child := 22, perm := { images := #[0, 1, 3, 2, 4, 5, 6, 8, 7] } },
        some { child := 22, perm := { images := #[1, 0, 3, 2, 4, 6, 5, 8, 7] } },
        none,
        some { child := 22, perm := { images := #[1, 2, 3, 0, 4, 6, 7, 8, 5] } },
        some { child := 23, perm := { images := #[0, 1, 3, 2, 4, 5, 6, 8, 7] } },
        some { child := 22, perm := { images := #[3, 1, 5, 2, 4, 8, 6, 0, 7] } },
        some { child := 22, perm := { images := #[1, 3, 5, 2, 4, 6, 8, 0, 7] } },
        some { child := 22, perm := { images := #[0, 1, 2, 3, 4, 5, 6, 7, 8] } },
        some { child := 22, perm := { images := #[1, 0, 2, 3, 4, 6, 5, 7, 8] } },
        some { child := 22, perm := { images := #[1, 2, 0, 3, 4, 6, 7, 5, 8] } },
        none,
        some { child := 23, perm := { images := #[0, 1, 2, 3, 4, 5, 6, 7, 8] } },
        some { child := 22, perm := { images := #[3, 1, 2, 5, 4, 8, 6, 7, 0] } },
        some { child := 22, perm := { images := #[1, 3, 2, 5, 4, 6, 8, 7, 0] } },
        some { child := 22, perm := { images := #[1, 2, 3, 5, 4, 6, 7, 8, 0] } }]]

theorem checks : checkRows Erdos76.CertificateExhaustion.Certificates.ExhaustionN9.level4
    Erdos76.CertificateExhaustion.Certificates.ExhaustionN9.level5 8 rows = true := by
  decide

theorem valid : RowsValidFrom Erdos76.CertificateExhaustion.Certificates.ExhaustionN9.level4
    Erdos76.CertificateExhaustion.Certificates.ExhaustionN9.level5 8 rows :=
  (checkRows_eq_true_iff _ _ _ _).mp checks

end Erdos76.CertificateExhaustion.Certificates.ExhaustionN9.Step4.Chunk2
