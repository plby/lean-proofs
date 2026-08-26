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

namespace Erdos76.CertificateExhaustion.Certificates.ExhaustionN9.Step2

def table : Array (Array (Option (Transition 9))) := #[
    #[some { child := 3, perm := { images := #[0, 7, 1, 2, 3, 4, 5, 6, 8] } },
        some { child := 1, perm := { images := #[0, 1, 7, 2, 3, 4, 5, 6, 8] } },
        some { child := 1, perm := { images := #[1, 0, 7, 2, 3, 4, 5, 6, 8] } },
        some { child := 1, perm := { images := #[0, 1, 2, 7, 3, 4, 5, 6, 8] } },
        some { child := 1, perm := { images := #[1, 0, 2, 7, 3, 4, 5, 6, 8] } },
        some { child := 2, perm := { images := #[1, 2, 0, 7, 3, 4, 5, 6, 8] } },
        some { child := 1, perm := { images := #[0, 1, 2, 3, 7, 4, 5, 6, 8] } },
        some { child := 1, perm := { images := #[1, 0, 2, 3, 7, 4, 5, 6, 8] } },
        some { child := 2, perm := { images := #[1, 2, 0, 3, 7, 4, 5, 6, 8] } },
        some { child := 2, perm := { images := #[1, 2, 3, 0, 7, 4, 5, 6, 8] } },
        some { child := 1, perm := { images := #[0, 1, 2, 3, 4, 7, 5, 6, 8] } },
        some { child := 1, perm := { images := #[1, 0, 2, 3, 4, 7, 5, 6, 8] } },
        some { child := 2, perm := { images := #[1, 2, 0, 3, 4, 7, 5, 6, 8] } },
        some { child := 2, perm := { images := #[1, 2, 3, 0, 4, 7, 5, 6, 8] } },
        some { child := 2, perm := { images := #[1, 2, 3, 4, 0, 7, 5, 6, 8] } },
        some { child := 1, perm := { images := #[0, 1, 2, 3, 4, 5, 7, 6, 8] } },
        some { child := 1, perm := { images := #[1, 0, 2, 3, 4, 5, 7, 6, 8] } },
        some { child := 2, perm := { images := #[1, 2, 0, 3, 4, 5, 7, 6, 8] } },
        some { child := 2, perm := { images := #[1, 2, 3, 0, 4, 5, 7, 6, 8] } },
        some { child := 2, perm := { images := #[1, 2, 3, 4, 0, 5, 7, 6, 8] } },
        some { child := 2, perm := { images := #[1, 2, 3, 4, 5, 0, 7, 6, 8] } },
        some { child := 1, perm := { images := #[0, 1, 2, 3, 4, 5, 6, 7, 8] } },
        some { child := 1, perm := { images := #[1, 0, 2, 3, 4, 5, 6, 7, 8] } },
        some { child := 2, perm := { images := #[1, 2, 0, 3, 4, 5, 6, 7, 8] } },
        some { child := 2, perm := { images := #[1, 2, 3, 0, 4, 5, 6, 7, 8] } },
        some { child := 2, perm := { images := #[1, 2, 3, 4, 0, 5, 6, 7, 8] } },
        some { child := 2, perm := { images := #[1, 2, 3, 4, 5, 0, 6, 7, 8] } },
        some { child := 2, perm := { images := #[1, 2, 3, 4, 5, 6, 0, 7, 8] } },
        none,
        none,
        some { child := 0, perm := { images := #[0, 1, 2, 3, 4, 5, 6, 7, 8] } },
        some { child := 0, perm := { images := #[0, 1, 3, 2, 4, 5, 6, 7, 8] } },
        some { child := 0, perm := { images := #[0, 1, 3, 4, 2, 5, 6, 7, 8] } },
        some { child := 0, perm := { images := #[0, 1, 3, 4, 5, 2, 6, 7, 8] } },
        some { child := 0, perm := { images := #[0, 1, 3, 4, 5, 6, 2, 7, 8] } },
        some { child := 0, perm := { images := #[0, 1, 3, 4, 5, 6, 7, 2, 8] } }],
    #[some { child := 1, perm := { images := #[8, 0, 2, 3, 4, 5, 6, 1, 7] } },
        some { child := 2, perm := { images := #[8, 0, 1, 3, 4, 5, 6, 2, 7] } },
        some { child := 2, perm := { images := #[0, 8, 1, 3, 4, 5, 6, 7, 2] } },
        some { child := 2, perm := { images := #[8, 0, 3, 1, 4, 5, 6, 2, 7] } },
        some { child := 2, perm := { images := #[0, 8, 3, 1, 4, 5, 6, 7, 2] } },
        some { child := 4, perm := { images := #[0, 1, 2, 8, 3, 4, 5, 6, 7] } },
        some { child := 2, perm := { images := #[8, 0, 3, 4, 1, 5, 6, 2, 7] } },
        some { child := 2, perm := { images := #[0, 8, 3, 4, 1, 5, 6, 7, 2] } },
        some { child := 4, perm := { images := #[0, 1, 2, 3, 8, 4, 5, 6, 7] } },
        some { child := 4, perm := { images := #[0, 1, 3, 2, 8, 4, 5, 6, 7] } },
        some { child := 2, perm := { images := #[8, 0, 3, 4, 5, 1, 6, 2, 7] } },
        some { child := 2, perm := { images := #[0, 8, 3, 4, 5, 1, 6, 7, 2] } },
        some { child := 4, perm := { images := #[0, 1, 2, 3, 4, 8, 5, 6, 7] } },
        some { child := 4, perm := { images := #[0, 1, 3, 2, 4, 8, 5, 6, 7] } },
        some { child := 4, perm := { images := #[0, 1, 3, 4, 2, 8, 5, 6, 7] } },
        some { child := 2, perm := { images := #[8, 0, 3, 4, 5, 6, 1, 2, 7] } },
        some { child := 2, perm := { images := #[0, 8, 3, 4, 5, 6, 1, 7, 2] } },
        some { child := 4, perm := { images := #[0, 1, 2, 3, 4, 5, 8, 6, 7] } },
        some { child := 4, perm := { images := #[0, 1, 3, 2, 4, 5, 8, 6, 7] } },
        some { child := 4, perm := { images := #[0, 1, 3, 4, 2, 5, 8, 6, 7] } },
        some { child := 4, perm := { images := #[0, 1, 3, 4, 5, 2, 8, 6, 7] } },
        none,
        some { child := 1, perm := { images := #[1, 0, 2, 3, 4, 5, 6, 8, 7] } },
        some { child := 2, perm := { images := #[1, 0, 2, 3, 4, 5, 6, 8, 7] } },
        some { child := 2, perm := { images := #[1, 0, 3, 2, 4, 5, 6, 8, 7] } },
        some { child := 2, perm := { images := #[1, 0, 3, 4, 2, 5, 6, 8, 7] } },
        some { child := 2, perm := { images := #[1, 0, 3, 4, 5, 2, 6, 8, 7] } },
        some { child := 2, perm := { images := #[1, 0, 3, 4, 5, 6, 2, 8, 7] } },
        some { child := 1, perm := { images := #[0, 1, 2, 3, 4, 5, 6, 7, 8] } },
        none,
        some { child := 2, perm := { images := #[0, 1, 2, 3, 4, 5, 6, 7, 8] } },
        some { child := 2, perm := { images := #[0, 1, 3, 2, 4, 5, 6, 7, 8] } },
        some { child := 2, perm := { images := #[0, 1, 3, 4, 2, 5, 6, 7, 8] } },
        some { child := 2, perm := { images := #[0, 1, 3, 4, 5, 2, 6, 7, 8] } },
        some { child := 2, perm := { images := #[0, 1, 3, 4, 5, 6, 2, 7, 8] } },
        some { child := 1, perm := { images := #[1, 7, 2, 3, 4, 5, 6, 8, 0] } }]]

theorem checks : checkStep Erdos76.CertificateExhaustion.Certificates.ExhaustionN9.level2
    Erdos76.CertificateExhaustion.Certificates.ExhaustionN9.level3 table = true := by
  decide

theorem valid : StepValid Erdos76.CertificateExhaustion.Certificates.ExhaustionN9.level2
    Erdos76.CertificateExhaustion.Certificates.ExhaustionN9.level3 table :=
  (checkStep_eq_true_iff _ _ _).mp checks

end Erdos76.CertificateExhaustion.Certificates.ExhaustionN9.Step2
