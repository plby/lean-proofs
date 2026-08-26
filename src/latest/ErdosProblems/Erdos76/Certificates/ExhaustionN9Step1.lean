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

namespace Erdos76.CertificateExhaustion.Certificates.ExhaustionN9.Step1

def table : Array (Array (Option (Transition 9))) := #[
    #[some { child := 0, perm := { images := #[8, 0, 2, 3, 4, 5, 6, 7, 1] } },
        some { child := 0, perm := { images := #[8, 2, 0, 3, 4, 5, 6, 7, 1] } },
        some { child := 1, perm := { images := #[0, 1, 8, 2, 3, 4, 5, 6, 7] } },
        some { child := 0, perm := { images := #[8, 2, 3, 0, 4, 5, 6, 7, 1] } },
        some { child := 1, perm := { images := #[0, 1, 2, 8, 3, 4, 5, 6, 7] } },
        some { child := 1, perm := { images := #[0, 2, 1, 8, 3, 4, 5, 6, 7] } },
        some { child := 0, perm := { images := #[8, 2, 3, 4, 0, 5, 6, 7, 1] } },
        some { child := 1, perm := { images := #[0, 1, 2, 3, 8, 4, 5, 6, 7] } },
        some { child := 1, perm := { images := #[0, 2, 1, 3, 8, 4, 5, 6, 7] } },
        some { child := 1, perm := { images := #[0, 2, 3, 1, 8, 4, 5, 6, 7] } },
        some { child := 0, perm := { images := #[8, 2, 3, 4, 5, 0, 6, 7, 1] } },
        some { child := 1, perm := { images := #[0, 1, 2, 3, 4, 8, 5, 6, 7] } },
        some { child := 1, perm := { images := #[0, 2, 1, 3, 4, 8, 5, 6, 7] } },
        some { child := 1, perm := { images := #[0, 2, 3, 1, 4, 8, 5, 6, 7] } },
        some { child := 1, perm := { images := #[0, 2, 3, 4, 1, 8, 5, 6, 7] } },
        some { child := 0, perm := { images := #[8, 2, 3, 4, 5, 6, 0, 7, 1] } },
        some { child := 1, perm := { images := #[0, 1, 2, 3, 4, 5, 8, 6, 7] } },
        some { child := 1, perm := { images := #[0, 2, 1, 3, 4, 5, 8, 6, 7] } },
        some { child := 1, perm := { images := #[0, 2, 3, 1, 4, 5, 8, 6, 7] } },
        some { child := 1, perm := { images := #[0, 2, 3, 4, 1, 5, 8, 6, 7] } },
        some { child := 1, perm := { images := #[0, 2, 3, 4, 5, 1, 8, 6, 7] } },
        some { child := 0, perm := { images := #[8, 2, 3, 4, 5, 6, 7, 0, 1] } },
        some { child := 1, perm := { images := #[0, 1, 2, 3, 4, 5, 6, 8, 7] } },
        some { child := 1, perm := { images := #[0, 2, 1, 3, 4, 5, 6, 8, 7] } },
        some { child := 1, perm := { images := #[0, 2, 3, 1, 4, 5, 6, 8, 7] } },
        some { child := 1, perm := { images := #[0, 2, 3, 4, 1, 5, 6, 8, 7] } },
        some { child := 1, perm := { images := #[0, 2, 3, 4, 5, 1, 6, 8, 7] } },
        some { child := 1, perm := { images := #[0, 2, 3, 4, 5, 6, 1, 8, 7] } },
        none,
        some { child := 0, perm := { images := #[0, 1, 2, 3, 4, 5, 6, 7, 8] } },
        some { child := 0, perm := { images := #[0, 2, 1, 3, 4, 5, 6, 7, 8] } },
        some { child := 0, perm := { images := #[0, 2, 3, 1, 4, 5, 6, 7, 8] } },
        some { child := 0, perm := { images := #[0, 2, 3, 4, 1, 5, 6, 7, 8] } },
        some { child := 0, perm := { images := #[0, 2, 3, 4, 5, 1, 6, 7, 8] } },
        some { child := 0, perm := { images := #[0, 2, 3, 4, 5, 6, 1, 7, 8] } },
        some { child := 0, perm := { images := #[0, 2, 3, 4, 5, 6, 7, 1, 8] } }]]

theorem checks : checkStep Erdos76.CertificateExhaustion.Certificates.ExhaustionN9.level1
    Erdos76.CertificateExhaustion.Certificates.ExhaustionN9.level2 table = true := by
  decide

theorem valid : StepValid Erdos76.CertificateExhaustion.Certificates.ExhaustionN9.level1
    Erdos76.CertificateExhaustion.Certificates.ExhaustionN9.level2 table :=
  (checkStep_eq_true_iff _ _ _).mp checks

end Erdos76.CertificateExhaustion.Certificates.ExhaustionN9.Step1
