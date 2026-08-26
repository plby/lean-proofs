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
import ErdosProblems.Erdos76.Certificates.ExhaustionN7Levels

namespace Erdos76.CertificateExhaustion.Certificates.ExhaustionN7.Step2

def table : Array (Array (Option (Transition 7))) := #[
    #[some { child := 3, perm := { images := #[0, 5, 1, 2, 3, 4, 6] } },
        some { child := 1, perm := { images := #[0, 1, 5, 2, 3, 4, 6] } },
        some { child := 1, perm := { images := #[1, 0, 5, 2, 3, 4, 6] } },
        some { child := 1, perm := { images := #[0, 1, 2, 5, 3, 4, 6] } },
        some { child := 1, perm := { images := #[1, 0, 2, 5, 3, 4, 6] } },
        some { child := 2, perm := { images := #[1, 2, 0, 5, 3, 4, 6] } },
        some { child := 1, perm := { images := #[0, 1, 2, 3, 5, 4, 6] } },
        some { child := 1, perm := { images := #[1, 0, 2, 3, 5, 4, 6] } },
        some { child := 2, perm := { images := #[1, 2, 0, 3, 5, 4, 6] } },
        some { child := 2, perm := { images := #[1, 2, 3, 0, 5, 4, 6] } },
        some { child := 1, perm := { images := #[0, 1, 2, 3, 4, 5, 6] } },
        some { child := 1, perm := { images := #[1, 0, 2, 3, 4, 5, 6] } },
        some { child := 2, perm := { images := #[1, 2, 0, 3, 4, 5, 6] } },
        some { child := 2, perm := { images := #[1, 2, 3, 0, 4, 5, 6] } },
        some { child := 2, perm := { images := #[1, 2, 3, 4, 0, 5, 6] } },
        none,
        none,
        some { child := 0, perm := { images := #[0, 1, 2, 3, 4, 5, 6] } },
        some { child := 0, perm := { images := #[0, 1, 3, 2, 4, 5, 6] } },
        some { child := 0, perm := { images := #[0, 1, 3, 4, 2, 5, 6] } },
        some { child := 0, perm := { images := #[0, 1, 3, 4, 5, 2, 6] } }],
    #[some { child := 1, perm := { images := #[0, 6, 2, 3, 4, 5, 1] } },
        some { child := 2, perm := { images := #[6, 0, 1, 3, 4, 2, 5] } },
        some { child := 2, perm := { images := #[0, 6, 1, 3, 4, 5, 2] } },
        some { child := 2, perm := { images := #[6, 0, 3, 1, 4, 2, 5] } },
        some { child := 2, perm := { images := #[0, 6, 3, 1, 4, 5, 2] } },
        some { child := 4, perm := { images := #[0, 1, 2, 6, 3, 4, 5] } },
        some { child := 2, perm := { images := #[6, 0, 3, 4, 1, 2, 5] } },
        some { child := 2, perm := { images := #[0, 6, 3, 4, 1, 5, 2] } },
        some { child := 4, perm := { images := #[0, 1, 2, 3, 6, 4, 5] } },
        some { child := 4, perm := { images := #[0, 1, 3, 2, 6, 4, 5] } },
        none,
        some { child := 1, perm := { images := #[1, 0, 2, 3, 4, 6, 5] } },
        some { child := 2, perm := { images := #[1, 0, 2, 3, 4, 6, 5] } },
        some { child := 2, perm := { images := #[1, 0, 3, 2, 4, 6, 5] } },
        some { child := 2, perm := { images := #[1, 0, 3, 4, 2, 6, 5] } },
        some { child := 1, perm := { images := #[0, 1, 2, 3, 4, 5, 6] } },
        none,
        some { child := 2, perm := { images := #[0, 1, 2, 3, 4, 5, 6] } },
        some { child := 2, perm := { images := #[0, 1, 3, 2, 4, 5, 6] } },
        some { child := 2, perm := { images := #[0, 1, 3, 4, 2, 5, 6] } },
        some { child := 1, perm := { images := #[5, 1, 2, 3, 4, 0, 6] } }]]

theorem checks : checkStep Erdos76.CertificateExhaustion.Certificates.ExhaustionN7.level2
    Erdos76.CertificateExhaustion.Certificates.ExhaustionN7.level3 table = true := by
  decide

end Erdos76.CertificateExhaustion.Certificates.ExhaustionN7.Step2
