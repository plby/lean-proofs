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
import ErdosProblems.Erdos76.Certificates.ExhaustionN8Levels

namespace Erdos76.CertificateExhaustion.Certificates.ExhaustionN8.Step0

def table : Array (Array (Option (Transition 8))) := #[
    #[some { child := 0, perm := { images := #[0, 7, 1, 2, 3, 4, 5, 6] } },
        some { child := 0, perm := { images := #[0, 1, 7, 2, 3, 4, 5, 6] } },
        some { child := 0, perm := { images := #[1, 0, 7, 2, 3, 4, 5, 6] } },
        some { child := 0, perm := { images := #[0, 1, 2, 7, 3, 4, 5, 6] } },
        some { child := 0, perm := { images := #[1, 0, 2, 7, 3, 4, 5, 6] } },
        some { child := 0, perm := { images := #[1, 2, 0, 7, 3, 4, 5, 6] } },
        some { child := 0, perm := { images := #[0, 1, 2, 3, 7, 4, 5, 6] } },
        some { child := 0, perm := { images := #[1, 0, 2, 3, 7, 4, 5, 6] } },
        some { child := 0, perm := { images := #[1, 2, 0, 3, 7, 4, 5, 6] } },
        some { child := 0, perm := { images := #[1, 2, 3, 0, 7, 4, 5, 6] } },
        some { child := 0, perm := { images := #[0, 1, 2, 3, 4, 7, 5, 6] } },
        some { child := 0, perm := { images := #[1, 0, 2, 3, 4, 7, 5, 6] } },
        some { child := 0, perm := { images := #[1, 2, 0, 3, 4, 7, 5, 6] } },
        some { child := 0, perm := { images := #[1, 2, 3, 0, 4, 7, 5, 6] } },
        some { child := 0, perm := { images := #[1, 2, 3, 4, 0, 7, 5, 6] } },
        some { child := 0, perm := { images := #[0, 1, 2, 3, 4, 5, 7, 6] } },
        some { child := 0, perm := { images := #[1, 0, 2, 3, 4, 5, 7, 6] } },
        some { child := 0, perm := { images := #[1, 2, 0, 3, 4, 5, 7, 6] } },
        some { child := 0, perm := { images := #[1, 2, 3, 0, 4, 5, 7, 6] } },
        some { child := 0, perm := { images := #[1, 2, 3, 4, 0, 5, 7, 6] } },
        some { child := 0, perm := { images := #[1, 2, 3, 4, 5, 0, 7, 6] } },
        some { child := 0, perm := { images := #[0, 1, 2, 3, 4, 5, 6, 7] } },
        some { child := 0, perm := { images := #[1, 0, 2, 3, 4, 5, 6, 7] } },
        some { child := 0, perm := { images := #[1, 2, 0, 3, 4, 5, 6, 7] } },
        some { child := 0, perm := { images := #[1, 2, 3, 0, 4, 5, 6, 7] } },
        some { child := 0, perm := { images := #[1, 2, 3, 4, 0, 5, 6, 7] } },
        some { child := 0, perm := { images := #[1, 2, 3, 4, 5, 0, 6, 7] } },
        some { child := 0, perm := { images := #[1, 2, 3, 4, 5, 6, 0, 7] } }]]

theorem checks : checkStep Erdos76.CertificateExhaustion.Certificates.ExhaustionN8.level0
    Erdos76.CertificateExhaustion.Certificates.ExhaustionN8.level1 table = true := by
  decide

end Erdos76.CertificateExhaustion.Certificates.ExhaustionN8.Step0
