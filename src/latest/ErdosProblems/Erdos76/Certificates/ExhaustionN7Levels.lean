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
import ErdosProblems.Erdos76.CertificateExhaustion

namespace Erdos76.CertificateExhaustion.Certificates.ExhaustionN7

open CertificateChecker

def level0 : Array (BitVec (edgeCount 7)) := #[0x0#21]

def level1 : Array (BitVec (edgeCount 7)) := #[0x8000#21]

def level2 : Array (BitVec (edgeCount 7)) := #[0x18000#21, 0x10400#21]

def level3 : Array (BitVec (edgeCount 7)) := #[0x38000#21, 0x18400#21, 0x30400#21, 0x108400#21, 0x20840#21]

end Erdos76.CertificateExhaustion.Certificates.ExhaustionN7
