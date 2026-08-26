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

namespace Erdos76.CertificateExhaustion.Certificates.ExhaustionN8

open CertificateChecker

def level0 : Array (BitVec (edgeCount 8)) := #[0x0#28]

def level1 : Array (BitVec (edgeCount 8)) := #[0x200000#28]

def level2 : Array (BitVec (edgeCount 8)) := #[0x600000#28, 0x408000#28]

def level3 : Array (BitVec (edgeCount 8)) := #[0xe00000#28, 0x608000#28, 0xc08000#28, 0x8208000#28, 0x810400#28]

def level4 : Array (BitVec (edgeCount 8)) := #[0x1e00000#28, 0xe08000#28, 0x1c08000#28, 0x8608000#28, 0x618000#28, 0x1818000#28, 0x610400#28, 0xa10400#28, 0x1810400#28, 0x4210400#28, 0x1020840#28]

end Erdos76.CertificateExhaustion.Certificates.ExhaustionN8
