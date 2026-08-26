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

namespace Erdos76.CertificateExhaustion.Certificates.ExhaustionN9

open CertificateChecker

def level0 : Array (BitVec (edgeCount 9)) := #[0x0#36]

def level1 : Array (BitVec (edgeCount 9)) := #[0x10000000#36]

def level2 : Array (BitVec (edgeCount 9)) := #[0x30000000#36, 0x20200000#36]

def level3 : Array (BitVec (edgeCount 9)) := #[0x70000000#36, 0x30200000#36, 0x60200000#36, 0x810200000#36, 0x40408000#36]

def level4 : Array (BitVec (edgeCount 9)) := #[0xf0000000#36, 0x70200000#36, 0xe0200000#36, 0x830200000#36, 0x30600000#36, 0xc0600000#36, 0x30408000#36, 0x50408000#36, 0xc0408000#36, 0x410408000#36, 0x80810400#36]

def level5 : Array (BitVec (edgeCount 9)) := #[0x1f0000000#36, 0xf0200000#36, 0x1e0200000#36, 0x870200000#36, 0x70600000#36, 0xd0600000#36, 0x1c0600000#36, 0x830600000#36, 0x850600000#36, 0x8c0600000#36, 0x70408000#36, 0xd0408000#36, 0x1c0408000#36, 0x430408000#36, 0x450408000#36, 0x420608000#36, 0x30c08000#36, 0x60c08000#36, 0x90c08000#36, 0x180c08000#36, 0x410c08000#36, 0x30810400#36, 0x90810400#36, 0x180810400#36, 0x210810400#36]

end Erdos76.CertificateExhaustion.Certificates.ExhaustionN9
