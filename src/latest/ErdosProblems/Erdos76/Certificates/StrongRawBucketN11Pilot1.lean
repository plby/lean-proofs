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
import ErdosProblems.Erdos76.RawBucketCertificate

/-! Raw-array scaling pilot containing the first 1 exact `n = 11`, `a = 0`
strong packing certificates. The generator is untrusted; `checks` is ordinary
kernel reduction via `by decide`. -/

namespace Erdos76.CertificateChecker.Certificates.StrongRawBucketN11Pilot1

open RawBucketCertificate

def record0 : Cert 11 :=
{ mask := BitVec.ofNat (edgeCount 11) 31560381763682303,
    denominator := 2,
    terms := #[(6, 1), (7, 1), (12, 1), (13, 1), (18, 1), (22, 1), (25, 1), (26, 1), (32, 1), (46, 1), (51, 1), (55, 1), (56, 1), (63, 1), (66, 1), (67, 1), (85, 1), (86, 1), (88, 1), (95, 1), (100, 1), (110, 1), (111, 1), (117, 1), (133, 1), (142, 1), (147, 1), (155, 1), (156, 1), (162, 1), (163, 1), (164, 1)],
    buckets := #[#[0, 1], #[2, 3], #[9, 10], #[4, 5], #[11, 12], #[16, 17], #[6, 7], #[9, 13], #[9, 18], #[21, 22], #[4, 8], #[14, 15], #[18, 19], #[4, 23], #[18, 24], #[2, 6], #[11, 14], #[2, 20], #[11, 21], #[6, 21], #[14, 26], #[3, 7], #[12, 15], #[3, 19], #[12, 22], #[7, 22], #[15, 19], #[27, 28], #[0, 8], #[0, 13], #[16, 20], #[16, 23], #[13, 25], #[8, 23], #[20, 27], #[27, 29], #[1, 5], #[1, 10], #[10, 17], #[5, 17], #[24, 25], #[24, 26], #[26, 28], #[28, 30], #[25, 31], #[], #[], #[], #[], #[], #[], #[], #[29, 30], #[29, 31], #[30, 31]] }

theorem check0 : checkStrong 11 0 record0 = true := by
  rfl

def records0_1 : Array (Cert 11) := #[record0]

theorem valid0_1 : RecordsValid 11 0 records0_1 := by
  simpa [records0_1] using RecordsValid.singleton check0

abbrev records : Array (Cert 11) := records0_1

theorem valid : RecordsValid 11 0 records := valid0_1

end Erdos76.CertificateChecker.Certificates.StrongRawBucketN11Pilot1
