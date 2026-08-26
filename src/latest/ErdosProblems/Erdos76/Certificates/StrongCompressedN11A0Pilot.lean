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
import ErdosProblems.Erdos76.CompressedCertificate
import ErdosProblems.Erdos76.Certificates.PairIndexN11

/-! Pilot compressed strong-packing certificate for one `n = 11`, `a = 0`
base of the Gruslys--Letzter almost-complete theorem. The generator is
untrusted; `checks` is an ordinary kernel reduction via `by decide`. -/

namespace Erdos76.CertificateChecker.Certificates.StrongCompressedN11A0Pilot

open Compressed

def payload : String :=
  "B/////////gcCgBGBBBFBBBFBEBDBBBGBOBFBEBBBHBDBBBSBBBCBHBFBKBBBGBQBJBFBIBBBGBBBBB"

theorem checks : checkStrongLinearStreamPayload 11 0 payload = true := by
  decide

theorem semantic (entry : Entry 11) (hentry : entry ∈ entries 11 payload) :
    HasStrongFractionalPacking (graphOfBits entry.1) (0 : ℝ) :=
  by
    simpa only [Nat.cast_zero] using
      checkStrongLinearStreamPayload_semantic 11 0 payload
        PackingCert.pairIndexValid_11 checks entry hentry

end Erdos76.CertificateChecker.Certificates.StrongCompressedN11A0Pilot
