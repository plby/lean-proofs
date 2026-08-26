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
import ErdosProblems.Erdos76.StagedBucketCertificate
import ErdosProblems.Erdos76.Certificates.PairIndexN11

/-! One-record executable pilot for the incidence-bucket strong-certificate
format. The generator is untrusted; both decoding and the finite certificate
conditions are checked by ordinary kernel reduction. -/

namespace Erdos76.CertificateChecker.Certificates.StrongBucketN11Pilot

open StagedBucketCertificate

def base : String :=
  "/////////gcCgBGBBBFBBBFBEBDBBBGBOBFBEBBBHBDBBBSBBBCBHBFBKBBBGBQBJBFBIBBBGBBBBB"

def lowBuckets : String :=
  "CABCCBCJBCEBCLBCQBCGBCJECJJCVBCEECOBCSBCETCSGCCECLDCCSCLKCGPCOMCDECMDCDQCMKCHPCPE"

def highBuckets : String :=
  "CbBCAICANCQECQHCNMCIPCUHCbCCBECBJCKHCFMCYBCYCCaCCcCCZGAAAAAAACdBCdCCeB"

theorem baseChecks : checkBaseRecord 11 0 base = true := by
  decide

theorem lowChecks : checkChunkRecord 11 0 27 base lowBuckets = true := by
  decide

theorem highChecks : checkChunkRecord 11 27 28 base highBuckets = true := by
  decide

end Erdos76.CertificateChecker.Certificates.StrongBucketN11Pilot
