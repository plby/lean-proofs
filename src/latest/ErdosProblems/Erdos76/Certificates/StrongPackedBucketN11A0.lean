/-
Copyright 2026 The Lean-Proofs Authors.
Licensed under the Apache License, Version 2.0.
-/
import ErdosProblems.Erdos76.Certificates.StrongPackedBucketN11Pilot172

/-! Production endpoint for the complete n=11, a=0 strong-certificate corpus. -/

namespace Erdos76.CertificateChecker.Certificates.StrongPackedBucketN11A0

open PackedBucketCertificate

abbrev records : List Blob := StrongPackedBucketN11Pilot172.records

/-- All 172 exact n=11, a=0 records pass the checker. -/
theorem valid : RecordsValid 11 0 records :=
  StrongPackedBucketN11Pilot172.valid

theorem strongPacking_of_mem {blob : Blob} (hblob : blob ∈ records) :
    ∃ entry : BucketCertificate.Entry 11, decode 11 blob = some entry ∧
      HasStrongFractionalPacking (graphOfBits entry.1) (0 : ℝ) :=
  StrongPackedBucketN11Pilot172.strongPacking_of_mem hblob

end Erdos76.CertificateChecker.Certificates.StrongPackedBucketN11A0
