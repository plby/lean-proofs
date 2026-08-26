/-
Copyright 2026 The Lean-Proofs Authors.
Licensed under the Apache License, Version 2.0.
-/
import ErdosProblems.Erdos76.Certificates.PairIndexN13
import ErdosProblems.Erdos76.Certificates.StrongPackedBucketN13A4PilotShard000

/-! Eight-record kernel-check pilot from the order-13, defect-four corpus.
This does not assert exhaustion of the order-13 bases. -/
namespace Erdos76.CertificateChecker.Certificates.StrongPackedBucketN13A4Pilot

open PackedBucketCertificate

abbrev records0_1 : List Blob := StrongPackedBucketN13A4PilotShard000.records
theorem valid0_1 : RecordsValid 13 4 records0_1 :=
  StrongPackedBucketN13A4PilotShard000.valid

abbrev records : List Blob := records0_1
theorem valid : RecordsValid 13 4 records := valid0_1

theorem strongPacking_of_mem {blob : Blob} (hblob : blob ∈ records) :
    ∃ entry : BucketCertificate.Entry 13, decode 13 blob = some entry ∧
      HasStrongFractionalPacking (graphOfBits entry.1) ((4 : ℕ) : ℝ) :=
  valid.strongPacking_of_mem PackingCert.pairIndexValid_13 hblob

end Erdos76.CertificateChecker.Certificates.StrongPackedBucketN13A4Pilot
