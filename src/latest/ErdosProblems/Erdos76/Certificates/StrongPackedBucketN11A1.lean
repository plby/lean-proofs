/-
Copyright 2026 The Lean-Proofs Authors.
Licensed under the Apache License, Version 2.0.
-/
import ErdosProblems.Erdos76.Certificates.PairIndexN11
import ErdosProblems.Erdos76.Certificates.StrongPackedBucketN11A1Shard000
import ErdosProblems.Erdos76.Certificates.StrongPackedBucketN11A1Shard001
import ErdosProblems.Erdos76.Certificates.StrongPackedBucketN11A1Shard002
import ErdosProblems.Erdos76.Certificates.StrongPackedBucketN11A1Shard003

/-! Production endpoint for all 467 exact n=11, a=1 strong certificates. -/

namespace Erdos76.CertificateChecker.Certificates.StrongPackedBucketN11A1

open PackedBucketCertificate

abbrev records0_1 : List Blob := StrongPackedBucketN11A1Shard000.records
theorem valid0_1 : RecordsValid 11 1 records0_1 :=
  StrongPackedBucketN11A1Shard000.valid

abbrev records1_2 : List Blob := StrongPackedBucketN11A1Shard001.records
theorem valid1_2 : RecordsValid 11 1 records1_2 :=
  StrongPackedBucketN11A1Shard001.valid

def records0_2 : List Blob :=
  records0_1 ++ records1_2
theorem valid0_2 : RecordsValid 11 1 records0_2 :=
  valid0_1.append valid1_2

abbrev records2_3 : List Blob := StrongPackedBucketN11A1Shard002.records
theorem valid2_3 : RecordsValid 11 1 records2_3 :=
  StrongPackedBucketN11A1Shard002.valid

abbrev records3_4 : List Blob := StrongPackedBucketN11A1Shard003.records
theorem valid3_4 : RecordsValid 11 1 records3_4 :=
  StrongPackedBucketN11A1Shard003.valid

def records2_4 : List Blob :=
  records2_3 ++ records3_4
theorem valid2_4 : RecordsValid 11 1 records2_4 :=
  valid2_3.append valid3_4

def records0_4 : List Blob :=
  records0_2 ++ records2_4
theorem valid0_4 : RecordsValid 11 1 records0_4 :=
  valid0_2.append valid2_4

abbrev records : List Blob := records0_4
theorem valid : RecordsValid 11 1 records := valid0_4

theorem strongPacking_of_mem {blob : Blob} (hblob : blob ∈ records) :
    ∃ entry : BucketCertificate.Entry 11, decode 11 blob = some entry ∧
      HasStrongFractionalPacking (graphOfBits entry.1) (((1 : ℕ) : ℝ)) :=
  valid.strongPacking_of_mem PackingCert.pairIndexValid_11 hblob

end Erdos76.CertificateChecker.Certificates.StrongPackedBucketN11A1

