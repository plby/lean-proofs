/-
Copyright 2026 The Lean-Proofs Authors.
Licensed under the Apache License, Version 2.0.
-/
import ErdosProblems.Erdos76.Certificates.StrongPackedBucketN12A0AlignedShard000
import ErdosProblems.Erdos76.Certificates.StrongPackedBucketN12A0AlignedShard001
import ErdosProblems.Erdos76.Certificates.StrongPackedBucketN12A0AlignedShard002
import ErdosProblems.Erdos76.Certificates.StrongPackedBucketN12A0AlignedShard003

/-! Balanced alignment aggregate for all 485 n=12, a=0 records. -/
namespace Erdos76.CertificateChecker.Certificates.StrongPackedBucketN12A0Aligned

open PackedBucketCertificate

abbrev missing0_1 : List (BitVec (edgeCount 12)) :=
  StrongPackedBucketN12A0AlignedShard000.missing
abbrev records0_1 : List Blob := StrongPackedBucketN12A0AlignedShard000.records
theorem aligned0_1 :
    AlignedValid 12 0 missing0_1 records0_1 :=
  StrongPackedBucketN12A0AlignedShard000.aligned

abbrev missing1_2 : List (BitVec (edgeCount 12)) :=
  StrongPackedBucketN12A0AlignedShard001.missing
abbrev records1_2 : List Blob := StrongPackedBucketN12A0AlignedShard001.records
theorem aligned1_2 :
    AlignedValid 12 0 missing1_2 records1_2 :=
  StrongPackedBucketN12A0AlignedShard001.aligned

def missing0_2 : List (BitVec (edgeCount 12)) :=
  missing0_1 ++ missing1_2
abbrev records0_2 : List Blob :=
  records0_1 ++ records1_2
theorem aligned0_2 :
    AlignedValid 12 0 missing0_2 records0_2 :=
  aligned0_1.append aligned1_2

abbrev missing2_3 : List (BitVec (edgeCount 12)) :=
  StrongPackedBucketN12A0AlignedShard002.missing
abbrev records2_3 : List Blob := StrongPackedBucketN12A0AlignedShard002.records
theorem aligned2_3 :
    AlignedValid 12 0 missing2_3 records2_3 :=
  StrongPackedBucketN12A0AlignedShard002.aligned

abbrev missing3_4 : List (BitVec (edgeCount 12)) :=
  StrongPackedBucketN12A0AlignedShard003.missing
abbrev records3_4 : List Blob := StrongPackedBucketN12A0AlignedShard003.records
theorem aligned3_4 :
    AlignedValid 12 0 missing3_4 records3_4 :=
  StrongPackedBucketN12A0AlignedShard003.aligned

def missing2_4 : List (BitVec (edgeCount 12)) :=
  missing2_3 ++ missing3_4
abbrev records2_4 : List Blob :=
  records2_3 ++ records3_4
theorem aligned2_4 :
    AlignedValid 12 0 missing2_4 records2_4 :=
  aligned2_3.append aligned3_4

def missing0_4 : List (BitVec (edgeCount 12)) :=
  missing0_2 ++ missing2_4
abbrev records0_4 : List Blob :=
  records0_2 ++ records2_4
theorem aligned0_4 :
    AlignedValid 12 0 missing0_4 records0_4 :=
  aligned0_2.append aligned2_4

abbrev missing : List (BitVec (edgeCount 12)) := missing0_4
abbrev records : List Blob := records0_4
theorem aligned : AlignedValid 12 0 missing records := aligned0_4

end Erdos76.CertificateChecker.Certificates.StrongPackedBucketN12A0Aligned
