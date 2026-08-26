/-
Copyright 2026 The Lean-Proofs Authors.
Licensed under the Apache License, Version 2.0.
-/
import ErdosProblems.Erdos76.Certificates.StrongPackedBucketN11A1AlignedShard000
import ErdosProblems.Erdos76.Certificates.StrongPackedBucketN11A1AlignedShard001
import ErdosProblems.Erdos76.Certificates.StrongPackedBucketN11A1AlignedShard002
import ErdosProblems.Erdos76.Certificates.StrongPackedBucketN11A1AlignedShard003

/-! Balanced decode-only alignment aggregate for n=11, a=1. -/
namespace Erdos76.CertificateChecker.Certificates.StrongPackedBucketN11A1Aligned

open PackedBucketCertificate

abbrev missing0_1 : List (BitVec (edgeCount 11)) :=
  StrongPackedBucketN11A1AlignedShard000.missing
abbrev records0_1 : List Blob := StrongPackedBucketN11A1AlignedShard000.records
theorem aligned0_1 :
    AlignedValid 11 1 missing0_1 records0_1 :=
  StrongPackedBucketN11A1AlignedShard000.aligned

abbrev missing1_2 : List (BitVec (edgeCount 11)) :=
  StrongPackedBucketN11A1AlignedShard001.missing
abbrev records1_2 : List Blob := StrongPackedBucketN11A1AlignedShard001.records
theorem aligned1_2 :
    AlignedValid 11 1 missing1_2 records1_2 :=
  StrongPackedBucketN11A1AlignedShard001.aligned

def missing0_2 : List (BitVec (edgeCount 11)) :=
  missing0_1 ++ missing1_2
abbrev records0_2 : List Blob :=
  records0_1 ++ records1_2
theorem aligned0_2 :
    AlignedValid 11 1 missing0_2 records0_2 :=
  aligned0_1.append aligned1_2

abbrev missing2_3 : List (BitVec (edgeCount 11)) :=
  StrongPackedBucketN11A1AlignedShard002.missing
abbrev records2_3 : List Blob := StrongPackedBucketN11A1AlignedShard002.records
theorem aligned2_3 :
    AlignedValid 11 1 missing2_3 records2_3 :=
  StrongPackedBucketN11A1AlignedShard002.aligned

abbrev missing3_4 : List (BitVec (edgeCount 11)) :=
  StrongPackedBucketN11A1AlignedShard003.missing
abbrev records3_4 : List Blob := StrongPackedBucketN11A1AlignedShard003.records
theorem aligned3_4 :
    AlignedValid 11 1 missing3_4 records3_4 :=
  StrongPackedBucketN11A1AlignedShard003.aligned

def missing2_4 : List (BitVec (edgeCount 11)) :=
  missing2_3 ++ missing3_4
abbrev records2_4 : List Blob :=
  records2_3 ++ records3_4
theorem aligned2_4 :
    AlignedValid 11 1 missing2_4 records2_4 :=
  aligned2_3.append aligned3_4

def missing0_4 : List (BitVec (edgeCount 11)) :=
  missing0_2 ++ missing2_4
abbrev records0_4 : List Blob :=
  records0_2 ++ records2_4
theorem aligned0_4 :
    AlignedValid 11 1 missing0_4 records0_4 :=
  aligned0_2.append aligned2_4

abbrev missing : List (BitVec (edgeCount 11)) := missing0_4
abbrev records : List Blob := records0_4
theorem aligned : AlignedValid 11 1 missing records :=
  aligned0_4

end Erdos76.CertificateChecker.Certificates.StrongPackedBucketN11A1Aligned

