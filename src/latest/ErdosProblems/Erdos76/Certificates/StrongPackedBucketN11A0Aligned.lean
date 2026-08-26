/-
Copyright 2026 The Lean-Proofs Authors.
Licensed under the Apache License, Version 2.0.
-/
import ErdosProblems.Erdos76.Certificates.StrongPackedBucketN11A0AlignedShard000
import ErdosProblems.Erdos76.Certificates.StrongPackedBucketN11A0AlignedShard001
import ErdosProblems.Erdos76.Certificates.StrongPackedBucketN11A0AlignedShard002
import ErdosProblems.Erdos76.Certificates.StrongPackedBucketN11A0AlignedShard003
import ErdosProblems.Erdos76.Certificates.StrongPackedBucketN11A0AlignedShard004
import ErdosProblems.Erdos76.Certificates.StrongPackedBucketN11A0AlignedShard005

/-! Balanced decode-only alignment aggregate for n=11, a=0. -/
namespace Erdos76.CertificateChecker.Certificates.StrongPackedBucketN11A0Aligned

open PackedBucketCertificate

abbrev missing0_1 : List (BitVec (edgeCount 11)) :=
  StrongPackedBucketN11A0AlignedShard000.missing
abbrev records0_1 : List Blob := StrongPackedBucketN11A0AlignedShard000.records
theorem aligned0_1 :
    AlignedValid 11 0 missing0_1 records0_1 :=
  StrongPackedBucketN11A0AlignedShard000.aligned

abbrev missing1_2 : List (BitVec (edgeCount 11)) :=
  StrongPackedBucketN11A0AlignedShard001.missing
abbrev records1_2 : List Blob := StrongPackedBucketN11A0AlignedShard001.records
theorem aligned1_2 :
    AlignedValid 11 0 missing1_2 records1_2 :=
  StrongPackedBucketN11A0AlignedShard001.aligned

abbrev missing2_3 : List (BitVec (edgeCount 11)) :=
  StrongPackedBucketN11A0AlignedShard002.missing
abbrev records2_3 : List Blob := StrongPackedBucketN11A0AlignedShard002.records
theorem aligned2_3 :
    AlignedValid 11 0 missing2_3 records2_3 :=
  StrongPackedBucketN11A0AlignedShard002.aligned

def missing1_3 : List (BitVec (edgeCount 11)) :=
  missing1_2 ++ missing2_3
abbrev records1_3 : List Blob :=
  records1_2 ++ records2_3
theorem aligned1_3 :
    AlignedValid 11 0 missing1_3 records1_3 :=
  aligned1_2.append aligned2_3

def missing0_3 : List (BitVec (edgeCount 11)) :=
  missing0_1 ++ missing1_3
abbrev records0_3 : List Blob :=
  records0_1 ++ records1_3
theorem aligned0_3 :
    AlignedValid 11 0 missing0_3 records0_3 :=
  aligned0_1.append aligned1_3

abbrev missing3_4 : List (BitVec (edgeCount 11)) :=
  StrongPackedBucketN11A0AlignedShard003.missing
abbrev records3_4 : List Blob := StrongPackedBucketN11A0AlignedShard003.records
theorem aligned3_4 :
    AlignedValid 11 0 missing3_4 records3_4 :=
  StrongPackedBucketN11A0AlignedShard003.aligned

abbrev missing4_5 : List (BitVec (edgeCount 11)) :=
  StrongPackedBucketN11A0AlignedShard004.missing
abbrev records4_5 : List Blob := StrongPackedBucketN11A0AlignedShard004.records
theorem aligned4_5 :
    AlignedValid 11 0 missing4_5 records4_5 :=
  StrongPackedBucketN11A0AlignedShard004.aligned

abbrev missing5_6 : List (BitVec (edgeCount 11)) :=
  StrongPackedBucketN11A0AlignedShard005.missing
abbrev records5_6 : List Blob := StrongPackedBucketN11A0AlignedShard005.records
theorem aligned5_6 :
    AlignedValid 11 0 missing5_6 records5_6 :=
  StrongPackedBucketN11A0AlignedShard005.aligned

def missing4_6 : List (BitVec (edgeCount 11)) :=
  missing4_5 ++ missing5_6
abbrev records4_6 : List Blob :=
  records4_5 ++ records5_6
theorem aligned4_6 :
    AlignedValid 11 0 missing4_6 records4_6 :=
  aligned4_5.append aligned5_6

def missing3_6 : List (BitVec (edgeCount 11)) :=
  missing3_4 ++ missing4_6
abbrev records3_6 : List Blob :=
  records3_4 ++ records4_6
theorem aligned3_6 :
    AlignedValid 11 0 missing3_6 records3_6 :=
  aligned3_4.append aligned4_6

def missing0_6 : List (BitVec (edgeCount 11)) :=
  missing0_3 ++ missing3_6
abbrev records0_6 : List Blob :=
  records0_3 ++ records3_6
theorem aligned0_6 :
    AlignedValid 11 0 missing0_6 records0_6 :=
  aligned0_3.append aligned3_6

abbrev missing : List (BitVec (edgeCount 11)) := missing0_6
abbrev records : List Blob := records0_6
theorem aligned : AlignedValid 11 0 missing records :=
  aligned0_6

end Erdos76.CertificateChecker.Certificates.StrongPackedBucketN11A0Aligned

