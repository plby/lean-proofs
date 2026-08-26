/-
Copyright 2026 The Lean-Proofs Authors.
Licensed under the Apache License, Version 2.0.
-/
import ErdosProblems.Erdos76.Certificates.StrongPackedBucketN11A2AlignedShard000
import ErdosProblems.Erdos76.Certificates.StrongPackedBucketN11A2AlignedShard001
import ErdosProblems.Erdos76.Certificates.StrongPackedBucketN11A2AlignedShard002
import ErdosProblems.Erdos76.Certificates.StrongPackedBucketN11A2AlignedShard003
import ErdosProblems.Erdos76.Certificates.StrongPackedBucketN11A2AlignedShard004
import ErdosProblems.Erdos76.Certificates.StrongPackedBucketN11A2AlignedShard005
import ErdosProblems.Erdos76.Certificates.StrongPackedBucketN11A2AlignedShard006
import ErdosProblems.Erdos76.Certificates.StrongPackedBucketN11A2AlignedShard007
import ErdosProblems.Erdos76.Certificates.StrongPackedBucketN11A2AlignedShard008
import ErdosProblems.Erdos76.Certificates.StrongPackedBucketN11A2AlignedShard009
import ErdosProblems.Erdos76.Certificates.StrongPackedBucketN11A2AlignedShard010

/-! Balanced decode-only alignment aggregate for n=11, a=2. -/
namespace Erdos76.CertificateChecker.Certificates.StrongPackedBucketN11A2Aligned

open PackedBucketCertificate

abbrev missing0_1 : List (BitVec (edgeCount 11)) :=
  StrongPackedBucketN11A2AlignedShard000.missing
abbrev records0_1 : List Blob := StrongPackedBucketN11A2AlignedShard000.records
theorem aligned0_1 :
    AlignedValid 11 2 missing0_1 records0_1 :=
  StrongPackedBucketN11A2AlignedShard000.aligned

abbrev missing1_2 : List (BitVec (edgeCount 11)) :=
  StrongPackedBucketN11A2AlignedShard001.missing
abbrev records1_2 : List Blob := StrongPackedBucketN11A2AlignedShard001.records
theorem aligned1_2 :
    AlignedValid 11 2 missing1_2 records1_2 :=
  StrongPackedBucketN11A2AlignedShard001.aligned

def missing0_2 : List (BitVec (edgeCount 11)) :=
  missing0_1 ++ missing1_2
abbrev records0_2 : List Blob :=
  records0_1 ++ records1_2
theorem aligned0_2 :
    AlignedValid 11 2 missing0_2 records0_2 :=
  aligned0_1.append aligned1_2

abbrev missing2_3 : List (BitVec (edgeCount 11)) :=
  StrongPackedBucketN11A2AlignedShard002.missing
abbrev records2_3 : List Blob := StrongPackedBucketN11A2AlignedShard002.records
theorem aligned2_3 :
    AlignedValid 11 2 missing2_3 records2_3 :=
  StrongPackedBucketN11A2AlignedShard002.aligned

abbrev missing3_4 : List (BitVec (edgeCount 11)) :=
  StrongPackedBucketN11A2AlignedShard003.missing
abbrev records3_4 : List Blob := StrongPackedBucketN11A2AlignedShard003.records
theorem aligned3_4 :
    AlignedValid 11 2 missing3_4 records3_4 :=
  StrongPackedBucketN11A2AlignedShard003.aligned

abbrev missing4_5 : List (BitVec (edgeCount 11)) :=
  StrongPackedBucketN11A2AlignedShard004.missing
abbrev records4_5 : List Blob := StrongPackedBucketN11A2AlignedShard004.records
theorem aligned4_5 :
    AlignedValid 11 2 missing4_5 records4_5 :=
  StrongPackedBucketN11A2AlignedShard004.aligned

def missing3_5 : List (BitVec (edgeCount 11)) :=
  missing3_4 ++ missing4_5
abbrev records3_5 : List Blob :=
  records3_4 ++ records4_5
theorem aligned3_5 :
    AlignedValid 11 2 missing3_5 records3_5 :=
  aligned3_4.append aligned4_5

def missing2_5 : List (BitVec (edgeCount 11)) :=
  missing2_3 ++ missing3_5
abbrev records2_5 : List Blob :=
  records2_3 ++ records3_5
theorem aligned2_5 :
    AlignedValid 11 2 missing2_5 records2_5 :=
  aligned2_3.append aligned3_5

def missing0_5 : List (BitVec (edgeCount 11)) :=
  missing0_2 ++ missing2_5
abbrev records0_5 : List Blob :=
  records0_2 ++ records2_5
theorem aligned0_5 :
    AlignedValid 11 2 missing0_5 records0_5 :=
  aligned0_2.append aligned2_5

abbrev missing5_6 : List (BitVec (edgeCount 11)) :=
  StrongPackedBucketN11A2AlignedShard005.missing
abbrev records5_6 : List Blob := StrongPackedBucketN11A2AlignedShard005.records
theorem aligned5_6 :
    AlignedValid 11 2 missing5_6 records5_6 :=
  StrongPackedBucketN11A2AlignedShard005.aligned

abbrev missing6_7 : List (BitVec (edgeCount 11)) :=
  StrongPackedBucketN11A2AlignedShard006.missing
abbrev records6_7 : List Blob := StrongPackedBucketN11A2AlignedShard006.records
theorem aligned6_7 :
    AlignedValid 11 2 missing6_7 records6_7 :=
  StrongPackedBucketN11A2AlignedShard006.aligned

abbrev missing7_8 : List (BitVec (edgeCount 11)) :=
  StrongPackedBucketN11A2AlignedShard007.missing
abbrev records7_8 : List Blob := StrongPackedBucketN11A2AlignedShard007.records
theorem aligned7_8 :
    AlignedValid 11 2 missing7_8 records7_8 :=
  StrongPackedBucketN11A2AlignedShard007.aligned

def missing6_8 : List (BitVec (edgeCount 11)) :=
  missing6_7 ++ missing7_8
abbrev records6_8 : List Blob :=
  records6_7 ++ records7_8
theorem aligned6_8 :
    AlignedValid 11 2 missing6_8 records6_8 :=
  aligned6_7.append aligned7_8

def missing5_8 : List (BitVec (edgeCount 11)) :=
  missing5_6 ++ missing6_8
abbrev records5_8 : List Blob :=
  records5_6 ++ records6_8
theorem aligned5_8 :
    AlignedValid 11 2 missing5_8 records5_8 :=
  aligned5_6.append aligned6_8

abbrev missing8_9 : List (BitVec (edgeCount 11)) :=
  StrongPackedBucketN11A2AlignedShard008.missing
abbrev records8_9 : List Blob := StrongPackedBucketN11A2AlignedShard008.records
theorem aligned8_9 :
    AlignedValid 11 2 missing8_9 records8_9 :=
  StrongPackedBucketN11A2AlignedShard008.aligned

abbrev missing9_10 : List (BitVec (edgeCount 11)) :=
  StrongPackedBucketN11A2AlignedShard009.missing
abbrev records9_10 : List Blob := StrongPackedBucketN11A2AlignedShard009.records
theorem aligned9_10 :
    AlignedValid 11 2 missing9_10 records9_10 :=
  StrongPackedBucketN11A2AlignedShard009.aligned

abbrev missing10_11 : List (BitVec (edgeCount 11)) :=
  StrongPackedBucketN11A2AlignedShard010.missing
abbrev records10_11 : List Blob := StrongPackedBucketN11A2AlignedShard010.records
theorem aligned10_11 :
    AlignedValid 11 2 missing10_11 records10_11 :=
  StrongPackedBucketN11A2AlignedShard010.aligned

def missing9_11 : List (BitVec (edgeCount 11)) :=
  missing9_10 ++ missing10_11
abbrev records9_11 : List Blob :=
  records9_10 ++ records10_11
theorem aligned9_11 :
    AlignedValid 11 2 missing9_11 records9_11 :=
  aligned9_10.append aligned10_11

def missing8_11 : List (BitVec (edgeCount 11)) :=
  missing8_9 ++ missing9_11
abbrev records8_11 : List Blob :=
  records8_9 ++ records9_11
theorem aligned8_11 :
    AlignedValid 11 2 missing8_11 records8_11 :=
  aligned8_9.append aligned9_11

def missing5_11 : List (BitVec (edgeCount 11)) :=
  missing5_8 ++ missing8_11
abbrev records5_11 : List Blob :=
  records5_8 ++ records8_11
theorem aligned5_11 :
    AlignedValid 11 2 missing5_11 records5_11 :=
  aligned5_8.append aligned8_11

def missing0_11 : List (BitVec (edgeCount 11)) :=
  missing0_5 ++ missing5_11
abbrev records0_11 : List Blob :=
  records0_5 ++ records5_11
theorem aligned0_11 :
    AlignedValid 11 2 missing0_11 records0_11 :=
  aligned0_5.append aligned5_11

abbrev missing : List (BitVec (edgeCount 11)) := missing0_11
abbrev records : List Blob := records0_11
theorem aligned : AlignedValid 11 2 missing records :=
  aligned0_11

end Erdos76.CertificateChecker.Certificates.StrongPackedBucketN11A2Aligned

