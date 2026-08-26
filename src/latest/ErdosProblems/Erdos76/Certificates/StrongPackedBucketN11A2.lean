/-
Copyright 2026 The Lean-Proofs Authors.
Licensed under the Apache License, Version 2.0.
-/
import ErdosProblems.Erdos76.Certificates.PairIndexN11
import ErdosProblems.Erdos76.Certificates.StrongPackedBucketN11A2Shard000
import ErdosProblems.Erdos76.Certificates.StrongPackedBucketN11A2Shard001
import ErdosProblems.Erdos76.Certificates.StrongPackedBucketN11A2Shard002
import ErdosProblems.Erdos76.Certificates.StrongPackedBucketN11A2Shard003
import ErdosProblems.Erdos76.Certificates.StrongPackedBucketN11A2Shard004
import ErdosProblems.Erdos76.Certificates.StrongPackedBucketN11A2Shard005
import ErdosProblems.Erdos76.Certificates.StrongPackedBucketN11A2Shard006
import ErdosProblems.Erdos76.Certificates.StrongPackedBucketN11A2Shard007
import ErdosProblems.Erdos76.Certificates.StrongPackedBucketN11A2Shard008
import ErdosProblems.Erdos76.Certificates.StrongPackedBucketN11A2Shard009
import ErdosProblems.Erdos76.Certificates.StrongPackedBucketN11A2Shard010

/-! Production endpoint for all 1305 exact n=11, a=2 strong certificates. -/

namespace Erdos76.CertificateChecker.Certificates.StrongPackedBucketN11A2

open PackedBucketCertificate

abbrev records0_1 : List Blob := StrongPackedBucketN11A2Shard000.records
theorem valid0_1 : RecordsValid 11 2 records0_1 :=
  StrongPackedBucketN11A2Shard000.valid

abbrev records1_2 : List Blob := StrongPackedBucketN11A2Shard001.records
theorem valid1_2 : RecordsValid 11 2 records1_2 :=
  StrongPackedBucketN11A2Shard001.valid

def records0_2 : List Blob :=
  records0_1 ++ records1_2
theorem valid0_2 : RecordsValid 11 2 records0_2 :=
  valid0_1.append valid1_2

abbrev records2_3 : List Blob := StrongPackedBucketN11A2Shard002.records
theorem valid2_3 : RecordsValid 11 2 records2_3 :=
  StrongPackedBucketN11A2Shard002.valid

abbrev records3_4 : List Blob := StrongPackedBucketN11A2Shard003.records
theorem valid3_4 : RecordsValid 11 2 records3_4 :=
  StrongPackedBucketN11A2Shard003.valid

abbrev records4_5 : List Blob := StrongPackedBucketN11A2Shard004.records
theorem valid4_5 : RecordsValid 11 2 records4_5 :=
  StrongPackedBucketN11A2Shard004.valid

def records3_5 : List Blob :=
  records3_4 ++ records4_5
theorem valid3_5 : RecordsValid 11 2 records3_5 :=
  valid3_4.append valid4_5

def records2_5 : List Blob :=
  records2_3 ++ records3_5
theorem valid2_5 : RecordsValid 11 2 records2_5 :=
  valid2_3.append valid3_5

def records0_5 : List Blob :=
  records0_2 ++ records2_5
theorem valid0_5 : RecordsValid 11 2 records0_5 :=
  valid0_2.append valid2_5

abbrev records5_6 : List Blob := StrongPackedBucketN11A2Shard005.records
theorem valid5_6 : RecordsValid 11 2 records5_6 :=
  StrongPackedBucketN11A2Shard005.valid

abbrev records6_7 : List Blob := StrongPackedBucketN11A2Shard006.records
theorem valid6_7 : RecordsValid 11 2 records6_7 :=
  StrongPackedBucketN11A2Shard006.valid

abbrev records7_8 : List Blob := StrongPackedBucketN11A2Shard007.records
theorem valid7_8 : RecordsValid 11 2 records7_8 :=
  StrongPackedBucketN11A2Shard007.valid

def records6_8 : List Blob :=
  records6_7 ++ records7_8
theorem valid6_8 : RecordsValid 11 2 records6_8 :=
  valid6_7.append valid7_8

def records5_8 : List Blob :=
  records5_6 ++ records6_8
theorem valid5_8 : RecordsValid 11 2 records5_8 :=
  valid5_6.append valid6_8

abbrev records8_9 : List Blob := StrongPackedBucketN11A2Shard008.records
theorem valid8_9 : RecordsValid 11 2 records8_9 :=
  StrongPackedBucketN11A2Shard008.valid

abbrev records9_10 : List Blob := StrongPackedBucketN11A2Shard009.records
theorem valid9_10 : RecordsValid 11 2 records9_10 :=
  StrongPackedBucketN11A2Shard009.valid

abbrev records10_11 : List Blob := StrongPackedBucketN11A2Shard010.records
theorem valid10_11 : RecordsValid 11 2 records10_11 :=
  StrongPackedBucketN11A2Shard010.valid

def records9_11 : List Blob :=
  records9_10 ++ records10_11
theorem valid9_11 : RecordsValid 11 2 records9_11 :=
  valid9_10.append valid10_11

def records8_11 : List Blob :=
  records8_9 ++ records9_11
theorem valid8_11 : RecordsValid 11 2 records8_11 :=
  valid8_9.append valid9_11

def records5_11 : List Blob :=
  records5_8 ++ records8_11
theorem valid5_11 : RecordsValid 11 2 records5_11 :=
  valid5_8.append valid8_11

def records0_11 : List Blob :=
  records0_5 ++ records5_11
theorem valid0_11 : RecordsValid 11 2 records0_11 :=
  valid0_5.append valid5_11

abbrev records : List Blob := records0_11
theorem valid : RecordsValid 11 2 records := valid0_11

theorem strongPacking_of_mem {blob : Blob} (hblob : blob ∈ records) :
    ∃ entry : BucketCertificate.Entry 11, decode 11 blob = some entry ∧
      HasStrongFractionalPacking (graphOfBits entry.1) (((2 : ℕ) : ℝ)) :=
  valid.strongPacking_of_mem PackingCert.pairIndexValid_11 hblob

end Erdos76.CertificateChecker.Certificates.StrongPackedBucketN11A2

