/-
Copyright 2026 The Lean-Proofs Authors.
Licensed under the Apache License, Version 2.0.
-/
import ErdosProblems.Erdos76.Certificates.PairIndexN11
import ErdosProblems.Erdos76.Certificates.StrongPackedBucketN11A3Shard000
import ErdosProblems.Erdos76.Certificates.StrongPackedBucketN11A3Shard001
import ErdosProblems.Erdos76.Certificates.StrongPackedBucketN11A3Shard002
import ErdosProblems.Erdos76.Certificates.StrongPackedBucketN11A3Shard003
import ErdosProblems.Erdos76.Certificates.StrongPackedBucketN11A3Shard004
import ErdosProblems.Erdos76.Certificates.StrongPackedBucketN11A3Shard005
import ErdosProblems.Erdos76.Certificates.StrongPackedBucketN11A3Shard006
import ErdosProblems.Erdos76.Certificates.StrongPackedBucketN11A3Shard007
import ErdosProblems.Erdos76.Certificates.StrongPackedBucketN11A3Shard008
import ErdosProblems.Erdos76.Certificates.StrongPackedBucketN11A3Shard009
import ErdosProblems.Erdos76.Certificates.StrongPackedBucketN11A3Shard010
import ErdosProblems.Erdos76.Certificates.StrongPackedBucketN11A3Shard011
import ErdosProblems.Erdos76.Certificates.StrongPackedBucketN11A3Shard012
import ErdosProblems.Erdos76.Certificates.StrongPackedBucketN11A3Shard013
import ErdosProblems.Erdos76.Certificates.StrongPackedBucketN11A3Shard014
import ErdosProblems.Erdos76.Certificates.StrongPackedBucketN11A3Shard015
import ErdosProblems.Erdos76.Certificates.StrongPackedBucketN11A3Shard016
import ErdosProblems.Erdos76.Certificates.StrongPackedBucketN11A3Shard017
import ErdosProblems.Erdos76.Certificates.StrongPackedBucketN11A3Shard018
import ErdosProblems.Erdos76.Certificates.StrongPackedBucketN11A3Shard019
import ErdosProblems.Erdos76.Certificates.StrongPackedBucketN11A3Shard020
import ErdosProblems.Erdos76.Certificates.StrongPackedBucketN11A3Shard021
import ErdosProblems.Erdos76.Certificates.StrongPackedBucketN11A3Shard022
import ErdosProblems.Erdos76.Certificates.StrongPackedBucketN11A3Shard023
import ErdosProblems.Erdos76.Certificates.StrongPackedBucketN11A3Shard024
import ErdosProblems.Erdos76.Certificates.StrongPackedBucketN11A3Shard025
import ErdosProblems.Erdos76.Certificates.StrongPackedBucketN11A3Shard026
import ErdosProblems.Erdos76.Certificates.StrongPackedBucketN11A3Shard027
import ErdosProblems.Erdos76.Certificates.StrongPackedBucketN11A3Shard028

/-! Production endpoint for all 3664 exact n=11, a=3 strong certificates. -/

namespace Erdos76.CertificateChecker.Certificates.StrongPackedBucketN11A3

open PackedBucketCertificate

abbrev records0_1 : List Blob := StrongPackedBucketN11A3Shard000.records
theorem valid0_1 : RecordsValid 11 3 records0_1 :=
  StrongPackedBucketN11A3Shard000.valid

abbrev records1_2 : List Blob := StrongPackedBucketN11A3Shard001.records
theorem valid1_2 : RecordsValid 11 3 records1_2 :=
  StrongPackedBucketN11A3Shard001.valid

abbrev records2_3 : List Blob := StrongPackedBucketN11A3Shard002.records
theorem valid2_3 : RecordsValid 11 3 records2_3 :=
  StrongPackedBucketN11A3Shard002.valid

def records1_3 : List Blob :=
  records1_2 ++ records2_3
theorem valid1_3 : RecordsValid 11 3 records1_3 :=
  valid1_2.append valid2_3

def records0_3 : List Blob :=
  records0_1 ++ records1_3
theorem valid0_3 : RecordsValid 11 3 records0_3 :=
  valid0_1.append valid1_3

abbrev records3_4 : List Blob := StrongPackedBucketN11A3Shard003.records
theorem valid3_4 : RecordsValid 11 3 records3_4 :=
  StrongPackedBucketN11A3Shard003.valid

abbrev records4_5 : List Blob := StrongPackedBucketN11A3Shard004.records
theorem valid4_5 : RecordsValid 11 3 records4_5 :=
  StrongPackedBucketN11A3Shard004.valid

def records3_5 : List Blob :=
  records3_4 ++ records4_5
theorem valid3_5 : RecordsValid 11 3 records3_5 :=
  valid3_4.append valid4_5

abbrev records5_6 : List Blob := StrongPackedBucketN11A3Shard005.records
theorem valid5_6 : RecordsValid 11 3 records5_6 :=
  StrongPackedBucketN11A3Shard005.valid

abbrev records6_7 : List Blob := StrongPackedBucketN11A3Shard006.records
theorem valid6_7 : RecordsValid 11 3 records6_7 :=
  StrongPackedBucketN11A3Shard006.valid

def records5_7 : List Blob :=
  records5_6 ++ records6_7
theorem valid5_7 : RecordsValid 11 3 records5_7 :=
  valid5_6.append valid6_7

def records3_7 : List Blob :=
  records3_5 ++ records5_7
theorem valid3_7 : RecordsValid 11 3 records3_7 :=
  valid3_5.append valid5_7

def records0_7 : List Blob :=
  records0_3 ++ records3_7
theorem valid0_7 : RecordsValid 11 3 records0_7 :=
  valid0_3.append valid3_7

abbrev records7_8 : List Blob := StrongPackedBucketN11A3Shard007.records
theorem valid7_8 : RecordsValid 11 3 records7_8 :=
  StrongPackedBucketN11A3Shard007.valid

abbrev records8_9 : List Blob := StrongPackedBucketN11A3Shard008.records
theorem valid8_9 : RecordsValid 11 3 records8_9 :=
  StrongPackedBucketN11A3Shard008.valid

abbrev records9_10 : List Blob := StrongPackedBucketN11A3Shard009.records
theorem valid9_10 : RecordsValid 11 3 records9_10 :=
  StrongPackedBucketN11A3Shard009.valid

def records8_10 : List Blob :=
  records8_9 ++ records9_10
theorem valid8_10 : RecordsValid 11 3 records8_10 :=
  valid8_9.append valid9_10

def records7_10 : List Blob :=
  records7_8 ++ records8_10
theorem valid7_10 : RecordsValid 11 3 records7_10 :=
  valid7_8.append valid8_10

abbrev records10_11 : List Blob := StrongPackedBucketN11A3Shard010.records
theorem valid10_11 : RecordsValid 11 3 records10_11 :=
  StrongPackedBucketN11A3Shard010.valid

abbrev records11_12 : List Blob := StrongPackedBucketN11A3Shard011.records
theorem valid11_12 : RecordsValid 11 3 records11_12 :=
  StrongPackedBucketN11A3Shard011.valid

def records10_12 : List Blob :=
  records10_11 ++ records11_12
theorem valid10_12 : RecordsValid 11 3 records10_12 :=
  valid10_11.append valid11_12

abbrev records12_13 : List Blob := StrongPackedBucketN11A3Shard012.records
theorem valid12_13 : RecordsValid 11 3 records12_13 :=
  StrongPackedBucketN11A3Shard012.valid

abbrev records13_14 : List Blob := StrongPackedBucketN11A3Shard013.records
theorem valid13_14 : RecordsValid 11 3 records13_14 :=
  StrongPackedBucketN11A3Shard013.valid

def records12_14 : List Blob :=
  records12_13 ++ records13_14
theorem valid12_14 : RecordsValid 11 3 records12_14 :=
  valid12_13.append valid13_14

def records10_14 : List Blob :=
  records10_12 ++ records12_14
theorem valid10_14 : RecordsValid 11 3 records10_14 :=
  valid10_12.append valid12_14

def records7_14 : List Blob :=
  records7_10 ++ records10_14
theorem valid7_14 : RecordsValid 11 3 records7_14 :=
  valid7_10.append valid10_14

def records0_14 : List Blob :=
  records0_7 ++ records7_14
theorem valid0_14 : RecordsValid 11 3 records0_14 :=
  valid0_7.append valid7_14

abbrev records14_15 : List Blob := StrongPackedBucketN11A3Shard014.records
theorem valid14_15 : RecordsValid 11 3 records14_15 :=
  StrongPackedBucketN11A3Shard014.valid

abbrev records15_16 : List Blob := StrongPackedBucketN11A3Shard015.records
theorem valid15_16 : RecordsValid 11 3 records15_16 :=
  StrongPackedBucketN11A3Shard015.valid

abbrev records16_17 : List Blob := StrongPackedBucketN11A3Shard016.records
theorem valid16_17 : RecordsValid 11 3 records16_17 :=
  StrongPackedBucketN11A3Shard016.valid

def records15_17 : List Blob :=
  records15_16 ++ records16_17
theorem valid15_17 : RecordsValid 11 3 records15_17 :=
  valid15_16.append valid16_17

def records14_17 : List Blob :=
  records14_15 ++ records15_17
theorem valid14_17 : RecordsValid 11 3 records14_17 :=
  valid14_15.append valid15_17

abbrev records17_18 : List Blob := StrongPackedBucketN11A3Shard017.records
theorem valid17_18 : RecordsValid 11 3 records17_18 :=
  StrongPackedBucketN11A3Shard017.valid

abbrev records18_19 : List Blob := StrongPackedBucketN11A3Shard018.records
theorem valid18_19 : RecordsValid 11 3 records18_19 :=
  StrongPackedBucketN11A3Shard018.valid

def records17_19 : List Blob :=
  records17_18 ++ records18_19
theorem valid17_19 : RecordsValid 11 3 records17_19 :=
  valid17_18.append valid18_19

abbrev records19_20 : List Blob := StrongPackedBucketN11A3Shard019.records
theorem valid19_20 : RecordsValid 11 3 records19_20 :=
  StrongPackedBucketN11A3Shard019.valid

abbrev records20_21 : List Blob := StrongPackedBucketN11A3Shard020.records
theorem valid20_21 : RecordsValid 11 3 records20_21 :=
  StrongPackedBucketN11A3Shard020.valid

def records19_21 : List Blob :=
  records19_20 ++ records20_21
theorem valid19_21 : RecordsValid 11 3 records19_21 :=
  valid19_20.append valid20_21

def records17_21 : List Blob :=
  records17_19 ++ records19_21
theorem valid17_21 : RecordsValid 11 3 records17_21 :=
  valid17_19.append valid19_21

def records14_21 : List Blob :=
  records14_17 ++ records17_21
theorem valid14_21 : RecordsValid 11 3 records14_21 :=
  valid14_17.append valid17_21

abbrev records21_22 : List Blob := StrongPackedBucketN11A3Shard021.records
theorem valid21_22 : RecordsValid 11 3 records21_22 :=
  StrongPackedBucketN11A3Shard021.valid

abbrev records22_23 : List Blob := StrongPackedBucketN11A3Shard022.records
theorem valid22_23 : RecordsValid 11 3 records22_23 :=
  StrongPackedBucketN11A3Shard022.valid

def records21_23 : List Blob :=
  records21_22 ++ records22_23
theorem valid21_23 : RecordsValid 11 3 records21_23 :=
  valid21_22.append valid22_23

abbrev records23_24 : List Blob := StrongPackedBucketN11A3Shard023.records
theorem valid23_24 : RecordsValid 11 3 records23_24 :=
  StrongPackedBucketN11A3Shard023.valid

abbrev records24_25 : List Blob := StrongPackedBucketN11A3Shard024.records
theorem valid24_25 : RecordsValid 11 3 records24_25 :=
  StrongPackedBucketN11A3Shard024.valid

def records23_25 : List Blob :=
  records23_24 ++ records24_25
theorem valid23_25 : RecordsValid 11 3 records23_25 :=
  valid23_24.append valid24_25

def records21_25 : List Blob :=
  records21_23 ++ records23_25
theorem valid21_25 : RecordsValid 11 3 records21_25 :=
  valid21_23.append valid23_25

abbrev records25_26 : List Blob := StrongPackedBucketN11A3Shard025.records
theorem valid25_26 : RecordsValid 11 3 records25_26 :=
  StrongPackedBucketN11A3Shard025.valid

abbrev records26_27 : List Blob := StrongPackedBucketN11A3Shard026.records
theorem valid26_27 : RecordsValid 11 3 records26_27 :=
  StrongPackedBucketN11A3Shard026.valid

def records25_27 : List Blob :=
  records25_26 ++ records26_27
theorem valid25_27 : RecordsValid 11 3 records25_27 :=
  valid25_26.append valid26_27

abbrev records27_28 : List Blob := StrongPackedBucketN11A3Shard027.records
theorem valid27_28 : RecordsValid 11 3 records27_28 :=
  StrongPackedBucketN11A3Shard027.valid

abbrev records28_29 : List Blob := StrongPackedBucketN11A3Shard028.records
theorem valid28_29 : RecordsValid 11 3 records28_29 :=
  StrongPackedBucketN11A3Shard028.valid

def records27_29 : List Blob :=
  records27_28 ++ records28_29
theorem valid27_29 : RecordsValid 11 3 records27_29 :=
  valid27_28.append valid28_29

def records25_29 : List Blob :=
  records25_27 ++ records27_29
theorem valid25_29 : RecordsValid 11 3 records25_29 :=
  valid25_27.append valid27_29

def records21_29 : List Blob :=
  records21_25 ++ records25_29
theorem valid21_29 : RecordsValid 11 3 records21_29 :=
  valid21_25.append valid25_29

def records14_29 : List Blob :=
  records14_21 ++ records21_29
theorem valid14_29 : RecordsValid 11 3 records14_29 :=
  valid14_21.append valid21_29

def records0_29 : List Blob :=
  records0_14 ++ records14_29
theorem valid0_29 : RecordsValid 11 3 records0_29 :=
  valid0_14.append valid14_29

abbrev records : List Blob := records0_29
theorem valid : RecordsValid 11 3 records := valid0_29

theorem strongPacking_of_mem {blob : Blob} (hblob : blob ∈ records) :
    ∃ entry : BucketCertificate.Entry 11, decode 11 blob = some entry ∧
      HasStrongFractionalPacking (graphOfBits entry.1) (((3 : ℕ) : ℝ)) :=
  valid.strongPacking_of_mem PackingCert.pairIndexValid_11 hblob

end Erdos76.CertificateChecker.Certificates.StrongPackedBucketN11A3

