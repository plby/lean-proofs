/-
Copyright 2026 The Lean-Proofs Authors.
Licensed under the Apache License, Version 2.0.
-/
import ErdosProblems.Erdos76.Certificates.PairIndexN12
import ErdosProblems.Erdos76.Certificates.StrongPackedBucketN12A2Shard000
import ErdosProblems.Erdos76.Certificates.StrongPackedBucketN12A2Shard001
import ErdosProblems.Erdos76.Certificates.StrongPackedBucketN12A2Shard002
import ErdosProblems.Erdos76.Certificates.StrongPackedBucketN12A2Shard003
import ErdosProblems.Erdos76.Certificates.StrongPackedBucketN12A2Shard004
import ErdosProblems.Erdos76.Certificates.StrongPackedBucketN12A2Shard005
import ErdosProblems.Erdos76.Certificates.StrongPackedBucketN12A2Shard006
import ErdosProblems.Erdos76.Certificates.StrongPackedBucketN12A2Shard007
import ErdosProblems.Erdos76.Certificates.StrongPackedBucketN12A2Shard008
import ErdosProblems.Erdos76.Certificates.StrongPackedBucketN12A2Shard009
import ErdosProblems.Erdos76.Certificates.StrongPackedBucketN12A2Shard010
import ErdosProblems.Erdos76.Certificates.StrongPackedBucketN12A2Shard011
import ErdosProblems.Erdos76.Certificates.StrongPackedBucketN12A2Shard012
import ErdosProblems.Erdos76.Certificates.StrongPackedBucketN12A2Shard013
import ErdosProblems.Erdos76.Certificates.StrongPackedBucketN12A2Shard014
import ErdosProblems.Erdos76.Certificates.StrongPackedBucketN12A2Shard015
import ErdosProblems.Erdos76.Certificates.StrongPackedBucketN12A2Shard016
import ErdosProblems.Erdos76.Certificates.StrongPackedBucketN12A2Shard017
import ErdosProblems.Erdos76.Certificates.StrongPackedBucketN12A2Shard018
import ErdosProblems.Erdos76.Certificates.StrongPackedBucketN12A2Shard019
import ErdosProblems.Erdos76.Certificates.StrongPackedBucketN12A2Shard020
import ErdosProblems.Erdos76.Certificates.StrongPackedBucketN12A2Shard021
import ErdosProblems.Erdos76.Certificates.StrongPackedBucketN12A2Shard022
import ErdosProblems.Erdos76.Certificates.StrongPackedBucketN12A2Shard023
import ErdosProblems.Erdos76.Certificates.StrongPackedBucketN12A2Shard024
import ErdosProblems.Erdos76.Certificates.StrongPackedBucketN12A2Shard025
import ErdosProblems.Erdos76.Certificates.StrongPackedBucketN12A2Shard026
import ErdosProblems.Erdos76.Certificates.StrongPackedBucketN12A2Shard027
import ErdosProblems.Erdos76.Certificates.StrongPackedBucketN12A2Shard028
import ErdosProblems.Erdos76.Certificates.StrongPackedBucketN12A2Shard029
import ErdosProblems.Erdos76.Certificates.StrongPackedBucketN12A2Shard030
import ErdosProblems.Erdos76.Certificates.StrongPackedBucketN12A2Shard031
import ErdosProblems.Erdos76.Certificates.StrongPackedBucketN12A2Shard032

/-! Production endpoint for all 4191 exact n=12, a=2 strong certificates. -/
namespace Erdos76.CertificateChecker.Certificates.StrongPackedBucketN12A2

open PackedBucketCertificate

abbrev records0_1 : List Blob := StrongPackedBucketN12A2Shard000.records
theorem valid0_1 : RecordsValid 12 2 records0_1 :=
  StrongPackedBucketN12A2Shard000.valid

abbrev records1_2 : List Blob := StrongPackedBucketN12A2Shard001.records
theorem valid1_2 : RecordsValid 12 2 records1_2 :=
  StrongPackedBucketN12A2Shard001.valid

def records0_2 : List Blob :=
  records0_1 ++ records1_2
theorem valid0_2 : RecordsValid 12 2 records0_2 :=
  valid0_1.append valid1_2

abbrev records2_3 : List Blob := StrongPackedBucketN12A2Shard002.records
theorem valid2_3 : RecordsValid 12 2 records2_3 :=
  StrongPackedBucketN12A2Shard002.valid

abbrev records3_4 : List Blob := StrongPackedBucketN12A2Shard003.records
theorem valid3_4 : RecordsValid 12 2 records3_4 :=
  StrongPackedBucketN12A2Shard003.valid

def records2_4 : List Blob :=
  records2_3 ++ records3_4
theorem valid2_4 : RecordsValid 12 2 records2_4 :=
  valid2_3.append valid3_4

def records0_4 : List Blob :=
  records0_2 ++ records2_4
theorem valid0_4 : RecordsValid 12 2 records0_4 :=
  valid0_2.append valid2_4

abbrev records4_5 : List Blob := StrongPackedBucketN12A2Shard004.records
theorem valid4_5 : RecordsValid 12 2 records4_5 :=
  StrongPackedBucketN12A2Shard004.valid

abbrev records5_6 : List Blob := StrongPackedBucketN12A2Shard005.records
theorem valid5_6 : RecordsValid 12 2 records5_6 :=
  StrongPackedBucketN12A2Shard005.valid

def records4_6 : List Blob :=
  records4_5 ++ records5_6
theorem valid4_6 : RecordsValid 12 2 records4_6 :=
  valid4_5.append valid5_6

abbrev records6_7 : List Blob := StrongPackedBucketN12A2Shard006.records
theorem valid6_7 : RecordsValid 12 2 records6_7 :=
  StrongPackedBucketN12A2Shard006.valid

abbrev records7_8 : List Blob := StrongPackedBucketN12A2Shard007.records
theorem valid7_8 : RecordsValid 12 2 records7_8 :=
  StrongPackedBucketN12A2Shard007.valid

def records6_8 : List Blob :=
  records6_7 ++ records7_8
theorem valid6_8 : RecordsValid 12 2 records6_8 :=
  valid6_7.append valid7_8

def records4_8 : List Blob :=
  records4_6 ++ records6_8
theorem valid4_8 : RecordsValid 12 2 records4_8 :=
  valid4_6.append valid6_8

def records0_8 : List Blob :=
  records0_4 ++ records4_8
theorem valid0_8 : RecordsValid 12 2 records0_8 :=
  valid0_4.append valid4_8

abbrev records8_9 : List Blob := StrongPackedBucketN12A2Shard008.records
theorem valid8_9 : RecordsValid 12 2 records8_9 :=
  StrongPackedBucketN12A2Shard008.valid

abbrev records9_10 : List Blob := StrongPackedBucketN12A2Shard009.records
theorem valid9_10 : RecordsValid 12 2 records9_10 :=
  StrongPackedBucketN12A2Shard009.valid

def records8_10 : List Blob :=
  records8_9 ++ records9_10
theorem valid8_10 : RecordsValid 12 2 records8_10 :=
  valid8_9.append valid9_10

abbrev records10_11 : List Blob := StrongPackedBucketN12A2Shard010.records
theorem valid10_11 : RecordsValid 12 2 records10_11 :=
  StrongPackedBucketN12A2Shard010.valid

abbrev records11_12 : List Blob := StrongPackedBucketN12A2Shard011.records
theorem valid11_12 : RecordsValid 12 2 records11_12 :=
  StrongPackedBucketN12A2Shard011.valid

def records10_12 : List Blob :=
  records10_11 ++ records11_12
theorem valid10_12 : RecordsValid 12 2 records10_12 :=
  valid10_11.append valid11_12

def records8_12 : List Blob :=
  records8_10 ++ records10_12
theorem valid8_12 : RecordsValid 12 2 records8_12 :=
  valid8_10.append valid10_12

abbrev records12_13 : List Blob := StrongPackedBucketN12A2Shard012.records
theorem valid12_13 : RecordsValid 12 2 records12_13 :=
  StrongPackedBucketN12A2Shard012.valid

abbrev records13_14 : List Blob := StrongPackedBucketN12A2Shard013.records
theorem valid13_14 : RecordsValid 12 2 records13_14 :=
  StrongPackedBucketN12A2Shard013.valid

def records12_14 : List Blob :=
  records12_13 ++ records13_14
theorem valid12_14 : RecordsValid 12 2 records12_14 :=
  valid12_13.append valid13_14

abbrev records14_15 : List Blob := StrongPackedBucketN12A2Shard014.records
theorem valid14_15 : RecordsValid 12 2 records14_15 :=
  StrongPackedBucketN12A2Shard014.valid

abbrev records15_16 : List Blob := StrongPackedBucketN12A2Shard015.records
theorem valid15_16 : RecordsValid 12 2 records15_16 :=
  StrongPackedBucketN12A2Shard015.valid

def records14_16 : List Blob :=
  records14_15 ++ records15_16
theorem valid14_16 : RecordsValid 12 2 records14_16 :=
  valid14_15.append valid15_16

def records12_16 : List Blob :=
  records12_14 ++ records14_16
theorem valid12_16 : RecordsValid 12 2 records12_16 :=
  valid12_14.append valid14_16

def records8_16 : List Blob :=
  records8_12 ++ records12_16
theorem valid8_16 : RecordsValid 12 2 records8_16 :=
  valid8_12.append valid12_16

def records0_16 : List Blob :=
  records0_8 ++ records8_16
theorem valid0_16 : RecordsValid 12 2 records0_16 :=
  valid0_8.append valid8_16

abbrev records16_17 : List Blob := StrongPackedBucketN12A2Shard016.records
theorem valid16_17 : RecordsValid 12 2 records16_17 :=
  StrongPackedBucketN12A2Shard016.valid

abbrev records17_18 : List Blob := StrongPackedBucketN12A2Shard017.records
theorem valid17_18 : RecordsValid 12 2 records17_18 :=
  StrongPackedBucketN12A2Shard017.valid

def records16_18 : List Blob :=
  records16_17 ++ records17_18
theorem valid16_18 : RecordsValid 12 2 records16_18 :=
  valid16_17.append valid17_18

abbrev records18_19 : List Blob := StrongPackedBucketN12A2Shard018.records
theorem valid18_19 : RecordsValid 12 2 records18_19 :=
  StrongPackedBucketN12A2Shard018.valid

abbrev records19_20 : List Blob := StrongPackedBucketN12A2Shard019.records
theorem valid19_20 : RecordsValid 12 2 records19_20 :=
  StrongPackedBucketN12A2Shard019.valid

def records18_20 : List Blob :=
  records18_19 ++ records19_20
theorem valid18_20 : RecordsValid 12 2 records18_20 :=
  valid18_19.append valid19_20

def records16_20 : List Blob :=
  records16_18 ++ records18_20
theorem valid16_20 : RecordsValid 12 2 records16_20 :=
  valid16_18.append valid18_20

abbrev records20_21 : List Blob := StrongPackedBucketN12A2Shard020.records
theorem valid20_21 : RecordsValid 12 2 records20_21 :=
  StrongPackedBucketN12A2Shard020.valid

abbrev records21_22 : List Blob := StrongPackedBucketN12A2Shard021.records
theorem valid21_22 : RecordsValid 12 2 records21_22 :=
  StrongPackedBucketN12A2Shard021.valid

def records20_22 : List Blob :=
  records20_21 ++ records21_22
theorem valid20_22 : RecordsValid 12 2 records20_22 :=
  valid20_21.append valid21_22

abbrev records22_23 : List Blob := StrongPackedBucketN12A2Shard022.records
theorem valid22_23 : RecordsValid 12 2 records22_23 :=
  StrongPackedBucketN12A2Shard022.valid

abbrev records23_24 : List Blob := StrongPackedBucketN12A2Shard023.records
theorem valid23_24 : RecordsValid 12 2 records23_24 :=
  StrongPackedBucketN12A2Shard023.valid

def records22_24 : List Blob :=
  records22_23 ++ records23_24
theorem valid22_24 : RecordsValid 12 2 records22_24 :=
  valid22_23.append valid23_24

def records20_24 : List Blob :=
  records20_22 ++ records22_24
theorem valid20_24 : RecordsValid 12 2 records20_24 :=
  valid20_22.append valid22_24

def records16_24 : List Blob :=
  records16_20 ++ records20_24
theorem valid16_24 : RecordsValid 12 2 records16_24 :=
  valid16_20.append valid20_24

abbrev records24_25 : List Blob := StrongPackedBucketN12A2Shard024.records
theorem valid24_25 : RecordsValid 12 2 records24_25 :=
  StrongPackedBucketN12A2Shard024.valid

abbrev records25_26 : List Blob := StrongPackedBucketN12A2Shard025.records
theorem valid25_26 : RecordsValid 12 2 records25_26 :=
  StrongPackedBucketN12A2Shard025.valid

def records24_26 : List Blob :=
  records24_25 ++ records25_26
theorem valid24_26 : RecordsValid 12 2 records24_26 :=
  valid24_25.append valid25_26

abbrev records26_27 : List Blob := StrongPackedBucketN12A2Shard026.records
theorem valid26_27 : RecordsValid 12 2 records26_27 :=
  StrongPackedBucketN12A2Shard026.valid

abbrev records27_28 : List Blob := StrongPackedBucketN12A2Shard027.records
theorem valid27_28 : RecordsValid 12 2 records27_28 :=
  StrongPackedBucketN12A2Shard027.valid

def records26_28 : List Blob :=
  records26_27 ++ records27_28
theorem valid26_28 : RecordsValid 12 2 records26_28 :=
  valid26_27.append valid27_28

def records24_28 : List Blob :=
  records24_26 ++ records26_28
theorem valid24_28 : RecordsValid 12 2 records24_28 :=
  valid24_26.append valid26_28

abbrev records28_29 : List Blob := StrongPackedBucketN12A2Shard028.records
theorem valid28_29 : RecordsValid 12 2 records28_29 :=
  StrongPackedBucketN12A2Shard028.valid

abbrev records29_30 : List Blob := StrongPackedBucketN12A2Shard029.records
theorem valid29_30 : RecordsValid 12 2 records29_30 :=
  StrongPackedBucketN12A2Shard029.valid

def records28_30 : List Blob :=
  records28_29 ++ records29_30
theorem valid28_30 : RecordsValid 12 2 records28_30 :=
  valid28_29.append valid29_30

abbrev records30_31 : List Blob := StrongPackedBucketN12A2Shard030.records
theorem valid30_31 : RecordsValid 12 2 records30_31 :=
  StrongPackedBucketN12A2Shard030.valid

abbrev records31_32 : List Blob := StrongPackedBucketN12A2Shard031.records
theorem valid31_32 : RecordsValid 12 2 records31_32 :=
  StrongPackedBucketN12A2Shard031.valid

abbrev records32_33 : List Blob := StrongPackedBucketN12A2Shard032.records
theorem valid32_33 : RecordsValid 12 2 records32_33 :=
  StrongPackedBucketN12A2Shard032.valid

def records31_33 : List Blob :=
  records31_32 ++ records32_33
theorem valid31_33 : RecordsValid 12 2 records31_33 :=
  valid31_32.append valid32_33

def records30_33 : List Blob :=
  records30_31 ++ records31_33
theorem valid30_33 : RecordsValid 12 2 records30_33 :=
  valid30_31.append valid31_33

def records28_33 : List Blob :=
  records28_30 ++ records30_33
theorem valid28_33 : RecordsValid 12 2 records28_33 :=
  valid28_30.append valid30_33

def records24_33 : List Blob :=
  records24_28 ++ records28_33
theorem valid24_33 : RecordsValid 12 2 records24_33 :=
  valid24_28.append valid28_33

def records16_33 : List Blob :=
  records16_24 ++ records24_33
theorem valid16_33 : RecordsValid 12 2 records16_33 :=
  valid16_24.append valid24_33

def records0_33 : List Blob :=
  records0_16 ++ records16_33
theorem valid0_33 : RecordsValid 12 2 records0_33 :=
  valid0_16.append valid16_33

abbrev records : List Blob := records0_33
theorem valid : RecordsValid 12 2 records := valid0_33

theorem strongPacking_of_mem {blob : Blob} (hblob : blob ∈ records) :
    ∃ entry : BucketCertificate.Entry 12, decode 12 blob = some entry ∧
      HasStrongFractionalPacking (graphOfBits entry.1) ((2 : ℕ) : ℝ) :=
  valid.strongPacking_of_mem PackingCert.pairIndexValid_12 hblob

end Erdos76.CertificateChecker.Certificates.StrongPackedBucketN12A2
