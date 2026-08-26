/-
Copyright 2026 The Lean-Proofs Authors.
Licensed under the Apache License, Version 2.0.
-/
import ErdosProblems.Erdos76.Certificates.StrongPackedBucketN12A2AlignedShard000
import ErdosProblems.Erdos76.Certificates.StrongPackedBucketN12A2AlignedShard001
import ErdosProblems.Erdos76.Certificates.StrongPackedBucketN12A2AlignedShard002
import ErdosProblems.Erdos76.Certificates.StrongPackedBucketN12A2AlignedShard003
import ErdosProblems.Erdos76.Certificates.StrongPackedBucketN12A2AlignedShard004
import ErdosProblems.Erdos76.Certificates.StrongPackedBucketN12A2AlignedShard005
import ErdosProblems.Erdos76.Certificates.StrongPackedBucketN12A2AlignedShard006
import ErdosProblems.Erdos76.Certificates.StrongPackedBucketN12A2AlignedShard007
import ErdosProblems.Erdos76.Certificates.StrongPackedBucketN12A2AlignedShard008
import ErdosProblems.Erdos76.Certificates.StrongPackedBucketN12A2AlignedShard009
import ErdosProblems.Erdos76.Certificates.StrongPackedBucketN12A2AlignedShard010
import ErdosProblems.Erdos76.Certificates.StrongPackedBucketN12A2AlignedShard011
import ErdosProblems.Erdos76.Certificates.StrongPackedBucketN12A2AlignedShard012
import ErdosProblems.Erdos76.Certificates.StrongPackedBucketN12A2AlignedShard013
import ErdosProblems.Erdos76.Certificates.StrongPackedBucketN12A2AlignedShard014
import ErdosProblems.Erdos76.Certificates.StrongPackedBucketN12A2AlignedShard015
import ErdosProblems.Erdos76.Certificates.StrongPackedBucketN12A2AlignedShard016
import ErdosProblems.Erdos76.Certificates.StrongPackedBucketN12A2AlignedShard017
import ErdosProblems.Erdos76.Certificates.StrongPackedBucketN12A2AlignedShard018
import ErdosProblems.Erdos76.Certificates.StrongPackedBucketN12A2AlignedShard019
import ErdosProblems.Erdos76.Certificates.StrongPackedBucketN12A2AlignedShard020
import ErdosProblems.Erdos76.Certificates.StrongPackedBucketN12A2AlignedShard021
import ErdosProblems.Erdos76.Certificates.StrongPackedBucketN12A2AlignedShard022
import ErdosProblems.Erdos76.Certificates.StrongPackedBucketN12A2AlignedShard023
import ErdosProblems.Erdos76.Certificates.StrongPackedBucketN12A2AlignedShard024
import ErdosProblems.Erdos76.Certificates.StrongPackedBucketN12A2AlignedShard025
import ErdosProblems.Erdos76.Certificates.StrongPackedBucketN12A2AlignedShard026
import ErdosProblems.Erdos76.Certificates.StrongPackedBucketN12A2AlignedShard027
import ErdosProblems.Erdos76.Certificates.StrongPackedBucketN12A2AlignedShard028
import ErdosProblems.Erdos76.Certificates.StrongPackedBucketN12A2AlignedShard029
import ErdosProblems.Erdos76.Certificates.StrongPackedBucketN12A2AlignedShard030
import ErdosProblems.Erdos76.Certificates.StrongPackedBucketN12A2AlignedShard031
import ErdosProblems.Erdos76.Certificates.StrongPackedBucketN12A2AlignedShard032

/-! Balanced alignment aggregate for all 4191 n=12, a=2 records. -/
namespace Erdos76.CertificateChecker.Certificates.StrongPackedBucketN12A2Aligned

open PackedBucketCertificate

abbrev missing0_1 : List (BitVec (edgeCount 12)) :=
  StrongPackedBucketN12A2AlignedShard000.missing
def records0_1 : List Blob := StrongPackedBucketN12A2AlignedShard000.records
theorem aligned0_1 :
    AlignedValid 12 2 missing0_1 records0_1 :=
  StrongPackedBucketN12A2AlignedShard000.aligned

abbrev missing1_2 : List (BitVec (edgeCount 12)) :=
  StrongPackedBucketN12A2AlignedShard001.missing
def records1_2 : List Blob := StrongPackedBucketN12A2AlignedShard001.records
theorem aligned1_2 :
    AlignedValid 12 2 missing1_2 records1_2 :=
  StrongPackedBucketN12A2AlignedShard001.aligned

def missing0_2 : List (BitVec (edgeCount 12)) :=
  missing0_1 ++ missing1_2
def records0_2 : List Blob :=
  records0_1 ++ records1_2
theorem aligned0_2 :
    AlignedValid 12 2 missing0_2 records0_2 :=
  aligned0_1.append aligned1_2

abbrev missing2_3 : List (BitVec (edgeCount 12)) :=
  StrongPackedBucketN12A2AlignedShard002.missing
def records2_3 : List Blob := StrongPackedBucketN12A2AlignedShard002.records
theorem aligned2_3 :
    AlignedValid 12 2 missing2_3 records2_3 :=
  StrongPackedBucketN12A2AlignedShard002.aligned

abbrev missing3_4 : List (BitVec (edgeCount 12)) :=
  StrongPackedBucketN12A2AlignedShard003.missing
def records3_4 : List Blob := StrongPackedBucketN12A2AlignedShard003.records
theorem aligned3_4 :
    AlignedValid 12 2 missing3_4 records3_4 :=
  StrongPackedBucketN12A2AlignedShard003.aligned

def missing2_4 : List (BitVec (edgeCount 12)) :=
  missing2_3 ++ missing3_4
def records2_4 : List Blob :=
  records2_3 ++ records3_4
theorem aligned2_4 :
    AlignedValid 12 2 missing2_4 records2_4 :=
  aligned2_3.append aligned3_4

def missing0_4 : List (BitVec (edgeCount 12)) :=
  missing0_2 ++ missing2_4
def records0_4 : List Blob :=
  records0_2 ++ records2_4
theorem aligned0_4 :
    AlignedValid 12 2 missing0_4 records0_4 :=
  aligned0_2.append aligned2_4

abbrev missing4_5 : List (BitVec (edgeCount 12)) :=
  StrongPackedBucketN12A2AlignedShard004.missing
def records4_5 : List Blob := StrongPackedBucketN12A2AlignedShard004.records
theorem aligned4_5 :
    AlignedValid 12 2 missing4_5 records4_5 :=
  StrongPackedBucketN12A2AlignedShard004.aligned

abbrev missing5_6 : List (BitVec (edgeCount 12)) :=
  StrongPackedBucketN12A2AlignedShard005.missing
def records5_6 : List Blob := StrongPackedBucketN12A2AlignedShard005.records
theorem aligned5_6 :
    AlignedValid 12 2 missing5_6 records5_6 :=
  StrongPackedBucketN12A2AlignedShard005.aligned

def missing4_6 : List (BitVec (edgeCount 12)) :=
  missing4_5 ++ missing5_6
def records4_6 : List Blob :=
  records4_5 ++ records5_6
theorem aligned4_6 :
    AlignedValid 12 2 missing4_6 records4_6 :=
  aligned4_5.append aligned5_6

abbrev missing6_7 : List (BitVec (edgeCount 12)) :=
  StrongPackedBucketN12A2AlignedShard006.missing
def records6_7 : List Blob := StrongPackedBucketN12A2AlignedShard006.records
theorem aligned6_7 :
    AlignedValid 12 2 missing6_7 records6_7 :=
  StrongPackedBucketN12A2AlignedShard006.aligned

abbrev missing7_8 : List (BitVec (edgeCount 12)) :=
  StrongPackedBucketN12A2AlignedShard007.missing
def records7_8 : List Blob := StrongPackedBucketN12A2AlignedShard007.records
theorem aligned7_8 :
    AlignedValid 12 2 missing7_8 records7_8 :=
  StrongPackedBucketN12A2AlignedShard007.aligned

def missing6_8 : List (BitVec (edgeCount 12)) :=
  missing6_7 ++ missing7_8
def records6_8 : List Blob :=
  records6_7 ++ records7_8
theorem aligned6_8 :
    AlignedValid 12 2 missing6_8 records6_8 :=
  aligned6_7.append aligned7_8

def missing4_8 : List (BitVec (edgeCount 12)) :=
  missing4_6 ++ missing6_8
def records4_8 : List Blob :=
  records4_6 ++ records6_8
theorem aligned4_8 :
    AlignedValid 12 2 missing4_8 records4_8 :=
  aligned4_6.append aligned6_8

def missing0_8 : List (BitVec (edgeCount 12)) :=
  missing0_4 ++ missing4_8
def records0_8 : List Blob :=
  records0_4 ++ records4_8
theorem aligned0_8 :
    AlignedValid 12 2 missing0_8 records0_8 :=
  aligned0_4.append aligned4_8

abbrev missing8_9 : List (BitVec (edgeCount 12)) :=
  StrongPackedBucketN12A2AlignedShard008.missing
def records8_9 : List Blob := StrongPackedBucketN12A2AlignedShard008.records
theorem aligned8_9 :
    AlignedValid 12 2 missing8_9 records8_9 :=
  StrongPackedBucketN12A2AlignedShard008.aligned

abbrev missing9_10 : List (BitVec (edgeCount 12)) :=
  StrongPackedBucketN12A2AlignedShard009.missing
def records9_10 : List Blob := StrongPackedBucketN12A2AlignedShard009.records
theorem aligned9_10 :
    AlignedValid 12 2 missing9_10 records9_10 :=
  StrongPackedBucketN12A2AlignedShard009.aligned

def missing8_10 : List (BitVec (edgeCount 12)) :=
  missing8_9 ++ missing9_10
def records8_10 : List Blob :=
  records8_9 ++ records9_10
theorem aligned8_10 :
    AlignedValid 12 2 missing8_10 records8_10 :=
  aligned8_9.append aligned9_10

abbrev missing10_11 : List (BitVec (edgeCount 12)) :=
  StrongPackedBucketN12A2AlignedShard010.missing
def records10_11 : List Blob := StrongPackedBucketN12A2AlignedShard010.records
theorem aligned10_11 :
    AlignedValid 12 2 missing10_11 records10_11 :=
  StrongPackedBucketN12A2AlignedShard010.aligned

abbrev missing11_12 : List (BitVec (edgeCount 12)) :=
  StrongPackedBucketN12A2AlignedShard011.missing
def records11_12 : List Blob := StrongPackedBucketN12A2AlignedShard011.records
theorem aligned11_12 :
    AlignedValid 12 2 missing11_12 records11_12 :=
  StrongPackedBucketN12A2AlignedShard011.aligned

def missing10_12 : List (BitVec (edgeCount 12)) :=
  missing10_11 ++ missing11_12
def records10_12 : List Blob :=
  records10_11 ++ records11_12
theorem aligned10_12 :
    AlignedValid 12 2 missing10_12 records10_12 :=
  aligned10_11.append aligned11_12

def missing8_12 : List (BitVec (edgeCount 12)) :=
  missing8_10 ++ missing10_12
def records8_12 : List Blob :=
  records8_10 ++ records10_12
theorem aligned8_12 :
    AlignedValid 12 2 missing8_12 records8_12 :=
  aligned8_10.append aligned10_12

abbrev missing12_13 : List (BitVec (edgeCount 12)) :=
  StrongPackedBucketN12A2AlignedShard012.missing
def records12_13 : List Blob := StrongPackedBucketN12A2AlignedShard012.records
theorem aligned12_13 :
    AlignedValid 12 2 missing12_13 records12_13 :=
  StrongPackedBucketN12A2AlignedShard012.aligned

abbrev missing13_14 : List (BitVec (edgeCount 12)) :=
  StrongPackedBucketN12A2AlignedShard013.missing
def records13_14 : List Blob := StrongPackedBucketN12A2AlignedShard013.records
theorem aligned13_14 :
    AlignedValid 12 2 missing13_14 records13_14 :=
  StrongPackedBucketN12A2AlignedShard013.aligned

def missing12_14 : List (BitVec (edgeCount 12)) :=
  missing12_13 ++ missing13_14
def records12_14 : List Blob :=
  records12_13 ++ records13_14
theorem aligned12_14 :
    AlignedValid 12 2 missing12_14 records12_14 :=
  aligned12_13.append aligned13_14

abbrev missing14_15 : List (BitVec (edgeCount 12)) :=
  StrongPackedBucketN12A2AlignedShard014.missing
def records14_15 : List Blob := StrongPackedBucketN12A2AlignedShard014.records
theorem aligned14_15 :
    AlignedValid 12 2 missing14_15 records14_15 :=
  StrongPackedBucketN12A2AlignedShard014.aligned

abbrev missing15_16 : List (BitVec (edgeCount 12)) :=
  StrongPackedBucketN12A2AlignedShard015.missing
def records15_16 : List Blob := StrongPackedBucketN12A2AlignedShard015.records
theorem aligned15_16 :
    AlignedValid 12 2 missing15_16 records15_16 :=
  StrongPackedBucketN12A2AlignedShard015.aligned

def missing14_16 : List (BitVec (edgeCount 12)) :=
  missing14_15 ++ missing15_16
def records14_16 : List Blob :=
  records14_15 ++ records15_16
theorem aligned14_16 :
    AlignedValid 12 2 missing14_16 records14_16 :=
  aligned14_15.append aligned15_16

def missing12_16 : List (BitVec (edgeCount 12)) :=
  missing12_14 ++ missing14_16
def records12_16 : List Blob :=
  records12_14 ++ records14_16
theorem aligned12_16 :
    AlignedValid 12 2 missing12_16 records12_16 :=
  aligned12_14.append aligned14_16

def missing8_16 : List (BitVec (edgeCount 12)) :=
  missing8_12 ++ missing12_16
def records8_16 : List Blob :=
  records8_12 ++ records12_16
theorem aligned8_16 :
    AlignedValid 12 2 missing8_16 records8_16 :=
  aligned8_12.append aligned12_16

def missing0_16 : List (BitVec (edgeCount 12)) :=
  missing0_8 ++ missing8_16
def records0_16 : List Blob :=
  records0_8 ++ records8_16
theorem aligned0_16 :
    AlignedValid 12 2 missing0_16 records0_16 :=
  aligned0_8.append aligned8_16

abbrev missing16_17 : List (BitVec (edgeCount 12)) :=
  StrongPackedBucketN12A2AlignedShard016.missing
def records16_17 : List Blob := StrongPackedBucketN12A2AlignedShard016.records
theorem aligned16_17 :
    AlignedValid 12 2 missing16_17 records16_17 :=
  StrongPackedBucketN12A2AlignedShard016.aligned

abbrev missing17_18 : List (BitVec (edgeCount 12)) :=
  StrongPackedBucketN12A2AlignedShard017.missing
def records17_18 : List Blob := StrongPackedBucketN12A2AlignedShard017.records
theorem aligned17_18 :
    AlignedValid 12 2 missing17_18 records17_18 :=
  StrongPackedBucketN12A2AlignedShard017.aligned

def missing16_18 : List (BitVec (edgeCount 12)) :=
  missing16_17 ++ missing17_18
def records16_18 : List Blob :=
  records16_17 ++ records17_18
theorem aligned16_18 :
    AlignedValid 12 2 missing16_18 records16_18 :=
  aligned16_17.append aligned17_18

abbrev missing18_19 : List (BitVec (edgeCount 12)) :=
  StrongPackedBucketN12A2AlignedShard018.missing
def records18_19 : List Blob := StrongPackedBucketN12A2AlignedShard018.records
theorem aligned18_19 :
    AlignedValid 12 2 missing18_19 records18_19 :=
  StrongPackedBucketN12A2AlignedShard018.aligned

abbrev missing19_20 : List (BitVec (edgeCount 12)) :=
  StrongPackedBucketN12A2AlignedShard019.missing
def records19_20 : List Blob := StrongPackedBucketN12A2AlignedShard019.records
theorem aligned19_20 :
    AlignedValid 12 2 missing19_20 records19_20 :=
  StrongPackedBucketN12A2AlignedShard019.aligned

def missing18_20 : List (BitVec (edgeCount 12)) :=
  missing18_19 ++ missing19_20
def records18_20 : List Blob :=
  records18_19 ++ records19_20
theorem aligned18_20 :
    AlignedValid 12 2 missing18_20 records18_20 :=
  aligned18_19.append aligned19_20

def missing16_20 : List (BitVec (edgeCount 12)) :=
  missing16_18 ++ missing18_20
def records16_20 : List Blob :=
  records16_18 ++ records18_20
theorem aligned16_20 :
    AlignedValid 12 2 missing16_20 records16_20 :=
  aligned16_18.append aligned18_20

abbrev missing20_21 : List (BitVec (edgeCount 12)) :=
  StrongPackedBucketN12A2AlignedShard020.missing
def records20_21 : List Blob := StrongPackedBucketN12A2AlignedShard020.records
theorem aligned20_21 :
    AlignedValid 12 2 missing20_21 records20_21 :=
  StrongPackedBucketN12A2AlignedShard020.aligned

abbrev missing21_22 : List (BitVec (edgeCount 12)) :=
  StrongPackedBucketN12A2AlignedShard021.missing
def records21_22 : List Blob := StrongPackedBucketN12A2AlignedShard021.records
theorem aligned21_22 :
    AlignedValid 12 2 missing21_22 records21_22 :=
  StrongPackedBucketN12A2AlignedShard021.aligned

def missing20_22 : List (BitVec (edgeCount 12)) :=
  missing20_21 ++ missing21_22
def records20_22 : List Blob :=
  records20_21 ++ records21_22
theorem aligned20_22 :
    AlignedValid 12 2 missing20_22 records20_22 :=
  aligned20_21.append aligned21_22

abbrev missing22_23 : List (BitVec (edgeCount 12)) :=
  StrongPackedBucketN12A2AlignedShard022.missing
def records22_23 : List Blob := StrongPackedBucketN12A2AlignedShard022.records
theorem aligned22_23 :
    AlignedValid 12 2 missing22_23 records22_23 :=
  StrongPackedBucketN12A2AlignedShard022.aligned

abbrev missing23_24 : List (BitVec (edgeCount 12)) :=
  StrongPackedBucketN12A2AlignedShard023.missing
def records23_24 : List Blob := StrongPackedBucketN12A2AlignedShard023.records
theorem aligned23_24 :
    AlignedValid 12 2 missing23_24 records23_24 :=
  StrongPackedBucketN12A2AlignedShard023.aligned

def missing22_24 : List (BitVec (edgeCount 12)) :=
  missing22_23 ++ missing23_24
def records22_24 : List Blob :=
  records22_23 ++ records23_24
theorem aligned22_24 :
    AlignedValid 12 2 missing22_24 records22_24 :=
  aligned22_23.append aligned23_24

def missing20_24 : List (BitVec (edgeCount 12)) :=
  missing20_22 ++ missing22_24
def records20_24 : List Blob :=
  records20_22 ++ records22_24
theorem aligned20_24 :
    AlignedValid 12 2 missing20_24 records20_24 :=
  aligned20_22.append aligned22_24

def missing16_24 : List (BitVec (edgeCount 12)) :=
  missing16_20 ++ missing20_24
def records16_24 : List Blob :=
  records16_20 ++ records20_24
theorem aligned16_24 :
    AlignedValid 12 2 missing16_24 records16_24 :=
  aligned16_20.append aligned20_24

abbrev missing24_25 : List (BitVec (edgeCount 12)) :=
  StrongPackedBucketN12A2AlignedShard024.missing
def records24_25 : List Blob := StrongPackedBucketN12A2AlignedShard024.records
theorem aligned24_25 :
    AlignedValid 12 2 missing24_25 records24_25 :=
  StrongPackedBucketN12A2AlignedShard024.aligned

abbrev missing25_26 : List (BitVec (edgeCount 12)) :=
  StrongPackedBucketN12A2AlignedShard025.missing
def records25_26 : List Blob := StrongPackedBucketN12A2AlignedShard025.records
theorem aligned25_26 :
    AlignedValid 12 2 missing25_26 records25_26 :=
  StrongPackedBucketN12A2AlignedShard025.aligned

def missing24_26 : List (BitVec (edgeCount 12)) :=
  missing24_25 ++ missing25_26
def records24_26 : List Blob :=
  records24_25 ++ records25_26
theorem aligned24_26 :
    AlignedValid 12 2 missing24_26 records24_26 :=
  aligned24_25.append aligned25_26

abbrev missing26_27 : List (BitVec (edgeCount 12)) :=
  StrongPackedBucketN12A2AlignedShard026.missing
def records26_27 : List Blob := StrongPackedBucketN12A2AlignedShard026.records
theorem aligned26_27 :
    AlignedValid 12 2 missing26_27 records26_27 :=
  StrongPackedBucketN12A2AlignedShard026.aligned

abbrev missing27_28 : List (BitVec (edgeCount 12)) :=
  StrongPackedBucketN12A2AlignedShard027.missing
def records27_28 : List Blob := StrongPackedBucketN12A2AlignedShard027.records
theorem aligned27_28 :
    AlignedValid 12 2 missing27_28 records27_28 :=
  StrongPackedBucketN12A2AlignedShard027.aligned

def missing26_28 : List (BitVec (edgeCount 12)) :=
  missing26_27 ++ missing27_28
def records26_28 : List Blob :=
  records26_27 ++ records27_28
theorem aligned26_28 :
    AlignedValid 12 2 missing26_28 records26_28 :=
  aligned26_27.append aligned27_28

def missing24_28 : List (BitVec (edgeCount 12)) :=
  missing24_26 ++ missing26_28
def records24_28 : List Blob :=
  records24_26 ++ records26_28
theorem aligned24_28 :
    AlignedValid 12 2 missing24_28 records24_28 :=
  aligned24_26.append aligned26_28

abbrev missing28_29 : List (BitVec (edgeCount 12)) :=
  StrongPackedBucketN12A2AlignedShard028.missing
def records28_29 : List Blob := StrongPackedBucketN12A2AlignedShard028.records
theorem aligned28_29 :
    AlignedValid 12 2 missing28_29 records28_29 :=
  StrongPackedBucketN12A2AlignedShard028.aligned

abbrev missing29_30 : List (BitVec (edgeCount 12)) :=
  StrongPackedBucketN12A2AlignedShard029.missing
def records29_30 : List Blob := StrongPackedBucketN12A2AlignedShard029.records
theorem aligned29_30 :
    AlignedValid 12 2 missing29_30 records29_30 :=
  StrongPackedBucketN12A2AlignedShard029.aligned

def missing28_30 : List (BitVec (edgeCount 12)) :=
  missing28_29 ++ missing29_30
def records28_30 : List Blob :=
  records28_29 ++ records29_30
theorem aligned28_30 :
    AlignedValid 12 2 missing28_30 records28_30 :=
  aligned28_29.append aligned29_30

abbrev missing30_31 : List (BitVec (edgeCount 12)) :=
  StrongPackedBucketN12A2AlignedShard030.missing
def records30_31 : List Blob := StrongPackedBucketN12A2AlignedShard030.records
theorem aligned30_31 :
    AlignedValid 12 2 missing30_31 records30_31 :=
  StrongPackedBucketN12A2AlignedShard030.aligned

abbrev missing31_32 : List (BitVec (edgeCount 12)) :=
  StrongPackedBucketN12A2AlignedShard031.missing
def records31_32 : List Blob := StrongPackedBucketN12A2AlignedShard031.records
theorem aligned31_32 :
    AlignedValid 12 2 missing31_32 records31_32 :=
  StrongPackedBucketN12A2AlignedShard031.aligned

abbrev missing32_33 : List (BitVec (edgeCount 12)) :=
  StrongPackedBucketN12A2AlignedShard032.missing
def records32_33 : List Blob := StrongPackedBucketN12A2AlignedShard032.records
theorem aligned32_33 :
    AlignedValid 12 2 missing32_33 records32_33 :=
  StrongPackedBucketN12A2AlignedShard032.aligned

def missing31_33 : List (BitVec (edgeCount 12)) :=
  missing31_32 ++ missing32_33
def records31_33 : List Blob :=
  records31_32 ++ records32_33
theorem aligned31_33 :
    AlignedValid 12 2 missing31_33 records31_33 :=
  aligned31_32.append aligned32_33

def missing30_33 : List (BitVec (edgeCount 12)) :=
  missing30_31 ++ missing31_33
def records30_33 : List Blob :=
  records30_31 ++ records31_33
theorem aligned30_33 :
    AlignedValid 12 2 missing30_33 records30_33 :=
  aligned30_31.append aligned31_33

def missing28_33 : List (BitVec (edgeCount 12)) :=
  missing28_30 ++ missing30_33
def records28_33 : List Blob :=
  records28_30 ++ records30_33
theorem aligned28_33 :
    AlignedValid 12 2 missing28_33 records28_33 :=
  aligned28_30.append aligned30_33

def missing24_33 : List (BitVec (edgeCount 12)) :=
  missing24_28 ++ missing28_33
def records24_33 : List Blob :=
  records24_28 ++ records28_33
theorem aligned24_33 :
    AlignedValid 12 2 missing24_33 records24_33 :=
  aligned24_28.append aligned28_33

def missing16_33 : List (BitVec (edgeCount 12)) :=
  missing16_24 ++ missing24_33
def records16_33 : List Blob :=
  records16_24 ++ records24_33
theorem aligned16_33 :
    AlignedValid 12 2 missing16_33 records16_33 :=
  aligned16_24.append aligned24_33

def missing0_33 : List (BitVec (edgeCount 12)) :=
  missing0_16 ++ missing16_33
def records0_33 : List Blob :=
  records0_16 ++ records16_33
theorem aligned0_33 :
    AlignedValid 12 2 missing0_33 records0_33 :=
  aligned0_16.append aligned16_33

abbrev missing : List (BitVec (edgeCount 12)) := missing0_33
def records : List Blob := records0_33
theorem aligned : AlignedValid 12 2 missing records := aligned0_33

end Erdos76.CertificateChecker.Certificates.StrongPackedBucketN12A2Aligned
