/-
Copyright 2026 The Lean-Proofs Authors.
Licensed under the Apache License, Version 2.0.
-/
import ErdosProblems.Erdos76.Certificates.StrongPackedBucketN11A3AlignedShard000
import ErdosProblems.Erdos76.Certificates.StrongPackedBucketN11A3AlignedShard001
import ErdosProblems.Erdos76.Certificates.StrongPackedBucketN11A3AlignedShard002
import ErdosProblems.Erdos76.Certificates.StrongPackedBucketN11A3AlignedShard003
import ErdosProblems.Erdos76.Certificates.StrongPackedBucketN11A3AlignedShard004
import ErdosProblems.Erdos76.Certificates.StrongPackedBucketN11A3AlignedShard005
import ErdosProblems.Erdos76.Certificates.StrongPackedBucketN11A3AlignedShard006
import ErdosProblems.Erdos76.Certificates.StrongPackedBucketN11A3AlignedShard007
import ErdosProblems.Erdos76.Certificates.StrongPackedBucketN11A3AlignedShard008
import ErdosProblems.Erdos76.Certificates.StrongPackedBucketN11A3AlignedShard009
import ErdosProblems.Erdos76.Certificates.StrongPackedBucketN11A3AlignedShard010
import ErdosProblems.Erdos76.Certificates.StrongPackedBucketN11A3AlignedShard011
import ErdosProblems.Erdos76.Certificates.StrongPackedBucketN11A3AlignedShard012
import ErdosProblems.Erdos76.Certificates.StrongPackedBucketN11A3AlignedShard013
import ErdosProblems.Erdos76.Certificates.StrongPackedBucketN11A3AlignedShard014
import ErdosProblems.Erdos76.Certificates.StrongPackedBucketN11A3AlignedShard015
import ErdosProblems.Erdos76.Certificates.StrongPackedBucketN11A3AlignedShard016
import ErdosProblems.Erdos76.Certificates.StrongPackedBucketN11A3AlignedShard017
import ErdosProblems.Erdos76.Certificates.StrongPackedBucketN11A3AlignedShard018
import ErdosProblems.Erdos76.Certificates.StrongPackedBucketN11A3AlignedShard019
import ErdosProblems.Erdos76.Certificates.StrongPackedBucketN11A3AlignedShard020
import ErdosProblems.Erdos76.Certificates.StrongPackedBucketN11A3AlignedShard021
import ErdosProblems.Erdos76.Certificates.StrongPackedBucketN11A3AlignedShard022
import ErdosProblems.Erdos76.Certificates.StrongPackedBucketN11A3AlignedShard023
import ErdosProblems.Erdos76.Certificates.StrongPackedBucketN11A3AlignedShard024
import ErdosProblems.Erdos76.Certificates.StrongPackedBucketN11A3AlignedShard025
import ErdosProblems.Erdos76.Certificates.StrongPackedBucketN11A3AlignedShard026
import ErdosProblems.Erdos76.Certificates.StrongPackedBucketN11A3AlignedShard027
import ErdosProblems.Erdos76.Certificates.StrongPackedBucketN11A3AlignedShard028

/-! Balanced decode-only alignment aggregate for n=11, a=3. -/
namespace Erdos76.CertificateChecker.Certificates.StrongPackedBucketN11A3Aligned

open PackedBucketCertificate

abbrev missing0_1 : List (BitVec (edgeCount 11)) :=
  StrongPackedBucketN11A3AlignedShard000.missing
abbrev records0_1 : List Blob := StrongPackedBucketN11A3AlignedShard000.records
theorem aligned0_1 :
    AlignedValid 11 3 missing0_1 records0_1 :=
  StrongPackedBucketN11A3AlignedShard000.aligned

abbrev missing1_2 : List (BitVec (edgeCount 11)) :=
  StrongPackedBucketN11A3AlignedShard001.missing
abbrev records1_2 : List Blob := StrongPackedBucketN11A3AlignedShard001.records
theorem aligned1_2 :
    AlignedValid 11 3 missing1_2 records1_2 :=
  StrongPackedBucketN11A3AlignedShard001.aligned

abbrev missing2_3 : List (BitVec (edgeCount 11)) :=
  StrongPackedBucketN11A3AlignedShard002.missing
abbrev records2_3 : List Blob := StrongPackedBucketN11A3AlignedShard002.records
theorem aligned2_3 :
    AlignedValid 11 3 missing2_3 records2_3 :=
  StrongPackedBucketN11A3AlignedShard002.aligned

def missing1_3 : List (BitVec (edgeCount 11)) :=
  missing1_2 ++ missing2_3
abbrev records1_3 : List Blob :=
  records1_2 ++ records2_3
theorem aligned1_3 :
    AlignedValid 11 3 missing1_3 records1_3 :=
  aligned1_2.append aligned2_3

def missing0_3 : List (BitVec (edgeCount 11)) :=
  missing0_1 ++ missing1_3
abbrev records0_3 : List Blob :=
  records0_1 ++ records1_3
theorem aligned0_3 :
    AlignedValid 11 3 missing0_3 records0_3 :=
  aligned0_1.append aligned1_3

abbrev missing3_4 : List (BitVec (edgeCount 11)) :=
  StrongPackedBucketN11A3AlignedShard003.missing
abbrev records3_4 : List Blob := StrongPackedBucketN11A3AlignedShard003.records
theorem aligned3_4 :
    AlignedValid 11 3 missing3_4 records3_4 :=
  StrongPackedBucketN11A3AlignedShard003.aligned

abbrev missing4_5 : List (BitVec (edgeCount 11)) :=
  StrongPackedBucketN11A3AlignedShard004.missing
abbrev records4_5 : List Blob := StrongPackedBucketN11A3AlignedShard004.records
theorem aligned4_5 :
    AlignedValid 11 3 missing4_5 records4_5 :=
  StrongPackedBucketN11A3AlignedShard004.aligned

def missing3_5 : List (BitVec (edgeCount 11)) :=
  missing3_4 ++ missing4_5
abbrev records3_5 : List Blob :=
  records3_4 ++ records4_5
theorem aligned3_5 :
    AlignedValid 11 3 missing3_5 records3_5 :=
  aligned3_4.append aligned4_5

abbrev missing5_6 : List (BitVec (edgeCount 11)) :=
  StrongPackedBucketN11A3AlignedShard005.missing
abbrev records5_6 : List Blob := StrongPackedBucketN11A3AlignedShard005.records
theorem aligned5_6 :
    AlignedValid 11 3 missing5_6 records5_6 :=
  StrongPackedBucketN11A3AlignedShard005.aligned

abbrev missing6_7 : List (BitVec (edgeCount 11)) :=
  StrongPackedBucketN11A3AlignedShard006.missing
abbrev records6_7 : List Blob := StrongPackedBucketN11A3AlignedShard006.records
theorem aligned6_7 :
    AlignedValid 11 3 missing6_7 records6_7 :=
  StrongPackedBucketN11A3AlignedShard006.aligned

def missing5_7 : List (BitVec (edgeCount 11)) :=
  missing5_6 ++ missing6_7
abbrev records5_7 : List Blob :=
  records5_6 ++ records6_7
theorem aligned5_7 :
    AlignedValid 11 3 missing5_7 records5_7 :=
  aligned5_6.append aligned6_7

def missing3_7 : List (BitVec (edgeCount 11)) :=
  missing3_5 ++ missing5_7
abbrev records3_7 : List Blob :=
  records3_5 ++ records5_7
theorem aligned3_7 :
    AlignedValid 11 3 missing3_7 records3_7 :=
  aligned3_5.append aligned5_7

def missing0_7 : List (BitVec (edgeCount 11)) :=
  missing0_3 ++ missing3_7
abbrev records0_7 : List Blob :=
  records0_3 ++ records3_7
theorem aligned0_7 :
    AlignedValid 11 3 missing0_7 records0_7 :=
  aligned0_3.append aligned3_7

abbrev missing7_8 : List (BitVec (edgeCount 11)) :=
  StrongPackedBucketN11A3AlignedShard007.missing
abbrev records7_8 : List Blob := StrongPackedBucketN11A3AlignedShard007.records
theorem aligned7_8 :
    AlignedValid 11 3 missing7_8 records7_8 :=
  StrongPackedBucketN11A3AlignedShard007.aligned

abbrev missing8_9 : List (BitVec (edgeCount 11)) :=
  StrongPackedBucketN11A3AlignedShard008.missing
abbrev records8_9 : List Blob := StrongPackedBucketN11A3AlignedShard008.records
theorem aligned8_9 :
    AlignedValid 11 3 missing8_9 records8_9 :=
  StrongPackedBucketN11A3AlignedShard008.aligned

abbrev missing9_10 : List (BitVec (edgeCount 11)) :=
  StrongPackedBucketN11A3AlignedShard009.missing
abbrev records9_10 : List Blob := StrongPackedBucketN11A3AlignedShard009.records
theorem aligned9_10 :
    AlignedValid 11 3 missing9_10 records9_10 :=
  StrongPackedBucketN11A3AlignedShard009.aligned

def missing8_10 : List (BitVec (edgeCount 11)) :=
  missing8_9 ++ missing9_10
abbrev records8_10 : List Blob :=
  records8_9 ++ records9_10
theorem aligned8_10 :
    AlignedValid 11 3 missing8_10 records8_10 :=
  aligned8_9.append aligned9_10

def missing7_10 : List (BitVec (edgeCount 11)) :=
  missing7_8 ++ missing8_10
abbrev records7_10 : List Blob :=
  records7_8 ++ records8_10
theorem aligned7_10 :
    AlignedValid 11 3 missing7_10 records7_10 :=
  aligned7_8.append aligned8_10

abbrev missing10_11 : List (BitVec (edgeCount 11)) :=
  StrongPackedBucketN11A3AlignedShard010.missing
abbrev records10_11 : List Blob := StrongPackedBucketN11A3AlignedShard010.records
theorem aligned10_11 :
    AlignedValid 11 3 missing10_11 records10_11 :=
  StrongPackedBucketN11A3AlignedShard010.aligned

abbrev missing11_12 : List (BitVec (edgeCount 11)) :=
  StrongPackedBucketN11A3AlignedShard011.missing
abbrev records11_12 : List Blob := StrongPackedBucketN11A3AlignedShard011.records
theorem aligned11_12 :
    AlignedValid 11 3 missing11_12 records11_12 :=
  StrongPackedBucketN11A3AlignedShard011.aligned

def missing10_12 : List (BitVec (edgeCount 11)) :=
  missing10_11 ++ missing11_12
abbrev records10_12 : List Blob :=
  records10_11 ++ records11_12
theorem aligned10_12 :
    AlignedValid 11 3 missing10_12 records10_12 :=
  aligned10_11.append aligned11_12

abbrev missing12_13 : List (BitVec (edgeCount 11)) :=
  StrongPackedBucketN11A3AlignedShard012.missing
abbrev records12_13 : List Blob := StrongPackedBucketN11A3AlignedShard012.records
theorem aligned12_13 :
    AlignedValid 11 3 missing12_13 records12_13 :=
  StrongPackedBucketN11A3AlignedShard012.aligned

abbrev missing13_14 : List (BitVec (edgeCount 11)) :=
  StrongPackedBucketN11A3AlignedShard013.missing
abbrev records13_14 : List Blob := StrongPackedBucketN11A3AlignedShard013.records
theorem aligned13_14 :
    AlignedValid 11 3 missing13_14 records13_14 :=
  StrongPackedBucketN11A3AlignedShard013.aligned

def missing12_14 : List (BitVec (edgeCount 11)) :=
  missing12_13 ++ missing13_14
abbrev records12_14 : List Blob :=
  records12_13 ++ records13_14
theorem aligned12_14 :
    AlignedValid 11 3 missing12_14 records12_14 :=
  aligned12_13.append aligned13_14

def missing10_14 : List (BitVec (edgeCount 11)) :=
  missing10_12 ++ missing12_14
abbrev records10_14 : List Blob :=
  records10_12 ++ records12_14
theorem aligned10_14 :
    AlignedValid 11 3 missing10_14 records10_14 :=
  aligned10_12.append aligned12_14

def missing7_14 : List (BitVec (edgeCount 11)) :=
  missing7_10 ++ missing10_14
abbrev records7_14 : List Blob :=
  records7_10 ++ records10_14
theorem aligned7_14 :
    AlignedValid 11 3 missing7_14 records7_14 :=
  aligned7_10.append aligned10_14

def missing0_14 : List (BitVec (edgeCount 11)) :=
  missing0_7 ++ missing7_14
abbrev records0_14 : List Blob :=
  records0_7 ++ records7_14
theorem aligned0_14 :
    AlignedValid 11 3 missing0_14 records0_14 :=
  aligned0_7.append aligned7_14

abbrev missing14_15 : List (BitVec (edgeCount 11)) :=
  StrongPackedBucketN11A3AlignedShard014.missing
abbrev records14_15 : List Blob := StrongPackedBucketN11A3AlignedShard014.records
theorem aligned14_15 :
    AlignedValid 11 3 missing14_15 records14_15 :=
  StrongPackedBucketN11A3AlignedShard014.aligned

abbrev missing15_16 : List (BitVec (edgeCount 11)) :=
  StrongPackedBucketN11A3AlignedShard015.missing
abbrev records15_16 : List Blob := StrongPackedBucketN11A3AlignedShard015.records
theorem aligned15_16 :
    AlignedValid 11 3 missing15_16 records15_16 :=
  StrongPackedBucketN11A3AlignedShard015.aligned

abbrev missing16_17 : List (BitVec (edgeCount 11)) :=
  StrongPackedBucketN11A3AlignedShard016.missing
abbrev records16_17 : List Blob := StrongPackedBucketN11A3AlignedShard016.records
theorem aligned16_17 :
    AlignedValid 11 3 missing16_17 records16_17 :=
  StrongPackedBucketN11A3AlignedShard016.aligned

def missing15_17 : List (BitVec (edgeCount 11)) :=
  missing15_16 ++ missing16_17
abbrev records15_17 : List Blob :=
  records15_16 ++ records16_17
theorem aligned15_17 :
    AlignedValid 11 3 missing15_17 records15_17 :=
  aligned15_16.append aligned16_17

def missing14_17 : List (BitVec (edgeCount 11)) :=
  missing14_15 ++ missing15_17
abbrev records14_17 : List Blob :=
  records14_15 ++ records15_17
theorem aligned14_17 :
    AlignedValid 11 3 missing14_17 records14_17 :=
  aligned14_15.append aligned15_17

abbrev missing17_18 : List (BitVec (edgeCount 11)) :=
  StrongPackedBucketN11A3AlignedShard017.missing
abbrev records17_18 : List Blob := StrongPackedBucketN11A3AlignedShard017.records
theorem aligned17_18 :
    AlignedValid 11 3 missing17_18 records17_18 :=
  StrongPackedBucketN11A3AlignedShard017.aligned

abbrev missing18_19 : List (BitVec (edgeCount 11)) :=
  StrongPackedBucketN11A3AlignedShard018.missing
abbrev records18_19 : List Blob := StrongPackedBucketN11A3AlignedShard018.records
theorem aligned18_19 :
    AlignedValid 11 3 missing18_19 records18_19 :=
  StrongPackedBucketN11A3AlignedShard018.aligned

def missing17_19 : List (BitVec (edgeCount 11)) :=
  missing17_18 ++ missing18_19
abbrev records17_19 : List Blob :=
  records17_18 ++ records18_19
theorem aligned17_19 :
    AlignedValid 11 3 missing17_19 records17_19 :=
  aligned17_18.append aligned18_19

abbrev missing19_20 : List (BitVec (edgeCount 11)) :=
  StrongPackedBucketN11A3AlignedShard019.missing
abbrev records19_20 : List Blob := StrongPackedBucketN11A3AlignedShard019.records
theorem aligned19_20 :
    AlignedValid 11 3 missing19_20 records19_20 :=
  StrongPackedBucketN11A3AlignedShard019.aligned

abbrev missing20_21 : List (BitVec (edgeCount 11)) :=
  StrongPackedBucketN11A3AlignedShard020.missing
abbrev records20_21 : List Blob := StrongPackedBucketN11A3AlignedShard020.records
theorem aligned20_21 :
    AlignedValid 11 3 missing20_21 records20_21 :=
  StrongPackedBucketN11A3AlignedShard020.aligned

def missing19_21 : List (BitVec (edgeCount 11)) :=
  missing19_20 ++ missing20_21
abbrev records19_21 : List Blob :=
  records19_20 ++ records20_21
theorem aligned19_21 :
    AlignedValid 11 3 missing19_21 records19_21 :=
  aligned19_20.append aligned20_21

def missing17_21 : List (BitVec (edgeCount 11)) :=
  missing17_19 ++ missing19_21
abbrev records17_21 : List Blob :=
  records17_19 ++ records19_21
theorem aligned17_21 :
    AlignedValid 11 3 missing17_21 records17_21 :=
  aligned17_19.append aligned19_21

def missing14_21 : List (BitVec (edgeCount 11)) :=
  missing14_17 ++ missing17_21
abbrev records14_21 : List Blob :=
  records14_17 ++ records17_21
theorem aligned14_21 :
    AlignedValid 11 3 missing14_21 records14_21 :=
  aligned14_17.append aligned17_21

abbrev missing21_22 : List (BitVec (edgeCount 11)) :=
  StrongPackedBucketN11A3AlignedShard021.missing
abbrev records21_22 : List Blob := StrongPackedBucketN11A3AlignedShard021.records
theorem aligned21_22 :
    AlignedValid 11 3 missing21_22 records21_22 :=
  StrongPackedBucketN11A3AlignedShard021.aligned

abbrev missing22_23 : List (BitVec (edgeCount 11)) :=
  StrongPackedBucketN11A3AlignedShard022.missing
abbrev records22_23 : List Blob := StrongPackedBucketN11A3AlignedShard022.records
theorem aligned22_23 :
    AlignedValid 11 3 missing22_23 records22_23 :=
  StrongPackedBucketN11A3AlignedShard022.aligned

def missing21_23 : List (BitVec (edgeCount 11)) :=
  missing21_22 ++ missing22_23
abbrev records21_23 : List Blob :=
  records21_22 ++ records22_23
theorem aligned21_23 :
    AlignedValid 11 3 missing21_23 records21_23 :=
  aligned21_22.append aligned22_23

abbrev missing23_24 : List (BitVec (edgeCount 11)) :=
  StrongPackedBucketN11A3AlignedShard023.missing
abbrev records23_24 : List Blob := StrongPackedBucketN11A3AlignedShard023.records
theorem aligned23_24 :
    AlignedValid 11 3 missing23_24 records23_24 :=
  StrongPackedBucketN11A3AlignedShard023.aligned

abbrev missing24_25 : List (BitVec (edgeCount 11)) :=
  StrongPackedBucketN11A3AlignedShard024.missing
abbrev records24_25 : List Blob := StrongPackedBucketN11A3AlignedShard024.records
theorem aligned24_25 :
    AlignedValid 11 3 missing24_25 records24_25 :=
  StrongPackedBucketN11A3AlignedShard024.aligned

def missing23_25 : List (BitVec (edgeCount 11)) :=
  missing23_24 ++ missing24_25
abbrev records23_25 : List Blob :=
  records23_24 ++ records24_25
theorem aligned23_25 :
    AlignedValid 11 3 missing23_25 records23_25 :=
  aligned23_24.append aligned24_25

def missing21_25 : List (BitVec (edgeCount 11)) :=
  missing21_23 ++ missing23_25
abbrev records21_25 : List Blob :=
  records21_23 ++ records23_25
theorem aligned21_25 :
    AlignedValid 11 3 missing21_25 records21_25 :=
  aligned21_23.append aligned23_25

abbrev missing25_26 : List (BitVec (edgeCount 11)) :=
  StrongPackedBucketN11A3AlignedShard025.missing
abbrev records25_26 : List Blob := StrongPackedBucketN11A3AlignedShard025.records
theorem aligned25_26 :
    AlignedValid 11 3 missing25_26 records25_26 :=
  StrongPackedBucketN11A3AlignedShard025.aligned

abbrev missing26_27 : List (BitVec (edgeCount 11)) :=
  StrongPackedBucketN11A3AlignedShard026.missing
abbrev records26_27 : List Blob := StrongPackedBucketN11A3AlignedShard026.records
theorem aligned26_27 :
    AlignedValid 11 3 missing26_27 records26_27 :=
  StrongPackedBucketN11A3AlignedShard026.aligned

def missing25_27 : List (BitVec (edgeCount 11)) :=
  missing25_26 ++ missing26_27
abbrev records25_27 : List Blob :=
  records25_26 ++ records26_27
theorem aligned25_27 :
    AlignedValid 11 3 missing25_27 records25_27 :=
  aligned25_26.append aligned26_27

abbrev missing27_28 : List (BitVec (edgeCount 11)) :=
  StrongPackedBucketN11A3AlignedShard027.missing
abbrev records27_28 : List Blob := StrongPackedBucketN11A3AlignedShard027.records
theorem aligned27_28 :
    AlignedValid 11 3 missing27_28 records27_28 :=
  StrongPackedBucketN11A3AlignedShard027.aligned

abbrev missing28_29 : List (BitVec (edgeCount 11)) :=
  StrongPackedBucketN11A3AlignedShard028.missing
abbrev records28_29 : List Blob := StrongPackedBucketN11A3AlignedShard028.records
theorem aligned28_29 :
    AlignedValid 11 3 missing28_29 records28_29 :=
  StrongPackedBucketN11A3AlignedShard028.aligned

def missing27_29 : List (BitVec (edgeCount 11)) :=
  missing27_28 ++ missing28_29
abbrev records27_29 : List Blob :=
  records27_28 ++ records28_29
theorem aligned27_29 :
    AlignedValid 11 3 missing27_29 records27_29 :=
  aligned27_28.append aligned28_29

def missing25_29 : List (BitVec (edgeCount 11)) :=
  missing25_27 ++ missing27_29
abbrev records25_29 : List Blob :=
  records25_27 ++ records27_29
theorem aligned25_29 :
    AlignedValid 11 3 missing25_29 records25_29 :=
  aligned25_27.append aligned27_29

def missing21_29 : List (BitVec (edgeCount 11)) :=
  missing21_25 ++ missing25_29
abbrev records21_29 : List Blob :=
  records21_25 ++ records25_29
theorem aligned21_29 :
    AlignedValid 11 3 missing21_29 records21_29 :=
  aligned21_25.append aligned25_29

def missing14_29 : List (BitVec (edgeCount 11)) :=
  missing14_21 ++ missing21_29
abbrev records14_29 : List Blob :=
  records14_21 ++ records21_29
theorem aligned14_29 :
    AlignedValid 11 3 missing14_29 records14_29 :=
  aligned14_21.append aligned21_29

def missing0_29 : List (BitVec (edgeCount 11)) :=
  missing0_14 ++ missing14_29
abbrev records0_29 : List Blob :=
  records0_14 ++ records14_29
theorem aligned0_29 :
    AlignedValid 11 3 missing0_29 records0_29 :=
  aligned0_14.append aligned14_29

abbrev missing : List (BitVec (edgeCount 11)) := missing0_29
abbrev records : List Blob := records0_29
theorem aligned : AlignedValid 11 3 missing records :=
  aligned0_29

end Erdos76.CertificateChecker.Certificates.StrongPackedBucketN11A3Aligned

