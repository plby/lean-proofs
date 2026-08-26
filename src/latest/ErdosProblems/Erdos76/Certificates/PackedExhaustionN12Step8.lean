/-
Copyright 2026 The Lean-Proofs Authors.
Licensed under the Apache License, Version 2.0.
-/
import ErdosProblems.Erdos76.Certificates.PackedExhaustionN12Step8Shard000
import ErdosProblems.Erdos76.Certificates.PackedExhaustionN12Step8Shard001
import ErdosProblems.Erdos76.Certificates.PackedExhaustionN12Step8Shard002
import ErdosProblems.Erdos76.Certificates.PackedExhaustionN12Step8Shard003
import ErdosProblems.Erdos76.Certificates.PackedExhaustionN12Step8Shard004
import ErdosProblems.Erdos76.Certificates.PackedExhaustionN12Step8Shard005
import ErdosProblems.Erdos76.Certificates.PackedExhaustionN12Step8Shard006
import ErdosProblems.Erdos76.Certificates.PackedExhaustionN12Step8Shard007
import ErdosProblems.Erdos76.Certificates.PackedExhaustionN12Step8Shard008
import ErdosProblems.Erdos76.Certificates.PackedExhaustionN12Step8Shard009
import ErdosProblems.Erdos76.Certificates.PackedExhaustionN12Step8Shard010
import ErdosProblems.Erdos76.Certificates.PackedExhaustionN12Step8Shard011
import ErdosProblems.Erdos76.Certificates.PackedExhaustionN12Step8Shard012
import ErdosProblems.Erdos76.Certificates.PackedExhaustionN12Step8Shard013
import ErdosProblems.Erdos76.Certificates.PackedExhaustionN12Step8Shard014
import ErdosProblems.Erdos76.Certificates.PackedExhaustionN12Step8Shard015
import ErdosProblems.Erdos76.Certificates.PackedExhaustionN12Step8Shard016
import ErdosProblems.Erdos76.Certificates.PackedExhaustionN12Step8Shard017
import ErdosProblems.Erdos76.Certificates.PackedExhaustionN12Step8Shard018
import ErdosProblems.Erdos76.Certificates.PackedExhaustionN12Step8Shard019
import ErdosProblems.Erdos76.Certificates.PackedExhaustionN12Step8Shard020
import ErdosProblems.Erdos76.Certificates.PackedExhaustionN12Step8Shard021
import ErdosProblems.Erdos76.Certificates.PackedExhaustionN12Step8Shard022
import ErdosProblems.Erdos76.Certificates.PackedExhaustionN12Step8Shard023
import ErdosProblems.Erdos76.Certificates.PackedExhaustionN12Step8Shard024
import ErdosProblems.Erdos76.Certificates.PackedExhaustionN12Step8Shard025
import ErdosProblems.Erdos76.Certificates.PackedExhaustionN12Step8Shard026
import ErdosProblems.Erdos76.Certificates.PackedExhaustionN12Step8Shard027
import ErdosProblems.Erdos76.Certificates.PackedExhaustionN12Step8Shard028
import ErdosProblems.Erdos76.Certificates.PackedExhaustionN12Step8Shard029
import ErdosProblems.Erdos76.Certificates.PackedExhaustionN12Step8Shard030
import ErdosProblems.Erdos76.Certificates.PackedExhaustionN12Step8Shard031
import ErdosProblems.Erdos76.Certificates.PackedExhaustionN12Step8Shard032
import ErdosProblems.Erdos76.Certificates.PackedExhaustionN12Step8Shard033
import ErdosProblems.Erdos76.Certificates.PackedExhaustionN12Step8Shard034
import ErdosProblems.Erdos76.Certificates.PackedExhaustionN12Step8Shard035
import ErdosProblems.Erdos76.Certificates.PackedExhaustionN12Step8Shard036
import ErdosProblems.Erdos76.Certificates.PackedExhaustionN12Step8Shard037
import ErdosProblems.Erdos76.Certificates.PackedExhaustionN12Step8Shard038
import ErdosProblems.Erdos76.Certificates.PackedExhaustionN12Step8Shard039
import ErdosProblems.Erdos76.Certificates.PackedExhaustionN12Step8Shard040
import ErdosProblems.Erdos76.Certificates.PackedExhaustionN12Step8Shard041
import ErdosProblems.Erdos76.Certificates.PackedExhaustionN12Step8Shard042
import ErdosProblems.Erdos76.Certificates.PackedExhaustionN12Step8Shard043
import ErdosProblems.Erdos76.Certificates.PackedExhaustionN12Step8Shard044
import ErdosProblems.Erdos76.Certificates.PackedExhaustionN12Step8Shard045
import ErdosProblems.Erdos76.Certificates.PackedExhaustionN12Step8Shard046
import ErdosProblems.Erdos76.Certificates.PackedExhaustionN12Step8Shard047
import ErdosProblems.Erdos76.Certificates.PackedExhaustionN12Step8Shard048
import ErdosProblems.Erdos76.Certificates.PackedExhaustionN12Step8Shard049
import ErdosProblems.Erdos76.Certificates.PackedExhaustionN12Step8Shard050
import ErdosProblems.Erdos76.Certificates.PackedExhaustionN12Step8Shard051
import ErdosProblems.Erdos76.Certificates.PackedExhaustionN12Step8Shard052
import ErdosProblems.Erdos76.Certificates.PackedExhaustionN12Step8Shard053
import ErdosProblems.Erdos76.Certificates.PackedExhaustionN12Step8Shard054
import ErdosProblems.Erdos76.Certificates.PackedExhaustionN12Step8Shard055
import ErdosProblems.Erdos76.Certificates.PackedExhaustionN12Step8Shard056
import ErdosProblems.Erdos76.Certificates.PackedExhaustionN12Step8Shard057
import ErdosProblems.Erdos76.Certificates.PackedExhaustionN12Step8Shard058
import ErdosProblems.Erdos76.Certificates.PackedExhaustionN12Step8Shard059
import ErdosProblems.Erdos76.Certificates.PackedExhaustionN12Step8Shard060

/-! Proof-only aggregate for the n=12 exhaustion step 8. -/
namespace Erdos76.CertificateExhaustion.Certificates.PackedExhaustionN12.Step8

open CertificateChecker
open CertificateChecker.PackedBucketCertificate
open Packed

abbrev rows0_1 : List Blob := PackedExhaustionN12Step8Shard000.rows
theorem rows0_1_length :
    rows0_1.length = 8 := PackedExhaustionN12Step8Shard000.rows_length
theorem valid0_1 :
    ClaimedRowsValidFrom PackingCert.pairIndexValid_12
      PackedExhaustionN12.level8 PackedExhaustionN12.level9 0 rows0_1 :=
  PackedExhaustionN12Step8Shard000.valid

abbrev rows1_2 : List Blob := PackedExhaustionN12Step8Shard001.rows
theorem rows1_2_length :
    rows1_2.length = 8 := PackedExhaustionN12Step8Shard001.rows_length
theorem valid1_2 :
    ClaimedRowsValidFrom PackingCert.pairIndexValid_12
      PackedExhaustionN12.level8 PackedExhaustionN12.level9 8 rows1_2 :=
  PackedExhaustionN12Step8Shard001.valid

abbrev rows2_3 : List Blob := PackedExhaustionN12Step8Shard002.rows
theorem rows2_3_length :
    rows2_3.length = 8 := PackedExhaustionN12Step8Shard002.rows_length
theorem valid2_3 :
    ClaimedRowsValidFrom PackingCert.pairIndexValid_12
      PackedExhaustionN12.level8 PackedExhaustionN12.level9 16 rows2_3 :=
  PackedExhaustionN12Step8Shard002.valid

def rows1_3 : List Blob :=
  rows1_2 ++ rows2_3
theorem rows1_3_length :
    rows1_3.length = 16 := by
  simp [rows1_3, rows1_2_length, rows2_3_length]
theorem valid1_3 :
    ClaimedRowsValidFrom PackingCert.pairIndexValid_12
      PackedExhaustionN12.level8 PackedExhaustionN12.level9 8 rows1_3 := by
  apply valid1_2.append
  simpa [rows1_2_length] using valid2_3

def rows0_3 : List Blob :=
  rows0_1 ++ rows1_3
theorem rows0_3_length :
    rows0_3.length = 24 := by
  simp [rows0_3, rows0_1_length, rows1_3_length]
theorem valid0_3 :
    ClaimedRowsValidFrom PackingCert.pairIndexValid_12
      PackedExhaustionN12.level8 PackedExhaustionN12.level9 0 rows0_3 := by
  apply valid0_1.append
  simpa [rows0_1_length] using valid1_3

abbrev rows3_4 : List Blob := PackedExhaustionN12Step8Shard003.rows
theorem rows3_4_length :
    rows3_4.length = 8 := PackedExhaustionN12Step8Shard003.rows_length
theorem valid3_4 :
    ClaimedRowsValidFrom PackingCert.pairIndexValid_12
      PackedExhaustionN12.level8 PackedExhaustionN12.level9 24 rows3_4 :=
  PackedExhaustionN12Step8Shard003.valid

abbrev rows4_5 : List Blob := PackedExhaustionN12Step8Shard004.rows
theorem rows4_5_length :
    rows4_5.length = 8 := PackedExhaustionN12Step8Shard004.rows_length
theorem valid4_5 :
    ClaimedRowsValidFrom PackingCert.pairIndexValid_12
      PackedExhaustionN12.level8 PackedExhaustionN12.level9 32 rows4_5 :=
  PackedExhaustionN12Step8Shard004.valid

def rows3_5 : List Blob :=
  rows3_4 ++ rows4_5
theorem rows3_5_length :
    rows3_5.length = 16 := by
  simp [rows3_5, rows3_4_length, rows4_5_length]
theorem valid3_5 :
    ClaimedRowsValidFrom PackingCert.pairIndexValid_12
      PackedExhaustionN12.level8 PackedExhaustionN12.level9 24 rows3_5 := by
  apply valid3_4.append
  simpa [rows3_4_length] using valid4_5

abbrev rows5_6 : List Blob := PackedExhaustionN12Step8Shard005.rows
theorem rows5_6_length :
    rows5_6.length = 8 := PackedExhaustionN12Step8Shard005.rows_length
theorem valid5_6 :
    ClaimedRowsValidFrom PackingCert.pairIndexValid_12
      PackedExhaustionN12.level8 PackedExhaustionN12.level9 40 rows5_6 :=
  PackedExhaustionN12Step8Shard005.valid

abbrev rows6_7 : List Blob := PackedExhaustionN12Step8Shard006.rows
theorem rows6_7_length :
    rows6_7.length = 8 := PackedExhaustionN12Step8Shard006.rows_length
theorem valid6_7 :
    ClaimedRowsValidFrom PackingCert.pairIndexValid_12
      PackedExhaustionN12.level8 PackedExhaustionN12.level9 48 rows6_7 :=
  PackedExhaustionN12Step8Shard006.valid

def rows5_7 : List Blob :=
  rows5_6 ++ rows6_7
theorem rows5_7_length :
    rows5_7.length = 16 := by
  simp [rows5_7, rows5_6_length, rows6_7_length]
theorem valid5_7 :
    ClaimedRowsValidFrom PackingCert.pairIndexValid_12
      PackedExhaustionN12.level8 PackedExhaustionN12.level9 40 rows5_7 := by
  apply valid5_6.append
  simpa [rows5_6_length] using valid6_7

def rows3_7 : List Blob :=
  rows3_5 ++ rows5_7
theorem rows3_7_length :
    rows3_7.length = 32 := by
  simp [rows3_7, rows3_5_length, rows5_7_length]
theorem valid3_7 :
    ClaimedRowsValidFrom PackingCert.pairIndexValid_12
      PackedExhaustionN12.level8 PackedExhaustionN12.level9 24 rows3_7 := by
  apply valid3_5.append
  simpa [rows3_5_length] using valid5_7

def rows0_7 : List Blob :=
  rows0_3 ++ rows3_7
theorem rows0_7_length :
    rows0_7.length = 56 := by
  simp [rows0_7, rows0_3_length, rows3_7_length]
theorem valid0_7 :
    ClaimedRowsValidFrom PackingCert.pairIndexValid_12
      PackedExhaustionN12.level8 PackedExhaustionN12.level9 0 rows0_7 := by
  apply valid0_3.append
  simpa [rows0_3_length] using valid3_7

abbrev rows7_8 : List Blob := PackedExhaustionN12Step8Shard007.rows
theorem rows7_8_length :
    rows7_8.length = 8 := PackedExhaustionN12Step8Shard007.rows_length
theorem valid7_8 :
    ClaimedRowsValidFrom PackingCert.pairIndexValid_12
      PackedExhaustionN12.level8 PackedExhaustionN12.level9 56 rows7_8 :=
  PackedExhaustionN12Step8Shard007.valid

abbrev rows8_9 : List Blob := PackedExhaustionN12Step8Shard008.rows
theorem rows8_9_length :
    rows8_9.length = 8 := PackedExhaustionN12Step8Shard008.rows_length
theorem valid8_9 :
    ClaimedRowsValidFrom PackingCert.pairIndexValid_12
      PackedExhaustionN12.level8 PackedExhaustionN12.level9 64 rows8_9 :=
  PackedExhaustionN12Step8Shard008.valid

def rows7_9 : List Blob :=
  rows7_8 ++ rows8_9
theorem rows7_9_length :
    rows7_9.length = 16 := by
  simp [rows7_9, rows7_8_length, rows8_9_length]
theorem valid7_9 :
    ClaimedRowsValidFrom PackingCert.pairIndexValid_12
      PackedExhaustionN12.level8 PackedExhaustionN12.level9 56 rows7_9 := by
  apply valid7_8.append
  simpa [rows7_8_length] using valid8_9

abbrev rows9_10 : List Blob := PackedExhaustionN12Step8Shard009.rows
theorem rows9_10_length :
    rows9_10.length = 8 := PackedExhaustionN12Step8Shard009.rows_length
theorem valid9_10 :
    ClaimedRowsValidFrom PackingCert.pairIndexValid_12
      PackedExhaustionN12.level8 PackedExhaustionN12.level9 72 rows9_10 :=
  PackedExhaustionN12Step8Shard009.valid

abbrev rows10_11 : List Blob := PackedExhaustionN12Step8Shard010.rows
theorem rows10_11_length :
    rows10_11.length = 8 := PackedExhaustionN12Step8Shard010.rows_length
theorem valid10_11 :
    ClaimedRowsValidFrom PackingCert.pairIndexValid_12
      PackedExhaustionN12.level8 PackedExhaustionN12.level9 80 rows10_11 :=
  PackedExhaustionN12Step8Shard010.valid

def rows9_11 : List Blob :=
  rows9_10 ++ rows10_11
theorem rows9_11_length :
    rows9_11.length = 16 := by
  simp [rows9_11, rows9_10_length, rows10_11_length]
theorem valid9_11 :
    ClaimedRowsValidFrom PackingCert.pairIndexValid_12
      PackedExhaustionN12.level8 PackedExhaustionN12.level9 72 rows9_11 := by
  apply valid9_10.append
  simpa [rows9_10_length] using valid10_11

def rows7_11 : List Blob :=
  rows7_9 ++ rows9_11
theorem rows7_11_length :
    rows7_11.length = 32 := by
  simp [rows7_11, rows7_9_length, rows9_11_length]
theorem valid7_11 :
    ClaimedRowsValidFrom PackingCert.pairIndexValid_12
      PackedExhaustionN12.level8 PackedExhaustionN12.level9 56 rows7_11 := by
  apply valid7_9.append
  simpa [rows7_9_length] using valid9_11

abbrev rows11_12 : List Blob := PackedExhaustionN12Step8Shard011.rows
theorem rows11_12_length :
    rows11_12.length = 8 := PackedExhaustionN12Step8Shard011.rows_length
theorem valid11_12 :
    ClaimedRowsValidFrom PackingCert.pairIndexValid_12
      PackedExhaustionN12.level8 PackedExhaustionN12.level9 88 rows11_12 :=
  PackedExhaustionN12Step8Shard011.valid

abbrev rows12_13 : List Blob := PackedExhaustionN12Step8Shard012.rows
theorem rows12_13_length :
    rows12_13.length = 8 := PackedExhaustionN12Step8Shard012.rows_length
theorem valid12_13 :
    ClaimedRowsValidFrom PackingCert.pairIndexValid_12
      PackedExhaustionN12.level8 PackedExhaustionN12.level9 96 rows12_13 :=
  PackedExhaustionN12Step8Shard012.valid

def rows11_13 : List Blob :=
  rows11_12 ++ rows12_13
theorem rows11_13_length :
    rows11_13.length = 16 := by
  simp [rows11_13, rows11_12_length, rows12_13_length]
theorem valid11_13 :
    ClaimedRowsValidFrom PackingCert.pairIndexValid_12
      PackedExhaustionN12.level8 PackedExhaustionN12.level9 88 rows11_13 := by
  apply valid11_12.append
  simpa [rows11_12_length] using valid12_13

abbrev rows13_14 : List Blob := PackedExhaustionN12Step8Shard013.rows
theorem rows13_14_length :
    rows13_14.length = 8 := PackedExhaustionN12Step8Shard013.rows_length
theorem valid13_14 :
    ClaimedRowsValidFrom PackingCert.pairIndexValid_12
      PackedExhaustionN12.level8 PackedExhaustionN12.level9 104 rows13_14 :=
  PackedExhaustionN12Step8Shard013.valid

abbrev rows14_15 : List Blob := PackedExhaustionN12Step8Shard014.rows
theorem rows14_15_length :
    rows14_15.length = 8 := PackedExhaustionN12Step8Shard014.rows_length
theorem valid14_15 :
    ClaimedRowsValidFrom PackingCert.pairIndexValid_12
      PackedExhaustionN12.level8 PackedExhaustionN12.level9 112 rows14_15 :=
  PackedExhaustionN12Step8Shard014.valid

def rows13_15 : List Blob :=
  rows13_14 ++ rows14_15
theorem rows13_15_length :
    rows13_15.length = 16 := by
  simp [rows13_15, rows13_14_length, rows14_15_length]
theorem valid13_15 :
    ClaimedRowsValidFrom PackingCert.pairIndexValid_12
      PackedExhaustionN12.level8 PackedExhaustionN12.level9 104 rows13_15 := by
  apply valid13_14.append
  simpa [rows13_14_length] using valid14_15

def rows11_15 : List Blob :=
  rows11_13 ++ rows13_15
theorem rows11_15_length :
    rows11_15.length = 32 := by
  simp [rows11_15, rows11_13_length, rows13_15_length]
theorem valid11_15 :
    ClaimedRowsValidFrom PackingCert.pairIndexValid_12
      PackedExhaustionN12.level8 PackedExhaustionN12.level9 88 rows11_15 := by
  apply valid11_13.append
  simpa [rows11_13_length] using valid13_15

def rows7_15 : List Blob :=
  rows7_11 ++ rows11_15
theorem rows7_15_length :
    rows7_15.length = 64 := by
  simp [rows7_15, rows7_11_length, rows11_15_length]
theorem valid7_15 :
    ClaimedRowsValidFrom PackingCert.pairIndexValid_12
      PackedExhaustionN12.level8 PackedExhaustionN12.level9 56 rows7_15 := by
  apply valid7_11.append
  simpa [rows7_11_length] using valid11_15

def rows0_15 : List Blob :=
  rows0_7 ++ rows7_15
theorem rows0_15_length :
    rows0_15.length = 120 := by
  simp [rows0_15, rows0_7_length, rows7_15_length]
theorem valid0_15 :
    ClaimedRowsValidFrom PackingCert.pairIndexValid_12
      PackedExhaustionN12.level8 PackedExhaustionN12.level9 0 rows0_15 := by
  apply valid0_7.append
  simpa [rows0_7_length] using valid7_15

abbrev rows15_16 : List Blob := PackedExhaustionN12Step8Shard015.rows
theorem rows15_16_length :
    rows15_16.length = 8 := PackedExhaustionN12Step8Shard015.rows_length
theorem valid15_16 :
    ClaimedRowsValidFrom PackingCert.pairIndexValid_12
      PackedExhaustionN12.level8 PackedExhaustionN12.level9 120 rows15_16 :=
  PackedExhaustionN12Step8Shard015.valid

abbrev rows16_17 : List Blob := PackedExhaustionN12Step8Shard016.rows
theorem rows16_17_length :
    rows16_17.length = 8 := PackedExhaustionN12Step8Shard016.rows_length
theorem valid16_17 :
    ClaimedRowsValidFrom PackingCert.pairIndexValid_12
      PackedExhaustionN12.level8 PackedExhaustionN12.level9 128 rows16_17 :=
  PackedExhaustionN12Step8Shard016.valid

abbrev rows17_18 : List Blob := PackedExhaustionN12Step8Shard017.rows
theorem rows17_18_length :
    rows17_18.length = 8 := PackedExhaustionN12Step8Shard017.rows_length
theorem valid17_18 :
    ClaimedRowsValidFrom PackingCert.pairIndexValid_12
      PackedExhaustionN12.level8 PackedExhaustionN12.level9 136 rows17_18 :=
  PackedExhaustionN12Step8Shard017.valid

def rows16_18 : List Blob :=
  rows16_17 ++ rows17_18
theorem rows16_18_length :
    rows16_18.length = 16 := by
  simp [rows16_18, rows16_17_length, rows17_18_length]
theorem valid16_18 :
    ClaimedRowsValidFrom PackingCert.pairIndexValid_12
      PackedExhaustionN12.level8 PackedExhaustionN12.level9 128 rows16_18 := by
  apply valid16_17.append
  simpa [rows16_17_length] using valid17_18

def rows15_18 : List Blob :=
  rows15_16 ++ rows16_18
theorem rows15_18_length :
    rows15_18.length = 24 := by
  simp [rows15_18, rows15_16_length, rows16_18_length]
theorem valid15_18 :
    ClaimedRowsValidFrom PackingCert.pairIndexValid_12
      PackedExhaustionN12.level8 PackedExhaustionN12.level9 120 rows15_18 := by
  apply valid15_16.append
  simpa [rows15_16_length] using valid16_18

abbrev rows18_19 : List Blob := PackedExhaustionN12Step8Shard018.rows
theorem rows18_19_length :
    rows18_19.length = 8 := PackedExhaustionN12Step8Shard018.rows_length
theorem valid18_19 :
    ClaimedRowsValidFrom PackingCert.pairIndexValid_12
      PackedExhaustionN12.level8 PackedExhaustionN12.level9 144 rows18_19 :=
  PackedExhaustionN12Step8Shard018.valid

abbrev rows19_20 : List Blob := PackedExhaustionN12Step8Shard019.rows
theorem rows19_20_length :
    rows19_20.length = 8 := PackedExhaustionN12Step8Shard019.rows_length
theorem valid19_20 :
    ClaimedRowsValidFrom PackingCert.pairIndexValid_12
      PackedExhaustionN12.level8 PackedExhaustionN12.level9 152 rows19_20 :=
  PackedExhaustionN12Step8Shard019.valid

def rows18_20 : List Blob :=
  rows18_19 ++ rows19_20
theorem rows18_20_length :
    rows18_20.length = 16 := by
  simp [rows18_20, rows18_19_length, rows19_20_length]
theorem valid18_20 :
    ClaimedRowsValidFrom PackingCert.pairIndexValid_12
      PackedExhaustionN12.level8 PackedExhaustionN12.level9 144 rows18_20 := by
  apply valid18_19.append
  simpa [rows18_19_length] using valid19_20

abbrev rows20_21 : List Blob := PackedExhaustionN12Step8Shard020.rows
theorem rows20_21_length :
    rows20_21.length = 8 := PackedExhaustionN12Step8Shard020.rows_length
theorem valid20_21 :
    ClaimedRowsValidFrom PackingCert.pairIndexValid_12
      PackedExhaustionN12.level8 PackedExhaustionN12.level9 160 rows20_21 :=
  PackedExhaustionN12Step8Shard020.valid

abbrev rows21_22 : List Blob := PackedExhaustionN12Step8Shard021.rows
theorem rows21_22_length :
    rows21_22.length = 8 := PackedExhaustionN12Step8Shard021.rows_length
theorem valid21_22 :
    ClaimedRowsValidFrom PackingCert.pairIndexValid_12
      PackedExhaustionN12.level8 PackedExhaustionN12.level9 168 rows21_22 :=
  PackedExhaustionN12Step8Shard021.valid

def rows20_22 : List Blob :=
  rows20_21 ++ rows21_22
theorem rows20_22_length :
    rows20_22.length = 16 := by
  simp [rows20_22, rows20_21_length, rows21_22_length]
theorem valid20_22 :
    ClaimedRowsValidFrom PackingCert.pairIndexValid_12
      PackedExhaustionN12.level8 PackedExhaustionN12.level9 160 rows20_22 := by
  apply valid20_21.append
  simpa [rows20_21_length] using valid21_22

def rows18_22 : List Blob :=
  rows18_20 ++ rows20_22
theorem rows18_22_length :
    rows18_22.length = 32 := by
  simp [rows18_22, rows18_20_length, rows20_22_length]
theorem valid18_22 :
    ClaimedRowsValidFrom PackingCert.pairIndexValid_12
      PackedExhaustionN12.level8 PackedExhaustionN12.level9 144 rows18_22 := by
  apply valid18_20.append
  simpa [rows18_20_length] using valid20_22

def rows15_22 : List Blob :=
  rows15_18 ++ rows18_22
theorem rows15_22_length :
    rows15_22.length = 56 := by
  simp [rows15_22, rows15_18_length, rows18_22_length]
theorem valid15_22 :
    ClaimedRowsValidFrom PackingCert.pairIndexValid_12
      PackedExhaustionN12.level8 PackedExhaustionN12.level9 120 rows15_22 := by
  apply valid15_18.append
  simpa [rows15_18_length] using valid18_22

abbrev rows22_23 : List Blob := PackedExhaustionN12Step8Shard022.rows
theorem rows22_23_length :
    rows22_23.length = 8 := PackedExhaustionN12Step8Shard022.rows_length
theorem valid22_23 :
    ClaimedRowsValidFrom PackingCert.pairIndexValid_12
      PackedExhaustionN12.level8 PackedExhaustionN12.level9 176 rows22_23 :=
  PackedExhaustionN12Step8Shard022.valid

abbrev rows23_24 : List Blob := PackedExhaustionN12Step8Shard023.rows
theorem rows23_24_length :
    rows23_24.length = 8 := PackedExhaustionN12Step8Shard023.rows_length
theorem valid23_24 :
    ClaimedRowsValidFrom PackingCert.pairIndexValid_12
      PackedExhaustionN12.level8 PackedExhaustionN12.level9 184 rows23_24 :=
  PackedExhaustionN12Step8Shard023.valid

def rows22_24 : List Blob :=
  rows22_23 ++ rows23_24
theorem rows22_24_length :
    rows22_24.length = 16 := by
  simp [rows22_24, rows22_23_length, rows23_24_length]
theorem valid22_24 :
    ClaimedRowsValidFrom PackingCert.pairIndexValid_12
      PackedExhaustionN12.level8 PackedExhaustionN12.level9 176 rows22_24 := by
  apply valid22_23.append
  simpa [rows22_23_length] using valid23_24

abbrev rows24_25 : List Blob := PackedExhaustionN12Step8Shard024.rows
theorem rows24_25_length :
    rows24_25.length = 8 := PackedExhaustionN12Step8Shard024.rows_length
theorem valid24_25 :
    ClaimedRowsValidFrom PackingCert.pairIndexValid_12
      PackedExhaustionN12.level8 PackedExhaustionN12.level9 192 rows24_25 :=
  PackedExhaustionN12Step8Shard024.valid

abbrev rows25_26 : List Blob := PackedExhaustionN12Step8Shard025.rows
theorem rows25_26_length :
    rows25_26.length = 8 := PackedExhaustionN12Step8Shard025.rows_length
theorem valid25_26 :
    ClaimedRowsValidFrom PackingCert.pairIndexValid_12
      PackedExhaustionN12.level8 PackedExhaustionN12.level9 200 rows25_26 :=
  PackedExhaustionN12Step8Shard025.valid

def rows24_26 : List Blob :=
  rows24_25 ++ rows25_26
theorem rows24_26_length :
    rows24_26.length = 16 := by
  simp [rows24_26, rows24_25_length, rows25_26_length]
theorem valid24_26 :
    ClaimedRowsValidFrom PackingCert.pairIndexValid_12
      PackedExhaustionN12.level8 PackedExhaustionN12.level9 192 rows24_26 := by
  apply valid24_25.append
  simpa [rows24_25_length] using valid25_26

def rows22_26 : List Blob :=
  rows22_24 ++ rows24_26
theorem rows22_26_length :
    rows22_26.length = 32 := by
  simp [rows22_26, rows22_24_length, rows24_26_length]
theorem valid22_26 :
    ClaimedRowsValidFrom PackingCert.pairIndexValid_12
      PackedExhaustionN12.level8 PackedExhaustionN12.level9 176 rows22_26 := by
  apply valid22_24.append
  simpa [rows22_24_length] using valid24_26

abbrev rows26_27 : List Blob := PackedExhaustionN12Step8Shard026.rows
theorem rows26_27_length :
    rows26_27.length = 8 := PackedExhaustionN12Step8Shard026.rows_length
theorem valid26_27 :
    ClaimedRowsValidFrom PackingCert.pairIndexValid_12
      PackedExhaustionN12.level8 PackedExhaustionN12.level9 208 rows26_27 :=
  PackedExhaustionN12Step8Shard026.valid

abbrev rows27_28 : List Blob := PackedExhaustionN12Step8Shard027.rows
theorem rows27_28_length :
    rows27_28.length = 8 := PackedExhaustionN12Step8Shard027.rows_length
theorem valid27_28 :
    ClaimedRowsValidFrom PackingCert.pairIndexValid_12
      PackedExhaustionN12.level8 PackedExhaustionN12.level9 216 rows27_28 :=
  PackedExhaustionN12Step8Shard027.valid

def rows26_28 : List Blob :=
  rows26_27 ++ rows27_28
theorem rows26_28_length :
    rows26_28.length = 16 := by
  simp [rows26_28, rows26_27_length, rows27_28_length]
theorem valid26_28 :
    ClaimedRowsValidFrom PackingCert.pairIndexValid_12
      PackedExhaustionN12.level8 PackedExhaustionN12.level9 208 rows26_28 := by
  apply valid26_27.append
  simpa [rows26_27_length] using valid27_28

abbrev rows28_29 : List Blob := PackedExhaustionN12Step8Shard028.rows
theorem rows28_29_length :
    rows28_29.length = 8 := PackedExhaustionN12Step8Shard028.rows_length
theorem valid28_29 :
    ClaimedRowsValidFrom PackingCert.pairIndexValid_12
      PackedExhaustionN12.level8 PackedExhaustionN12.level9 224 rows28_29 :=
  PackedExhaustionN12Step8Shard028.valid

abbrev rows29_30 : List Blob := PackedExhaustionN12Step8Shard029.rows
theorem rows29_30_length :
    rows29_30.length = 8 := PackedExhaustionN12Step8Shard029.rows_length
theorem valid29_30 :
    ClaimedRowsValidFrom PackingCert.pairIndexValid_12
      PackedExhaustionN12.level8 PackedExhaustionN12.level9 232 rows29_30 :=
  PackedExhaustionN12Step8Shard029.valid

def rows28_30 : List Blob :=
  rows28_29 ++ rows29_30
theorem rows28_30_length :
    rows28_30.length = 16 := by
  simp [rows28_30, rows28_29_length, rows29_30_length]
theorem valid28_30 :
    ClaimedRowsValidFrom PackingCert.pairIndexValid_12
      PackedExhaustionN12.level8 PackedExhaustionN12.level9 224 rows28_30 := by
  apply valid28_29.append
  simpa [rows28_29_length] using valid29_30

def rows26_30 : List Blob :=
  rows26_28 ++ rows28_30
theorem rows26_30_length :
    rows26_30.length = 32 := by
  simp [rows26_30, rows26_28_length, rows28_30_length]
theorem valid26_30 :
    ClaimedRowsValidFrom PackingCert.pairIndexValid_12
      PackedExhaustionN12.level8 PackedExhaustionN12.level9 208 rows26_30 := by
  apply valid26_28.append
  simpa [rows26_28_length] using valid28_30

def rows22_30 : List Blob :=
  rows22_26 ++ rows26_30
theorem rows22_30_length :
    rows22_30.length = 64 := by
  simp [rows22_30, rows22_26_length, rows26_30_length]
theorem valid22_30 :
    ClaimedRowsValidFrom PackingCert.pairIndexValid_12
      PackedExhaustionN12.level8 PackedExhaustionN12.level9 176 rows22_30 := by
  apply valid22_26.append
  simpa [rows22_26_length] using valid26_30

def rows15_30 : List Blob :=
  rows15_22 ++ rows22_30
theorem rows15_30_length :
    rows15_30.length = 120 := by
  simp [rows15_30, rows15_22_length, rows22_30_length]
theorem valid15_30 :
    ClaimedRowsValidFrom PackingCert.pairIndexValid_12
      PackedExhaustionN12.level8 PackedExhaustionN12.level9 120 rows15_30 := by
  apply valid15_22.append
  simpa [rows15_22_length] using valid22_30

def rows0_30 : List Blob :=
  rows0_15 ++ rows15_30
theorem rows0_30_length :
    rows0_30.length = 240 := by
  simp [rows0_30, rows0_15_length, rows15_30_length]
theorem valid0_30 :
    ClaimedRowsValidFrom PackingCert.pairIndexValid_12
      PackedExhaustionN12.level8 PackedExhaustionN12.level9 0 rows0_30 := by
  apply valid0_15.append
  simpa [rows0_15_length] using valid15_30

abbrev rows30_31 : List Blob := PackedExhaustionN12Step8Shard030.rows
theorem rows30_31_length :
    rows30_31.length = 8 := PackedExhaustionN12Step8Shard030.rows_length
theorem valid30_31 :
    ClaimedRowsValidFrom PackingCert.pairIndexValid_12
      PackedExhaustionN12.level8 PackedExhaustionN12.level9 240 rows30_31 :=
  PackedExhaustionN12Step8Shard030.valid

abbrev rows31_32 : List Blob := PackedExhaustionN12Step8Shard031.rows
theorem rows31_32_length :
    rows31_32.length = 8 := PackedExhaustionN12Step8Shard031.rows_length
theorem valid31_32 :
    ClaimedRowsValidFrom PackingCert.pairIndexValid_12
      PackedExhaustionN12.level8 PackedExhaustionN12.level9 248 rows31_32 :=
  PackedExhaustionN12Step8Shard031.valid

abbrev rows32_33 : List Blob := PackedExhaustionN12Step8Shard032.rows
theorem rows32_33_length :
    rows32_33.length = 8 := PackedExhaustionN12Step8Shard032.rows_length
theorem valid32_33 :
    ClaimedRowsValidFrom PackingCert.pairIndexValid_12
      PackedExhaustionN12.level8 PackedExhaustionN12.level9 256 rows32_33 :=
  PackedExhaustionN12Step8Shard032.valid

def rows31_33 : List Blob :=
  rows31_32 ++ rows32_33
theorem rows31_33_length :
    rows31_33.length = 16 := by
  simp [rows31_33, rows31_32_length, rows32_33_length]
theorem valid31_33 :
    ClaimedRowsValidFrom PackingCert.pairIndexValid_12
      PackedExhaustionN12.level8 PackedExhaustionN12.level9 248 rows31_33 := by
  apply valid31_32.append
  simpa [rows31_32_length] using valid32_33

def rows30_33 : List Blob :=
  rows30_31 ++ rows31_33
theorem rows30_33_length :
    rows30_33.length = 24 := by
  simp [rows30_33, rows30_31_length, rows31_33_length]
theorem valid30_33 :
    ClaimedRowsValidFrom PackingCert.pairIndexValid_12
      PackedExhaustionN12.level8 PackedExhaustionN12.level9 240 rows30_33 := by
  apply valid30_31.append
  simpa [rows30_31_length] using valid31_33

abbrev rows33_34 : List Blob := PackedExhaustionN12Step8Shard033.rows
theorem rows33_34_length :
    rows33_34.length = 8 := PackedExhaustionN12Step8Shard033.rows_length
theorem valid33_34 :
    ClaimedRowsValidFrom PackingCert.pairIndexValid_12
      PackedExhaustionN12.level8 PackedExhaustionN12.level9 264 rows33_34 :=
  PackedExhaustionN12Step8Shard033.valid

abbrev rows34_35 : List Blob := PackedExhaustionN12Step8Shard034.rows
theorem rows34_35_length :
    rows34_35.length = 8 := PackedExhaustionN12Step8Shard034.rows_length
theorem valid34_35 :
    ClaimedRowsValidFrom PackingCert.pairIndexValid_12
      PackedExhaustionN12.level8 PackedExhaustionN12.level9 272 rows34_35 :=
  PackedExhaustionN12Step8Shard034.valid

def rows33_35 : List Blob :=
  rows33_34 ++ rows34_35
theorem rows33_35_length :
    rows33_35.length = 16 := by
  simp [rows33_35, rows33_34_length, rows34_35_length]
theorem valid33_35 :
    ClaimedRowsValidFrom PackingCert.pairIndexValid_12
      PackedExhaustionN12.level8 PackedExhaustionN12.level9 264 rows33_35 := by
  apply valid33_34.append
  simpa [rows33_34_length] using valid34_35

abbrev rows35_36 : List Blob := PackedExhaustionN12Step8Shard035.rows
theorem rows35_36_length :
    rows35_36.length = 8 := PackedExhaustionN12Step8Shard035.rows_length
theorem valid35_36 :
    ClaimedRowsValidFrom PackingCert.pairIndexValid_12
      PackedExhaustionN12.level8 PackedExhaustionN12.level9 280 rows35_36 :=
  PackedExhaustionN12Step8Shard035.valid

abbrev rows36_37 : List Blob := PackedExhaustionN12Step8Shard036.rows
theorem rows36_37_length :
    rows36_37.length = 8 := PackedExhaustionN12Step8Shard036.rows_length
theorem valid36_37 :
    ClaimedRowsValidFrom PackingCert.pairIndexValid_12
      PackedExhaustionN12.level8 PackedExhaustionN12.level9 288 rows36_37 :=
  PackedExhaustionN12Step8Shard036.valid

def rows35_37 : List Blob :=
  rows35_36 ++ rows36_37
theorem rows35_37_length :
    rows35_37.length = 16 := by
  simp [rows35_37, rows35_36_length, rows36_37_length]
theorem valid35_37 :
    ClaimedRowsValidFrom PackingCert.pairIndexValid_12
      PackedExhaustionN12.level8 PackedExhaustionN12.level9 280 rows35_37 := by
  apply valid35_36.append
  simpa [rows35_36_length] using valid36_37

def rows33_37 : List Blob :=
  rows33_35 ++ rows35_37
theorem rows33_37_length :
    rows33_37.length = 32 := by
  simp [rows33_37, rows33_35_length, rows35_37_length]
theorem valid33_37 :
    ClaimedRowsValidFrom PackingCert.pairIndexValid_12
      PackedExhaustionN12.level8 PackedExhaustionN12.level9 264 rows33_37 := by
  apply valid33_35.append
  simpa [rows33_35_length] using valid35_37

def rows30_37 : List Blob :=
  rows30_33 ++ rows33_37
theorem rows30_37_length :
    rows30_37.length = 56 := by
  simp [rows30_37, rows30_33_length, rows33_37_length]
theorem valid30_37 :
    ClaimedRowsValidFrom PackingCert.pairIndexValid_12
      PackedExhaustionN12.level8 PackedExhaustionN12.level9 240 rows30_37 := by
  apply valid30_33.append
  simpa [rows30_33_length] using valid33_37

abbrev rows37_38 : List Blob := PackedExhaustionN12Step8Shard037.rows
theorem rows37_38_length :
    rows37_38.length = 8 := PackedExhaustionN12Step8Shard037.rows_length
theorem valid37_38 :
    ClaimedRowsValidFrom PackingCert.pairIndexValid_12
      PackedExhaustionN12.level8 PackedExhaustionN12.level9 296 rows37_38 :=
  PackedExhaustionN12Step8Shard037.valid

abbrev rows38_39 : List Blob := PackedExhaustionN12Step8Shard038.rows
theorem rows38_39_length :
    rows38_39.length = 8 := PackedExhaustionN12Step8Shard038.rows_length
theorem valid38_39 :
    ClaimedRowsValidFrom PackingCert.pairIndexValid_12
      PackedExhaustionN12.level8 PackedExhaustionN12.level9 304 rows38_39 :=
  PackedExhaustionN12Step8Shard038.valid

def rows37_39 : List Blob :=
  rows37_38 ++ rows38_39
theorem rows37_39_length :
    rows37_39.length = 16 := by
  simp [rows37_39, rows37_38_length, rows38_39_length]
theorem valid37_39 :
    ClaimedRowsValidFrom PackingCert.pairIndexValid_12
      PackedExhaustionN12.level8 PackedExhaustionN12.level9 296 rows37_39 := by
  apply valid37_38.append
  simpa [rows37_38_length] using valid38_39

abbrev rows39_40 : List Blob := PackedExhaustionN12Step8Shard039.rows
theorem rows39_40_length :
    rows39_40.length = 8 := PackedExhaustionN12Step8Shard039.rows_length
theorem valid39_40 :
    ClaimedRowsValidFrom PackingCert.pairIndexValid_12
      PackedExhaustionN12.level8 PackedExhaustionN12.level9 312 rows39_40 :=
  PackedExhaustionN12Step8Shard039.valid

abbrev rows40_41 : List Blob := PackedExhaustionN12Step8Shard040.rows
theorem rows40_41_length :
    rows40_41.length = 8 := PackedExhaustionN12Step8Shard040.rows_length
theorem valid40_41 :
    ClaimedRowsValidFrom PackingCert.pairIndexValid_12
      PackedExhaustionN12.level8 PackedExhaustionN12.level9 320 rows40_41 :=
  PackedExhaustionN12Step8Shard040.valid

def rows39_41 : List Blob :=
  rows39_40 ++ rows40_41
theorem rows39_41_length :
    rows39_41.length = 16 := by
  simp [rows39_41, rows39_40_length, rows40_41_length]
theorem valid39_41 :
    ClaimedRowsValidFrom PackingCert.pairIndexValid_12
      PackedExhaustionN12.level8 PackedExhaustionN12.level9 312 rows39_41 := by
  apply valid39_40.append
  simpa [rows39_40_length] using valid40_41

def rows37_41 : List Blob :=
  rows37_39 ++ rows39_41
theorem rows37_41_length :
    rows37_41.length = 32 := by
  simp [rows37_41, rows37_39_length, rows39_41_length]
theorem valid37_41 :
    ClaimedRowsValidFrom PackingCert.pairIndexValid_12
      PackedExhaustionN12.level8 PackedExhaustionN12.level9 296 rows37_41 := by
  apply valid37_39.append
  simpa [rows37_39_length] using valid39_41

abbrev rows41_42 : List Blob := PackedExhaustionN12Step8Shard041.rows
theorem rows41_42_length :
    rows41_42.length = 8 := PackedExhaustionN12Step8Shard041.rows_length
theorem valid41_42 :
    ClaimedRowsValidFrom PackingCert.pairIndexValid_12
      PackedExhaustionN12.level8 PackedExhaustionN12.level9 328 rows41_42 :=
  PackedExhaustionN12Step8Shard041.valid

abbrev rows42_43 : List Blob := PackedExhaustionN12Step8Shard042.rows
theorem rows42_43_length :
    rows42_43.length = 8 := PackedExhaustionN12Step8Shard042.rows_length
theorem valid42_43 :
    ClaimedRowsValidFrom PackingCert.pairIndexValid_12
      PackedExhaustionN12.level8 PackedExhaustionN12.level9 336 rows42_43 :=
  PackedExhaustionN12Step8Shard042.valid

def rows41_43 : List Blob :=
  rows41_42 ++ rows42_43
theorem rows41_43_length :
    rows41_43.length = 16 := by
  simp [rows41_43, rows41_42_length, rows42_43_length]
theorem valid41_43 :
    ClaimedRowsValidFrom PackingCert.pairIndexValid_12
      PackedExhaustionN12.level8 PackedExhaustionN12.level9 328 rows41_43 := by
  apply valid41_42.append
  simpa [rows41_42_length] using valid42_43

abbrev rows43_44 : List Blob := PackedExhaustionN12Step8Shard043.rows
theorem rows43_44_length :
    rows43_44.length = 8 := PackedExhaustionN12Step8Shard043.rows_length
theorem valid43_44 :
    ClaimedRowsValidFrom PackingCert.pairIndexValid_12
      PackedExhaustionN12.level8 PackedExhaustionN12.level9 344 rows43_44 :=
  PackedExhaustionN12Step8Shard043.valid

abbrev rows44_45 : List Blob := PackedExhaustionN12Step8Shard044.rows
theorem rows44_45_length :
    rows44_45.length = 8 := PackedExhaustionN12Step8Shard044.rows_length
theorem valid44_45 :
    ClaimedRowsValidFrom PackingCert.pairIndexValid_12
      PackedExhaustionN12.level8 PackedExhaustionN12.level9 352 rows44_45 :=
  PackedExhaustionN12Step8Shard044.valid

def rows43_45 : List Blob :=
  rows43_44 ++ rows44_45
theorem rows43_45_length :
    rows43_45.length = 16 := by
  simp [rows43_45, rows43_44_length, rows44_45_length]
theorem valid43_45 :
    ClaimedRowsValidFrom PackingCert.pairIndexValid_12
      PackedExhaustionN12.level8 PackedExhaustionN12.level9 344 rows43_45 := by
  apply valid43_44.append
  simpa [rows43_44_length] using valid44_45

def rows41_45 : List Blob :=
  rows41_43 ++ rows43_45
theorem rows41_45_length :
    rows41_45.length = 32 := by
  simp [rows41_45, rows41_43_length, rows43_45_length]
theorem valid41_45 :
    ClaimedRowsValidFrom PackingCert.pairIndexValid_12
      PackedExhaustionN12.level8 PackedExhaustionN12.level9 328 rows41_45 := by
  apply valid41_43.append
  simpa [rows41_43_length] using valid43_45

def rows37_45 : List Blob :=
  rows37_41 ++ rows41_45
theorem rows37_45_length :
    rows37_45.length = 64 := by
  simp [rows37_45, rows37_41_length, rows41_45_length]
theorem valid37_45 :
    ClaimedRowsValidFrom PackingCert.pairIndexValid_12
      PackedExhaustionN12.level8 PackedExhaustionN12.level9 296 rows37_45 := by
  apply valid37_41.append
  simpa [rows37_41_length] using valid41_45

def rows30_45 : List Blob :=
  rows30_37 ++ rows37_45
theorem rows30_45_length :
    rows30_45.length = 120 := by
  simp [rows30_45, rows30_37_length, rows37_45_length]
theorem valid30_45 :
    ClaimedRowsValidFrom PackingCert.pairIndexValid_12
      PackedExhaustionN12.level8 PackedExhaustionN12.level9 240 rows30_45 := by
  apply valid30_37.append
  simpa [rows30_37_length] using valid37_45

abbrev rows45_46 : List Blob := PackedExhaustionN12Step8Shard045.rows
theorem rows45_46_length :
    rows45_46.length = 8 := PackedExhaustionN12Step8Shard045.rows_length
theorem valid45_46 :
    ClaimedRowsValidFrom PackingCert.pairIndexValid_12
      PackedExhaustionN12.level8 PackedExhaustionN12.level9 360 rows45_46 :=
  PackedExhaustionN12Step8Shard045.valid

abbrev rows46_47 : List Blob := PackedExhaustionN12Step8Shard046.rows
theorem rows46_47_length :
    rows46_47.length = 8 := PackedExhaustionN12Step8Shard046.rows_length
theorem valid46_47 :
    ClaimedRowsValidFrom PackingCert.pairIndexValid_12
      PackedExhaustionN12.level8 PackedExhaustionN12.level9 368 rows46_47 :=
  PackedExhaustionN12Step8Shard046.valid

def rows45_47 : List Blob :=
  rows45_46 ++ rows46_47
theorem rows45_47_length :
    rows45_47.length = 16 := by
  simp [rows45_47, rows45_46_length, rows46_47_length]
theorem valid45_47 :
    ClaimedRowsValidFrom PackingCert.pairIndexValid_12
      PackedExhaustionN12.level8 PackedExhaustionN12.level9 360 rows45_47 := by
  apply valid45_46.append
  simpa [rows45_46_length] using valid46_47

abbrev rows47_48 : List Blob := PackedExhaustionN12Step8Shard047.rows
theorem rows47_48_length :
    rows47_48.length = 8 := PackedExhaustionN12Step8Shard047.rows_length
theorem valid47_48 :
    ClaimedRowsValidFrom PackingCert.pairIndexValid_12
      PackedExhaustionN12.level8 PackedExhaustionN12.level9 376 rows47_48 :=
  PackedExhaustionN12Step8Shard047.valid

abbrev rows48_49 : List Blob := PackedExhaustionN12Step8Shard048.rows
theorem rows48_49_length :
    rows48_49.length = 8 := PackedExhaustionN12Step8Shard048.rows_length
theorem valid48_49 :
    ClaimedRowsValidFrom PackingCert.pairIndexValid_12
      PackedExhaustionN12.level8 PackedExhaustionN12.level9 384 rows48_49 :=
  PackedExhaustionN12Step8Shard048.valid

def rows47_49 : List Blob :=
  rows47_48 ++ rows48_49
theorem rows47_49_length :
    rows47_49.length = 16 := by
  simp [rows47_49, rows47_48_length, rows48_49_length]
theorem valid47_49 :
    ClaimedRowsValidFrom PackingCert.pairIndexValid_12
      PackedExhaustionN12.level8 PackedExhaustionN12.level9 376 rows47_49 := by
  apply valid47_48.append
  simpa [rows47_48_length] using valid48_49

def rows45_49 : List Blob :=
  rows45_47 ++ rows47_49
theorem rows45_49_length :
    rows45_49.length = 32 := by
  simp [rows45_49, rows45_47_length, rows47_49_length]
theorem valid45_49 :
    ClaimedRowsValidFrom PackingCert.pairIndexValid_12
      PackedExhaustionN12.level8 PackedExhaustionN12.level9 360 rows45_49 := by
  apply valid45_47.append
  simpa [rows45_47_length] using valid47_49

abbrev rows49_50 : List Blob := PackedExhaustionN12Step8Shard049.rows
theorem rows49_50_length :
    rows49_50.length = 8 := PackedExhaustionN12Step8Shard049.rows_length
theorem valid49_50 :
    ClaimedRowsValidFrom PackingCert.pairIndexValid_12
      PackedExhaustionN12.level8 PackedExhaustionN12.level9 392 rows49_50 :=
  PackedExhaustionN12Step8Shard049.valid

abbrev rows50_51 : List Blob := PackedExhaustionN12Step8Shard050.rows
theorem rows50_51_length :
    rows50_51.length = 8 := PackedExhaustionN12Step8Shard050.rows_length
theorem valid50_51 :
    ClaimedRowsValidFrom PackingCert.pairIndexValid_12
      PackedExhaustionN12.level8 PackedExhaustionN12.level9 400 rows50_51 :=
  PackedExhaustionN12Step8Shard050.valid

def rows49_51 : List Blob :=
  rows49_50 ++ rows50_51
theorem rows49_51_length :
    rows49_51.length = 16 := by
  simp [rows49_51, rows49_50_length, rows50_51_length]
theorem valid49_51 :
    ClaimedRowsValidFrom PackingCert.pairIndexValid_12
      PackedExhaustionN12.level8 PackedExhaustionN12.level9 392 rows49_51 := by
  apply valid49_50.append
  simpa [rows49_50_length] using valid50_51

abbrev rows51_52 : List Blob := PackedExhaustionN12Step8Shard051.rows
theorem rows51_52_length :
    rows51_52.length = 8 := PackedExhaustionN12Step8Shard051.rows_length
theorem valid51_52 :
    ClaimedRowsValidFrom PackingCert.pairIndexValid_12
      PackedExhaustionN12.level8 PackedExhaustionN12.level9 408 rows51_52 :=
  PackedExhaustionN12Step8Shard051.valid

abbrev rows52_53 : List Blob := PackedExhaustionN12Step8Shard052.rows
theorem rows52_53_length :
    rows52_53.length = 8 := PackedExhaustionN12Step8Shard052.rows_length
theorem valid52_53 :
    ClaimedRowsValidFrom PackingCert.pairIndexValid_12
      PackedExhaustionN12.level8 PackedExhaustionN12.level9 416 rows52_53 :=
  PackedExhaustionN12Step8Shard052.valid

def rows51_53 : List Blob :=
  rows51_52 ++ rows52_53
theorem rows51_53_length :
    rows51_53.length = 16 := by
  simp [rows51_53, rows51_52_length, rows52_53_length]
theorem valid51_53 :
    ClaimedRowsValidFrom PackingCert.pairIndexValid_12
      PackedExhaustionN12.level8 PackedExhaustionN12.level9 408 rows51_53 := by
  apply valid51_52.append
  simpa [rows51_52_length] using valid52_53

def rows49_53 : List Blob :=
  rows49_51 ++ rows51_53
theorem rows49_53_length :
    rows49_53.length = 32 := by
  simp [rows49_53, rows49_51_length, rows51_53_length]
theorem valid49_53 :
    ClaimedRowsValidFrom PackingCert.pairIndexValid_12
      PackedExhaustionN12.level8 PackedExhaustionN12.level9 392 rows49_53 := by
  apply valid49_51.append
  simpa [rows49_51_length] using valid51_53

def rows45_53 : List Blob :=
  rows45_49 ++ rows49_53
theorem rows45_53_length :
    rows45_53.length = 64 := by
  simp [rows45_53, rows45_49_length, rows49_53_length]
theorem valid45_53 :
    ClaimedRowsValidFrom PackingCert.pairIndexValid_12
      PackedExhaustionN12.level8 PackedExhaustionN12.level9 360 rows45_53 := by
  apply valid45_49.append
  simpa [rows45_49_length] using valid49_53

abbrev rows53_54 : List Blob := PackedExhaustionN12Step8Shard053.rows
theorem rows53_54_length :
    rows53_54.length = 8 := PackedExhaustionN12Step8Shard053.rows_length
theorem valid53_54 :
    ClaimedRowsValidFrom PackingCert.pairIndexValid_12
      PackedExhaustionN12.level8 PackedExhaustionN12.level9 424 rows53_54 :=
  PackedExhaustionN12Step8Shard053.valid

abbrev rows54_55 : List Blob := PackedExhaustionN12Step8Shard054.rows
theorem rows54_55_length :
    rows54_55.length = 8 := PackedExhaustionN12Step8Shard054.rows_length
theorem valid54_55 :
    ClaimedRowsValidFrom PackingCert.pairIndexValid_12
      PackedExhaustionN12.level8 PackedExhaustionN12.level9 432 rows54_55 :=
  PackedExhaustionN12Step8Shard054.valid

def rows53_55 : List Blob :=
  rows53_54 ++ rows54_55
theorem rows53_55_length :
    rows53_55.length = 16 := by
  simp [rows53_55, rows53_54_length, rows54_55_length]
theorem valid53_55 :
    ClaimedRowsValidFrom PackingCert.pairIndexValid_12
      PackedExhaustionN12.level8 PackedExhaustionN12.level9 424 rows53_55 := by
  apply valid53_54.append
  simpa [rows53_54_length] using valid54_55

abbrev rows55_56 : List Blob := PackedExhaustionN12Step8Shard055.rows
theorem rows55_56_length :
    rows55_56.length = 8 := PackedExhaustionN12Step8Shard055.rows_length
theorem valid55_56 :
    ClaimedRowsValidFrom PackingCert.pairIndexValid_12
      PackedExhaustionN12.level8 PackedExhaustionN12.level9 440 rows55_56 :=
  PackedExhaustionN12Step8Shard055.valid

abbrev rows56_57 : List Blob := PackedExhaustionN12Step8Shard056.rows
theorem rows56_57_length :
    rows56_57.length = 8 := PackedExhaustionN12Step8Shard056.rows_length
theorem valid56_57 :
    ClaimedRowsValidFrom PackingCert.pairIndexValid_12
      PackedExhaustionN12.level8 PackedExhaustionN12.level9 448 rows56_57 :=
  PackedExhaustionN12Step8Shard056.valid

def rows55_57 : List Blob :=
  rows55_56 ++ rows56_57
theorem rows55_57_length :
    rows55_57.length = 16 := by
  simp [rows55_57, rows55_56_length, rows56_57_length]
theorem valid55_57 :
    ClaimedRowsValidFrom PackingCert.pairIndexValid_12
      PackedExhaustionN12.level8 PackedExhaustionN12.level9 440 rows55_57 := by
  apply valid55_56.append
  simpa [rows55_56_length] using valid56_57

def rows53_57 : List Blob :=
  rows53_55 ++ rows55_57
theorem rows53_57_length :
    rows53_57.length = 32 := by
  simp [rows53_57, rows53_55_length, rows55_57_length]
theorem valid53_57 :
    ClaimedRowsValidFrom PackingCert.pairIndexValid_12
      PackedExhaustionN12.level8 PackedExhaustionN12.level9 424 rows53_57 := by
  apply valid53_55.append
  simpa [rows53_55_length] using valid55_57

abbrev rows57_58 : List Blob := PackedExhaustionN12Step8Shard057.rows
theorem rows57_58_length :
    rows57_58.length = 8 := PackedExhaustionN12Step8Shard057.rows_length
theorem valid57_58 :
    ClaimedRowsValidFrom PackingCert.pairIndexValid_12
      PackedExhaustionN12.level8 PackedExhaustionN12.level9 456 rows57_58 :=
  PackedExhaustionN12Step8Shard057.valid

abbrev rows58_59 : List Blob := PackedExhaustionN12Step8Shard058.rows
theorem rows58_59_length :
    rows58_59.length = 8 := PackedExhaustionN12Step8Shard058.rows_length
theorem valid58_59 :
    ClaimedRowsValidFrom PackingCert.pairIndexValid_12
      PackedExhaustionN12.level8 PackedExhaustionN12.level9 464 rows58_59 :=
  PackedExhaustionN12Step8Shard058.valid

def rows57_59 : List Blob :=
  rows57_58 ++ rows58_59
theorem rows57_59_length :
    rows57_59.length = 16 := by
  simp [rows57_59, rows57_58_length, rows58_59_length]
theorem valid57_59 :
    ClaimedRowsValidFrom PackingCert.pairIndexValid_12
      PackedExhaustionN12.level8 PackedExhaustionN12.level9 456 rows57_59 := by
  apply valid57_58.append
  simpa [rows57_58_length] using valid58_59

abbrev rows59_60 : List Blob := PackedExhaustionN12Step8Shard059.rows
theorem rows59_60_length :
    rows59_60.length = 8 := PackedExhaustionN12Step8Shard059.rows_length
theorem valid59_60 :
    ClaimedRowsValidFrom PackingCert.pairIndexValid_12
      PackedExhaustionN12.level8 PackedExhaustionN12.level9 472 rows59_60 :=
  PackedExhaustionN12Step8Shard059.valid

abbrev rows60_61 : List Blob := PackedExhaustionN12Step8Shard060.rows
theorem rows60_61_length :
    rows60_61.length = 5 := PackedExhaustionN12Step8Shard060.rows_length
theorem valid60_61 :
    ClaimedRowsValidFrom PackingCert.pairIndexValid_12
      PackedExhaustionN12.level8 PackedExhaustionN12.level9 480 rows60_61 :=
  PackedExhaustionN12Step8Shard060.valid

def rows59_61 : List Blob :=
  rows59_60 ++ rows60_61
theorem rows59_61_length :
    rows59_61.length = 13 := by
  simp [rows59_61, rows59_60_length, rows60_61_length]
theorem valid59_61 :
    ClaimedRowsValidFrom PackingCert.pairIndexValid_12
      PackedExhaustionN12.level8 PackedExhaustionN12.level9 472 rows59_61 := by
  apply valid59_60.append
  simpa [rows59_60_length] using valid60_61

def rows57_61 : List Blob :=
  rows57_59 ++ rows59_61
theorem rows57_61_length :
    rows57_61.length = 29 := by
  simp [rows57_61, rows57_59_length, rows59_61_length]
theorem valid57_61 :
    ClaimedRowsValidFrom PackingCert.pairIndexValid_12
      PackedExhaustionN12.level8 PackedExhaustionN12.level9 456 rows57_61 := by
  apply valid57_59.append
  simpa [rows57_59_length] using valid59_61

def rows53_61 : List Blob :=
  rows53_57 ++ rows57_61
theorem rows53_61_length :
    rows53_61.length = 61 := by
  simp [rows53_61, rows53_57_length, rows57_61_length]
theorem valid53_61 :
    ClaimedRowsValidFrom PackingCert.pairIndexValid_12
      PackedExhaustionN12.level8 PackedExhaustionN12.level9 424 rows53_61 := by
  apply valid53_57.append
  simpa [rows53_57_length] using valid57_61

def rows45_61 : List Blob :=
  rows45_53 ++ rows53_61
theorem rows45_61_length :
    rows45_61.length = 125 := by
  simp [rows45_61, rows45_53_length, rows53_61_length]
theorem valid45_61 :
    ClaimedRowsValidFrom PackingCert.pairIndexValid_12
      PackedExhaustionN12.level8 PackedExhaustionN12.level9 360 rows45_61 := by
  apply valid45_53.append
  simpa [rows45_53_length] using valid53_61

def rows30_61 : List Blob :=
  rows30_45 ++ rows45_61
theorem rows30_61_length :
    rows30_61.length = 245 := by
  simp [rows30_61, rows30_45_length, rows45_61_length]
theorem valid30_61 :
    ClaimedRowsValidFrom PackingCert.pairIndexValid_12
      PackedExhaustionN12.level8 PackedExhaustionN12.level9 240 rows30_61 := by
  apply valid30_45.append
  simpa [rows30_45_length] using valid45_61

def rows0_61 : List Blob :=
  rows0_30 ++ rows30_61
theorem rows0_61_length :
    rows0_61.length = 485 := by
  simp [rows0_61, rows0_30_length, rows30_61_length]
theorem valid0_61 :
    ClaimedRowsValidFrom PackingCert.pairIndexValid_12
      PackedExhaustionN12.level8 PackedExhaustionN12.level9 0 rows0_61 := by
  apply valid0_30.append
  simpa [rows0_30_length] using valid30_61

abbrev rows : List Blob := rows0_61
theorem rows_length : rows.length = 485 := rows0_61_length
theorem valid : ClaimedRowsValidFrom PackingCert.pairIndexValid_12
    PackedExhaustionN12.level8 PackedExhaustionN12.level9 0 rows := valid0_61

def table : Array (Array (Option (Transition 12))) :=
  claimedTableFrom 12 rows

theorem stepValid :
    CertificateExhaustion.StepValid PackedExhaustionN12.level8.toArray
      PackedExhaustionN12.level9.toArray table := by
  apply valid.stepValid
  simpa [PackedExhaustionN12.level8, rows_length]

end Erdos76.CertificateExhaustion.Certificates.PackedExhaustionN12.Step8
