/-
Copyright 2026 The Lean-Proofs Authors.
Licensed under the Apache License, Version 2.0.
-/
import ErdosProblems.Erdos76.Certificates.PackedExhaustionN12Step7Shard000
import ErdosProblems.Erdos76.Certificates.PackedExhaustionN12Step7Shard001
import ErdosProblems.Erdos76.Certificates.PackedExhaustionN12Step7Shard002
import ErdosProblems.Erdos76.Certificates.PackedExhaustionN12Step7Shard003
import ErdosProblems.Erdos76.Certificates.PackedExhaustionN12Step7Shard004
import ErdosProblems.Erdos76.Certificates.PackedExhaustionN12Step7Shard005
import ErdosProblems.Erdos76.Certificates.PackedExhaustionN12Step7Shard006
import ErdosProblems.Erdos76.Certificates.PackedExhaustionN12Step7Shard007
import ErdosProblems.Erdos76.Certificates.PackedExhaustionN12Step7Shard008
import ErdosProblems.Erdos76.Certificates.PackedExhaustionN12Step7Shard009
import ErdosProblems.Erdos76.Certificates.PackedExhaustionN12Step7Shard010
import ErdosProblems.Erdos76.Certificates.PackedExhaustionN12Step7Shard011
import ErdosProblems.Erdos76.Certificates.PackedExhaustionN12Step7Shard012
import ErdosProblems.Erdos76.Certificates.PackedExhaustionN12Step7Shard013
import ErdosProblems.Erdos76.Certificates.PackedExhaustionN12Step7Shard014
import ErdosProblems.Erdos76.Certificates.PackedExhaustionN12Step7Shard015
import ErdosProblems.Erdos76.Certificates.PackedExhaustionN12Step7Shard016
import ErdosProblems.Erdos76.Certificates.PackedExhaustionN12Step7Shard017
import ErdosProblems.Erdos76.Certificates.PackedExhaustionN12Step7Shard018
import ErdosProblems.Erdos76.Certificates.PackedExhaustionN12Step7Shard019
import ErdosProblems.Erdos76.Certificates.PackedExhaustionN12Step7Shard020
import ErdosProblems.Erdos76.Certificates.PackedExhaustionN12Step7Shard021

/-! Proof-only aggregate for the n=12 exhaustion step 7. -/
namespace Erdos76.CertificateExhaustion.Certificates.PackedExhaustionN12.Step7

open CertificateChecker
open CertificateChecker.PackedBucketCertificate
open Packed

abbrev rows0_1 : List Blob := PackedExhaustionN12Step7Shard000.rows
theorem rows0_1_length :
    rows0_1.length = 8 := PackedExhaustionN12Step7Shard000.rows_length
theorem valid0_1 :
    ClaimedRowsValidFrom PackingCert.pairIndexValid_12
      PackedExhaustionN12.level7 PackedExhaustionN12.level8 0 rows0_1 :=
  PackedExhaustionN12Step7Shard000.valid

abbrev rows1_2 : List Blob := PackedExhaustionN12Step7Shard001.rows
theorem rows1_2_length :
    rows1_2.length = 8 := PackedExhaustionN12Step7Shard001.rows_length
theorem valid1_2 :
    ClaimedRowsValidFrom PackingCert.pairIndexValid_12
      PackedExhaustionN12.level7 PackedExhaustionN12.level8 8 rows1_2 :=
  PackedExhaustionN12Step7Shard001.valid

def rows0_2 : List Blob :=
  rows0_1 ++ rows1_2
theorem rows0_2_length :
    rows0_2.length = 16 := by
  simp [rows0_2, rows0_1_length, rows1_2_length]
theorem valid0_2 :
    ClaimedRowsValidFrom PackingCert.pairIndexValid_12
      PackedExhaustionN12.level7 PackedExhaustionN12.level8 0 rows0_2 := by
  apply valid0_1.append
  simpa [rows0_1_length] using valid1_2

abbrev rows2_3 : List Blob := PackedExhaustionN12Step7Shard002.rows
theorem rows2_3_length :
    rows2_3.length = 8 := PackedExhaustionN12Step7Shard002.rows_length
theorem valid2_3 :
    ClaimedRowsValidFrom PackingCert.pairIndexValid_12
      PackedExhaustionN12.level7 PackedExhaustionN12.level8 16 rows2_3 :=
  PackedExhaustionN12Step7Shard002.valid

abbrev rows3_4 : List Blob := PackedExhaustionN12Step7Shard003.rows
theorem rows3_4_length :
    rows3_4.length = 8 := PackedExhaustionN12Step7Shard003.rows_length
theorem valid3_4 :
    ClaimedRowsValidFrom PackingCert.pairIndexValid_12
      PackedExhaustionN12.level7 PackedExhaustionN12.level8 24 rows3_4 :=
  PackedExhaustionN12Step7Shard003.valid

abbrev rows4_5 : List Blob := PackedExhaustionN12Step7Shard004.rows
theorem rows4_5_length :
    rows4_5.length = 8 := PackedExhaustionN12Step7Shard004.rows_length
theorem valid4_5 :
    ClaimedRowsValidFrom PackingCert.pairIndexValid_12
      PackedExhaustionN12.level7 PackedExhaustionN12.level8 32 rows4_5 :=
  PackedExhaustionN12Step7Shard004.valid

def rows3_5 : List Blob :=
  rows3_4 ++ rows4_5
theorem rows3_5_length :
    rows3_5.length = 16 := by
  simp [rows3_5, rows3_4_length, rows4_5_length]
theorem valid3_5 :
    ClaimedRowsValidFrom PackingCert.pairIndexValid_12
      PackedExhaustionN12.level7 PackedExhaustionN12.level8 24 rows3_5 := by
  apply valid3_4.append
  simpa [rows3_4_length] using valid4_5

def rows2_5 : List Blob :=
  rows2_3 ++ rows3_5
theorem rows2_5_length :
    rows2_5.length = 24 := by
  simp [rows2_5, rows2_3_length, rows3_5_length]
theorem valid2_5 :
    ClaimedRowsValidFrom PackingCert.pairIndexValid_12
      PackedExhaustionN12.level7 PackedExhaustionN12.level8 16 rows2_5 := by
  apply valid2_3.append
  simpa [rows2_3_length] using valid3_5

def rows0_5 : List Blob :=
  rows0_2 ++ rows2_5
theorem rows0_5_length :
    rows0_5.length = 40 := by
  simp [rows0_5, rows0_2_length, rows2_5_length]
theorem valid0_5 :
    ClaimedRowsValidFrom PackingCert.pairIndexValid_12
      PackedExhaustionN12.level7 PackedExhaustionN12.level8 0 rows0_5 := by
  apply valid0_2.append
  simpa [rows0_2_length] using valid2_5

abbrev rows5_6 : List Blob := PackedExhaustionN12Step7Shard005.rows
theorem rows5_6_length :
    rows5_6.length = 8 := PackedExhaustionN12Step7Shard005.rows_length
theorem valid5_6 :
    ClaimedRowsValidFrom PackingCert.pairIndexValid_12
      PackedExhaustionN12.level7 PackedExhaustionN12.level8 40 rows5_6 :=
  PackedExhaustionN12Step7Shard005.valid

abbrev rows6_7 : List Blob := PackedExhaustionN12Step7Shard006.rows
theorem rows6_7_length :
    rows6_7.length = 8 := PackedExhaustionN12Step7Shard006.rows_length
theorem valid6_7 :
    ClaimedRowsValidFrom PackingCert.pairIndexValid_12
      PackedExhaustionN12.level7 PackedExhaustionN12.level8 48 rows6_7 :=
  PackedExhaustionN12Step7Shard006.valid

abbrev rows7_8 : List Blob := PackedExhaustionN12Step7Shard007.rows
theorem rows7_8_length :
    rows7_8.length = 8 := PackedExhaustionN12Step7Shard007.rows_length
theorem valid7_8 :
    ClaimedRowsValidFrom PackingCert.pairIndexValid_12
      PackedExhaustionN12.level7 PackedExhaustionN12.level8 56 rows7_8 :=
  PackedExhaustionN12Step7Shard007.valid

def rows6_8 : List Blob :=
  rows6_7 ++ rows7_8
theorem rows6_8_length :
    rows6_8.length = 16 := by
  simp [rows6_8, rows6_7_length, rows7_8_length]
theorem valid6_8 :
    ClaimedRowsValidFrom PackingCert.pairIndexValid_12
      PackedExhaustionN12.level7 PackedExhaustionN12.level8 48 rows6_8 := by
  apply valid6_7.append
  simpa [rows6_7_length] using valid7_8

def rows5_8 : List Blob :=
  rows5_6 ++ rows6_8
theorem rows5_8_length :
    rows5_8.length = 24 := by
  simp [rows5_8, rows5_6_length, rows6_8_length]
theorem valid5_8 :
    ClaimedRowsValidFrom PackingCert.pairIndexValid_12
      PackedExhaustionN12.level7 PackedExhaustionN12.level8 40 rows5_8 := by
  apply valid5_6.append
  simpa [rows5_6_length] using valid6_8

abbrev rows8_9 : List Blob := PackedExhaustionN12Step7Shard008.rows
theorem rows8_9_length :
    rows8_9.length = 8 := PackedExhaustionN12Step7Shard008.rows_length
theorem valid8_9 :
    ClaimedRowsValidFrom PackingCert.pairIndexValid_12
      PackedExhaustionN12.level7 PackedExhaustionN12.level8 64 rows8_9 :=
  PackedExhaustionN12Step7Shard008.valid

abbrev rows9_10 : List Blob := PackedExhaustionN12Step7Shard009.rows
theorem rows9_10_length :
    rows9_10.length = 8 := PackedExhaustionN12Step7Shard009.rows_length
theorem valid9_10 :
    ClaimedRowsValidFrom PackingCert.pairIndexValid_12
      PackedExhaustionN12.level7 PackedExhaustionN12.level8 72 rows9_10 :=
  PackedExhaustionN12Step7Shard009.valid

abbrev rows10_11 : List Blob := PackedExhaustionN12Step7Shard010.rows
theorem rows10_11_length :
    rows10_11.length = 8 := PackedExhaustionN12Step7Shard010.rows_length
theorem valid10_11 :
    ClaimedRowsValidFrom PackingCert.pairIndexValid_12
      PackedExhaustionN12.level7 PackedExhaustionN12.level8 80 rows10_11 :=
  PackedExhaustionN12Step7Shard010.valid

def rows9_11 : List Blob :=
  rows9_10 ++ rows10_11
theorem rows9_11_length :
    rows9_11.length = 16 := by
  simp [rows9_11, rows9_10_length, rows10_11_length]
theorem valid9_11 :
    ClaimedRowsValidFrom PackingCert.pairIndexValid_12
      PackedExhaustionN12.level7 PackedExhaustionN12.level8 72 rows9_11 := by
  apply valid9_10.append
  simpa [rows9_10_length] using valid10_11

def rows8_11 : List Blob :=
  rows8_9 ++ rows9_11
theorem rows8_11_length :
    rows8_11.length = 24 := by
  simp [rows8_11, rows8_9_length, rows9_11_length]
theorem valid8_11 :
    ClaimedRowsValidFrom PackingCert.pairIndexValid_12
      PackedExhaustionN12.level7 PackedExhaustionN12.level8 64 rows8_11 := by
  apply valid8_9.append
  simpa [rows8_9_length] using valid9_11

def rows5_11 : List Blob :=
  rows5_8 ++ rows8_11
theorem rows5_11_length :
    rows5_11.length = 48 := by
  simp [rows5_11, rows5_8_length, rows8_11_length]
theorem valid5_11 :
    ClaimedRowsValidFrom PackingCert.pairIndexValid_12
      PackedExhaustionN12.level7 PackedExhaustionN12.level8 40 rows5_11 := by
  apply valid5_8.append
  simpa [rows5_8_length] using valid8_11

def rows0_11 : List Blob :=
  rows0_5 ++ rows5_11
theorem rows0_11_length :
    rows0_11.length = 88 := by
  simp [rows0_11, rows0_5_length, rows5_11_length]
theorem valid0_11 :
    ClaimedRowsValidFrom PackingCert.pairIndexValid_12
      PackedExhaustionN12.level7 PackedExhaustionN12.level8 0 rows0_11 := by
  apply valid0_5.append
  simpa [rows0_5_length] using valid5_11

abbrev rows11_12 : List Blob := PackedExhaustionN12Step7Shard011.rows
theorem rows11_12_length :
    rows11_12.length = 8 := PackedExhaustionN12Step7Shard011.rows_length
theorem valid11_12 :
    ClaimedRowsValidFrom PackingCert.pairIndexValid_12
      PackedExhaustionN12.level7 PackedExhaustionN12.level8 88 rows11_12 :=
  PackedExhaustionN12Step7Shard011.valid

abbrev rows12_13 : List Blob := PackedExhaustionN12Step7Shard012.rows
theorem rows12_13_length :
    rows12_13.length = 8 := PackedExhaustionN12Step7Shard012.rows_length
theorem valid12_13 :
    ClaimedRowsValidFrom PackingCert.pairIndexValid_12
      PackedExhaustionN12.level7 PackedExhaustionN12.level8 96 rows12_13 :=
  PackedExhaustionN12Step7Shard012.valid

def rows11_13 : List Blob :=
  rows11_12 ++ rows12_13
theorem rows11_13_length :
    rows11_13.length = 16 := by
  simp [rows11_13, rows11_12_length, rows12_13_length]
theorem valid11_13 :
    ClaimedRowsValidFrom PackingCert.pairIndexValid_12
      PackedExhaustionN12.level7 PackedExhaustionN12.level8 88 rows11_13 := by
  apply valid11_12.append
  simpa [rows11_12_length] using valid12_13

abbrev rows13_14 : List Blob := PackedExhaustionN12Step7Shard013.rows
theorem rows13_14_length :
    rows13_14.length = 8 := PackedExhaustionN12Step7Shard013.rows_length
theorem valid13_14 :
    ClaimedRowsValidFrom PackingCert.pairIndexValid_12
      PackedExhaustionN12.level7 PackedExhaustionN12.level8 104 rows13_14 :=
  PackedExhaustionN12Step7Shard013.valid

abbrev rows14_15 : List Blob := PackedExhaustionN12Step7Shard014.rows
theorem rows14_15_length :
    rows14_15.length = 8 := PackedExhaustionN12Step7Shard014.rows_length
theorem valid14_15 :
    ClaimedRowsValidFrom PackingCert.pairIndexValid_12
      PackedExhaustionN12.level7 PackedExhaustionN12.level8 112 rows14_15 :=
  PackedExhaustionN12Step7Shard014.valid

abbrev rows15_16 : List Blob := PackedExhaustionN12Step7Shard015.rows
theorem rows15_16_length :
    rows15_16.length = 8 := PackedExhaustionN12Step7Shard015.rows_length
theorem valid15_16 :
    ClaimedRowsValidFrom PackingCert.pairIndexValid_12
      PackedExhaustionN12.level7 PackedExhaustionN12.level8 120 rows15_16 :=
  PackedExhaustionN12Step7Shard015.valid

def rows14_16 : List Blob :=
  rows14_15 ++ rows15_16
theorem rows14_16_length :
    rows14_16.length = 16 := by
  simp [rows14_16, rows14_15_length, rows15_16_length]
theorem valid14_16 :
    ClaimedRowsValidFrom PackingCert.pairIndexValid_12
      PackedExhaustionN12.level7 PackedExhaustionN12.level8 112 rows14_16 := by
  apply valid14_15.append
  simpa [rows14_15_length] using valid15_16

def rows13_16 : List Blob :=
  rows13_14 ++ rows14_16
theorem rows13_16_length :
    rows13_16.length = 24 := by
  simp [rows13_16, rows13_14_length, rows14_16_length]
theorem valid13_16 :
    ClaimedRowsValidFrom PackingCert.pairIndexValid_12
      PackedExhaustionN12.level7 PackedExhaustionN12.level8 104 rows13_16 := by
  apply valid13_14.append
  simpa [rows13_14_length] using valid14_16

def rows11_16 : List Blob :=
  rows11_13 ++ rows13_16
theorem rows11_16_length :
    rows11_16.length = 40 := by
  simp [rows11_16, rows11_13_length, rows13_16_length]
theorem valid11_16 :
    ClaimedRowsValidFrom PackingCert.pairIndexValid_12
      PackedExhaustionN12.level7 PackedExhaustionN12.level8 88 rows11_16 := by
  apply valid11_13.append
  simpa [rows11_13_length] using valid13_16

abbrev rows16_17 : List Blob := PackedExhaustionN12Step7Shard016.rows
theorem rows16_17_length :
    rows16_17.length = 8 := PackedExhaustionN12Step7Shard016.rows_length
theorem valid16_17 :
    ClaimedRowsValidFrom PackingCert.pairIndexValid_12
      PackedExhaustionN12.level7 PackedExhaustionN12.level8 128 rows16_17 :=
  PackedExhaustionN12Step7Shard016.valid

abbrev rows17_18 : List Blob := PackedExhaustionN12Step7Shard017.rows
theorem rows17_18_length :
    rows17_18.length = 8 := PackedExhaustionN12Step7Shard017.rows_length
theorem valid17_18 :
    ClaimedRowsValidFrom PackingCert.pairIndexValid_12
      PackedExhaustionN12.level7 PackedExhaustionN12.level8 136 rows17_18 :=
  PackedExhaustionN12Step7Shard017.valid

abbrev rows18_19 : List Blob := PackedExhaustionN12Step7Shard018.rows
theorem rows18_19_length :
    rows18_19.length = 8 := PackedExhaustionN12Step7Shard018.rows_length
theorem valid18_19 :
    ClaimedRowsValidFrom PackingCert.pairIndexValid_12
      PackedExhaustionN12.level7 PackedExhaustionN12.level8 144 rows18_19 :=
  PackedExhaustionN12Step7Shard018.valid

def rows17_19 : List Blob :=
  rows17_18 ++ rows18_19
theorem rows17_19_length :
    rows17_19.length = 16 := by
  simp [rows17_19, rows17_18_length, rows18_19_length]
theorem valid17_19 :
    ClaimedRowsValidFrom PackingCert.pairIndexValid_12
      PackedExhaustionN12.level7 PackedExhaustionN12.level8 136 rows17_19 := by
  apply valid17_18.append
  simpa [rows17_18_length] using valid18_19

def rows16_19 : List Blob :=
  rows16_17 ++ rows17_19
theorem rows16_19_length :
    rows16_19.length = 24 := by
  simp [rows16_19, rows16_17_length, rows17_19_length]
theorem valid16_19 :
    ClaimedRowsValidFrom PackingCert.pairIndexValid_12
      PackedExhaustionN12.level7 PackedExhaustionN12.level8 128 rows16_19 := by
  apply valid16_17.append
  simpa [rows16_17_length] using valid17_19

abbrev rows19_20 : List Blob := PackedExhaustionN12Step7Shard019.rows
theorem rows19_20_length :
    rows19_20.length = 8 := PackedExhaustionN12Step7Shard019.rows_length
theorem valid19_20 :
    ClaimedRowsValidFrom PackingCert.pairIndexValid_12
      PackedExhaustionN12.level7 PackedExhaustionN12.level8 152 rows19_20 :=
  PackedExhaustionN12Step7Shard019.valid

abbrev rows20_21 : List Blob := PackedExhaustionN12Step7Shard020.rows
theorem rows20_21_length :
    rows20_21.length = 8 := PackedExhaustionN12Step7Shard020.rows_length
theorem valid20_21 :
    ClaimedRowsValidFrom PackingCert.pairIndexValid_12
      PackedExhaustionN12.level7 PackedExhaustionN12.level8 160 rows20_21 :=
  PackedExhaustionN12Step7Shard020.valid

abbrev rows21_22 : List Blob := PackedExhaustionN12Step7Shard021.rows
theorem rows21_22_length :
    rows21_22.length = 7 := PackedExhaustionN12Step7Shard021.rows_length
theorem valid21_22 :
    ClaimedRowsValidFrom PackingCert.pairIndexValid_12
      PackedExhaustionN12.level7 PackedExhaustionN12.level8 168 rows21_22 :=
  PackedExhaustionN12Step7Shard021.valid

def rows20_22 : List Blob :=
  rows20_21 ++ rows21_22
theorem rows20_22_length :
    rows20_22.length = 15 := by
  simp [rows20_22, rows20_21_length, rows21_22_length]
theorem valid20_22 :
    ClaimedRowsValidFrom PackingCert.pairIndexValid_12
      PackedExhaustionN12.level7 PackedExhaustionN12.level8 160 rows20_22 := by
  apply valid20_21.append
  simpa [rows20_21_length] using valid21_22

def rows19_22 : List Blob :=
  rows19_20 ++ rows20_22
theorem rows19_22_length :
    rows19_22.length = 23 := by
  simp [rows19_22, rows19_20_length, rows20_22_length]
theorem valid19_22 :
    ClaimedRowsValidFrom PackingCert.pairIndexValid_12
      PackedExhaustionN12.level7 PackedExhaustionN12.level8 152 rows19_22 := by
  apply valid19_20.append
  simpa [rows19_20_length] using valid20_22

def rows16_22 : List Blob :=
  rows16_19 ++ rows19_22
theorem rows16_22_length :
    rows16_22.length = 47 := by
  simp [rows16_22, rows16_19_length, rows19_22_length]
theorem valid16_22 :
    ClaimedRowsValidFrom PackingCert.pairIndexValid_12
      PackedExhaustionN12.level7 PackedExhaustionN12.level8 128 rows16_22 := by
  apply valid16_19.append
  simpa [rows16_19_length] using valid19_22

def rows11_22 : List Blob :=
  rows11_16 ++ rows16_22
theorem rows11_22_length :
    rows11_22.length = 87 := by
  simp [rows11_22, rows11_16_length, rows16_22_length]
theorem valid11_22 :
    ClaimedRowsValidFrom PackingCert.pairIndexValid_12
      PackedExhaustionN12.level7 PackedExhaustionN12.level8 88 rows11_22 := by
  apply valid11_16.append
  simpa [rows11_16_length] using valid16_22

def rows0_22 : List Blob :=
  rows0_11 ++ rows11_22
theorem rows0_22_length :
    rows0_22.length = 175 := by
  simp [rows0_22, rows0_11_length, rows11_22_length]
theorem valid0_22 :
    ClaimedRowsValidFrom PackingCert.pairIndexValid_12
      PackedExhaustionN12.level7 PackedExhaustionN12.level8 0 rows0_22 := by
  apply valid0_11.append
  simpa [rows0_11_length] using valid11_22

abbrev rows : List Blob := rows0_22
theorem rows_length : rows.length = 175 := rows0_22_length
theorem valid : ClaimedRowsValidFrom PackingCert.pairIndexValid_12
    PackedExhaustionN12.level7 PackedExhaustionN12.level8 0 rows := valid0_22

def table : Array (Array (Option (Transition 12))) :=
  claimedTableFrom 12 rows

theorem stepValid :
    CertificateExhaustion.StepValid PackedExhaustionN12.level7.toArray
      PackedExhaustionN12.level8.toArray table := by
  apply valid.stepValid
  simpa [PackedExhaustionN12.level7, rows_length]

end Erdos76.CertificateExhaustion.Certificates.PackedExhaustionN12.Step7
