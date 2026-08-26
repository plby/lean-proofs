/-
Copyright 2026 The Lean-Proofs Authors.
Licensed under the Apache License, Version 2.0.
-/
import ErdosProblems.Erdos76.Certificates.PackedExhaustionN12Step6Shard000
import ErdosProblems.Erdos76.Certificates.PackedExhaustionN12Step6Shard001
import ErdosProblems.Erdos76.Certificates.PackedExhaustionN12Step6Shard002
import ErdosProblems.Erdos76.Certificates.PackedExhaustionN12Step6Shard003
import ErdosProblems.Erdos76.Certificates.PackedExhaustionN12Step6Shard004
import ErdosProblems.Erdos76.Certificates.PackedExhaustionN12Step6Shard005
import ErdosProblems.Erdos76.Certificates.PackedExhaustionN12Step6Shard006
import ErdosProblems.Erdos76.Certificates.PackedExhaustionN12Step6Shard007
import ErdosProblems.Erdos76.Certificates.PackedExhaustionN12Step6Shard008

/-! Proof-only aggregate for the n=12 exhaustion step 6. -/
namespace Erdos76.CertificateExhaustion.Certificates.PackedExhaustionN12.Step6

open CertificateChecker
open CertificateChecker.PackedBucketCertificate
open Packed

abbrev rows0_1 : List Blob := PackedExhaustionN12Step6Shard000.rows
theorem rows0_1_length :
    rows0_1.length = 8 := PackedExhaustionN12Step6Shard000.rows_length
theorem valid0_1 :
    ClaimedRowsValidFrom PackingCert.pairIndexValid_12
      PackedExhaustionN12.level6 PackedExhaustionN12.level7 0 rows0_1 :=
  PackedExhaustionN12Step6Shard000.valid

abbrev rows1_2 : List Blob := PackedExhaustionN12Step6Shard001.rows
theorem rows1_2_length :
    rows1_2.length = 8 := PackedExhaustionN12Step6Shard001.rows_length
theorem valid1_2 :
    ClaimedRowsValidFrom PackingCert.pairIndexValid_12
      PackedExhaustionN12.level6 PackedExhaustionN12.level7 8 rows1_2 :=
  PackedExhaustionN12Step6Shard001.valid

def rows0_2 : List Blob :=
  rows0_1 ++ rows1_2
theorem rows0_2_length :
    rows0_2.length = 16 := by
  simp [rows0_2, rows0_1_length, rows1_2_length]
theorem valid0_2 :
    ClaimedRowsValidFrom PackingCert.pairIndexValid_12
      PackedExhaustionN12.level6 PackedExhaustionN12.level7 0 rows0_2 := by
  apply valid0_1.append
  simpa [rows0_1_length] using valid1_2

abbrev rows2_3 : List Blob := PackedExhaustionN12Step6Shard002.rows
theorem rows2_3_length :
    rows2_3.length = 8 := PackedExhaustionN12Step6Shard002.rows_length
theorem valid2_3 :
    ClaimedRowsValidFrom PackingCert.pairIndexValid_12
      PackedExhaustionN12.level6 PackedExhaustionN12.level7 16 rows2_3 :=
  PackedExhaustionN12Step6Shard002.valid

abbrev rows3_4 : List Blob := PackedExhaustionN12Step6Shard003.rows
theorem rows3_4_length :
    rows3_4.length = 8 := PackedExhaustionN12Step6Shard003.rows_length
theorem valid3_4 :
    ClaimedRowsValidFrom PackingCert.pairIndexValid_12
      PackedExhaustionN12.level6 PackedExhaustionN12.level7 24 rows3_4 :=
  PackedExhaustionN12Step6Shard003.valid

def rows2_4 : List Blob :=
  rows2_3 ++ rows3_4
theorem rows2_4_length :
    rows2_4.length = 16 := by
  simp [rows2_4, rows2_3_length, rows3_4_length]
theorem valid2_4 :
    ClaimedRowsValidFrom PackingCert.pairIndexValid_12
      PackedExhaustionN12.level6 PackedExhaustionN12.level7 16 rows2_4 := by
  apply valid2_3.append
  simpa [rows2_3_length] using valid3_4

def rows0_4 : List Blob :=
  rows0_2 ++ rows2_4
theorem rows0_4_length :
    rows0_4.length = 32 := by
  simp [rows0_4, rows0_2_length, rows2_4_length]
theorem valid0_4 :
    ClaimedRowsValidFrom PackingCert.pairIndexValid_12
      PackedExhaustionN12.level6 PackedExhaustionN12.level7 0 rows0_4 := by
  apply valid0_2.append
  simpa [rows0_2_length] using valid2_4

abbrev rows4_5 : List Blob := PackedExhaustionN12Step6Shard004.rows
theorem rows4_5_length :
    rows4_5.length = 8 := PackedExhaustionN12Step6Shard004.rows_length
theorem valid4_5 :
    ClaimedRowsValidFrom PackingCert.pairIndexValid_12
      PackedExhaustionN12.level6 PackedExhaustionN12.level7 32 rows4_5 :=
  PackedExhaustionN12Step6Shard004.valid

abbrev rows5_6 : List Blob := PackedExhaustionN12Step6Shard005.rows
theorem rows5_6_length :
    rows5_6.length = 8 := PackedExhaustionN12Step6Shard005.rows_length
theorem valid5_6 :
    ClaimedRowsValidFrom PackingCert.pairIndexValid_12
      PackedExhaustionN12.level6 PackedExhaustionN12.level7 40 rows5_6 :=
  PackedExhaustionN12Step6Shard005.valid

def rows4_6 : List Blob :=
  rows4_5 ++ rows5_6
theorem rows4_6_length :
    rows4_6.length = 16 := by
  simp [rows4_6, rows4_5_length, rows5_6_length]
theorem valid4_6 :
    ClaimedRowsValidFrom PackingCert.pairIndexValid_12
      PackedExhaustionN12.level6 PackedExhaustionN12.level7 32 rows4_6 := by
  apply valid4_5.append
  simpa [rows4_5_length] using valid5_6

abbrev rows6_7 : List Blob := PackedExhaustionN12Step6Shard006.rows
theorem rows6_7_length :
    rows6_7.length = 8 := PackedExhaustionN12Step6Shard006.rows_length
theorem valid6_7 :
    ClaimedRowsValidFrom PackingCert.pairIndexValid_12
      PackedExhaustionN12.level6 PackedExhaustionN12.level7 48 rows6_7 :=
  PackedExhaustionN12Step6Shard006.valid

abbrev rows7_8 : List Blob := PackedExhaustionN12Step6Shard007.rows
theorem rows7_8_length :
    rows7_8.length = 8 := PackedExhaustionN12Step6Shard007.rows_length
theorem valid7_8 :
    ClaimedRowsValidFrom PackingCert.pairIndexValid_12
      PackedExhaustionN12.level6 PackedExhaustionN12.level7 56 rows7_8 :=
  PackedExhaustionN12Step6Shard007.valid

abbrev rows8_9 : List Blob := PackedExhaustionN12Step6Shard008.rows
theorem rows8_9_length :
    rows8_9.length = 4 := PackedExhaustionN12Step6Shard008.rows_length
theorem valid8_9 :
    ClaimedRowsValidFrom PackingCert.pairIndexValid_12
      PackedExhaustionN12.level6 PackedExhaustionN12.level7 64 rows8_9 :=
  PackedExhaustionN12Step6Shard008.valid

def rows7_9 : List Blob :=
  rows7_8 ++ rows8_9
theorem rows7_9_length :
    rows7_9.length = 12 := by
  simp [rows7_9, rows7_8_length, rows8_9_length]
theorem valid7_9 :
    ClaimedRowsValidFrom PackingCert.pairIndexValid_12
      PackedExhaustionN12.level6 PackedExhaustionN12.level7 56 rows7_9 := by
  apply valid7_8.append
  simpa [rows7_8_length] using valid8_9

def rows6_9 : List Blob :=
  rows6_7 ++ rows7_9
theorem rows6_9_length :
    rows6_9.length = 20 := by
  simp [rows6_9, rows6_7_length, rows7_9_length]
theorem valid6_9 :
    ClaimedRowsValidFrom PackingCert.pairIndexValid_12
      PackedExhaustionN12.level6 PackedExhaustionN12.level7 48 rows6_9 := by
  apply valid6_7.append
  simpa [rows6_7_length] using valid7_9

def rows4_9 : List Blob :=
  rows4_6 ++ rows6_9
theorem rows4_9_length :
    rows4_9.length = 36 := by
  simp [rows4_9, rows4_6_length, rows6_9_length]
theorem valid4_9 :
    ClaimedRowsValidFrom PackingCert.pairIndexValid_12
      PackedExhaustionN12.level6 PackedExhaustionN12.level7 32 rows4_9 := by
  apply valid4_6.append
  simpa [rows4_6_length] using valid6_9

def rows0_9 : List Blob :=
  rows0_4 ++ rows4_9
theorem rows0_9_length :
    rows0_9.length = 68 := by
  simp [rows0_9, rows0_4_length, rows4_9_length]
theorem valid0_9 :
    ClaimedRowsValidFrom PackingCert.pairIndexValid_12
      PackedExhaustionN12.level6 PackedExhaustionN12.level7 0 rows0_9 := by
  apply valid0_4.append
  simpa [rows0_4_length] using valid4_9

abbrev rows : List Blob := rows0_9
theorem rows_length : rows.length = 68 := rows0_9_length
theorem valid : ClaimedRowsValidFrom PackingCert.pairIndexValid_12
    PackedExhaustionN12.level6 PackedExhaustionN12.level7 0 rows := valid0_9

def table : Array (Array (Option (Transition 12))) :=
  claimedTableFrom 12 rows

theorem stepValid :
    CertificateExhaustion.StepValid PackedExhaustionN12.level6.toArray
      PackedExhaustionN12.level7.toArray table := by
  apply valid.stepValid
  simpa [PackedExhaustionN12.level6, rows_length]

end Erdos76.CertificateExhaustion.Certificates.PackedExhaustionN12.Step6
