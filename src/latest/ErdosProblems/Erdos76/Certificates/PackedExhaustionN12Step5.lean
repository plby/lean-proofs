/-
Copyright 2026 The Lean-Proofs Authors.
Licensed under the Apache License, Version 2.0.
-/
import ErdosProblems.Erdos76.Certificates.PackedExhaustionN12Step5Shard000
import ErdosProblems.Erdos76.Certificates.PackedExhaustionN12Step5Shard001
import ErdosProblems.Erdos76.Certificates.PackedExhaustionN12Step5Shard002
import ErdosProblems.Erdos76.Certificates.PackedExhaustionN12Step5Shard003

/-! Proof-only aggregate for the n=12 exhaustion step 5. -/
namespace Erdos76.CertificateExhaustion.Certificates.PackedExhaustionN12.Step5

open CertificateChecker
open CertificateChecker.PackedBucketCertificate
open Packed

abbrev rows0_1 : List Blob := PackedExhaustionN12Step5Shard000.rows
theorem rows0_1_length :
    rows0_1.length = 8 := PackedExhaustionN12Step5Shard000.rows_length
theorem valid0_1 :
    ClaimedRowsValidFrom PackingCert.pairIndexValid_12
      PackedExhaustionN12.level5 PackedExhaustionN12.level6 0 rows0_1 :=
  PackedExhaustionN12Step5Shard000.valid

abbrev rows1_2 : List Blob := PackedExhaustionN12Step5Shard001.rows
theorem rows1_2_length :
    rows1_2.length = 8 := PackedExhaustionN12Step5Shard001.rows_length
theorem valid1_2 :
    ClaimedRowsValidFrom PackingCert.pairIndexValid_12
      PackedExhaustionN12.level5 PackedExhaustionN12.level6 8 rows1_2 :=
  PackedExhaustionN12Step5Shard001.valid

def rows0_2 : List Blob :=
  rows0_1 ++ rows1_2
theorem rows0_2_length :
    rows0_2.length = 16 := by
  simp [rows0_2, rows0_1_length, rows1_2_length]
theorem valid0_2 :
    ClaimedRowsValidFrom PackingCert.pairIndexValid_12
      PackedExhaustionN12.level5 PackedExhaustionN12.level6 0 rows0_2 := by
  apply valid0_1.append
  simpa [rows0_1_length] using valid1_2

abbrev rows2_3 : List Blob := PackedExhaustionN12Step5Shard002.rows
theorem rows2_3_length :
    rows2_3.length = 8 := PackedExhaustionN12Step5Shard002.rows_length
theorem valid2_3 :
    ClaimedRowsValidFrom PackingCert.pairIndexValid_12
      PackedExhaustionN12.level5 PackedExhaustionN12.level6 16 rows2_3 :=
  PackedExhaustionN12Step5Shard002.valid

abbrev rows3_4 : List Blob := PackedExhaustionN12Step5Shard003.rows
theorem rows3_4_length :
    rows3_4.length = 2 := PackedExhaustionN12Step5Shard003.rows_length
theorem valid3_4 :
    ClaimedRowsValidFrom PackingCert.pairIndexValid_12
      PackedExhaustionN12.level5 PackedExhaustionN12.level6 24 rows3_4 :=
  PackedExhaustionN12Step5Shard003.valid

def rows2_4 : List Blob :=
  rows2_3 ++ rows3_4
theorem rows2_4_length :
    rows2_4.length = 10 := by
  simp [rows2_4, rows2_3_length, rows3_4_length]
theorem valid2_4 :
    ClaimedRowsValidFrom PackingCert.pairIndexValid_12
      PackedExhaustionN12.level5 PackedExhaustionN12.level6 16 rows2_4 := by
  apply valid2_3.append
  simpa [rows2_3_length] using valid3_4

def rows0_4 : List Blob :=
  rows0_2 ++ rows2_4
theorem rows0_4_length :
    rows0_4.length = 26 := by
  simp [rows0_4, rows0_2_length, rows2_4_length]
theorem valid0_4 :
    ClaimedRowsValidFrom PackingCert.pairIndexValid_12
      PackedExhaustionN12.level5 PackedExhaustionN12.level6 0 rows0_4 := by
  apply valid0_2.append
  simpa [rows0_2_length] using valid2_4

abbrev rows : List Blob := rows0_4
theorem rows_length : rows.length = 26 := rows0_4_length
theorem valid : ClaimedRowsValidFrom PackingCert.pairIndexValid_12
    PackedExhaustionN12.level5 PackedExhaustionN12.level6 0 rows := valid0_4

def table : Array (Array (Option (Transition 12))) :=
  claimedTableFrom 12 rows

theorem stepValid :
    CertificateExhaustion.StepValid PackedExhaustionN12.level5.toArray
      PackedExhaustionN12.level6.toArray table := by
  apply valid.stepValid
  simpa [PackedExhaustionN12.level5, rows_length]

end Erdos76.CertificateExhaustion.Certificates.PackedExhaustionN12.Step5
