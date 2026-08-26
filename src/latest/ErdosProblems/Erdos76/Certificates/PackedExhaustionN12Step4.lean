/-
Copyright 2026 The Lean-Proofs Authors.
Licensed under the Apache License, Version 2.0.
-/
import ErdosProblems.Erdos76.Certificates.PackedExhaustionN12Step4Shard000
import ErdosProblems.Erdos76.Certificates.PackedExhaustionN12Step4Shard001

/-! Proof-only aggregate for the n=12 exhaustion step 4. -/
namespace Erdos76.CertificateExhaustion.Certificates.PackedExhaustionN12.Step4

open CertificateChecker
open CertificateChecker.PackedBucketCertificate
open Packed

abbrev rows0_1 : List Blob := PackedExhaustionN12Step4Shard000.rows
theorem rows0_1_length :
    rows0_1.length = 8 := PackedExhaustionN12Step4Shard000.rows_length
theorem valid0_1 :
    ClaimedRowsValidFrom PackingCert.pairIndexValid_12
      PackedExhaustionN12.level4 PackedExhaustionN12.level5 0 rows0_1 :=
  PackedExhaustionN12Step4Shard000.valid

abbrev rows1_2 : List Blob := PackedExhaustionN12Step4Shard001.rows
theorem rows1_2_length :
    rows1_2.length = 3 := PackedExhaustionN12Step4Shard001.rows_length
theorem valid1_2 :
    ClaimedRowsValidFrom PackingCert.pairIndexValid_12
      PackedExhaustionN12.level4 PackedExhaustionN12.level5 8 rows1_2 :=
  PackedExhaustionN12Step4Shard001.valid

def rows0_2 : List Blob :=
  rows0_1 ++ rows1_2
theorem rows0_2_length :
    rows0_2.length = 11 := by
  simp [rows0_2, rows0_1_length, rows1_2_length]
theorem valid0_2 :
    ClaimedRowsValidFrom PackingCert.pairIndexValid_12
      PackedExhaustionN12.level4 PackedExhaustionN12.level5 0 rows0_2 := by
  apply valid0_1.append
  simpa [rows0_1_length] using valid1_2

abbrev rows : List Blob := rows0_2
theorem rows_length : rows.length = 11 := rows0_2_length
theorem valid : ClaimedRowsValidFrom PackingCert.pairIndexValid_12
    PackedExhaustionN12.level4 PackedExhaustionN12.level5 0 rows := valid0_2

def table : Array (Array (Option (Transition 12))) :=
  claimedTableFrom 12 rows

theorem stepValid :
    CertificateExhaustion.StepValid PackedExhaustionN12.level4.toArray
      PackedExhaustionN12.level5.toArray table := by
  apply valid.stepValid
  simpa [PackedExhaustionN12.level4, rows_length]

end Erdos76.CertificateExhaustion.Certificates.PackedExhaustionN12.Step4
