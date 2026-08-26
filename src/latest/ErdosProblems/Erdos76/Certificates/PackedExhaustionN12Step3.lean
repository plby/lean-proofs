/-
Copyright 2026 The Lean-Proofs Authors.
Licensed under the Apache License, Version 2.0.
-/
import ErdosProblems.Erdos76.Certificates.PackedExhaustionN12Step3Shard000

/-! Proof-only aggregate for the n=12 exhaustion step 3. -/
namespace Erdos76.CertificateExhaustion.Certificates.PackedExhaustionN12.Step3

open CertificateChecker
open CertificateChecker.PackedBucketCertificate
open Packed

abbrev rows0_1 : List Blob := PackedExhaustionN12Step3Shard000.rows
theorem rows0_1_length :
    rows0_1.length = 5 := PackedExhaustionN12Step3Shard000.rows_length
theorem valid0_1 :
    ClaimedRowsValidFrom PackingCert.pairIndexValid_12
      PackedExhaustionN12.level3 PackedExhaustionN12.level4 0 rows0_1 :=
  PackedExhaustionN12Step3Shard000.valid

abbrev rows : List Blob := rows0_1
theorem rows_length : rows.length = 5 := rows0_1_length
theorem valid : ClaimedRowsValidFrom PackingCert.pairIndexValid_12
    PackedExhaustionN12.level3 PackedExhaustionN12.level4 0 rows := valid0_1

def table : Array (Array (Option (Transition 12))) :=
  claimedTableFrom 12 rows

theorem stepValid :
    CertificateExhaustion.StepValid PackedExhaustionN12.level3.toArray
      PackedExhaustionN12.level4.toArray table := by
  apply valid.stepValid
  simpa [PackedExhaustionN12.level3, rows_length]

end Erdos76.CertificateExhaustion.Certificates.PackedExhaustionN12.Step3
