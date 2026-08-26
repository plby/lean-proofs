/-
Copyright 2026 The Lean-Proofs Authors.
Licensed under the Apache License, Version 2.0.
-/
import ErdosProblems.Erdos76.Certificates.PairIndexN11
import ErdosProblems.Erdos76.Certificates.StrongPackedBucketN11Pilot32
import ErdosProblems.Erdos76.Certificates.StrongPackedBucketN11Pilot172Shard1
import ErdosProblems.Erdos76.Certificates.StrongPackedBucketN11Pilot172Shard2
import ErdosProblems.Erdos76.Certificates.StrongPackedBucketN11Pilot172Shard3
import ErdosProblems.Erdos76.Certificates.StrongPackedBucketN11Pilot172Shard4
import ErdosProblems.Erdos76.Certificates.StrongPackedBucketN11Pilot172Shard5

/-!
# Complete 172-record packed-certificate scaling pilot

The semantic check for every record occurs in an independent leaf theorem.
This module joins those leaves by proof-only `RecordsValid.append` nodes and
exports the sound strong-fractional-packing consequence for every member.
-/

namespace Erdos76.CertificateChecker.Certificates.StrongPackedBucketN11Pilot172

open PackedBucketCertificate

abbrev shard0Records : List Blob := StrongPackedBucketN11Pilot32.records
abbrev shard1Records : List Blob := StrongPackedBucketN11Pilot172Shard1.records
abbrev shard2Records : List Blob := StrongPackedBucketN11Pilot172Shard2.records
abbrev shard3Records : List Blob := StrongPackedBucketN11Pilot172Shard3.records
abbrev shard4Records : List Blob := StrongPackedBucketN11Pilot172Shard4.records
abbrev shard5Records : List Blob := StrongPackedBucketN11Pilot172Shard5.records

def records0_64 : List Blob := shard0Records ++ shard1Records
theorem valid0_64 : RecordsValid 11 0 records0_64 :=
  StrongPackedBucketN11Pilot32.valid.append
    StrongPackedBucketN11Pilot172Shard1.valid

def records64_128 : List Blob := shard2Records ++ shard3Records
theorem valid64_128 : RecordsValid 11 0 records64_128 :=
  StrongPackedBucketN11Pilot172Shard2.valid.append
    StrongPackedBucketN11Pilot172Shard3.valid

def records128_172 : List Blob := shard4Records ++ shard5Records
theorem valid128_172 : RecordsValid 11 0 records128_172 :=
  StrongPackedBucketN11Pilot172Shard4.valid.append
    StrongPackedBucketN11Pilot172Shard5.valid

def records0_128 : List Blob := records0_64 ++ records64_128
theorem valid0_128 : RecordsValid 11 0 records0_128 :=
  valid0_64.append valid64_128

def records : List Blob := records0_128 ++ records128_172

/-- All 172 independently packed records pass the kernel-reduced checker. -/
theorem valid : RecordsValid 11 0 records :=
  valid0_128.append valid128_172

/-- Semantic soundness of any checked leaf, independently of the proof-tree
sharding used to assemble the 172-record collection. -/
theorem strongPacking_of_mem {blob : Blob} (hblob : blob ∈ records) :
    ∃ entry : BucketCertificate.Entry 11, decode 11 blob = some entry ∧
      HasStrongFractionalPacking (graphOfBits entry.1) (0 : ℝ) := by
  simpa only [Nat.cast_zero] using
    valid.strongPacking_of_mem PackingCert.pairIndexValid_11 hblob

end Erdos76.CertificateChecker.Certificates.StrongPackedBucketN11Pilot172
