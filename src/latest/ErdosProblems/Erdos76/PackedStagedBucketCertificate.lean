/-
Copyright 2026 The Lean-Proofs Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
import ErdosProblems.Erdos76.PackedBucketCertificate
import ErdosProblems.Erdos76.StagedBucketCertificate

/-!
# Staged packed-natural strong certificates

Large records are split at bucket-row boundaries.  The graph and packing
terms form one packed blob; each small consecutive group of incidence rows is
another packed blob.  Each executable leaf stays shallow, while the soundness
theorems assemble their proposition-level facts.
-/

namespace Erdos76
namespace CertificateChecker
namespace PackedStagedBucketCertificate

open PackingCert
open Compressed
open PackedBucketCertificate
open StagedBucketCertificate

abbrev BaseEntry (n : ℕ) := StagedBucketCertificate.BaseEntry n

def readBase (n : ℕ) (input : Cursor) : Option (BaseEntry n × Cursor) := do
  let (mask, afterMask) ← readNat input
  if ¬mask < 2 ^ edgeCount n then none else
  let (denominator, afterDenominator) ← readNat afterMask
  if denominator = 0 then none else
  let (termCount, afterCount) ← readNat afterDenominator
  if n.choose 3 < termCount then none else
  let (terms, rest) ← PackedBucketCertificate.readTerms n termCount none afterCount
  some ((BitVec.ofNat (edgeCount n) mask, ⟨denominator, terms⟩), rest)

def decodeBase (n : ℕ) (blob : Blob) : Option (BaseEntry n) := do
  let (entry, rest) ← readBase n blob.cursor
  if rest.1 = 0 ∧ rest.2 = 0 then some entry else none

def decodeChunk (termCount count : ℕ) (blob : Blob) :
    Option (List (List ℕ)) := do
  let (rows, rest) ←
    PackedBucketCertificate.readBuckets termCount count blob.cursor
  if rest.1 = 0 ∧ rest.2 = 0 then some rows else none

def checkDenominator (n : ℕ) (base : Blob) : Bool :=
  match decodeBase n base with
  | none => false
  | some entry => decide (0 < entry.2.denominator)

def checkTriangles (n : ℕ) (base : Blob) : Bool :=
  match decodeBase n base with
  | none => false
  | some entry => entry.2.terms.all (fun q ↦
      decide ((graphOfBits entry.1).IsNClique 3 q.triangle))

def checkKeys (n : ℕ) (base : Blob) : Bool :=
  match decodeBase n base with
  | none => false
  | some entry => decide (entry.2.terms.map PackingTerm.triangle).Nodup

def checkHalf (n : ℕ) (base : Blob) : Bool :=
  match decodeBase n base with
  | none => false
  | some entry => entry.2.terms.all (fun q ↦
      decide (2 * q.numerator ≤ entry.2.denominator))

def checkObjective (n a : ℕ) (base : Blob) : Bool :=
  match decodeBase n base with
  | none => false
  | some entry => decide (entry.2.denominator *
      ((graphOfBits entry.1).edgeFinset.card - a) ≤
        3 * entry.2.totalNumerator)

theorem checkBaseParts_sound (n a : ℕ) (base : Blob)
    (hden : checkDenominator n base = true)
    (htri : checkTriangles n base = true)
    (hkeys : checkKeys n base = true)
    (hhalf : checkHalf n base = true)
    (hobj : checkObjective n a base = true) :
    ∃ entry : BaseEntry n, decodeBase n base = some entry ∧
      BaseValid (graphOfBits entry.1) a entry.2 := by
  cases hdecode : decodeBase n base with
  | none => simp [checkDenominator, hdecode] at hden
  | some entry =>
      refine ⟨entry, rfl, ?_⟩
      unfold BaseValid
      refine ⟨?_, ⟨?_, ⟨?_, ⟨?_, ?_⟩⟩⟩⟩
      · simpa [checkDenominator, hdecode] using hden
      · simpa [checkTriangles, hdecode] using htri
      · simpa [checkKeys, hdecode] using hkeys
      · simpa [checkHalf, hdecode] using hhalf
      · simpa [checkObjective, hdecode] using hobj

def checkRowChunk (n start count : ℕ) (base chunk : Blob) : Bool :=
  match decodeBase n base with
  | none => false
  | some entry =>
      match decodeChunk entry.2.terms.length count chunk with
      | none => false
      | some rows => decide (rows.length = count) &&
          StagedBucketCertificate.checkRowChunk entry.2 start rows

theorem checkRowChunk_sound (n start count : ℕ) (base chunk : Blob)
    (h : checkRowChunk n start count base chunk = true) :
    ∃ entry : BaseEntry n, ∃ rows : List (List ℕ),
      decodeBase n base = some entry ∧
      decodeChunk entry.2.terms.length count chunk = some rows ∧
      rows.length = count ∧ RowChunkValid entry.2 start rows := by
  cases hbase : decodeBase n base with
  | none => simp [checkRowChunk, hbase] at h
  | some entry =>
      cases hrows : decodeChunk entry.2.terms.length count chunk with
      | none => simp [checkRowChunk, hbase, hrows] at h
      | some rows =>
          refine ⟨entry, rows, rfl, hrows, ?_, ?_⟩
          · have hh : decide (rows.length = count) = true ∧
                StagedBucketCertificate.checkRowChunk
                  entry.2 start rows = true := by
              simpa [checkRowChunk, hbase, hrows] using h
            simpa using hh.1
          · exact (StagedBucketCertificate.checkRowChunk_eq_true_iff
              entry.2 start rows).mp
              (by
                have hh : decide (rows.length = count) = true ∧
                    StagedBucketCertificate.checkRowChunk
                      entry.2 start rows = true := by
                  simpa [checkRowChunk, hbase, hrows] using h
                exact hh.2)

/-- Proof-only chain of independently checked packed row chunks.  A generated
leaf uses ordinary `by decide`; the `step` constructor merely joins facts. -/
inductive CheckedChunks (n : ℕ) (base : Blob) : ℕ → Prop where
  | done : CheckedChunks n base (edgeCount n)
  | step {start count : ℕ} (chunk : Blob)
      (head : checkRowChunk n start count base chunk = true)
      (tail : CheckedChunks n base (start + count)) :
      CheckedChunks n base start

theorem CheckedChunks.sound {n : ℕ} {base : Blob} {start : ℕ}
    (h : CheckedChunks n base start) {entry : BaseEntry n}
    (hbase : decodeBase n base = some entry) :
    ChunksValidFrom entry.2 start := by
  induction h generalizing entry with
  | done => exact ChunksValidFrom.done
  | @step start count chunk head tail ih =>
      obtain ⟨entry', rows, hbase', hrows, hlength, hvalid⟩ :=
        checkRowChunk_sound n start count base chunk head
      have hentry : entry' = entry := by
        rw [hbase] at hbase'
        exact (Option.some.inj hbase').symm
      subst entry'
      apply ChunksValidFrom.step rows hvalid
      simpa only [hlength] using ih hbase

/-- Complete semantic endpoint for one staged packed record. -/
theorem checkedRecord_sound (n a : ℕ) (base : Blob)
    (hpairs : PairIndexValid n)
    (hden : checkDenominator n base = true)
    (htri : checkTriangles n base = true)
    (hkeys : checkKeys n base = true)
    (hhalf : checkHalf n base = true)
    (hobj : checkObjective n a base = true)
    (hchunks : CheckedChunks n base 0) :
    ∃ entry : BaseEntry n, decodeBase n base = some entry ∧
      HasStrongFractionalPacking (graphOfBits entry.1) (a : ℝ) := by
  obtain ⟨entry, hdecode, hbase⟩ :=
    checkBaseParts_sound n a base hden htri hkeys hhalf hobj
  refine ⟨entry, hdecode, ?_⟩
  apply PackingCert.checkStrong_sound_hasStrongFractionalPacking a entry.2
  rw [PackingCert.checkStrong_eq_true_iff]
  exact hbase.strongValidOfChunks hpairs a entry.2
    (hchunks.sound hdecode)

end PackedStagedBucketCertificate
end CertificateChecker
end Erdos76
