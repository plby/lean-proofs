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
import ErdosProblems.Erdos76.BucketCertificate

/-!
# Packed-natural storage for strong bucket certificates

This module is an alternative to the recursive `String.toList` data path.
Every six-bit wire digit is packed into one natural number, least-significant
digit first.  A cursor stores only the number of remaining digits and the
unconsumed quotient.  Reading one digit is therefore a remainder and division
by 64, with no recursive conversion of the complete payload.

Records are decoded and checked independently.  The `RecordsValid` interface
then assembles arbitrarily large collections from checked leaves without
performing any certificate reduction at an internal tree node.
-/

namespace Erdos76
namespace CertificateChecker
namespace PackedBucketCertificate

open Compressed
open PackingCert

/-- Number of six-bit digits in one independently reducible natural-number
chunk.  Thus every arithmetic operation is on at most 480 input bits. -/
def chunkDigits : ℕ := 80

/-- A finite sequence of six-bit digits.  Each element of `chunks` packs the
next at most `chunkDigits` digits, least-significant digit first. -/
structure Blob where
  digitCount : ℕ
  chunks : List ℕ
  deriving DecidableEq

/-- Unconsumed suffix of a packed blob. -/
structure Cursor where
  remaining : ℕ
  inChunk : ℕ
  data : ℕ
  rest : List ℕ
  deriving DecidableEq

def Blob.cursor (blob : Blob) : Cursor :=
  match blob.chunks with
  | [] => ⟨blob.digitCount, 0, 0, []⟩
  | data :: rest =>
      ⟨blob.digitCount, min chunkDigits blob.digitCount, data, rest⟩

/-- Consume one six-bit digit. -/
def readDigit : Cursor → Option (ℕ × Cursor)
  | ⟨0, _, _, _⟩ => none
  | ⟨_ + 1, 0, _, _⟩ => none
  | ⟨remaining + 1, inChunk + 1, data, rest⟩ =>
      let digit := data % 64
      let quotient := data / 64
      if inChunk = 0 then
        if quotient ≠ 0 then none else
        match remaining, rest with
        | 0, [] => some (digit, ⟨0, 0, 0, []⟩)
        | remaining + 1, next :: tail =>
            some (digit, ⟨remaining + 1,
              min chunkDigits (remaining + 1), next, tail⟩)
        | _, _ => none
      else
        some (digit, ⟨remaining, inChunk, quotient, rest⟩)

/-- Consume one little-endian base-32 varint.  The explicit fuel is bounded
by the number of remaining packed digits; on valid generated data, recursion
depth is only the number of digits in this one integer field. -/
def readVarNat : ℕ → Cursor → Option (ℕ × Cursor)
  | 0, _ => none
  | fuel + 1, input => do
      let (d, rest) ← readDigit input
      if d < 32 then
        some (d, rest)
      else
        let (tail, suffix) ← readVarNat fuel rest
        some (d - 32 + 32 * tail, suffix)

/-- Read a varint using all remaining digits as malformed-input fuel. -/
def readNat (input : Cursor) : Option (ℕ × Cursor) :=
  readVarNat input.remaining input

def readTerm (n : ℕ) (previous : Option ℕ) (input : Cursor) :
    Option (PackingTerm n × ℕ × Cursor) := do
  let (delta, afterDelta) ← readNat input
  if previous.isSome ∧ delta = 0 then none else
  let rank := previous.getD 0 + delta
  let (i, j, k) ← triangleAt? n rank
  let (numerator, rest) ← readNat afterDelta
  if numerator = 0 then none else
  some (⟨i, j, k, numerator⟩, rank, rest)

/-- Decode four packing terms per recursive frame. -/
def readTerms (n : ℕ) :
    ℕ → Option ℕ → Cursor → Option (List (PackingTerm n) × Cursor)
  | 0, _, input => some ([], input)
  | 1, previous, input => do
      let (q₁, _, rest) ← readTerm n previous input
      some ([q₁], rest)
  | 2, previous, input => do
      let (q₁, rank₁, after₁) ← readTerm n previous input
      let (q₂, _, rest) ← readTerm n (some rank₁) after₁
      some ([q₁, q₂], rest)
  | 3, previous, input => do
      let (q₁, rank₁, after₁) ← readTerm n previous input
      let (q₂, rank₂, after₂) ← readTerm n (some rank₁) after₁
      let (q₃, _, rest) ← readTerm n (some rank₂) after₂
      some ([q₁, q₂, q₃], rest)
  | count + 4, previous, input => do
      let (q₁, rank₁, after₁) ← readTerm n previous input
      let (q₂, rank₂, after₂) ← readTerm n (some rank₁) after₁
      let (q₃, rank₃, after₃) ← readTerm n (some rank₂) after₂
      let (q₄, rank₄, after₄) ← readTerm n (some rank₃) after₃
      let (terms, rest) ← readTerms n count (some rank₄) after₄
      some (q₁ :: q₂ :: q₃ :: q₄ :: terms, rest)

def readRefs : ℕ →
    ℕ → Option ℕ → Cursor → Option (List ℕ × Cursor)
  | _, 0, _, input => some ([], input)
  | termCount, count + 1, previous, input => do
      let (delta, afterDelta) ← readNat input
      if previous.isSome ∧ delta = 0 then none else
      let index := previous.getD 0 + delta
      if ¬index < termCount then none else
      let (refs, rest) ← readRefs termCount count (some index) afterDelta
      some (index :: refs, rest)

def readBucket (termCount : ℕ) (input : Cursor) :
    Option (List ℕ × Cursor) := do
  let (refCount, afterCount) ← readNat input
  readRefs termCount refCount none afterCount

/-- Decode four incidence buckets per recursive frame. -/
def readBuckets (termCount : ℕ) :
    ℕ → Cursor → Option (List (List ℕ) × Cursor)
  | 0, input => some ([], input)
  | 1, input => do
      let (r₁, rest) ← readBucket termCount input
      some ([r₁], rest)
  | 2, input => do
      let (r₁, after₁) ← readBucket termCount input
      let (r₂, rest) ← readBucket termCount after₁
      some ([r₁, r₂], rest)
  | 3, input => do
      let (r₁, after₁) ← readBucket termCount input
      let (r₂, after₂) ← readBucket termCount after₁
      let (r₃, rest) ← readBucket termCount after₂
      some ([r₁, r₂, r₃], rest)
  | count + 4, input => do
      let (r₁, after₁) ← readBucket termCount input
      let (r₂, after₂) ← readBucket termCount after₁
      let (r₃, after₃) ← readBucket termCount after₂
      let (r₄, after₄) ← readBucket termCount after₃
      let (buckets, rest) ← readBuckets termCount count after₄
      some (r₁ :: r₂ :: r₃ :: r₄ :: buckets, rest)

def readEntry (n : ℕ) (input : Cursor) :
    Option (BucketCertificate.Entry n × Cursor) := do
  let (mask, afterMask) ← readNat input
  if ¬mask < 2 ^ edgeCount n then none else
  let (denominator, afterDenominator) ← readNat afterMask
  if denominator = 0 then none else
  let (termCount, afterCount) ← readNat afterDenominator
  if n.choose 3 < termCount then none else
  let (terms, afterTerms) ← readTerms n termCount none afterCount
  let (buckets, rest) ← readBuckets termCount (edgeCount n) afterTerms
  some ((BitVec.ofNat (edgeCount n) mask,
    ⟨⟨denominator, terms⟩, buckets⟩), rest)

/-- Decode one independently packed record.  Both an exhausted digit count
and a zero residual quotient are required, rejecting truncation, trailing
digits, and data above the declared packed length. -/
def decode (n : ℕ) (blob : Blob) : Option (BucketCertificate.Entry n) := do
  let (entry, rest) ← readEntry n blob.cursor
  if rest.remaining = 0 ∧ rest.inChunk = 0 ∧ rest.data = 0 ∧
      rest.rest = [] then some entry else none

def checkStrong (n a : ℕ) (blob : Blob) : Bool :=
  match decode n blob with
  | none => false
  | some entry =>
      BucketCertificate.checkStrong (graphOfBits entry.1) a entry.2

theorem checkStrong_sound (n a : ℕ) (blob : Blob)
    (hpairs : PairIndexValid n) (h : checkStrong n a blob = true) :
    ∃ entry : BucketCertificate.Entry n, decode n blob = some entry ∧
      HasStrongFractionalPacking (graphOfBits entry.1) (a : ℝ) := by
  cases hdecode : decode n blob with
  | none => simp [checkStrong, hdecode] at h
  | some entry =>
      refine ⟨entry, rfl, ?_⟩
      apply BucketCertificate.checkStrong_sound hpairs a entry.2
      simpa [checkStrong, hdecode] using h

/-- Proof-only aggregate.  Internal assembly nodes do not decode data. -/
def RecordsValid (n a : ℕ) (records : List Blob) : Prop :=
  ∀ blob ∈ records, checkStrong n a blob = true

@[simp] theorem recordsValid_nil (n a : ℕ) :
    RecordsValid n a [] := by simp [RecordsValid]

theorem RecordsValid.cons {n a : ℕ} {blob : Blob} {records : List Blob}
    (hblob : checkStrong n a blob = true)
    (hrecords : RecordsValid n a records) :
    RecordsValid n a (blob :: records) := by
  intro b hb
  simp only [List.mem_cons] at hb
  rcases hb with rfl | hb
  · exact hblob
  · exact hrecords b hb

theorem RecordsValid.append {n a : ℕ} {left right : List Blob}
    (hleft : RecordsValid n a left) (hright : RecordsValid n a right) :
    RecordsValid n a (left ++ right) := by
  intro blob hblob
  simp only [List.mem_append] at hblob
  rcases hblob with hblob | hblob
  · exact hleft blob hblob
  · exact hright blob hblob

/-- Every leaf of a proof-only aggregate decodes to a semantically sound
strong fractional-packing certificate.  This is the bridge used by finite
classification files: hierarchy affects proof assembly only, never the
meaning of a checked record. -/
theorem RecordsValid.strongPacking_of_mem {n a : ℕ} {records : List Blob}
    (hpairs : PairIndexValid n) (hrecords : RecordsValid n a records)
    {blob : Blob} (hblob : blob ∈ records) :
    ∃ entry : BucketCertificate.Entry n, decode n blob = some entry ∧
      HasStrongFractionalPacking (graphOfBits entry.1) (a : ℝ) :=
  checkStrong_sound n a blob hpairs (hrecords blob hblob)

end PackedBucketCertificate
end CertificateChecker
end Erdos76
