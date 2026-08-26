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
# Cursor-based byte decoder for compact bucket certificates

This decoder reads the same six-bit alphabet as `CompressedCertificate`, but
indexes a `ByteArray` by a natural cursor.  It never constructs the full list
of input characters or copies an unconsumed suffix.  Decoding still produces
the verified `BucketCertificate.Entry`, so no new mathematical checker is
trusted.
-/

namespace Erdos76
namespace CertificateChecker
namespace ByteBucketCertificate

open Compressed
open PackingCert

def base64ByteDigit (b : UInt8) : Option ℕ :=
  let x := b.toNat
  if 65 ≤ x ∧ x ≤ 90 then some (x - 65)
  else if 97 ≤ x ∧ x ≤ 122 then some (26 + x - 97)
  else if 48 ≤ x ∧ x ≤ 57 then some (52 + x - 48)
  else if x = 43 then some 62
  else if x = 47 then some 63
  else none

/-- Cursor-based varint reader.  Fuel is bounded by the remaining byte count. -/
def readVarNatAt (input : ByteArray) :
    ℕ → ℕ → Option (ℕ × ℕ)
  | _, 0 => none
  | pos, fuel + 1 => do
      if h : pos < input.size then
        let d ← base64ByteDigit input[pos]
        if d < 32 then some (d, pos + 1)
        else
          let (tail, next) ← readVarNatAt input (pos + 1) fuel
          some (d - 32 + 32 * tail, next)
      else none

def readVar (input : ByteArray) (pos : ℕ) : Option (ℕ × ℕ) :=
  readVarNatAt input pos (input.size - pos)

def readTermsAt (n : ℕ) (input : ByteArray) :
    ℕ → Option ℕ → ℕ → Option (List (PackingTerm n) × ℕ)
  | 0, _, pos => some ([], pos)
  | count + 1, previous, pos => do
      let (delta, afterDelta) ← readVar input pos
      if previous.isSome ∧ delta = 0 then none else
      let rank := previous.getD 0 + delta
      let (i, j, k) ← triangleAt? n rank
      let (numerator, afterNumerator) ← readVar input afterDelta
      if numerator = 0 then none else
      let (terms, next) ←
        readTermsAt n input count (some rank) afterNumerator
      some (⟨i, j, k, numerator⟩ :: terms, next)

def readRefsAt (termCount : ℕ) (input : ByteArray) :
    ℕ → Option ℕ → ℕ → Option (List ℕ × ℕ)
  | 0, _, pos => some ([], pos)
  | count + 1, previous, pos => do
      let (delta, afterDelta) ← readVar input pos
      if previous.isSome ∧ delta = 0 then none else
      let index := previous.getD 0 + delta
      if ¬index < termCount then none else
      let (refs, next) ←
        readRefsAt termCount input count (some index) afterDelta
      some (index :: refs, next)

def readBucketAt (termCount : ℕ) (input : ByteArray) (pos : ℕ) :
    Option (List ℕ × ℕ) := do
  let (refCount, afterCount) ← readVar input pos
  readRefsAt termCount input refCount none afterCount

/-- Four buckets per recursive frame. -/
def readBucketsAt (termCount : ℕ) (input : ByteArray) :
    ℕ → ℕ → Option (List (List ℕ) × ℕ)
  | 0, pos => some ([], pos)
  | 1, pos => do
      let (r₁, next) ← readBucketAt termCount input pos
      some ([r₁], next)
  | 2, pos => do
      let (r₁, p₁) ← readBucketAt termCount input pos
      let (r₂, next) ← readBucketAt termCount input p₁
      some ([r₁, r₂], next)
  | 3, pos => do
      let (r₁, p₁) ← readBucketAt termCount input pos
      let (r₂, p₂) ← readBucketAt termCount input p₁
      let (r₃, next) ← readBucketAt termCount input p₂
      some ([r₁, r₂, r₃], next)
  | count + 4, pos => do
      let (r₁, p₁) ← readBucketAt termCount input pos
      let (r₂, p₂) ← readBucketAt termCount input p₁
      let (r₃, p₃) ← readBucketAt termCount input p₂
      let (r₄, p₄) ← readBucketAt termCount input p₃
      let (rest, next) ← readBucketsAt termCount input count p₄
      some (r₁ :: r₂ :: r₃ :: r₄ :: rest, next)

def decodeRecord (n : ℕ) (record : String) :
    Option (BucketCertificate.Entry n) := do
  let input := record.toUTF8
  let (mask, afterMask) ← readVar input 0
  if ¬mask < 2 ^ edgeCount n then none else
  let (denominator, afterDenominator) ← readVar input afterMask
  if denominator = 0 then none else
  let (termCount, afterCount) ← readVar input afterDenominator
  if n.choose 3 < termCount then none else
  let (terms, afterTerms) ← readTermsAt n input termCount none afterCount
  let (buckets, next) ←
    readBucketsAt termCount input (edgeCount n) afterTerms
  if next = input.size then
    some (BitVec.ofNat (edgeCount n) mask,
      ⟨⟨denominator, terms⟩, buckets⟩)
  else none

def checkStrongRecord (n a : ℕ) (record : String) : Bool :=
  match decodeRecord n record with
  | none => false
  | some entry =>
      BucketCertificate.checkStrong (graphOfBits entry.1) a entry.2

theorem checkStrongRecord_sound (n a : ℕ) (record : String)
    (hpairs : PairIndexValid n)
    (h : checkStrongRecord n a record = true) :
    ∃ entry : BucketCertificate.Entry n,
      decodeRecord n record = some entry ∧
      HasStrongFractionalPacking (graphOfBits entry.1) (a : ℝ) := by
  cases hdecode : decodeRecord n record with
  | none => simp [checkStrongRecord, hdecode] at h
  | some entry =>
      refine ⟨entry, rfl, ?_⟩
      apply BucketCertificate.checkStrong_sound hpairs a entry.2
      simpa [checkStrongRecord, hdecode] using h

end ByteBucketCertificate
end CertificateChecker
end Erdos76
