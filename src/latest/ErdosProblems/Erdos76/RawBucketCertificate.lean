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
# Proof-free raw-array storage for incidence certificates

This bounded experiment removes the recursive string parser from the kernel
reduction path.  Triangle terms are stored as `(absolute lexicographic rank,
numerator)` pairs and buckets as arrays of term indices.  Decoding produces
the already verified `BucketCertificate.Cert`, so the mathematical soundness
bridge is reused unchanged.
-/

namespace Erdos76
namespace CertificateChecker
namespace RawBucketCertificate

open Compressed
open PackingCert

structure Cert (n : ℕ) where
  mask : BitVec (edgeCount n)
  denominator : ℕ
  terms : Array (ℕ × ℕ)
  buckets : Array (Array ℕ)
  deriving DecidableEq

def decodeTerm (n : ℕ) (raw : ℕ × ℕ) : Option (PackingTerm n) := do
  let (i, j, k) ← triangleAt? n raw.1
  some ⟨i, j, k, raw.2⟩

/-- Four-at-a-time term decoder, avoiding a recursive frame per array
element. -/
def decodeTermList (n : ℕ) :
    List (ℕ × ℕ) → Option (List (PackingTerm n))
  | [] => some []
  | [q₁] => do
      let r₁ ← decodeTerm n q₁
      some [r₁]
  | [q₁, q₂] => do
      let r₁ ← decodeTerm n q₁
      let r₂ ← decodeTerm n q₂
      some [r₁, r₂]
  | [q₁, q₂, q₃] => do
      let r₁ ← decodeTerm n q₁
      let r₂ ← decodeTerm n q₂
      let r₃ ← decodeTerm n q₃
      some [r₁, r₂, r₃]
  | q₁ :: q₂ :: q₃ :: q₄ :: rest => do
      let r₁ ← decodeTerm n q₁
      let r₂ ← decodeTerm n q₂
      let r₃ ← decodeTerm n q₃
      let r₄ ← decodeTerm n q₄
      let decoded ← decodeTermList n rest
      some (r₁ :: r₂ :: r₃ :: r₄ :: decoded)

def decode (n : ℕ) (raw : Cert n) :
    Option (BucketCertificate.Entry n) := do
  let terms ← decodeTermList n raw.terms.toList
  some (raw.mask,
    ⟨⟨raw.denominator, terms⟩, raw.buckets.toList.map Array.toList⟩)

def checkStrong (n a : ℕ) (raw : Cert n) : Bool :=
  match decode n raw with
  | none => false
  | some entry =>
      BucketCertificate.checkStrong (graphOfBits entry.1) a entry.2

theorem checkStrong_sound (n a : ℕ) (raw : Cert n)
    (hpairs : PairIndexValid n) (h : checkStrong n a raw = true) :
    ∃ entry : BucketCertificate.Entry n, decode n raw = some entry ∧
      HasStrongFractionalPacking (graphOfBits entry.1) (a : ℝ) := by
  cases hdecode : decode n raw with
  | none => simp [checkStrong, hdecode] at h
  | some entry =>
      refine ⟨entry, rfl, ?_⟩
      apply BucketCertificate.checkStrong_sound hpairs a entry.2
      simpa [checkStrong, hdecode] using h

/-- Aggregate executable check used for the 1/8/32-record scaling pilots. -/
def checkStrongArray (n a : ℕ) (records : Array (Cert n)) : Bool :=
  records.all (checkStrong n a)

theorem checkStrongArray_sound (n a : ℕ) (records : Array (Cert n))
    (h : checkStrongArray n a records = true) :
    ∀ raw ∈ records, checkStrong n a raw = true := by
  have hall : ∀ i (hi : i < records.size),
      checkStrong n a records[i] = true := by
    simpa [checkStrongArray, Array.all_eq_true] using h
  intro raw hraw
  obtain ⟨i, hi, hiraw⟩ := Array.getElem_of_mem hraw
  rw [← hiraw]
  exact hall i hi

/-- Proof-only aggregate used after each raw record has been checked in its
own ordinary reduction command. -/
def RecordsValid (n a : ℕ) (records : Array (Cert n)) : Prop :=
  ∀ raw ∈ records, checkStrong n a raw = true

theorem recordsValid_empty (n a : ℕ) :
    RecordsValid n a #[] := by simp [RecordsValid]

theorem RecordsValid.singleton {n a : ℕ} {raw : Cert n}
    (hraw : checkStrong n a raw = true) :
    RecordsValid n a #[raw] := by
  intro r hr
  have hr' : r = raw := by
    simpa using hr
  subst r
  exact hraw

/-- Hierarchical aggregate constructor; it performs no certificate
reduction. -/
theorem RecordsValid.append {n a : ℕ}
    {left right : Array (Cert n)}
    (hleft : RecordsValid n a left)
    (hright : RecordsValid n a right) :
    RecordsValid n a (left ++ right) := by
  intro raw hraw
  simp only [Array.mem_append] at hraw
  rcases hraw with hraw | hraw
  · exact hleft raw hraw
  · exact hright raw hraw

end RawBucketCertificate
end CertificateChecker
end Erdos76
