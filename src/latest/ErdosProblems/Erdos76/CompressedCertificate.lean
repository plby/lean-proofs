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
import ErdosProblems.Erdos76.LinearCertificateChecker

/-!
# Compact strong-packing certificates

The large finite bases at orders `11`, `12`, and `13` are stored as strings
over the Base64 alphabet.  Each character is used directly as a six-bit digit;
there is no trusted binary or Base64 library in the verification path.  A
natural number is represented little-endian in base 32, with bit five of each
digit indicating that another digit follows.

A payload contains the following natural-number fields:

* the number of records;
* for every record, a dense graph mask, denominator, and number of terms;
* for every term, the delta of its lexicographic triangle rank and its
  numerator.

Triangle ranks refer to the lexicographic list of triples `i < j < k`.  The
decoder rejects malformed characters, truncated and trailing data, zero
denominators and numerators, non-increasing ranks, out-of-range masks and
triangle ranks, and impossible term counts.  Its output is the existing
`PackingCert` type, so all mathematical validation is still performed by the
existing `checkStrong` checker.  The compact decoder is only a data path.
-/

namespace Erdos76
namespace CertificateChecker
namespace Compressed

open PackingCert

/-- One decoded graph/certificate entry. -/
abbrev Entry (n : ℕ) := BitVec (edgeCount n) × PackingCert n

/-! ## Six-bit alphabet and natural-number decoder -/

/-- Value of a character in the standard Base64 alphabet. -/
def base64Digit (c : Char) : Option ℕ :=
  let x := c.toNat
  if 'A'.toNat ≤ x ∧ x ≤ 'Z'.toNat then
    some (x - 'A'.toNat)
  else if 'a'.toNat ≤ x ∧ x ≤ 'z'.toNat then
    some (26 + x - 'a'.toNat)
  else if '0'.toNat ≤ x ∧ x ≤ '9'.toNat then
    some (52 + x - '0'.toNat)
  else if c = '+' then some 62
  else if c = '/' then some 63
  else none

/-- Read one little-endian base-32 varint.  Digits `32,...,63` carry the
continuation bit, while digits `0,...,31` terminate the number. -/
def readVarNat : List Char → Option (ℕ × List Char)
  | [] => none
  | c :: cs => do
      let d ← base64Digit c
      if d < 32 then
        some (d, cs)
      else
        let (tail, rest) ← readVarNat cs
        some (d - 32 + 32 * tail, rest)

/-! ## Lexicographic triangle decoder -/

/-- Locate the first vertex of the `rank`-th lexicographic triple.  There are
`choose (n - i - 1) 2` triples whose first vertex is `i`.  The explicit fuel
keeps reduction depth bounded by `n`, independently of the number of
triangles. -/
def findFirstVertex (n : ℕ) : ℕ → ℕ → ℕ → Option (ℕ × ℕ)
  | _, _, 0 => none
  | rank, i, fuel + 1 =>
      let block := (n - i - 1).choose 2
      if rank < block then some (i, rank)
      else findFirstVertex n (rank - block) (i + 1) fuel

/-- Once the first vertex is fixed, locate the second and third vertices.
There are `n - j - 1` possible third vertices for a fixed second vertex `j`. -/
def findSecondVertex (n : ℕ) : ℕ → ℕ → ℕ → Option (ℕ × ℕ)
  | _, _, 0 => none
  | rank, j, fuel + 1 =>
      let block := n - j - 1
      if rank < block then some (j, j + 1 + rank)
      else findSecondVertex n (rank - block) (j + 1) fuel

/-- Direct combinatorial unranking of the lexicographic list of triples
`i < j < k`.  Unlike materializing that list with nested `flatMap`, this has
only linear reduction depth. -/
def triangleAt? (n rank : ℕ) : Option (Fin n × Fin n × Fin n) := do
  let (i, residual) ← findFirstVertex n rank 0 n
  let (j, k) ← findSecondVertex n residual (i + 1) n
  if hi : i < n then
    if hj : j < n then
      if hk : k < n then
        some (⟨i, hi⟩, ⟨j, hj⟩, ⟨k, hk⟩)
      else none
    else none
  else none

/-- Decode a fixed number of delta-ranked positive terms.  The first delta is
the absolute rank (and may be zero); every later delta must be positive. -/
def readTerms (n : ℕ) :
    ℕ → Option ℕ → List Char → Option (List (PackingTerm n) × List Char)
  | 0, _, input => some ([], input)
  | count + 1, previous, input => do
      let (delta, afterDelta) ← readVarNat input
      if previous.isSome ∧ delta = 0 then none else
      let rank := previous.getD 0 + delta
      let (i, j, k) ← triangleAt? n rank
      let (numerator, afterNumerator) ← readVarNat afterDelta
      if numerator = 0 then none else
      let (terms, rest) ← readTerms n count (some rank) afterNumerator
      some (⟨i, j, k, numerator⟩ :: terms, rest)

/-! ## Record and payload decoder -/

/-- Decode one graph and packing certificate. -/
def readEntry (n : ℕ) (input : List Char) : Option (Entry n × List Char) := do
  let (mask, afterMask) ← readVarNat input
  if ¬mask < 2 ^ edgeCount n then none else
  let (denominator, afterDenominator) ← readVarNat afterMask
  if denominator = 0 then none else
  let (termCount, afterCount) ← readVarNat afterDenominator
  if n.choose 3 < termCount then none else
  let (terms, rest) ← readTerms n termCount none afterCount
  some ((BitVec.ofNat (edgeCount n) mask, ⟨denominator, terms⟩), rest)

/-- Decode exactly `count` records. -/
def readEntryList (n : ℕ) :
    ℕ → List Char → Option (List (Entry n) × List Char)
  | 0, input => some ([], input)
  | count + 1, input => do
      let (entry, afterEntry) ← readEntry n input
      let (entries, rest) ← readEntryList n count afterEntry
      some (entry :: entries, rest)

/-- Decode a complete payload.  The leading record count and empty remainder
make truncation, surplus records, and trailing characters all failures. -/
def decodeEntries (n : ℕ) (payload : String) : Option (List (Entry n)) := do
  let (count, afterCount) ← readVarNat payload.toList
  let (entries, rest) ← readEntryList n count afterCount
  if rest.isEmpty then some entries else none

/-- Total projection used by generated data modules after the decoding check
has established that the payload is well formed. -/
def entries (n : ℕ) (payload : String) : List (Entry n) :=
  (decodeEntries n payload).getD []

/-! ## Streaming record validation -/

/-- Parse and validate exactly `count` records without first constructing a
deep list of every decoded record.  At the endpoint the input must be empty.
This is generic in the executable entry predicate, so generated data may use
the same stream parser with either the direct or blocked load checker. -/
def checkEntryStream (n : ℕ) (check : Entry n → Bool) :
    ℕ → List Char → Bool
  | 0, input => input.isEmpty
  | count + 1, input =>
      match readEntry n input with
      | none => false
      | some (entry, rest) =>
          check entry && checkEntryStream n check count rest

/-- A successful streaming check reconstructs exactly the ordinary decoded
record list, with no unconsumed input, and validates every entry. -/
theorem checkEntryStream_sound (n : ℕ) (check : Entry n → Bool)
    (count : ℕ) (input : List Char)
    (h : checkEntryStream n check count input = true) :
    ∃ decoded : List (Entry n),
      readEntryList n count input = some (decoded, []) ∧
      decoded.all check = true := by
  induction count generalizing input with
  | zero =>
      have hinput : input = [] := by
        simpa [checkEntryStream] using h
      subst input
      exact ⟨[], by simp [readEntryList], by simp⟩
  | succ count ih =>
      cases hread : readEntry n input with
      | none => simp [checkEntryStream, hread] at h
      | some result =>
          obtain ⟨entry, rest⟩ := result
          have hs : check entry = true ∧
              checkEntryStream n check count rest = true := by
            simpa [checkEntryStream, hread] using h
          have hentry : check entry = true := hs.1
          have hrest : checkEntryStream n check count rest = true := hs.2
          obtain ⟨decoded, hdecoded, hall⟩ := ih rest hrest
          refine ⟨entry :: decoded, ?_, ?_⟩
          · simp [readEntryList, hread, hdecoded]
          · simp [hentry, hall]

/-- Streaming version of the production flat numeric checker. -/
def checkStrongLinearStreamPayload (n a : ℕ) (payload : String) : Bool :=
  match readVarNat payload.toList with
  | none => false
  | some (count, input) =>
      checkEntryStream n (fun entry ↦
        entry.2.checkStrongLinear (graphOfBits entry.1) a) count input

/-- Streaming acceptance implies the same projected-entry validation theorem
as the materializing decoder. -/
theorem checkStrongLinearStreamPayload_sound (n a : ℕ) (payload : String)
    (h : checkStrongLinearStreamPayload n a payload = true) :
    (entries n payload).all (fun entry ↦
      entry.2.checkStrongLinear (graphOfBits entry.1) a) = true := by
  cases hcount : readVarNat payload.toList with
  | none => simp [checkStrongLinearStreamPayload, hcount] at h
  | some result =>
      obtain ⟨count, input⟩ := result
      have hstream : checkEntryStream n (fun entry ↦
          entry.2.checkStrongLinear (graphOfBits entry.1) a) count input = true := by
        simpa [checkStrongLinearStreamPayload, hcount] using h
      obtain ⟨decoded, hdecoded, hall⟩ :=
        checkEntryStream_sound n (fun entry ↦
          entry.2.checkStrongLinear (graphOfBits entry.1) a) count input hstream
      have hdecode : decodeEntries n payload = some decoded := by
        simp [decodeEntries, hcount, hdecoded]
      simpa [entries, hdecode] using hall

theorem checkStrongLinearStreamPayload_semantic (n a : ℕ) (payload : String)
    (hpairs : PackingCert.PairIndexValid n)
    (h : checkStrongLinearStreamPayload n a payload = true)
    (entry : Entry n) (hentry : entry ∈ entries n payload) :
    HasStrongFractionalPacking (graphOfBits entry.1) (a : ℝ) := by
  apply PackingCert.checkStrongLinear_sound hpairs a entry.2
  exact (List.all_eq_true.mp
    (checkStrongLinearStreamPayload_sound n a payload h)) entry hentry

/-! ## Reuse of the existing strong checker -/

/-- Decode a payload and run the existing strong-packing checker on every
record.  Decode failure is rejection, rather than the vacuous empty list. -/
def checkStrongPayload (n a : ℕ) (payload : String) : Bool :=
  match decodeEntries n payload with
  | none => false
  | some decoded =>
      decoded.all fun entry ↦
        entry.2.checkStrong (graphOfBits entry.1) a

/-- Linear pilot checker.  Its semantic bridge is supplied by
`checkStrongFast_sound` in `FastCertificateChecker`. -/
def checkStrongFastPayload (n a : ℕ) (payload : String) : Bool :=
  match decodeEntries n payload with
  | none => false
  | some decoded =>
      decoded.all fun entry ↦
        entry.2.checkStrongFast (graphOfBits entry.1) a

/-- Production compact checker.  The decoded sparse terms are accumulated
into one flat unordered-edge array, so each term performs exactly three
persistent-array updates. -/
def checkStrongLinearPayload (n a : ℕ) (payload : String) : Bool :=
  match decodeEntries n payload with
  | none => false
  | some decoded =>
      decoded.all fun entry ↦
        entry.2.checkStrongLinear (graphOfBits entry.1) a

/-- Acceptance by the flat compact checker validates every projected entry. -/
theorem checkStrongLinearPayload_sound (n a : ℕ) (payload : String)
    (h : checkStrongLinearPayload n a payload = true) :
    (entries n payload).all (fun entry ↦
      entry.2.checkStrongLinear (graphOfBits entry.1) a) = true := by
  cases hdecode : decodeEntries n payload with
  | none => simp [checkStrongLinearPayload, hdecode] at h
  | some decoded =>
      simpa [checkStrongLinearPayload, entries, hdecode] using h

/-- Pointwise semantic consequence of the production flat compact checker. -/
theorem checkStrongLinearPayload_semantic (n a : ℕ) (payload : String)
    (hpairs : PackingCert.PairIndexValid n)
    (h : checkStrongLinearPayload n a payload = true)
    (entry : Entry n) (hentry : entry ∈ entries n payload) :
    HasStrongFractionalPacking (graphOfBits entry.1) (a : ℝ) := by
  apply PackingCert.checkStrongLinear_sound hpairs a entry.2
  exact (List.all_eq_true.mp
    (checkStrongLinearPayload_sound n a payload h)) entry hentry

/-- Acceptance by the linear payload checker validates every projected
entry. -/
theorem checkStrongFastPayload_sound (n a : ℕ) (payload : String)
    (h : checkStrongFastPayload n a payload = true) :
    (entries n payload).all (fun entry ↦
      entry.2.checkStrongFast (graphOfBits entry.1) a) = true := by
  cases hdecode : decodeEntries n payload with
  | none => simp [checkStrongFastPayload, hdecode] at h
  | some decoded => simpa [checkStrongFastPayload, entries, hdecode] using h

/-- Pointwise semantic consequence of the linear compact checker. -/
theorem checkStrongFastPayload_semantic (n a : ℕ) (payload : String)
    (h : checkStrongFastPayload n a payload = true)
    (entry : Entry n) (hentry : entry ∈ entries n payload) :
    HasStrongFractionalPacking (graphOfBits entry.1) (a : ℝ) := by
  apply PackingCert.checkStrongFast_sound a entry.2
  exact (List.all_eq_true.mp (checkStrongFastPayload_sound n a payload h))
    entry hentry

/-- Acceptance implies that every total-projection entry passes the original
`PackingCert.checkStrong`. -/
theorem checkStrongPayload_sound (n a : ℕ) (payload : String)
    (h : checkStrongPayload n a payload = true) :
    (entries n payload).all (fun entry ↦
      entry.2.checkStrong (graphOfBits entry.1) a) = true := by
  cases hdecode : decodeEntries n payload with
  | none => simp [checkStrongPayload, hdecode] at h
  | some decoded => simpa [checkStrongPayload, entries, hdecode] using h

/-- Pointwise Boolean consequence in the form used by exhaustion bridges. -/
theorem checkStrongPayload_entry (n a : ℕ) (payload : String)
    (h : checkStrongPayload n a payload = true)
    (entry : Entry n) (hentry : entry ∈ entries n payload) :
    entry.2.checkStrong (graphOfBits entry.1) a = true := by
  exact (List.all_eq_true.mp (checkStrongPayload_sound n a payload h)) entry hentry

/-- Semantic soundness is inherited, without any new mathematical checker,
from the existing `checkStrong` bridge. -/
theorem checkStrongPayload_semantic (n a : ℕ) (payload : String)
    (h : checkStrongPayload n a payload = true)
    (entry : Entry n) (hentry : entry ∈ entries n payload) :
    HasStrongFractionalPacking (graphOfBits entry.1) (a : ℝ) :=
  PackingCert.checkStrong_sound_hasStrongFractionalPacking a entry.2
    (checkStrongPayload_entry n a payload h entry hentry)

end Compressed
end CertificateChecker
end Erdos76
