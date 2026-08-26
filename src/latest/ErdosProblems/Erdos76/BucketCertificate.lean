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
import ErdosProblems.Erdos76.CompressedCertificate

/-!
# Incidence-bucket strong certificates

The flat verifier in `LinearCertificateChecker` is intentionally simple, but
computing every edge load by scanning every term is too expensive for the
large `n = 13` bases.  A bucket certificate supplies, for each canonical edge
index, a strictly increasing list of term indices.  Every term index must
occur in the three buckets belonging to its triangle.  Extra references only
increase a bucket load, so accepting a bucket load bounded by the common
denominator is a sound upper bound for the genuine edge load.

The wire format appends `edgeCount n` buckets to each ordinary compressed
entry.  A bucket is its reference count followed by delta-coded term indices.
-/

namespace Erdos76
namespace CertificateChecker
namespace BucketCertificate

open Compressed
open PackingCert

structure Cert (n : ℕ) where
  packing : PackingCert n
  buckets : List (List ℕ)
  deriving DecidableEq

abbrev Entry (n : ℕ) := BitVec (edgeCount n) × Cert n

/-! ## Bucket decoder -/

/-- Read one strictly increasing, in-range delta-coded reference list. -/
def readRefs : ℕ →
    ℕ → Option ℕ → List Char → Option (List ℕ × List Char)
  | _, 0, _, input => some ([], input)
  | termCount, count + 1, previous, input => do
      let (delta, afterDelta) ← readVarNat input
      if previous.isSome ∧ delta = 0 then none else
      let index := previous.getD 0 + delta
      if ¬index < termCount then none else
      let (refs, rest) ← readRefs termCount count (some index) afterDelta
      some (index :: refs, rest)

/-- Read one reference bucket. -/
def readBucket (termCount : ℕ) (input : List Char) :
    Option (List ℕ × List Char) := do
  let (refCount, afterCount) ← readVarNat input
  readRefs termCount refCount none afterCount

/-- Read exactly the canonical number of edge buckets.  Four buckets are
consumed per recursive frame; this keeps a complete `n = 13` record below the
stock kernel recursion-depth limit without changing the wire format. -/
def readBuckets (termCount : ℕ) :
    ℕ → List Char → Option (List (List ℕ) × List Char)
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

/-- Decode an ordinary graph/packing entry followed by all incidence
buckets. -/
def readEntry (n : ℕ) (input : List Char) :
    Option (Entry n × List Char) := do
  let (base, afterBase) ← Compressed.readEntry n input
  let (buckets, rest) ←
    readBuckets base.2.terms.length (edgeCount n) afterBase
  some ((base.1, ⟨base.2, buckets⟩), rest)

def readEntryList (n : ℕ) :
    ℕ → List Char → Option (List (Entry n) × List Char)
  | 0, input => some ([], input)
  | count + 1, input => do
      let (entry, afterEntry) ← readEntry n input
      let (entries, rest) ← readEntryList n count afterEntry
      some (entry :: entries, rest)

def decodeEntries (n : ℕ) (payload : String) :
    Option (List (Entry n)) := do
  let (count, afterCount) ← readVarNat payload.toList
  let (decoded, rest) ← readEntryList n count afterCount
  if rest.isEmpty then some decoded else none

def entries (n : ℕ) (payload : String) : List (Entry n) :=
  (decodeEntries n payload).getD []

/-! ## Executable bucket checker -/

def numeratorAt (c : PackingCert n) (index : ℕ) : ℕ :=
  ((c.terms[index]?).map PackingTerm.numerator).getD 0

/-- Sum references through a finset.  Thus repeated references, although the
wire decoder already rejects them by strict delta coding, can never make the
semantic upper-bound argument unsound. -/
def bucketNumerator (c : PackingCert n) (refs : List ℕ) : ℕ :=
  refs.toFinset.sum (numeratorAt c)

def coversTerm (buckets : List (List ℕ))
    (index : ℕ) (q : PackingTerm n) : Bool :=
  (buckets.getD (edgeIndex q.i q.j) []).contains index &&
    (buckets.getD (edgeIndex q.i q.k) []).contains index &&
      (buckets.getD (edgeIndex q.j q.k) []).contains index

/-- Fast executable checker.  Reference bounds and strict increase are
already enforced by `readRefs`; they are nevertheless harmless to repeat in
the proposition-level soundness interface below. -/
def checkStrong (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (a : ℕ) (c : Cert n) : Bool :=
  decide (0 < c.packing.denominator) &&
    c.packing.terms.all (fun q ↦ decide (G.IsNClique 3 q.triangle)) &&
      decide (c.packing.terms.map PackingTerm.triangle).Nodup &&
        c.packing.terms.all (fun q ↦
          decide (2 * q.numerator ≤ c.packing.denominator)) &&
          decide (c.buckets.length = edgeCount n) &&
            c.packing.terms.zipIdx.all (fun indexed ↦
              coversTerm c.buckets indexed.2 indexed.1) &&
              c.buckets.all (fun refs ↦
                refs.all (fun index ↦
                  decide (index < c.packing.terms.length)) &&
                decide (bucketNumerator c.packing refs ≤
                  c.packing.denominator)) &&
                decide (c.packing.denominator * (G.edgeFinset.card - a) ≤
                  3 * c.packing.totalNumerator)

/-- Proposition reflected by the executable bucket checker. -/
def Valid (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (a : ℕ) (c : Cert n) : Prop :=
  0 < c.packing.denominator ∧
    (∀ q ∈ c.packing.terms, G.IsNClique 3 q.triangle) ∧
      (c.packing.terms.map PackingTerm.triangle).Nodup ∧
        (∀ q ∈ c.packing.terms,
          2 * q.numerator ≤ c.packing.denominator) ∧
          c.buckets.length = edgeCount n ∧
            (∀ q index, (q, index) ∈ c.packing.terms.zipIdx →
              coversTerm c.buckets index q = true) ∧
              (∀ refs ∈ c.buckets,
                (∀ index ∈ refs, index < c.packing.terms.length) ∧
                bucketNumerator c.packing refs ≤ c.packing.denominator) ∧
                c.packing.denominator * (G.edgeFinset.card - a) ≤
                  3 * c.packing.totalNumerator

@[simp] theorem checkStrong_eq_true_iff
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (a : ℕ) (c : Cert n) :
    checkStrong G a c = true ↔ Valid G a c := by
  simp [checkStrong, Valid, List.all_eq_true, and_assoc]

/-! ## Soundness of incidence upper bounds -/

/-- Inject a list of nonzero summands into a finite target set.  This small
generic lemma is the combinatorial core of bucket soundness. -/
lemma sum_map_le_finset_sum {α : Type*}
    (items : List (α × ℕ)) (S : Finset ℕ)
    (f : α × ℕ → ℕ) (g : ℕ → ℕ)
    (hnodup : (items.map Prod.snd).Nodup)
    (hvalue : ∀ p ∈ items, f p ≠ 0 → f p = g p.2)
    (hmem : ∀ p ∈ items, f p ≠ 0 → p.2 ∈ S) :
    (items.map f).sum ≤ S.sum g := by
  induction items generalizing S with
  | nil => simp
  | cons p items ih =>
      simp only [List.map_cons] at hnodup ⊢
      have hpnot : p.2 ∉ items.map Prod.snd :=
        (List.nodup_cons.mp hnodup).1
      have htailnodup : (items.map Prod.snd).Nodup :=
        (List.nodup_cons.mp hnodup).2
      by_cases hpzero : f p = 0
      · simpa [hpzero] using
          (ih S htailnodup
            (fun q hq hq0 ↦ hvalue q (by simp [hq]) hq0)
            (fun q hq hq0 ↦ hmem q (by simp [hq]) hq0))
      · have hpS : p.2 ∈ S := hmem p (by simp) hpzero
        have htailmem : ∀ q ∈ items, f q ≠ 0 → q.2 ∈ S.erase p.2 := by
          intro q hq hq0
          apply Finset.mem_erase.mpr
          constructor
          · intro hqp
            apply hpnot
            exact List.mem_map.mpr ⟨q, hq, by simpa using hqp⟩
          · exact hmem q (by simp [hq]) hq0
        have htail := ih (S.erase p.2) htailnodup
          (fun q hq hq0 ↦ hvalue q (by simp [hq]) hq0) htailmem
        calc
          f p + (items.map f).sum ≤
              g p.2 + (S.erase p.2).sum g := by
            exact Nat.add_le_add (Nat.le_of_eq (hvalue p (by simp) hpzero)) htail
          _ = S.sum g := by
            simpa [Nat.add_comm] using S.sum_erase_add g hpS

lemma mem_bucket_of_coversTerm (buckets : List (List ℕ))
    (index : ℕ) (q : PackingTerm n) (edge : ℕ)
    (hcovers : coversTerm buckets index q = true)
    (hedge : edgeIndex q.i q.j = edge ∨
      edgeIndex q.i q.k = edge ∨ edgeIndex q.j q.k = edge) :
    index ∈ buckets.getD edge [] := by
  simp [coversTerm] at hcovers
  rcases hedge with hedge | hedge | hedge
  · simpa [← hedge] using hcovers.1.1
  · simpa [← hedge] using hcovers.1.2
  · simpa [← hedge] using hcovers.2

/-- The three expected bucket references dominate the true load of one
canonical non-loop edge. -/
lemma termEdgeSum_le_bucketNumerator (hpairs : PairIndexValid n)
    {G : SimpleGraph (Fin n)} (c : Cert n)
    (hterms : ∀ q ∈ c.packing.terms, G.IsNClique 3 q.triangle)
    (hcovers : ∀ q index, (q, index) ∈ c.packing.terms.zipIdx →
      coversTerm c.buckets index q = true)
    (i j : Fin n) (hij : i ≠ j) :
    termEdgeSum c.packing.terms (edgeIndex i j) ≤
      bucketNumerator c.packing
        (c.buckets.getD (edgeIndex i j) []) := by
  let items := c.packing.terms.zipIdx
  let f : PackingTerm n × ℕ → ℕ := fun p ↦
    termEdgeEntry p.1 (edgeIndex i j)
  have hnodup : (items.map Prod.snd).Nodup := by
    dsimp [items]
    rw [List.zipIdx_map_snd]
    exact List.nodup_range'
  have hvalue : ∀ p ∈ items, f p ≠ 0 →
      f p = numeratorAt c.packing p.2 := by
    intro p hp hp0
    have hpget : c.packing.terms[p.2]? = some p.1 :=
      List.mem_zipIdx_iff_getElem?.mp hp
    have hqmem : p.1 ∈ c.packing.terms := by
      exact List.mem_of_getElem? hpget
    have hqClique := hterms p.1 hqmem
    have hnum : numeratorAt c.packing p.2 = p.1.numerator := by
      simp [numeratorAt, hpget]
    dsimp [f]
    rw [termEdgeEntry_eq_indicator hpairs p.1 hqClique i j hij]
    by_cases hedge : s(i, j) ∈ p.1.triangle.sym2
    · simp [hedge, hnum]
    · exfalso
      apply hp0
      dsimp [f]
      rw [termEdgeEntry_eq_indicator hpairs p.1 hqClique i j hij]
      simp [hedge]
  have hmem : ∀ p ∈ items, f p ≠ 0 →
      p.2 ∈ (c.buckets.getD (edgeIndex i j) []).toFinset := by
    intro p hp hp0
    apply List.mem_toFinset.mpr
    apply mem_bucket_of_coversTerm c.buckets p.2 p.1 (edgeIndex i j)
      (hcovers p.1 p.2 hp)
    dsimp [f] at hp0
    unfold termEdgeEntry at hp0
    by_cases h₁ : edgeIndex p.1.i p.1.j = edgeIndex i j <;>
      by_cases h₂ : edgeIndex p.1.i p.1.k = edgeIndex i j <;>
      by_cases h₃ : edgeIndex p.1.j p.1.k = edgeIndex i j <;>
      simp_all
  have hbound := sum_map_le_finset_sum items
    (c.buckets.getD (edgeIndex i j) []).toFinset f
    (numeratorAt c.packing) hnodup hvalue hmem
  have hmap : items.map f =
      c.packing.terms.map (fun q ↦ termEdgeEntry q (edgeIndex i j)) := by
    calc
      items.map f =
          (items.map Prod.fst).map
            (fun q ↦ termEdgeEntry q (edgeIndex i j)) := by
        rw [List.map_map]
        rfl
      _ = c.packing.terms.map
          (fun q ↦ termEdgeEntry q (edgeIndex i j)) := by
        dsimp [items]
        rw [List.zipIdx_map_fst]
  unfold termEdgeSum bucketNumerator
  rw [← hmap]
  exact hbound

/-- Bucket validity implies the original natural-number strong
specification. -/
theorem Valid.strongValid (hpairs : PairIndexValid n)
    {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    (a : ℕ) (c : Cert n) (hc : Valid G a c) :
    c.packing.StrongValid G a := by
  rcases hc with
    ⟨hden, hterms, hkeys, hhalf, hbuckets, hcovers, hcaps, hobjective⟩
  refine ⟨⟨hden, hterms, ?_⟩, hkeys, hhalf, hobjective⟩
  intro i hi j hj hadj
  have hij : i ≠ j := by
    intro hij
    subst j
    exact G.loopless.irrefl i hadj
  have hindex : edgeIndex i j < edgeCount n := hpairs.1 i j hij
  have hbindex : edgeIndex i j < c.buckets.length := by
    rw [hbuckets]
    exact hindex
  have hgetD : c.buckets.getD (edgeIndex i j) [] =
      c.buckets[edgeIndex i j] := by
    rw [List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem hbindex]
    rfl
  have hbmem : c.buckets.getD (edgeIndex i j) [] ∈ c.buckets := by
    rw [hgetD]
    exact List.getElem_mem hbindex
  have hcap := (hcaps _ hbmem).2
  calc
    c.packing.edgeNumerator s(i, j) =
        termEdgeSum c.packing.terms (edgeIndex i j) := by
      symm
      exact termEdgeSum_eq_edgeNumerator hpairs c.packing hterms i j hij
    _ ≤ bucketNumerator c.packing
        (c.buckets.getD (edgeIndex i j) []) :=
      termEdgeSum_le_bucketNumerator hpairs c hterms hcovers i j hij
    _ ≤ c.packing.denominator := hcap

/-- Semantic soundness of the fast bucket checker. -/
theorem checkStrong_sound (hpairs : PairIndexValid n)
    {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    (a : ℕ) (c : Cert n) (hc : checkStrong G a c = true) :
    HasStrongFractionalPacking G (a : ℝ) := by
  apply PackingCert.checkStrong_sound_hasStrongFractionalPacking a c.packing
  exact (PackingCert.checkStrong_eq_true_iff G a c.packing).mpr
    ((checkStrong_eq_true_iff G a c).mp hc |>.strongValid hpairs a c)

/-! ## Compact payload bridge -/

def checkStrongPayload (n a : ℕ) (payload : String) : Bool :=
  match decodeEntries n payload with
  | none => false
  | some decoded =>
      decoded.all fun entry ↦ checkStrong (graphOfBits entry.1) a entry.2

theorem checkStrongPayload_sound (n a : ℕ) (payload : String)
    (h : checkStrongPayload n a payload = true) :
    (entries n payload).all (fun entry ↦
      checkStrong (graphOfBits entry.1) a entry.2) = true := by
  cases hdecode : decodeEntries n payload with
  | none => simp [checkStrongPayload, hdecode] at h
  | some decoded => simpa [checkStrongPayload, entries, hdecode] using h

theorem checkStrongPayload_semantic (n a : ℕ) (payload : String)
    (hpairs : PairIndexValid n)
    (h : checkStrongPayload n a payload = true)
    (entry : Entry n) (hentry : entry ∈ entries n payload) :
    HasStrongFractionalPacking (graphOfBits entry.1) (a : ℝ) := by
  apply checkStrong_sound hpairs a entry.2
  exact (List.all_eq_true.mp (checkStrongPayload_sound n a payload h))
    entry hentry

/-! ## Independently checkable record shards -/

/-- Decode exactly one record, without a leading record count.  The empty
remainder condition makes record strings independently checkable and safely
concatenable by an untrusted generator. -/
def decodeRecord (n : ℕ) (record : String) : Option (Entry n) := do
  let (entry, rest) ← readEntry n record.toList
  if rest.isEmpty then some entry else none

def checkStrongRecord (n a : ℕ) (record : String) : Bool :=
  match decodeRecord n record with
  | none => false
  | some entry => checkStrong (graphOfBits entry.1) a entry.2

theorem checkStrongRecord_sound (n a : ℕ) (record : String)
    (hpairs : PairIndexValid n)
    (h : checkStrongRecord n a record = true) :
    ∃ entry : Entry n, decodeRecord n record = some entry ∧
      HasStrongFractionalPacking (graphOfBits entry.1) (a : ℝ) := by
  cases hdecode : decodeRecord n record with
  | none => simp [checkStrongRecord, hdecode] at h
  | some entry =>
      refine ⟨entry, rfl, ?_⟩
      apply checkStrong_sound hpairs a entry.2
      simpa [checkStrongRecord, hdecode] using h

/-- Proposition used to assemble independently checked record strings without
rerunning their decoders. -/
def RecordsValid (n a : ℕ) (records : List String) : Prop :=
  ∀ record ∈ records, checkStrongRecord n a record = true

theorem RecordsValid.cons {n a : ℕ} {record : String}
    {records : List String}
    (hrecord : checkStrongRecord n a record = true)
    (hrecords : RecordsValid n a records) :
    RecordsValid n a (record :: records) := by
  intro r hr
  simp only [List.mem_cons] at hr
  rcases hr with hr | hr
  · subst r
    exact hrecord
  · exact hrecords r hr

@[simp] theorem recordsValid_nil (n a : ℕ) :
    RecordsValid n a [] := by simp [RecordsValid]

end BucketCertificate
end CertificateChecker
end Erdos76
