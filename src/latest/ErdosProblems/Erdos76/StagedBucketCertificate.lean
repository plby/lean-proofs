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
import ErdosProblems.Erdos76.ByteBucketCertificate

/-!
# Three-phase compact bucket certificates

One full compact record still saturates the stock reduction depth.  This
module separates it into a base term string and two independently checked
bucket-row strings.  The phase propositions are assembled proof-theoretically;
the kernel never reduces all three parsers in one `decide` call.
-/

namespace Erdos76
namespace CertificateChecker
namespace StagedBucketCertificate

open Compressed
open PackingCert
open ByteBucketCertificate

abbrev BaseEntry (n : ℕ) := BitVec (edgeCount n) × PackingCert n

def decodeBase (n : ℕ) (payload : String) : Option (BaseEntry n) := do
  let input := payload.toUTF8
  let (mask, afterMask) ← readVar input 0
  if ¬mask < 2 ^ edgeCount n then none else
  let (denominator, afterDenominator) ← readVar input afterMask
  if denominator = 0 then none else
  let (termCount, afterCount) ← readVar input afterDenominator
  if n.choose 3 < termCount then none else
  let (terms, next) ← readTermsAt n input termCount none afterCount
  if next = input.size then
    some (BitVec.ofNat (edgeCount n) mask, ⟨denominator, terms⟩)
  else none

def decodeChunk (termCount count : ℕ) (payload : String) :
    Option (List (List ℕ)) := do
  let input := payload.toUTF8
  let (rows, next) ← readBucketsAt termCount input count 0
  if next = input.size then some rows else none

def BaseValid (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (a : ℕ) (c : PackingCert n) : Prop :=
  0 < c.denominator ∧
    (∀ q ∈ c.terms, G.IsNClique 3 q.triangle) ∧
      (c.terms.map PackingTerm.triangle).Nodup ∧
        (∀ q ∈ c.terms, 2 * q.numerator ≤ c.denominator) ∧
          c.denominator * (G.edgeFinset.card - a) ≤ 3 * c.totalNumerator

def checkBase (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (a : ℕ) (c : PackingCert n) : Bool :=
  decide (0 < c.denominator) &&
    c.terms.all (fun q ↦ decide (G.IsNClique 3 q.triangle)) &&
      decide (c.terms.map PackingTerm.triangle).Nodup &&
        c.terms.all (fun q ↦ decide (2 * q.numerator ≤ c.denominator)) &&
          decide (c.denominator * (G.edgeFinset.card - a) ≤
            3 * c.totalNumerator)

@[simp] theorem checkBase_eq_true_iff
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (a : ℕ) (c : PackingCert n) :
    checkBase G a c = true ↔ BaseValid G a c := by
  simp [checkBase, BaseValid, List.all_eq_true, and_assoc]

/-! The base predicate is deliberately exposed in five small pieces.  A
single conjunction is convenient propositionally, but normalizing it together
with the decoder exceeds the stock recursion-depth limit for some production
records. -/

def checkDenominatorRecord (n : ℕ) (base : String) : Bool :=
  match decodeBase n base with
  | none => false
  | some entry => decide (0 < entry.2.denominator)

def checkTrianglesRecord (n : ℕ) (base : String) : Bool :=
  match decodeBase n base with
  | none => false
  | some entry => entry.2.terms.all (fun q ↦
      decide ((graphOfBits entry.1).IsNClique 3 q.triangle))

def checkKeysRecord (n : ℕ) (base : String) : Bool :=
  match decodeBase n base with
  | none => false
  | some entry => decide (entry.2.terms.map PackingTerm.triangle).Nodup

def checkHalfRecord (n : ℕ) (base : String) : Bool :=
  match decodeBase n base with
  | none => false
  | some entry => entry.2.terms.all (fun q ↦
      decide (2 * q.numerator ≤ entry.2.denominator))

def checkObjectiveRecord (n a : ℕ) (base : String) : Bool :=
  match decodeBase n base with
  | none => false
  | some entry => decide (entry.2.denominator *
      ((graphOfBits entry.1).edgeFinset.card - a) ≤
        3 * entry.2.totalNumerator)

/-- Five independently reduced base checks reconstruct the proposition-level
base certificate without rerunning a combined Boolean conjunction. -/
theorem checkBaseParts_sound (n a : ℕ) (base : String)
    (hden : checkDenominatorRecord n base = true)
    (htri : checkTrianglesRecord n base = true)
    (hkeys : checkKeysRecord n base = true)
    (hhalf : checkHalfRecord n base = true)
    (hobj : checkObjectiveRecord n a base = true) :
    ∃ entry : BaseEntry n, decodeBase n base = some entry ∧
      BaseValid (graphOfBits entry.1) a entry.2 := by
  cases hdecode : decodeBase n base with
  | none => simp [checkDenominatorRecord, hdecode] at hden
  | some entry =>
      refine ⟨entry, rfl, ?_⟩
      unfold BaseValid
      refine ⟨?_, ⟨?_, ⟨?_, ⟨?_, ?_⟩⟩⟩⟩
      · simpa [checkDenominatorRecord, hdecode] using hden
      · simpa [checkTrianglesRecord, hdecode] using htri
      · simpa [checkKeysRecord, hdecode] using hkeys
      · simpa [checkHalfRecord, hdecode] using hhalf
      · simpa [checkObjectiveRecord, hdecode] using hobj

def coversEdge (rows : List (List ℕ)) (start edge index : ℕ) : Bool :=
  if start ≤ edge ∧ edge < start + rows.length then
    (rows.getD (edge - start) []).contains index
  else true

def coversTerm (rows : List (List ℕ)) (start index : ℕ)
    (q : PackingTerm n) : Bool :=
  coversEdge rows start (edgeIndex q.i q.j) index &&
    coversEdge rows start (edgeIndex q.i q.k) index &&
      coversEdge rows start (edgeIndex q.j q.k) index

def ChunkValid (c : PackingCert n) (start : ℕ)
    (rows : List (List ℕ)) : Prop :=
  start + rows.length ≤ edgeCount n ∧
    (∀ q index, (q, index) ∈ c.terms.zipIdx →
      coversTerm rows start index q = true) ∧
      ∀ refs ∈ rows,
        (∀ index ∈ refs, index < c.terms.length) ∧
          BucketCertificate.bucketNumerator c refs ≤ c.denominator

def checkChunk (c : PackingCert n) (start : ℕ)
    (rows : List (List ℕ)) : Bool :=
  decide (start + rows.length ≤ edgeCount n) &&
    c.terms.zipIdx.all (fun indexed ↦
      coversTerm rows start indexed.2 indexed.1) &&
      rows.all (fun refs ↦
        refs.all (fun index ↦ decide (index < c.terms.length)) &&
          decide (BucketCertificate.bucketNumerator c refs ≤ c.denominator))

@[simp] theorem checkChunk_eq_true_iff (c : PackingCert n)
    (start : ℕ) (rows : List (List ℕ)) :
    checkChunk c start rows = true ↔ ChunkValid c start rows := by
  simp [checkChunk, ChunkValid, List.all_eq_true, and_assoc]

/-! ## Shallow row chunks -/

/-- A single bucket row must contain the index of every term using its edge.
The implication form avoids looking up any of the other rows. -/
def RowValid (c : PackingCert n) (edge : ℕ) (refs : List ℕ) : Prop :=
  (∀ q index, (q, index) ∈ c.terms.zipIdx →
    (edgeIndex q.i q.j = edge ∨ edgeIndex q.i q.k = edge ∨
      edgeIndex q.j q.k = edge) → index ∈ refs) ∧
    (∀ index ∈ refs, index < c.terms.length) ∧
      BucketCertificate.bucketNumerator c refs ≤ c.denominator

def checkRow (c : PackingCert n) (edge : ℕ) (refs : List ℕ) : Bool :=
  c.terms.zipIdx.all (fun indexed ↦
    if edgeIndex indexed.1.i indexed.1.j = edge ∨
        edgeIndex indexed.1.i indexed.1.k = edge ∨
        edgeIndex indexed.1.j indexed.1.k = edge then
      refs.contains indexed.2
    else true) &&
    refs.all (fun index ↦ decide (index < c.terms.length)) &&
      decide (BucketCertificate.bucketNumerator c refs ≤ c.denominator)

@[simp] theorem checkRow_eq_true_iff (c : PackingCert n)
    (edge : ℕ) (refs : List ℕ) :
    checkRow c edge refs = true ↔ RowValid c edge refs := by
  constructor
  · intro h
    simp only [checkRow, Bool.and_eq_true] at h
    refine ⟨?_, ?_, ?_⟩
    · intro q index hmem hedge
      have hcovers := List.all_eq_true.mp h.1.1 (q, index) hmem
      simp only [if_pos hedge] at hcovers
      simpa using hcovers
    · intro index hmem
      have hbound := List.all_eq_true.mp h.1.2 index hmem
      simpa using hbound
    · simpa using h.2
  · rintro ⟨hcovers, hbounds, hcap⟩
    simp only [checkRow, Bool.and_eq_true]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · apply List.all_eq_true.mpr
      intro indexed hmem
      by_cases hedge : edgeIndex indexed.1.i indexed.1.j = edge ∨
          edgeIndex indexed.1.i indexed.1.k = edge ∨
          edgeIndex indexed.1.j indexed.1.k = edge
      · simp only [if_pos hedge]
        simpa using hcovers indexed.1 indexed.2 hmem hedge
      · simp only [if_neg hedge]
    · apply List.all_eq_true.mpr
      intro index hmem
      simpa using hbounds index hmem
    · simpa using hcap

def RowChunkValid (c : PackingCert n) (start : ℕ)
    (rows : List (List ℕ)) : Prop :=
  start + rows.length ≤ edgeCount n ∧
    ∀ refs index, (refs, index) ∈ rows.zipIdx →
      RowValid c (start + index) refs

def checkRowChunk (c : PackingCert n) (start : ℕ)
    (rows : List (List ℕ)) : Bool :=
  decide (start + rows.length ≤ edgeCount n) &&
    rows.zipIdx.all (fun indexed ↦
      checkRow c (start + indexed.2) indexed.1)

@[simp] theorem checkRowChunk_eq_true_iff (c : PackingCert n)
    (start : ℕ) (rows : List (List ℕ)) :
    checkRowChunk c start rows = true ↔ RowChunkValid c start rows := by
  simp [checkRowChunk, RowChunkValid, List.all_eq_true, and_assoc]

def checkBaseRecord (n a : ℕ) (base : String) : Bool :=
  match decodeBase n base with
  | none => false
  | some entry => checkBase (graphOfBits entry.1) a entry.2

def checkChunkRecord (n start count : ℕ)
    (base chunk : String) : Bool :=
  match decodeBase n base with
  | none => false
  | some entry =>
      match decodeChunk entry.2.terms.length count chunk with
      | none => false
      | some rows => checkChunk entry.2 start rows

theorem checkBaseRecord_sound (n a : ℕ) (base : String)
    (h : checkBaseRecord n a base = true) :
    ∃ entry : BaseEntry n, decodeBase n base = some entry ∧
      BaseValid (graphOfBits entry.1) a entry.2 := by
  cases hdecode : decodeBase n base with
  | none => simp [checkBaseRecord, hdecode] at h
  | some entry =>
      refine ⟨entry, rfl, ?_⟩
      exact (checkBase_eq_true_iff (graphOfBits entry.1) a entry.2).mp
        (by simpa [checkBaseRecord, hdecode] using h)

theorem checkChunkRecord_sound (n start count : ℕ)
    (base chunk : String) (h : checkChunkRecord n start count base chunk = true) :
    ∃ entry : BaseEntry n, ∃ rows : List (List ℕ),
      decodeBase n base = some entry ∧
      decodeChunk entry.2.terms.length count chunk = some rows ∧
      ChunkValid entry.2 start rows := by
  cases hbase : decodeBase n base with
  | none => simp [checkChunkRecord, hbase] at h
  | some entry =>
      cases hrows : decodeChunk entry.2.terms.length count chunk with
      | none => simp [checkChunkRecord, hbase, hrows] at h
      | some rows =>
          refine ⟨entry, rows, rfl, hrows, ?_⟩
          exact (checkChunk_eq_true_iff entry.2 start rows).mp
            (by simpa [checkChunkRecord, hbase, hrows] using h)

/-- Independently decode and validate a small consecutive collection of
bucket rows.  The explicit length check is what lets checked chunks tile the
whole canonical edge range propositionally. -/
def checkRowChunkRecord (n start count : ℕ)
    (base chunk : String) : Bool :=
  match decodeBase n base with
  | none => false
  | some entry =>
      match decodeChunk entry.2.terms.length count chunk with
      | none => false
      | some rows => decide (rows.length = count) &&
          checkRowChunk entry.2 start rows

theorem checkRowChunkRecord_sound (n start count : ℕ)
    (base chunk : String)
    (h : checkRowChunkRecord n start count base chunk = true) :
    ∃ entry : BaseEntry n, ∃ rows : List (List ℕ),
      decodeBase n base = some entry ∧
      decodeChunk entry.2.terms.length count chunk = some rows ∧
      rows.length = count ∧ RowChunkValid entry.2 start rows := by
  cases hbase : decodeBase n base with
  | none => simp [checkRowChunkRecord, hbase] at h
  | some entry =>
      cases hrows : decodeChunk entry.2.terms.length count chunk with
      | none => simp [checkRowChunkRecord, hbase, hrows] at h
      | some rows =>
          refine ⟨entry, rows, rfl, hrows, ?_, ?_⟩
          · have hh : decide (rows.length = count) = true ∧
                checkRowChunk entry.2 start rows = true := by
              simpa [checkRowChunkRecord, hbase, hrows] using h
            simpa using hh.1
          · exact (checkRowChunk_eq_true_iff entry.2 start rows).mp
              (by
                have hh : decide (rows.length = count) = true ∧
                    checkRowChunk entry.2 start rows = true := by
                  simpa [checkRowChunkRecord, hbase, hrows] using h
                exact hh.2)

/-! ## Proposition-only assembly of row chunks -/

/-- One valid incidence row dominates the genuine load of its canonical
edge. -/
lemma termEdgeSum_le_row (hpairs : PairIndexValid n)
    {G : SimpleGraph (Fin n)} (c : PackingCert n)
    (hterms : ∀ q ∈ c.terms, G.IsNClique 3 q.triangle)
    (edge : ℕ) (refs : List ℕ) (hrow : RowValid c edge refs)
    (i j : Fin n) (hij : i ≠ j) (hedge : edgeIndex i j = edge) :
    termEdgeSum c.terms (edgeIndex i j) ≤
      BucketCertificate.bucketNumerator c refs := by
  let items := c.terms.zipIdx
  let f : PackingTerm n × ℕ → ℕ := fun p ↦
    termEdgeEntry p.1 (edgeIndex i j)
  have hnodup : (items.map Prod.snd).Nodup := by
    dsimp [items]
    rw [List.zipIdx_map_snd]
    exact List.nodup_range'
  have hvalue : ∀ p ∈ items, f p ≠ 0 →
      f p = BucketCertificate.numeratorAt c p.2 := by
    intro p hp hp0
    have hpget : c.terms[p.2]? = some p.1 :=
      List.mem_zipIdx_iff_getElem?.mp hp
    have hqmem : p.1 ∈ c.terms := List.mem_of_getElem? hpget
    have hqClique := hterms p.1 hqmem
    have hnum : BucketCertificate.numeratorAt c p.2 = p.1.numerator := by
      simp [BucketCertificate.numeratorAt, hpget]
    dsimp [f]
    rw [termEdgeEntry_eq_indicator hpairs p.1 hqClique i j hij]
    by_cases hmember : s(i, j) ∈ p.1.triangle.sym2
    · simp [hmember, hnum]
    · exfalso
      apply hp0
      dsimp [f]
      rw [termEdgeEntry_eq_indicator hpairs p.1 hqClique i j hij]
      simp [hmember]
  have hmem : ∀ p ∈ items, f p ≠ 0 → p.2 ∈ refs.toFinset := by
    intro p hp hp0
    apply List.mem_toFinset.mpr
    apply hrow.1 p.1 p.2 hp
    dsimp [f] at hp0
    unfold termEdgeEntry at hp0
    by_cases h₁ : edgeIndex p.1.i p.1.j = edgeIndex i j <;>
      by_cases h₂ : edgeIndex p.1.i p.1.k = edgeIndex i j <;>
      by_cases h₃ : edgeIndex p.1.j p.1.k = edgeIndex i j <;>
      simp_all [hedge]
  have hbound := BucketCertificate.sum_map_le_finset_sum items refs.toFinset f
    (BucketCertificate.numeratorAt c) hnodup hvalue hmem
  have hmap : items.map f =
      c.terms.map (fun q ↦ termEdgeEntry q (edgeIndex i j)) := by
    calc
      items.map f = (items.map Prod.fst).map
          (fun q ↦ termEdgeEntry q (edgeIndex i j)) := by
        rw [List.map_map]
        rfl
      _ = c.terms.map (fun q ↦ termEdgeEntry q (edgeIndex i j)) := by
        dsimp [items]
        rw [List.zipIdx_map_fst]
  unfold termEdgeSum BucketCertificate.bucketNumerator
  rw [← hmap]
  exact hbound

lemma RowChunkValid.row {c : PackingCert n} {start : ℕ}
    {rows : List (List ℕ)} (h : RowChunkValid c start rows)
    {edge : ℕ} (hlower : start ≤ edge)
    (hupper : edge < start + rows.length) :
    ∃ refs : List ℕ, RowValid c edge refs := by
  let index := edge - start
  have hindex : index < rows.length := by
    dsimp [index]
    omega
  let refs := rows[index]
  have hzip : (refs, index) ∈ rows.zipIdx := by
    apply List.mem_zipIdx_iff_getElem?.mpr
    dsimp [refs]
    rw [List.getElem?_eq_getElem hindex]
  refine ⟨refs, ?_⟩
  have hv := h.2 refs index hzip
  have hedge : start + index = edge := by
    dsimp [index]
    omega
  simpa only [hedge] using hv

/-- A finite proof tree of consecutive chunks.  Generated modules construct
this with `step`; internal nodes perform no Boolean reduction. -/
inductive ChunksValidFrom (c : PackingCert n) : ℕ → Prop where
  | done : ChunksValidFrom c (edgeCount n)
  | step {start : ℕ} (rows : List (List ℕ))
      (head : RowChunkValid c start rows)
      (tail : ChunksValidFrom c (start + rows.length)) :
      ChunksValidFrom c start

theorem ChunksValidFrom.row {c : PackingCert n} {start edge : ℕ}
    (h : ChunksValidFrom c start) (hlower : start ≤ edge)
    (hupper : edge < edgeCount n) :
    ∃ refs : List ℕ, RowValid c edge refs := by
  induction h generalizing edge with
  | done => omega
  | @step start rows head tail ih =>
      by_cases hedge : edge < start + rows.length
      · exact head.row hlower hedge
      · exact ih (by omega) hupper

/-- Base validity plus consecutive valid rows implies the original strong
natural-number certificate. -/
theorem BaseValid.strongValidOfChunks (hpairs : PairIndexValid n)
    {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    (a : ℕ) (c : PackingCert n) (hbase : BaseValid G a c)
    (hchunks : ChunksValidFrom c 0) : c.StrongValid G a := by
  rcases hbase with ⟨hden, hterms, hkeys, hhalf, hobjective⟩
  refine ⟨⟨hden, hterms, ?_⟩, hkeys, hhalf, hobjective⟩
  intro i hi j hj hadj
  have hij : i ≠ j := by
    intro hij
    subst j
    exact G.loopless.irrefl i hadj
  have hindex : edgeIndex i j < edgeCount n := hpairs.1 i j hij
  obtain ⟨refs, hrow⟩ := hchunks.row (Nat.zero_le _) hindex
  calc
    c.edgeNumerator s(i, j) =
        termEdgeSum c.terms (edgeIndex i j) := by
      symm
      exact termEdgeSum_eq_edgeNumerator hpairs c hterms i j hij
    _ ≤ BucketCertificate.bucketNumerator c refs :=
      termEdgeSum_le_row hpairs c hterms (edgeIndex i j) refs hrow i j hij rfl
    _ ≤ c.denominator := hrow.2.2

end StagedBucketCertificate
end CertificateChecker
end Erdos76
