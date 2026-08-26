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
import ErdosProblems.Erdos76.FiniteStabilityCertificateChecker

/-!
# Incremental finite-stability search traces

This module checks the search DAG used for the finite stability calculation.
A transition from order `n` to `n+1` assigns the `n` edges incident with the
new final vertex one at a time.  Only reachable prefixes are stored.  Each of
the two children of a prefix is either another prefix, a robust strict packing
certificate, a completed canonical representative, or (at order 17) a
pentagon-exception certificate.

The checker is data-independent and supports row sharding.  Generated data is
kept in separate modules.
-/

open Finset
open scoped BigOperators

namespace Erdos76
namespace IncrementalStabilityTrace

open CertificateChecker
open CertificateChecker.PackingCert
open CertificateExhaustion
open FiniteStabilityCertificateChecker

/-! ## Partial colourings and robust lower certificates -/

/-- Known edges of one colour after the first `depth` incident edges of the
new final vertex have been assigned.  `colour = true` is the graph colour and
`colour = false` is its complement. -/
def knownColourCode {n : ℕ} (parent : BitVec (edgeCount n))
    (depth : ℕ) (mask : BitVec n) (colour : Bool) : GraphCode (n + 1) :=
  fun u v ↦
    if hu : u.1 < n then
      if hv : v.1 < n then
        decide (parent.getLsbD (edgeIndex u.1 v.1) = colour)
      else if hdepth : u.1 < depth then
        decide (mask.getLsbD u.1 = colour)
      else false
    else if hv : v.1 < n then
      if hdepth : v.1 < depth then
        decide (mask.getLsbD v.1 = colour)
      else false
    else false

/-- A complete colouring agrees with a parent representative and a prefix of
the incident-edge mask. -/
def IsPrefixCompletion {n : ℕ} (parent : BitVec (edgeCount n))
    (depth : ℕ) (mask : BitVec n) (G : SimpleGraph (Fin (n + 1))) : Prop :=
  IsInitialVertexExtension (graphOfBits parent) G ∧
    ∀ i : Fin n, i.1 < depth →
      (G.Adj i.castSucc (Fin.last n) ↔ mask.getLsbD i.1 = true)

@[simp] lemma knownColourCode_old_adj {n : ℕ}
    (parent : BitVec (edgeCount n)) (depth : ℕ) (mask : BitVec n)
    (colour : Bool) (i j : Fin n) :
    (graphOfCode (knownColourCode parent depth mask colour)).Adj
        i.castSucc j.castSucc ↔
      i ≠ j ∧ parent.getLsbD (edgeIndex i.1 j.1) = colour := by
  simp [graphOfCode, knownColourCode, edgeIndex_comm, ne_comm]

@[simp] lemma knownColourCode_new_adj {n : ℕ}
    (parent : BitVec (edgeCount n)) (depth : ℕ) (mask : BitVec n)
    (colour : Bool) (i : Fin n) :
    (graphOfCode (knownColourCode parent depth mask colour)).Adj
        i.castSucc (Fin.last n) ↔
      i.1 < depth ∧ mask.getLsbD i.1 = colour := by
  simp [graphOfCode, knownColourCode, Fin.castSucc_ne_last,
    edgeIndex_comm, ne_comm]

lemma knownRed_le_of_prefixCompletion {n : ℕ}
    {parent : BitVec (edgeCount n)} {depth : ℕ} {mask : BitVec n}
    {G : SimpleGraph (Fin (n + 1))}
    (hG : IsPrefixCompletion parent depth mask G) :
    graphOfCode (knownColourCode parent depth mask true) ≤ G := by
  intro u v huv
  induction u using Fin.lastCases with
  | last =>
      induction v using Fin.lastCases with
      | last => exact ((graphOfCode
          (knownColourCode parent depth mask true)).loopless.irrefl _ huv).elim
      | cast i =>
          have hi := (knownColourCode_new_adj parent depth mask true i).mp
            (by simpa [SimpleGraph.adj_comm] using huv)
          rw [G.adj_comm]
          exact (hG.2 i hi.1).2 hi.2
  | cast i =>
      induction v using Fin.lastCases with
      | last =>
          have hi := (knownColourCode_new_adj parent depth mask true i).mp huv
          exact (hG.2 i hi.1).2 hi.2
      | cast j =>
          have hij := (knownColourCode_old_adj parent depth mask true i j).mp huv
          exact (hG.1 i j).1 (by
            simpa [graphOfBits_adj] using hij)

lemma knownBlue_le_compl_of_prefixCompletion {n : ℕ}
    {parent : BitVec (edgeCount n)} {depth : ℕ} {mask : BitVec n}
    {G : SimpleGraph (Fin (n + 1))}
    (hG : IsPrefixCompletion parent depth mask G) :
    graphOfCode (knownColourCode parent depth mask false) ≤ Gᶜ := by
  intro u v huv
  induction u using Fin.lastCases with
  | last =>
      induction v using Fin.lastCases with
      | last => exact ((graphOfCode
          (knownColourCode parent depth mask false)).loopless.irrefl _ huv).elim
      | cast i =>
          have hi := (knownColourCode_new_adj parent depth mask false i).mp
            (by simpa [SimpleGraph.adj_comm] using huv)
          simp only [SimpleGraph.compl_adj]
          refine ⟨(Fin.castSucc_ne_last i).symm, ?_⟩
          intro hred
          have := (hG.2 i hi.1).1 (by simpa [G.adj_comm] using hred)
          cases hbit : mask.getLsbD i.1 <;> simp_all
  | cast i =>
      induction v using Fin.lastCases with
      | last =>
          have hi := (knownColourCode_new_adj parent depth mask false i).mp huv
          simp only [SimpleGraph.compl_adj]
          refine ⟨Fin.castSucc_ne_last i, ?_⟩
          intro hred
          have := (hG.2 i hi.1).1 hred
          cases hbit : mask.getLsbD i.1 <;> simp_all
      | cast j =>
          have hij := (knownColourCode_old_adj parent depth mask false i j).mp huv
          simp only [SimpleGraph.compl_adj]
          refine ⟨by simpa using hij.1, ?_⟩
          intro hred
          have hold := (hG.1 i j).2 hred
          have hold' := (graphOfBits_adj parent i j).mp hold
          cases hbit : parent.getLsbD (edgeIndex i.1 j.1) <;> simp_all

/-- A sparse packing checked on known edges, with the capacity inequality
strengthened to every vertex pair.  It therefore remains feasible under every
completion of the partial colouring. -/
def CompletionPackingValid {n : ℕ} (known : SimpleGraph (Fin n))
    [DecidableRel known.Adj] (c : PackingCert n) : Prop :=
  0 < c.denominator ∧
    (∀ q ∈ c.terms, known.IsNClique 3 q.triangle) ∧
      ∀ i ∈ List.finRange n, ∀ j ∈ List.finRange n,
        c.edgeNumerator s(i, j) ≤ c.denominator

/-- Executable robust packing checker. -/
def checkCompletionPacking {n : ℕ} (known : SimpleGraph (Fin n))
    [DecidableRel known.Adj] (c : PackingCert n) : Bool :=
  decide (0 < c.denominator) &&
    c.terms.all (fun q ↦ decide (known.IsNClique 3 q.triangle)) &&
      (List.finRange n).all fun i ↦
        (List.finRange n).all fun j ↦
          decide (c.edgeNumerator s(i, j) ≤ c.denominator)

@[simp] theorem checkCompletionPacking_eq_true_iff {n : ℕ}
    (known : SimpleGraph (Fin n)) [DecidableRel known.Adj]
    (c : PackingCert n) :
    checkCompletionPacking known c = true ↔ CompletionPackingValid known c := by
  simp [checkCompletionPacking, CompletionPackingValid, List.all_eq_true,
    and_assoc]

theorem CompletionPackingValid.isFractionalPacking
    {n : ℕ} {known G : SimpleGraph (Fin n)}
    [DecidableRel known.Adj] [DecidableRel G.Adj]
    {c : PackingCert n} (hc : CompletionPackingValid known c)
    (hsub : known ≤ G) : IsFractionalPacking G c.weight := by
  have hterms : ∀ q ∈ c.terms, G.IsNClique 3 q.triangle := by
    intro q hq
    exact (hc.2.1 q hq).mono hsub
  constructor
  · intro t ht
    exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · intro e he
    have hedge : c.edgeNumerator e ≤ c.denominator := by
      induction e using Sym2.inductionOn with
      | _ i j => exact hc.2.2 i (List.mem_finRange i) j (List.mem_finRange j)
    rw [fractionalEdgeLoad_weight c hterms e]
    apply (div_le_one (by exact_mod_cast hc.1)).2
    exact_mod_cast hedge

/-- Pair of robust sparse packings on the currently known red and blue
edges. -/
structure PartialLowerCert (n : ℕ) where
  red : PackingCert n
  blue : PackingCert n
  deriving DecidableEq

namespace PartialLowerCert

def Valid {n : ℕ} (knownRed knownBlue : SimpleGraph (Fin n))
    [DecidableRel knownRed.Adj] [DecidableRel knownBlue.Adj]
    (c : PartialLowerCert n) : Prop :=
  CompletionPackingValid knownRed c.red ∧
    CompletionPackingValid knownBlue c.blue ∧
    n * (n - 1) * c.red.denominator * c.blue.denominator <
      12 * (c.red.totalNumerator * c.blue.denominator +
        c.blue.totalNumerator * c.red.denominator)

def check {n : ℕ} (knownRed knownBlue : SimpleGraph (Fin n))
    [DecidableRel knownRed.Adj] [DecidableRel knownBlue.Adj]
    (c : PartialLowerCert n) : Bool :=
  checkCompletionPacking knownRed c.red &&
    checkCompletionPacking knownBlue c.blue &&
      decide (n * (n - 1) * c.red.denominator * c.blue.denominator <
        12 * (c.red.totalNumerator * c.blue.denominator +
          c.blue.totalNumerator * c.red.denominator))

@[simp] theorem check_eq_true_iff {n : ℕ}
    (knownRed knownBlue : SimpleGraph (Fin n))
    [DecidableRel knownRed.Adj] [DecidableRel knownBlue.Adj]
    (c : PartialLowerCert n) :
    c.check knownRed knownBlue = true ↔ c.Valid knownRed knownBlue := by
  simp [check, Valid, and_assoc]

theorem Valid.not_fractionalCoveredSizeAtMost_of_prefixCompletion
    {n : ℕ} {parent : BitVec (edgeCount n)}
    {depth : ℕ} {mask : BitVec n}
    {G : SimpleGraph (Fin (n + 1))} [DecidableRel G.Adj]
    (c : PartialLowerCert (n + 1))
    (hc : c.Valid
      (graphOfCode (knownColourCode parent depth mask true))
      (graphOfCode (knownColourCode parent depth mask false)))
    (hprefix : IsPrefixCompletion parent depth mask G) :
    ¬ FractionalCoveredSizeAtMost G (stabilityThreshold (n + 1)) := by
  have hredValid : c.red.Valid G := by
    refine ⟨hc.1.1, ?_, ?_⟩
    · intro q hq
      exact (hc.1.2.1 q hq).mono (knownRed_le_of_prefixCompletion hprefix)
    · intro i hi j hj _
      exact hc.1.2.2 i hi j hj
  have hblueValid : c.blue.Valid Gᶜ := by
    refine ⟨hc.2.1.1, ?_, ?_⟩
    · intro q hq
      exact (hc.2.1.2.1 q hq).mono
        (knownBlue_le_compl_of_prefixCompletion hprefix)
    · intro i hi j hj _
      exact hc.2.1.2.2 i hi j hj
  let full : TwoColorLowerCert (n + 1) := ⟨c.red, c.blue⟩
  have hfull : full.Valid G := ⟨hredValid, hblueValid, hc.2.2⟩
  exact hfull.not_fractionalCoveredSizeAtMost full (by omega)

end PartialLowerCert

/-! ## Direct-indexed, postorder search DAG -/

/-- The bitvector represented by the natural-number prefix stored in generated
trace data. -/
def prefixBits (n pref : ℕ) : BitVec n := BitVec.ofNat n pref

@[simp] theorem prefixBits_getLsbD (n pref i : ℕ) (hi : i < n) :
    (prefixBits n pref).getLsbD i = pref.testBit i := by
  simp [prefixBits, BitVec.getLsbD, Nat.testBit_mod_two_pow, hi]

lemma IsPrefixCompletion.nextBlue {n : ℕ}
    {parent : BitVec (edgeCount n)} {depth pref : ℕ}
    {G : SimpleGraph (Fin (n + 1))}
    (h : IsPrefixCompletion parent depth (prefixBits n pref) G)
    (hdepth : depth < n) (hprefix : pref < 2 ^ depth)
    (hblue : ¬G.Adj (⟨depth, hdepth⟩ : Fin n).castSucc (Fin.last n)) :
    IsPrefixCompletion parent (depth + 1) (prefixBits n pref) G := by
  refine ⟨h.1, ?_⟩
  intro i hi
  by_cases hid : i.1 < depth
  · exact h.2 i hid
  · have hieq : i.1 = depth := by omega
    have hiFin : i = (⟨depth, hdepth⟩ : Fin n) := by
      apply Fin.ext
      simpa using hieq
    subst i
    have hbit : (prefixBits n pref).getLsbD depth = false := by
      rw [prefixBits_getLsbD n pref depth hdepth]
      exact Nat.testBit_lt_two_pow hprefix
    simp only [hbit, Bool.false_eq_true, iff_false]
    exact hblue

lemma IsPrefixCompletion.nextRed {n : ℕ}
    {parent : BitVec (edgeCount n)} {depth pref : ℕ}
    {G : SimpleGraph (Fin (n + 1))}
    (h : IsPrefixCompletion parent depth (prefixBits n pref) G)
    (hdepth : depth < n) (hprefix : pref < 2 ^ depth)
    (hred : G.Adj (⟨depth, hdepth⟩ : Fin n).castSucc (Fin.last n)) :
    IsPrefixCompletion parent (depth + 1)
      (prefixBits n (pref + 2 ^ depth)) G := by
  refine ⟨h.1, ?_⟩
  intro i hi
  by_cases hid : i.1 < depth
  · have hbit := prefixBits_getLsbD n (pref + 2 ^ depth) i.1 i.isLt
    have hadd : (pref + 2 ^ depth).testBit i.1 = pref.testBit i.1 := by
      rw [Nat.add_comm]
      exact Nat.testBit_two_pow_add_gt hid pref
    rw [hbit, hadd]
    have hold := h.2 i hid
    change G.Adj i.castSucc (Fin.last n) ↔
      (prefixBits n pref).getLsbD i.1 = true at hold
    rw [prefixBits_getLsbD n pref i.1 i.isLt] at hold
    exact hold
  · have hieq : i.1 = depth := by omega
    have hiFin : i = (⟨depth, hdepth⟩ : Fin n) := by
      apply Fin.ext
      simpa using hieq
    subst i
    have hbit0 : pref.testBit depth = false :=
      Nat.testBit_lt_two_pow hprefix
    have hbit := prefixBits_getLsbD n (pref + 2 ^ depth) depth hdepth
    have hadd : (pref + 2 ^ depth).testBit depth = true := by
      rw [Nat.add_comm, Nat.testBit_two_pow_add_eq, hbit0]
      rfl
    rw [hbit, hadd]
    simpa using hred

/-- At full depth the known-red graph is exactly the completed graph. -/
lemma graphOfCode_knownRed_eq {n : ℕ}
    {parent : BitVec (edgeCount n)} {pref : ℕ}
    {G : SimpleGraph (Fin (n + 1))}
    (h : IsPrefixCompletion parent n (prefixBits n pref) G) :
    graphOfCode (knownColourCode parent n (prefixBits n pref) true) = G := by
  ext u v
  induction u using Fin.lastCases with
  | last =>
      induction v using Fin.lastCases with
      | last => simp
      | cast i =>
          rw [SimpleGraph.adj_comm]
          simpa [SimpleGraph.adj_comm] using (h.2 i i.isLt).symm
  | cast i =>
      induction v using Fin.lastCases with
      | last => simpa using (h.2 i i.isLt).symm
      | cast j =>
          rw [knownColourCode_old_adj]
          simpa [graphOfBits_adj] using (h.1 i j)

/-- Terminal and branching actions for one reachable prefix.  Split children
are direct indices into the same node array.  Generated tables use postorder,
so the checker can require both indices to be strictly smaller than the
current index. -/
inductive NodeKind (n : ℕ)
  | split (blue red : ℕ)
  | prune (certificate : PartialLowerCert (n + 1))
  | retain (child : ℕ) (route : CanonicalRoute (n + 1))
  | pentagon (certificate : RoutedPentagonCert (n + 1))
  | close (certificate : RoutedCloseCert (n + 1))
  deriving DecidableEq

instance {n : ℕ} : Inhabited (NodeKind n) := ⟨.split 0 0⟩

/-- One reachable state in the incident-edge prefix tree. -/
structure TraceNode (n : ℕ) where
  parent : ℕ
  depth : ℕ
  pref : ℕ
  kind : NodeKind n
  deriving DecidableEq, Inhabited

/-- All direct-indexed data for one extension stage `n → n+1`. -/
structure StageData (n : ℕ) where
  parents : Array (BitVec (edgeCount n))
  children : Array (BitVec (edgeCount (n + 1)))
  nodes : Array (TraceNode n)
  roots : Array ℕ
  deriving DecidableEq

namespace TraceNode

/-- A node has the prescribed parent, prefix depth, and prefix number. -/
def StateMatches {n : ℕ} (x : TraceNode n)
    (parent depth pref : ℕ) : Prop :=
  x.parent = parent ∧ x.depth = depth ∧ x.pref = pref

instance {n : ℕ} (x : TraceNode n) (parent depth pref : ℕ) :
    Decidable (x.StateMatches parent depth pref) := by
  unfold StateMatches
  infer_instance

/-- The graph code consisting of the known red edges at a node. -/
def knownRedCode {n : ℕ} (d : StageData n) (x : TraceNode n) :
    GraphCode (n + 1) :=
  knownColourCode (d.parents.getD x.parent 0) x.depth
    (prefixBits n x.pref) true

/-- The graph code consisting of the known blue edges at a node. -/
def knownBlueCode {n : ℕ} (d : StageData n) (x : TraceNode n) :
    GraphCode (n + 1) :=
  knownColourCode (d.parents.getD x.parent 0) x.depth
    (prefixBits n x.pref) false

/-- Local validity of one postorder node.  All references are O(1) direct
lookups; in particular, no existential scan of a representative array occurs. -/
def Valid {n : ℕ} (d : StageData n) (index : ℕ) (x : TraceNode n) : Prop :=
  x.parent < d.parents.size ∧ x.depth ≤ n ∧ x.pref < 2 ^ x.depth ∧
    match x.kind with
    | .split blue red =>
        x.depth < n ∧ blue < index ∧ red < index ∧
          (d.nodes.getD blue default).StateMatches
            x.parent (x.depth + 1) x.pref ∧
          (d.nodes.getD red default).StateMatches
            x.parent (x.depth + 1) (x.pref + 2 ^ x.depth)
    | .prune certificate =>
        certificate.check (graphOfCode (x.knownRedCode d))
          (graphOfCode (x.knownBlueCode d)) = true
    | .retain child route =>
        x.depth = n ∧ child < d.children.size ∧
          SourceMatches (x.knownRedCode d) route ∧ route.Valid ∧
          route.target = d.children.getD child 0
    | .pentagon certificate =>
        n + 1 = 17 ∧ x.depth = n ∧
          certificate.Valid (x.knownRedCode d)
    | .close certificate =>
        n + 1 = 22 ∧ x.depth = n ∧
          certificate.Valid (x.knownRedCode d) 2

instance {n : ℕ} (d : StageData n) (index : ℕ) (x : TraceNode n) :
    Decidable (x.Valid d index) := by
  unfold Valid
  cases x.kind <;> infer_instance

end TraceNode

namespace StageData

/-- Each parent has a direct root at depth zero with the empty prefix. -/
def RootsValid {n : ℕ} (d : StageData n) : Prop :=
  d.roots.size = d.parents.size ∧
    ∀ p : Fin d.parents.size,
      d.roots.getD p.1 d.nodes.size < d.nodes.size ∧
        (d.nodes.getD (d.roots.getD p.1 d.nodes.size) default).StateMatches
          p.1 0 0

instance {n : ℕ} (d : StageData n) : Decidable d.RootsValid := by
  unfold RootsValid
  infer_instance

/-- Every global node row is locally valid. -/
def NodesValid {n : ℕ} (d : StageData n) : Prop :=
  ∀ i : Fin d.nodes.size, d.nodes[i].Valid d i.1

instance {n : ℕ} (d : StageData n) : Decidable d.NodesValid := by
  unfold NodesValid
  infer_instance

/-- Semantic validity of a complete stage. -/
def Valid {n : ℕ} (d : StageData n) : Prop := d.RootsValid ∧ d.NodesValid

instance {n : ℕ} (d : StageData n) : Decidable d.Valid := by
  unfold Valid
  infer_instance

def checkRoots {n : ℕ} (d : StageData n) : Bool := decide d.RootsValid

@[simp] theorem checkRoots_eq_true_iff {n : ℕ} (d : StageData n) :
    d.checkRoots = true ↔ d.RootsValid := by
  simp [checkRoots]

/-- Recursive consecutive-row predicate used to compose generated shards. -/
def RowsValidListFrom {n : ℕ} (d : StageData n) :
    ℕ → List (TraceNode n) → Prop
  | _, [] => True
  | start, row :: rows =>
      if h : start < d.nodes.size then
        d.nodes[start] = row ∧ row.Valid d start ∧
          RowsValidListFrom d (start + 1) rows
      else False

instance {n : ℕ} (d : StageData n) (start : ℕ)
    (rows : List (TraceNode n)) :
    Decidable (RowsValidListFrom d start rows) := by
  induction rows generalizing start with
  | nil => exact isTrue trivial
  | cons row rows ih =>
      simp only [RowsValidListFrom]
      split <;> infer_instance

/-- Check a consecutive shard beginning at the global node index `start`. -/
def RowsValidFrom {n : ℕ} (d : StageData n) (start : ℕ)
    (rows : Array (TraceNode n)) : Prop :=
  RowsValidListFrom d start rows.toList

instance {n : ℕ} (d : StageData n) (start : ℕ)
    (rows : Array (TraceNode n)) : Decidable (RowsValidFrom d start rows) := by
  unfold RowsValidFrom
  infer_instance

def checkRows {n : ℕ} (d : StageData n) (start : ℕ)
    (rows : Array (TraceNode n)) : Bool :=
  decide (RowsValidFrom d start rows)

@[simp] theorem checkRows_eq_true_iff {n : ℕ} (d : StageData n)
    (start : ℕ) (rows : Array (TraceNode n)) :
    d.checkRows start rows = true ↔ RowsValidFrom d start rows := by
  simp [checkRows]

theorem RowsValidListFrom.append {n : ℕ} {d : StageData n}
    {start : ℕ} {a b : List (TraceNode n)}
    (ha : RowsValidListFrom d start a)
    (hb : RowsValidListFrom d (start + a.length) b) :
    RowsValidListFrom d start (a ++ b) := by
  induction a generalizing start with
  | nil => simpa [RowsValidListFrom] using hb
  | cons row rows ih =>
      simp only [List.cons_append, RowsValidListFrom] at ha ⊢
      by_cases hstart : start < d.nodes.size
      · rw [dif_pos hstart] at ha ⊢
        obtain ⟨hrow, hvalid, htail⟩ := ha
        refine ⟨hrow, hvalid, ih htail ?_⟩
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hb
      · rw [dif_neg hstart] at ha
        exact False.elim ha

theorem RowsValidFrom.append {n : ℕ} {d : StageData n}
    {start : ℕ} {a b : Array (TraceNode n)}
    (ha : RowsValidFrom d start a)
    (hb : RowsValidFrom d (start + a.size) b) :
    RowsValidFrom d start (a ++ b) := by
  unfold RowsValidFrom at ha hb ⊢
  simpa using RowsValidListFrom.append ha hb

theorem RowsValidListFrom.get {n : ℕ} {d : StageData n}
    {start : ℕ} {rows : List (TraceNode n)}
    (hrows : RowsValidListFrom d start rows)
    (q : ℕ) (hq : q < rows.length) :
    start + q < d.nodes.size ∧
      d.nodes.getD (start + q) default = rows[q] ∧
        rows[q].Valid d (start + q) := by
  induction rows generalizing start q with
  | nil => simp at hq
  | cons row rows ih =>
      simp only [RowsValidListFrom] at hrows
      by_cases hstart : start < d.nodes.size
      · rw [dif_pos hstart] at hrows
        obtain ⟨hrow, hvalid, htail⟩ := hrows
        cases q with
        | zero =>
            have hget : d.nodes.getD start default = d.nodes[start] :=
              (Array.getElem_eq_getD default).symm
            simpa [hget] using And.intro hstart (And.intro hrow hvalid)
        | succ q =>
            have hq' : q < rows.length := by simpa using hq
            have hgot := ih htail q hq'
            simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hgot
      · rw [dif_neg hstart] at hrows
        exact False.elim hrows

/-- Shards covering the entire node array reconstruct global node validity. -/
theorem NodesValid.of_rowsValidFrom {n : ℕ} {d : StageData n}
    (hrows : RowsValidFrom d 0 d.nodes) : d.NodesValid := by
  intro i
  have hiList : i.1 < d.nodes.toList.length := by simpa using i.isLt
  obtain ⟨hi, hrow, hvalid⟩ :=
    RowsValidListFrom.get hrows i.1 hiList
  have hlist : d.nodes.toList[i.1] = d.nodes[i] := Array.getElem_toList _
  have hget : d.nodes.getD i.1 default = d.nodes[i] := by
    exact (Array.getElem_eq_getD default).symm
  simpa [hlist, hget] using hvalid

/-- Executable shard checks plus the root check yield a valid extension stage. -/
theorem valid_of_checks {n : ℕ} {d : StageData n}
    (hroots : d.checkRoots = true)
    (hrows : d.checkRows 0 d.nodes = true) : d.Valid :=
  ⟨(checkRoots_eq_true_iff d).mp hroots,
    NodesValid.of_rowsValidFrom ((checkRows_eq_true_iff d 0 d.nodes).mp hrows)⟩

/-! ## Semantic soundness of a checked stage -/

/-- A representative is allowed to exchange the two colours. -/
def IsOrientedRepresented {m : ℕ}
    (reps : Array (BitVec (edgeCount m)))
    (G : SimpleGraph (Fin m)) : Prop :=
  ∃ i : Fin reps.size,
    Nonempty (G ≃g graphOfBits reps[i]) ∨
      Nonempty (Gᶜ ≃g graphOfBits reps[i])

/-- Isomorphisms commute with graph complementation. -/
noncomputable def complementIso {m : ℕ}
    {G H : SimpleGraph (Fin m)} (f : G ≃g H) : Gᶜ ≃g Hᶜ where
  __ := f.toEquiv
  map_rel_iff' := by
    intro x y
    simp [SimpleGraph.compl_adj, f.map_rel_iff]

/-- The four possible semantic outcomes of a stage.  The complement-pentagon
alternative records an accumulated colour swap; it is eliminated later using
self-complementarity of the pentagon template. -/
def Outcome {n : ℕ} (d : StageData n)
    (G : SimpleGraph (Fin (n + 1))) : Prop :=
  IsOrientedRepresented d.children G ∨
    (n + 1 = 17 ∧ IsPentagonExceptional G) ∨
    (n + 1 = 17 ∧ IsPentagonExceptional Gᶜ) ∨
    (n + 1 = 22 ∧ CloseToBipartite G 2) ∨
    (n + 1 = 22 ∧ CloseToBipartite Gᶜ 2)

theorem Outcome.iso {n : ℕ} {d : StageData n}
    {G H : SimpleGraph (Fin (n + 1))}
    (h : d.Outcome H) (f : G ≃g H) : d.Outcome G := by
  rcases h with hrep | hpent | hpentc | hclose | hclosec
  · left
    obtain ⟨i, hi | hi⟩ := hrep
    · exact ⟨i, Or.inl ⟨f.trans hi.some⟩⟩
    · exact ⟨i, Or.inr ⟨(complementIso f).trans hi.some⟩⟩
  · right; left
    exact ⟨hpent.1, isPentagonExceptional_iso hpent.2 f.symm⟩
  · right; right; left
    exact ⟨hpentc.1,
      isPentagonExceptional_iso hpentc.2 (complementIso f).symm⟩
  · right; right; right; left
    exact ⟨hclose.1, closeToBipartite_iso hclose.2 f.symm⟩
  · right; right; right; right
    exact ⟨hclosec.1,
      closeToBipartite_iso hclosec.2 (complementIso f).symm⟩

theorem Outcome.compl {n : ℕ} {d : StageData n}
    {G : SimpleGraph (Fin (n + 1))} (h : d.Outcome Gᶜ) : d.Outcome G := by
  rcases h with hrep | hpent | hpentc | hclose | hclosec
  · left
    obtain ⟨i, hi | hi⟩ := hrep
    · exact ⟨i, Or.inr hi⟩
    · exact ⟨i, Or.inl (by simpa using hi)⟩
  · right; right; left
    exact hpent
  · right; left
    exact ⟨hpentc.1, by simpa using hpentc.2⟩
  · right; right; right; right
    exact hclose
  · right; right; right; left
    exact ⟨hclosec.1, by simpa using hclosec.2⟩

theorem resolveNode {n : ℕ} (d : StageData n) (hd : d.NodesValid) :
    ∀ index : ℕ, index < d.nodes.size →
      ∀ G : SimpleGraph (Fin (n + 1)),
        IsPrefixCompletion
          (d.parents.getD (d.nodes.getD index default).parent 0)
          (d.nodes.getD index default).depth
          (prefixBits n (d.nodes.getD index default).pref) G →
        FractionalCoveredSizeAtMost G (stabilityThreshold (n + 1)) →
        d.Outcome G := by
  intro index
  induction index using Nat.strong_induction_on with
  | h index ih =>
      intro hindex G hprefix hupper
      classical
      letI : DecidableRel G.Adj := Classical.decRel _
      let x := d.nodes[index]
      have hxget : d.nodes.getD index default = x := by
        simpa [x] using (Array.getElem_eq_getD default).symm
      have hxvalid : x.Valid d index := by
        simpa [x] using hd ⟨index, hindex⟩
      have hprefix' : IsPrefixCompletion
          (d.parents.getD x.parent 0) x.depth
          (prefixBits n x.pref) G := by simpa [hxget] using hprefix
      cases hkind : x.kind with
      | split blue red =>
          have hv := hxvalid
          simp only [TraceNode.Valid, hkind] at hv
          obtain ⟨_, hxdepth, hxprefix, hlt, hblue, hred,
            hblueState, hredState⟩ := hv
          by_cases hedge : G.Adj (⟨x.depth, hlt⟩ : Fin n).castSucc
              (Fin.last n)
          · have hprefRed := hprefix'.nextRed hlt hxprefix hedge
            have hrange : red < d.nodes.size := lt_trans hred hindex
            apply ih red hred hrange G
            · rcases hredState with ⟨hp, hd, hb⟩
              rw [hp, hd, hb]
              exact hprefRed
            · exact hupper
          · have hprefBlue := hprefix'.nextBlue hlt hxprefix hedge
            have hrange : blue < d.nodes.size := lt_trans hblue hindex
            apply ih blue hblue hrange G
            · rcases hblueState with ⟨hp, hd, hb⟩
              rw [hp, hd, hb]
              exact hprefBlue
            · exact hupper
      | prune certificate =>
          have hv := hxvalid
          simp only [TraceNode.Valid, hkind] at hv
          obtain ⟨_, _, _, hcert⟩ := hv
          have hcert' := (PartialLowerCert.check_eq_true_iff
            (graphOfCode (x.knownRedCode d))
            (graphOfCode (x.knownBlueCode d)) certificate).mp hcert
          exact (PartialLowerCert.Valid.not_fractionalCoveredSizeAtMost_of_prefixCompletion
            certificate hcert' hprefix') hupper |>.elim
      | retain child route =>
          have hv := hxvalid
          simp only [TraceNode.Valid, hkind] at hv
          obtain ⟨_, _, _, hxdepth, hchild, hsource, hroute, htarget⟩ := hv
          have hprefixFull : IsPrefixCompletion
              (d.parents.getD x.parent 0) n (prefixBits n x.pref) G := by
            simpa [hxdepth] using hprefix'
          have hgraph : graphOfCode (x.knownRedCode d) = G := by
            simpa [TraceNode.knownRedCode, hxdepth] using
              graphOfCode_knownRed_eq hprefixFull
          have hchildGet : d.children.getD child 0 =
              d.children[child]'hchild := by
            exact (Array.getElem_eq_getD 0).symm
          have htarget' : route.target = d.children[child]'hchild :=
            htarget.trans hchildGet
          let f : G ≃g route.routedTarget := by
            have f' := hsource.iso.trans hroute.iso
            simpa [hgraph] using f'
          left
          change ∃ i : Fin d.children.size,
            Nonempty (G ≃g graphOfBits d.children[i]) ∨
              Nonempty (Gᶜ ≃g graphOfBits d.children[i])
          refine ⟨⟨child, hchild⟩, ?_⟩
          cases hswap : route.swap with
          | false =>
              left
              refine ⟨?_⟩
              simpa [CanonicalRoute.routedTarget, hswap, htarget'] using f
          | true =>
              right
              refine ⟨?_⟩
              have fc := complementIso f
              simpa [CanonicalRoute.routedTarget, hswap, htarget'] using fc
      | pentagon certificate =>
          have hv := hxvalid
          simp only [TraceNode.Valid, hkind] at hv
          obtain ⟨_, _, _, hn17, hxdepth, hcert⟩ := hv
          have hprefixFull : IsPrefixCompletion
              (d.parents.getD x.parent 0) n (prefixBits n x.pref) G := by
            simpa [hxdepth] using hprefix'
          have hgraph : graphOfCode (x.knownRedCode d) = G := by
            simpa [TraceNode.knownRedCode, hxdepth] using
              graphOfCode_knownRed_eq hprefixFull
          right; left
          exact ⟨hn17, by
            simpa [hgraph] using hcert.isPentagonExceptional (by omega)⟩
      | close certificate =>
          have hv := hxvalid
          simp only [TraceNode.Valid, hkind] at hv
          obtain ⟨_, _, _, _, hxdepth, hcert⟩ := hv
          have hprefixFull : IsPrefixCompletion
              (d.parents.getD x.parent 0) n (prefixBits n x.pref) G := by
            simpa [hxdepth] using hprefix'
          have hgraph : graphOfCode (x.knownRedCode d) = G := by
            simpa [TraceNode.knownRedCode, hxdepth] using
              graphOfCode_knownRed_eq hprefixFull
          rcases hcert.closeToBipartite with hclose | hclose
          · right; right; right; left
            exact ⟨by omega, by simpa [hgraph] using hclose⟩
          · right; right; right; right
            exact ⟨by omega, by simpa [hgraph] using hclose⟩

/-- Starting from the direct root of a represented parent, a checked stage
resolves every upper-bounded extension. -/
theorem resolveRoot {n : ℕ} (d : StageData n) (hd : d.Valid)
    (p : Fin d.parents.size) (G : SimpleGraph (Fin (n + 1)))
    (hG : IsPrefixCompletion d.parents[p] 0 (prefixBits n 0) G)
    (hupper : FractionalCoveredSizeAtMost G (stabilityThreshold (n + 1))) :
    d.Outcome G := by
  have hroot := hd.1.2 p
  let index := d.roots.getD p.1 d.nodes.size
  rcases hroot.2 with ⟨hp, hdepth, hpref⟩
  apply resolveNode d hd.2 index hroot.1 G
  · have hparent : d.parents.getD p.1 0 = d.parents[p] :=
      (Array.getElem_eq_getD 0).symm
    rw [hp, hdepth, hpref, hparent]
    exact hG
  · exact hupper

/-- A checked stage transports an upper-bounded standard extension of any
oriented parent representative to one of its terminal outcomes. -/
theorem resolveExtension {n : ℕ} (d : StageData n) (hd : d.Valid)
    (H : SimpleGraph (Fin n)) (G : SimpleGraph (Fin (n + 1)))
    (hHG : IsInitialVertexExtension H G)
    (hrep : IsOrientedRepresented d.parents H)
    (hupper : FractionalCoveredSizeAtMost G (stabilityThreshold (n + 1))) :
    d.Outcome G := by
  classical
  obtain ⟨p, hrep | hrep⟩ := hrep
  · let f := hrep.some
    obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair
      (fun i : Fin n ↦ i.castSucc)
      (fun i : Fin n ↦ (f i).castSucc)
      (Fin.castSucc_injective n)
      ((Fin.castSucc_injective n).comp f.injective)
    let P : SimpleGraph (Fin (n + 1)) := G.map σ.toEmbedding
    let giso : G ≃g P :=
      { __ := σ
        map_rel_iff' := by
          intro u v
          simpa [P] using (SimpleGraph.map_adj_apply
            (G := G) (f := σ.toEmbedding) (a := u) (b := v)) }
    have hPprefix : IsPrefixCompletion d.parents[p] 0 (prefixBits n 0) P := by
      refine ⟨?_, by omega⟩
      intro a b
      have hold : H.Adj (f.symm a) (f.symm b) ↔
          G.Adj (f.symm a).castSucc (f.symm b).castSucc :=
        hHG (f.symm a) (f.symm b)
      have hσa : σ ((f.symm a).castSucc) = a.castSucc := by
        simpa using hσ (f.symm a)
      have hσb : σ ((f.symm b).castSucc) = b.castSucc := by
        simpa using hσ (f.symm b)
      have hmap := SimpleGraph.map_adj_apply
        (G := G) (f := σ.toEmbedding)
          (a := (f.symm a).castSucc) (b := (f.symm b).castSucc)
      change (graphOfBits d.parents[p]).Adj a b ↔
        P.Adj a.castSucc b.castSucc
      have hf : (graphOfBits d.parents[p]).Adj a b ↔
          H.Adj (f.symm a) (f.symm b) := by
        simpa using (f.map_rel_iff (a := f.symm a) (b := f.symm b))
      have hgmap : G.Adj (f.symm a).castSucc (f.symm b).castSucc ↔
          P.Adj a.castSucc b.castSucc := by
        simpa [P, hσa, hσb] using hmap.symm
      exact hf.trans (hold.trans hgmap)
    have hPupper : FractionalCoveredSizeAtMost P
        (stabilityThreshold (n + 1)) :=
      fractionalCoveredSizeAtMost_relabel hupper σ
    exact (d.resolveRoot hd p P hPprefix hPupper).iso giso
  · have hHGc : IsInitialVertexExtension Hᶜ Gᶜ := by
      intro a b
      simp only [SimpleGraph.compl_adj]
      constructor
      · rintro ⟨hab, hnadj⟩
        refine ⟨by simpa using hab, ?_⟩
        exact fun hadj ↦ hnadj ((hHG a b).mpr hadj)
      · rintro ⟨hab, hnadj⟩
        refine ⟨by simpa using hab, ?_⟩
        exact fun hadj ↦ hnadj ((hHG a b).mp hadj)
    have hupperc : FractionalCoveredSizeAtMost Gᶜ
        (stabilityThreshold (n + 1)) :=
      fractionalCoveredSizeAtMost_compl hupper
    have hresult : d.Outcome Gᶜ := by
      let f := hrep.some
      obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair
        (fun i : Fin n ↦ i.castSucc)
        (fun i : Fin n ↦ (f i).castSucc)
        (Fin.castSucc_injective n)
        ((Fin.castSucc_injective n).comp f.injective)
      let P : SimpleGraph (Fin (n + 1)) := Gᶜ.map σ.toEmbedding
      let giso : Gᶜ ≃g P :=
        { __ := σ
          map_rel_iff' := by
            intro u v
            simpa [P] using (SimpleGraph.map_adj_apply
              (G := Gᶜ) (f := σ.toEmbedding) (a := u) (b := v)) }
      have hPprefix : IsPrefixCompletion d.parents[p] 0 (prefixBits n 0) P := by
        refine ⟨?_, by omega⟩
        intro a b
        have hold : Hᶜ.Adj (f.symm a) (f.symm b) ↔
            Gᶜ.Adj (f.symm a).castSucc (f.symm b).castSucc :=
          hHGc (f.symm a) (f.symm b)
        have hσa : σ ((f.symm a).castSucc) = a.castSucc := by
          simpa using hσ (f.symm a)
        have hσb : σ ((f.symm b).castSucc) = b.castSucc := by
          simpa using hσ (f.symm b)
        have hmap := SimpleGraph.map_adj_apply
          (G := Gᶜ) (f := σ.toEmbedding)
            (a := (f.symm a).castSucc) (b := (f.symm b).castSucc)
        change (graphOfBits d.parents[p]).Adj a b ↔
          P.Adj a.castSucc b.castSucc
        have hf : (graphOfBits d.parents[p]).Adj a b ↔
            Hᶜ.Adj (f.symm a) (f.symm b) := by
          simpa using (f.map_rel_iff (a := f.symm a) (b := f.symm b))
        have hgmap : Gᶜ.Adj (f.symm a).castSucc (f.symm b).castSucc ↔
            P.Adj a.castSucc b.castSucc := by
          simpa [P, hσa, hσb] using hmap.symm
        exact hf.trans (hold.trans hgmap)
      have hPupper : FractionalCoveredSizeAtMost P
          (stabilityThreshold (n + 1)) :=
        fractionalCoveredSizeAtMost_relabel hupperc σ
      exact (d.resolveRoot hd p P hPprefix hPupper).iso giso
    exact hresult.compl

end StageData

/-! ## The complete order-zero through order-22 trace -/

/-- A coherent collection of the 22 one-vertex extension stages. -/
structure TraceData where
  level : (n : Fin 23) → Array (BitVec (edgeCount n))
  stage : (n : Fin 22) → StageData n

namespace TraceData

def Coherent (d : TraceData) : Prop :=
  (d.level 0).size = 1 ∧ (d.level 0).getD 0 0 = 0 ∧
    (d.level 22).size = 0 ∧
    (∀ n : Fin 22, (d.stage n).parents = d.level ⟨n.1, by omega⟩) ∧
    (∀ n : Fin 22, (d.stage n).children = d.level ⟨n.1 + 1, by omega⟩)

instance (d : TraceData) : Decidable d.Coherent := by
  unfold Coherent
  infer_instance

def Valid (d : TraceData) : Prop :=
  d.Coherent ∧ ∀ n : Fin 22, (d.stage n).Valid

instance (d : TraceData) : Decidable d.Valid := by
  unfold Valid
  infer_instance

def checkCoherent (d : TraceData) : Bool := decide d.Coherent

@[simp] theorem checkCoherent_eq_true_iff (d : TraceData) :
    d.checkCoherent = true ↔ d.Coherent := by simp [checkCoherent]

/-- A standard upper chain at every order inspected by the trace. -/
def IsFullUpperChain (C : ∀ n : ℕ, SimpleGraph (Fin n)) : Prop :=
  (∀ n ≤ 22,
    FractionalCoveredSizeAtMost (C n) (stabilityThreshold n)) ∧
  (∀ n < 22, IsInitialVertexExtension (C n) (C (n + 1)))

/-- Classification conclusion, with a temporary complement-pentagon branch.
The next section removes this branch using the self-complementarity of `C₅`. -/
def TraceConclusion (C : ∀ n : ℕ, SimpleGraph (Fin n)) : Prop :=
  IsPentagonExceptional (C 17) ∨ IsPentagonExceptional (C 17)ᶜ ∨
    CloseToBipartite (C 22) 2 ∨ CloseToBipartite (C 22)ᶜ 2

theorem Valid.traceFullUpperChain (d : TraceData) (hd : d.Valid)
    (C : ∀ n : ℕ, SimpleGraph (Fin n)) (hC : IsFullUpperChain C) :
    TraceConclusion C := by
  have progress : ∀ (m : ℕ) (hm : m ≤ 22),
      StageData.IsOrientedRepresented (d.level ⟨m, by omega⟩) (C m) ∨
        TraceConclusion C := by
    intro m hm
    induction m with
    | zero =>
        left
        have hsize := hd.1.1
        let i : Fin (d.level 0).size := ⟨0, by omega⟩
        refine ⟨i, Or.inl ⟨?_⟩⟩
        let e : C 0 ≃g graphOfBits (d.level 0)[i] :=
          { __ := Equiv.refl _
            map_rel_iff' := by
              intro u
              exact Fin.elim0 u }
        exact e
    | succ m ih =>
        have hm22 : m < 22 := by omega
        rcases ih (by omega) with hrep | hdone
        · let s : Fin 22 := ⟨m, hm22⟩
          have hparents : (d.stage s).parents =
              d.level ⟨m, by omega⟩ := hd.1.2.2.2.1 s
          have hchildren : (d.stage s).children =
              d.level ⟨m + 1, by omega⟩ := hd.1.2.2.2.2 s
          have hstage := (d.stage s).resolveExtension (hd.2 s)
            (C m) (C (m + 1)) (hC.2 m hm22)
            (by simpa [hparents] using hrep) (hC.1 (m + 1) (by omega))
          rcases hstage with hnext | hpent | hpentc | hclose | hclosec
          · left
            simpa [hchildren] using hnext
          · right; left
            have hm : m + 1 = 17 := hpent.1
            rw [← hm]
            exact hpent.2
          · right; right; left
            have hm : m + 1 = 17 := hpentc.1
            rw [← hm]
            exact hpentc.2
          · right; right; right; left
            have hm : m + 1 = 22 := hclose.1
            rw [← hm]
            exact hclose.2
          · right; right; right; right
            have hm : m + 1 = 22 := hclosec.1
            rw [← hm]
            exact hclosec.2
        · exact Or.inr hdone
  rcases progress 22 (by omega) with hrep | hdone
  · obtain ⟨i, _⟩ := hrep
    have hz : (d.level ⟨22, by omega⟩).size = 0 := by
      simpa using hd.1.2.2.1
    exact Fin.elim0 (Fin.cast hz i)
  · exact hdone

end TraceData

/-! ## Self-complementarity of the pentagon exception -/

/-- Multiplication by two modulo five, written explicitly to keep the finite
calculation transparent to the kernel. -/
def pentagonComplementPerm : Equiv.Perm (Fin 5) where
  toFun i := ⟨(2 * i.1) % 5, Nat.mod_lt _ (by omega)⟩
  invFun i := ⟨(3 * i.1) % 5, Nat.mod_lt _ (by omega)⟩
  left_inv i := by
    apply Fin.ext
    fin_cases i <;> rfl
  right_inv i := by
    apply Fin.ext
    fin_cases i <;> rfl

lemma cycleGraph_five_complement (a b : Fin 5) (hab : a ≠ b) :
    ¬(SimpleGraph.cycleGraph 5).Adj a b ↔
      (SimpleGraph.cycleGraph 5).Adj
        (pentagonComplementPerm a) (pentagonComplementPerm b) := by
  fin_cases a <;> fin_cases b <;>
    simp_all [SimpleGraph.cycleGraph, pentagonComplementPerm] <;> decide

lemma isPentagonBlowup_compl {α : Type*} {G : SimpleGraph α}
    {blob : α → Fin 5} (h : IsPentagonBlowup G blob) :
    IsPentagonBlowup Gᶜ (pentagonComplementPerm ∘ blob) := by
  constructor
  · exact pentagonComplementPerm.surjective.comp h.1
  · intro u v huv
    have hblob : blob u ≠ blob v := by
      intro heq
      exact huv (congrArg pentagonComplementPerm heq)
    have huv' : u ≠ v := fun huvEq ↦ hblob (congrArg blob huvEq)
    rw [SimpleGraph.compl_adj, and_iff_right huv', h.2 hblob]
    exact cycleGraph_five_complement (blob u) (blob v) hblob

lemma edgeFlipDistance_compl {α : Type*} [Fintype α] [DecidableEq α]
    (G H : SimpleGraph α) : edgeFlipDistance Gᶜ Hᶜ = edgeFlipDistance G H := by
  classical
  unfold edgeFlipDistance
  rw [Nat.add_comm
    (G.edgeFinset \ H.edgeFinset).card
    (H.edgeFinset \ G.edgeFinset).card]
  apply congrArg₂ (fun a b : ℕ ↦ a + b)
  · apply congrArg Finset.card
    ext e
    induction e using Sym2.inductionOn with
    | _ u v =>
        simp only [Finset.mem_sdiff, SimpleGraph.mem_edgeFinset,
          SimpleGraph.compl_adj]
        constructor
        · rintro ⟨⟨huv, hnG⟩, hnHc⟩
          have hH : H.Adj u v := by
            by_contra hnH
            exact hnHc ⟨huv, hnH⟩
          exact ⟨hH, hnG⟩
        · rintro ⟨hH, hnG⟩
          exact ⟨⟨H.ne_of_adj hH, hnG⟩, fun hHc ↦ hHc.2 hH⟩
  · apply congrArg Finset.card
    ext e
    induction e using Sym2.inductionOn with
    | _ u v =>
        simp only [Finset.mem_sdiff, SimpleGraph.mem_edgeFinset,
          SimpleGraph.compl_adj]
        constructor
        · rintro ⟨⟨huv, hnH⟩, hnGc⟩
          have hG : G.Adj u v := by
            by_contra hnG
            exact hnGc ⟨huv, hnG⟩
          exact ⟨hG, hnH⟩
        · rintro ⟨hG, hnH⟩
          exact ⟨⟨G.ne_of_adj hG, hnH⟩, fun hGc ↦ hGc.2 hG⟩

theorem isPentagonExceptional_compl {α : Type*}
    [Fintype α] [DecidableEq α] {G : SimpleGraph α}
    (h : IsPentagonExceptional G) : IsPentagonExceptional Gᶜ := by
  refine ⟨h.1, ?_⟩
  rcases h.2 with ⟨blob, hblob⟩ | ⟨H, blob, hblob, hflip⟩
  · left
    exact ⟨pentagonComplementPerm ∘ blob, isPentagonBlowup_compl hblob⟩
  · right
    refine ⟨Hᶜ, pentagonComplementPerm ∘ blob,
      isPentagonBlowup_compl hblob, ?_⟩
    simpa [edgeFlipDistance_compl] using hflip

theorem isPentagonExceptional_iff_compl {α : Type*}
    [Fintype α] [DecidableEq α] (G : SimpleGraph α) :
    IsPentagonExceptional Gᶜ ↔ IsPentagonExceptional G := by
  constructor
  · intro h
    have := isPentagonExceptional_compl h
    simpa using this
  · exact isPentagonExceptional_compl

/-! ## Downward normalization and the classification theorem

The published finite search starts at the unique graph of order zero.  The
classification interface, on the other hand, is intentionally stated only
for a supplied chain from order 17 through order 22.  The following lemmas
bridge those formulations.  Repeated deletion averaging constructs orders
2 through 16 below a relabelled copy of the supplied order-17 graph; orders
zero and one are then harmless because they contain no triangles. -/

private lemma stabilityThreshold_scale_trace (m : ℕ) (hm : 2 ≤ m) :
    stabilityThreshold (m + 1) =
      ((m + 1 : ℕ) : ℝ) * stabilityThreshold m /
        (((m + 1 : ℕ) : ℝ) - 2) := by
  have hne : (((m + 1 : ℕ) : ℝ) - 2) ≠ 0 := by
    have hm' : (1 : ℝ) < m := by
      exact_mod_cast (show 1 < m by omega)
    norm_num
    linarith
  apply (eq_div_iff hne).2
  simp only [stabilityThreshold, Nat.cast_add, Nat.cast_one]
  ring

private lemma fractionalCoveredSizeAtMost_induce_erase_trace
    {α : Type*} [Fintype α] [DecidableEq α]
    (G : SimpleGraph α) (u : α) (q : ℝ)
    (hdel : DeletionFractionalCoveredSizeAtMost G u q) :
    FractionalCoveredSizeAtMost
      (G.induce ((univ.erase u : Finset α) : Set α)) q := by
  classical
  let S : Finset α := univ.erase u
  let H : SimpleGraph S := G.induce (S : Set α)
  intro wR wB hwR hwB
  let vR : Finset α → ℝ := extendInducedWeight S wR
  let vB : Finset α → ℝ := extendInducedWeight S wB
  have huS : u ∉ S := by simp [S]
  have hzero (K : SimpleGraph α) (w : Finset S → ℝ) :
      ∀ e ∈ K.edgeFinset, u ∈ e.toFinset →
        fractionalEdgeLoad K (extendInducedWeight S w) e = 0 := by
    intro e he hue
    induction e using Sym2.inductionOn with
    | _ a b =>
        have hua : u = a ∨ u = b := by simpa using hue
        rcases hua with rfl | rfl
        · exact fractionalEdgeLoad_extendInducedWeight_eq_zero_of_not_mem
            K S w u b huS
        · rw [show s(a, u) = s(u, a) from
              Sym2.sound (Sym2.Rel.swap a u)]
          exact fractionalEdgeLoad_extendInducedWeight_eq_zero_of_not_mem
            K S w u a huS
  have hvR : IsDeletionPacking G u vR := by
    refine ⟨hwR.extendInduced, ?_⟩
    exact hzero G wR
  have hvB : IsDeletionPacking Gᶜ u vB := by
    refine ⟨hwB.extendInduced_compl, ?_⟩
    exact hzero Gᶜ wB
  have hupper := hdel vR vB hvR hvB
  dsimp only [vR, vB] at hupper
  rw [twoColorCoveredSize, fractionalCoveredSize_extendInducedWeight,
    fractionalCoveredSize_extendInducedWeight, compl_induce] at hupper
  simpa only [H, S, twoColorCoveredSize] using hupper

private theorem exists_standard_deletion_step_trace
    (m : ℕ) (hm : 2 ≤ m) (G : SimpleGraph (Fin (m + 1)))
    (hG : FractionalCoveredSizeAtMost G (stabilityThreshold (m + 1))) :
    ∃ (H : SimpleGraph (Fin m)) (P : SimpleGraph (Fin (m + 1)))
      (φ : Fin (m + 1) ≃ Fin (m + 1)),
      FractionalCoveredSizeAtMost H (stabilityThreshold m) ∧
      FractionalCoveredSizeAtMost P (stabilityThreshold (m + 1)) ∧
      IsInitialVertexExtension H P ∧ P = G.map φ.toEmbedding := by
  have hcard : 3 ≤ Fintype.card (Fin (m + 1)) := by simp; omega
  have hscale : stabilityThreshold (m + 1) ≤
      (Fintype.card (Fin (m + 1)) : ℝ) * stabilityThreshold m /
        ((Fintype.card (Fin (m + 1)) : ℝ) - 2) := by
    rw [Fintype.card_fin, ← stabilityThreshold_scale_trace m hm]
  obtain ⟨u, hu⟩ := exists_deletion_fractionalCoveredSizeAtMost
    G (stabilityThreshold (m + 1)) (stabilityThreshold m) hcard hG hscale
  let S : Finset (Fin (m + 1)) := univ.erase u
  have hScard : Fintype.card S = m := by
    rw [Fintype.card_coe]
    simp [S]
  let e : S ≃ Fin m := Fintype.equivFinOfCardEq hScard
  obtain ⟨φ, hφ⟩ := Equiv.Perm.exists_extending_pair
    (fun i : Fin m ↦ ((e.symm i : S) : Fin (m + 1)))
    (fun i : Fin m ↦ i.castSucc)
    (Subtype.val_injective.comp e.symm.injective) (Fin.castSucc_injective m)
  let K : SimpleGraph S := G.induce (S : Set (Fin (m + 1)))
  let H : SimpleGraph (Fin m) := K.map e.toEmbedding
  let P : SimpleGraph (Fin (m + 1)) := G.map φ.toEmbedding
  have hK : FractionalCoveredSizeAtMost K (stabilityThreshold m) := by
    simpa only [K, S] using fractionalCoveredSizeAtMost_induce_erase_trace
      G u (stabilityThreshold m) hu
  have hH : FractionalCoveredSizeAtMost H (stabilityThreshold m) :=
    fractionalCoveredSizeAtMost_relabel hK e
  have hP : FractionalCoveredSizeAtMost P
      (stabilityThreshold (m + 1)) :=
    fractionalCoveredSizeAtMost_relabel hG φ
  refine ⟨H, P, φ, hH, hP, ?_, rfl⟩
  intro a b
  dsimp only [H, K, P]
  have hleft :
      ((G.induce (S : Set (Fin (m + 1)))).map e.toEmbedding).Adj a b ↔
        (G.induce (S : Set (Fin (m + 1)))).Adj (e.symm a) (e.symm b) := by
    rw [← SimpleGraph.comap_symm (G.induce (S : Set (Fin (m + 1)))) e]
    rfl
  rw [hleft]
  change G.Adj ((e.symm a : S) : Fin (m + 1))
      ((e.symm b : S) : Fin (m + 1)) ↔
    (G.map φ.toEmbedding).Adj a.castSucc b.castSucc
  rw [← hφ a, ← hφ b]
  exact (SimpleGraph.map_adj_apply
    (G := G) (f := φ.toEmbedding)
      (a := ((e.symm a : S) : Fin (m + 1)))
      (b := ((e.symm b : S) : Fin (m + 1)))).symm

private def replaceTraceGraph
    (C : ∀ k : ℕ, SimpleGraph (Fin k)) (m : ℕ)
    (G : SimpleGraph (Fin m)) : ∀ k : ℕ, SimpleGraph (Fin k) :=
  fun k ↦ if h : k = m then
    cast (congrArg (fun r ↦ SimpleGraph (Fin r)) h.symm) G
  else C k

@[simp] private lemma replaceTraceGraph_same
    (C : ∀ k : ℕ, SimpleGraph (Fin k)) (m : ℕ)
    (G : SimpleGraph (Fin m)) : replaceTraceGraph C m G m = G := by
  simp [replaceTraceGraph]

private lemma replaceTraceGraph_of_ne
    (C : ∀ k : ℕ, SimpleGraph (Fin k)) (m k : ℕ)
    (G : SimpleGraph (Fin m)) (hkm : k ≠ m) :
    replaceTraceGraph C m G k = C k := by
  simp [replaceTraceGraph, hkm]

private theorem exists_standard_fractional_upper_chain_two :
    ∀ hi : ℕ, 2 ≤ hi → ∀ G : SimpleGraph (Fin hi),
      FractionalCoveredSizeAtMost G (stabilityThreshold hi) →
      ∃ (C : ∀ m : ℕ, SimpleGraph (Fin m)) (φ : Fin hi ≃ Fin hi),
        IsStandardFractionalUpperChain C 2 hi ∧
          C hi = G.map φ.toEmbedding := by
  intro hi hhi
  induction hi, hhi using Nat.le_induction with
  | base =>
      intro G hG
      let C : ∀ m : ℕ, SimpleGraph (Fin m) :=
        replaceTraceGraph (fun m ↦ (⊥ : SimpleGraph (Fin m))) 2 G
      refine ⟨C, Equiv.refl (Fin 2), ?_, ?_⟩
      · constructor
        · intro m hm2 hmle
          have hm : m = 2 := by omega
          subst m
          simpa only [C, replaceTraceGraph_same] using hG
        · intro m hm2 hmlt
          omega
      · change G = G.map (Equiv.refl (Fin 2)).toEmbedding
        ext a b
        simp [SimpleGraph.map_adj]
  | succ m hm ih =>
      intro G hG
      obtain ⟨H, P, φ, hH, hP, hHP, hPiso⟩ :=
        exists_standard_deletion_step_trace m hm G hG
      obtain ⟨C, ψ, hC, htop⟩ := ih H hH
      obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair
        (fun i : Fin m ↦ i.castSucc)
        (fun i : Fin m ↦ (ψ i).castSucc)
        (Fin.castSucc_injective m)
        ((Fin.castSucc_injective m).comp ψ.injective)
      let P' : SimpleGraph (Fin (m + 1)) := P.map σ.toEmbedding
      have hP' : FractionalCoveredSizeAtMost P'
          (stabilityThreshold (m + 1)) :=
        fractionalCoveredSizeAtMost_relabel hP σ
      have hCP : IsInitialVertexExtension (C m) P' := by
        intro a b
        have hleft : (C m).Adj a b ↔
            H.Adj (ψ.symm a) (ψ.symm b) := by
          rw [htop, ← SimpleGraph.comap_symm H ψ]
          rfl
        rw [hleft, hHP]
        change P.Adj (ψ.symm a).castSucc (ψ.symm b).castSucc ↔
          (P.map σ.toEmbedding).Adj a.castSucc b.castSucc
        have hσa : σ ((ψ.symm a).castSucc) = a.castSucc := by
          simpa using hσ (ψ.symm a)
        have hσb : σ ((ψ.symm b).castSucc) = b.castSucc := by
          simpa using hσ (ψ.symm b)
        rw [← hσa, ← hσb]
        exact (SimpleGraph.map_adj_apply
          (G := P) (f := σ.toEmbedding)
            (a := (ψ.symm a).castSucc)
            (b := (ψ.symm b).castSucc)).symm
      let C' : ∀ r : ℕ, SimpleGraph (Fin r) :=
        replaceTraceGraph C (m + 1) P'
      refine ⟨C', φ.trans σ, ?_, ?_⟩
      · constructor
        · intro r hr2 hrle
          by_cases hr : r = m + 1
          · subst r
            simpa only [C', replaceTraceGraph_same] using hP'
          · dsimp only [C']
            rw [replaceTraceGraph_of_ne C (m + 1) r P' hr]
            exact hC.1 r hr2 (by omega)
        · intro r hr2 hrlt
          by_cases hrm : r = m
          · subst r
            dsimp only [C']
            rw [replaceTraceGraph_of_ne C (m + 1) m P' (by omega),
              replaceTraceGraph_same]
            exact hCP
          · have hrm' : r < m := by omega
            dsimp only [C']
            rw [replaceTraceGraph_of_ne C (m + 1) r P' (by omega),
              replaceTraceGraph_of_ne C (m + 1) (r + 1) P' (by omega)]
            exact hC.2 r hr2 hrm'
      · dsimp only [C']
        rw [replaceTraceGraph_same]
        dsimp only [P']
        rw [hPiso, SimpleGraph.map_map]
        rfl

private lemma fractionalCoveredSizeAtMost_small
    (n : ℕ) (hn : n < 3) (G : SimpleGraph (Fin n)) :
    FractionalCoveredSizeAtMost G (stabilityThreshold n) := by
  classical
  have zero_size (K : SimpleGraph (Fin n)) (w : Finset (Fin n) → ℝ) :
      fractionalSize K w = 0 := by
    rw [fractionalSize]
    apply sum_eq_zero
    intro t ht
    have htcard : t.card = 3 :=
      (SimpleGraph.mem_cliqueFinset_iff.mp ht).card_eq
    have htuniv : t.card ≤ n := by
      have := card_le_card (show t ⊆ (univ : Finset (Fin n)) from subset_univ t)
      simpa using this
    omega
  intro wR wB hwR hwB
  rw [twoColorCoveredSize, fractionalCoveredSize, fractionalCoveredSize,
    zero_size G wR, zero_size Gᶜ wB]
  interval_cases n <;> norm_num [stabilityThreshold]

/-- Pad a standard chain beginning at order two by the unique restrictions at
orders zero and one. -/
private theorem pad_standard_chain_to_zero
    (C : ∀ m : ℕ, SimpleGraph (Fin m))
    (hC : IsStandardFractionalUpperChain C 2 17) :
    ∃ D : ∀ m : ℕ, SimpleGraph (Fin m),
      IsStandardFractionalUpperChain D 0 17 ∧ D 17 = C 17 := by
  let D : ∀ m : ℕ, SimpleGraph (Fin m) := fun m ↦
    if m < 2 then (⊥ : SimpleGraph (Fin m)) else C m
  refine ⟨D, ?_, by simp [D]⟩
  constructor
  · intro m hm0 hm17
    by_cases hm2 : 2 ≤ m
    · have hmnlt : ¬m < 2 := by omega
      simpa only [D, if_neg hmnlt] using hC.1 m hm2 hm17
    · have hm3 : m < 3 := by omega
      exact fractionalCoveredSizeAtMost_small m hm3 (D m)
  · intro m hm0 hm17
    by_cases hm2 : 2 ≤ m
    · have hmnlt : ¬m < 2 := by omega
      have hm1nlt : ¬m + 1 < 2 := by omega
      simpa only [D, if_neg hmnlt, if_neg hm1nlt] using hC.2 m hm2 hm17
    · have hm : m = 0 ∨ m = 1 := by omega
      rcases hm with rfl | rfl
      · intro a
        exact Fin.elim0 a
      · intro a b
        have hab : a = b := Subsingleton.elim _ _
        subst b
        simp [D]

/-- Extend a relabelled order-17 endpoint along a supplied standard chain.
At every successor, a permutation of the new vertex set is chosen extending
the permutation already used on the old vertices. -/
private theorem extend_relabelled_standard_chain :
    ∀ hi : ℕ, 17 ≤ hi →
      ∀ (C D : ∀ m : ℕ, SimpleGraph (Fin m))
        (ψ : Fin 17 ≃ Fin 17),
        IsStandardFractionalUpperChain C 17 hi →
        IsStandardFractionalUpperChain D 0 17 →
        D 17 = (C 17).map ψ.toEmbedding →
        ∃ (E : ∀ m : ℕ, SimpleGraph (Fin m)) (φ : Fin hi ≃ Fin hi),
          IsStandardFractionalUpperChain E 0 hi ∧
          E 17 = (C 17).map ψ.toEmbedding ∧
          E hi = (C hi).map φ.toEmbedding := by
  intro hi hhi
  induction hi, hhi using Nat.le_induction with
  | base =>
      intro C D ψ hC hD htop
      exact ⟨D, ψ, hD, htop, htop⟩
  | succ m hm ih =>
      intro C D ψ hC hD htop
      have hCm : IsStandardFractionalUpperChain C 17 m := by
        constructor
        · intro r hr17 hrm
          exact hC.1 r hr17 (by omega)
        · intro r hr17 hrm
          exact hC.2 r hr17 (by omega)
      obtain ⟨E, τ, hE, hE17, hEm⟩ := ih C D ψ hCm hD htop
      obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair
        (fun i : Fin m ↦ i.castSucc)
        (fun i : Fin m ↦ (τ i).castSucc)
        (Fin.castSucc_injective m)
        ((Fin.castSucc_injective m).comp τ.injective)
      let P : SimpleGraph (Fin (m + 1)) := (C (m + 1)).map σ.toEmbedding
      have hP : FractionalCoveredSizeAtMost P
          (stabilityThreshold (m + 1)) :=
        fractionalCoveredSizeAtMost_relabel
          (hC.1 (m + 1) (by omega) (by omega)) σ
      have hEP : IsInitialVertexExtension (E m) P := by
        intro a b
        have hleft : (E m).Adj a b ↔
            (C m).Adj (τ.symm a) (τ.symm b) := by
          rw [hEm, ← SimpleGraph.comap_symm (C m) τ]
          rfl
        rw [hleft, hC.2 m (by omega) (by omega)]
        change (C (m + 1)).Adj (τ.symm a).castSucc
            (τ.symm b).castSucc ↔
          ((C (m + 1)).map σ.toEmbedding).Adj a.castSucc b.castSucc
        have hσa : σ ((τ.symm a).castSucc) = a.castSucc := by
          simpa using hσ (τ.symm a)
        have hσb : σ ((τ.symm b).castSucc) = b.castSucc := by
          simpa using hσ (τ.symm b)
        rw [← hσa, ← hσb]
        exact (SimpleGraph.map_adj_apply
          (G := C (m + 1)) (f := σ.toEmbedding)
            (a := (τ.symm a).castSucc)
            (b := (τ.symm b).castSucc)).symm
      let E' : ∀ r : ℕ, SimpleGraph (Fin r) :=
        replaceTraceGraph E (m + 1) P
      refine ⟨E', σ, ?_, ?_, ?_⟩
      · constructor
        · intro r hr0 hrle
          by_cases hr : r = m + 1
          · subst r
            simpa only [E', replaceTraceGraph_same] using hP
          · dsimp only [E']
            rw [replaceTraceGraph_of_ne E (m + 1) r P hr]
            exact hE.1 r hr0 (by omega)
        · intro r hr0 hrlt
          by_cases hrm : r = m
          · subst r
            dsimp only [E']
            rw [replaceTraceGraph_of_ne E (m + 1) m P (by omega),
              replaceTraceGraph_same]
            exact hEP
          · have hrm' : r < m := by omega
            dsimp only [E']
            rw [replaceTraceGraph_of_ne E (m + 1) r P (by omega),
              replaceTraceGraph_of_ne E (m + 1) (r + 1) P (by omega)]
            exact hE.2 r hr0 hrm'
      · dsimp only [E']
        rw [replaceTraceGraph_of_ne E (m + 1) 17 P (by omega)]
        exact hE17
      · dsimp only [E']
        rw [replaceTraceGraph_same]

/-- Soundness of an accepted incremental search trace for the exact finite
classification interface used by the stability induction.  The hypotheses
contain no graph enumeration: a generated artifact proves `d.Valid` from its
independently checked row shards. -/
theorem TraceData.Valid.finiteStabilityClassification
    (d : TraceData) (hd : d.Valid) : FiniteStabilityClassification := by
  intro C hC
  obtain ⟨Ctwo, φ, hCtwo, htop17⟩ :=
    exists_standard_fractional_upper_chain_two 17 (by omega) (C 17)
      (hC.1 17 (by omega) (by omega))
  obtain ⟨D, hD, hD17⟩ := pad_standard_chain_to_zero Ctwo hCtwo
  have hDtop : D 17 = (C 17).map φ.toEmbedding := hD17.trans htop17
  obtain ⟨E, τ, hE, hE17, hE22⟩ :=
    extend_relabelled_standard_chain 22 (by omega) C D φ hC hD hDtop
  have hfull : TraceData.IsFullUpperChain E := by
    constructor
    · intro n hn
      exact hE.1 n (by omega) hn
    · intro n hn
      exact hE.2 n (by omega) hn
  have hmap17 : ((C 17).map φ.toEmbedding).map φ.symm.toEmbedding = C 17 := by
    rw [SimpleGraph.map_map]
    simpa using (C 17).map_id
  have hmap22 : ((C 22).map τ.toEmbedding).map τ.symm.toEmbedding = C 22 := by
    rw [SimpleGraph.map_map]
    simpa using (C 22).map_id
  have hcmap22 : ((C 22).map τ.toEmbedding)ᶜ.map τ.symm.toEmbedding =
      (C 22)ᶜ := by
    rw [← compl_map_equiv ((C 22).map τ.toEmbedding) τ.symm, hmap22]
  rcases TraceData.Valid.traceFullUpperChain d hd E hfull with
      hpent | hpentc | hclose | hclosec
  · left
    rw [hE17] at hpent
    have hback := isPentagonExceptional_relabel hpent φ.symm
    simpa only [hmap17] using hback
  · left
    have hpent' : IsPentagonExceptional (E 17) :=
      (isPentagonExceptional_iff_compl (E 17)).mp hpentc
    rw [hE17] at hpent'
    have hback := isPentagonExceptional_relabel hpent' φ.symm
    simpa only [hmap17] using hback
  · right; left
    rw [hE22] at hclose
    have hback := closeToBipartite_relabel hclose τ.symm
    simpa only [hmap22] using hback
  · right; right
    rw [hE22] at hclosec
    have hback := closeToBipartite_relabel hclosec τ.symm
    simpa only [hcmap22] using hback

end IncrementalStabilityTrace
end Erdos76
