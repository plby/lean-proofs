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
import ErdosProblems.Erdos76.CertificateExhaustion
import ErdosProblems.Erdos76.FractionalStabilityInduction

/-!
# Finite certificate interfaces for the stability obligations

This file is the data-independent checker for the two finite obligations used
by the stability induction.  It does not contain the output of a graph search.

The important negative certificate is a pair of sparse fractional triangle
packings, one in each colour.  A natural-number inequality checks that their
covered size is strictly larger than the sharp threshold.  Such a certificate
contradicts `FractionalCoveredSizeAtMost`.

Search output may be canonicalized.  A routed entry stores a source mask, a
canonical target mask, an explicit checked permutation, and a colour-swap bit.
All semantic transport is proved below.  The final finite checkers quantify
only over finite Boolean graph codes and finite certificate lists.
-/

open Finset
open scoped BigOperators

namespace Erdos76
namespace FiniteStabilityCertificateChecker

open CertificateChecker
open CertificateChecker.PackingCert
open CertificateExhaustion

/-! ## A trivially exhaustive finite graph code -/

/-- A full Boolean adjacency table.  The decoder removes loops and closes the
relation under symmetry, so every value decodes to a simple graph. -/
abbrev GraphCode (n : ℕ) := Fin n → Fin n → Bool

/-- Decode a full Boolean adjacency table. -/
def graphOfCode {n : ℕ} (c : GraphCode n) : SimpleGraph (Fin n) :=
  SimpleGraph.fromRel fun i j ↦ c i j = true

instance {n : ℕ} (c : GraphCode n) : DecidableRel (graphOfCode c).Adj := by
  dsimp only [graphOfCode]
  infer_instance

/-- The (noncomputable) Boolean code used only in semantic soundness.  The
checker itself consumes concrete Boolean functions. -/
noncomputable def codeOfGraph {n : ℕ} (G : SimpleGraph (Fin n)) : GraphCode n := by
  classical
  exact fun i j ↦ decide (G.Adj i j)

@[simp] theorem graphOfCode_codeOfGraph {n : ℕ} (G : SimpleGraph (Fin n)) :
    graphOfCode (codeOfGraph G) = G := by
  classical
  ext i j
  simp only [graphOfCode, SimpleGraph.fromRel_adj]
  simp only [codeOfGraph, decide_eq_true_eq]
  constructor
  · rintro ⟨_hij, hij | hji⟩
    · exact hij
    · exact (G.adj_comm j i).mp hji
  · intro hij
    exact ⟨hij.ne, Or.inl hij⟩

/-- Full-table view of the compact upper-triangular graph mask. -/
def codeOfBits {n : ℕ} (bits : BitVec (edgeCount n)) : GraphCode n :=
  fun i j ↦ bits.getLsbD (edgeIndex i.1 j.1)

@[simp] theorem graphOfCode_codeOfBits {n : ℕ}
    (bits : BitVec (edgeCount n)) :
    graphOfCode (codeOfBits bits) = graphOfBits bits :=
  rfl

/-! ## Explicit finite witnesses for the structural conclusions -/

/-- Proof-free witnesses for the two alternatives in
`IsPentagonExceptional`. -/
inductive PentagonWitness (n : ℕ) where
  | blowup (blob : Fin n → Fin 5)
  | oneFlip (base : GraphCode n) (blob : Fin n → Fin 5)
  deriving DecidableEq, Fintype

namespace PentagonWitness

/-- Executable flip distance with the adjacency decision procedures exposed
as ordinary instance arguments. -/
def flipDistance {n : ℕ} (G H : SimpleGraph (Fin n))
    [DecidableRel G.Adj] [DecidableRel H.Adj] : ℕ :=
  (G.edgeFinset \ H.edgeFinset).card + (H.edgeFinset \ G.edgeFinset).card

lemma flipDistance_eq_edgeFlipDistance {n : ℕ} (G H : SimpleGraph (Fin n))
    [DecidableRel G.Adj] [DecidableRel H.Adj] :
    flipDistance G H = edgeFlipDistance G H := by
  classical
  unfold flipDistance edgeFlipDistance
  apply congrArg₂ (fun a b : ℕ ↦ a + b)
  · apply congrArg Finset.card
    ext e
    simp only [Finset.mem_sdiff, SimpleGraph.mem_edgeFinset]
  · apply congrArg Finset.card
    ext e
    simp only [Finset.mem_sdiff, SimpleGraph.mem_edgeFinset]

/-- Fully bounded formulation of a pentagon blow-up witness. -/
def BlowupValid {n : ℕ} (G : SimpleGraph (Fin n))
    (blob : Fin n → Fin 5) : Prop :=
  (∀ a : Fin 5, ∃ u : Fin n, blob u = a) ∧
    ∀ u v : Fin n, blob u ≠ blob v →
      (G.Adj u v ↔ (SimpleGraph.cycleGraph 5).Adj (blob u) (blob v))

instance {n : ℕ} (c : GraphCode n) (blob : Fin n → Fin 5) :
    Decidable (BlowupValid (graphOfCode c) blob) := by
  unfold BlowupValid
  infer_instance

/-- Semantic validity of a pentagon witness. -/
def Valid {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (w : PentagonWitness n) : Prop :=
  match w with
  | .blowup blob => BlowupValid G blob
  | .oneFlip base blob =>
      BlowupValid (graphOfCode base) blob ∧
        flipDistance G (graphOfCode base) = 1

instance {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (w : PentagonWitness n) : Decidable (w.Valid G) := by
  cases w <;> unfold Valid BlowupValid flipDistance <;> infer_instance

/-- Executable pentagon-witness verifier. -/
def check {n : ℕ} (c : GraphCode n) (w : PentagonWitness n) : Bool :=
  decide (w.Valid (graphOfCode c))

@[simp] theorem check_eq_true_iff {n : ℕ} (c : GraphCode n)
    (w : PentagonWitness n) :
    w.check c = true ↔ w.Valid (graphOfCode c) := by
  simp [check]

/-- A valid proof-free witness gives the semantic exceptional predicate. -/
theorem Valid.isPentagonExceptional {n : ℕ} {G : SimpleGraph (Fin n)}
    [DecidableRel G.Adj] {w : PentagonWitness n} (hw : w.Valid G) (hn : n ≤ 25) :
    IsPentagonExceptional G := by
  refine ⟨by simpa using hn, ?_⟩
  cases w with
  | blowup blob =>
      exact Or.inl ⟨blob, ⟨hw.1, fun h ↦ hw.2 _ _ h⟩⟩
  | oneFlip base blob =>
      exact Or.inr ⟨graphOfCode base, blob,
        ⟨hw.1.1, fun h ↦ hw.1.2 _ _ h⟩,
        by simpa [flipDistance_eq_edgeFlipDistance] using hw.2⟩

/-- Conversely, at an order at most 25 the semantic predicate has finite
proof-free witness data. -/
theorem exists_valid_iff {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (hn : n ≤ 25) :
    (∃ w : PentagonWitness n, w.Valid G) ↔ IsPentagonExceptional G := by
  constructor
  · rintro ⟨w, hw⟩
    exact hw.isPentagonExceptional hn
  · rintro ⟨_hcard, h⟩
    rcases h with ⟨blob, hblob⟩ | ⟨H, blob, hblob, hflip⟩
    · refine ⟨.blowup blob, ?_⟩
      refine ⟨?_, ?_⟩
      · intro a
        exact hblob.1 a
      · intro u v h
        exact hblob.2 h
    · let c := codeOfGraph H
      refine ⟨.oneFlip c blob, ?_⟩
      refine ⟨?_, ?_⟩
      · refine ⟨?_, ?_⟩
        · intro a
          exact hblob.1 a
        · intro u v h
          simpa [c] using hblob.2 h
      · simpa [c, flipDistance_eq_edgeFlipDistance] using hflip

end PentagonWitness

/-- A Boolean side of a bipartition. -/
structure CloseWitness (n : ℕ) where
  side : Fin n → Bool
  deriving DecidableEq, Fintype

namespace CloseWitness

/-- The set represented by a Boolean side function. -/
def sideSet {n : ℕ} (w : CloseWitness n) : Set (Fin n) :=
  {v | w.side v = true}

/-- Executable same-side test on an unordered pair. -/
def sameSideBool {n : ℕ} (w : CloseWitness n) : Sym2 (Fin n) → Bool :=
  Sym2.lift ⟨fun u v ↦ w.side u == w.side v,
    fun u v ↦ by simp [eq_comm]⟩

@[simp] lemma sameSideBool_eq_true_iff {n : ℕ} (w : CloseWitness n)
    (e : Sym2 (Fin n)) :
    w.sameSideBool e = true ↔ SameSide w.sideSet e := by
  induction e using Sym2.inductionOn with
  | _ u v =>
      simp only [sameSideBool, Sym2.lift_mk, sameSide_mk, sideSet,
        Set.mem_setOf_eq]
      cases w.side u <;> cases w.side v <;> decide

/-- Finite validity condition for a close-to-bipartite witness. -/
def Valid {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (k : ℕ) (w : CloseWitness n) : Prop :=
  (G.edgeFinset.filter fun e ↦ w.sameSideBool e = true).card ≤ k

instance {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (k : ℕ) (w : CloseWitness n) : Decidable (w.Valid G k) := by
  unfold Valid
  infer_instance

/-- Executable close-to-bipartite witness verifier. -/
def check {n : ℕ} (c : GraphCode n) (k : ℕ) (w : CloseWitness n) : Bool :=
  decide (w.Valid (graphOfCode c) k)

@[simp] theorem check_eq_true_iff {n : ℕ} (c : GraphCode n)
    (k : ℕ) (w : CloseWitness n) :
    w.check c k = true ↔ w.Valid (graphOfCode c) k := by
  simp [check]

/-- Semantic soundness of a checked side. -/
theorem Valid.closeToBipartite {n : ℕ} {G : SimpleGraph (Fin n)}
    [DecidableRel G.Adj] {k : ℕ} {w : CloseWitness n}
    (hw : w.Valid G k) : CloseToBipartite G k := by
  apply closeToBipartite_of_partitionClose
  refine ⟨w.sideSet, ?_⟩
  have heq : internalEdgeFinset G w.sideSet =
      G.edgeFinset.filter fun e ↦ w.sameSideBool e = true := by
    ext e
    simp [internalEdgeFinset, sameSideBool_eq_true_iff]
  rw [heq]
  exact hw

/-- Every semantic close-to-bipartite witness has a finite Boolean side
witness. -/
theorem exists_valid_iff {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (k : ℕ) :
    (∃ w : CloseWitness n, w.Valid G k) ↔ CloseToBipartite G k := by
  constructor
  · rintro ⟨w, hw⟩
    exact hw.closeToBipartite
  · intro h
    classical
    obtain ⟨s, hs⟩ := h.partition_witness
    let w : CloseWitness n :=
      ⟨fun v ↦ decide (v ∈ s)⟩
    refine ⟨w, ?_⟩
    have hside : w.sideSet = s := by
      ext v
      simp [w, sideSet]
    unfold Valid
    have heq : internalEdgeFinset G w.sideSet =
        G.edgeFinset.filter fun e ↦ w.sameSideBool e = true := by
      ext e
      simp [internalEdgeFinset, sameSideBool_eq_true_iff]
    rw [← heq, hside]
    exact hs

end CloseWitness

/-! ## Strict two-colour lower certificates -/

/-- Two sparse packing certificates, one in the graph and one in its
complement. -/
structure TwoColorLowerCert (n : ℕ) where
  red : PackingCert n
  blue : PackingCert n
  deriving DecidableEq

namespace TwoColorLowerCert

/-- Natural-number validity condition proving covered size strictly above the
sharp order-`n` threshold `n(n-1)/4`. -/
def Valid {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (c : TwoColorLowerCert n) : Prop :=
  c.red.Valid G ∧ c.blue.Valid Gᶜ ∧
    n * (n - 1) * c.red.denominator * c.blue.denominator <
      12 * (c.red.totalNumerator * c.blue.denominator +
        c.blue.totalNumerator * c.red.denominator)

/-- Executable strict lower-bound verifier. -/
def check {n : ℕ} (code : GraphCode n) (c : TwoColorLowerCert n) : Bool :=
  c.red.check (graphOfCode code) &&
    c.blue.check (graphOfCode code)ᶜ &&
      decide (n * (n - 1) * c.red.denominator * c.blue.denominator <
        12 * (c.red.totalNumerator * c.blue.denominator +
          c.blue.totalNumerator * c.red.denominator))

/-- Direct graph-input form of the executable checker. -/
def checkGraph {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (c : TwoColorLowerCert n) : Bool :=
  c.red.check G && c.blue.check Gᶜ &&
    decide (n * (n - 1) * c.red.denominator * c.blue.denominator <
      12 * (c.red.totalNumerator * c.blue.denominator +
        c.blue.totalNumerator * c.red.denominator))

@[simp] theorem check_eq_true_iff {n : ℕ} (code : GraphCode n)
    (c : TwoColorLowerCert n) :
    c.check code = true ↔ c.Valid (graphOfCode code) := by
  simp [check, Valid, and_assoc]

@[simp] theorem checkGraph_eq_true_iff {n : ℕ}
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (c : TwoColorLowerCert n) :
    c.checkGraph G = true ↔ c.Valid G := by
  simp [checkGraph, Valid, and_assoc]

/-- The real weights decoded from an accepted two-colour certificate are
feasible and strictly beat `stabilityThreshold n`. -/
theorem Valid.sound {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    (c : TwoColorLowerCert n) (hc : c.Valid G) (hn : 1 ≤ n) :
    IsFractionalPacking G c.red.weight ∧
      IsFractionalPacking Gᶜ c.blue.weight ∧
      stabilityThreshold n <
        twoColorCoveredSize G c.red.weight c.blue.weight := by
  have hred := hc.1.isFractionalPacking c.red
  have hblue := hc.2.1.isFractionalPacking c.blue
  refine ⟨hred, hblue, ?_⟩
  have hdr : (0 : ℝ) < c.red.denominator := by
    exact_mod_cast hc.1.1
  have hdb : (0 : ℝ) < c.blue.denominator := by
    exact_mod_cast hc.2.1.1
  have hnat :
      ((n * (n - 1) * c.red.denominator * c.blue.denominator : ℕ) : ℝ) <
        ((12 * (c.red.totalNumerator * c.blue.denominator +
          c.blue.totalNumerator * c.red.denominator) : ℕ) : ℝ) := by
    exact_mod_cast hc.2.2
  push_cast [Nat.cast_sub hn] at hnat
  rw [twoColorCoveredSize, fractionalCoveredSize,
    fractionalCoveredSize, fractionalSize_weight c.red hc.1.2.1,
    fractionalSize_weight c.blue hc.2.1.2.1]
  unfold stabilityThreshold
  field_simp
  nlinarith

/-- A strict accepted lower certificate contradicts the universal upper
bound used in the stability induction. -/
theorem Valid.not_fractionalCoveredSizeAtMost {n : ℕ}
    {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    (c : TwoColorLowerCert n) (hc : c.Valid G) (hn : 1 ≤ n) :
    ¬ FractionalCoveredSizeAtMost G (stabilityThreshold n) := by
  intro hupper
  obtain ⟨hr, hb, hgt⟩ := hc.sound c hn
  exact (not_lt_of_ge (hupper c.red.weight c.blue.weight hr hb)) hgt

end TwoColorLowerCert

/-! ## Relabelling lemmas used by canonical search output -/

/-- An isomorphism identifies its target with the map of its source. -/
lemma iso_map_eq {α β : Type*} {G : SimpleGraph α} {H : SimpleGraph β}
    (f : G ≃g H) : G.map f.toEquiv.toEmbedding = H := by
  ext x y
  rw [SimpleGraph.map_adj]
  constructor
  · rintro ⟨a, b, hab, rfl, rfl⟩
    exact f.map_rel_iff.mpr hab
  · intro hxy
    refine ⟨f.symm x, f.symm y, ?_, f.apply_symm_apply x,
      f.apply_symm_apply y⟩
    exact f.map_rel_iff.mp (by simpa using hxy)

/-- The fractional two-colour upper-bound predicate is invariant under a
change of vertex labels. -/
theorem fractionalCoveredSizeAtMost_relabel
    {α β : Type*} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β]
    {G : SimpleGraph α} {q : ℝ}
    (hG : FractionalCoveredSizeAtMost G q) (e : α ≃ β) :
    FractionalCoveredSizeAtMost (G.map e.toEmbedding) q := by
  classical
  intro wR wB hwR hwB
  let uR : Finset α → ℝ := relabelWeight e.symm wR
  let uB : Finset α → ℝ := relabelWeight e.symm wB
  have hmap : (G.map e.toEmbedding).map e.symm.toEmbedding = G := by
    rw [SimpleGraph.map_map]
    simpa using G.map_id
  have huR : IsFractionalPacking G uR := by
    simpa only [uR, hmap] using hwR.relabel e.symm
  have hc : (G.map e.toEmbedding)ᶜ.map e.symm.toEmbedding = Gᶜ := by
    rw [← compl_map_equiv (G.map e.toEmbedding) e.symm, hmap]
  have huB : IsFractionalPacking Gᶜ uB := by
    simpa only [uB, hc] using hwB.relabel e.symm
  have hupper := hG uR uB huR huB
  have hsR : fractionalCoveredSize G uR =
      fractionalCoveredSize (G.map e.toEmbedding) wR := by
    simpa only [uR, hmap] using
      fractionalCoveredSize_relabel (G.map e.toEmbedding) e.symm wR
  have hsB : fractionalCoveredSize Gᶜ uB =
      fractionalCoveredSize (G.map e.toEmbedding)ᶜ wB := by
    simpa only [uB, hc] using
      fractionalCoveredSize_relabel (G.map e.toEmbedding)ᶜ e.symm wB
  simpa [twoColorCoveredSize, hsR, hsB] using hupper

/-- Swapping the names of the two colours does not change an upper bound. -/
theorem fractionalCoveredSizeAtMost_compl
    {α : Type*} [Fintype α] [DecidableEq α]
    {G : SimpleGraph α} {q : ℝ}
    (hG : FractionalCoveredSizeAtMost G q) :
    FractionalCoveredSizeAtMost Gᶜ q := by
  classical
  intro wR wB hwR hwB
  have h := hG wB wR (by simpa using hwB) hwR
  simpa [twoColorCoveredSize, add_comm] using h

/-- Isomorphic graphs satisfy the same fractional upper bounds. -/
theorem fractionalCoveredSizeAtMost_iso
    {α β : Type*} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β]
    {G : SimpleGraph α} {H : SimpleGraph β} {q : ℝ}
    (hG : FractionalCoveredSizeAtMost G q) (f : G ≃g H) :
    FractionalCoveredSizeAtMost H q := by
  rw [← iso_map_eq f]
  exact fractionalCoveredSizeAtMost_relabel hG f.toEquiv

/-- Partition witnesses transport along a vertex equivalence. -/
theorem partitionCloseToBipartite_relabel
    {α β : Type*} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β]
    {G : SimpleGraph α} {k : ℕ}
    (hG : PartitionCloseToBipartite G k) (e : α ≃ β) :
    PartitionCloseToBipartite (G.map e.toEmbedding) k := by
  classical
  obtain ⟨s, hs⟩ := hG
  let t : Set β := e '' s
  refine ⟨t, ?_⟩
  have hfinset :
      internalEdgeFinset (G.map e.toEmbedding) t =
        (internalEdgeFinset G s).map e.toEmbedding.sym2Map := by
    ext p
    induction p using Sym2.inductionOn with
    | _ a b =>
        let x := e.symm a
        let y := e.symm b
        have hax : e x = a := e.apply_symm_apply a
        have hby : e y = b := e.apply_symm_apply b
        have hmapAdj :
            (G.map e.toEmbedding).Adj a b ↔ G.Adj x y := by
          rw [← hax, ← hby]
          exact SimpleGraph.map_adj_apply
        simp only [internalEdgeFinset, mem_filter, SimpleGraph.mem_edgeFinset,
          SimpleGraph.mem_edgeSet, sameSide_mk, mem_map]
        constructor
        · rintro ⟨hab, hside⟩
          refine ⟨s(x, y), ⟨hmapAdj.mp hab, ?_⟩, ?_⟩
          · simpa [x, y, hax, hby, t] using hside
          · simpa [x, y, hax, hby]
        · rintro ⟨q, hq, hqeq⟩
          have hq' : q = s(x, y) := by
            apply e.toEmbedding.sym2Map.injective
            simpa [x, y, hax, hby] using hqeq
          subst q
          exact ⟨hmapAdj.mpr hq.1,
            by simpa [x, y, hax, hby, t] using hq.2⟩
  rw [hfinset, card_map]
  exact hs

/-- Closeness to bipartiteness is invariant under relabelling. -/
theorem closeToBipartite_relabel
    {α β : Type*} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β]
    {G : SimpleGraph α} {k : ℕ}
    (hG : CloseToBipartite G k) (e : α ≃ β) :
    CloseToBipartite (G.map e.toEmbedding) k :=
  closeToBipartite_of_partitionClose
    (partitionCloseToBipartite_relabel hG.partition_witness e)

/-- Closeness to bipartiteness is invariant under graph isomorphism. -/
theorem closeToBipartite_iso
    {α β : Type*} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β]
    {G : SimpleGraph α} {H : SimpleGraph β} {k : ℕ}
    (hG : CloseToBipartite G k) (f : G ≃g H) :
    CloseToBipartite H k := by
  rw [← iso_map_eq f]
  exact closeToBipartite_relabel hG f.toEquiv

/-- Flip distance is unchanged by a bijective relabelling. -/
theorem edgeFlipDistance_relabel
    {α β : Type*} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β]
    (G H : SimpleGraph α) (e : α ≃ β) :
    edgeFlipDistance (G.map e.toEmbedding) (H.map e.toEmbedding) =
      edgeFlipDistance G H := by
  classical
  unfold edgeFlipDistance
  have edge_mem_map (A : SimpleGraph α) (p : Sym2 α) :
      p ∈ @SimpleGraph.edgeFinset α A
          (@SimpleGraph.fintypeEdgeSet α A inferInstance
            (Classical.decRel _)) ↔
        e.toEmbedding.sym2Map p ∈
          @SimpleGraph.edgeFinset β (A.map e.toEmbedding)
            (@SimpleGraph.fintypeEdgeSet β (A.map e.toEmbedding)
              inferInstance (Classical.decRel _)) := by
    induction p using Sym2.inductionOn with
    | _ u v =>
        simpa [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using
          (SimpleGraph.map_adj_apply (G := A) (f := e.toEmbedding)
            (a := u) (b := v)).symm
  apply congrArg₂ (fun a b : ℕ ↦ a + b)
  · symm
    apply Finset.card_bij
        (fun p _ ↦ e.toEmbedding.sym2Map p)
    · intro p hp
      rw [Finset.mem_sdiff] at hp ⊢
      exact ⟨(edge_mem_map G p).mp hp.1,
        fun hmem ↦ hp.2 ((edge_mem_map H p).mpr hmem)⟩
    · intro p _ q _ hpq
      exact e.toEmbedding.sym2Map.injective hpq
    · intro q hq
      let p := e.symm.toEmbedding.sym2Map q
      have hpq : e.toEmbedding.sym2Map p = q := by
        induction q using Sym2.inductionOn with
        | _ u v => simp [p]
      refine ⟨p, ?_, hpq⟩
      rw [Finset.mem_sdiff] at hq ⊢
      rw [← hpq] at hq
      exact ⟨(edge_mem_map G p).mpr hq.1,
        fun hmem ↦ hq.2 ((edge_mem_map H p).mp hmem)⟩
  · symm
    apply Finset.card_bij
        (fun p _ ↦ e.toEmbedding.sym2Map p)
    · intro p hp
      rw [Finset.mem_sdiff] at hp ⊢
      exact ⟨(edge_mem_map H p).mp hp.1,
        fun hmem ↦ hp.2 ((edge_mem_map G p).mpr hmem)⟩
    · intro p _ q _ hpq
      exact e.toEmbedding.sym2Map.injective hpq
    · intro q hq
      let p := e.symm.toEmbedding.sym2Map q
      have hpq : e.toEmbedding.sym2Map p = q := by
        induction q using Sym2.inductionOn with
        | _ u v => simp [p]
      refine ⟨p, ?_, hpq⟩
      rw [Finset.mem_sdiff] at hq ⊢
      rw [← hpq] at hq
      exact ⟨(edge_mem_map H p).mpr hq.1,
        fun hmem ↦ hq.2 ((edge_mem_map G p).mp hmem)⟩

/-- Pentagon blow-ups are invariant under relabelling. -/
theorem isPentagonBlowup_relabel
    {α β : Type*} {G : SimpleGraph α} {blob : α → Fin 5}
    (hG : IsPentagonBlowup G blob) (e : α ≃ β) :
    IsPentagonBlowup (G.map e.toEmbedding) (blob ∘ e.symm) := by
  constructor
  · intro a
    obtain ⟨x, hx⟩ := hG.1 a
    exact ⟨e x, by simpa using hx⟩
  · intro u v huv
    have hmap : (G.map e.toEmbedding).Adj u v ↔
        G.Adj (e.symm u) (e.symm v) := by
      simpa using (SimpleGraph.map_adj_apply (G := G) (f := e.toEmbedding)
        (a := e.symm u) (b := e.symm v))
    rw [hmap]
    exact hG.2 huv

/-- The finite pentagon-exception predicate is invariant under relabelling. -/
theorem isPentagonExceptional_relabel
    {α β : Type*} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β]
    {G : SimpleGraph α} (hG : IsPentagonExceptional G) (e : α ≃ β) :
    IsPentagonExceptional (G.map e.toEmbedding) := by
  refine ⟨?_, ?_⟩
  · rw [← Fintype.card_congr e]
    exact hG.1
  · rcases hG.2 with hblow | ⟨H, blob, hblob, hflip⟩
    · rcases hblow with ⟨blob, hblob⟩
      exact Or.inl ⟨blob ∘ e.symm, isPentagonBlowup_relabel hblob e⟩
    · exact Or.inr ⟨H.map e.toEmbedding, blob ∘ e.symm,
        isPentagonBlowup_relabel hblob e,
        by rw [edgeFlipDistance_relabel]; exact hflip⟩

/-- The finite pentagon-exception predicate is invariant under graph
isomorphism. -/
theorem isPentagonExceptional_iso
    {α β : Type*} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β]
    {G : SimpleGraph α} {H : SimpleGraph β}
    (hG : IsPentagonExceptional G) (f : G ≃g H) :
    IsPentagonExceptional H := by
  rw [← iso_map_eq f]
  exact isPentagonExceptional_relabel hG f.toEquiv

/-! ## Checked canonical routes -/

/-- A proof-free isomorphism route from a concrete source mask to a canonical
target mask.  When `swap` is true, the source is identified with the
complement of the target. -/
structure CanonicalRoute (n : ℕ) where
  source : BitVec (edgeCount n)
  target : BitVec (edgeCount n)
  perm : VertexPermutation n
  swap : Bool
  deriving DecidableEq

namespace CanonicalRoute

/-- The target graph after the optional colour swap. -/
def routedTarget {n : ℕ} (r : CanonicalRoute n) : SimpleGraph (Fin n) :=
  if r.swap then (graphOfBits r.target)ᶜ else graphOfBits r.target

instance {n : ℕ} (r : CanonicalRoute n) :
    DecidableRel r.routedTarget.Adj := by
  unfold routedTarget
  split <;> infer_instance

/-- Finite validity of a canonical route. -/
def Valid {n : ℕ} [NeZero n] (r : CanonicalRoute n) : Prop :=
  r.perm.Valid ∧ ∀ u v : Fin n,
    (graphOfBits r.source).Adj u v ↔
      r.routedTarget.Adj (r.perm.apply u) (r.perm.apply v)

instance {n : ℕ} [NeZero n] (r : CanonicalRoute n) : Decidable r.Valid := by
  cases hs : r.swap <;> simp [Valid, routedTarget, hs] <;> infer_instance

/-- Executable route checker. -/
def check {n : ℕ} [NeZero n] (r : CanonicalRoute n) : Bool :=
  decide r.Valid

@[simp] theorem check_eq_true_iff {n : ℕ} [NeZero n]
    (r : CanonicalRoute n) : r.check = true ↔ r.Valid := by
  simp [check]

/-- A checked route gives the promised graph isomorphism. -/
noncomputable def Valid.iso {n : ℕ} [NeZero n] {r : CanonicalRoute n}
    (hr : r.Valid) : graphOfBits r.source ≃g r.routedTarget where
  __ := r.perm.equiv hr.1
  map_rel_iff' := by
    intro u v
    simpa using (hr.2 u v).symm

end CanonicalRoute

/-! ## Routed certificate payloads -/

/-- A full-table code is the source graph of a route. -/
def SourceMatches {n : ℕ} (code : GraphCode n) (r : CanonicalRoute n) : Prop :=
  ∀ u v : Fin n,
    (graphOfCode code).Adj u v ↔ (graphOfBits r.source).Adj u v

instance {n : ℕ} (code : GraphCode n) (r : CanonicalRoute n) :
    Decidable (SourceMatches code r) := by
  unfold SourceMatches
  infer_instance

/-- A source match itself is an identity-on-vertices graph isomorphism. -/
def SourceMatches.iso {n : ℕ} {code : GraphCode n} {r : CanonicalRoute n}
    (h : SourceMatches code r) :
    graphOfCode code ≃g graphOfBits r.source where
  __ := Equiv.refl _
  map_rel_iff' := by
    intro u v
    exact (h u v).symm

/-- A strict lower certificate attached to a checked canonical route. -/
structure RoutedLowerCert (n : ℕ) where
  route : CanonicalRoute n
  payload : TwoColorLowerCert n
  deriving DecidableEq

namespace RoutedLowerCert

def Valid {n : ℕ} [NeZero n] (code : GraphCode n)
    (c : RoutedLowerCert n) : Prop :=
  SourceMatches code c.route ∧ c.route.Valid ∧
    c.payload.checkGraph (graphOfBits c.route.target) = true

instance {n : ℕ} [NeZero n] (code : GraphCode n)
    (c : RoutedLowerCert n) : Decidable (c.Valid code) := by
  unfold Valid
  infer_instance

def check {n : ℕ} [NeZero n] (code : GraphCode n)
    (c : RoutedLowerCert n) : Bool :=
  decide (c.Valid code)

@[simp] theorem check_eq_true_iff {n : ℕ} [NeZero n]
    (code : GraphCode n) (c : RoutedLowerCert n) :
    c.check code = true ↔ c.Valid code := by
  simp [check]

/-- Soundness of a routed strict lower certificate.  The optional route
colour swap is harmless because the two-colour upper predicate is symmetric. -/
theorem Valid.not_fractionalCoveredSizeAtMost {n : ℕ} [NeZero n]
    {code : GraphCode n} {c : RoutedLowerCert n} (hc : c.Valid code)
    (hn : 1 ≤ n) :
    ¬ FractionalCoveredSizeAtMost (graphOfCode code)
      (stabilityThreshold n) := by
  intro hupper
  let f : graphOfCode code ≃g c.route.routedTarget :=
    (hc.1.iso).trans hc.2.1.iso
  have hroute := fractionalCoveredSizeAtMost_iso hupper f
  have htarget : FractionalCoveredSizeAtMost (graphOfBits c.route.target)
      (stabilityThreshold n) := by
    cases hs : c.route.swap with
    | false => simpa [CanonicalRoute.routedTarget, hs] using hroute
    | true =>
        have := fractionalCoveredSizeAtMost_compl hroute
        simpa [CanonicalRoute.routedTarget, hs] using this
  exact TwoColorLowerCert.Valid.not_fractionalCoveredSizeAtMost
    c.payload
      ((TwoColorLowerCert.checkGraph_eq_true_iff
        (graphOfBits c.route.target) c.payload).mp hc.2.2) hn htarget

end RoutedLowerCert

/-- A finite list contains a valid strict-lower route for the graph code. -/
def LowerCovered {n : ℕ} [NeZero n]
    (entries : Array (RoutedLowerCert n)) (code : GraphCode n) : Prop :=
  ∃ i : Fin entries.size, entries[i].Valid code

instance {n : ℕ} [NeZero n] (entries : Array (RoutedLowerCert n))
    (code : GraphCode n) : Decidable (LowerCovered entries code) := by
  unfold LowerCovered
  infer_instance

def checkLowerCovered {n : ℕ} [NeZero n]
    (entries : Array (RoutedLowerCert n)) (code : GraphCode n) : Bool :=
  decide (LowerCovered entries code)

@[simp] theorem checkLowerCovered_eq_true_iff {n : ℕ} [NeZero n]
    (entries : Array (RoutedLowerCert n)) (code : GraphCode n) :
    checkLowerCovered entries code = true ↔ LowerCovered entries code := by
  simp [checkLowerCovered]

theorem LowerCovered.not_fractionalCoveredSizeAtMost
    {n : ℕ} [NeZero n] {entries : Array (RoutedLowerCert n)}
    {code : GraphCode n} (h : LowerCovered entries code) (hn : 1 ≤ n) :
    ¬ FractionalCoveredSizeAtMost (graphOfCode code)
      (stabilityThreshold n) := by
  obtain ⟨i, hi⟩ := h
  exact hi.not_fractionalCoveredSizeAtMost hn

/-- A pentagon witness attached to a canonical route.  Pentagon conclusions
are colour-sensitive, so this route is required not to swap colours. -/
structure RoutedPentagonCert (n : ℕ) where
  route : CanonicalRoute n
  payload : PentagonWitness n
  deriving DecidableEq

namespace RoutedPentagonCert

def Valid {n : ℕ} [NeZero n] (code : GraphCode n)
    (c : RoutedPentagonCert n) : Prop :=
  SourceMatches code c.route ∧ c.route.Valid ∧ c.route.swap = false ∧
    decide (c.payload.Valid (graphOfBits c.route.target)) = true

instance {n : ℕ} [NeZero n] (code : GraphCode n)
    (c : RoutedPentagonCert n) : Decidable (c.Valid code) := by
  unfold Valid
  infer_instance

def check {n : ℕ} [NeZero n] (code : GraphCode n)
    (c : RoutedPentagonCert n) : Bool :=
  decide (c.Valid code)

@[simp] theorem check_eq_true_iff {n : ℕ} [NeZero n]
    (code : GraphCode n) (c : RoutedPentagonCert n) :
    c.check code = true ↔ c.Valid code := by
  simp [check]

theorem Valid.isPentagonExceptional {n : ℕ} [NeZero n]
    {code : GraphCode n} {c : RoutedPentagonCert n}
    (hc : c.Valid code) (hn : n ≤ 25) :
    IsPentagonExceptional (graphOfCode code) := by
  have htarget := PentagonWitness.Valid.isPentagonExceptional
    (of_decide_eq_true hc.2.2.2) hn
  have f : graphOfCode code ≃g graphOfBits c.route.target := by
    have hr := hc.2.1.iso
    rw [show c.route.routedTarget = graphOfBits c.route.target by
      simp [CanonicalRoute.routedTarget, hc.2.2.1]] at hr
    exact hc.1.iso |>.trans hr
  exact isPentagonExceptional_iso htarget f.symm

end RoutedPentagonCert

def PentagonCovered {n : ℕ} [NeZero n]
    (entries : Array (RoutedPentagonCert n)) (code : GraphCode n) : Prop :=
  ∃ i : Fin entries.size, entries[i].Valid code

instance {n : ℕ} [NeZero n] (entries : Array (RoutedPentagonCert n))
    (code : GraphCode n) : Decidable (PentagonCovered entries code) := by
  unfold PentagonCovered
  infer_instance

def checkPentagonCovered {n : ℕ} [NeZero n]
    (entries : Array (RoutedPentagonCert n)) (code : GraphCode n) : Bool :=
  decide (PentagonCovered entries code)

@[simp] theorem checkPentagonCovered_eq_true_iff {n : ℕ} [NeZero n]
    (entries : Array (RoutedPentagonCert n)) (code : GraphCode n) :
    checkPentagonCovered entries code = true ↔ PentagonCovered entries code := by
  simp [checkPentagonCovered]

theorem PentagonCovered.isPentagonExceptional
    {n : ℕ} [NeZero n] {entries : Array (RoutedPentagonCert n)}
    {code : GraphCode n} (h : PentagonCovered entries code) (hn : n ≤ 25) :
    IsPentagonExceptional (graphOfCode code) := by
  obtain ⟨i, hi⟩ := h
  exact hi.isPentagonExceptional hn

/-- A close-to-bipartite witness attached to a canonical route.  A swapped
route certifies closeness of the source complement. -/
structure RoutedCloseCert (n : ℕ) where
  route : CanonicalRoute n
  payload : CloseWitness n
  deriving DecidableEq

namespace RoutedCloseCert

def Valid {n : ℕ} [NeZero n] (code : GraphCode n) (k : ℕ)
    (c : RoutedCloseCert n) : Prop :=
  SourceMatches code c.route ∧ c.route.Valid ∧
    decide (c.payload.Valid (graphOfBits c.route.target) k) = true

instance {n : ℕ} [NeZero n] (code : GraphCode n) (k : ℕ)
    (c : RoutedCloseCert n) : Decidable (c.Valid code k) := by
  unfold Valid
  infer_instance

def check {n : ℕ} [NeZero n] (code : GraphCode n) (k : ℕ)
    (c : RoutedCloseCert n) : Bool :=
  decide (c.Valid code k)

@[simp] theorem check_eq_true_iff {n : ℕ} [NeZero n]
    (code : GraphCode n) (k : ℕ) (c : RoutedCloseCert n) :
    c.check code k = true ↔ c.Valid code k := by
  simp [check]

theorem Valid.closeToBipartite {n : ℕ} [NeZero n]
    {code : GraphCode n} {k : ℕ} {c : RoutedCloseCert n}
    (hc : c.Valid code k) :
    CloseToBipartite (graphOfCode code) k ∨
      CloseToBipartite (graphOfCode code)ᶜ k := by
  have htarget := CloseWitness.Valid.closeToBipartite
    (of_decide_eq_true hc.2.2)
  let f : graphOfCode code ≃g c.route.routedTarget :=
    hc.1.iso |>.trans hc.2.1.iso
  cases hs : c.route.swap with
  | false =>
      left
      have f' : graphOfCode code ≃g graphOfBits c.route.target := by
        simpa [CanonicalRoute.routedTarget, hs] using f
      exact closeToBipartite_iso htarget f'.symm
  | true =>
      right
      have complementIso {G H : SimpleGraph (Fin n)}
          (g : G ≃g H) : Gᶜ ≃g Hᶜ :=
        { __ := g.toEquiv
          map_rel_iff' := by
            intro x y
            simp [SimpleGraph.compl_adj, g.map_rel_iff] }
      have f' : (graphOfCode code)ᶜ ≃g graphOfBits c.route.target := by
        have hfcompl := complementIso f
        simpa [CanonicalRoute.routedTarget, hs] using hfcompl
      exact closeToBipartite_iso htarget f'.symm

end RoutedCloseCert

def CloseCovered {n : ℕ} [NeZero n]
    (entries : Array (RoutedCloseCert n)) (code : GraphCode n) (k : ℕ) : Prop :=
  ∃ i : Fin entries.size, entries[i].Valid code k

instance {n : ℕ} [NeZero n] (entries : Array (RoutedCloseCert n))
    (code : GraphCode n) (k : ℕ) : Decidable (CloseCovered entries code k) := by
  unfold CloseCovered
  infer_instance

def checkCloseCovered {n : ℕ} [NeZero n]
    (entries : Array (RoutedCloseCert n)) (code : GraphCode n) (k : ℕ) : Bool :=
  decide (CloseCovered entries code k)

@[simp] theorem checkCloseCovered_eq_true_iff {n : ℕ} [NeZero n]
    (entries : Array (RoutedCloseCert n)) (code : GraphCode n) (k : ℕ) :
    checkCloseCovered entries code k = true ↔ CloseCovered entries code k := by
  simp [checkCloseCovered]

theorem CloseCovered.closeToBipartite
    {n : ℕ} [NeZero n] {entries : Array (RoutedCloseCert n)}
    {code : GraphCode n} {k : ℕ} (h : CloseCovered entries code k) :
    CloseToBipartite (graphOfCode code) k ∨
      CloseToBipartite (graphOfCode code)ᶜ k := by
  obtain ⟨i, hi⟩ := h
  exact hi.closeToBipartite

/-! ## Checker for `FiniteStabilityClassification` -/

/-- Executable old-vertex compatibility between consecutive full-table
codes. -/
def CodeInitialVertexExtension {n : ℕ}
    (H : GraphCode n) (G : GraphCode (n + 1)) : Prop :=
  ∀ u v : Fin n,
    (graphOfCode H).Adj u v ↔
      (graphOfCode G).Adj u.castSucc v.castSucc

instance {n : ℕ} (H : GraphCode n) (G : GraphCode (n + 1)) :
    Decidable (CodeInitialVertexExtension H G) := by
  unfold CodeInitialVertexExtension
  infer_instance

/-- The six concrete labelled colourings inspected by the finite
classification obligation. -/
structure ClassificationCodes where
  c17 : GraphCode 17
  c18 : GraphCode 18
  c19 : GraphCode 19
  c20 : GraphCode 20
  c21 : GraphCode 21
  c22 : GraphCode 22
  deriving DecidableEq

namespace ClassificationCodes

def IsChain (c : ClassificationCodes) : Prop :=
  CodeInitialVertexExtension c.c17 c.c18 ∧
  CodeInitialVertexExtension c.c18 c.c19 ∧
  CodeInitialVertexExtension c.c19 c.c20 ∧
  CodeInitialVertexExtension c.c20 c.c21 ∧
  CodeInitialVertexExtension c.c21 c.c22

instance (c : ClassificationCodes) : Decidable c.IsChain := by
  unfold IsChain
  infer_instance

end ClassificationCodes

/-- Data-independent certificate format for the order-17--22 finite
classification.  A bad branch at any order is closed by a strict lower
packing; surviving branches end in a pentagon or bipartite-close witness. -/
structure FiniteStabilityCertificate where
  lower17 : Array (RoutedLowerCert 17)
  lower18 : Array (RoutedLowerCert 18)
  lower19 : Array (RoutedLowerCert 19)
  lower20 : Array (RoutedLowerCert 20)
  lower21 : Array (RoutedLowerCert 21)
  lower22 : Array (RoutedLowerCert 22)
  pentagon17 : Array (RoutedPentagonCert 17)
  close22 : Array (RoutedCloseCert 22)

namespace FiniteStabilityCertificate

/-- Constructive six-fold finite universal quantification, with the pointwise
decision procedure supplied explicitly so instance search never has to infer
nested `DecidablePred`s. -/
def decidableForall₆
    {A B C D E F : Type*}
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    [Fintype C] [DecidableEq C] [Fintype D] [DecidableEq D]
    [Fintype E] [DecidableEq E] [Fintype F] [DecidableEq F]
    (p : A → B → C → D → E → F → Prop)
    (hp : ∀ a b c d e f, Decidable (p a b c d e f)) :
    Decidable (∀ a b c d e f, p a b c d e f) := by
  letI point (a : A) (b : B) (c : C) (d : D) (e : E) (f : F) :
      Decidable (p a b c d e f) := hp a b c d e f
  letI levelF (a : A) (b : B) (c : C) (d : D) (e : E) :
      Decidable (∀ f, p a b c d e f) :=
    Fintype.decidableForallFintype
  letI levelE (a : A) (b : B) (c : C) (d : D) :
      Decidable (∀ e f, p a b c d e f) :=
    Fintype.decidableForallFintype
  letI levelD (a : A) (b : B) (c : C) :
      Decidable (∀ d e f, p a b c d e f) :=
    Fintype.decidableForallFintype
  letI levelC (a : A) (b : B) :
      Decidable (∀ c d e f, p a b c d e f) :=
    Fintype.decidableForallFintype
  letI levelB (a : A) :
      Decidable (∀ b c d e f, p a b c d e f) :=
    Fintype.decidableForallFintype
  exact Fintype.decidableForallFintype

/-- Exhaustive finite validity predicate.  This deliberately says nothing
about how a generator traverses the search tree; sharded/direct-index tables
may be converted to these arrays after checking their own indexing. -/
def Valid (d : FiniteStabilityCertificate) : Prop :=
  ∀ c17 : GraphCode 17, ∀ c18 : GraphCode 18,
  ∀ c19 : GraphCode 19, ∀ c20 : GraphCode 20,
  ∀ c21 : GraphCode 21, ∀ c22 : GraphCode 22,
    let c : ClassificationCodes := ⟨c17, c18, c19, c20, c21, c22⟩
    c.IsChain →
      PentagonCovered d.pentagon17 c17 ∨
        CloseCovered d.close22 c22 2 ∨
        LowerCovered d.lower17 c17 ∨
        LowerCovered d.lower18 c18 ∨
        LowerCovered d.lower19 c19 ∨
        LowerCovered d.lower20 c20 ∨
        LowerCovered d.lower21 c21 ∨
        LowerCovered d.lower22 c22

instance (d : FiniteStabilityCertificate) : Decidable d.Valid := by
  unfold Valid
  apply decidableForall₆
  intro c17 c18 c19 c20 c21 c22
  infer_instance

/-- Executable top-level classification checker. -/
def check (d : FiniteStabilityCertificate) : Bool := decide d.Valid

@[simp] theorem check_eq_true_iff (d : FiniteStabilityCertificate) :
    d.check = true ↔ d.Valid := by
  change decide d.Valid = true ↔ d.Valid
  constructor
  · exact of_decide_eq_true (p := d.Valid)
  · exact decide_eq_true (p := d.Valid)

/-- Kernel soundness of an accepted finite classification certificate. -/
theorem Valid.finiteStabilityClassification
    (d : FiniteStabilityCertificate) (hd : d.Valid) :
    FiniteStabilityClassification := by
  intro C hchain
  let c : ClassificationCodes :=
    { c17 := codeOfGraph (C 17)
      c18 := codeOfGraph (C 18)
      c19 := codeOfGraph (C 19)
      c20 := codeOfGraph (C 20)
      c21 := codeOfGraph (C 21)
      c22 := codeOfGraph (C 22) }
  have hc : c.IsChain := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
      intro u v <;> simp only [c, graphOfCode_codeOfGraph]
    · exact hchain.2 17 (by omega) (by omega) u v
    · exact hchain.2 18 (by omega) (by omega) u v
    · exact hchain.2 19 (by omega) (by omega) u v
    · exact hchain.2 20 (by omega) (by omega) u v
    · exact hchain.2 21 (by omega) (by omega) u v
  rcases hd c.c17 c.c18 c.c19 c.c20 c.c21 c.c22 hc with
    hpent | hclose | h17 | h18 | h19 | h20 | h21 | h22
  · left
    simpa [c] using hpent.isPentagonExceptional (by omega)
  · right
    simpa [c] using hclose.closeToBipartite
  · exact (h17.not_fractionalCoveredSizeAtMost (by omega))
      (by simpa [c] using hchain.1 17 (by omega) (by omega)) |>.elim
  · exact (h18.not_fractionalCoveredSizeAtMost (by omega))
      (by simpa [c] using hchain.1 18 (by omega) (by omega)) |>.elim
  · exact (h19.not_fractionalCoveredSizeAtMost (by omega))
      (by simpa [c] using hchain.1 19 (by omega) (by omega)) |>.elim
  · exact (h20.not_fractionalCoveredSizeAtMost (by omega))
      (by simpa [c] using hchain.1 20 (by omega) (by omega)) |>.elim
  · exact (h21.not_fractionalCoveredSizeAtMost (by omega))
      (by simpa [c] using hchain.1 21 (by omega) (by omega)) |>.elim
  · exact (h22.not_fractionalCoveredSizeAtMost (by omega))
      (by simpa [c] using hchain.1 22 (by omega) (by omega)) |>.elim

theorem check_finiteStabilityClassification
    (d : FiniteStabilityCertificate) (hd : d.check = true) :
    FiniteStabilityClassification :=
  (d.check_eq_true_iff.mp hd).finiteStabilityClassification d

end FiniteStabilityCertificate

/-! ## Checker for `PentagonExtensionStep` -/

/-- Constructive three-fold finite universal quantification. -/
def decidableForall₃
    {A B C : Type*}
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    [Fintype C] [DecidableEq C]
    (p : A → B → C → Prop)
    (hp : ∀ a b c, Decidable (p a b c)) :
    Decidable (∀ a b c, p a b c) := by
  letI point (a : A) (b : B) (c : C) : Decidable (p a b c) := hp a b c
  letI levelC (a : A) (b : B) : Decidable (∀ c, p a b c) :=
    Fintype.decidableForallFintype
  letI levelB (a : A) : Decidable (∀ b c, p a b c) :=
    Fintype.decidableForallFintype
  exact Fintype.decidableForallFintype

/-- Certificate payload for one transition from order `n` to order `n+1`.
At order 26 the pentagon alternative is automatically disabled by the
explicit cardinal bound, so every branch must close by a strict packing. -/
structure PentagonStepCertificate (n : ℕ) where
  pentagonNext : Array (RoutedPentagonCert (n + 1))
  lowerNext : Array (RoutedLowerCert (n + 1))

namespace PentagonStepCertificate

def Valid {n : ℕ} [NeZero n] [NeZero (n + 1)]
    (d : PentagonStepCertificate n) : Prop :=
  ∀ hcode : GraphCode n, ∀ gcode : GraphCode (n + 1),
    ∀ hw : PentagonWitness n,
      hw.Valid (graphOfCode hcode) →
      CodeInitialVertexExtension hcode gcode →
      ((n + 1 ≤ 25 ∧ PentagonCovered d.pentagonNext gcode) ∨
        LowerCovered d.lowerNext gcode)

instance {n : ℕ} [NeZero n] [NeZero (n + 1)]
    (d : PentagonStepCertificate n) : Decidable d.Valid := by
  unfold Valid
  apply decidableForall₃
  intro hcode gcode hw
  infer_instance

def check {n : ℕ} [NeZero n] [NeZero (n + 1)]
    (d : PentagonStepCertificate n) : Bool := decide d.Valid

@[simp] theorem check_eq_true_iff {n : ℕ} [NeZero n] [NeZero (n + 1)]
    (d : PentagonStepCertificate n) : d.check = true ↔ d.Valid := by
  change decide d.Valid = true ↔ d.Valid
  constructor
  · exact of_decide_eq_true (p := d.Valid)
  · exact decide_eq_true (p := d.Valid)

/-- Semantic soundness of one accepted transition table. -/
theorem Valid.pentagonExtensionAt {n : ℕ} [NeZero n] [NeZero (n + 1)]
    (d : PentagonStepCertificate n) (hd : d.Valid)
    (hn : n ≤ 25) :
    ∀ (H : SimpleGraph (Fin n)) (G : SimpleGraph (Fin (n + 1))),
      IsInitialVertexExtension H G → IsPentagonExceptional H →
      FractionalCoveredSizeAtMost G (stabilityThreshold (n + 1)) →
      IsPentagonExceptional G := by
  intro H G hHG hH hupper
  classical
  letI : DecidableRel H.Adj := Classical.decRel _
  letI : DecidableRel G.Adj := Classical.decRel _
  obtain ⟨hw, hhw⟩ :=
    (PentagonWitness.exists_valid_iff H hn).mpr hH
  let hcode := codeOfGraph H
  let gcode := codeOfGraph G
  have hcodeExt : CodeInitialVertexExtension hcode gcode := by
    intro u v
    simpa [hcode, gcode] using hHG u v
  rcases hd hcode gcode hw (by simpa [hcode] using hhw) hcodeExt with
    ⟨hnext, hpent⟩ | hlower
  · simpa [gcode] using hpent.isPentagonExceptional hnext
  · exact (hlower.not_fractionalCoveredSizeAtMost (by omega))
      (by simpa [gcode] using hupper) |>.elim

end PentagonStepCertificate

/-- The nine finite transition tables needed for orders 17 through 25. -/
structure PentagonExtensionCertificate where
  step17 : PentagonStepCertificate 17
  step18 : PentagonStepCertificate 18
  step19 : PentagonStepCertificate 19
  step20 : PentagonStepCertificate 20
  step21 : PentagonStepCertificate 21
  step22 : PentagonStepCertificate 22
  step23 : PentagonStepCertificate 23
  step24 : PentagonStepCertificate 24
  step25 : PentagonStepCertificate 25

namespace PentagonExtensionCertificate

def Valid (d : PentagonExtensionCertificate) : Prop :=
  d.step17.Valid ∧ d.step18.Valid ∧ d.step19.Valid ∧
    d.step20.Valid ∧ d.step21.Valid ∧ d.step22.Valid ∧
    d.step23.Valid ∧ d.step24.Valid ∧ d.step25.Valid

instance (d : PentagonExtensionCertificate) : Decidable d.Valid := by
  unfold Valid
  infer_instance

def check (d : PentagonExtensionCertificate) : Bool := decide d.Valid

@[simp] theorem check_eq_true_iff (d : PentagonExtensionCertificate) :
    d.check = true ↔ d.Valid := by
  change decide d.Valid = true ↔ d.Valid
  constructor
  · exact of_decide_eq_true (p := d.Valid)
  · exact decide_eq_true (p := d.Valid)

/-- Kernel soundness of all nine accepted transition tables. -/
theorem Valid.pentagonExtensionStep
    (d : PentagonExtensionCertificate) (hd : d.Valid) :
    PentagonExtensionStep := by
  intro n hn17 hn26 H G hHG hH hupper
  have hthreshold :
      (((n + 1 : ℕ) : ℝ) * (n : ℝ) / 4) =
        stabilityThreshold (n + 1) := by
    unfold stabilityThreshold
    push_cast
    ring
  rw [hthreshold] at hupper
  rcases hd with ⟨h17, h18, h19, h20, h21, h22, h23, h24, h25⟩
  interval_cases n
  · exact h17.pentagonExtensionAt d.step17 (by omega) H G hHG hH hupper
  · exact h18.pentagonExtensionAt d.step18 (by omega) H G hHG hH hupper
  · exact h19.pentagonExtensionAt d.step19 (by omega) H G hHG hH hupper
  · exact h20.pentagonExtensionAt d.step20 (by omega) H G hHG hH hupper
  · exact h21.pentagonExtensionAt d.step21 (by omega) H G hHG hH hupper
  · exact h22.pentagonExtensionAt d.step22 (by omega) H G hHG hH hupper
  · exact h23.pentagonExtensionAt d.step23 (by omega) H G hHG hH hupper
  · exact h24.pentagonExtensionAt d.step24 (by omega) H G hHG hH hupper
  · exact h25.pentagonExtensionAt d.step25 (by omega) H G hHG hH hupper

theorem check_pentagonExtensionStep
    (d : PentagonExtensionCertificate) (hd : d.check = true) :
    PentagonExtensionStep :=
  (d.check_eq_true_iff.mp hd).pentagonExtensionStep d

end PentagonExtensionCertificate

end FiniteStabilityCertificateChecker
end Erdos76
