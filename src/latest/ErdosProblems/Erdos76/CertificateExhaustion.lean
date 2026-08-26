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
import ErdosProblems.Erdos76.CertificateChecker
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Tactic

/-!
# Verified exhaustion of finite graph representatives

This module checks canonicalization output without formalizing a graph
canonicalizer.  At each level the untrusted generator supplies graph-bit
representatives.  For every representative and every absent unordered vertex
pair it supplies the index of a representative at the next level and an
explicit vertex permutation witnessing the relabeling.

The data checker is fully executable.  The semantic theorem is independent of
packing certificates: every labeled graph with the target number of edges is
permutation-isomorphic to one of the final representatives.
-/

open Finset
open scoped BigOperators

namespace Erdos76
namespace CertificateExhaustion

open CertificateChecker

/-! ## Proof-free permutation data -/

/-- An explicit permutation candidate.  Its array entry at `i` is the image
of vertex `i`; bijectivity is checked rather than stored as proof data. -/
structure VertexPermutation (n : ℕ) where
  images : Array (Fin n)
  deriving DecidableEq

namespace VertexPermutation

variable {n : ℕ} [NeZero n]

/-- Total executable application, with an irrelevant fallback.  A valid
candidate has exactly `n` entries, so the fallback is never used. -/
def apply (p : VertexPermutation n) (i : Fin n) : Fin n :=
  p.images.getD i.1 0

/-- The natural finite condition saying that the array is a permutation. -/
def Valid (p : VertexPermutation n) : Prop :=
  p.images.size = n ∧ p.images.toList.Nodup

instance (p : VertexPermutation n) : Decidable p.Valid := by
  unfold Valid
  infer_instance

/-- Executable permutation checker. -/
def check (p : VertexPermutation n) : Bool := decide p.Valid

@[simp] theorem check_eq_true_iff (p : VertexPermutation n) :
    p.check = true ↔ p.Valid := by
  simp [check]

lemma apply_eq_getElem (p : VertexPermutation n) (hp : p.Valid) (i : Fin n) :
    p.apply i = p.images[i.1]'(by simpa [hp.1] using i.isLt) := by
  exact (Array.getElem_eq_getD 0).symm

/-- A checked array produces an actual permutation in the kernel. -/
noncomputable def equiv (p : VertexPermutation n) (hp : p.Valid) : Equiv.Perm (Fin n) := by
  apply Equiv.ofBijective p.apply
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨?_, rfl⟩
  intro i j hij
  have hlen : p.images.toList.length = n := by simpa using hp.1
  have hi : i.1 < p.images.toList.length := by simpa [hlen] using i.isLt
  have hj : j.1 < p.images.toList.length := by simpa [hlen] using j.isLt
  have hget : p.images.toList[i.1] = p.images.toList[j.1] := by
    rw [Array.getElem_toList hi, Array.getElem_toList hj]
    simpa [apply_eq_getElem p hp] using hij
  have hfin : (⟨i.1, hi⟩ : Fin p.images.toList.length) = ⟨j.1, hj⟩ :=
    (List.Nodup.get_inj_iff hp.2).mp (by simpa [List.get_eq_getElem] using hget)
  apply Fin.ext
  simpa using congrArg Fin.val hfin

@[simp] lemma equiv_apply (p : VertexPermutation n) (hp : p.Valid) (i : Fin n) :
    p.equiv hp i = p.apply i :=
  Equiv.ofBijective_apply _ _ _

end VertexPermutation

/-! ## One-level transition certificates -/

/-- Add one unordered vertex pair to a graph. -/
def addEdge {n : ℕ} (G : SimpleGraph (Fin n)) (i j : Fin n) :
    SimpleGraph (Fin n) :=
  G ⊔ SimpleGraph.fromEdgeSet {s(i, j)}

instance {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (i j : Fin n) :
    DecidableRel (addEdge G i j).Adj := by
  unfold addEdge
  infer_instance

@[simp] lemma addEdge_adj {n : ℕ} (G : SimpleGraph (Fin n)) (i j x y : Fin n) :
    (addEdge G i j).Adj x y ↔
      G.Adj x y ∨ (s(x, y) = s(i, j) ∧ x ≠ y) := by
  simp [addEdge, SimpleGraph.fromEdgeSet_adj]

lemma addEdge_comm {n : ℕ} (G : SimpleGraph (Fin n)) (i j : Fin n) :
    addEdge G i j = addEdge G j i := by
  unfold addEdge
  rw [Sym2.eq_swap]

/-- One direct-table entry emitted by the untrusted canonicalization program.
The table position supplies the parent and added pair; `perm` maps those old
labels to the labels of `child`. -/
structure Transition (n : ℕ) where
  child : ℕ
  perm : VertexPermutation n
  deriving DecidableEq

/-- Soundness of the witness stored at the direct table position `(p,i,j)`. -/
def Transition.Valid {n : ℕ} [NeZero n]
    (parents children : Array (BitVec (edgeCount n)))
    (p : Fin parents.size) (i j : Fin n) (r : Transition n) : Prop :=
  r.child < children.size ∧ r.perm.Valid ∧
    ∀ x y : Fin n,
      (addEdge (graphOfBits parents[p]) i j).Adj x y ↔
        (graphOfBits (children.getD r.child 0)).Adj
          (r.perm.apply x) (r.perm.apply y)

instance {n : ℕ} [NeZero n]
    (parents children : Array (BitVec (edgeCount n)))
    (p : Fin parents.size) (i j : Fin n) (r : Transition n) :
    Decidable (r.Valid parents children p i j) := by
  unfold Transition.Valid
  infer_instance

/-- The direct slot for an unordered pair.  Rows are indexed by parent and
columns by the same triangular `edgeIndex` used by graph bit-vectors. -/
def transitionAt {n : ℕ} (table : Array (Array (Option (Transition n))))
    (p : ℕ) (i j : Fin n) : Option (Transition n) :=
  (table.getD p #[]).getD (edgeIndex i j) none

/-- The local condition checked at one direct-table slot.  Naming this
condition separately gives Lean an explicit decidability split on the stored
`Option`, rather than asking instance synthesis to reduce a dependent match
inside the finite universal quantifiers of `StepValid`. -/
def SlotValid {n : ℕ} [NeZero n]
    (parents children : Array (BitVec (edgeCount n)))
    (p : Fin parents.size) (i j : Fin n)
    (slot : Option (Transition n)) : Prop :=
  match slot with
  | none => (graphOfBits parents[p]).Adj i j
  | some r => ¬ (graphOfBits parents[p]).Adj i j ∧
      r.Valid parents children p i j

instance {n : ℕ} [NeZero n]
    (parents children : Array (BitVec (edgeCount n)))
    (p : Fin parents.size) (i j : Fin n)
    (slot : Option (Transition n)) :
    Decidable (SlotValid parents children p i j slot) := by
  cases slot <;> unfold SlotValid <;> infer_instance

/-- Every row has the expected direct-indexed size.  A present parent edge has
no extension entry; every absent pair has one locally sound witness.  Thus the
checker performs one lookup per pair instead of scanning all transitions. -/
def StepValid {n : ℕ} [NeZero n]
    (parents children : Array (BitVec (edgeCount n)))
    (table : Array (Array (Option (Transition n)))) : Prop :=
  table.size = parents.size ∧
    ∀ p : Fin parents.size,
      (table.getD p #[]).size = edgeCount n ∧
        ∀ i j : Fin n, i < j →
          SlotValid parents children p i j (transitionAt table p i j)

instance {n : ℕ} [NeZero n]
    (parents children : Array (BitVec (edgeCount n)))
    (table : Array (Array (Option (Transition n)))) :
    Decidable (StepValid parents children table) := by
  unfold StepValid
  infer_instance

/-- Executable one-level exhaustion checker. -/
def checkStep {n : ℕ} [NeZero n]
    (parents children : Array (BitVec (edgeCount n)))
    (table : Array (Array (Option (Transition n)))) : Bool :=
  decide (StepValid parents children table)

@[simp] theorem checkStep_eq_true_iff {n : ℕ} [NeZero n]
    (parents children : Array (BitVec (edgeCount n)))
    (table : Array (Array (Option (Transition n)))) :
    checkStep parents children table = true ↔
      StepValid parents children table := by
  simp [checkStep]

/-! ## Sharded row checking

Large exhaustion levels are emitted and checked in small consecutive row
chunks.  The following predicates retain the direct-table representation but
allow the kernel to reduce each chunk independently. -/

/-- Validity of one already-indexed parent row. -/
def RowValid {n : ℕ} [NeZero n]
    (parents children : Array (BitVec (edgeCount n)))
    (p : Fin parents.size) (row : Array (Option (Transition n))) : Prop :=
  row.size = edgeCount n ∧
    ∀ i j : Fin n, i < j →
      SlotValid parents children p i j
        (row.getD (edgeIndex i j) none)

instance {n : ℕ} [NeZero n]
    (parents children : Array (BitVec (edgeCount n)))
    (p : Fin parents.size) (row : Array (Option (Transition n))) :
    Decidable (RowValid parents children p row) := by
  unfold RowValid
  infer_instance

/-- Recursive consecutive-row predicate on lists.  The recursion is useful
only for cheap proof composition; generated data remains in arrays. -/
def RowsValidListFrom {n : ℕ} [NeZero n]
    (parents children : Array (BitVec (edgeCount n))) :
    ℕ → List (Array (Option (Transition n))) → Prop
  | _, [] => True
  | start, row :: rows =>
      if h : start < parents.size then
        RowValid parents children ⟨start, h⟩ row ∧
          RowsValidListFrom parents children (start + 1) rows
      else False

instance {n : ℕ} [NeZero n]
    (parents children : Array (BitVec (edgeCount n)))
    (start : ℕ) (rows : List (Array (Option (Transition n)))) :
    Decidable (RowsValidListFrom parents children start rows) := by
  induction rows generalizing start with
  | nil => exact isTrue trivial
  | cons row rows ih =>
      simp only [RowsValidListFrom]
      split <;> infer_instance

/-- Check a consecutive array of rows beginning at the global parent index
`start`. -/
def RowsValidFrom {n : ℕ} [NeZero n]
    (parents children : Array (BitVec (edgeCount n))) (start : ℕ)
    (rows : Array (Array (Option (Transition n)))) : Prop :=
  RowsValidListFrom parents children start rows.toList

instance {n : ℕ} [NeZero n]
    (parents children : Array (BitVec (edgeCount n))) (start : ℕ)
    (rows : Array (Array (Option (Transition n)))) :
    Decidable (RowsValidFrom parents children start rows) := by
  unfold RowsValidFrom
  infer_instance

/-- Executable row-range checker. -/
def checkRows {n : ℕ} [NeZero n]
    (parents children : Array (BitVec (edgeCount n))) (start : ℕ)
    (rows : Array (Array (Option (Transition n)))) : Bool :=
  decide (RowsValidFrom parents children start rows)

@[simp] theorem checkRows_eq_true_iff {n : ℕ} [NeZero n]
    (parents children : Array (BitVec (edgeCount n))) (start : ℕ)
    (rows : Array (Array (Option (Transition n)))) :
    checkRows parents children start rows = true ↔
      RowsValidFrom parents children start rows := by
  simp [checkRows]

/-- Consecutive list certificates compose without rechecking their rows. -/
theorem RowsValidListFrom.append {n : ℕ} [NeZero n]
    {parents children : Array (BitVec (edgeCount n))}
    {start : ℕ} {a b : List (Array (Option (Transition n)))}
    (ha : RowsValidListFrom parents children start a)
    (hb : RowsValidListFrom parents children (start + a.length) b) :
    RowsValidListFrom parents children start (a ++ b) := by
  induction a generalizing start with
  | nil => simpa [RowsValidListFrom] using hb
  | cons row rows ih =>
      simp only [List.cons_append, RowsValidListFrom] at ha ⊢
      by_cases hstart : start < parents.size
      · rw [dif_pos hstart] at ha ⊢
        obtain ⟨hrow, hrows⟩ := ha
        refine ⟨hrow, ih hrows ?_⟩
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hb
      · rw [dif_neg hstart] at ha
        exact False.elim ha

/-- Array form of row-range composition, used by generated shard modules. -/
theorem RowsValidFrom.append {n : ℕ} [NeZero n]
    {parents children : Array (BitVec (edgeCount n))}
    {start : ℕ} {a b : Array (Array (Option (Transition n)))}
    (ha : RowsValidFrom parents children start a)
    (hb : RowsValidFrom parents children (start + a.size) b) :
    RowsValidFrom parents children start (a ++ b) := by
  unfold RowsValidFrom at ha hb ⊢
  simpa using RowsValidListFrom.append ha hb

/-- Lookup a checked local list row together with its global parent index. -/
theorem RowsValidListFrom.get {n : ℕ} [NeZero n]
    {parents children : Array (BitVec (edgeCount n))}
    {start : ℕ} {rows : List (Array (Option (Transition n)))}
    (hrows : RowsValidListFrom parents children start rows)
    (q : ℕ) (hq : q < rows.length) :
    ∃ p : Fin parents.size, p.1 = start + q ∧
      RowValid parents children p rows[q] := by
  induction rows generalizing start q with
  | nil => simp at hq
  | cons row rows ih =>
      simp only [RowsValidListFrom] at hrows
      by_cases hstart : start < parents.size
      · rw [dif_pos hstart] at hrows
        obtain ⟨hrow, htail⟩ := hrows
        cases q with
        | zero => exact ⟨⟨start, hstart⟩, rfl, hrow⟩
        | succ q =>
            have hq' : q < rows.length := by simpa using hq
            obtain ⟨p, hp, hrowp⟩ := ih htail q hq'
            refine ⟨p, ?_, hrowp⟩
            omega
      · rw [dif_neg hstart] at hrows
        exact False.elim hrows

/-- A proof for all rows, together with the outer table-size equality,
reconstructs the original `StepValid` predicate. -/
theorem StepValid.of_rowsValidFrom {n : ℕ} [NeZero n]
    {parents children : Array (BitVec (edgeCount n))}
    {table : Array (Array (Option (Transition n)))}
    (hsize : table.size = parents.size)
    (hrows : RowsValidFrom parents children 0 table) :
    StepValid parents children table := by
  refine ⟨hsize, ?_⟩
  intro p
  have hpList : p.1 < table.toList.length := by simpa [hsize] using p.isLt
  obtain ⟨p', hp', hrow⟩ :=
    RowsValidListFrom.get hrows p.1 hpList
  have hpp : p' = p := by
    apply Fin.ext
    simpa using hp'
  subst p'
  have hlist : table.toList[p.1] = table[p.1]'(by simpa [hsize] using p.isLt) := by
    exact Array.getElem_toList _
  rw [hlist] at hrow
  have hgetD : table.getD p.1 #[] = table[p.1]'(by simpa [hsize] using p.isLt) :=
    (Array.getElem_eq_getD #[]).symm
  simpa only [RowValid, transitionAt, hgetD] using hrow

/-! ## Semantic soundness of one transition level -/

/-- A graph is represented when relabeling its vertices by a permutation gives
one of the bit graphs in `reps`. -/
def IsRepresented {n : ℕ} (reps : Array (BitVec (edgeCount n)))
    (G : SimpleGraph (Fin n)) : Prop :=
  ∃ k : Fin reps.size, Nonempty (G ≃g graphOfBits reps[k])

/-- An isomorphism extends across adding the corresponding edge. -/
noncomputable def SimpleGraph.Iso.addEdge {n : ℕ}
    {G H : SimpleGraph (Fin n)} (f : G ≃g H) (i j : Fin n) :
    addEdge G i j ≃g addEdge H (f i) (f j) where
  __ := f.toEquiv
  map_rel_iff' := by
    intro x y
    simp only [addEdge_adj]
    change (H.Adj (f x) (f y) ∨
      (s(f x, f y) = s(f i, f j) ∧ f x ≠ f y)) ↔
        G.Adj x y ∨ (s(x, y) = s(i, j) ∧ x ≠ y)
    rw [f.map_rel_iff]
    simp [Sym2.eq_iff, f.toEquiv.injective.eq_iff]

/-- Semantic isomorphism certified by one accepted transition record. -/
noncomputable def Transition.Valid.iso {n : ℕ} [NeZero n]
    {parents children : Array (BitVec (edgeCount n))}
    {p : Fin parents.size} {i j : Fin n} {r : Transition n}
    (hr : r.Valid parents children p i j) :
    addEdge (graphOfBits parents[p]) i j ≃g
      graphOfBits (children.getD r.child 0) where
  __ := r.perm.equiv hr.2.1
  map_rel_iff' := by
    intro x y
    simpa using (hr.2.2 x y).symm

/-- Constant-time semantic lookup of the witness for an absent parent edge. -/
theorem StepValid.lookup_missing {n : ℕ} [NeZero n]
    {parents children : Array (BitVec (edgeCount n))}
    {table : Array (Array (Option (Transition n)))}
    (hs : StepValid parents children table)
    (p : Fin parents.size) (i j : Fin n) (hij : i < j)
    (hmissing : ¬ (graphOfBits parents[p]).Adj i j) :
    ∃ r : Transition n, r.Valid parents children p i j := by
  have hslot := hs.2 p |>.2 i j hij
  generalize hget : transitionAt table p i j = slot at hslot
  cases slot with
  | none => exact (hmissing hslot).elim
  | some r => exact ⟨r, hslot.2⟩

/-- One valid table represents every one-edge extension of one of its parent
representatives. -/
theorem StepValid.addEdge_representative {n : ℕ} [NeZero n]
    {parents children : Array (BitVec (edgeCount n))}
    {table : Array (Array (Option (Transition n)))}
    (hs : StepValid parents children table)
    (p : Fin parents.size) (i j : Fin n) (hij : i < j)
    (hmissing : ¬ (graphOfBits parents[p]).Adj i j) :
    IsRepresented children (addEdge (graphOfBits parents[p]) i j) := by
  obtain ⟨r, hr⟩ := hs.lookup_missing p i j hij hmissing
  have hchild : r.child < children.size := hr.1
  let cidx : Fin children.size := ⟨r.child, hchild⟩
  refine ⟨cidx, ⟨?_⟩⟩
  have hiso := hr.iso
  have hcget : children.getD r.child 0 = children[cidx] := by
    exact (Array.getElem_eq_getD 0).symm
  rw [hcget] at hiso
  exact hiso

/-- Boolean form of `StepValid.addEdge_representative`. -/
theorem checkStep_addEdge_representative {n : ℕ} [NeZero n]
    {parents children : Array (BitVec (edgeCount n))}
    {table : Array (Array (Option (Transition n)))}
    (hs : checkStep parents children table = true)
    (p : Fin parents.size) (i j : Fin n) (hij : i < j)
    (hmissing : ¬ (graphOfBits parents[p]).Adj i j) :
    IsRepresented children (addEdge (graphOfBits parents[p]) i j) :=
  ((checkStep_eq_true_iff parents children table).mp hs).addEdge_representative
    p i j hij hmissing

/-- The semantic induction hook: a valid level represents every genuine
one-edge extension of every graph represented at the preceding level. -/
theorem StepValid.addEdge_represented {n : ℕ} [NeZero n]
    {parents children : Array (BitVec (edgeCount n))}
    {table : Array (Array (Option (Transition n)))}
    (hs : StepValid parents children table)
    {G : SimpleGraph (Fin n)} (hG : IsRepresented parents G)
    (i j : Fin n) (hij : i ≠ j) (hmissing : ¬ G.Adj i j) :
    IsRepresented children (addEdge G i j) := by
  obtain ⟨p, ⟨f⟩⟩ := hG
  have hmissing' : ¬ (graphOfBits parents[p]).Adj (f i) (f j) := by
    intro h
    exact hmissing (f.map_rel_iff.mp h)
  rcases lt_trichotomy (f i) (f j) with hlt | heq | hgt
  · obtain ⟨c, ⟨g⟩⟩ := hs.addEdge_representative p (f i) (f j) hlt hmissing'
    exact ⟨c, ⟨(SimpleGraph.Iso.addEdge f i j).trans g⟩⟩
  · exact (hij (f.injective heq)).elim
  · have hmissing'' : ¬ (graphOfBits parents[p]).Adj (f j) (f i) := by
      simpa [SimpleGraph.adj_comm] using hmissing'
    obtain ⟨c, ⟨g⟩⟩ :=
      hs.addEdge_representative p (f j) (f i) hgt hmissing''
    have g' : addEdge (graphOfBits parents[p]) (f i) (f j) ≃g
        graphOfBits children[c] := by
      rw [addEdge_comm]
      exact g
    exact ⟨c, ⟨(SimpleGraph.Iso.addEdge f i j).trans g'⟩⟩

/-! ## Complete level chains -/

/-- A proof-free exhaustion certificate.  `levels[k]` contains graph-bit
representatives with `k` edges and `steps[k]` certifies all one-edge
extensions from level `k` into level `k+1`. -/
structure ExhaustionData (n : ℕ) where
  levels : Array (Array (BitVec (edgeCount n)))
  steps : Array (Array (Array (Option (Transition n))))

namespace ExhaustionData

variable {n : ℕ} [NeZero n]

/-- Representatives at level `k`; out-of-range access is empty and is ruled
out by `Valid` in every semantic use. -/
def level (d : ExhaustionData n) (k : ℕ) : Array (BitVec (edgeCount n)) :=
  d.levels.getD k #[]

/-- Direct transition table following level `k`. -/
def step (d : ExhaustionData n) (k : ℕ) :
    Array (Array (Option (Transition n))) :=
  d.steps.getD k #[]

/-- Complete finite condition checked for an exhaustion certificate. -/
def Valid (d : ExhaustionData n) : Prop :=
  d.levels.size = d.steps.size + 1 ∧
    (d.level 0).size = 1 ∧ (d.level 0).getD 0 0 = 0 ∧
      ∀ k : Fin d.steps.size,
        StepValid (d.level k) (d.level (k + 1)) (d.step k)

instance (d : ExhaustionData n) : Decidable d.Valid := by
  unfold Valid
  infer_instance

/-- Executable full-chain checker. -/
def check (d : ExhaustionData n) : Bool := decide d.Valid

@[simp] theorem check_eq_true_iff (d : ExhaustionData n) :
    d.check = true ↔ d.Valid := by
  simp [check]

lemma Valid.stepValid {d : ExhaustionData n} (hd : d.Valid)
    (k : ℕ) (hk : k < d.steps.size) :
    StepValid (d.level k) (d.level (k + 1)) (d.step k) :=
  hd.2.2.2 ⟨k, hk⟩

@[simp] lemma graphOfBits_zero :
    graphOfBits (0 : BitVec (edgeCount n)) = (⊥ : SimpleGraph (Fin n)) := by
  ext i j
  simp [graphOfBits]

/-- The checked initial singleton level represents the empty graph. -/
theorem Valid.baseRepresented {d : ExhaustionData n} (hd : d.Valid) :
    IsRepresented (d.level 0) (⊥ : SimpleGraph (Fin n)) := by
  let k : Fin (d.level 0).size := ⟨0, by rw [hd.2.1]; omega⟩
  refine ⟨k, ⟨?_⟩⟩
  have hk : (d.level 0)[k] = (d.level 0).getD 0 0 :=
    Array.getElem_eq_getD 0
  rw [hk, hd.2.2.1, graphOfBits_zero]

/-- Finset induction underlying exhaustive generation: every loopless finite
edge set of a checked size is represented at the correspondingly numbered
level. -/
theorem Valid.represents_fromEdgeFinset {d : ExhaustionData n} (hd : d.Valid)
    (S : Finset (Sym2 (Fin n)))
    (hloopless : ∀ e ∈ S, ¬ e.IsDiag) (hcard : S.card ≤ d.steps.size) :
    IsRepresented (d.level S.card)
      (SimpleGraph.fromEdgeSet (↑S : Set (Sym2 (Fin n)))) := by
  induction S using Finset.induction with
  | empty =>
      simpa using hd.baseRepresented
  | @insert e S he ih =>
      have hcardS : S.card < d.steps.size := by
        simp [he] at hcard
        omega
      have ihrep : IsRepresented (d.level S.card)
          (SimpleGraph.fromEdgeSet (↑S : Set (Sym2 (Fin n)))) :=
        ih (fun e heS ↦ hloopless e (Finset.mem_insert_of_mem heS)) hcardS.le
      induction e using Sym2.inductionOn with
      | _ x y =>
          have hxy : x ≠ y := by
            simpa using hloopless s(x, y) (Finset.mem_insert_self _ _)
          have hmissing :
              ¬ (SimpleGraph.fromEdgeSet (↑S : Set (Sym2 (Fin n)))).Adj x y := by
            simp [SimpleGraph.fromEdgeSet_adj, he, hxy]
          have hstep := (hd.stepValid S.card hcardS).addEdge_represented
            ihrep x y hxy hmissing
          have hg :
              SimpleGraph.fromEdgeSet (↑(insert s(x, y) S) : Set (Sym2 (Fin n))) =
                addEdge (SimpleGraph.fromEdgeSet (↑S : Set (Sym2 (Fin n)))) x y := by
            ext a b
            simp [addEdge, SimpleGraph.fromEdgeSet_adj, and_or_left, and_comm,
              and_left_comm, and_assoc, or_comm]
          have hcardInsert : (insert s(x, y) S).card = S.card + 1 := by simp [he]
          rw [hcardInsert, hg]
          exact hstep

/-- Instance-free semantic exhaustion theorem.  `G.edgeSet.ncard` counts
edges without placing a decidable-adjacency instance in the theorem type. -/
theorem Valid.representsGraph {d : ExhaustionData n} (hd : d.Valid)
    (G : SimpleGraph (Fin n)) (hcard : G.edgeSet.ncard ≤ d.steps.size) :
    IsRepresented (d.level G.edgeSet.ncard) G := by
  classical
  let S : Finset (Sym2 (Fin n)) := G.edgeSet.toFinset
  have hScard : S.card = G.edgeSet.ncard := by
    exact (Set.ncard_eq_toFinset_card' G.edgeSet).symm
  have hloopless : ∀ e ∈ S, ¬ e.IsDiag := by
    intro e he
    apply G.not_isDiag_of_mem_edgeSet
    simpa [S] using he
  have hrep := hd.represents_fromEdgeFinset S hloopless (by simpa [hScard] using hcard)
  have hgraph : SimpleGraph.fromEdgeSet (↑S : Set (Sym2 (Fin n))) = G := by
    simp [S, Set.coe_toFinset, SimpleGraph.fromEdgeSet_edgeSet]
  simpa [hScard, hgraph] using hrep

/-- An accepted full exhaustion certificate classifies every graph with the
target number of edges by a representative in its last level. -/
theorem check_representsGraph_atTarget {d : ExhaustionData n}
    (hd : d.check = true) (G : SimpleGraph (Fin n))
    (hcard : G.edgeSet.ncard = d.steps.size) :
    IsRepresented (d.level d.steps.size) G := by
  have hv := (check_eq_true_iff d).mp hd
  simpa [hcard] using hv.representsGraph G hcard.le

/-- Generic semantic transport hook.  Any permutation-isomorphism-invariant
property proved for all final representatives therefore holds for every graph
with the target edge count. -/
theorem check_transport_atTarget {d : ExhaustionData n}
    (hd : d.check = true) (P : SimpleGraph (Fin n) → Prop)
    (hP : ∀ k : Fin (d.level d.steps.size).size,
      P (graphOfBits (d.level d.steps.size)[k]))
    (htransport : ∀ G H : SimpleGraph (Fin n), Nonempty (G ≃g H) → P H → P G)
    (G : SimpleGraph (Fin n)) (hcard : G.edgeSet.ncard = d.steps.size) :
    P G := by
  obtain ⟨k, hiso⟩ := check_representsGraph_atTarget hd G hcard
  exact htransport G (graphOfBits (d.level d.steps.size)[k]) hiso (hP k)

end ExhaustionData

end CertificateExhaustion
end Erdos76
