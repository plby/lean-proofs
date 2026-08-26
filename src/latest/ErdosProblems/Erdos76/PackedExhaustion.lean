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
import ErdosProblems.Erdos76.PackedBucketCertificate

/-!
# Packed transition rows for graph exhaustion

For a fixed parent graph the row position determines which edge slot is being
extended.  A present parent edge consumes no wire data.  Every absent slot
stores a child index followed by the `n` images of an explicit vertex
permutation.  Rows are checked independently and assembled proof-theoretically
into the existing direct-table `StepValid` predicate.
-/

namespace Erdos76
namespace CertificateExhaustion
namespace Packed

open CertificateChecker
open CertificateChecker.PackedBucketCertificate

def readImages (n : ℕ) :
    ℕ → Cursor → Option (List (Fin n) × Cursor)
  | 0, input => some ([], input)
  | count + 1, input => do
      let (image, afterImage) ← readNat input
      if h : image < n then
        let (images, rest) ← readImages n count afterImage
        some (⟨image, h⟩ :: images, rest)
      else none

def readTransition (n : ℕ) (input : Cursor) :
    Option (Transition n × Cursor) := do
  let (child, afterChild) ← readNat input
  let (images, rest) ← readImages n n afterChild
  some (⟨child, ⟨images.toArray⟩⟩, rest)

def readSlot (n : ℕ) (parent : BitVec (edgeCount n))
    (index : ℕ) (input : Cursor) :
    Option (Option (Transition n) × Cursor) :=
  if parent.getLsbD index then some (none, input)
  else do
    let (transition, rest) ← readTransition n input
    some (some transition, rest)

/-- Four edge slots per recursive frame keep the parser below the stock
kernel recursion-depth limit at `n = 13`. -/
def readSlots (n : ℕ) (parent : BitVec (edgeCount n)) :
    ℕ → ℕ → Cursor →
      Option (List (Option (Transition n)) × Cursor)
  | 0, _, input => some ([], input)
  | 1, index, input => do
      let (r₁, rest) ← readSlot n parent index input
      some ([r₁], rest)
  | 2, index, input => do
      let (r₁, after₁) ← readSlot n parent index input
      let (r₂, rest) ← readSlot n parent (index + 1) after₁
      some ([r₁, r₂], rest)
  | 3, index, input => do
      let (r₁, after₁) ← readSlot n parent index input
      let (r₂, after₂) ← readSlot n parent (index + 1) after₁
      let (r₃, rest) ← readSlot n parent (index + 2) after₂
      some ([r₁, r₂, r₃], rest)
  | count + 4, index, input => do
      let (r₁, after₁) ← readSlot n parent index input
      let (r₂, after₂) ← readSlot n parent (index + 1) after₁
      let (r₃, after₃) ← readSlot n parent (index + 2) after₂
      let (r₄, after₄) ← readSlot n parent (index + 3) after₃
      let (rows, rest) ← readSlots n parent count (index + 4) after₄
      some (r₁ :: r₂ :: r₃ :: r₄ :: rows, rest)

def decodeRow (n : ℕ) (parent : BitVec (edgeCount n)) (blob : Blob) :
    Option (Array (Option (Transition n))) := do
  let (slots, rest) ← readSlots n parent (edgeCount n) 0 blob.cursor
  if rest.remaining = 0 ∧ rest.inChunk = 0 ∧ rest.data = 0 ∧
      rest.rest = [] then
    some slots.toArray
  else none

def rowOf (n : ℕ) (parent : BitVec (edgeCount n)) (blob : Blob) :
    Array (Option (Transition n)) :=
  (decodeRow n parent blob).getD #[]

/-! ## Sparse transition validation

The exhaustion graphs have at most thirteen edges.  Checking adjacency on all
ordered vertex pairs for every transition wastes most of the kernel work.
The sparse predicate checks only mapped source edges and equality of edge
counts.  Injectivity of the checked permutation then upgrades inclusion to
graph equality. -/

def Transition.SparseValid {n : ℕ} [NeZero n]
    (parents children : Array (BitVec (edgeCount n)))
    (p : Fin parents.size) (i j : Fin n) (r : Transition n) : Prop :=
  r.child < children.size ∧ r.perm.Valid ∧
    (addEdge (graphOfBits parents[p]) i j).edgeFinset.card =
      (graphOfBits (children.getD r.child 0)).edgeFinset.card ∧
    ∀ x y : Fin n, (addEdge (graphOfBits parents[p]) i j).Adj x y →
      (graphOfBits (children.getD r.child 0)).Adj
        (r.perm.apply x) (r.perm.apply y)

def Transition.checkSparse {n : ℕ} [NeZero n]
    (parents children : Array (BitVec (edgeCount n)))
    (p : Fin parents.size) (i j : Fin n) (r : Transition n) : Bool :=
  decide (r.child < children.size) && r.perm.check &&
    decide ((addEdge (graphOfBits parents[p]) i j).edgeFinset.card =
      (graphOfBits (children.getD r.child 0)).edgeFinset.card) &&
    (List.finRange n).all (fun x ↦
      (List.finRange n).all (fun y ↦
        if (addEdge (graphOfBits parents[p]) i j).Adj x y then
          decide ((graphOfBits (children.getD r.child 0)).Adj
            (r.perm.apply x) (r.perm.apply y))
        else true))

@[simp] theorem Transition.checkSparse_eq_true_iff {n : ℕ} [NeZero n]
    (parents children : Array (BitVec (edgeCount n)))
    (p : Fin parents.size) (i j : Fin n) (r : Transition n) :
    Transition.checkSparse parents children p i j r = true ↔
      Transition.SparseValid parents children p i j r := by
  constructor
  · intro h
    simp only [Transition.checkSparse, Bool.and_eq_true] at h
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa using h.1.1.1
    · simpa using h.1.1.2
    · simpa using h.1.2
    · intro x y hadj
      have hx : x ∈ List.finRange n := List.mem_finRange x
      have hy : y ∈ List.finRange n := List.mem_finRange y
      have houter := List.all_eq_true.mp h.2 x hx
      have hinner := List.all_eq_true.mp houter y hy
      simp only [if_pos hadj] at hinner
      simpa using hinner
  · rintro ⟨hchild, hperm, hcard, hforward⟩
    simp only [Transition.checkSparse, Bool.and_eq_true]
    refine ⟨⟨⟨by simpa using hchild, by simpa using hperm⟩,
      by simpa using hcard⟩, ?_⟩
    apply List.all_eq_true.mpr
    intro x hx
    apply List.all_eq_true.mpr
    intro y hy
    by_cases hadj : (addEdge (graphOfBits parents[p]) i j).Adj x y
    · simp only [if_pos hadj]
      simpa using hforward x y hadj
    · simp only [if_neg hadj]

instance {n : ℕ} [NeZero n]
    (parents children : Array (BitVec (edgeCount n)))
    (p : Fin parents.size) (i j : Fin n) (r : Transition n) :
    Decidable (Transition.SparseValid parents children p i j r) :=
  decidable_of_iff (Transition.checkSparse parents children p i j r = true)
    (Transition.checkSparse_eq_true_iff parents children p i j r)

theorem Transition.SparseValid.valid {n : ℕ} [NeZero n]
    {parents children : Array (BitVec (edgeCount n))}
    {p : Fin parents.size} {i j : Fin n} {r : Transition n}
    (h : Transition.SparseValid parents children p i j r) :
    r.Valid parents children p i j := by
  rcases h with ⟨hchild, hperm, hcard, hforward⟩
  refine ⟨hchild, hperm, ?_⟩
  let source := addEdge (graphOfBits parents[p]) i j
  let target := graphOfBits (children.getD r.child 0)
  let e : Equiv.Perm (Fin n) := r.perm.equiv hperm
  have hsubset : source.edgeFinset.map e.toEmbedding.sym2Map ⊆
      target.edgeFinset := by
    intro mapped hmapped
    rw [Finset.mem_map] at hmapped
    obtain ⟨edge, hedge, rfl⟩ := hmapped
    induction edge using Sym2.inductionOn with
    | _ x y =>
        have hadj : source.Adj x y := by
          simpa [SimpleGraph.mem_edgeFinset] using hedge
        have hmapped := hforward x y (by simpa [source] using hadj)
        simpa [target, e, VertexPermutation.equiv_apply,
          Sym2.map_mk, SimpleGraph.mem_edgeFinset] using hmapped
  have hcard' : (source.edgeFinset.map e.toEmbedding.sym2Map).card =
      target.edgeFinset.card := by
    rw [Finset.card_map]
    simpa [source, target] using hcard
  have hedgeFinset : source.edgeFinset.map e.toEmbedding.sym2Map =
      target.edgeFinset :=
    Finset.eq_of_subset_of_card_le hsubset hcard'.ge
  intro x y
  change source.Adj x y ↔
    target.Adj (r.perm.apply x) (r.perm.apply y)
  constructor
  · intro hs
    exact hforward x y (by simpa [source] using hs)
  · intro ht
    have htmem : e.toEmbedding.sym2Map s(x, y) ∈
        target.edgeFinset := by
      simpa [target, e, VertexPermutation.equiv_apply,
        SimpleGraph.mem_edgeFinset, Sym2.map_mk] using ht
    rw [← hedgeFinset, Finset.mem_map] at htmem
    obtain ⟨q, hq, hqe⟩ := htmem
    have hqeq : q = s(x, y) := e.toEmbedding.sym2Map.injective hqe
    subst q
    simpa [source, SimpleGraph.mem_edgeFinset] using hq

/-! ## Claimed-mask rows -/

/-- A packed transition carries the target mask used by its repeated local
checks.  A separate scalar equality ties it to `children[child]`. -/
structure ClaimedTransition (n : ℕ) where
  child : ℕ
  target : BitVec (edgeCount n)
  perm : VertexPermutation n
  deriving DecidableEq

def ClaimedTransition.erase (r : ClaimedTransition n) : Transition n :=
  ⟨r.child, r.perm⟩

structure ClaimedRow (n : ℕ) where
  parent : BitVec (edgeCount n)
  slots : Array (Option (ClaimedTransition n))
  deriving DecidableEq

/-- A level with an executable lookup function.  Generated `maskAt`
definitions use a balanced range split, so lookup depth is logarithmic in the
number of representatives. -/
structure Level (n : ℕ) where
  count : ℕ
  maskAt : ℕ → BitVec (edgeCount n)

def Level.getD (level : Level n) (index : ℕ) : BitVec (edgeCount n) :=
  if index < level.count then level.maskAt index else 0

def Level.toArray (level : Level n) : Array (BitVec (edgeCount n)) :=
  Array.ofFn (fun index : Fin level.count ↦ level.maskAt index)

@[simp] theorem Level.toArray_size (level : Level n) :
    level.toArray.size = level.count := by simp [Level.toArray]

@[simp] theorem Level.toArray_getElem (level : Level n)
    (index : Fin level.count) : level.toArray[index] = level.maskAt index := by
  simp [Level.toArray]

theorem Level.toArray_getD (level : Level n) (index : ℕ) :
    level.toArray.getD index 0 = level.getD index := by
  by_cases hindex : index < level.count
  · have harray : index < level.toArray.size := by
      simpa only [Level.toArray_size] using hindex
    rw [← Array.getElem_eq_getD (h := harray)]
    simp [Level.toArray, Level.getD, hindex]
  · have harray : ¬index < level.toArray.size := by simpa only [Level.toArray_size]
    have hle : level.toArray.size ≤ index := Nat.le_of_not_gt harray
    simp [Array.getD, Level.getD, hindex, harray, hle]

def readClaimedTransition (n : ℕ) (input : Cursor) :
    Option (ClaimedTransition n × Cursor) := do
  let (child, afterChild) ← readNat input
  let (target, afterTarget) ← readNat afterChild
  if ¬target < 2 ^ edgeCount n then none else
  let (images, rest) ← readImages n n afterTarget
  some (⟨child, BitVec.ofNat (edgeCount n) target, ⟨images.toArray⟩⟩, rest)

def readClaimedSlot (n : ℕ) (parent : BitVec (edgeCount n))
    (index : ℕ) (input : Cursor) :
    Option (Option (ClaimedTransition n) × Cursor) :=
  if parent.getLsbD index then some (none, input)
  else do
    let (transition, rest) ← readClaimedTransition n input
    some (some transition, rest)

def readClaimedSlots (n : ℕ) (parent : BitVec (edgeCount n)) :
    ℕ → ℕ → Cursor →
      Option (List (Option (ClaimedTransition n)) × Cursor)
  | 0, _, input => some ([], input)
  | 1, index, input => do
      let (r₁, rest) ← readClaimedSlot n parent index input
      some ([r₁], rest)
  | 2, index, input => do
      let (r₁, after₁) ← readClaimedSlot n parent index input
      let (r₂, rest) ← readClaimedSlot n parent (index + 1) after₁
      some ([r₁, r₂], rest)
  | 3, index, input => do
      let (r₁, after₁) ← readClaimedSlot n parent index input
      let (r₂, after₂) ← readClaimedSlot n parent (index + 1) after₁
      let (r₃, rest) ← readClaimedSlot n parent (index + 2) after₂
      some ([r₁, r₂, r₃], rest)
  | count + 4, index, input => do
      let (r₁, after₁) ← readClaimedSlot n parent index input
      let (r₂, after₂) ← readClaimedSlot n parent (index + 1) after₁
      let (r₃, after₃) ← readClaimedSlot n parent (index + 2) after₂
      let (r₄, after₄) ← readClaimedSlot n parent (index + 3) after₃
      let (rows, rest) ← readClaimedSlots n parent count (index + 4) after₄
      some (r₁ :: r₂ :: r₃ :: r₄ :: rows, rest)

def decodeClaimedRow (n : ℕ) (blob : Blob) : Option (ClaimedRow n) := do
  let (parent, afterParent) ← readNat blob.cursor
  if ¬parent < 2 ^ edgeCount n then none else
  let parentMask := BitVec.ofNat (edgeCount n) parent
  let (slots, rest) ←
    readClaimedSlots n parentMask (edgeCount n) 0 afterParent
  if rest.remaining = 0 ∧ rest.inChunk = 0 ∧ rest.data = 0 ∧
      rest.rest = [] then some ⟨parentMask, slots.toArray⟩ else none

def ClaimedTransition.LocalValid {n : ℕ} [NeZero n]
    (parent : BitVec (edgeCount n)) (children : Array (BitVec (edgeCount n)))
    (i j : Fin n) (r : ClaimedTransition n) : Prop :=
  r.child < children.size ∧ r.target = children.getD r.child 0 ∧
    r.perm.Valid ∧
    (addEdge (graphOfBits parent) i j).edgeFinset.card =
      (graphOfBits r.target).edgeFinset.card ∧
    ∀ x y : Fin n, (addEdge (graphOfBits parent) i j).Adj x y →
      (graphOfBits r.target).Adj (r.perm.apply x) (r.perm.apply y)

def ClaimedTransition.checkLocal {n : ℕ} [NeZero n]
    (parent : BitVec (edgeCount n)) (children : Array (BitVec (edgeCount n)))
    (i j : Fin n) (r : ClaimedTransition n) : Bool :=
  decide (r.child < children.size) && decide (r.target = children.getD r.child 0) &&
    r.perm.check && decide ((addEdge (graphOfBits parent) i j).edgeFinset.card =
      (graphOfBits r.target).edgeFinset.card) &&
    (List.finRange n).all (fun x ↦ (List.finRange n).all (fun y ↦
      if (addEdge (graphOfBits parent) i j).Adj x y then
        decide ((graphOfBits r.target).Adj (r.perm.apply x) (r.perm.apply y))
      else true))

@[simp] theorem ClaimedTransition.checkLocal_eq_true_iff {n : ℕ} [NeZero n]
    (parent : BitVec (edgeCount n)) (children : Array (BitVec (edgeCount n)))
    (i j : Fin n) (r : ClaimedTransition n) :
    r.checkLocal parent children i j = true ↔ r.LocalValid parent children i j := by
  constructor
  · intro h
    simp only [ClaimedTransition.checkLocal, Bool.and_eq_true] at h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa using h.1.1.1.1
    · simpa using h.1.1.1.2
    · simpa using h.1.1.2
    · simpa using h.1.2
    · intro x y hadj
      have hx : x ∈ List.finRange n := List.mem_finRange x
      have hy : y ∈ List.finRange n := List.mem_finRange y
      have houter := List.all_eq_true.mp h.2 x hx
      have hinner := List.all_eq_true.mp houter y hy
      simp only [if_pos hadj] at hinner
      simpa using hinner
  · rintro ⟨hchild, htarget, hperm, hcard, hforward⟩
    simp only [ClaimedTransition.checkLocal, Bool.and_eq_true]
    refine ⟨⟨⟨⟨by simpa using hchild, by simpa using htarget⟩,
      by simpa using hperm⟩, by simpa using hcard⟩, ?_⟩
    apply List.all_eq_true.mpr
    intro x hx
    apply List.all_eq_true.mpr
    intro y hy
    by_cases hadj : (addEdge (graphOfBits parent) i j).Adj x y
    · simp only [if_pos hadj]
      simpa using hforward x y hadj
    · simp only [if_neg hadj]

instance {n : ℕ} [NeZero n] (parent : BitVec (edgeCount n))
    (children : Array (BitVec (edgeCount n))) (i j : Fin n)
    (r : ClaimedTransition n) : Decidable (r.LocalValid parent children i j) :=
  decidable_of_iff (r.checkLocal parent children i j = true)
    (ClaimedTransition.checkLocal_eq_true_iff parent children i j r)

theorem ClaimedTransition.LocalValid.valid {n : ℕ} [NeZero n]
    {parents children : Array (BitVec (edgeCount n))} {p : Fin parents.size}
    {parent : BitVec (edgeCount n)} {i j : Fin n} {r : ClaimedTransition n}
    (hparent : parent = parents[p]) (h : r.LocalValid parent children i j) :
    r.erase.Valid parents children p i j := by
  rcases h with ⟨hchild, htarget, hperm, hcard, hforward⟩
  refine ⟨hchild, hperm, ?_⟩
  have hlocal : ∀ x y : Fin n,
      (addEdge (graphOfBits parent) i j).Adj x y ↔
        (graphOfBits r.target).Adj (r.perm.apply x) (r.perm.apply y) := by
    let fakeParents : Array (BitVec (edgeCount n)) := #[parent]
    let fakeChildren : Array (BitVec (edgeCount n)) := #[r.target]
    let fake : Transition n := ⟨0, r.perm⟩
    have hs : Transition.SparseValid fakeParents fakeChildren
        ⟨0, by simp [fakeParents]⟩ i j fake := by
      refine ⟨by simp [fake, fakeChildren], hperm, ?_, ?_⟩
      · change (addEdge (graphOfBits parent) i j).edgeFinset.card =
          (graphOfBits r.target).edgeFinset.card
        exact hcard
      · simpa [fakeParents, fakeChildren, fake] using hforward
    simpa [fakeParents, fakeChildren, fake] using
      (Transition.SparseValid.valid hs).2.2
  intro x y
  change (addEdge (graphOfBits parents[p]) i j).Adj x y ↔
    (graphOfBits (children.getD r.child 0)).Adj
      (r.perm.apply x) (r.perm.apply y)
  rw [← hparent, ← htarget]
  exact hlocal x y

def ClaimedRow.erase (row : ClaimedRow n) :
    Array (Option (Transition n)) :=
  row.slots.map (Option.map ClaimedTransition.erase)

lemma getD_map_option {α β : Type*} (xs : Array (Option α))
    (f : α → β) (index : ℕ) :
    (xs.map (Option.map f)).getD index none =
      Option.map f (xs.getD index none) := by
  by_cases hindex : index < xs.size
  · have hmap : index < (xs.map (Option.map f)).size := by simpa
    rw [← Array.getElem_eq_getD (h := hmap),
      ← Array.getElem_eq_getD (h := hindex)]
    simp
  · have hmap : ¬index < (xs.map (Option.map f)).size := by
      simpa only [Array.size_map] using hindex
    have hle : xs.size ≤ index := Nat.le_of_not_gt hindex
    simp [Array.getD, hindex, hmap, hle]

def ClaimedSlotValid {n : ℕ} [NeZero n]
    (parent : BitVec (edgeCount n))
    (children : Array (BitVec (edgeCount n))) (i j : Fin n)
    (slot : Option (ClaimedTransition n)) : Prop :=
  match slot with
  | none => (graphOfBits parent).Adj i j
  | some r => ¬(graphOfBits parent).Adj i j ∧
      r.LocalValid parent children i j

instance {n : ℕ} [NeZero n] (parent : BitVec (edgeCount n))
    (children : Array (BitVec (edgeCount n))) (i j : Fin n)
    (slot : Option (ClaimedTransition n)) :
    Decidable (ClaimedSlotValid parent children i j slot) := by
  cases slot <;> unfold ClaimedSlotValid <;> infer_instance

def ClaimedRow.Valid {n : ℕ} [NeZero n]
    (parents children : Array (BitVec (edgeCount n)))
    (p : Fin parents.size) (row : ClaimedRow n) : Prop :=
  row.parent = parents[p] ∧ row.slots.size = edgeCount n ∧
    ∀ i j : Fin n, i < j →
      ClaimedSlotValid row.parent children i j
        (row.slots.getD (edgeIndex i j) none)

instance {n : ℕ} [NeZero n]
    (parents children : Array (BitVec (edgeCount n)))
    (p : Fin parents.size) (row : ClaimedRow n) : Decidable (row.Valid parents children p) := by
  unfold ClaimedRow.Valid
  infer_instance

theorem ClaimedRow.Valid.valid {n : ℕ} [NeZero n]
    {parents children : Array (BitVec (edgeCount n))}
    {p : Fin parents.size} {row : ClaimedRow n}
    (h : row.Valid parents children p) :
    RowValid parents children p row.erase := by
  refine ⟨by simp [ClaimedRow.erase, h.2.1], ?_⟩
  intro i j hij
  have hslot := h.2.2 i j hij
  rw [ClaimedRow.erase, getD_map_option]
  generalize hget : row.slots.getD (edgeIndex i j) none = slot at hslot ⊢
  cases slot with
  | none => simpa [h.1, ClaimedSlotValid, SlotValid] using hslot
  | some r => exact ⟨by simpa [h.1] using hslot.1, hslot.2.valid h.1⟩

def checkClaimedRow {n : ℕ} [NeZero n]
    (parents children : Array (BitVec (edgeCount n)))
    (parentIndex : ℕ) (blob : Blob) : Bool :=
  if h : parentIndex < parents.size then
    match decodeClaimedRow n blob with
    | none => false
    | some row => decide (row.Valid parents children ⟨parentIndex, h⟩)
  else false

theorem checkClaimedRow_sound {n : ℕ} [NeZero n]
    (parents children : Array (BitVec (edgeCount n)))
    (parentIndex : ℕ) (blob : Blob)
    (h : checkClaimedRow parents children parentIndex blob = true) :
    ∃ hp : parentIndex < parents.size, ∃ row : ClaimedRow n,
      decodeClaimedRow n blob = some row ∧
        RowValid parents children ⟨parentIndex, hp⟩ row.erase := by
  unfold checkClaimedRow at h
  split at h
  next hp =>
    cases hdecode : decodeClaimedRow n blob with
    | none => simp [hdecode] at h
    | some row =>
        refine ⟨hp, row, rfl, ?_⟩
        apply ClaimedRow.Valid.valid
        simpa [hdecode] using h
  next hp => simp at h

/-! ## Split local and level-alignment checks -/

def ClaimedTransition.CoreValid {n : ℕ} [NeZero n]
    (parent : BitVec (edgeCount n)) (i j : Fin n)
    (r : ClaimedTransition n) : Prop :=
  r.perm.Valid ∧
    (addEdge (graphOfBits parent) i j).edgeFinset.card =
      (graphOfBits r.target).edgeFinset.card ∧
    ∀ x y : Fin n, (addEdge (graphOfBits parent) i j).Adj x y →
      (graphOfBits r.target).Adj (r.perm.apply x) (r.perm.apply y)

def ClaimedTransition.checkCore {n : ℕ} [NeZero n]
    (parent : BitVec (edgeCount n)) (i j : Fin n)
    (r : ClaimedTransition n) : Bool :=
  r.perm.check && decide ((addEdge (graphOfBits parent) i j).edgeFinset.card =
    (graphOfBits r.target).edgeFinset.card) &&
    (List.finRange n).all (fun x ↦ (List.finRange n).all (fun y ↦
      if (addEdge (graphOfBits parent) i j).Adj x y then
        decide ((graphOfBits r.target).Adj (r.perm.apply x) (r.perm.apply y))
      else true))

@[simp] theorem ClaimedTransition.checkCore_eq_true_iff {n : ℕ} [NeZero n]
    (parent : BitVec (edgeCount n)) (i j : Fin n)
    (r : ClaimedTransition n) :
    r.checkCore parent i j = true ↔ r.CoreValid parent i j := by
  constructor
  · intro h
    simp only [ClaimedTransition.checkCore, Bool.and_eq_true] at h
    refine ⟨by simpa using h.1.1, by simpa using h.1.2, ?_⟩
    intro x y hadj
    have hx : x ∈ List.finRange n := List.mem_finRange x
    have hy : y ∈ List.finRange n := List.mem_finRange y
    have houter := List.all_eq_true.mp h.2 x hx
    have hinner := List.all_eq_true.mp houter y hy
    simp only [if_pos hadj] at hinner
    simpa using hinner
  · rintro ⟨hperm, hcard, hforward⟩
    simp only [ClaimedTransition.checkCore, Bool.and_eq_true]
    refine ⟨⟨by simpa using hperm, by simpa using hcard⟩, ?_⟩
    apply List.all_eq_true.mpr
    intro x hx
    apply List.all_eq_true.mpr
    intro y hy
    by_cases hadj : (addEdge (graphOfBits parent) i j).Adj x y
    · simp only [if_pos hadj]
      simpa using hforward x y hadj
    · simp only [if_neg hadj]

instance {n : ℕ} [NeZero n] (parent : BitVec (edgeCount n))
    (i j : Fin n) (r : ClaimedTransition n) :
    Decidable (r.CoreValid parent i j) :=
  decidable_of_iff (r.checkCore parent i j = true)
    (ClaimedTransition.checkCore_eq_true_iff parent i j r)

def CoreSlotValid {n : ℕ} [NeZero n] (parent : BitVec (edgeCount n))
    (i j : Fin n) (slot : Option (ClaimedTransition n)) : Prop :=
  match slot with
  | none => (graphOfBits parent).Adj i j
  | some r => ¬(graphOfBits parent).Adj i j ∧ r.CoreValid parent i j

instance {n : ℕ} [NeZero n] (parent : BitVec (edgeCount n))
    (i j : Fin n) (slot : Option (ClaimedTransition n)) :
    Decidable (CoreSlotValid parent i j slot) := by
  cases slot <;> unfold CoreSlotValid <;> infer_instance

def ClaimedRow.CoreValid {n : ℕ} [NeZero n]
    (parents : Level n) (p : Fin parents.count) (row : ClaimedRow n) : Prop :=
  row.parent = parents.maskAt p ∧ row.slots.size = edgeCount n ∧
    ∀ i j : Fin n, i < j → CoreSlotValid row.parent i j
      (row.slots.getD (edgeIndex i j) none)

instance {n : ℕ} [NeZero n] (parents : Level n)
    (p : Fin parents.count) (row : ClaimedRow n) :
    Decidable (row.CoreValid parents p) := by
  unfold ClaimedRow.CoreValid
  infer_instance

def ClaimedTransition.ClaimValid (children : Level n)
    (r : ClaimedTransition n) : Prop :=
  r.child < children.count ∧ r.target = children.getD r.child

instance (children : Level n) (r : ClaimedTransition n) :
    Decidable (r.ClaimValid children) := by
  unfold ClaimedTransition.ClaimValid Level.getD
  infer_instance

def ClaimedRow.ClaimsValid (children : Level n) (row : ClaimedRow n) : Prop :=
  row.slots.toList.all (fun
    | none => true
    | some transition => decide (transition.ClaimValid children)) = true

instance (children : Level n) (row : ClaimedRow n) :
    Decidable (row.ClaimsValid children) := by
  unfold ClaimedRow.ClaimsValid
  infer_instance

def checkClaimedRowCore {n : ℕ} [NeZero n]
    (parents : Level n) (parentIndex : ℕ) (blob : Blob) : Bool :=
  if h : parentIndex < parents.count then
    match decodeClaimedRow n blob with
    | none => false
    | some row => decide (row.CoreValid parents ⟨parentIndex, h⟩)
  else false

def checkClaimedRowClaims (children : Level n) (blob : Blob) : Bool :=
  match decodeClaimedRow n blob with
  | none => false
  | some row => decide (row.ClaimsValid children)

theorem checkClaimedRowCore_sound {n : ℕ} [NeZero n]
    (parents : Level n) (parentIndex : ℕ) (blob : Blob)
    (h : checkClaimedRowCore parents parentIndex blob = true) :
    ∃ hp : parentIndex < parents.count, ∃ row : ClaimedRow n,
      decodeClaimedRow n blob = some row ∧
        row.CoreValid parents ⟨parentIndex, hp⟩ := by
  unfold checkClaimedRowCore at h
  split at h
  next hp =>
    cases hdecode : decodeClaimedRow n blob with
    | none => simp [hdecode] at h
    | some row => exact ⟨hp, row, rfl, by simpa [hdecode] using h⟩
  next hp => simp at h

theorem checkClaimedRowClaims_sound (children : Level n) (blob : Blob)
    (h : checkClaimedRowClaims children blob = true) :
    ∃ row : ClaimedRow n, decodeClaimedRow n blob = some row ∧
      row.ClaimsValid children := by
  cases hdecode : decodeClaimedRow n blob with
  | none => simp [checkClaimedRowClaims, hdecode] at h
  | some row => exact ⟨row, rfl, by simpa [checkClaimedRowClaims, hdecode] using h⟩

theorem ClaimedRow.CoreValid.valid {n : ℕ} [NeZero n]
    (hpairs : CertificateChecker.PackingCert.PairIndexValid n)
    {parents children : Level n} {p : Fin parents.count} {row : ClaimedRow n}
    (hcore : row.CoreValid parents p) (hclaims : row.ClaimsValid children) :
    RowValid parents.toArray children.toArray
      ⟨p, by simpa only [Level.toArray_size] using p.isLt⟩ row.erase := by
  let p' : Fin parents.toArray.size :=
    ⟨p, by simpa only [Level.toArray_size] using p.isLt⟩
  change RowValid parents.toArray children.toArray p' row.erase
  refine ⟨by simp [ClaimedRow.erase, hcore.2.1], ?_⟩
  intro i j hij
  have hslot := hcore.2.2 i j hij
  have hindex : edgeIndex i j < row.slots.size := by
    rw [hcore.2.1]
    exact hpairs.1 i j (by omega)
  have hget : row.slots.getD (edgeIndex i j) none = row.slots[edgeIndex i j] :=
    (Array.getElem_eq_getD none).symm
  rw [ClaimedRow.erase, getD_map_option, hget]
  rw [hget, hcore.1] at hslot
  generalize hslotEq : row.slots[edgeIndex i j] = slot at hslot ⊢
  cases slot with
  | none =>
      have hslot' : (graphOfBits (parents.maskAt p)).Adj i j := by
        simpa [CoreSlotValid] using hslot
      change (graphOfBits parents.toArray[p']).Adj i j
      simpa [p', Level.toArray] using hslot'
  | some r =>
      have hslot' :
          ¬(graphOfBits (parents.maskAt p)).Adj i j ∧
            r.CoreValid (parents.maskAt p) i j := by
        simpa [CoreSlotValid] using hslot
      have hrmem : some r ∈ row.slots.toList := by
        rw [← hslotEq]
        exact Array.getElem_mem_toList hindex
      have hclaimBool := List.all_eq_true.mp hclaims (some r) hrmem
      have hclaim : r.ClaimValid children := by
        exact of_decide_eq_true (by simpa using hclaimBool)
      have hlocal : r.LocalValid (parents.maskAt p) children.toArray i j := by
        refine ⟨by simpa only [Level.toArray_size] using hclaim.1, ?_,
          hslot'.2.1, hslot'.2.2.1, hslot'.2.2.2⟩
        rw [Level.toArray_getD]
        exact hclaim.2
      have hparent : parents.maskAt p = parents.toArray[p'] := by
        simp [p', Level.toArray]
      exact ⟨by simpa [p', Level.toArray] using hslot'.1,
        hlocal.valid hparent⟩

/-- The two shallow executable leaves can be checked independently and then
combined without re-evaluating either checker. -/
theorem checkClaimedRowSplit_sound {n : ℕ} [NeZero n]
    (hpairs : CertificateChecker.PackingCert.PairIndexValid n)
    (parents children : Level n) (parentIndex : ℕ) (blob : Blob)
    (hcore : checkClaimedRowCore parents parentIndex blob = true)
    (hclaims : checkClaimedRowClaims children blob = true) :
    ∃ hp : parentIndex < parents.count, ∃ row : ClaimedRow n,
      decodeClaimedRow n blob = some row ∧
        RowValid parents.toArray children.toArray
          ⟨parentIndex, by simpa only [Level.toArray_size] using hp⟩ row.erase := by
  rcases checkClaimedRowCore_sound parents parentIndex blob hcore with
    ⟨hp, row, hdecode, hrowCore⟩
  rcases checkClaimedRowClaims_sound children blob hclaims with
    ⟨row', hdecode', hrowClaims⟩
  rw [hdecode] at hdecode'
  injection hdecode' with hrow
  subst row'
  exact ⟨hp, row, hdecode, hrowCore.valid hpairs hrowClaims⟩

def SparseSlotValid {n : ℕ} [NeZero n]
    (parents children : Array (BitVec (edgeCount n)))
    (p : Fin parents.size) (i j : Fin n)
    (slot : Option (Transition n)) : Prop :=
  match slot with
  | none => (graphOfBits parents[p]).Adj i j
  | some r => ¬(graphOfBits parents[p]).Adj i j ∧
      Transition.SparseValid parents children p i j r

instance {n : ℕ} [NeZero n]
    (parents children : Array (BitVec (edgeCount n)))
    (p : Fin parents.size) (i j : Fin n)
    (slot : Option (Transition n)) :
    Decidable (SparseSlotValid parents children p i j slot) := by
  cases slot <;> unfold SparseSlotValid <;> infer_instance

def SparseRowValid {n : ℕ} [NeZero n]
    (parents children : Array (BitVec (edgeCount n)))
    (p : Fin parents.size) (row : Array (Option (Transition n))) : Prop :=
  row.size = edgeCount n ∧
    ∀ i j : Fin n, i < j →
      SparseSlotValid parents children p i j
        (row.getD (edgeIndex i j) none)

instance {n : ℕ} [NeZero n]
    (parents children : Array (BitVec (edgeCount n)))
    (p : Fin parents.size) (row : Array (Option (Transition n))) :
    Decidable (SparseRowValid parents children p row) := by
  unfold SparseRowValid
  infer_instance

theorem SparseRowValid.valid {n : ℕ} [NeZero n]
    {parents children : Array (BitVec (edgeCount n))}
    {p : Fin parents.size} {row : Array (Option (Transition n))}
    (h : SparseRowValid parents children p row) :
    RowValid parents children p row := by
  refine ⟨h.1, ?_⟩
  intro i j hij
  have hslot := h.2 i j hij
  generalize hget : row.getD (edgeIndex i j) none = slot at hslot ⊢
  cases slot with
  | none => exact hslot
  | some r => exact ⟨hslot.1, Transition.SparseValid.valid hslot.2⟩

def checkRowSparse {n : ℕ} [NeZero n]
    (parents children : Array (BitVec (edgeCount n)))
    (parentIndex : ℕ) (blob : Blob) : Bool :=
  if h : parentIndex < parents.size then
    match decodeRow n parents[parentIndex] blob with
    | none => false
    | some row => decide (SparseRowValid parents children ⟨parentIndex, h⟩ row)
  else false

theorem checkRowSparse_sound {n : ℕ} [NeZero n]
    (parents children : Array (BitVec (edgeCount n)))
    (parentIndex : ℕ) (blob : Blob)
    (h : checkRowSparse parents children parentIndex blob = true) :
    ∃ hp : parentIndex < parents.size,
      ∃ row : Array (Option (Transition n)),
        decodeRow n parents[parentIndex] blob = some row ∧
          RowValid parents children ⟨parentIndex, hp⟩ row := by
  unfold checkRowSparse at h
  split at h
  next hp =>
    cases hdecode : decodeRow n parents[parentIndex] blob with
    | none => simp [hdecode] at h
    | some row =>
        refine ⟨hp, row, hdecode, ?_⟩
        apply SparseRowValid.valid
        simpa [hdecode] using h
  next hp => simp at h

def checkRow {n : ℕ} [NeZero n]
    (parents children : Array (BitVec (edgeCount n)))
    (parentIndex : ℕ) (blob : Blob) : Bool :=
  if h : parentIndex < parents.size then
    match decodeRow n parents[parentIndex] blob with
    | none => false
    | some row => decide (RowValid parents children ⟨parentIndex, h⟩ row)
  else false

theorem checkRow_sound {n : ℕ} [NeZero n]
    (parents children : Array (BitVec (edgeCount n)))
    (parentIndex : ℕ) (blob : Blob)
    (h : checkRow parents children parentIndex blob = true) :
    ∃ hp : parentIndex < parents.size,
      ∃ row : Array (Option (Transition n)),
        decodeRow n parents[parentIndex] blob = some row ∧
          RowValid parents children ⟨parentIndex, hp⟩ row := by
  unfold checkRow at h
  split at h
  next hp =>
    cases hdecode : decodeRow n parents[parentIndex] blob with
    | none => simp [hdecode] at h
    | some row =>
        refine ⟨hp, row, hdecode, ?_⟩
        simpa [hdecode] using h
  next hp => simp at h

/-- Proof-only consecutive-row aggregate.  Generated modules use one ordinary
`by decide` leaf per row (or other empirically safe row shard). -/
inductive RowsValidFrom {n : ℕ} [NeZero n]
    (parents children : Array (BitVec (edgeCount n))) :
    ℕ → List Blob → Prop where
  | nil (start : ℕ) : RowsValidFrom parents children start []
  | cons {start : ℕ} {blob : Blob} {blobs : List Blob}
      (head : checkRow parents children start blob = true)
      (tail : RowsValidFrom parents children (start + 1) blobs) :
      RowsValidFrom parents children start (blob :: blobs)

def tableListFrom {n : ℕ} (parents : Array (BitVec (edgeCount n))) :
    ℕ → List Blob → List (Array (Option (Transition n)))
  | _, [] => []
  | start, blob :: blobs =>
      rowOf n (parents.getD start 0) blob ::
        tableListFrom parents (start + 1) blobs

def tableFrom {n : ℕ} (parents : Array (BitVec (edgeCount n)))
    (start : ℕ) (blobs : List Blob) :
    Array (Array (Option (Transition n))) :=
  (tableListFrom parents start blobs).toArray

@[simp] lemma tableListFrom_length {n : ℕ}
    (parents : Array (BitVec (edgeCount n))) (start : ℕ)
    (blobs : List Blob) :
    (tableListFrom parents start blobs).length = blobs.length := by
  induction blobs generalizing start with
  | nil => simp [tableListFrom]
  | cons blob blobs ih => simp [tableListFrom, ih]

theorem RowsValidFrom.toRowsValidListFrom {n : ℕ} [NeZero n]
    {parents children : Array (BitVec (edgeCount n))}
    {start : ℕ} {blobs : List Blob}
    (h : RowsValidFrom parents children start blobs) :
    CertificateExhaustion.RowsValidListFrom parents children start
      (tableFrom parents start blobs).toList := by
  change CertificateExhaustion.RowsValidListFrom parents children start
    (tableListFrom parents start blobs)
  induction h with
  | nil start => simp [tableListFrom, CertificateExhaustion.RowsValidListFrom]
  | @cons start blob blobs head tail ih =>
      obtain ⟨hp, row, hdecode, hrow⟩ :=
        checkRow_sound parents children start blob head
      simp only [tableListFrom,
        CertificateExhaustion.RowsValidListFrom]
      rw [dif_pos hp]
      constructor
      · have hparent : parents.getD start 0 = parents[start] :=
          (Array.getElem_eq_getD 0).symm
        rw [hparent]
        simpa [rowOf, hdecode] using hrow
      · exact ih

theorem RowsValidFrom.toRowsValidFrom {n : ℕ} [NeZero n]
    {parents children : Array (BitVec (edgeCount n))}
    {start : ℕ} {blobs : List Blob}
    (h : RowsValidFrom parents children start blobs) :
    CertificateExhaustion.RowsValidFrom parents children start
      (tableFrom parents start blobs) := by
  unfold CertificateExhaustion.RowsValidFrom
  exact h.toRowsValidListFrom

theorem RowsValidFrom.stepValid {n : ℕ} [NeZero n]
    {parents children : Array (BitVec (edgeCount n))}
    {blobs : List Blob} (h : RowsValidFrom parents children 0 blobs)
    (hsize : blobs.length = parents.size) :
    StepValid parents children (tableFrom parents 0 blobs) := by
  apply StepValid.of_rowsValidFrom
  · simpa [tableFrom] using hsize
  · exact h.toRowsValidFrom

/-! Production aggregate using the sparse transition checker. -/

inductive SparseRowsValidFrom {n : ℕ} [NeZero n]
    (parents children : Array (BitVec (edgeCount n))) :
    ℕ → List Blob → Prop where
  | nil (start : ℕ) : SparseRowsValidFrom parents children start []
  | cons {start : ℕ} {blob : Blob} {blobs : List Blob}
      (head : checkRowSparse parents children start blob = true)
      (tail : SparseRowsValidFrom parents children (start + 1) blobs) :
      SparseRowsValidFrom parents children start (blob :: blobs)

theorem SparseRowsValidFrom.append {n : ℕ} [NeZero n]
    {parents children : Array (BitVec (edgeCount n))}
    {start : ℕ} {left right : List Blob}
    (hleft : SparseRowsValidFrom parents children start left)
    (hright : SparseRowsValidFrom parents children
      (start + left.length) right) :
    SparseRowsValidFrom parents children start (left ++ right) := by
  induction hleft with
  | nil start => simpa using hright
  | @cons start blob blobs head tail ih =>
      apply SparseRowsValidFrom.cons head
      apply ih
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hright

theorem SparseRowsValidFrom.toRowsValidListFrom {n : ℕ} [NeZero n]
    {parents children : Array (BitVec (edgeCount n))}
    {start : ℕ} {blobs : List Blob}
    (h : SparseRowsValidFrom parents children start blobs) :
    CertificateExhaustion.RowsValidListFrom parents children start
      (tableFrom parents start blobs).toList := by
  change CertificateExhaustion.RowsValidListFrom parents children start
    (tableListFrom parents start blobs)
  induction h with
  | nil start => simp [tableListFrom, CertificateExhaustion.RowsValidListFrom]
  | @cons start blob blobs head tail ih =>
      obtain ⟨hp, row, hdecode, hrow⟩ :=
        checkRowSparse_sound parents children start blob head
      simp only [tableListFrom,
        CertificateExhaustion.RowsValidListFrom]
      rw [dif_pos hp]
      constructor
      · have hparent : parents.getD start 0 = parents[start] :=
          (Array.getElem_eq_getD 0).symm
        rw [hparent]
        simpa [rowOf, hdecode] using hrow
      · exact ih

theorem SparseRowsValidFrom.toRowsValidFrom {n : ℕ} [NeZero n]
    {parents children : Array (BitVec (edgeCount n))}
    {start : ℕ} {blobs : List Blob}
    (h : SparseRowsValidFrom parents children start blobs) :
    CertificateExhaustion.RowsValidFrom parents children start
      (tableFrom parents start blobs) := by
  unfold CertificateExhaustion.RowsValidFrom
  exact h.toRowsValidListFrom

theorem SparseRowsValidFrom.stepValid {n : ℕ} [NeZero n]
    {parents children : Array (BitVec (edgeCount n))}
    {blobs : List Blob} (h : SparseRowsValidFrom parents children 0 blobs)
    (hsize : blobs.length = parents.size) :
    StepValid parents children (tableFrom parents 0 blobs) := by
  apply StepValid.of_rowsValidFrom
  · simpa [tableFrom] using hsize
  · exact h.toRowsValidFrom

/-! Production aggregate for split claimed-mask rows.  Each generated row has
two independent ordinary-`decide` leaves: one checks the graph/permutation
semantics against local target masks, and the other checks the shallow
child-index-to-mask lookups. -/

def claimedRowOf (n : ℕ) (blob : Blob) :
    Array (Option (Transition n)) :=
  match decodeClaimedRow n blob with
  | none => #[]
  | some row => row.erase

def claimedTableListFrom (n : ℕ) : List Blob →
    List (Array (Option (Transition n)))
  | [] => []
  | blob :: blobs => claimedRowOf n blob :: claimedTableListFrom n blobs

def claimedTableFrom (n : ℕ) (blobs : List Blob) :
    Array (Array (Option (Transition n))) :=
  (claimedTableListFrom n blobs).toArray

@[simp] theorem claimedTableListFrom_length (n : ℕ) (blobs : List Blob) :
    (claimedTableListFrom n blobs).length = blobs.length := by
  induction blobs with
  | nil => simp [claimedTableListFrom]
  | cons blob blobs ih => simp [claimedTableListFrom, ih]

inductive ClaimedRowsValidFrom {n : ℕ} [NeZero n]
    (hpairs : CertificateChecker.PackingCert.PairIndexValid n)
    (parents children : Level n) : ℕ → List Blob → Prop where
  | nil (start : ℕ) : ClaimedRowsValidFrom hpairs parents children start []
  | cons {start : ℕ} {blob : Blob} {blobs : List Blob}
      (core : checkClaimedRowCore parents start blob = true)
      (claims : checkClaimedRowClaims children blob = true)
      (tail : ClaimedRowsValidFrom hpairs parents children (start + 1) blobs) :
      ClaimedRowsValidFrom hpairs parents children start (blob :: blobs)

theorem ClaimedRowsValidFrom.append {n : ℕ} [NeZero n]
    {hpairs : CertificateChecker.PackingCert.PairIndexValid n}
    {parents children : Level n} {start : ℕ} {left right : List Blob}
    (hleft : ClaimedRowsValidFrom hpairs parents children start left)
    (hright : ClaimedRowsValidFrom hpairs parents children
      (start + left.length) right) :
    ClaimedRowsValidFrom hpairs parents children start (left ++ right) := by
  induction hleft with
  | nil start => simpa using hright
  | @cons start blob blobs core claims tail ih =>
      apply ClaimedRowsValidFrom.cons core claims
      apply ih
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hright

theorem ClaimedRowsValidFrom.toRowsValidListFrom {n : ℕ} [NeZero n]
    {hpairs : CertificateChecker.PackingCert.PairIndexValid n}
    {parents children : Level n} {start : ℕ} {blobs : List Blob}
    (h : ClaimedRowsValidFrom hpairs parents children start blobs) :
    CertificateExhaustion.RowsValidListFrom parents.toArray children.toArray start
      (claimedTableFrom n blobs).toList := by
  change CertificateExhaustion.RowsValidListFrom parents.toArray children.toArray
    start (claimedTableListFrom n blobs)
  induction h with
  | nil start =>
      simp [claimedTableListFrom, CertificateExhaustion.RowsValidListFrom]
  | @cons start blob blobs core claims tail ih =>
      obtain ⟨hp, row, hdecode, hrow⟩ :=
        checkClaimedRowSplit_sound hpairs parents children start blob core claims
      simp only [claimedTableListFrom,
        CertificateExhaustion.RowsValidListFrom]
      have hp' : start < parents.toArray.size := by
        simpa only [Level.toArray_size] using hp
      rw [dif_pos hp']
      constructor
      · simpa [claimedRowOf, hdecode] using hrow
      · exact ih

theorem ClaimedRowsValidFrom.toRowsValidFrom {n : ℕ} [NeZero n]
    {hpairs : CertificateChecker.PackingCert.PairIndexValid n}
    {parents children : Level n} {start : ℕ} {blobs : List Blob}
    (h : ClaimedRowsValidFrom hpairs parents children start blobs) :
    CertificateExhaustion.RowsValidFrom parents.toArray children.toArray start
      (claimedTableFrom n blobs) := by
  unfold CertificateExhaustion.RowsValidFrom
  exact h.toRowsValidListFrom

theorem ClaimedRowsValidFrom.stepValid {n : ℕ} [NeZero n]
    {hpairs : CertificateChecker.PackingCert.PairIndexValid n}
    {parents children : Level n} {blobs : List Blob}
    (h : ClaimedRowsValidFrom hpairs parents children 0 blobs)
    (hsize : blobs.length = parents.count) :
    StepValid parents.toArray children.toArray (claimedTableFrom n blobs) := by
  apply StepValid.of_rowsValidFrom
  · simpa [claimedTableFrom] using hsize
  · exact h.toRowsValidFrom

end Packed
end CertificateExhaustion
end Erdos76
