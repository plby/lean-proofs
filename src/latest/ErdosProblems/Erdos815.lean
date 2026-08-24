/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- Original license: Apache 2.0. Note: This file has been modified. -/
/-
This is a Lean formalization of a solution to Erdős Problem 815.
https://www.erdosproblems.com/forum/thread/815

Informal authors:
- Lothar Narins
- Alexey Pokrovskiy
- Tibor Szabó

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos815.md
-/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Coloring.Constructions
import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Data.Nat.Dist

/-!
# Erdős Problem 815

Narins, Pokrovskiy, and Szabó disproved the proposed eventual cycle
statement by constructing arbitrarily large degree-3-critical graphs with
no cycle of length 23.  The construction and its complete mathematical
proof are documented in `tex/815.tex`.
-/

namespace Erdos815

open Classical Finset Set SimpleGraph

attribute [local instance] Classical.decEq Classical.propDecidable

/-- A finite graph has the exact criticality property occurring in Problem 815:
it has `2|V|-2` edges, and every induced graph on a proper vertex subset has
minimum degree at most two. -/
noncomputable def DegreeThreeCritical {V : Type*} [Fintype V]
    (G : SimpleGraph V) : Prop :=
  G.edgeFinset.card = 2 * Fintype.card V - 2 ∧
    ∀ s : Set V, s ≠ Set.univ → (G.induce s).minDegree ≤ 2

/-- The affirmative assertion asked in Erdős Problem 815. -/
def Erdos815Statement : Prop :=
  ∀ k : ℕ, 3 ≤ k → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    ∀ G : SimpleGraph (Fin n),
      DegreeThreeCritical G → cycleGraph k ⊑ G

/-- The 24-periodic sequence used by Narins--Pokrovskiy--Szabó, with
zero-based indexing. -/
def avoidingValue (i : ℕ) : ℕ :=
  match i % 24 with
  | 0 => 1
  | 1 => 2
  | 2 => 1
  | 3 => 4
  | 4 => 3
  | 5 => 2
  | 6 => 7
  | 7 => 6
  | 8 => 5
  | 9 => 6
  | 10 => 7
  | 11 => 2
  | 12 => 3
  | 13 => 4
  | 14 => 1
  | 15 => 2
  | 16 => 1
  | 17 => 8
  | 18 => 9
  | 19 => 6
  | 20 => 5
  | 21 => 6
  | 22 => 9
  | _ => 8

theorem avoidingValue_pos (i : ℕ) : 0 < avoidingValue i := by
  have hbounded : ∀ r : Fin 24, 0 < avoidingValue r := by decide
  simpa [avoidingValue] using
    hbounded ⟨i % 24, Nat.mod_lt _ (by omega)⟩

theorem avoidingValue_le_nine (i : ℕ) : avoidingValue i ≤ 9 := by
  have hbounded : ∀ r : Fin 24, avoidingValue r ≤ 9 := by decide
  simpa [avoidingValue] using
    hbounded ⟨i % 24, Nat.mod_lt _ (by omega)⟩

theorem avoidingValue_parity (i : ℕ) :
    avoidingValue i % 2 = (i + 1) % 2 := by
  have hbounded : ∀ r : Fin 24,
      avoidingValue r % 2 = (r + 1) % 2 := by decide
  have h := hbounded ⟨i % 24, Nat.mod_lt _ (by omega)⟩
  have hav : avoidingValue (i % 24) = avoidingValue i := by
    simp [avoidingValue]
  rw [hav] at h
  have hmod : (i % 24 + 1) % 2 = (i + 1) % 2 := by omega
  exact h.trans hmod

theorem avoidingValue_eq_of_mod_eq {i j : ℕ}
    (h : i % 24 = j % 24) :
    avoidingValue i = avoidingValue j := by
  simp [avoidingValue, h]

private theorem avoidingValue_avoid20_low : ∀ r : Fin 24,
    avoidingValue r + avoidingValue ((r + 1) % 24) + 1 ≠ 20 ∧
    avoidingValue r + avoidingValue ((r + 2) % 24) + 2 ≠ 20 ∧
    avoidingValue r + avoidingValue ((r + 3) % 24) + 3 ≠ 20 ∧
    avoidingValue r + avoidingValue ((r + 4) % 24) + 4 ≠ 20 ∧
    avoidingValue r + avoidingValue ((r + 5) % 24) + 5 ≠ 20 ∧
    avoidingValue r + avoidingValue ((r + 6) % 24) + 6 ≠ 20 ∧
    avoidingValue r + avoidingValue ((r + 7) % 24) + 7 ≠ 20 ∧
    avoidingValue r + avoidingValue ((r + 8) % 24) + 8 ≠ 20 ∧
    avoidingValue r + avoidingValue ((r + 9) % 24) + 9 ≠ 20 := by
  decide

private theorem avoidingValue_avoid20_high : ∀ r : Fin 24,
    avoidingValue r + avoidingValue ((r + 10) % 24) + 10 ≠ 20 ∧
    avoidingValue r + avoidingValue ((r + 11) % 24) + 11 ≠ 20 ∧
    avoidingValue r + avoidingValue ((r + 12) % 24) + 12 ≠ 20 ∧
    avoidingValue r + avoidingValue ((r + 13) % 24) + 13 ≠ 20 ∧
    avoidingValue r + avoidingValue ((r + 14) % 24) + 14 ≠ 20 ∧
    avoidingValue r + avoidingValue ((r + 15) % 24) + 15 ≠ 20 ∧
    avoidingValue r + avoidingValue ((r + 16) % 24) + 16 ≠ 20 ∧
    avoidingValue r + avoidingValue ((r + 17) % 24) + 17 ≠ 20 ∧
    avoidingValue r + avoidingValue ((r + 18) % 24) + 18 ≠ 20 := by
  decide

private theorem avoidingValue_avoid20_bounded
    (r : Fin 24) (d : Fin 20) (hdPos : 0 < (d : ℕ)) :
    avoidingValue r +
        avoidingValue (((r : ℕ) + (d : ℕ)) % 24) + (d : ℕ) ≠ 20 := by
  rcases d with ⟨d, hdLt⟩
  change 0 < d at hdPos
  change avoidingValue r + avoidingValue (((r : ℕ) + d) % 24) + d ≠ 20
  have hdCases :
      d = 1 ∨ d = 2 ∨ d = 3 ∨ d = 4 ∨ d = 5 ∨ d = 6 ∨ d = 7 ∨
      d = 8 ∨ d = 9 ∨ d = 10 ∨ d = 11 ∨ d = 12 ∨ d = 13 ∨
      d = 14 ∨ d = 15 ∨ d = 16 ∨ d = 17 ∨ d = 18 ∨ d = 19 := by
    omega
  rcases hdCases with
    (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
  · exact (avoidingValue_avoid20_low r).1
  · exact (avoidingValue_avoid20_low r).2.1
  · exact (avoidingValue_avoid20_low r).2.2.1
  · exact (avoidingValue_avoid20_low r).2.2.2.1
  · exact (avoidingValue_avoid20_low r).2.2.2.2.1
  · exact (avoidingValue_avoid20_low r).2.2.2.2.2.1
  · exact (avoidingValue_avoid20_low r).2.2.2.2.2.2.1
  · exact (avoidingValue_avoid20_low r).2.2.2.2.2.2.2.1
  · exact (avoidingValue_avoid20_low r).2.2.2.2.2.2.2.2
  · exact (avoidingValue_avoid20_high r).1
  · exact (avoidingValue_avoid20_high r).2.1
  · exact (avoidingValue_avoid20_high r).2.2.1
  · exact (avoidingValue_avoid20_high r).2.2.2.1
  · exact (avoidingValue_avoid20_high r).2.2.2.2.1
  · exact (avoidingValue_avoid20_high r).2.2.2.2.2.1
  · exact (avoidingValue_avoid20_high r).2.2.2.2.2.2.1
  · exact (avoidingValue_avoid20_high r).2.2.2.2.2.2.2.1
  · exact (avoidingValue_avoid20_high r).2.2.2.2.2.2.2.2
  · have hrPos := avoidingValue_pos (r : ℕ)
    have hrdPos := avoidingValue_pos (((r : ℕ) + 19) % 24)
    omega

theorem avoidingValue_avoid20_of_lt {i j : ℕ} (hij : i < j) :
    avoidingValue i + avoidingValue j + Nat.dist i j ≠ 20 := by
  intro hEq
  have hiPos := avoidingValue_pos i
  have hjPos := avoidingValue_pos j
  have hd : Nat.dist i j = j - i :=
    Nat.dist_eq_sub_of_le (Nat.le_of_lt hij)
  let d := j - i
  have hdPos : 0 < d := by
    dsimp [d]
    omega
  have hdLt : d < 20 := by
    rw [hd] at hEq
    change avoidingValue i + avoidingValue j + d = 20 at hEq
    omega
  let r : Fin 24 := ⟨i % 24, Nat.mod_lt _ (by omega)⟩
  have hiVal : avoidingValue i = avoidingValue (r : ℕ) := by
    apply avoidingValue_eq_of_mod_eq
    simp [r]
  have hijEq : i + d = j := by
    dsimp [d]
    omega
  have hjMod : j % 24 = (((r : ℕ) + d) % 24) % 24 := by
    rw [Nat.mod_mod]
    have hdMod : d % 24 = d := Nat.mod_eq_of_lt (by omega)
    calc
      j % 24 = (i + d) % 24 := by rw [hijEq]
      _ = (i % 24 + d % 24) % 24 := Nat.add_mod _ _ _
      _ = (i % 24 + d) % 24 := by rw [hdMod]
      _ = ((r : ℕ) + d) % 24 := by rfl
  have hjVal :
      avoidingValue j = avoidingValue (((r : ℕ) + d) % 24) :=
    avoidingValue_eq_of_mod_eq hjMod
  have htable :=
    avoidingValue_avoid20_bounded r ⟨d, hdLt⟩ hdPos
  change avoidingValue r +
      avoidingValue (((r : ℕ) + d) % 24) + d ≠ 20 at htable
  apply htable
  rw [← hiVal, ← hjVal]
  rw [hd] at hEq
  change avoidingValue i + avoidingValue j + d = 20 at hEq
  exact hEq

theorem avoidingValue_avoid20 {i j : ℕ} (hij : i ≠ j) :
    avoidingValue i + avoidingValue j + Nat.dist i j ≠ 20 := by
  rcases lt_or_gt_of_ne hij with hij | hji
  · exact avoidingValue_avoid20_of_lt hij
  · intro hEq
    apply avoidingValue_avoid20_of_lt hji
    rw [Nat.dist_comm]
    omega

/-! ## A reusable finite parent-tree construction -/

section ParentGraph

variable {V : Type*} [Fintype V]

/-- The undirected graph associated to a rooted parent map. -/
def parentGraph (root : V) (parent : V → V) : SimpleGraph V :=
  SimpleGraph.fromRel fun v w ↦ v ≠ root ∧ parent v = w

@[simp]
lemma parentGraph_adj (root : V) (parent : V → V) (v w : V) :
    (parentGraph root parent).Adj v w ↔
      v ≠ w ∧ ((v ≠ root ∧ parent v = w) ∨
        (w ≠ root ∧ parent w = v)) :=
  Iff.rfl

variable (root : V) (parent : V → V) (height : V → ℕ)

lemma parentGraph_adj_parent
    (hroot : parent root = root)
    (hdesc : ∀ v, v ≠ root → height (parent v) < height v)
    {v : V} (hv : v ≠ root) :
    (parentGraph root parent).Adj v (parent v) := by
  rw [parentGraph_adj]
  exact ⟨fun h ↦ (hdesc v hv).ne (congrArg height h).symm,
    Or.inl ⟨hv, rfl⟩⟩

lemma parentGraph_reachable_root
    (hroot : parent root = root)
    (hdesc : ∀ v, v ≠ root → height (parent v) < height v) :
    ∀ v, (parentGraph root parent).Reachable v root := by
  intro v
  induction hvh : height v using Nat.strong_induction_on generalizing v with
  | h n ih =>
      by_cases hv : v = root
      · subst v
        exact .rfl
      · exact
          (parentGraph_adj_parent root parent height hroot hdesc hv).reachable.trans
            (ih (height (parent v)) (by
              simpa [← hvh] using hdesc v hv) (parent v) rfl)

lemma parentGraph_connected
    (hroot : parent root = root)
    (hdesc : ∀ v, v ≠ root → height (parent v) < height v) :
    (parentGraph root parent).Connected := by
  rw [connected_iff_exists_forall_reachable]
  exact ⟨root, fun v ↦
    (parentGraph_reachable_root root parent height hroot hdesc v).symm⟩

/-- Each nonroot vertex determines its parent edge. -/
noncomputable def parentEdge
    (hroot : parent root = root)
    (hdesc : ∀ v, v ≠ root → height (parent v) < height v) :
    {v : V // v ≠ root} → (parentGraph root parent).edgeSet :=
  fun v ↦ ⟨s(v.1, parent v.1), by
    rw [mem_edgeSet]
    exact parentGraph_adj_parent root parent height hroot hdesc v.2⟩

lemma parentEdge_injective
    (hroot : parent root = root)
    (hdesc : ∀ v, v ≠ root → height (parent v) < height v) :
    Function.Injective (parentEdge root parent height hroot hdesc) := by
  intro v w hvw
  have he : s(v.1, parent v.1) = s(w.1, parent w.1) :=
    congrArg Subtype.val hvw
  rw [Sym2.eq_iff] at he
  rcases he with he | he
  · exact Subtype.ext he.1
  · exfalso
    have hvlt := hdesc v.1 v.2
    have hwlt := hdesc w.1 w.2
    have hvwlt : height w.1 < height v.1 := by
      simpa only [he.2] using hvlt
    have hcycle : height w.1 < height (parent w.1) := by
      simpa only [he.1] using hvwlt
    exact Nat.lt_asymm hcycle hwlt

lemma parentEdge_surjective
    (hroot : parent root = root)
    (hdesc : ∀ v, v ≠ root → height (parent v) < height v) :
    Function.Surjective (parentEdge root parent height hroot hdesc) := by
  rintro ⟨e, he⟩
  induction e using Sym2.inductionOn with
  | _ v w =>
      rw [mem_edgeSet, parentGraph_adj] at he
      rcases he.2 with hv | hw
      · refine ⟨⟨v, hv.1⟩, ?_⟩
        apply Subtype.ext
        simp only [parentEdge, hv.2]
      · refine ⟨⟨w, hw.1⟩, ?_⟩
        apply Subtype.ext
        simp only [parentEdge, hw.2]
        exact Sym2.eq_swap

noncomputable def parentEdgeEquiv
    (hroot : parent root = root)
    (hdesc : ∀ v, v ≠ root → height (parent v) < height v) :
    {v : V // v ≠ root} ≃ (parentGraph root parent).edgeSet :=
  Equiv.ofBijective (parentEdge root parent height hroot hdesc)
    ⟨parentEdge_injective root parent height hroot hdesc,
      parentEdge_surjective root parent height hroot hdesc⟩

lemma natCard_ne_root (root : V) :
    Nat.card {v : V // v ≠ root} + 1 = Nat.card V := by
  classical
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  let e : {v : V // v ≠ root} ≃ ↥(({root} : Finset V)ᶜ) :=
    { toFun := fun v ↦ ⟨v, Finset.mem_compl.mpr (by
        simpa only [Finset.mem_singleton] using v.2)⟩
      invFun := fun v ↦ ⟨v, by
        have hv := Finset.mem_compl.mp v.2
        simpa only [Finset.mem_singleton] using hv⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  rw [Fintype.card_congr e, Fintype.card_coe]
  rw [Finset.card_compl, Finset.card_singleton]
  letI : Nonempty V := ⟨root⟩
  exact Nat.sub_add_cancel Fintype.card_pos

lemma parentGraph_isTree
    (hroot : parent root = root)
    (hdesc : ∀ v, v ≠ root → height (parent v) < height v) :
    (parentGraph root parent).IsTree := by
  rw [isTree_iff_connected_and_card]
  refine ⟨parentGraph_connected root parent height hroot hdesc, ?_⟩
  rw [Nat.card_congr (parentEdgeEquiv root parent height hroot hdesc).symm]
  exact natCard_ne_root root

lemma parentGraph_neighborFinset_terminal
    (hroot : parent root = root)
    (hdesc : ∀ v, v ≠ root → height (parent v) < height v)
    {v : V} (hv : v ≠ root)
    (hterminal : ∀ w, w ≠ root → parent w ≠ v) :
    (parentGraph root parent).neighborFinset v = {parent v} := by
  ext w
  simp only [mem_neighborFinset, Finset.mem_singleton]
  constructor
  · rw [parentGraph_adj]
    rintro ⟨_, h | h⟩
    · exact h.2.symm
    · exact False.elim (hterminal w h.1 h.2)
  · rintro rfl
    exact parentGraph_adj_parent root parent height hroot hdesc hv

lemma parentGraph_adj_height_step
    (hstep : ∀ v, v ≠ root → height (parent v) + 1 = height v)
    {v w : V} (hadj : (parentGraph root parent).Adj v w) :
    height v + 1 = height w ∨ height w + 1 = height v := by
  rw [parentGraph_adj] at hadj
  rcases hadj.2 with h | h
  · right
    simpa [h.2] using hstep v h.1
  · left
    simpa [h.2] using hstep w h.1

lemma parentGraph_walk_height_le
    (hstep : ∀ v, v ≠ root → height (parent v) + 1 = height v)
    {v w : V} (p : (parentGraph root parent).Walk v w) :
    height w ≤ height v + p.length := by
  induction p with
  | nil => simp
  | @cons u v w huv p ih =>
      have hs := parentGraph_adj_height_step root parent height hstep huv
      simp only [Walk.length_cons]
      omega

end ParentGraph

/-! ## The Narins--Pokrovskiy--Szabó tree -/

/-- Endpoints of the spine receive two binary-tree attachments and all
other spine vertices receive one. -/
def attachmentCount (m : ℕ) (i : Fin (m + 2)) : ℕ :=
  if i.val = 0 ∨ i.val + 1 = m + 2 then 2 else 1

lemma attachmentCount_pos (m : ℕ) (i : Fin (m + 2)) :
    0 < attachmentCount m i := by
  simp only [attachmentCount]
  split <;> omega

/-- A level-l node is represented by its l left/right choices. -/
abbrev BinaryNode (h : ℕ) := Σ l : Fin h, Fin l.val → Bool

/-- A binary attachment records its spine anchor, copy number, and node. -/
abbrev ArmNode (m : ℕ) :=
  Σ i : Fin (m + 2),
    Fin (attachmentCount m i) × BinaryNode (avoidingValue i.val)

/-- Vertices of the NPS tree. -/
abbrev TreeVertex (m : ℕ) := Fin (m + 2) ⊕ ArmNode m

instance (m : ℕ) : Fintype (TreeVertex m) := inferInstance
instance (m : ℕ) : DecidableEq (TreeVertex m) := inferInstance

def treeRoot (m : ℕ) : TreeVertex m :=
  Sum.inl ⟨0, by omega⟩

/-- Rank measured from the first spine vertex. -/
def treeHeight {m : ℕ} : TreeVertex m → ℕ
  | Sum.inl i => i.val
  | Sum.inr ⟨i, _, ⟨l, _⟩⟩ => i.val + l.val + 1

/-- The rooted parent map; a positive-level word loses its final bit. -/
def treeParent {m : ℕ} : TreeVertex m → TreeVertex m
  | Sum.inl i =>
      if hi : i.val = 0 then Sum.inl i
      else Sum.inl ⟨i.val - 1, by omega⟩
  | Sum.inr ⟨i, c, ⟨l, bits⟩⟩ =>
      if hl : l.val = 0 then Sum.inl i
      else Sum.inr ⟨i, c, ⟨⟨l.val - 1, by omega⟩,
        fun j ↦ bits ⟨j.val,
          lt_trans j.isLt
            (Nat.sub_lt (Nat.zero_lt_of_ne_zero hl) (by omega))⟩⟩⟩

@[simp] lemma treeHeight_root (m : ℕ) :
    treeHeight (treeRoot m) = 0 := rfl

@[simp] lemma treeParent_root (m : ℕ) :
    treeParent (treeRoot m) = treeRoot m := by
  simp [treeParent, treeRoot]

lemma treeHeight_parent_add_one {m : ℕ} (v : TreeVertex m)
    (hv : v ≠ treeRoot m) :
    treeHeight (treeParent v) + 1 = treeHeight v := by
  rcases v with i | a
  · have hi : i.val ≠ 0 := by
      intro hi
      apply hv
      unfold treeRoot
      exact congrArg Sum.inl (Fin.ext hi)
    simp [treeParent, treeHeight, hi]
    omega
  · rcases a with ⟨i, c, ⟨l, bits⟩⟩
    by_cases hl : l.val = 0
    · simp [treeParent, treeHeight, hl]
    · simp [treeParent, treeHeight, hl]
      omega

lemma treeHeight_parent_lt {m : ℕ} (v : TreeVertex m)
    (hv : v ≠ treeRoot m) :
    treeHeight (treeParent v) < treeHeight v := by
  rw [← treeHeight_parent_add_one v hv]
  omega

def treeGraph (m : ℕ) : SimpleGraph (TreeVertex m) :=
  parentGraph (treeRoot m) treeParent

@[simp] lemma treeGraph_adj {m : ℕ} (v w : TreeVertex m) :
    (treeGraph m).Adj v w ↔
      v ≠ w ∧ ((v ≠ treeRoot m ∧ treeParent v = w) ∨
        (w ≠ treeRoot m ∧ treeParent w = v)) :=
  Iff.rfl

theorem treeGraph_isTree (m : ℕ) : (treeGraph m).IsTree :=
  parentGraph_isTree (treeRoot m) treeParent treeHeight
    (treeParent_root m) treeHeight_parent_lt

def treeAnchor {m : ℕ} : TreeVertex m → Fin (m + 2)
  | Sum.inl i => i
  | Sum.inr ⟨i, _⟩ => i

@[simp] lemma treeAnchor_parent_arm {m : ℕ} (a : ArmNode m) :
    treeAnchor (treeParent (Sum.inr a : TreeVertex m)) = a.1 := by
  rcases a with ⟨i, c, ⟨l, bits⟩⟩
  by_cases hl : l.val = 0
  · simp [treeParent, treeAnchor, hl]
  · simp [treeParent, treeAnchor, hl]

/-- Attached vertices on the final level are exactly the intended leaves. -/
def IsArmLeaf {m : ℕ} : TreeVertex m → Prop
  | Sum.inl _ => False
  | Sum.inr ⟨i, _, ⟨l, _⟩⟩ =>
      l.val + 1 = avoidingValue i.val

/-- The two children of a nonfinal binary-tree node. -/
def armChild {m : ℕ} (i : Fin (m + 2))
    (c : Fin (attachmentCount m i))
    (l : Fin (avoidingValue i.val)) (bits : Fin l.val → Bool)
    (hnlast : l.val + 1 < avoidingValue i.val) (b : Bool) :
    TreeVertex m :=
  Sum.inr ⟨i, c, ⟨⟨l.val + 1, hnlast⟩, Fin.snoc bits b⟩⟩

@[simp] lemma treeParent_armChild {m : ℕ} (i : Fin (m + 2))
    (c : Fin (attachmentCount m i))
    (l : Fin (avoidingValue i.val)) (bits : Fin l.val → Bool)
    (hnlast : l.val + 1 < avoidingValue i.val) (b : Bool) :
    treeParent (armChild i c l bits hnlast b) =
      Sum.inr ⟨i, c, ⟨l, bits⟩⟩ := by
  simp [armChild, treeParent]
  funext j
  have hj :
      (⟨j.val, by omega⟩ : Fin (l.val + 1)) = j.castSucc :=
    Fin.ext rfl
  rw [hj, Fin.snoc_castSucc]

instance {m : ℕ} : DecidablePred (@IsArmLeaf m) := fun v ↦ by
  rcases v with i | ⟨i, c, l, bits⟩ <;>
    simp only [IsArmLeaf] <;> infer_instance

lemma isArmLeaf_ne_root {m : ℕ} {v : TreeVertex m}
    (hv : IsArmLeaf v) : v ≠ treeRoot m := by
  rcases v with i | a
  · simp [IsArmLeaf] at hv
  · simp [treeRoot]

lemma isArmLeaf_has_no_child {m : ℕ} {v : TreeVertex m}
    (hv : IsArmLeaf v) :
    ∀ w : TreeVertex m, w ≠ treeRoot m → treeParent w ≠ v := by
  rcases v with i | a
  · simp [IsArmLeaf] at hv
  · rcases a with ⟨i, c, ⟨l, bits⟩⟩
    change l.val + 1 = avoidingValue i.val at hv
    intro w hw heq
    rcases w with j | b
    · simp only [treeParent] at heq
      split at heq <;> simp at heq
    · rcases b with ⟨j, d, ⟨k, choices⟩⟩
      have hanchor : j = i := by
        calc
          j = treeAnchor (treeParent
              (Sum.inr ⟨j, d, ⟨k, choices⟩⟩ : TreeVertex m)) :=
            (treeAnchor_parent_arm ⟨j, d, ⟨k, choices⟩⟩).symm
          _ = treeAnchor
              (Sum.inr ⟨i, c, ⟨l, bits⟩⟩ : TreeVertex m) :=
            congrArg treeAnchor heq
          _ = i := rfl
      have hheight := treeHeight_parent_add_one
        (Sum.inr ⟨j, d, ⟨k, choices⟩⟩ : TreeVertex m) hw
      rw [heq] at hheight
      simp only [treeHeight] at hheight
      have hij : j.val = i.val := congrArg Fin.val hanchor
      have hk := k.isLt
      have hv' : l.val + 1 = avoidingValue j.val := by
        rw [hij]
        exact hv
      omega

lemma treeGraph_neighborFinset_leaf {m : ℕ} {v : TreeVertex m}
    (hv : IsArmLeaf v) :
    (treeGraph m).neighborFinset v = {treeParent v} :=
  parentGraph_neighborFinset_terminal (treeRoot m) treeParent treeHeight
    (treeParent_root m) treeHeight_parent_lt (isArmLeaf_ne_root hv)
    (isArmLeaf_has_no_child hv)

lemma treeGraph_degree_leaf {m : ℕ} {v : TreeVertex m}
    (hv : IsArmLeaf v) :
    (treeGraph m).degree v = 1 := by
  rw [← card_neighborFinset_eq_degree, treeGraph_neighborFinset_leaf hv]
  simp

lemma isArmLeaf_height_mod_two {m : ℕ} {v : TreeVertex m}
    (hv : IsArmLeaf v) :
    treeHeight v % 2 = 1 := by
  rcases v with i | ⟨i, c, ⟨l, bits⟩⟩
  · simp [IsArmLeaf] at hv
  · change l.val + 1 = avoidingValue i.val at hv
    simp only [treeHeight]
    have hp := avoidingValue_parity i.val
    omega

lemma treeVertex_card_lower_bound (m : ℕ) :
    m + 2 ≤ Fintype.card (TreeVertex m) := by
  change m + 2 ≤ Fintype.card (Fin (m + 2) ⊕ ArmNode m)
  rw [Fintype.card_sum, Fintype.card_fin]
  omega

lemma augmentedTreeVertex_card_lower_bound (m : ℕ) :
    m + 4 ≤ Fintype.card (TreeVertex m ⊕ Fin 2) := by
  rw [Fintype.card_sum, Fintype.card_fin]
  exact Nat.add_le_add_right (treeVertex_card_lower_bound m) 2

lemma augmentedTreeVertex_card_ge (N : ℕ) :
    N ≤ Fintype.card (TreeVertex N ⊕ Fin 2) :=
  le_trans (by omega) (augmentedTreeVertex_card_lower_bound N)

lemma binaryNode_card (h : ℕ) :
    Fintype.card (BinaryNode h) = 2 ^ h - 1 := by
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fun, Fintype.card_fin, Fintype.card_bool]
  rw [Fin.sum_univ_eq_sum_range]
  induction h with
  | zero => simp
  | succ h ih =>
      rw [Finset.sum_range_succ, ih, pow_succ]
      have hpow : 0 < 2 ^ h := pow_pos (by omega) h
      omega

lemma attachmentCount_sum (m : ℕ) :
    ∑ i : Fin (m + 2), attachmentCount m i = m + 4 := by
  let first : Fin (m + 2) := ⟨0, by omega⟩
  let last : Fin (m + 2) := ⟨m + 1, by omega⟩
  let endpoints := Finset.univ.filter fun i : Fin (m + 2) ↦
    i.val = 0 ∨ i.val + 1 = m + 2
  have hendpoints : endpoints = {first, last} := by
    ext i
    simp only [endpoints, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro (hi | hi)
      · left
        apply Fin.ext
        simpa [first] using hi
      · right
        apply Fin.ext
        simp only [last]
        omega
    · rintro (rfl | rfl)
      · left
        simp [first]
      · right
        simp [last]
  have hne : first ≠ last := by
    intro h
    have hv := congrArg Fin.val h
    simp only [first, last] at hv
    omega
  have hindicator :
      (∑ i : Fin (m + 2),
        if i.val = 0 ∨ i.val + 1 = m + 2 then 1 else 0) = 2 := by
    calc
      (∑ i : Fin (m + 2),
        if i.val = 0 ∨ i.val + 1 = m + 2 then 1 else 0) =
          endpoints.card := by simp [endpoints]
      _ = ({first, last} : Finset (Fin (m + 2))).card := by
        rw [hendpoints]
      _ = 2 := by simp [hne]
  calc
    (∑ i : Fin (m + 2), attachmentCount m i) =
        ∑ i : Fin (m + 2),
          (1 + if i.val = 0 ∨ i.val + 1 = m + 2 then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro i _
      simp only [attachmentCount]
      split <;> simp_all
    _ = (m + 2) + 2 := by
      rw [Finset.sum_add_distrib, hindicator]
      simp
    _ = m + 4 := by omega

abbrev ArmLeafCode (m : ℕ) :=
  Σ i : Fin (m + 2),
    Fin (attachmentCount m i) ×
      (Fin (avoidingValue i.val - 1) → Bool)

def lastArmLevel {m : ℕ} (i : Fin (m + 2)) :
    Fin (avoidingValue i.val) :=
  ⟨avoidingValue i.val - 1, by
    have hi := avoidingValue_pos i.val
    omega⟩

def armLeafCodeVertex {m : ℕ} (x : ArmLeafCode m) :
    TreeVertex m :=
  Sum.inr ⟨x.1, x.2.1, ⟨lastArmLevel x.1, x.2.2⟩⟩

lemma armLeafCodeVertex_injective {m : ℕ} :
    Function.Injective (@armLeafCodeVertex m) := by
  rintro ⟨i, c, bits⟩ ⟨j, d, choices⟩ h
  simp only [armLeafCodeVertex, Sum.inr.injEq] at h
  cases h
  rfl

def armLeafCodeEmbedding (m : ℕ) :
    ArmLeafCode m ↪ TreeVertex m :=
  ⟨armLeafCodeVertex, armLeafCodeVertex_injective⟩

def armLeafFinset (m : ℕ) : Finset (TreeVertex m) :=
  Finset.univ.map (armLeafCodeEmbedding m)

lemma mem_armLeafFinset_iff {m : ℕ} (v : TreeVertex m) :
    v ∈ armLeafFinset m ↔ IsArmLeaf v := by
  constructor
  · rw [armLeafFinset, Finset.mem_map]
    rintro ⟨x, _, rfl⟩
    rcases x with ⟨i, c, bits⟩
    change (lastArmLevel i).val + 1 = avoidingValue i.val
    simp only [lastArmLevel]
    exact Nat.sub_add_cancel (avoidingValue_pos i.val)
  · intro hv
    rcases v with i | ⟨i, c, ⟨l, bits⟩⟩
    · simp [IsArmLeaf] at hv
    · change l.val + 1 = avoidingValue i.val at hv
      have hlval : l.val = avoidingValue i.val - 1 := by omega
      have hl : l = lastArmLevel i := Fin.ext hlval
      subst l
      rw [armLeafFinset, Finset.mem_map]
      exact ⟨⟨i, c, bits⟩, Finset.mem_univ _, rfl⟩

@[simp] lemma armLeafFinset_card (m : ℕ) :
    (armLeafFinset m).card =
      ∑ i : Fin (m + 2),
        attachmentCount m i * 2 ^ (avoidingValue i.val - 1) := by
  rw [armLeafFinset, Finset.card_map, Finset.card_univ]
  simp only [ArmLeafCode, Fintype.card_sigma, Fintype.card_prod,
    Fintype.card_fin, Fintype.card_fun, Fintype.card_bool]

lemma armLeafFinset_eq_filter (m : ℕ) :
    armLeafFinset m = Finset.univ.filter IsArmLeaf := by
  ext v
  simp only [mem_armLeafFinset_iff, Finset.mem_filter,
    Finset.mem_univ, true_and]

lemma armNode_card (m : ℕ) :
    Fintype.card (ArmNode m) =
      ∑ i : Fin (m + 2),
        attachmentCount m i * (2 ^ avoidingValue i.val - 1) := by
  rw [Fintype.card_sigma]
  apply Finset.sum_congr rfl
  intro i _
  rw [Fintype.card_prod, Fintype.card_fin, binaryNode_card]

lemma two_mul_pow_pred (h : ℕ) (hh : 0 < h) :
    2 * 2 ^ (h - 1) = (2 ^ h - 1) + 1 := by
  have hsplit : h - 1 + 1 = h := Nat.sub_add_cancel hh
  have hpow : 0 < 2 ^ (h - 1) := pow_pos (by omega) _
  have hpowEq : 2 ^ h = 2 * 2 ^ (h - 1) := by
    calc
      2 ^ h = 2 ^ (h - 1 + 1) := by rw [hsplit]
      _ = 2 ^ (h - 1) * 2 := pow_succ _ _
      _ = 2 * 2 ^ (h - 1) := by omega
  rw [hpowEq]
  omega

lemma two_mul_armLeafFinset_card_aux (m : ℕ) :
    2 * (armLeafFinset m).card =
      Fintype.card (ArmNode m) +
        ∑ i : Fin (m + 2), attachmentCount m i := by
  rw [armLeafFinset_card, armNode_card, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have hp :=
    two_mul_pow_pred (avoidingValue i.val) (avoidingValue_pos i.val)
  calc
    2 * (attachmentCount m i * 2 ^ (avoidingValue i.val - 1)) =
        attachmentCount m i *
          (2 * 2 ^ (avoidingValue i.val - 1)) := by
      simp only [mul_left_comm]
    _ = attachmentCount m i *
        ((2 ^ avoidingValue i.val - 1) + 1) := by rw [hp]
    _ = attachmentCount m i * (2 ^ avoidingValue i.val - 1) +
        attachmentCount m i := by
      rw [Nat.mul_add, Nat.mul_one]

theorem two_mul_armLeafFinset_card (m : ℕ) :
    2 * (armLeafFinset m).card =
      Fintype.card (TreeVertex m) + 2 := by
  rw [two_mul_armLeafFinset_card_aux, attachmentCount_sum]
  change Fintype.card (ArmNode m) + (m + 4) =
    Fintype.card (Fin (m + 2) ⊕ ArmNode m) + 2
  rw [Fintype.card_sum, Fintype.card_fin]
  omega

lemma treeGraph_dist_anchor_arm_le {m : ℕ} (i : Fin (m + 2))
    (c : Fin (attachmentCount m i))
    (l : Fin (avoidingValue i.val)) (bits : Fin l.val → Bool) :
    (treeGraph m).dist (Sum.inl i)
      (Sum.inr ⟨i, c, ⟨l, bits⟩⟩ : TreeVertex m) ≤ l.val + 1 := by
  induction hlv : l.val using Nat.strong_induction_on generalizing l bits with
  | h n ih =>
      let node : TreeVertex m := Sum.inr ⟨i, c, ⟨l, bits⟩⟩
      have hnode : node ≠ treeRoot m := by simp [node, treeRoot]
      by_cases hl : l.val = 0
      · have hp : treeParent node = Sum.inl i := by
          simp [node, treeParent, hl]
        have hadj : (treeGraph m).Adj (Sum.inl i) node := by
          have ha :=
            parentGraph_adj_parent (treeRoot m) treeParent treeHeight
              (treeParent_root m) treeHeight_parent_lt hnode
          rw [hp] at ha
          exact ha.symm
        have hd : (treeGraph m).dist (Sum.inl i) node = 1 :=
          dist_eq_one_iff_adj.mpr hadj
        rw [hd]
        omega
      · let lp : Fin (avoidingValue i.val) := ⟨l.val - 1, by omega⟩
        let pbits : Fin lp.val → Bool := fun j ↦
          bits ⟨j.val, lt_trans j.isLt
            (Nat.sub_lt (Nat.zero_lt_of_ne_zero hl) (by omega))⟩
        let pnode : TreeVertex m :=
          Sum.inr ⟨i, c, ⟨lp, pbits⟩⟩
        have hp : treeParent node = pnode := by
          simp [node, pnode, lp, pbits, treeParent, hl]
        have hpn : pnode ≠ treeRoot m := by simp [pnode, treeRoot]
        have hadj : (treeGraph m).Adj pnode node := by
          have ha :=
            parentGraph_adj_parent (treeRoot m) treeParent treeHeight
              (treeParent_root m) treeHeight_parent_lt hnode
          rw [hp] at ha
          exact ha.symm
        have hdist : (treeGraph m).dist pnode node = 1 :=
          dist_eq_one_iff_adj.mpr hadj
        have hip := ih lp.val (by simp [lp]; omega) lp pbits rfl
        have htri := (treeGraph_isTree m).connected.dist_triangle
          (u := Sum.inl i) (v := pnode) (w := node)
        rw [hdist] at htri
        dsimp [node] at htri
        change (treeGraph m).dist (Sum.inl i) pnode ≤ lp.val + 1 at hip
        simp only [lp] at hip
        omega

theorem treeGraph_dist_anchor_arm {m : ℕ} (i : Fin (m + 2))
    (c : Fin (attachmentCount m i))
    (l : Fin (avoidingValue i.val)) (bits : Fin l.val → Bool) :
    (treeGraph m).dist (Sum.inl i)
      (Sum.inr ⟨i, c, ⟨l, bits⟩⟩ : TreeVertex m) = l.val + 1 := by
  apply Nat.le_antisymm (treeGraph_dist_anchor_arm_le i c l bits)
  let node : TreeVertex m := Sum.inr ⟨i, c, ⟨l, bits⟩⟩
  obtain ⟨p, hp⟩ :=
    (treeGraph_isTree m).connected.exists_walk_length_eq_dist
      (Sum.inl i) node
  have hwalk :=
    parentGraph_walk_height_le (treeRoot m) treeParent treeHeight
      treeHeight_parent_add_one p
  change i.val + l.val + 1 ≤ i.val + p.length at hwalk
  dsimp [node] at hp
  rw [hp] at hwalk
  change l.val + 1 ≤
    (treeGraph m).dist (Sum.inl i)
      (Sum.inr ⟨i, c, ⟨l, bits⟩⟩ : TreeVertex m)
  omega

lemma treeGraph_dist_spine_le {m : ℕ} (i j : Fin (m + 2))
    (hij : i.val ≤ j.val) :
    (treeGraph m).dist (Sum.inl i) (Sum.inl j) ≤ j.val - i.val := by
  induction hd : j.val - i.val using Nat.strong_induction_on generalizing j with
  | h n ih =>
      by_cases hji : j.val = i.val
      · have hji' : j = i := Fin.ext hji
        subst j
        simp
      · let jp : Fin (m + 2) := ⟨j.val - 1, by omega⟩
        have hijp : i.val ≤ jp.val := by simp [jp]; omega
        have hsmall : jp.val - i.val < n := by simp [jp]; omega
        have hip := ih (jp.val - i.val) hsmall jp hijp rfl
        have hj0 : j.val ≠ 0 := by omega
        have hp :
            treeParent (Sum.inl j : TreeVertex m) = Sum.inl jp := by
          simp [treeParent, jp, hj0]
        have hjroot : (Sum.inl j : TreeVertex m) ≠ treeRoot m := by
          intro hj
          have hheight := congrArg treeHeight hj
          change j.val = 0 at hheight
          exact hj0 hheight
        have hadj : (treeGraph m).Adj (Sum.inl jp) (Sum.inl j) := by
          have ha :=
            parentGraph_adj_parent (treeRoot m) treeParent treeHeight
              (treeParent_root m) treeHeight_parent_lt hjroot
          rw [hp] at ha
          exact ha.symm
        have hdist :
            (treeGraph m).dist (Sum.inl jp) (Sum.inl j) = 1 :=
          dist_eq_one_iff_adj.mpr hadj
        have htri := (treeGraph_isTree m).connected.dist_triangle
          (u := Sum.inl i) (v := Sum.inl jp) (w := Sum.inl j)
        rw [hdist] at htri
        omega

theorem treeGraph_dist_spine {m : ℕ} (i j : Fin (m + 2))
    (hij : i.val ≤ j.val) :
    (treeGraph m).dist (Sum.inl i) (Sum.inl j) =
      j.val - i.val := by
  apply Nat.le_antisymm (treeGraph_dist_spine_le i j hij)
  obtain ⟨p, hp⟩ :=
    (treeGraph_isTree m).connected.exists_walk_length_eq_dist
      (Sum.inl i) (Sum.inl j)
  have hwalk :=
    parentGraph_walk_height_le (treeRoot m) treeParent treeHeight
      treeHeight_parent_add_one p
  simp only [treeHeight] at hwalk
  have hwalk' : j.val ≤ i.val + p.length := by
    simpa only [treeGraph] using hwalk
  calc
    j.val - i.val ≤ p.length := by
      rw [Nat.sub_le_iff_le_add]
      simpa [Nat.add_comm] using hwalk'
    _ = (treeGraph m).dist (Sum.inl i) (Sum.inl j) := hp

/-- A one-Lipschitz potential certifying the full cost of crossing from an
arm at the cut to an arm on its right. -/
def cutPotential {m : ℕ} (cut : Fin (m + 2)) :
    TreeVertex m → ℕ
  | Sum.inl i => 10 + i.val
  | Sum.inr ⟨i, _, ⟨l, _⟩⟩ =>
      if i.val ≤ cut.val then 10 + i.val - (l.val + 1)
      else 10 + i.val + (l.val + 1)

lemma cutPotential_parent_step {m : ℕ} (cut : Fin (m + 2))
    (v : TreeVertex m) (hv : v ≠ treeRoot m) :
    cutPotential cut (treeParent v) + 1 = cutPotential cut v ∨
      cutPotential cut v + 1 = cutPotential cut (treeParent v) := by
  rcases v with i | a
  · have hi : i.val ≠ 0 := by
      intro hi
      apply hv
      unfold treeRoot
      exact congrArg Sum.inl (Fin.ext hi)
    simp only [treeParent, hi, dite_false, cutPotential]
    left
    omega
  · rcases a with ⟨i, c, ⟨l, bits⟩⟩
    have hbound := avoidingValue_le_nine i.val
    have hlbound := l.isLt
    by_cases hl : l.val = 0
    · by_cases hic : i.val ≤ cut.val
      · simp [treeParent, cutPotential, hl, hic]
        omega
      · simp [treeParent, cutPotential, hl, hic]
    · by_cases hic : i.val ≤ cut.val
      · simp [treeParent, cutPotential, hl, hic]
        omega
      · simp [treeParent, cutPotential, hl, hic]
        omega

lemma treeGraph_adj_cutPotential_step {m : ℕ} (cut : Fin (m + 2))
    {v w : TreeVertex m} (hadj : (treeGraph m).Adj v w) :
    cutPotential cut v + 1 = cutPotential cut w ∨
      cutPotential cut w + 1 = cutPotential cut v := by
  rw [treeGraph_adj] at hadj
  rcases hadj.2 with h | h
  · have hs := cutPotential_parent_step cut v h.1
    rcases hs with hs | hs
    · right
      simpa [h.2] using hs
    · left
      simpa [h.2] using hs
  · have hs := cutPotential_parent_step cut w h.1
    rcases hs with hs | hs
    · left
      simpa [h.2] using hs
    · right
      simpa [h.2] using hs

lemma treeGraph_walk_cutPotential_le {m : ℕ} (cut : Fin (m + 2))
    {v w : TreeVertex m} (p : (treeGraph m).Walk v w) :
    cutPotential cut w ≤ cutPotential cut v + p.length := by
  induction p with
  | nil => simp
  | @cons u v w huv p ih =>
      have hs := treeGraph_adj_cutPotential_step cut huv
      simp only [Walk.length_cons]
      omega

theorem treeGraph_dist_arms_distinct {m : ℕ}
    (i j : Fin (m + 2)) (hij : i.val < j.val)
    (ci : Fin (attachmentCount m i))
    (cj : Fin (attachmentCount m j))
    (li : Fin (avoidingValue i.val))
    (lj : Fin (avoidingValue j.val))
    (bi : Fin li.val → Bool) (bj : Fin lj.val → Bool) :
    (treeGraph m).dist
      (Sum.inr ⟨i, ci, ⟨li, bi⟩⟩ : TreeVertex m)
      (Sum.inr ⟨j, cj, ⟨lj, bj⟩⟩ : TreeVertex m) =
        (li.val + 1) + (j.val - i.val) + (lj.val + 1) := by
  let vi : TreeVertex m := Sum.inr ⟨i, ci, ⟨li, bi⟩⟩
  let vj : TreeVertex m := Sum.inr ⟨j, cj, ⟨lj, bj⟩⟩
  apply Nat.le_antisymm
  · have htri₁ := (treeGraph_isTree m).connected.dist_triangle
        (u := vi) (v := Sum.inl i) (w := vj)
    have htri₂ := (treeGraph_isTree m).connected.dist_triangle
        (u := Sum.inl i) (v := Sum.inl j) (w := vj)
    have hai := treeGraph_dist_anchor_arm i ci li bi
    have haj := treeGraph_dist_anchor_arm j cj lj bj
    have hs := treeGraph_dist_spine i j hij.le
    rw [dist_comm] at hai
    dsimp [vi, vj] at htri₁ htri₂ ⊢
    rw [hai] at htri₁
    rw [haj, hs] at htri₂
    omega
  · obtain ⟨p, hp⟩ :=
      (treeGraph_isTree m).connected.exists_walk_length_eq_dist vi vj
    have hpot := treeGraph_walk_cutPotential_le i p
    have hiBound := avoidingValue_le_nine i.val
    have hli := li.isLt
    have hjnot : ¬j.val ≤ i.val := by omega
    dsimp [vi, vj, cutPotential] at hpot hp ⊢
    simp only [le_refl, if_true, hjnot, if_false] at hpot
    calc
      (li.val + 1) + (j.val - i.val) + (lj.val + 1) ≤
          p.length := by omega
      _ = (treeGraph m).dist
          (Sum.inr ⟨i, ci, ⟨li, bi⟩⟩ : TreeVertex m)
          (Sum.inr ⟨j, cj, ⟨lj, bj⟩⟩ : TreeVertex m) := hp

lemma treeGraph_isPath_length_eq_dist {m : ℕ}
    {v w : TreeVertex m} {q : (treeGraph m).Walk v w}
    (hq : q.IsPath) :
    q.length = (treeGraph m).dist v w := by
  obtain ⟨p, hp, hplen⟩ :=
    (treeGraph_isTree m).connected.exists_path_of_dist v w
  have hpq : p = q :=
    (treeGraph_isTree m).existsUnique_path v w |>.unique hp hq
  rw [← hpq]
  exact hplen

theorem treeGraph_no_leaf_path_twenty
    (havoid : ∀ {i j : ℕ}, i < j →
      avoidingValue i + avoidingValue j + (j - i) ≠ 20)
    {m : ℕ} {v w : TreeVertex m}
    (hv : IsArmLeaf v) (hw : IsArmLeaf w)
    (q : (treeGraph m).Walk v w) (hq : q.IsPath) :
    q.length ≠ 20 := by
  have hlen := treeGraph_isPath_length_eq_dist hq
  rcases v with i₀ | ⟨i, ci, ⟨li, bi⟩⟩
  · simp [IsArmLeaf] at hv
  · rcases w with j₀ | ⟨j, cj, ⟨lj, bj⟩⟩
    · simp [IsArmLeaf] at hw
    · change li.val + 1 = avoidingValue i.val at hv
      change lj.val + 1 = avoidingValue j.val at hw
      intro hq20
      rw [hlen] at hq20
      by_cases hij : i.val = j.val
      · have hijFin : i = j := Fin.ext hij
        subst j
        have htri := (treeGraph_isTree m).connected.dist_triangle
          (u := (Sum.inr ⟨i, ci, ⟨li, bi⟩⟩ : TreeVertex m))
          (v := Sum.inl i)
          (w := (Sum.inr ⟨i, cj, ⟨lj, bj⟩⟩ : TreeVertex m))
        have hdi := treeGraph_dist_anchor_arm i ci li bi
        have hdj := treeGraph_dist_anchor_arm i cj lj bj
        rw [dist_comm] at hdi
        rw [hdi, hdj] at htri
        have hnine := avoidingValue_le_nine i.val
        omega
      · rcases lt_or_gt_of_ne hij with hijlt | hjilt
        · have hd :=
            treeGraph_dist_arms_distinct i j hijlt ci cj li lj bi bj
          rw [hd] at hq20
          apply havoid hijlt
          omega
        · have hd :=
            treeGraph_dist_arms_distinct j i hjilt cj ci lj li bj bi
          rw [dist_comm] at hq20
          rw [hd] at hq20
          apply havoid hjilt
          omega

theorem treeGraph_no_leaf_path_length_20
    {m : ℕ} {v w : TreeVertex m}
    (hv : IsArmLeaf v) (hw : IsArmLeaf w)
    (q : (treeGraph m).Walk v w) (hq : q.IsPath) :
    q.length ≠ 20 :=
  treeGraph_no_leaf_path_twenty
    (fun {i j} hij ↦ by
      have h := avoidingValue_avoid20_of_lt hij
      rw [Nat.dist_eq_sub_of_le hij.le] at h
      exact h)
    hv hw q hq

/-- The parity coloring of the rooted NPS tree. -/
def treeColor {m : ℕ} (v : TreeVertex m) : Fin 2 :=
  ⟨treeHeight v % 2, Nat.mod_lt _ (by omega)⟩

lemma treeColor_proper {m : ℕ} {v w : TreeVertex m}
    (hvw : (treeGraph m).Adj v w) :
    treeColor v ≠ treeColor w := by
  have hs :=
    parentGraph_adj_height_step (treeRoot m) treeParent treeHeight
      treeHeight_parent_add_one hvw
  intro heq
  have hval := congrArg Fin.val heq
  simp only [treeColor] at hval
  rcases hs with hs | hs <;> omega

lemma treeColor_eq_one_of_isArmLeaf {m : ℕ} {v : TreeVertex m}
    (hv : IsArmLeaf v) :
    treeColor v = 1 := by
  apply Fin.ext
  simpa only [treeColor, Fin.val_one] using isArmLeaf_height_mod_two hv

lemma three_le_degree_of_three_neighbors
    {V : Type*} [Fintype V] {G : SimpleGraph V} {v a b c : V}
    (ha : G.Adj v a) (hb : G.Adj v b) (hc : G.Adj v c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    3 ≤ G.degree v := by
  rw [← card_neighborFinset_eq_degree]
  have hsub : ({a, b, c} : Finset V) ⊆ G.neighborFinset v := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · simpa using ha
    · simpa using hb
    · simpa using hc
  have hcard : ({a, b, c} : Finset V).card = 3 := by
    simp [hab, hac, hbc]
  rw [← hcard]
  exact Finset.card_le_card hsub

lemma treeGraph_degree_arm_ge_three {m : ℕ}
    (i : Fin (m + 2)) (c : Fin (attachmentCount m i))
    (l : Fin (avoidingValue i.val)) (bits : Fin l.val → Bool)
    (hnlast : l.val + 1 < avoidingValue i.val) :
    3 ≤ (treeGraph m).degree
      (Sum.inr ⟨i, c, ⟨l, bits⟩⟩ : TreeVertex m) := by
  let v : TreeVertex m := Sum.inr ⟨i, c, ⟨l, bits⟩⟩
  let p : TreeVertex m := treeParent v
  let cf : TreeVertex m := armChild i c l bits hnlast false
  let ct : TreeVertex m := armChild i c l bits hnlast true
  have hvroot : v ≠ treeRoot m := by simp [v, treeRoot]
  have hcfroot : cf ≠ treeRoot m := by simp [cf, armChild, treeRoot]
  have hctroot : ct ≠ treeRoot m := by simp [ct, armChild, treeRoot]
  have hvp : (treeGraph m).Adj v p :=
    parentGraph_adj_parent (treeRoot m) treeParent treeHeight
      (treeParent_root m) treeHeight_parent_lt hvroot
  have hvcf : (treeGraph m).Adj v cf := by
    have h :=
      parentGraph_adj_parent (treeRoot m) treeParent treeHeight
        (treeParent_root m) treeHeight_parent_lt hcfroot
    rw [show treeParent cf = v by
      simp [cf, v, treeParent_armChild]] at h
    exact h.symm
  have hvct : (treeGraph m).Adj v ct := by
    have h :=
      parentGraph_adj_parent (treeRoot m) treeParent treeHeight
        (treeParent_root m) treeHeight_parent_lt hctroot
    rw [show treeParent ct = v by
      simp [ct, v, treeParent_armChild]] at h
    exact h.symm
  have hpcf : p ≠ cf := by
    intro h
    have hpheight := treeHeight_parent_add_one v hvroot
    have heq := congrArg treeHeight h
    simp only [p, cf, v, armChild, treeHeight] at heq hpheight
    omega
  have hpct : p ≠ ct := by
    intro h
    have hpheight := treeHeight_parent_add_one v hvroot
    have heq := congrArg treeHeight h
    simp only [p, ct, v, armChild, treeHeight] at heq hpheight
    omega
  have hfc : cf ≠ ct := by
    intro h
    simp [cf, ct, armChild, Fin.snoc_inj] at h
  exact three_le_degree_of_three_neighbors hvp hvcf hvct
    hpcf hpct hfc

/-- Root node of one binary attachment. -/
def armRoot {m : ℕ} (i : Fin (m + 2))
    (c : Fin (attachmentCount m i)) : TreeVertex m :=
  Sum.inr ⟨i, c, ⟨⟨0, avoidingValue_pos i.val⟩, Fin.elim0⟩⟩

@[simp] lemma treeParent_armRoot {m : ℕ} (i : Fin (m + 2))
    (c : Fin (attachmentCount m i)) :
    treeParent (armRoot i c) = Sum.inl i := by
  simp [armRoot, treeParent]

lemma treeGraph_adj_spine_armRoot {m : ℕ} (i : Fin (m + 2))
    (c : Fin (attachmentCount m i)) :
    (treeGraph m).Adj (Sum.inl i) (armRoot i c) := by
  rw [treeGraph_adj]
  refine ⟨by simp [armRoot], Or.inr ⟨by simp [armRoot, treeRoot], ?_⟩⟩
  exact treeParent_armRoot i c

lemma treeGraph_adj_spine_succ {m : ℕ} (i : Fin (m + 2))
    (hi : i.val + 1 < m + 2) :
    (treeGraph m).Adj (Sum.inl i)
      (Sum.inl ⟨i.val + 1, hi⟩ : TreeVertex m) := by
  rw [treeGraph_adj]
  refine ⟨?_, Or.inr ⟨?_, ?_⟩⟩
  · intro h
    have := congrArg treeHeight h
    simp only [treeHeight] at this
    omega
  · intro h
    have hs : (⟨i.val + 1, hi⟩ : Fin (m + 2)) =
        ⟨0, by omega⟩ := Sum.inl.inj h
    have := congrArg Fin.val hs
    change i.val + 1 = 0 at this
    omega
  · simp [treeParent]

lemma treeGraph_adj_spine_pred {m : ℕ} (i : Fin (m + 2))
    (hi : 0 < i.val) :
    (treeGraph m).Adj (Sum.inl i)
      (Sum.inl ⟨i.val - 1, by omega⟩ : TreeVertex m) := by
  rw [treeGraph_adj]
  refine ⟨?_, Or.inl ⟨?_, ?_⟩⟩
  · intro h
    have := congrArg treeHeight h
    simp only [treeHeight] at this
    omega
  · intro h
    apply hi.ne'
    have hs : i = ⟨0, by omega⟩ := Sum.inl.inj h
    exact congrArg Fin.val hs
  · simp [treeParent, show i.val ≠ 0 by omega]

lemma treeGraph_degree_spine_ge_three {m : ℕ} (i : Fin (m + 2)) :
    3 ≤ (treeGraph m).degree (Sum.inl i : TreeVertex m) := by
  by_cases hfirst : i.val = 0
  · have hiend : i.val = 0 ∨ i.val + 1 = m + 2 := Or.inl hfirst
    have hac : attachmentCount m i = 2 := by
      rw [attachmentCount, if_pos hiend]
    let c0 : Fin (attachmentCount m i) := ⟨0, by omega⟩
    let c1 : Fin (attachmentCount m i) := ⟨1, by omega⟩
    let j : Fin (m + 2) := ⟨i.val + 1, by omega⟩
    have hj := treeGraph_adj_spine_succ i j.isLt
    have h0 := treeGraph_adj_spine_armRoot i c0
    have h1 := treeGraph_adj_spine_armRoot i c1
    apply three_le_degree_of_three_neighbors hj h0 h1
    · simp [j, armRoot]
    · simp [j, armRoot]
    · intro h
      have heq : c0 = c1 := by
        simpa [armRoot] using h
      have := congrArg Fin.val heq
      simp [c0, c1] at this
  · by_cases hlast : i.val + 1 = m + 2
    · have hiend : i.val = 0 ∨ i.val + 1 = m + 2 := Or.inr hlast
      have hac : attachmentCount m i = 2 := by
        rw [attachmentCount, if_pos hiend]
      let c0 : Fin (attachmentCount m i) := ⟨0, by omega⟩
      let c1 : Fin (attachmentCount m i) := ⟨1, by omega⟩
      let j : Fin (m + 2) := ⟨i.val - 1, by omega⟩
      have hj := treeGraph_adj_spine_pred i (by omega)
      have h0 := treeGraph_adj_spine_armRoot i c0
      have h1 := treeGraph_adj_spine_armRoot i c1
      apply three_le_degree_of_three_neighbors hj h0 h1
      · simp [j, armRoot]
      · simp [j, armRoot]
      · intro h
        have heq : c0 = c1 := by
          simpa [armRoot] using h
        have := congrArg Fin.val heq
        simp [c0, c1] at this
    · have hac : attachmentCount m i = 1 := by
        rw [attachmentCount, if_neg]
        exact fun h ↦ h.elim hfirst hlast
      let c0 : Fin (attachmentCount m i) := ⟨0, by omega⟩
      let jp : Fin (m + 2) := ⟨i.val - 1, by omega⟩
      let js : Fin (m + 2) := ⟨i.val + 1, by omega⟩
      have hp := treeGraph_adj_spine_pred i (by omega)
      have hs := treeGraph_adj_spine_succ i (by omega)
      have h0 := treeGraph_adj_spine_armRoot i c0
      apply three_le_degree_of_three_neighbors hp hs h0
      · intro h
        have heq := congrArg treeHeight h
        simp only [treeHeight] at heq
        omega
      · simp [jp, armRoot]
      · simp [js, armRoot]

/-- Every non-leaf vertex of the NPS tree has at least three neighbors. -/
lemma treeGraph_lower_degree_le {m : ℕ} (v : TreeVertex m) :
    (if IsArmLeaf v then 1 else 3) ≤ (treeGraph m).degree v := by
  by_cases hv : IsArmLeaf v
  · simp [hv, treeGraph_degree_leaf hv]
  · simp only [hv, if_false]
    rcases v with i | ⟨i, c, ⟨l, bits⟩⟩
    · exact treeGraph_degree_spine_ge_three i
    · apply treeGraph_degree_arm_ge_three i c l bits
      change ¬ l.val + 1 = avoidingValue i.val at hv
      omega

lemma treeGraph_sum_lower_degrees (m : ℕ) :
    (∑ v : TreeVertex m, if IsArmLeaf v then 1 else 3) =
      ∑ v : TreeVertex m, (treeGraph m).degree v := by
  let leaves := Finset.univ.filter (@IsArmLeaf m)
  let nonleaves := Finset.univ.filter (fun v : TreeVertex m ↦ ¬ IsArmLeaf v)
  have hpartition : leaves.card + nonleaves.card =
      Fintype.card (TreeVertex m) := by
    simpa only [leaves, nonleaves, Finset.card_univ] using
      (Finset.card_filter_add_card_filter_not
        (s := (Finset.univ : Finset (TreeVertex m))) IsArmLeaf)
  have hleaves : 2 * leaves.card = Fintype.card (TreeVertex m) + 2 := by
    dsimp [leaves]
    rw [← armLeafFinset_eq_filter]
    exact two_mul_armLeafFinset_card m
  have hlower :
      (∑ v : TreeVertex m, if IsArmLeaf v then 1 else 3) =
        leaves.card + 3 * nonleaves.card := by
    have hsumLeaf :
        (∑ v : TreeVertex m, if IsArmLeaf v then 1 else 0) =
          leaves.card := by
      change (∑ v ∈ (Finset.univ : Finset (TreeVertex m)),
        if IsArmLeaf v then 1 else 0) =
          (Finset.univ.filter IsArmLeaf).card
      exact Finset.sum_boole IsArmLeaf Finset.univ
    have hsumNonleaf :
        (∑ v : TreeVertex m, if ¬ IsArmLeaf v then 1 else 0) =
          nonleaves.card := by
      change (∑ v ∈ (Finset.univ : Finset (TreeVertex m)),
        if ¬ IsArmLeaf v then 1 else 0) =
          (Finset.univ.filter (fun v : TreeVertex m ↦ ¬ IsArmLeaf v)).card
      exact Finset.sum_boole
        (fun v : TreeVertex m ↦ ¬ IsArmLeaf v) Finset.univ
    rw [Finset.sum_ite]
    simp only [Finset.sum_const, Finset.card_filter, smul_eq_mul,
      Nat.one_mul, Nat.mul_comm]
    rw [hsumLeaf, hsumNonleaf]
  have htreeEdges := (treeGraph_isTree m).card_edgeFinset
  have hhandshake := (treeGraph m).sum_degrees_eq_twice_card_edges
  have hcardpos : 0 < Fintype.card (TreeVertex m) := by
    exact lt_of_lt_of_le (by omega) (treeVertex_card_lower_bound m)
  rw [hlower]
  omega

/-- The explicit NPS tree is a 1--3 tree. -/
theorem treeGraph_degree_one_or_three (m : ℕ) (v : TreeVertex m) :
    (treeGraph m).degree v = 1 ∨ (treeGraph m).degree v = 3 := by
  have hsum := treeGraph_sum_lower_degrees m
  have hall := (Finset.sum_eq_sum_iff_of_le
    (s := Finset.univ)
    (fun w (_ : w ∈ (Finset.univ : Finset (TreeVertex m))) ↦
      treeGraph_lower_degree_le w)).mp hsum
  have hv := hall v (Finset.mem_univ v)
  by_cases hleaf : IsArmLeaf v
  · left
    simpa [hleaf] using hv.symm
  · right
    simpa [hleaf] using hv.symm

theorem treeGraph_degree_one_iff_isArmLeaf {m : ℕ} (v : TreeVertex m) :
    (treeGraph m).degree v = 1 ↔ IsArmLeaf v := by
  constructor
  · intro hv
    by_contra hn
    have hlow := treeGraph_lower_degree_le v
    simp [hn, hv] at hlow
  · exact treeGraph_degree_leaf

/-! ## The two-apex augmentation -/

/-- Add two adjacent apex vertices, both joined to every leaf of a finite
graph. -/
noncomputable def twoApexAugmentation {V : Type*} [Fintype V]
    (T : SimpleGraph V) : SimpleGraph (V ⊕ Fin 2) where
  Adj
    | .inl v, .inl w => T.Adj v w
    | .inl v, .inr _ => T.degree v = 1
    | .inr _, .inl v => T.degree v = 1
    | .inr i, .inr j => i ≠ j
  symm := ⟨by
    rintro (v | i) (w | j)
    · exact T.adj_symm
    · exact id
    · exact id
    · exact Ne.symm⟩
  loopless := ⟨by
    rintro (v | i)
    · exact T.loopless.irrefl v
    · exact fun h ↦ h rfl⟩

@[simp] lemma twoApexAugmentation_adj_inl_inl
    {V : Type*} [Fintype V] (T : SimpleGraph V) (v w : V) :
    (twoApexAugmentation T).Adj (.inl v) (.inl w) ↔ T.Adj v w :=
  Iff.rfl

@[simp] lemma twoApexAugmentation_adj_inl_inr
    {V : Type*} [Fintype V] (T : SimpleGraph V) (v : V) (i : Fin 2) :
    (twoApexAugmentation T).Adj (.inl v) (.inr i) ↔ T.degree v = 1 :=
  Iff.rfl

@[simp] lemma twoApexAugmentation_adj_inr_inl
    {V : Type*} [Fintype V] (T : SimpleGraph V) (i : Fin 2) (v : V) :
    (twoApexAugmentation T).Adj (.inr i) (.inl v) ↔ T.degree v = 1 :=
  Iff.rfl

@[simp] lemma twoApexAugmentation_adj_inr_inr
    {V : Type*} [Fintype V] (T : SimpleGraph V) (i j : Fin 2) :
    (twoApexAugmentation T).Adj (.inr i) (.inr j) ↔ i ≠ j :=
  Iff.rfl

noncomputable def neighborSetInlLeafEquiv
    {V : Type*} [Fintype V] (T : SimpleGraph V) (v : V)
    (hv : T.degree v = 1) :
    (twoApexAugmentation T).neighborSet (.inl v) ≃
      T.neighborSet v ⊕ Fin 2 where
  toFun x := match h : x.1 with
    | .inl w => .inl ⟨w, by
        have hx := x.property
        rw [h] at hx
        exact hx⟩
    | .inr i => .inr i
  invFun
    | .inl w => ⟨.inl w.1, w.2⟩
    | .inr i => ⟨.inr i, hv⟩
  left_inv := by rintro ⟨w | i, h⟩ <;> rfl
  right_inv := by rintro (w | i) <;> rfl

noncomputable def neighborSetInlNonleafEquiv
    {V : Type*} [Fintype V] (T : SimpleGraph V) (v : V)
    (hv : T.degree v ≠ 1) :
    (twoApexAugmentation T).neighborSet (.inl v) ≃ T.neighborSet v where
  toFun x := match h : x.1 with
    | .inl w => ⟨w, by
        have hx := x.property
        rw [h] at hx
        exact hx⟩
    | .inr _ => False.elim (hv (by
        have hx := x.property
        rw [h] at hx
        exact hx))
  invFun w := ⟨.inl w.1, w.2⟩
  left_inv := by
    rintro ⟨w | i, h⟩
    · rfl
    · exact False.elim (hv h)
  right_inv := by rintro w; rfl

noncomputable def neighborSetInrEquiv
    {V : Type*} [Fintype V] (T : SimpleGraph V) (i : Fin 2) :
    (twoApexAugmentation T).neighborSet (.inr i) ≃
      ({v : V // T.degree v = 1} ⊕ {j : Fin 2 // j ≠ i}) where
  toFun x := match h : x.1 with
    | .inl v => .inl ⟨v, by
        have hx := x.property
        rw [h] at hx
        exact hx⟩
    | .inr j => .inr ⟨j, Ne.symm (by
        have hx := x.property
        rw [h] at hx
        exact hx)⟩
  invFun
    | .inl v => ⟨.inl v.1, v.2⟩
    | .inr j => ⟨.inr j.1, Ne.symm j.2⟩
  left_inv := by rintro ⟨v | j, h⟩ <;> rfl
  right_inv := by rintro (v | j) <;> rfl

lemma degree_induce_le_degree {W : Type*} [Fintype W]
    (G : SimpleGraph W) (s : Set W) (v : s) :
    (G.induce s).degree v ≤ G.degree v := by
  have h := congrArg Finset.card (G.map_neighborFinset_induce v)
  rw [Finset.card_map, SimpleGraph.card_neighborFinset_eq_degree] at h
  rw [h]
  exact Finset.card_le_card Finset.inter_subset_left

lemma neighborSet_subset_of_degree_induce_eq_degree
    {W : Type*} [Fintype W] (G : SimpleGraph W) (s : Set W) (v : s)
    (hdegree : (G.induce s).degree v = G.degree v) :
    G.neighborSet v ⊆ s := by
  have hcard := congrArg Finset.card (G.map_neighborFinset_induce v)
  rw [Finset.card_map, SimpleGraph.card_neighborFinset_eq_degree,
    hdegree] at hcard
  have hcard' : #(G.neighborFinset (v : W)) ≤
      #(G.neighborFinset (v : W) ∩ s.toFinset) := by
    rw [SimpleGraph.card_neighborFinset_eq_degree]
    exact hcard.le
  have heq :
      G.neighborFinset (v : W) ∩ s.toFinset = G.neighborFinset v :=
    Finset.eq_of_subset_of_card_le Finset.inter_subset_left hcard'
  intro w hw
  have hw' : w ∈ G.neighborFinset (v : W) := by simpa using hw
  have : w ∈ G.neighborFinset (v : W) ∩ s.toFinset :=
    heq.symm ▸ hw'
  simpa using (Finset.mem_inter.mp this).2

lemma twoApexAugmentation_degree_inl
    {V : Type*} [Fintype V] (T : SimpleGraph V)
    (hdegree : ∀ v, T.degree v = 1 ∨ T.degree v = 3) (v : V) :
    (twoApexAugmentation T).degree (.inl v) = 3 := by
  rcases hdegree v with hv | hv
  · rw [← SimpleGraph.card_neighborSet_eq_degree,
      Fintype.card_congr (neighborSetInlLeafEquiv T v hv),
      Fintype.card_sum, SimpleGraph.card_neighborSet_eq_degree, hv]
    rfl
  · rw [← SimpleGraph.card_neighborSet_eq_degree,
      Fintype.card_congr (neighborSetInlNonleafEquiv T v (by omega)),
      SimpleGraph.card_neighborSet_eq_degree]
    exact hv

theorem twoApexAugmentation_minDegree_le_two
    {V : Type*} [Fintype V] (T : SimpleGraph V) (hT : T.IsTree)
    (hdegree : ∀ v, T.degree v = 1 ∨ T.degree v = 3)
    (s : Set (V ⊕ Fin 2)) (hs : s ≠ Set.univ) :
    ((twoApexAugmentation T).induce s).minDegree ≤ 2 := by
  let A := twoApexAugmentation T
  change (A.induce s).minDegree ≤ 2
  by_contra hnot
  have hmin : 3 ≤ (A.induce s).minDegree := by omega
  have hallDegree (x : s) : 3 ≤ (A.induce s).degree x :=
    hmin.trans ((A.induce s).minDegree_le_degree x)
  have hsNonempty : s.Nonempty := by
    by_contra h
    have hse : s = ∅ := Set.not_nonempty_iff_eq_empty.mp h
    subst s
    simp at hmin
  have hbase : ∃ v : V, Sum.inl v ∈ s := by
    by_contra hnone
    have hsub :
        s.toFinset ⊆ Finset.univ.image (Sum.inr : Fin 2 → V ⊕ Fin 2) := by
      intro x hx
      have hxs : x ∈ s := by simpa using hx
      cases x with
      | inl v => exact False.elim (hnone ⟨v, hxs⟩)
      | inr i => simp
    have hcard : Fintype.card s ≤ 2 := by
      have h := Finset.card_le_card hsub
      have himage :
          #(Finset.univ.image (Sum.inr : Fin 2 → V ⊕ Fin 2)) = 2 := by
        rw [Finset.card_image_of_injective]
        · simp
        · exact Sum.inr_injective
      rw [himage] at h
      simpa only [Set.toFinset_card] using h
    obtain ⟨x, hx⟩ := hsNonempty
    have hxlt : (A.induce s).degree ⟨x, hx⟩ < Fintype.card s :=
      (A.induce s).degree_lt_card_verts ⟨x, hx⟩
    have hxge := hallDegree ⟨x, hx⟩
    omega
  obtain ⟨v₀, hv₀⟩ := hbase
  have hbaseNeighborClosure (v : V) (hv : Sum.inl v ∈ s) :
      A.neighborSet (.inl v) ⊆ s := by
    let x : s := ⟨.inl v, hv⟩
    have hambient : A.degree (.inl v) = 3 :=
      twoApexAugmentation_degree_inl T hdegree v
    have hindLe : (A.induce s).degree x ≤ A.degree (.inl v) :=
      degree_induce_le_degree A s x
    have heq : (A.induce s).degree x = A.degree (.inl v) := by
      have hx := hallDegree x
      omega
    exact neighborSet_subset_of_degree_induce_eq_degree A s x heq
  let baseSet : Set V := {v | Sum.inl v ∈ s}
  let H : T.Subgraph := (⊤ : T.Subgraph).induce baseSet
  have hbaseAll : ∀ v : V, Sum.inl v ∈ s := by
    intro v
    have hr : T.Reachable v₀ v := hT.connected v₀ v
    have hvH : v ∈ H.verts := by
      apply hr.mem_subgraphVerts (H := H) (u := v₀)
      · intro x hx y hxy
        have hxS : Sum.inl x ∈ s := hx
        have hyS : Sum.inl y ∈ s :=
          hbaseNeighborClosure x hxS (by simpa [A] using hxy)
        exact ⟨hx, hyS, by simpa [H] using hxy⟩
      · exact hv₀
    exact hvH
  haveI : Nonempty V := hT.connected.nonempty
  let v : V := Classical.arbitrary V
  have hvpos : 0 < T.degree v := by
    rcases hdegree v with hv | hv <;> omega
  obtain ⟨w, hvw⟩ := (T.degree_pos_iff_exists_adj v).mp hvpos
  letI : Nontrivial V := nontrivial_of_ne v w (T.ne_of_adj hvw)
  obtain ⟨leaf, hleaf⟩ := hT.exists_vert_degree_one_of_nontrivial
  have hapex : ∀ i : Fin 2, Sum.inr i ∈ s := by
    intro i
    exact hbaseNeighborClosure leaf (hbaseAll leaf) (by
      simp [A, hleaf])
  apply hs
  ext x
  cases x with
  | inl v => simp [hbaseAll v]
  | inr i => simp [hapex i]

noncomputable def leafFinset {V : Type*} [Fintype V]
    (T : SimpleGraph V) : Finset V :=
  Finset.univ.filter fun v ↦ T.degree v = 1

lemma two_mul_card_leafFinset {V : Type*} [Fintype V]
    (T : SimpleGraph V) (hT : T.IsTree)
    (hdegree : ∀ v, T.degree v = 1 ∨ T.degree v = 3) :
    2 * (leafFinset T).card = Fintype.card V + 2 := by
  have hindicator :
      (∑ v : V, if T.degree v = 1 then 2 else 0) =
        2 * (leafFinset T).card := by
    rw [Finset.sum_ite]
    simp [leafFinset, mul_comm]
  have hsum :
      (∑ v : V, T.degree v) + 2 * (leafFinset T).card =
        3 * Fintype.card V := by
    rw [← hindicator, ← Finset.sum_add_distrib]
    calc
      ∑ v : V, (T.degree v + if T.degree v = 1 then 2 else 0) =
          ∑ _v : V, 3 := by
            apply Finset.sum_congr rfl
            intro v _
            rcases hdegree v with hv | hv <;> simp [hv]
      _ = 3 * Fintype.card V := by simp [mul_comm]
  have hhandshake := T.sum_degrees_eq_twice_card_edges
  have hedge := hT.card_edgeFinset
  omega

lemma twoApexAugmentation_degree_inr {V : Type*} [Fintype V]
    (T : SimpleGraph V) (i : Fin 2) :
    (twoApexAugmentation T).degree (.inr i) =
      (leafFinset T).card + 1 := by
  rw [← SimpleGraph.card_neighborSet_eq_degree,
    Fintype.card_congr (neighborSetInrEquiv T i), Fintype.card_sum]
  have hi : Fintype.card {j : Fin 2 // j ≠ i} = 1 := by
    fin_cases i <;> decide
  rw [hi]
  congr 1
  rw [leafFinset, ← Set.toFinset_ofPred]
  exact (Set.toFinset_card {v : V | T.degree v = 1}).symm

theorem twoApexAugmentation_card_edgeFinset
    {V : Type*} [Fintype V] (T : SimpleGraph V) (hT : T.IsTree)
    (hdegree : ∀ v, T.degree v = 1 ∨ T.degree v = 3) :
    (twoApexAugmentation T).edgeFinset.card =
      2 * Fintype.card (V ⊕ Fin 2) - 2 := by
  let A := twoApexAugmentation T
  change A.edgeFinset.card = 2 * Fintype.card (V ⊕ Fin 2) - 2
  have hsum : ∑ x : V ⊕ Fin 2, A.degree x =
      3 * Fintype.card V + 2 * ((leafFinset T).card + 1) := by
    rw [Fintype.sum_sum_type]
    simp [A, twoApexAugmentation_degree_inl T hdegree,
      twoApexAugmentation_degree_inr, mul_comm]
  have hleaves := two_mul_card_leafFinset T hT hdegree
  have hhandshake := A.sum_degrees_eq_twice_card_edges
  simp only [Fintype.card_sum, Fintype.card_fin] at *
  omega

/-! ## Bipartite deletion and apex neighborhoods -/

def twoApexColor {V : Type*} (color : V → Fin 2) :
    V ⊕ Fin 2 → Fin 2
  | .inl v => color v
  | .inr _ => 0

theorem twoApexAugmentation_delete_apexEdge_colorable_two
    {V : Type*} [Fintype V] (T : SimpleGraph V) (color : V → Fin 2)
    (hproper : ∀ {v w : V}, T.Adj v w → color v ≠ color w)
    (hleaf : ∀ v : V, T.degree v = 1 → color v = 1) :
    ((twoApexAugmentation T).deleteEdges
      {s(Sum.inr (0 : Fin 2), Sum.inr (1 : Fin 2))}).Colorable 2 := by
  refine ⟨SimpleGraph.Coloring.mk (twoApexColor color) ?_⟩
  rintro (v | i) (w | j) hadj
  rw [SimpleGraph.deleteEdges_adj] at hadj
  · exact hproper hadj.1
  · have hv := hleaf v hadj.1
    simpa [twoApexColor, hv]
  · have hw := hleaf w hadj.1
    simpa [twoApexColor, hw]
  · exfalso
    apply hadj.2
    fin_cases i <;> fin_cases j <;> simp_all [Sym2.eq_iff]

theorem twoApexAugmentation_first_apex_neighbor_is_leaf
    {V : Type*} [Fintype V] (T : SimpleGraph V) :
    ∀ z : V ⊕ Fin 2,
      (twoApexAugmentation T).Adj (Sum.inr 0) z → z ≠ Sum.inr 1 →
        ∃ a : V, z = Sum.inl a ∧ T.degree a = 1 := by
  rintro (a | i) hadj hne
  · exact ⟨a, rfl, hadj⟩
  · fin_cases i <;> simp_all

theorem twoApexAugmentation_second_apex_neighbor_is_leaf
    {V : Type*} [Fintype V] (T : SimpleGraph V) :
    ∀ z : V ⊕ Fin 2,
      (twoApexAugmentation T).Adj z (Sum.inr 1) → z ≠ Sum.inr 0 →
        ∃ b : V, z = Sum.inl b ∧ T.degree b = 1 := by
  rintro (b | i) hadj hne
  · exact ⟨b, rfl, hadj⟩
  · fin_cases i <;> simp_all

/-! ## Converting a 23-cycle to a length-20 leaf path -/

/-- An odd closed walk must traverse a distinguished edge if deleting that
edge leaves a two-colorable graph. -/
lemma distinguished_edge_mem_of_odd_loop
    {V : Type*} {G : SimpleGraph V} {x y u : V}
    (hcol : (G.deleteEdges {s(x, y)}).Colorable 2)
    (c : G.Walk u u) (hodd : Odd c.length) :
    s(x, y) ∈ c.edges := by
  by_contra hxy
  let c' : (G.deleteEdges {s(x, y)}).Walk u u :=
    c.toDeleteEdges {s(x, y)} (by
      intro e he hes
      rw [Set.mem_singleton_iff] at hes
      exact hxy (hes ▸ he))
  have heven : Even c'.length :=
    (two_colorable_iff_forall_loop_even.mp hcol) u c'
  have hlen : c'.length = c.length := by simp [c']
  exact (Nat.not_even_iff_odd.mpr hodd) (hlen ▸ heven)

/-- Removing a specified edge from a simple cycle leaves the complementary
path between its endpoints. -/
lemma exists_complementary_path_of_mem_cycle_edges
    {V : Type*} {G : SimpleGraph V} {x y u : V}
    {c : G.Walk u u} (hc : c.IsCycle) (hxy : s(x, y) ∈ c.edges) :
    ∃ p : G.Walk x y,
      p.IsPath ∧ p.length + 1 = c.length ∧ s(x, y) ∉ p.edges := by
  have hxm : x ∈ c.support := c.fst_mem_support_of_mem_edges hxy
  let cr : G.Walk x x := c.rotate x hxm
  have hcr : cr.IsCycle := hc.rotate hxm
  have hxycr : s(x, y) ∈ cr.edges :=
    (c.rotate_edges x hxm).perm.mem_iff.mpr hxy
  have hcrlen : cr.length = c.length := by simp [cr]
  have hxyAdj : G.Adj x y := cr.adj_of_mem_edges hxycr
  have hxyne : x ≠ y := hxyAdj.ne
  have htailLen : cr.tail.length + 1 = cr.length :=
    Walk.length_tail_add_one hcr.not_nil
  by_cases hsnd : cr.snd = y
  · let q : G.Walk y x := cr.tail.copy hsnd rfl
    let p : G.Walk x y := q.reverse
    refine ⟨p, ?_, ?_, ?_⟩
    · simpa only [p, q, Walk.isPath_reverse_iff, Walk.isPath_copy] using
        hcr.isPath_tail
    · simp only [p, q, Walk.length_reverse, Walk.length_copy]
      omega
    · intro hmem
      have hmem' : s(x, y) ∈ cr.tail.edges := by
        simpa [p, q, Walk.edges_reverse] using hmem
      rw [← cr.cons_tail_eq hcr.not_nil] at hcr
      have hhead : s(x, y) = s(x, cr.snd) := by simpa [hsnd]
      exact ((Walk.cons_isCycle_iff _ _).mp hcr).2 (hhead ▸ hmem')
  · have hxyTail : s(x, y) ∈ cr.tail.edges := by
      rw [← cr.cons_tail_eq hcr.not_nil, Walk.edges_cons,
        List.mem_cons] at hxycr
      rcases hxycr with hhead | htail
      · rw [Sym2.eq_iff] at hhead
        rcases hhead with h | h
        · exact (hsnd h.2.symm).elim
        · exact (hxyne h.2.symm).elim
      · exact htail
    have htailNotNil : ¬ cr.tail.Nil := by
      rw [Walk.not_nil_iff_lt_length]
      have h := hcr.three_le_length
      simp only [Walk.length_tail]
      omega
    have hpenTail : y = cr.tail.penultimate :=
      hcr.isPath_tail.eq_penultimate_of_mem_edges hxyTail
    have hpen : cr.penultimate = y := by
      rw [← cr.cons_tail_eq hcr.not_nil]
      simpa [Walk.penultimate_cons_of_not_nil, htailNotNil] using
        hpenTail.symm
    have hsndRev : cr.reverse.snd = y := by simpa using hpen
    let q : G.Walk y x := cr.reverse.tail.copy hsndRev rfl
    let p : G.Walk x y := q.reverse
    refine ⟨p, ?_, ?_, ?_⟩
    · simpa only [p, q, Walk.isPath_reverse_iff, Walk.isPath_copy] using
        hcr.reverse.isPath_tail
    · have hrevTailLen :
          cr.reverse.tail.length + 1 = cr.reverse.length :=
        Walk.length_tail_add_one hcr.reverse.not_nil
      simp only [p, q, Walk.length_reverse, Walk.length_copy] at *
      omega
    · intro hmem
      have hmem' : s(x, y) ∈ cr.reverse.tail.edges := by
        simpa [p, q, Walk.edges_reverse] using hmem
      have hcrrev := hcr.reverse
      rw [← cr.reverse.cons_tail_eq hcrrev.not_nil] at hcrrev
      have hhead : s(x, y) = s(x, cr.reverse.snd) := by
        simpa [hsndRev]
      exact ((Walk.cons_isCycle_iff _ _).mp hcrrev).2 (hhead ▸ hmem')

/-- A 23-cycle whose distinguished-edge deletion is bipartite contains a
complementary length-22 path between the distinguished vertices. -/
lemma exists_length_22_path_of_cycleGraph_23
    {V : Type*} {G : SimpleGraph V} {x y : V}
    (hcol : (G.deleteEdges {s(x, y)}).Colorable 2)
    (hcycle : cycleGraph 23 ⊑ G) :
    ∃ p : G.Walk x y,
      p.IsPath ∧ p.length = 22 ∧ s(x, y) ∉ p.edges := by
  obtain ⟨u, c, hc, hclen⟩ :=
    (cycleGraph_isContained_iff (n := 23) (by omega)).mp hcycle
  have hodd : Odd c.length := by
    rw [hclen]
    exact ⟨11, by omega⟩
  have hxy := distinguished_edge_mem_of_odd_loop hcol c hodd
  obtain ⟨p, hp, hplen, hfree⟩ :=
    exists_complementary_path_of_mem_cycle_edges hc hxy
  refine ⟨p, hp, ?_, hfree⟩
  omega

/-- Extract the old middle of a length-22 apex-to-apex path. -/
lemma exists_leaf_path_length_20_of_apex_path
    {V : Type*} [Fintype V] {T : SimpleGraph V}
    {G : SimpleGraph (V ⊕ Fin 2)}
    (hold : ∀ a b : V,
      G.Adj (Sum.inl a) (Sum.inl b) ↔ T.Adj a b)
    (hx : ∀ z : V ⊕ Fin 2,
      G.Adj (Sum.inr 0) z → z ≠ Sum.inr 1 →
        ∃ a : V, z = Sum.inl a ∧ T.degree a = 1)
    (hy : ∀ z : V ⊕ Fin 2,
      G.Adj z (Sum.inr 1) → z ≠ Sum.inr 0 →
        ∃ b : V, z = Sum.inl b ∧ T.degree b = 1)
    (p : G.Walk (Sum.inr 0) (Sum.inr 1))
    (hp : p.IsPath) (hplen : p.length = 22)
    (hfree : s(Sum.inr 0, Sum.inr 1) ∉ p.edges) :
    ∃ (a b : V) (q : T.Walk a b),
      T.degree a = 1 ∧ T.degree b = 1 ∧
        q.IsPath ∧ q.length = 20 := by
  have hpNotNil : ¬ p.Nil := by
    rw [Walk.not_nil_iff_lt_length, hplen]
    omega
  have htailNotNil : ¬ p.tail.Nil := by
    rw [Walk.not_nil_iff_lt_length]
    simp only [Walk.length_tail, hplen]
    omega
  have hsndNe : p.snd ≠ Sum.inr 1 := by
    intro h
    apply hfree
    simpa [h] using p.mk_start_snd_mem_edges hpNotNil
  have hpenNe : p.penultimate ≠ Sum.inr 0 := by
    intro h
    apply hfree
    have hm := p.mk_penultimate_end_mem_edges hpNotNil
    simpa [h, Sym2.eq_swap] using hm
  obtain ⟨a, haSnd, haLeaf⟩ :=
    hx p.snd (p.adj_snd hpNotNil) hsndNe
  obtain ⟨b, hbPen, hbLeaf⟩ :=
    hy p.penultimate (p.adj_penultimate hpNotNil) hpenNe
  have hpenTail : p.tail.penultimate = p.penultimate := by
    rw [← p.cons_tail_eq hpNotNil]
    simp [Walk.penultimate_cons_of_not_nil, htailNotNil]
  let q₀ : G.Walk p.snd p.penultimate :=
    p.tail.dropLast.copy rfl hpenTail
  have hq₀Path : q₀.IsPath := by
    rw [Walk.isPath_copy]
    exact hp.tail.dropLast
  have hq₀Len : q₀.length = 20 := by
    simp only [q₀, Walk.length_copy, Walk.length_dropLast,
      Walk.length_tail, hplen]
  have hq₀Old :
      ∀ z ∈ q₀.support,
        z ∈ Set.range (Sum.inl : V → V ⊕ Fin 2) := by
    intro z hz
    have hzTailDrop : z ∈ p.tail.dropLast.support := by
      simpa only [q₀, Walk.support_copy] using hz
    obtain ⟨i, hiEq, hiLe⟩ :=
      Walk.mem_support_iff_exists_getVert.mp hzTailDrop
    have hiLen : i ≤ 20 := by
      have h : p.tail.dropLast.length = 20 := by
        simp only [Walk.length_dropLast, Walk.length_tail, hplen]
      simpa only [h] using hiLe
    have hiTail : i < p.tail.length := by
      simp only [Walk.length_tail, hplen]
      omega
    have hzi : p.getVert (i + 1) = z := by
      rw [← hiEq, Walk.getVert_dropLast hiTail, Walk.getVert_tail]
    cases z with
    | inl v => exact ⟨v, rfl⟩
    | inr j =>
        fin_cases j
        · change p.getVert (i + 1) = Sum.inr (0 : Fin 2) at hzi
          have heq : i + 1 = 0 := hp.getVert_injOn
            (by simp only [Set.mem_ofPred_eq, hplen]; omega)
            (by simp only [Set.mem_ofPred_eq]; omega)
            (by simpa only [Walk.getVert_zero] using hzi)
          omega
        · change p.getVert (i + 1) = Sum.inr (1 : Fin 2) at hzi
          have heq : i + 1 = p.length := hp.getVert_injOn
            (by simp only [Set.mem_ofPred_eq, hplen]; omega)
            (by simp only [Set.mem_ofPred_eq]; omega)
            (by simpa only [Walk.getVert_length] using hzi)
          omega
  let oldFun : V ↪ V ⊕ Fin 2 :=
    ⟨Sum.inl, Sum.inl_injective⟩
  let oldEmbedding : T ↪g G :=
    { __ := oldFun
      map_rel_iff' := fun {a b} ↦ hold a b }
  let qOld : G.Walk (Sum.inl a) (Sum.inl b) :=
    q₀.copy haSnd hbPen
  have hqOldPath : qOld.IsPath := by
    simpa only [qOld, Walk.isPath_copy] using hq₀Path
  have hqOldOld :
      ∀ z ∈ qOld.support,
        z ∈ Set.range (Sum.inl : V → V ⊕ Fin 2) := by
    intro z hz
    apply hq₀Old z
    simpa only [qOld, Walk.support_copy] using hz
  let q₁ :=
    qOld.induce (Set.range (Sum.inl : V → V ⊕ Fin 2)) hqOldOld
  let q : T.Walk a b :=
    (q₁.map oldEmbedding.isoInduceRange.symm.toHom).copy
      (by
        change oldEmbedding.isoInduceRange.symm _ = a
        exact oldEmbedding.isoInduceRange.symm_apply_apply a)
      (by
        change oldEmbedding.isoInduceRange.symm _ = b
        exact oldEmbedding.isoInduceRange.symm_apply_apply b)
  refine ⟨a, b, q, haLeaf, hbLeaf, ?_, ?_⟩
  · rw [Walk.isPath_copy]
    apply Walk.IsPath.map oldEmbedding.isoInduceRange.symm.injective
    rw [Walk.isPath_def]
    simp only [q₁, Walk.support_induce]
    rw [← List.nodup_map_iff Subtype.val_injective,
      List.attachWith_map_subtype_val]
    exact hqOldPath.support_nodup
  · simp only [q, Walk.length_copy, Walk.length_map]
    have hinduce : q₁.length = qOld.length := by
      have hs : q₁.support.length = qOld.support.length := by
        simp only [q₁, Walk.support_induce, List.length_attachWith]
      have h₁ := q₁.length_support
      have hOld := qOld.length_support
      omega
    rw [hinduce]
    simpa only [qOld, Walk.length_copy] using hq₀Len

/-- A C_23 in a two-apex graph produces a length-20 leaf-to-leaf path
in the old induced graph. -/
lemma exists_leaf_path_length_20_of_cycleGraph_23
    {V : Type*} [Fintype V] {T : SimpleGraph V}
    {G : SimpleGraph (V ⊕ Fin 2)}
    (hcol : (G.deleteEdges {s(Sum.inr 0, Sum.inr 1)}).Colorable 2)
    (hold : ∀ a b : V,
      G.Adj (Sum.inl a) (Sum.inl b) ↔ T.Adj a b)
    (hx : ∀ z : V ⊕ Fin 2,
      G.Adj (Sum.inr 0) z → z ≠ Sum.inr 1 →
        ∃ a : V, z = Sum.inl a ∧ T.degree a = 1)
    (hy : ∀ z : V ⊕ Fin 2,
      G.Adj z (Sum.inr 1) → z ≠ Sum.inr 0 →
        ∃ b : V, z = Sum.inl b ∧ T.degree b = 1)
    (hcycle : cycleGraph 23 ⊑ G) :
    ∃ (a b : V) (q : T.Walk a b),
      T.degree a = 1 ∧ T.degree b = 1 ∧
        q.IsPath ∧ q.length = 20 := by
  obtain ⟨p, hp, hplen, hfree⟩ :=
    exists_length_22_path_of_cycleGraph_23 hcol hcycle
  exact
    exists_leaf_path_length_20_of_apex_path hold hx hy p hp hplen hfree

/-! ## The Narins--Pokrovskiy--Szabó counterexample family -/

/-- The graph obtained from the explicit NPS tree by adjoining the two
apex vertices. -/
noncomputable def npsGraph (m : ℕ) :
    SimpleGraph (TreeVertex m ⊕ Fin 2) :=
  twoApexAugmentation (treeGraph m)

lemma npsGraph_delete_apexEdge_colorable_two (m : ℕ) :
    ((npsGraph m).deleteEdges
      {s(Sum.inr (0 : Fin 2), Sum.inr (1 : Fin 2))}).Colorable 2 := by
  apply twoApexAugmentation_delete_apexEdge_colorable_two
    (treeGraph m) treeColor
  · exact treeColor_proper
  · intro v hv
    exact treeColor_eq_one_of_isArmLeaf
      ((treeGraph_degree_one_iff_isArmLeaf v).mp hv)

theorem npsGraph_degreeThreeCritical (m : ℕ) :
    DegreeThreeCritical (npsGraph m) := by
  constructor
  · exact twoApexAugmentation_card_edgeFinset
      (treeGraph m) (treeGraph_isTree m)
      (treeGraph_degree_one_or_three m)
  · intro s hs
    exact twoApexAugmentation_minDegree_le_two
      (treeGraph m) (treeGraph_isTree m)
      (treeGraph_degree_one_or_three m) s hs

/-- Every member of the NPS family is `C₂₃`-free. -/
theorem npsGraph_cycleGraph_23_free (m : ℕ) :
    ¬ cycleGraph 23 ⊑ npsGraph m := by
  intro hcycle
  obtain ⟨a, b, q, ha, hb, hq, hlen⟩ :=
    exists_leaf_path_length_20_of_cycleGraph_23
      (T := treeGraph m) (G := npsGraph m)
      (npsGraph_delete_apexEdge_colorable_two m)
      (fun _ _ ↦ Iff.rfl)
      (twoApexAugmentation_first_apex_neighbor_is_leaf (treeGraph m))
      (twoApexAugmentation_second_apex_neighbor_is_leaf (treeGraph m))
      hcycle
  have hal := (treeGraph_degree_one_iff_isArmLeaf a).mp ha
  have hbl := (treeGraph_degree_one_iff_isArmLeaf b).mp hb
  exact (treeGraph_no_leaf_path_length_20 hal hbl q hq) hlen

theorem nps_arbitrarily_large_counterexamples :
    ∀ N : ℕ,
      ∃ (V : Type) (_ : Fintype V) (G : SimpleGraph V),
        N ≤ Fintype.card V ∧ DegreeThreeCritical G ∧
          ¬ cycleGraph 23 ⊑ G := by
  intro N
  refine ⟨TreeVertex N ⊕ Fin 2, inferInstance, npsGraph N,
    augmentedTreeVertex_card_ge N, ?_, ?_⟩
  · exact npsGraph_degreeThreeCritical N
  · exact npsGraph_cycleGraph_23_free N

/-! ## Relabeling and the final logical reduction -/

theorem degreeThreeCritical_overFin
    {V : Type*} [Fintype V] (G : SimpleGraph V)
    (hG : DegreeThreeCritical G) :
    DegreeThreeCritical (G.overFin rfl) := by
  classical
  let φ := G.overFinIso rfl
  constructor
  · have hedge := φ.card_edgeFinset_eq
    rw [← hedge]
    simpa only [Fintype.card_fin] using hG.1
  · intro s hs
    let t : Set V := φ ⁻¹' s
    have ht : t ≠ Set.univ := by
      intro htuniv
      apply hs
      ext y
      simp only [Set.mem_univ, iff_true]
      obtain ⟨x, rfl⟩ := φ.surjective y
      have hx : x ∈ t := by
        rw [htuniv]
        exact Set.mem_univ x
      exact hx
    have hbij : Set.BijOn φ t s := by
      refine ⟨?_, ?_, ?_⟩
      · intro x hx
        exact hx
      · intro x _ y _ hxy
        exact φ.injective hxy
      · intro y hy
        refine ⟨φ.symm y, ?_, ?_⟩
        · change φ (φ.symm y) ∈ s
          simpa using hy
        · exact φ.apply_symm_apply y
    let ψ := φ.induce hbij
    rw [← ψ.minDegree_eq]
    exact hG.2 t ht

theorem cycleGraph_23_free_overFin
    {V : Type*} [Fintype V] (G : SimpleGraph V)
    (hfree : ¬ cycleGraph 23 ⊑ G) :
    ¬ cycleGraph 23 ⊑ G.overFin rfl := by
  intro hcopy
  exact hfree
    ((isContained_congr_right (G.overFinIso rfl)).mpr hcopy)

theorem finiteCounterexample_to_fin
    {V : Type*} [Fintype V] (G : SimpleGraph V)
    (hG : DegreeThreeCritical G)
    (hfree : ¬ cycleGraph 23 ⊑ G) :
    ∃ G' : SimpleGraph (Fin (Fintype.card V)),
      DegreeThreeCritical G' ∧ ¬ cycleGraph 23 ⊑ G' := by
  exact ⟨G.overFin rfl, degreeThreeCritical_overFin G hG,
    cycleGraph_23_free_overFin G hfree⟩

theorem arbitraryCounterexamples_to_fin
    (hcounter : ∀ N : ℕ,
      ∃ (V : Type) (_ : Fintype V) (G : SimpleGraph V),
        N ≤ Fintype.card V ∧ DegreeThreeCritical G ∧
          ¬ cycleGraph 23 ⊑ G) :
    ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧
      ∃ G : SimpleGraph (Fin n),
        DegreeThreeCritical G ∧ ¬ cycleGraph 23 ⊑ G := by
  intro N
  obtain ⟨V, inst, G, hcard, hG, hfree⟩ := hcounter N
  letI : Fintype V := inst
  refine ⟨Fintype.card V, hcard, ?_⟩
  exact finiteCounterexample_to_fin G hG hfree

theorem erdos815_of_fin_counterexamples
    (hcounter : ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧
      ∃ G : SimpleGraph (Fin n),
        DegreeThreeCritical G ∧ ¬ cycleGraph 23 ⊑ G) :
    ¬ Erdos815Statement := by
  intro hstatement
  ·
    obtain ⟨N, hN⟩ := hstatement 23 (by omega)
    obtain ⟨n, hn, G, hG, hfree⟩ := hcounter N
    exact (hfree (hN n hn G hG)).elim

theorem erdos815_of_arbitrary_counterexamples
    (hcounter : ∀ N : ℕ,
      ∃ (V : Type) (_ : Fintype V) (G : SimpleGraph V),
        N ≤ Fintype.card V ∧ DegreeThreeCritical G ∧
          ¬ cycleGraph 23 ⊑ G) :
    ¬ Erdos815Statement :=
  erdos815_of_fin_counterexamples
    (arbitraryCounterexamples_to_fin hcounter)

/-- **Resolution of Erdős Problem 815.**  The proposed eventual cycle
statement is false: the NPS construction gives arbitrarily large
degree-three-critical graphs containing no copy of `C₂₃`. -/
theorem not_erdos_815 : ¬ (∀ k : ℕ, 3 ≤ k → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
  ∀ G : SimpleGraph (Fin n),
    Erdos815.DegreeThreeCritical G → SimpleGraph.cycleGraph k ⊑ G) :=
  erdos815_of_arbitrary_counterexamples
    nps_arbitrarily_large_counterexamples

#print axioms Erdos815.not_erdos_815

end Erdos815

alias _root_.Erdos815.erdos_815 := _root_.Erdos815.not_erdos_815
