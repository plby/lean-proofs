import ErdosProblems.Erdos591.AtomicSpacing
import ErdosProblems.Erdos591.MacroRank
import Mathlib.Data.Nat.Pairing
import Mathlib.Data.List.GetD

/-!
# Finite stages of the countably branching macro forest

Node zero is the empty cursor. At construction time `r`, the scheduled
parent is `Nat.unpair r |>.1` and the new label parameter is the other
component plus one. Each new input block appears once in the global
log. Branch records retain the blocks on their ancestry as a sublist.
-/

namespace Erdos591.Positive.Game.Macro.Forest

abbrev Block := List (Finset ℕ × ℕ)
abbrev Segment := ℕ × Block

def raw (xs : Block) : List ℕ := Atomic.inputs (Atomic.tag false xs)

@[simp] theorem raw_nil : raw [] = [] := rfl

@[simp] theorem raw_append (xs ys : Block) : raw (xs ++ ys) = raw xs ++ raw ys := by
  simp [raw]

theorem raw_sublist {xs ys : Block} (h : List.Sublist xs ys) :
    List.Sublist (raw xs) (raw ys) := by
  simpa [raw, Atomic.inputs_tag] using
    h.flatMap (fun a => a.1.sort (· ≤ ·) ++ [a.2])

structure Node where
  segments : List Segment
  cursor : LabeledWord
  legal : LabeledWord.LegalRun LabeledWord.initial (segments.flatMap Prod.snd) cursor

namespace Node

def atoms (p : Node) : Block := p.segments.flatMap Prod.snd

def initial : Node := ⟨[], LabeledWord.initial, .nil _⟩

def append (p : Node) (index : ℕ) (xs : Block) (v : LabeledWord)
    (h : LabeledWord.LegalRun p.cursor xs v) : Node where
  segments := p.segments ++ [(index, xs)]
  cursor := v
  legal := by simpa using p.legal.append h

@[simp] theorem atoms_append (p : Node) (index : ℕ) (xs : Block) (v : LabeledWord)
    (h : LabeledWord.LegalRun p.cursor xs v) :
    (p.append index xs v h).atoms = p.atoms ++ xs := by simp [atoms, append]

theorem invariant (p : Node) : p.cursor.CursorInvariant :=
  p.legal.cursorInvariant LabeledWord.cursorInvariant_initial

theorem support (p : Node) : p.cursor.support ⊆ (raw p.atoms).toFinset := by
  simpa [raw, atoms] using p.legal.support false

theorem coordinates (p : Node) : p.cursor.coordinates = p.atoms.map Prod.snd := by
  simpa [atoms, LabeledWord.initial] using LabeledWord.runAtoms_coordinates p.legal.run

end Node

/-- Completed parents are copied with no new input. Only a live parent
produces a new macro-child. -/
inductive Expansion (q : ℕ) : LabeledWord → Block → LabeledWord → Prop
  | idle (w : LabeledWord) (h : w.terminal = true) : Expansion q w [] w
  | live {w v : LabeledWord} {xs : Block} (h : Extension q w xs v) : Expansion q w xs v

theorem Expansion.legal {q : ℕ} {w v : LabeledWord} {xs : Block}
    (h : Expansion q w xs v) : LabeledWord.LegalRun w xs v := by
  cases h with
  | idle => exact .nil _
  | live h => exact h.legal

theorem Expansion.end {q : ℕ} {w v : LabeledWord} {xs : Block}
    (h : Expansion q w xs v) : v.terminal = true ∨ v.relaxed = true := by
  cases h with
  | idle ht => exact Or.inl ht
  | live h => exact h.end

theorem Expansion.extension {q : ℕ} {w v : LabeledWord} {xs : Block}
    (h : Expansion q w xs v) (hw : w.terminal = false) : Extension q w xs v := by
  cases h with
  | idle ht => simp [hw] at ht
  | live h => exact h

structure Chunk {N : Set ℕ} (H : Set ℕ) (b : Concrete.Hist N → ℕ)
    (F : Finset ℕ) (q : ℕ) (w : LabeledWord) where
  block : Block
  cursor : LabeledWord
  expansion : Expansion q w block cursor
  increasing : (raw block).Pairwise (· < ·)
  pool : ∀ x ∈ raw block, x ∈ H
  fresh : ∀ x ∈ raw block, F.sup id < x
  spaced : Atomic.Spaced b F (Atomic.tag false block)

theorem chunk_nonempty {N H : Set ℕ} (hH : H.Infinite)
    (b : Concrete.Hist N → ℕ) (F : Finset ℕ) (q : ℕ) (w : LabeledWord) :
    Nonempty (Chunk H b F q w) := by
  cases ht : w.terminal with
  | true =>
      exact ⟨⟨[], w, .idle w ht, by simp, by simp, by simp, Atomic.spaced_nil b F⟩⟩
  | false =>
      obtain ⟨xs, v, hext, hi, hm, hf, hs⟩ :=
        spaced_extension_exists hH b F q false ⟨w, ht⟩
      exact ⟨⟨xs, v, .live hext, hi, hm, hf, hs⟩⟩

noncomputable def chooseChunk {N H : Set ℕ} (hH : H.Infinite)
    (b : Concrete.Hist N → ℕ) (F : Finset ℕ) (q : ℕ) (w : LabeledWord) :
    Chunk H b F q w := Classical.choice (chunk_nonempty hH b F q w)

structure Stage where
  nodes : List Node
  log : List Segment

namespace Stage

def atoms (S : Stage) : Block := S.log.flatMap Prod.snd
def inputs (S : Stage) : List ℕ := raw S.atoms
def support (S : Stage) : Finset ℕ := S.inputs.toFinset
def initial : Stage := ⟨[Node.initial], []⟩

def append (S : Stage) (p : Node) (xs : Block) (v : LabeledWord)
    (h : LabeledWord.LegalRun p.cursor xs v) : Stage :=
  ⟨S.nodes ++ [p.append S.log.length xs v h], S.log ++ [(S.log.length, xs)]⟩

@[simp] theorem atoms_append (S : Stage) (p : Node) (xs : Block) (v : LabeledWord)
    (h : LabeledWord.LegalRun p.cursor xs v) :
    (S.append p xs v h).atoms = S.atoms ++ xs := by simp [atoms, append]

@[simp] theorem inputs_append (S : Stage) (p : Node) (xs : Block) (v : LabeledWord)
    (h : LabeledWord.LegalRun p.cursor xs v) :
    (S.append p xs v h).inputs = S.inputs ++ raw xs := by simp [inputs]

def scheduledParent (S : Stage) : Node :=
  S.nodes.getD (Nat.unpair S.log.length).1 Node.initial

def parameter (S : Stage) : ℕ := (Nat.unpair S.log.length).2 + 1

noncomputable def next {N H : Set ℕ} (hH : H.Infinite)
    (b : Concrete.Hist N → ℕ) (S : Stage) : Stage :=
  let c := chooseChunk hH b S.support S.parameter S.scheduledParent.cursor
  S.append S.scheduledParent c.block c.cursor c.expansion.legal

structure Valid {N : Set ℕ} (H : Set ℕ) (b : Concrete.Hist N → ℕ) (S : Stage) : Prop where
  shape : S.nodes.length = S.log.length + 1
  names : S.log.map Prod.fst = List.range S.log.length
  branches : ∀ p ∈ S.nodes, List.Sublist p.segments S.log
  increasing : S.inputs.Pairwise (· < ·)
  pool : ∀ x ∈ S.inputs, x ∈ H
  positive : ∀ x ∈ S.inputs, 0 < x
  spaced : Atomic.Spaced b ∅ (Atomic.tag false S.atoms)

theorem valid_initial {N : Set ℕ} (H : Set ℕ) (b : Concrete.Hist N → ℕ) :
    Valid H b initial := by
  constructor
  · rfl
  · rfl
  · intro p hp
    have heq : p = Node.initial := by simpa [initial] using hp
    subst p
    exact List.Sublist.refl []
  · exact List.Pairwise.nil
  · exact fun _ h => False.elim (List.not_mem_nil h)
  · exact fun _ h => False.elim (List.not_mem_nil h)
  · exact Atomic.spaced_nil b ∅

theorem Valid.parent_mem {N H : Set ℕ} {b : Concrete.Hist N → ℕ} {S : Stage}
    (h : Valid H b S) : S.scheduledParent ∈ S.nodes := by
  have hi : (Nat.unpair S.log.length).1 < S.nodes.length := by
    have hu := Nat.unpair_left_le S.log.length
    have hs := h.shape
    omega
  rw [scheduledParent, List.getD_eq_getElem _ _ hi]
  exact List.getElem_mem hi

theorem Valid.append {N H : Set ℕ} {b : Concrete.Hist N → ℕ} {S : Stage}
    (h : Valid H b S) (p : Node) (hp : p ∈ S.nodes) {q : ℕ}
    (c : Chunk H b S.support q p.cursor) :
    Valid H b (S.append p c.block c.cursor c.expansion.legal) := by
  constructor
  · simpa [Stage.append] using h.shape
  · simpa [Stage.append, List.range_succ] using
      congrArg (fun xs => xs ++ [S.log.length]) h.names
  · intro v hv
    rcases List.mem_append.mp hv with hv | hv
    · exact (h.branches v hv).trans (List.sublist_append_left _ _)
    · have heq : v = p.append S.log.length c.block c.cursor c.expansion.legal := by
        simpa using hv
      subst v
      exact (h.branches p hp).append (List.Sublist.refl _)
  · rw [inputs_append]
    refine List.pairwise_append.mpr ⟨h.increasing, c.increasing, ?_⟩
    intro x hx y hy
    exact (Finset.le_sup (f := id) (List.mem_toFinset.mpr hx)).trans_lt (c.fresh y hy)
  · intro x hx
    rw [inputs_append, List.mem_append] at hx
    exact hx.elim (h.pool x) (c.pool x)
  · intro x hx
    rw [inputs_append, List.mem_append] at hx
    exact hx.elim (h.positive x) (fun hy => (Nat.zero_le _).trans_lt (c.fresh x hy))
  · simp only [atoms_append, Atomic.tag_append]
    apply h.spaced.append
    simpa [support, inputs, raw] using c.spaced

theorem Valid.next {N H : Set ℕ} (hH : H.Infinite)
    {b : Concrete.Hist N → ℕ} {S : Stage} (h : Valid H b S) : Valid H b (next hH b S) :=
  h.append S.scheduledParent h.parent_mem
    (chooseChunk hH b S.support S.parameter S.scheduledParent.cursor)

end Stage

#print axioms chunk_nonempty
#print axioms Stage.Valid.next

end Erdos591.Positive.Game.Macro.Forest
