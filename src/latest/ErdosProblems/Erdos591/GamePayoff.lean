import ErdosProblems.Erdos591.GameClosed
import ErdosProblems.Erdos591.GameParser
import Mathlib.Data.List.GetD

/-!
# The exact clarity and blue-pair payoff

Cuts are tested between adjacent coordinates of literal words. Body and
leaf labels are one-based indices, as in the mathematical construction.
The payoff uses a graph on the existing exact carrier `Negative.Exact.G`;
unique decoding prevents the existential vertex witnesses from changing
the color of a fixed pair of words.
-/

namespace Erdos591.Positive.Game.Payoff

open Erdos591.Negative.Exact

/-- Position `k` is a cut when an entry of the other word occurs
strictly between this coordinate and its next coordinate. -/
def Cut (xs ys : List ℕ) (k : ℕ) : Prop :=
  k + 1 < xs.length ∧ ∃ y ∈ ys, xs.getD k 0 < y ∧ y < xs.getD (k + 1) 0

/-- The coordinate position of zero-based leaf `j` in zero-based body
`i`: one root, the earlier complete bodies, and this body's marker
precede it. -/
def leafPosition (s : List (List ℕ)) (i j : ℕ) : ℕ :=
  2 + ((s.take i).map (fun a => a.length + 1)).sum + j

def LeafCut (s t : List (List ℕ)) (i j : ℕ) : Prop :=
  i < s.length ∧ j < (s.getD i []).length ∧ Cut (word s) (word t) (leafPosition s i j)

theorem flatMap_leaf_lt (s : List (List ℕ)) (i j : ℕ)
    (hi : i < s.length) (hj : j < (s.getD i []).length) :
    ((s.take i).map (fun a => a.length + 1)).sum + 1 + j < (s.flatMap levelWord).length := by
  induction i generalizing s with
  | zero =>
      cases s with
      | nil => simp at hi
      | cons a s =>
          simp only [List.getD_cons_zero] at hj
          simp only [List.take_zero, List.map_nil, List.sum_nil, Nat.zero_add,
            List.flatMap_cons, List.length_append, levelWord_length]
          omega
  | succ i ih =>
      cases s with
      | nil => simp at hi
      | cons a s =>
          have hi' : i < s.length := by simpa using hi
          have hj' : j < (s.getD i []).length := by simpa using hj
          have hrest := ih s hi' hj'
          simp only [List.take_succ_cons, List.map_cons, List.sum_cons,
            List.flatMap_cons, List.length_append, levelWord_length]
          omega

theorem flatMap_leaf_value (s : List (List ℕ)) (i j : ℕ)
    (hi : i < s.length) (hj : j < (s.getD i []).length) :
    (s.flatMap levelWord).getD
      (((s.take i).map (fun a => a.length + 1)).sum + 1 + j) 0 =
      (s.getD i []).getD j 0 := by
  induction i generalizing s with
  | zero =>
      cases s with
      | nil => simp at hi
      | cons a s =>
          simp only [List.getD_cons_zero] at hj
          simp only [List.take_zero, List.map_nil, List.sum_nil, Nat.zero_add,
            List.flatMap_cons, List.getD_cons_zero]
          rw [List.getD_append _ _ _ _ (by simp only [levelWord_length]; omega)]
          simp [levelWord, Nat.add_comm]
  | succ i ih =>
      cases s with
      | nil => simp at hi
      | cons a s =>
          have hi' : i < s.length := by simpa using hi
          have hj' : j < (s.getD i []).length := by simpa using hj
          simp only [List.take_succ_cons, List.map_cons, List.sum_cons,
            List.flatMap_cons, List.getD_cons_succ]
          rw [List.getD_append_right _ _ _ _ (by simp only [levelWord_length]; omega)]
          have hind : a.length + 1 + ((s.take i).map (fun a => a.length + 1)).sum + 1 + j -
              (levelWord a).length = ((s.take i).map (fun a => a.length + 1)).sum + 1 + j := by
            simp only [levelWord_length]
            omega
          rw [hind]
          exact ih s hi' hj'

theorem leafPosition_lt (s : List (List ℕ)) (i j : ℕ)
    (hi : i < s.length) (hj : j < (s.getD i []).length) :
    leafPosition s i j < (word s).length := by
  have h := flatMap_leaf_lt s i j hi hj
  simp only [leafPosition, word, List.length_cons]
  omega

theorem leafPosition_value (s : List (List ℕ)) (i j : ℕ)
    (hi : i < s.length) (hj : j < (s.getD i []).length) :
    (word s).getD (leafPosition s i j) 0 = (s.getD i []).getD j 0 := by
  have hindex : leafPosition s i j =
      (((s.take i).map (fun a => a.length + 1)).sum + 1 + j) + 1 := by
    simp only [leafPosition]
    omega
  rw [hindex, word, List.getD_cons_succ]
  exact flatMap_leaf_value s i j hi hj

/-- The labels of one completed cursor agree exactly with its leaf
cuts. Strict marker bounds explicitly exclude the last body and each
body's last leaf. No coordinate cut is allowed at a root or body marker.
-/
structure ClearSide (w : LabeledWord) (s t : G) : Prop where
  coordinates : word s.val = w.coordinates
  labels_length : w.bodyLabels.length = s.val.length
  root_bounds : ∀ i ∈ w.rootLabel, 0 < i ∧ i < s.val.length
  body_bounds : ∀ i < s.val.length, ∀ j ∈ w.bodyLabels.getD i ∅,
    0 < j ∧ j < (s.val.getD i []).length
  root_exact : ∀ i, i + 1 ∈ w.rootLabel ↔ ∃ j, LeafCut s.val t.val i j
  body_exact : ∀ i < s.val.length, ∀ j,
    j + 1 ∈ w.bodyLabels.getD i ∅ ↔ LeafCut s.val t.val i j
  all_cuts_leaves : ∀ k, Cut (word s.val) (word t.val) k →
    ∃ i j, LeafCut s.val t.val i j ∧ k = leafPosition s.val i j

def Clear (b : Board) (s t : G) : Prop :=
  ClearSide b.left s t ∧ ClearSide b.right t s ∧
    Disjoint (word s.val).toFinset (word t.val).toFinset

def MaxOrder (inside : Bool) (b : Board) : Prop :=
  if inside then b.right.coordinates.getLastD 0 < b.left.coordinates.getLastD 0
  else b.left.coordinates.getLastD 0 < b.right.coordinates.getLastD 0

def Winning (blue : SimpleGraph G) (inside : Bool) (b : Board) : Prop :=
  ∃ s t : G, Clear b s t ∧ blue.Adj s t ∧ MaxOrder inside b

noncomputable def payoff (blue : SimpleGraph G) (inside : Bool) (b : Board) : Bool := by
  classical
  exact decide (Winning blue inside b)

@[simp] theorem payoff_true_iff (blue : SimpleGraph G) (inside : Bool) (b : Board) :
    payoff blue inside b = true ↔ Winning blue inside b := by
  simp [payoff]

theorem literal_vertex_unique {s t : G} (h : word s.val = word t.val) : s = t :=
  Subtype.ext (Parser.word_injective h)

/-- The payoff's color is exactly the given graph color of the two
decoded literal vertices. The witnesses cannot be replaced by different
vertices with the same coordinate word. -/
theorem winning_iff (blue : SimpleGraph G) (inside : Bool) (b : Board) (s t : G)
    (hs : word s.val = b.left.coordinates) (ht : word t.val = b.right.coordinates) :
    Winning blue inside b ↔ Clear b s t ∧ blue.Adj s t ∧ MaxOrder inside b := by
  constructor
  · rintro ⟨s', t', hclear, hblue, hmax⟩
    have hss : s' = s := literal_vertex_unique (hclear.1.coordinates.trans hs.symm)
    have htt : t' = t := literal_vertex_unique (hclear.2.1.coordinates.trans ht.symm)
    subst s'
    subst t'
    exact ⟨hclear, hblue, hmax⟩
  · intro h
    exact ⟨s, t, h⟩

theorem ClearSide.root_mem_iff_body_nonempty {w : LabeledWord} {s t : G}
    (h : ClearSide w s t) {i : ℕ} (hi : i < s.val.length) :
    i + 1 ∈ w.rootLabel ↔ (w.bodyLabels.getD i ∅).Nonempty := by
  constructor
  · intro hroot
    obtain ⟨j, hj⟩ := (h.root_exact i).1 hroot
    exact ⟨j + 1, (h.body_exact i hi j).2 hj⟩
  · rintro ⟨j, hj⟩
    have hjpos := (h.body_bounds i hi j hj).1
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hjpos)
    exact (h.root_exact i).2 ⟨k, (h.body_exact i hi k).1 hj⟩

theorem ClearSide.cut_not_last_body {w : LabeledWord} {s t : G}
    (h : ClearSide w s t) {i j : ℕ} (hc : LeafCut s.val t.val i j) :
    i + 1 < s.val.length :=
  (h.root_bounds (i + 1) ((h.root_exact i).2 ⟨j, hc⟩)).2

theorem ClearSide.cut_not_last_leaf {w : LabeledWord} {s t : G}
    (h : ClearSide w s t) {i j : ℕ} (hc : LeafCut s.val t.val i j) :
    j + 1 < (s.val.getD i []).length :=
  (h.body_bounds i hc.1 (j + 1) ((h.body_exact i hc.1 j).2 hc)).2

/-- The concrete game with the mathematical clarity/blue-pair payoff. -/
noncomputable def exactGame (N : Set ℕ) (blue : SimpleGraph G) :
    FiniteResponseGame (Concrete.Hist N) N :=
  Concrete.game N (payoff blue)

theorem uniformization {N : Set ℕ} (hN : N.Infinite) (blue : SimpleGraph G) :
    ∃ H, H ⊆ N ∧ H.Infinite ∧ ∃ (b : Concrete.Hist N → ℕ) (v : Concrete.Hist N → Bool),
      (exactGame N blue).ValueSystem H b v ∧
      (∀ p q, History.Next q p → b p ≤ b q) ∧
      ((∃ σ : (exactGame N blue).ArchitectStrategy,
          (exactGame N blue).ArchitectWins H b σ
            (History.initial (Position.Next N) Position.initial)) ∨
        (exactGame N blue).AllBuilderWins H b
          (History.initial (Position.Next N) Position.initial)) :=
  Concrete.uniformization hN (payoff blue)

#print axioms winning_iff
#print axioms uniformization

end Erdos591.Positive.Game.Payoff
