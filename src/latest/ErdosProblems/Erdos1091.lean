/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import Mathlib.Combinatorics.SimpleGraph.Walk.Chord
import Mathlib.Combinatorics.SimpleGraph.Walk.Decomp
import Mathlib.Combinatorics.SimpleGraph.Trails
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated
import Mathlib.Tactic
import ErdosProblems.Erdos127.CriticalClique
import ErdosProblems.Erdos1091.Brooks
import ErdosProblems.Erdos1091.VossCase2
import ErdosProblems.Erdos1091.VossCase2b
import ErdosProblems.Erdos1091.VossCase3
import ErdosProblems.Erdos1091.VossCase1Triangle
import ErdosProblems.Erdos1091.VossInnerParity
import ErdosProblems.Erdos1091.VossCase1
import ErdosProblems.Erdos58.Critical
import ErdosProblems.Erdos744

/-!
# Erdős Problem 1091

Voss proved that every finite `K₄`-free graph of chromatic number four
contains an odd cycle with at least two chords.  Alexeev, Putterman,
Sawhney, Sellke, and Valiant later disproved the proposed unbounded
strengthening by constructing arbitrarily large four-critical graphs in
which every cycle has at most ten chords.

Both conclusions are proved below, together with a fully four-critical
counterexample family on exactly `20*m+31` vertices. The affirmative proof
uses Voss's maximal-ear analysis and a local coloring extension for the
triangular prism. The final theorem is `erdos_1091_resolution`.
Cycles are Mathlib closed walks
satisfying `Walk.IsCycle`; chords use Mathlib's `Walk.IsChord` predicate and
are counted as unordered edges in `Sym2 V`.
-/

open Filter SimpleGraph

namespace Erdos1091

universe u

namespace Walk

variable {V : Type u} {G : SimpleGraph V} {u v : V}

/-- The finite set of chords of a walk in a finite ambient graph. -/
noncomputable def chordFinset [Fintype V] (p : G.Walk u v) : Finset (Sym2 V) := by
  classical
  exact {e ∈ G.edgeFinset | p.IsChord e}

@[simp]
theorem mem_chordFinset [Fintype V] (p : G.Walk u v) (e : Sym2 V) :
    e ∈ chordFinset p ↔ p.IsChord e := by
  classical
  simp only [chordFinset, Finset.mem_filter, SimpleGraph.mem_edgeFinset]
  constructor
  · exact fun h ↦ h.2
  · exact fun h ↦ ⟨h.1, h⟩

/-- The number of ambient-graph chords of a walk. -/
noncomputable def chordCount [Fintype V] (p : G.Walk u v) : ℕ :=
  (chordFinset p).card

theorem chordCount_eq_zero_iff [Fintype V] (p : G.Walk u v) :
    chordCount p = 0 ↔ p.IsChordless := by
  classical
  simp only [chordCount, Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem,
    mem_chordFinset, SimpleGraph.Walk.IsChordless]

end Walk

/-- Passing a walk to a supergraph preserves every old chord, so its ambient
chord count can only increase. -/
theorem chordCount_transfer_mono {V : Type u} [Fintype V]
    {G H : SimpleGraph V} (hHG : H ≤ G) {a b : V} (p : H.Walk a b) :
    Walk.chordCount p ≤
      Walk.chordCount (p.transfer G fun e he ↦
        edgeSet_mono hHG (p.edges_subset_edgeSet he)) := by
  classical
  let q : G.Walk a b := p.transfer G fun e he ↦
    edgeSet_mono hHG (p.edges_subset_edgeSet he)
  apply Finset.card_le_card
  intro e he
  rw [Walk.mem_chordFinset] at he ⊢
  refine ⟨edgeSet_mono hHG he.1, ?_, ?_⟩
  · simpa [q] using he.2.1
  · simpa [q] using he.2.2

/-- A finite graph contains an odd cycle having at least `d` chords. -/
def HasOddCycleWithAtLeastChords {V : Type u} [Fintype V]
    (G : SimpleGraph V) (d : ℕ) : Prop :=
  ∃ (u : V) (p : G.Walk u u), p.IsCycle ∧ Odd p.length ∧ d ≤ Walk.chordCount p

/-- Voss's explicit pair of distinct chords is equivalent to the numerical
two-chord threshold used in the problem statement. -/
theorem hasOddCycleWithAtLeastChords_two_iff {V : Type u} [Fintype V]
    (G : SimpleGraph V) :
    HasOddCycleWithAtLeastChords G 2 ↔ Voss.HasOddCycleWithTwoChords G := by
  classical
  constructor
  · rintro ⟨z, C, hC, hodd, hcount⟩
    have hcard : 1 < (Walk.chordFinset C).card := by
      change 2 ≤ (Walk.chordFinset C).card at hcount
      omega
    obtain ⟨e, he, f, hf, hef⟩ := Finset.one_lt_card.mp hcard
    exact ⟨z, C, hC, hodd, e, f, hef,
      (Walk.mem_chordFinset C e).mp he, (Walk.mem_chordFinset C f).mp hf⟩
  · rintro ⟨z, C, hC, hodd, e, f, hef, he, hf⟩
    refine ⟨z, C, hC, hodd, ?_⟩
    have hcard : 1 < (Walk.chordFinset C).card := Finset.one_lt_card.mpr
      ⟨e, (Walk.mem_chordFinset C e).mpr he,
        f, (Walk.mem_chordFinset C f).mpr hf, hef⟩
    change 2 ≤ (Walk.chordFinset C).card
    omega

/-- A witnessed odd chorded cycle in a spanning subgraph remains such a
cycle in every supergraph. -/
theorem hasOddCycleWithAtLeastChords_mono {V : Type u} [Fintype V]
    {G H : SimpleGraph V} (hHG : H ≤ G) {d : ℕ}
    (h : HasOddCycleWithAtLeastChords H d) :
    HasOddCycleWithAtLeastChords G d := by
  obtain ⟨u, p, hp, hodd, hchords⟩ := h
  let q : G.Walk u u := p.transfer G fun e he ↦
    edgeSet_mono hHG (p.edges_subset_edgeSet he)
  refine ⟨u, q, ?_, ?_, hchords.trans (chordCount_transfer_mono hHG p)⟩
  · exact hp.transfer _
  · simpa [q] using hodd

/-- Every cycle of the finite graph has at most `d` chords. -/
def CyclesHaveAtMostChords {V : Type u} [Fintype V]
    (G : SimpleGraph V) (d : ℕ) : Prop :=
  ∀ (u : V) (p : G.Walk u u), p.IsCycle → Walk.chordCount p ≤ d

/-- Deleting edges cannot increase the chord count of any surviving cycle. -/
theorem cyclesHaveAtMostChords_of_le {V : Type u} [Fintype V]
    {G H : SimpleGraph V} {d : ℕ} (hHG : H ≤ G) (hG : CyclesHaveAtMostChords G d) :
    CyclesHaveAtMostChords H d := by
  intro u p hp
  let q : G.Walk u u := p.transfer G fun e he =>
    edgeSet_mono hHG (p.edges_subset_edgeSet he)
  exact (chordCount_transfer_mono hHG p).trans (hG u q (hp.transfer _))

/-- The graph has chromatic number exactly four. -/
def ChromaticFour {V : Type u} (G : SimpleGraph V) : Prop :=
  G.chromaticNumber = (4 : ℕ∞)

/-- Every induced subgraph on at most `r` vertices is three-colorable. -/
def LocallyThreeColorable {V : Type u} [Fintype V]
    (G : SimpleGraph V) (r : ℕ) : Prop :=
  ∀ s : Finset V, s.card ≤ r →
    (G.induce (s : Set V)).chromaticNumber ≤ (3 : ℕ∞)

/-- The proposed quantitative strengthening in Problem 1091. -/
def QuantitativeGuarantee (f : ℕ → ℕ) : Prop :=
  Tendsto f atTop atTop ∧
    ∀ (r n : ℕ) (G : SimpleGraph (Fin n)),
      ChromaticFour G →
      LocallyThreeColorable G r →
      HasOddCycleWithAtLeastChords G (f r)

namespace Counterexample

/-- The leaves consist of the exceptional left leaf, three ordinary leaves
at each spine block, and the exceptional right leaf. -/
abbrev LeafId (m : ℕ) := Unit ⊕ ((Fin (m + 1) × Fin 3) ⊕ Unit)

def leftLeaf (m : ℕ) : LeafId m := Sum.inl ()
def regularLeaf (m : ℕ) (i : Fin (m + 1)) (s : Fin 3) : LeafId m :=
  Sum.inr (Sum.inl (i, s))
def rightLeaf (m : ℕ) : LeafId m := Sum.inr (Sum.inr ())

/-- The APSSV graph has one hub, `m+1` spine pentagons, and one pentagon
for every leaf identifier. -/
abbrev Vertex (m : ℕ) :=
  Unit ⊕ ((Fin (m + 1) × Fin 5) ⊕ (LeafId m × Fin 5))

def hub (m : ℕ) : Vertex m := Sum.inl ()
def spine (m : ℕ) (i : Fin (m + 1)) (x : Fin 5) : Vertex m :=
  Sum.inr (Sum.inl (i, x))
def leaf (m : ℕ) (l : LeafId m) (x : Fin 5) : Vertex m :=
  Sum.inr (Sum.inr (l, x))

def regularPosition : Fin 3 → Fin 5 := ![1, 3, 4]

def attachmentBlock (m : ℕ) : LeafId m → Fin (m + 1)
  | Sum.inl _ => 0
  | Sum.inr (Sum.inl p) => p.1
  | Sum.inr (Sum.inr _) => ⟨m, Nat.lt_succ_self m⟩

def attachmentPosition (m : ℕ) : LeafId m → Fin 5
  | Sum.inl _ => 0
  | Sum.inr (Sum.inl p) => regularPosition p.2
  | Sum.inr (Sum.inr _) => 2

/-- Adjacency between two vertices on the spine.  Besides rim edges there
is one bridge from position `2` of block `i` to position `0` of block
`i+1`. -/
def spineAdjacent {m : ℕ} (i : Fin (m + 1)) (x : Fin 5)
    (j : Fin (m + 1)) (y : Fin 5) : Prop :=
  (i = j ∧ (cycleGraph 5).Adj x y) ∨
    (i.val + 1 = j.val ∧ x = 2 ∧ y = 0) ∨
    (j.val + 1 = i.val ∧ y = 2 ∧ x = 0)

theorem spineAdjacent_symm {m : ℕ} {i j : Fin (m + 1)} {x y : Fin 5} :
    spineAdjacent i x j y → spineAdjacent j y i x := by
  rintro (⟨rfl, h⟩ | ⟨hij, rfl, rfl⟩ | ⟨hji, rfl, rfl⟩)
  · exact Or.inl ⟨rfl, h.symm⟩
  · exact Or.inr (Or.inr ⟨hij, rfl, rfl⟩)
  · exact Or.inr (Or.inl ⟨hji, rfl, rfl⟩)

theorem not_spineAdjacent_self {m : ℕ} (i : Fin (m + 1)) (x : Fin 5) :
    ¬spineAdjacent i x i x := by
  rintro (⟨_, h⟩ | ⟨_, hx, hy⟩ | ⟨_, hx, hy⟩)
  · exact h.ne rfl
  · omega
  · omega

def spineLeafAdjacent {m : ℕ} (i : Fin (m + 1)) (x : Fin 5)
    (l : LeafId m) (y : Fin 5) : Prop :=
  i = attachmentBlock m l ∧ x = attachmentPosition m l ∧
    y = attachmentPosition m l

/-- The adjacency relation of the APSSV graph, written by vertex kind so
that all later proofs can eliminate an edge without unpacking `Sym2`. -/
def adjacent (m : ℕ) : Vertex m → Vertex m → Prop
  | Sum.inl _, Sum.inl _ => False
  | Sum.inl _, Sum.inr (Sum.inl _) => False
  | Sum.inl _, Sum.inr (Sum.inr (l, x)) => x ≠ attachmentPosition m l
  | Sum.inr (Sum.inl _), Sum.inl _ => False
  | Sum.inr (Sum.inl (i, x)), Sum.inr (Sum.inl (j, y)) => spineAdjacent i x j y
  | Sum.inr (Sum.inl (i, x)), Sum.inr (Sum.inr (l, y)) => spineLeafAdjacent i x l y
  | Sum.inr (Sum.inr (l, x)), Sum.inl _ => x ≠ attachmentPosition m l
  | Sum.inr (Sum.inr (l, x)), Sum.inr (Sum.inl (i, y)) => spineLeafAdjacent i y l x
  | Sum.inr (Sum.inr (l, x)), Sum.inr (Sum.inr (k, y)) =>
      l = k ∧ (cycleGraph 5).Adj x y

theorem adjacent_symm (m : ℕ) : Std.Symm (adjacent m) := by
  constructor
  intro a b hab
  rcases a with a | (a | a) <;> rcases b with b | (b | b)
  · exact hab.elim
  · exact hab.elim
  · exact hab
  · exact hab.elim
  · exact spineAdjacent_symm hab
  · exact hab
  · exact hab
  · exact hab
  · exact ⟨hab.1.symm, hab.2.symm⟩

theorem adjacent_loopless (m : ℕ) : Std.Irrefl (adjacent m) := by
  constructor
  intro a
  rcases a with a | (a | a)
  · exact id
  · exact not_spineAdjacent_self a.1 a.2
  · exact fun h ↦ h.2.ne rfl

/-- The explicit graph used by Alexeev--Putterman--Sawhney--Sellke--Valiant. -/
def graph (m : ℕ) : SimpleGraph (Vertex m) where
  Adj := adjacent m
  symm := adjacent_symm m
  loopless := adjacent_loopless m

noncomputable instance (m : ℕ) : DecidableRel (graph m).Adj := fun _ _ ↦
  Classical.propDecidable _

noncomputable instance (m : ℕ) : DecidableEq (Vertex m) := Classical.decEq _

@[simp] theorem hub_adj_leaf_iff (m : ℕ) (l : LeafId m) (x : Fin 5) :
    (graph m).Adj (hub m) (leaf m l x) ↔ x ≠ attachmentPosition m l := Iff.rfl

@[simp] theorem leaf_adj_leaf_iff (m : ℕ) (l k : LeafId m) (x y : Fin 5) :
    (graph m).Adj (leaf m l x) (leaf m k y) ↔
      l = k ∧ (cycleGraph 5).Adj x y := Iff.rfl

@[simp] theorem spine_adj_leaf_iff (m : ℕ) (i : Fin (m + 1)) (x : Fin 5)
    (l : LeafId m) (y : Fin 5) :
    (graph m).Adj (spine m i x) (leaf m l y) ↔ spineLeafAdjacent i x l y := Iff.rfl

@[simp] theorem hub_not_adj_spine (m : ℕ) (i : Fin (m + 1)) (x : Fin 5) :
    ¬(graph m).Adj (hub m) (spine m i x) := by simp [graph, adjacent, hub, spine]

theorem card_vertex (m : ℕ) : Fintype.card (Vertex m) = 20 * m + 31 := by
  simp [Vertex, LeafId]
  omega

/-- In a three-coloring, if four vertices of a pentagon avoid a fixed
color, then the fifth vertex has that color. -/
theorem finThree_pentagon_forcing (t : Fin 5) (a : Fin 3) (c : Fin 5 → Fin 3)
    (hcycle : ∀ x y, (cycleGraph 5).Adj x y → c x ≠ c y)
    (havoid : ∀ x, x ≠ t → c x ≠ a) : c t = a := by
  have h01 := hcycle 0 1 (by decide)
  have h12 := hcycle 1 2 (by decide)
  have h23 := hcycle 2 3 (by decide)
  have h34 := hcycle 3 4 (by decide)
  have h40 := hcycle 4 0 (by decide)
  fin_cases t
  · have ha1 := havoid 1 (by decide)
    have ha2 := havoid 2 (by decide)
    have ha3 := havoid 3 (by decide)
    have ha4 := havoid 4 (by decide)
    change c 0 = a
    apply Fin.ext
    omega
  · have ha0 := havoid 0 (by decide)
    have ha2 := havoid 2 (by decide)
    have ha3 := havoid 3 (by decide)
    have ha4 := havoid 4 (by decide)
    change c 1 = a
    apply Fin.ext
    omega
  · have ha0 := havoid 0 (by decide)
    have ha1 := havoid 1 (by decide)
    have ha3 := havoid 3 (by decide)
    have ha4 := havoid 4 (by decide)
    change c 2 = a
    apply Fin.ext
    omega
  · have ha0 := havoid 0 (by decide)
    have ha1 := havoid 1 (by decide)
    have ha2 := havoid 2 (by decide)
    have ha4 := havoid 4 (by decide)
    change c 3 = a
    apply Fin.ext
    omega
  · have ha0 := havoid 0 (by decide)
    have ha1 := havoid 1 (by decide)
    have ha2 := havoid 2 (by decide)
    have ha3 := havoid 3 (by decide)
    change c 4 = a
    apply Fin.ext
    omega

/-- The attachment vertex of every leaf receives the hub color in any
three-coloring. -/
theorem leaf_forcing (m : ℕ) (c : (graph m).Coloring (Fin 3)) (l : LeafId m) :
    c (leaf m l (attachmentPosition m l)) = c (hub m) := by
  apply finThree_pentagon_forcing (attachmentPosition m l) (c (hub m))
    (fun x ↦ c (leaf m l x))
  · intro x y hxy
    exact c.valid ((leaf_adj_leaf_iff m l l x y).2 ⟨rfl, hxy⟩)
  · intro x hxt
    exact c.valid ((hub_adj_leaf_iff m l x).2 hxt) |>.symm

theorem attachment_spine_avoids (m : ℕ) (c : (graph m).Coloring (Fin 3))
    (l : LeafId m) :
    c (spine m (attachmentBlock m l) (attachmentPosition m l)) ≠ c (hub m) := by
  have h := c.valid ((spine_adj_leaf_iff m (attachmentBlock m l)
    (attachmentPosition m l) l (attachmentPosition m l)).2 ⟨rfl, rfl, rfl⟩)
  rwa [leaf_forcing m c l] at h

theorem regular_spine_avoids (m : ℕ) (c : (graph m).Coloring (Fin 3))
    (i : Fin (m + 1)) (s : Fin 3) :
    c (spine m i (regularPosition s)) ≠ c (hub m) := by
  simpa [regularLeaf, attachmentBlock, attachmentPosition] using
    attachment_spine_avoids m c (regularLeaf m i s)

theorem left_spine_avoids (m : ℕ) (c : (graph m).Coloring (Fin 3)) :
    c (spine m 0 0) ≠ c (hub m) := by
  simpa [leftLeaf, attachmentBlock, attachmentPosition] using
    attachment_spine_avoids m c (leftLeaf m)

theorem right_spine_avoids (m : ℕ) (c : (graph m).Coloring (Fin 3)) :
    c (spine m ⟨m, Nat.lt_succ_self m⟩ 2) ≠ c (hub m) := by
  simpa [rightLeaf, attachmentBlock, attachmentPosition] using
    attachment_spine_avoids m c (rightLeaf m)

theorem spine_c_forcing (m : ℕ) (c : (graph m).Coloring (Fin 3))
    (i : Fin (m + 1)) (ha : c (spine m i 0) ≠ c (hub m)) :
    c (spine m i 2) = c (hub m) := by
  apply finThree_pentagon_forcing 2 (c (hub m)) (fun x ↦ c (spine m i x))
  · intro x y hxy
    exact c.valid (show spineAdjacent i x i y from Or.inl ⟨rfl, hxy⟩)
  · intro x hx
    fin_cases x
    · exact ha
    · simpa [regularPosition] using regular_spine_avoids m c i 0
    · exact (hx rfl).elim
    · simpa [regularPosition] using regular_spine_avoids m c i 1
    · simpa [regularPosition] using regular_spine_avoids m c i 2

theorem terminal_a_forcing (m : ℕ) (c : (graph m).Coloring (Fin 3)) :
    c (spine m ⟨m, Nat.lt_succ_self m⟩ 0) = c (hub m) := by
  let i : Fin (m + 1) := ⟨m, Nat.lt_succ_self m⟩
  apply finThree_pentagon_forcing 0 (c (hub m)) (fun x ↦ c (spine m i x))
  · intro x y hxy
    exact c.valid (show spineAdjacent i x i y from Or.inl ⟨rfl, hxy⟩)
  · intro x hx
    fin_cases x
    · exact (hx rfl).elim
    · simpa [i, regularPosition] using regular_spine_avoids m c i 0
    · simpa [i] using right_spine_avoids m c
    · simpa [i, regularPosition] using regular_spine_avoids m c i 1
    · simpa [i, regularPosition] using regular_spine_avoids m c i 2

theorem not_colorable_three (m : ℕ) : ¬(graph m).Colorable 3 := by
  rintro ⟨c⟩
  have hA : ∀ k : ℕ, ∀ hk : k ≤ m,
      c (spine m ⟨k, Nat.lt_succ_of_le hk⟩ 0) ≠ c (hub m) := by
    intro k
    induction k with
    | zero =>
        intro hk
        simpa using left_spine_avoids m c
    | succ k ih =>
        intro hk
        have hk' : k ≤ m := le_trans (Nat.le_succ k) hk
        let i : Fin (m + 1) := ⟨k, Nat.lt_succ_of_le hk'⟩
        let j : Fin (m + 1) := ⟨k + 1, Nat.lt_succ_of_le hk⟩
        have hia : c (spine m i 0) ≠ c (hub m) := by
          simpa [i] using ih hk'
        have hic : c (spine m i 2) = c (hub m) := spine_c_forcing m c i hia
        have hedge : (graph m).Adj (spine m i 2) (spine m j 0) := by
          exact Or.inr (Or.inl ⟨by simp [i, j], rfl, rfl⟩)
        have hcolors := c.valid hedge
        rw [hic] at hcolors
        simpa [j] using hcolors.symm
  have havoid := hA m le_rfl
  exact havoid (terminal_a_forcing m c)

def spineColor : Fin 5 → Fin 4 := ![0, 1, 2, 0, 1]
def leafColor : Fin 5 → Fin 4 := ![1, 2, 0, 1, 2]

theorem spineColor_valid :
    ∀ x y, (cycleGraph 5).Adj x y → spineColor x ≠ spineColor y := by decide

theorem leafColor_valid :
    ∀ x y, (cycleGraph 5).Adj x y → leafColor x ≠ leafColor y := by decide

theorem attachment_colors_differ : ∀ x, spineColor x ≠ leafColor x := by decide

def fourColor (m : ℕ) : Vertex m → Fin 4
  | Sum.inl _ => 3
  | Sum.inr (Sum.inl (_, x)) => spineColor x
  | Sum.inr (Sum.inr (_, x)) => leafColor x

/-- A concrete four-coloring: the hub gets color `3`, all spine rims use
`0,1,2,0,1`, and all leaf rims use its cyclic color shift. -/
def fourColoring (m : ℕ) : (graph m).Coloring (Fin 4) := by
  apply SimpleGraph.Coloring.mk (fourColor m)
  intro a b hab
  rcases a with a | (a | a) <;> rcases b with b | (b | b)
  · exact hab.elim
  · exact hab.elim
  · rcases b with ⟨l, x⟩
    fin_cases x <;> simp [fourColor, leafColor]
  · exact hab.elim
  · rcases a with ⟨i, x⟩
    rcases b with ⟨j, y⟩
    rcases hab with ⟨rfl, hxy⟩ | ⟨hij, rfl, rfl⟩ | ⟨hji, rfl, rfl⟩
    · exact spineColor_valid x y hxy
    · simp [fourColor, spineColor]
    · simp [fourColor, spineColor]
  · rcases a with ⟨i, x⟩
    rcases b with ⟨l, y⟩
    rcases hab with ⟨_, rfl, rfl⟩
    exact attachment_colors_differ _
  · rcases a with ⟨l, x⟩
    fin_cases x <;> simp [fourColor, leafColor]
  · rcases a with ⟨l, x⟩
    rcases b with ⟨i, y⟩
    rcases hab with ⟨_, rfl, rfl⟩
    exact (attachment_colors_differ _).symm
  · rcases a with ⟨l, x⟩
    rcases b with ⟨k, y⟩
    exact leafColor_valid x y hab.2

theorem colorable_four (m : ℕ) : (graph m).Colorable 4 :=
  ⟨fourColoring m⟩

theorem chromatic_four (m : ℕ) : ChromaticFour (graph m) := by
  exact SimpleGraph.chromaticNumber_eq_iff_colorable_not_colorable.mpr
    ⟨colorable_four m, not_colorable_three m⟩

theorem fourColor_eq_three_iff (m : ℕ) (v : Vertex m) :
    fourColor m v = 3 ↔ v = hub m := by
  rcases v with a | (a | a)
  · simp [fourColor, hub]
  · rcases a with ⟨i, x⟩
    fin_cases x <;> simp [fourColor, hub, spineColor]
  · rcases a with ⟨l, x⟩
    fin_cases x <;> simp [fourColor, hub, leafColor]

theorem adj_hub_iff_exists_leaf (m : ℕ) (v : Vertex m) :
    (graph m).Adj (hub m) v ↔
      ∃ (l : LeafId m) (x : Fin 5), x ≠ attachmentPosition m l ∧ v = leaf m l x := by
  rcases v with a | (a | a)
  · simp [graph, adjacent, hub, leaf]
  · rcases a with ⟨i, x⟩
    simp [graph, adjacent, hub, spine, leaf]
  · rcases a with ⟨l, x⟩
    constructor
    · intro h
      exact ⟨l, x, h, rfl⟩
    · rintro ⟨k, y, hy, hEq⟩
      cases hEq
      exact hy

theorem cycleGraph_five_no_triangle :
    ¬∃ x y z : Fin 5, (cycleGraph 5).Adj x y ∧
      (cycleGraph 5).Adj x z ∧ (cycleGraph 5).Adj y z := by decide

theorem no_triangle_among_hub_neighbors (m : ℕ) (v₀ v₁ v₂ : Vertex m)
    (hn₀ : (graph m).Adj (hub m) v₀)
    (hn₁ : (graph m).Adj (hub m) v₁)
    (hn₂ : (graph m).Adj (hub m) v₂)
    (h₀₁ : (graph m).Adj v₀ v₁)
    (h₀₂ : (graph m).Adj v₀ v₂)
    (h₁₂ : (graph m).Adj v₁ v₂) : False := by
  obtain ⟨l₀, x₀, _, rfl⟩ := (adj_hub_iff_exists_leaf m v₀).mp hn₀
  obtain ⟨l₁, x₁, _, rfl⟩ := (adj_hub_iff_exists_leaf m v₁).mp hn₁
  obtain ⟨l₂, x₂, _, rfl⟩ := (adj_hub_iff_exists_leaf m v₂).mp hn₂
  apply cycleGraph_five_no_triangle
  exact ⟨x₀, x₁, x₂, (leaf_adj_leaf_iff m l₀ l₁ x₀ x₁).mp h₀₁ |>.2,
    (leaf_adj_leaf_iff m l₀ l₂ x₀ x₂).mp h₀₂ |>.2,
    (leaf_adj_leaf_iff m l₁ l₂ x₁ x₂).mp h₁₂ |>.2⟩

theorem cliqueFree_four (m : ℕ) : (graph m).CliqueFree 4 := by
  classical
  unfold SimpleGraph.CliqueFree
  intro s hs
  have hsurj := SimpleGraph.Coloring.surjOn_of_card_le_isClique hs.isClique
    (by simp [hs.card_eq]) (fourColoring m)
  obtain ⟨v, hvs, hcv⟩ := hsurj (Set.mem_univ (3 : Fin 4))
  have hv : v = hub m := (fourColor_eq_three_iff m v).mp hcv
  subst v
  have ht : (graph m).IsNClique 3 (s.erase (hub m)) := by
    simpa using hs.erase_of_mem hvs
  obtain ⟨v₀, v₁, v₂, h₀₁ne, h₀₂ne, h₁₂ne, hset⟩ :=
    Finset.card_eq_three.mp ht.card_eq
  have hv₀ : v₀ ∈ s.erase (hub m) := by simp [hset]
  have hv₁ : v₁ ∈ s.erase (hub m) := by simp [hset]
  have hv₂ : v₂ ∈ s.erase (hub m) := by simp [hset]
  have hn₀ : (graph m).Adj (hub m) v₀ :=
    hs.isClique hvs (Finset.mem_of_mem_erase hv₀) (Finset.ne_of_mem_erase hv₀).symm
  have hn₁ : (graph m).Adj (hub m) v₁ :=
    hs.isClique hvs (Finset.mem_of_mem_erase hv₁) (Finset.ne_of_mem_erase hv₁).symm
  have hn₂ : (graph m).Adj (hub m) v₂ :=
    hs.isClique hvs (Finset.mem_of_mem_erase hv₂) (Finset.ne_of_mem_erase hv₂).symm
  have h₀₁ : (graph m).Adj v₀ v₁ := ht.isClique hv₀ hv₁ h₀₁ne
  have h₀₂ : (graph m).Adj v₀ v₂ := ht.isClique hv₀ hv₂ h₀₂ne
  have h₁₂ : (graph m).Adj v₁ v₂ := ht.isClique hv₁ hv₂ h₁₂ne
  exact no_triangle_among_hub_neighbors m v₀ v₁ v₂ hn₀ hn₁ hn₂ h₀₁ h₀₂ h₁₂

def spineHom (m : ℕ) (i : Fin (m + 1)) : cycleGraph 5 →g graph m :=
  ⟨spine m i, fun {_ _} h ↦ Or.inl ⟨rfl, h⟩⟩

def leafHom (m : ℕ) (l : LeafId m) : cycleGraph 5 →g graph m :=
  ⟨leaf m l, fun {_ _} h ↦ ⟨rfl, h⟩⟩

theorem spine_same_block_reachable (m : ℕ) (i : Fin (m + 1)) (x y : Fin 5) :
    (graph m).Reachable (spine m i x) (spine m i y) :=
  (cycleGraph_connected (n := 4) x y).map (spineHom m i)

theorem leaf_same_block_reachable (m : ℕ) (l : LeafId m) (x y : Fin 5) :
    (graph m).Reachable (leaf m l x) (leaf m l y) :=
  (cycleGraph_connected (n := 4) x y).map (leafHom m l)

theorem spine_root_reachable_nat (m : ℕ) :
    ∀ k : ℕ, ∀ hk : k ≤ m, ∀ x : Fin 5,
      (graph m).Reachable (spine m 0 0)
        (spine m ⟨k, Nat.lt_succ_of_le hk⟩ x) := by
  intro k
  induction k with
  | zero =>
      intro hk x
      simpa using spine_same_block_reachable m (0 : Fin (m + 1)) 0 x
  | succ k ih =>
      intro hk x
      have hk' : k ≤ m := le_trans (Nat.le_succ k) hk
      let i : Fin (m + 1) := ⟨k, Nat.lt_succ_of_le hk'⟩
      let j : Fin (m + 1) := ⟨k + 1, Nat.lt_succ_of_le hk⟩
      have hroot : (graph m).Reachable (spine m 0 0) (spine m i 2) := by
        simpa [i] using ih hk' (2 : Fin 5)
      have hbridge : (graph m).Adj (spine m i 2) (spine m j 0) :=
        Or.inr (Or.inl ⟨by simp [i, j], rfl, rfl⟩)
      have hrim := spine_same_block_reachable m j 0 x
      simpa [j] using hroot.trans (hbridge.reachable.trans hrim)

theorem spine_root_reachable (m : ℕ) (i : Fin (m + 1)) (x : Fin 5) :
    (graph m).Reachable (spine m 0 0) (spine m i x) := by
  simpa [Fin.ext_iff] using spine_root_reachable_nat m i.val (Nat.le_of_lt_succ i.isLt) x

theorem nonhub_root_reachable (m : ℕ) (v : Vertex m) (hv : v ≠ hub m) :
    (graph m).Reachable (spine m 0 0) v := by
  rcases v with a | (a | a)
  · exact (hv (by simp [hub])).elim
  · exact spine_root_reachable m a.1 a.2
  · rcases a with ⟨l, x⟩
    have hroot := spine_root_reachable m (attachmentBlock m l) (attachmentPosition m l)
    have hatt : (graph m).Adj
        (spine m (attachmentBlock m l) (attachmentPosition m l))
        (leaf m l (attachmentPosition m l)) := ⟨rfl, rfl, rfl⟩
    exact hroot.trans (hatt.reachable.trans
      (leaf_same_block_reachable m l (attachmentPosition m l) x))

theorem nonhub_reachable (m : ℕ) (u v : Vertex m)
    (hu : u ≠ hub m) (hv : v ≠ hub m) : (graph m).Reachable u v :=
  (nonhub_root_reachable m u hu).symm.trans (nonhub_root_reachable m v hv)

def leafRimNeighbor (m : ℕ) (l : LeafId m) (x : Fin 5) (v : Vertex m) : Prop :=
  ∃ y : Fin 5, (cycleGraph 5).Adj x y ∧ v = leaf m l y

def spineRimNeighbor (m : ℕ) (i : Fin (m + 1)) (x : Fin 5) (v : Vertex m) : Prop :=
  ∃ y : Fin 5, (cycleGraph 5).Adj x y ∧ v = spine m i y

theorem attachment_injective (m : ℕ) : Function.Injective
    (fun l : LeafId m ↦ (attachmentBlock m l, attachmentPosition m l)) := by
  intro l k h
  rcases l with a | l <;> rcases k with b | k
  · simp
  · rcases k with p | b
    · rcases p with ⟨i, s⟩
      fin_cases s <;> simp [attachmentBlock, attachmentPosition, regularPosition] at h
    · simp [attachmentBlock, attachmentPosition] at h
  · rcases l with p | a
    · rcases p with ⟨i, s⟩
      fin_cases s <;> simp [attachmentBlock, attachmentPosition, regularPosition] at h
    · simp [attachmentBlock, attachmentPosition] at h
  · rcases l with p | a <;> rcases k with q | b
    · rcases p with ⟨i, s⟩
      rcases q with ⟨j, t⟩
      have hij : i = j := congrArg Prod.fst h
      have hregular : Function.Injective regularPosition := by decide
      have hst : s = t := hregular (congrArg Prod.snd h)
      subst j
      subst t
      rfl
    · rcases p with ⟨i, s⟩
      fin_cases s <;> simp [attachmentBlock, attachmentPosition, regularPosition] at h
    · rcases q with ⟨j, t⟩
      fin_cases t <;> simp [attachmentBlock, attachmentPosition, regularPosition] at h
    · simp

theorem attachmentBlock_eq_zero_of_position_eq_zero (m : ℕ) (l : LeafId m)
    (h : attachmentPosition m l = 0) : attachmentBlock m l = 0 := by
  rcases l with a | l
  · rfl
  rcases l with p | b
  · rcases p with ⟨i, s⟩
    fin_cases s <;> simp [attachmentPosition, regularPosition] at h
  · simp [attachmentPosition] at h

theorem attachmentBlock_eq_last_of_position_eq_two (m : ℕ) (l : LeafId m)
    (h : attachmentPosition m l = 2) :
    attachmentBlock m l = ⟨m, Nat.lt_succ_self m⟩ := by
  rcases l with a | l
  · simp [attachmentPosition] at h
  rcases l with p | b
  · rcases p with ⟨i, s⟩
    fin_cases s <;> simp [attachmentPosition, regularPosition] at h
  · rfl

theorem leaf_external_unique (m : ℕ) (l : LeafId m) (x : Fin 5) (v w : Vertex m)
    (hv : (graph m).Adj (leaf m l x) v) (hvr : ¬leafRimNeighbor m l x v)
    (hw : (graph m).Adj (leaf m l x) w) (hwr : ¬leafRimNeighbor m l x w) : v = w := by
  rcases v with a | (a | a) <;> rcases w with b | (b | b)
  all_goals
    simp [graph, adjacent, leaf, spine, hub, leafRimNeighbor, spineLeafAdjacent] at *
  all_goals aesop

theorem spine_external_unique (m : ℕ) (i : Fin (m + 1)) (x : Fin 5) (v w : Vertex m)
    (hv : (graph m).Adj (spine m i x) v) (hvr : ¬spineRimNeighbor m i x v)
    (hw : (graph m).Adj (spine m i x) w) (hwr : ¬spineRimNeighbor m i x w) : v = w := by
  rcases v with a | (a | a) <;> rcases w with b | (b | b)
  · exact hv.elim
  · exact hv.elim
  · exact hv.elim
  · exact hw.elim
  · rcases a with ⟨j, y⟩
    rcases b with ⟨k, z⟩
    simp [graph, adjacent, spine, spineRimNeighbor, spineAdjacent] at hv hvr hw hwr ⊢
    grind
  · rcases a with ⟨j, y⟩
    rcases b with ⟨l, z⟩
    change spineAdjacent i x j y at hv
    change spineLeafAdjacent i x l z at hw
    have hvconn :
        (i.val + 1 = j.val ∧ x = 2 ∧ y = 0) ∨
          (j.val + 1 = i.val ∧ y = 2 ∧ x = 0) := by
      rcases hv with hRim | hnext | hprev
      · exact (hvr ⟨y, hRim.2,
          congrArg (fun q ↦ spine m q y) hRim.1.symm⟩).elim
      · exact Or.inl hnext
      · exact Or.inr hprev
    rcases hw with ⟨hil, hxl, rfl⟩
    rcases hvconn with (⟨hij, hx2, hy0⟩ | ⟨hji, hy2, hx0⟩)
    · have him := attachmentBlock_eq_last_of_position_eq_two m l (hxl.symm.trans hx2)
      have hval := congrArg Fin.val (hil.trans him)
      change i.val = m at hval
      omega
    · have hi0 := attachmentBlock_eq_zero_of_position_eq_zero m l (hxl.symm.trans hx0)
      have hval := congrArg Fin.val (hil.trans hi0)
      change i.val = 0 at hval
      omega
  · exact hw.elim
  · rcases a with ⟨l, z⟩
    rcases b with ⟨j, y⟩
    change spineLeafAdjacent i x l z at hv
    change spineAdjacent i x j y at hw
    have hwconn :
        (i.val + 1 = j.val ∧ x = 2 ∧ y = 0) ∨
          (j.val + 1 = i.val ∧ y = 2 ∧ x = 0) := by
      rcases hw with hRim | hnext | hprev
      · exact (hwr ⟨y, hRim.2,
          congrArg (fun q ↦ spine m q y) hRim.1.symm⟩).elim
      · exact Or.inl hnext
      · exact Or.inr hprev
    rcases hv with ⟨hil, hxl, rfl⟩
    rcases hwconn with (⟨hij, hx2, hy0⟩ | ⟨hji, hy2, hx0⟩)
    · have him := attachmentBlock_eq_last_of_position_eq_two m l (hxl.symm.trans hx2)
      have hval := congrArg Fin.val (hil.trans him)
      change i.val = m at hval
      omega
    · have hi0 := attachmentBlock_eq_zero_of_position_eq_zero m l (hxl.symm.trans hx0)
      have hval := congrArg Fin.val (hil.trans hi0)
      change i.val = 0 at hval
      omega
  · rcases a with ⟨l, y⟩
    rcases b with ⟨k, z⟩
    rcases hv with ⟨hil, hxl, hyl⟩
    rcases hw with ⟨hik, hxk, hzk⟩
    have hpairs : (attachmentBlock m l, attachmentPosition m l) =
        (attachmentBlock m k, attachmentPosition m k) := by
      rw [← hil, ← hik, ← hxl, ← hxk]
    have hlk : l = k := attachment_injective m hpairs
    subst k
    simp_all

theorem degree_le_three_of_rim_partition {V : Type*} [Fintype V]
    [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
    (u : V) (rim : V → Prop) (rimVertices : Finset V)
    (hrim : ∀ v, rim v → v ∈ rimVertices) (hrimCard : rimVertices.card ≤ 2)
    (hexternal : ∀ v w, G.Adj u v → ¬rim v → G.Adj u w → ¬rim w → v = w) :
    G.degree u ≤ 3 := by
  classical
  let N := G.neighborFinset u
  have hR : (N.filter rim).card ≤ 2 := by
    apply le_trans (Finset.card_le_card ?_) hrimCard
    intro v hv
    exact hrim v (Finset.mem_filter.mp hv).2
  have hE : (N.filter fun v ↦ ¬rim v).card ≤ 1 := by
    rw [Finset.card_le_one_iff]
    intro v w hv hw
    obtain ⟨hvN, hvr⟩ := Finset.mem_filter.mp hv
    obtain ⟨hwN, hwr⟩ := Finset.mem_filter.mp hw
    exact hexternal v w (by simpa [N] using hvN) hvr
      (by simpa [N] using hwN) hwr
  have hpart : (N.filter rim).card + (N.filter fun v ↦ ¬rim v).card = N.card :=
    Finset.card_filter_add_card_filter_not rim
  have hN : N.card ≤ 3 := by omega
  change (G.neighborFinset u).card ≤ 3
  simpa only [N] using hN

theorem leaf_degree_le_three (m : ℕ) (l : LeafId m) (x : Fin 5) :
    (graph m).degree (leaf m l x) ≤ 3 := by
  classical
  let R : Finset (Vertex m) :=
    ((cycleGraph 5).neighborFinset x).image (leaf m l)
  apply degree_le_three_of_rim_partition (G := graph m) (leaf m l x)
    (leafRimNeighbor m l x) R
  · rintro v ⟨y, hy, rfl⟩
    exact Finset.mem_image.mpr ⟨y, by simpa using hy, rfl⟩
  · calc
      R.card ≤ ((cycleGraph 5).neighborFinset x).card := Finset.card_image_le
      _ = 2 := by
        rw [SimpleGraph.card_neighborFinset_eq_degree, cycleGraph_degree_three_le]
  · exact leaf_external_unique m l x

theorem spine_degree_le_three (m : ℕ) (i : Fin (m + 1)) (x : Fin 5) :
    (graph m).degree (spine m i x) ≤ 3 := by
  classical
  let R : Finset (Vertex m) :=
    ((cycleGraph 5).neighborFinset x).image (spine m i)
  apply degree_le_three_of_rim_partition (G := graph m) (spine m i x)
    (spineRimNeighbor m i x) R
  · rintro v ⟨y, hy, rfl⟩
    exact Finset.mem_image.mpr ⟨y, by simpa using hy, rfl⟩
  · calc
      R.card ≤ ((cycleGraph 5).neighborFinset x).card := Finset.card_image_le
      _ = 2 := by
        rw [SimpleGraph.card_neighborFinset_eq_degree, cycleGraph_degree_three_le]
  · exact spine_external_unique m i x

theorem nonhub_degree_le_three (m : ℕ) (v : Vertex m) (hv : v ≠ hub m) :
    (graph m).degree v ≤ 3 := by
  rcases v with a | (a | a)
  · exact (hv (by simp [hub])).elim
  · exact spine_degree_le_three m a.1 a.2
  · exact leaf_degree_le_three m a.1 a.2

abbrev NonhubVertex (m : ℕ) := {v : Vertex m // v ≠ hub m}

def nonhubGraph (m : ℕ) : SimpleGraph (NonhubVertex m) :=
  (graph m).induce {v | v ≠ hub m}

def spineNH (m : ℕ) (i : Fin (m + 1)) (x : Fin 5) : NonhubVertex m :=
  ⟨spine m i x, by simp [spine, hub]⟩

def leafNH (m : ℕ) (l : LeafId m) (x : Fin 5) : NonhubVertex m :=
  ⟨leaf m l x, by simp [leaf, hub]⟩

def spineNHHom (m : ℕ) (i : Fin (m + 1)) : cycleGraph 5 →g nonhubGraph m :=
  ⟨spineNH m i, fun {_ _} h ↦ Or.inl ⟨rfl, h⟩⟩

def leafNHHom (m : ℕ) (l : LeafId m) : cycleGraph 5 →g nonhubGraph m :=
  ⟨leafNH m l, fun {_ _} h ↦ ⟨rfl, h⟩⟩

theorem spineNH_same_block_reachable (m : ℕ) (i : Fin (m + 1)) (x y : Fin 5) :
    (nonhubGraph m).Reachable (spineNH m i x) (spineNH m i y) :=
  (cycleGraph_connected (n := 4) x y).map (spineNHHom m i)

theorem leafNH_same_block_reachable (m : ℕ) (l : LeafId m) (x y : Fin 5) :
    (nonhubGraph m).Reachable (leafNH m l x) (leafNH m l y) :=
  (cycleGraph_connected (n := 4) x y).map (leafNHHom m l)

theorem spineNH_root_reachable_nat (m : ℕ) :
    ∀ k : ℕ, ∀ hk : k ≤ m, ∀ x : Fin 5,
      (nonhubGraph m).Reachable (spineNH m 0 0)
        (spineNH m ⟨k, Nat.lt_succ_of_le hk⟩ x) := by
  intro k
  induction k with
  | zero =>
      intro hk x
      simpa using spineNH_same_block_reachable m (0 : Fin (m + 1)) 0 x
  | succ k ih =>
      intro hk x
      have hk' : k ≤ m := le_trans (Nat.le_succ k) hk
      let i : Fin (m + 1) := ⟨k, Nat.lt_succ_of_le hk'⟩
      let j : Fin (m + 1) := ⟨k + 1, Nat.lt_succ_of_le hk⟩
      have hroot : (nonhubGraph m).Reachable (spineNH m 0 0) (spineNH m i 2) := by
        simpa [i] using ih hk' (2 : Fin 5)
      have hbridge : (nonhubGraph m).Adj (spineNH m i 2) (spineNH m j 0) :=
        Or.inr (Or.inl ⟨by simp [i, j], rfl, rfl⟩)
      have hrim := spineNH_same_block_reachable m j 0 x
      simpa [j] using hroot.trans (hbridge.reachable.trans hrim)

theorem spineNH_root_reachable (m : ℕ) (i : Fin (m + 1)) (x : Fin 5) :
    (nonhubGraph m).Reachable (spineNH m 0 0) (spineNH m i x) := by
  simpa [Fin.ext_iff] using
    spineNH_root_reachable_nat m i.val (Nat.le_of_lt_succ i.isLt) x

theorem nonhubGraph_root_reachable (m : ℕ) (v : NonhubVertex m) :
    (nonhubGraph m).Reachable (spineNH m 0 0) v := by
  rcases v with ⟨v, hv⟩
  rcases v with a | (a | a)
  · exact (hv (by simp [hub])).elim
  · exact spineNH_root_reachable m a.1 a.2
  · rcases a with ⟨l, x⟩
    have hroot := spineNH_root_reachable m (attachmentBlock m l) (attachmentPosition m l)
    have hatt : (nonhubGraph m).Adj
        (spineNH m (attachmentBlock m l) (attachmentPosition m l))
        (leafNH m l (attachmentPosition m l)) := ⟨rfl, rfl, rfl⟩
    exact hroot.trans (hatt.reachable.trans
      (leafNH_same_block_reachable m l (attachmentPosition m l) x))

theorem nonhubGraph_connected (m : ℕ) : (nonhubGraph m).Connected := by
  let : Nonempty (NonhubVertex m) := ⟨spineNH m 0 0⟩
  exact ⟨fun u v ↦
    (nonhubGraph_root_reachable m u).symm.trans (nonhubGraph_root_reachable m v)⟩

theorem walk_exists_boundary_edge {V : Type*} {G : SimpleGraph V} (S : Set V)
    {u v : V} (p : G.Walk u v) (hu : u ∈ S) (hv : v ∉ S) :
    ∃ a b, a ∈ S ∧ b ∉ S ∧ G.Adj a b := by
  induction p with
  | nil => exact (hv hu).elim
  | @cons u w v huw p ih =>
      by_cases hw : w ∈ S
      · exact ih hw hv
      · exact ⟨u, w, hu, hw, huw⟩

theorem edge_mem_of_walk_crosses_cut {V : Type*} {G : SimpleGraph V}
    (P : V → Prop) (e : Sym2 V)
    (hcross : ∀ {a b}, G.Adj a b → P a → ¬P b → s(a, b) = e)
    {u v : V} (p : G.Walk u v) (hu : P u) (hv : ¬P v) : e ∈ p.edges := by
  induction p with
  | nil => exact (hv hu).elim
  | @cons u w v huw p ih =>
      by_cases hw : P w
      · simp only [SimpleGraph.Walk.edges_cons, List.mem_cons]
        exact Or.inr (ih hw hv)
      · have he := hcross huw hu hw
        simp only [SimpleGraph.Walk.edges_cons, List.mem_cons]
        exact Or.inl he.symm

theorem IsPath.avoids_cut_of_endpoints (m : ℕ) {u v : NonhubVertex m}
    (P : NonhubVertex m → Prop) (e : Sym2 (NonhubVertex m))
    (hcross : ∀ {a b}, (nonhubGraph m).Adj a b → P a → ¬P b → s(a, b) = e)
    (p : (nonhubGraph m).Walk u v) (hp : p.IsPath) (hu : ¬P u) (hv : ¬P v) :
    ∀ x ∈ p.support, ¬P x := by
  intro x hx hPx
  let q₁ := p.takeUntil x hx
  let q₂ := p.dropUntil x hx
  have he₁ : e ∈ q₁.edges := by
    have hcross' : ∀ {a b}, (nonhubGraph m).Adj a b →
        (¬P a) → ¬(¬P b) → s(a, b) = e := by
      intro a b hab ha hb
      have hPb : P b := Classical.byContradiction fun h ↦ hb h
      simpa [Sym2.eq_swap] using hcross hab.symm hPb ha
    exact edge_mem_of_walk_crosses_cut (fun z ↦ ¬P z) e hcross' q₁ hu (by simpa)
  have he₂ : e ∈ q₂.edges := edge_mem_of_walk_crosses_cut P e hcross q₂ hPx hv
  have hpEq : p = q₁.append q₂ := by simp [q₁, q₂]
  have htrail := hp.isTrail
  rw [SimpleGraph.Walk.isTrail_def, hpEq, SimpleGraph.Walk.edges_append] at htrail
  exact List.disjoint_of_nodup_append htrail he₁ he₂

/-- A simple cycle based outside one side of a cut cannot visit that side
when the cut has a unique crossing edge. -/
theorem IsCycle.avoids_unique_cut (m : ℕ) {u : NonhubVertex m}
    (P : NonhubVertex m → Prop) (e : Sym2 (NonhubVertex m))
    (hcross : ∀ {a b}, (nonhubGraph m).Adj a b → P a → ¬P b → s(a, b) = e)
    (p : (nonhubGraph m).Walk u u) (hp : p.IsCycle) (hu : ¬P u) :
    ∀ x ∈ p.support, ¬P x := by
  intro x hx hPx
  have hnil : ¬p.Nil := hp.not_nil
  have hsupp : p.support = u :: p.tail.support := by
    exact (p.cons_support_tail hnil).symm
  have hxTail : x ∈ p.tail.support := by
    rw [hsupp] at hx
    rcases List.mem_cons.mp hx with (rfl | hx)
    · exact (hu hPx).elim
    · exact hx
  by_cases hsnd : P p.snd
  · have heFirst : s(u, p.snd) = e := by
      simpa [Sym2.eq_swap] using hcross (p.adj_snd hnil).symm hsnd hu
    have heTail : e ∈ p.tail.edges :=
      edge_mem_of_walk_crosses_cut P e hcross p.tail hsnd hu
    have htrail := hp.isTrail.edges_nodup
    rw [← p.cons_tail_eq hnil, SimpleGraph.Walk.edges_cons, heFirst,
      List.nodup_cons] at htrail
    exact (htrail.1 heTail).elim
  · exact (IsPath.avoids_cut_of_endpoints m P e hcross p.tail hp.isPath_tail
      hsnd hu x hxTail) hPx

theorem edge_mem_of_support_crosses_cut (m : ℕ) {u v a b : NonhubVertex m}
    (P : NonhubVertex m → Prop) (e : Sym2 (NonhubVertex m))
    (hcross : ∀ {x y}, (nonhubGraph m).Adj x y → P x → ¬P y → s(x, y) = e)
    (p : (nonhubGraph m).Walk u v) (ha : a ∈ p.support) (hb : b ∈ p.support)
    (hPa : P a) (hPb : ¬P b) : e ∈ p.edges := by
  classical
  by_cases hu : P u
  · have he := edge_mem_of_walk_crosses_cut P e hcross (p.takeUntil b hb) hu hPb
    exact p.edges_takeUntil_subset_edges hb he
  · have hcross' : ∀ {x y}, (nonhubGraph m).Adj x y →
        (¬P x) → ¬(¬P y) → s(x, y) = e := by
      intro x y hxy hx hy
      have hy' : P y := Classical.not_not.mp hy
      simpa [Sym2.eq_swap] using hcross hxy.symm hy' hx
    have he := edge_mem_of_walk_crosses_cut (¬P ·) e hcross'
      (p.takeUntil a ha) hu (by simpa using hPa)
    exact p.edges_takeUntil_subset_edges ha he

def leafSide (m : ℕ) (l : LeafId m) (z : NonhubVertex m) : Prop :=
  ∃ x : Fin 5, z.1 = leaf m l x

def leafBridgeEdge (m : ℕ) (l : LeafId m) : Sym2 (NonhubVertex m) :=
  s(leafNH m l (attachmentPosition m l),
    spineNH m (attachmentBlock m l) (attachmentPosition m l))

theorem leafSide_crossing (m : ℕ) (l : LeafId m) {a b : NonhubVertex m}
    (hab : (nonhubGraph m).Adj a b) (ha : leafSide m l a) (hb : ¬leafSide m l b) :
    s(a, b) = leafBridgeEdge m l := by
  obtain ⟨x, hax⟩ := ha
  have hae : a = leafNH m l x := Subtype.ext hax
  subst a
  rcases b with ⟨b, hbNH⟩
  rcases b with c | (c | c)
  · exact (hbNH (by simp [hub])).elim
  · rcases c with ⟨i, y⟩
    change spineLeafAdjacent i y l x at hab
    rcases hab with ⟨hi, hy, hx⟩
    apply Sym2.eq_iff.mpr
    left
    constructor
    · exact Subtype.ext (congrArg (fun q ↦ leaf m l q) hx)
    · apply Subtype.ext
      change spine m i y =
        spine m (attachmentBlock m l) (attachmentPosition m l)
      simp only [hi, hy]
  · rcases c with ⟨k, y⟩
    change l = k ∧ (cycleGraph 5).Adj x y at hab
    exfalso
    apply hb
    rcases hab with ⟨rfl, _⟩
    exact ⟨y, rfl⟩

/-- Index of the spine block containing a spine vertex, or of the spine
block to which a leaf vertex is attached. -/
def blockIndex (m : ℕ) (z : NonhubVertex m) : Fin (m + 1) :=
  match z.1 with
  | Sum.inl _ => 0
  | Sum.inr (Sum.inl (i, _)) => i
  | Sum.inr (Sum.inr (l, _)) => attachmentBlock m l

def spinePrefix (m : ℕ) (k : Fin m) (z : NonhubVertex m) : Prop :=
  (blockIndex m z).val ≤ k.val

def spineBridgeEdge (m : ℕ) (k : Fin m) : Sym2 (NonhubVertex m) :=
  s(spineNH m k.castSucc 2, spineNH m k.succ 0)

theorem spinePrefix_crossing (m : ℕ) (k : Fin m) {a b : NonhubVertex m}
    (hab : (nonhubGraph m).Adj a b) (ha : spinePrefix m k a)
    (hb : ¬spinePrefix m k b) :
    s(a, b) = spineBridgeEdge m k := by
  rcases a with ⟨a, haNH⟩
  rcases b with ⟨b, hbNH⟩
  rcases a with a | (a | a)
  · exact (haNH (by simp [hub])).elim
  · rcases a with ⟨i, x⟩
    rcases b with b | (b | b)
    · exact (hbNH (by simp [hub])).elim
    · rcases b with ⟨j, y⟩
      change spineAdjacent i x j y at hab
      change i.val ≤ k.val at ha
      change ¬j.val ≤ k.val at hb
      rcases hab with (⟨hij, _⟩ | ⟨hij, hx, hy⟩ | ⟨hji, _, _⟩)
      · subst j
        exact (hb ha).elim
      · have hi : i = k.castSucc := by apply Fin.ext; simp; omega
        have hj : j = k.succ := by apply Fin.ext; simp; omega
        subst i
        subst j
        subst x
        subst y
        rfl
      · omega
    · rcases b with ⟨l, y⟩
      change spineLeafAdjacent i x l y at hab
      change i.val ≤ k.val at ha
      change ¬(attachmentBlock m l).val ≤ k.val at hb
      exact (hb (hab.1 ▸ ha)).elim
  · rcases a with ⟨l, x⟩
    rcases b with b | (b | b)
    · exact (hbNH (by simp [hub])).elim
    · rcases b with ⟨j, y⟩
      change spineLeafAdjacent j y l x at hab
      change (attachmentBlock m l).val ≤ k.val at ha
      change ¬j.val ≤ k.val at hb
      exact (hb (hab.1.symm ▸ ha)).elim
    · rcases b with ⟨r, y⟩
      change l = r ∧ (cycleGraph 5).Adj x y at hab
      change (attachmentBlock m l).val ≤ k.val at ha
      change ¬(attachmentBlock m r).val ≤ k.val at hb
      rcases hab with ⟨rfl, _⟩
      exact (hb ha).elim

theorem path_blockIndex_between_endpoints (m : ℕ) {u v : NonhubVertex m}
    (p : (nonhubGraph m).Walk u v) (hp : p.IsPath) {z : NonhubVertex m}
    (hz : z ∈ p.support) :
    min (blockIndex m u).val (blockIndex m v).val ≤ (blockIndex m z).val ∧
      (blockIndex m z).val ≤ max (blockIndex m u).val (blockIndex m v).val := by
  classical
  constructor
  · by_contra hlt
    have hzM : (blockIndex m z).val < m := by
      have huLt := (blockIndex m u).isLt
      have hvLt := (blockIndex m v).isLt
      omega
    let k : Fin m := ⟨(blockIndex m z).val, hzM⟩
    have hu : ¬spinePrefix m k u := by
      change ¬(blockIndex m u).val ≤ k.val
      dsimp [k]
      omega
    have hv : ¬spinePrefix m k v := by
      change ¬(blockIndex m v).val ≤ k.val
      dsimp [k]
      omega
    have havoid := IsPath.avoids_cut_of_endpoints m (spinePrefix m k)
      (spineBridgeEdge m k) (spinePrefix_crossing m k) p hp hu hv z hz
    apply havoid
    change (blockIndex m z).val ≤ k.val
    rfl
  · by_contra hgt
    have hzPos : 0 < (blockIndex m z).val := by omega
    let k : Fin m := ⟨(blockIndex m z).val - 1, by
      have hzLt := (blockIndex m z).isLt
      omega⟩
    have hcross : ∀ {a b : NonhubVertex m}, (nonhubGraph m).Adj a b →
        (¬spinePrefix m k a) → ¬(¬spinePrefix m k b) →
        s(a, b) = spineBridgeEdge m k := by
      intro a b hab ha hb
      have hb' : spinePrefix m k b := Classical.not_not.mp hb
      simpa [Sym2.eq_swap] using spinePrefix_crossing m k hab.symm hb' ha
    have hu : ¬(¬spinePrefix m k u) := by
      simp only [not_not]
      change (blockIndex m u).val ≤ k.val
      dsimp [k]
      omega
    have hv : ¬(¬spinePrefix m k v) := by
      simp only [not_not]
      change (blockIndex m v).val ≤ k.val
      dsimp [k]
      omega
    have havoid := IsPath.avoids_cut_of_endpoints m (¬spinePrefix m k ·)
      (spineBridgeEdge m k) hcross p hp hu hv z hz
    apply havoid
    change ¬(blockIndex m z).val ≤ k.val
    dsimp [k]
    omega

theorem cycle_based_leaf_stays_leaf (m : ℕ) (l : LeafId m) (x : Fin 5)
    (p : (nonhubGraph m).Walk (leafNH m l x) (leafNH m l x))
    (hp : p.IsCycle) :
    ∀ z ∈ p.support, leafSide m l z := by
  classical
  have hcross : ∀ {a b : NonhubVertex m}, (nonhubGraph m).Adj a b →
      (¬leafSide m l a) → ¬(¬leafSide m l b) →
      s(a, b) = leafBridgeEdge m l := by
    intro a b hab ha hb
    have hb' : leafSide m l b := Classical.not_not.mp hb
    simpa [Sym2.eq_swap] using leafSide_crossing m l hab.symm hb' ha
  have hbase : ¬(¬leafSide m l (leafNH m l x)) := by
    simp only [not_not]
    exact ⟨x, rfl⟩
  intro z hz
  exact Classical.not_not.mp
    (IsCycle.avoids_unique_cut m (¬leafSide m l ·) (leafBridgeEdge m l)
      hcross p hp hbase z hz)

theorem cycle_based_spine_has_no_leaf (m : ℕ) (i : Fin (m + 1)) (x : Fin 5)
    (p : (nonhubGraph m).Walk (spineNH m i x) (spineNH m i x))
    (hp : p.IsCycle) (l : LeafId m) :
    ∀ z ∈ p.support, ¬leafSide m l z := by
  apply IsCycle.avoids_unique_cut m (leafSide m l) (leafBridgeEdge m l)
    (leafSide_crossing m l) p hp
  rintro ⟨y, hy⟩
  change spine m i x = leaf m l y at hy
  simp [spine, leaf] at hy

theorem cycle_based_spine_same_index (m : ℕ) (i : Fin (m + 1)) (x : Fin 5)
    (p : (nonhubGraph m).Walk (spineNH m i x) (spineNH m i x))
    (hp : p.IsCycle) :
    ∀ z ∈ p.support, blockIndex m z = i := by
  classical
  intro z hz
  apply Fin.ext
  by_contra hne
  have hltOr : (blockIndex m z).val < i.val ∨ i.val < (blockIndex m z).val := by
    omega
  rcases hltOr with hlt | hgt
  · let k : Fin m := ⟨(blockIndex m z).val, by
        have hi := i.isLt
        omega⟩
    have hbase : ¬spinePrefix m k (spineNH m i x) := by
      change ¬i.val ≤ k.val
      simp only [k]
      omega
    have havoid := IsCycle.avoids_unique_cut m (spinePrefix m k)
      (spineBridgeEdge m k) (spinePrefix_crossing m k) p hp hbase z hz
    apply havoid
    change (blockIndex m z).val ≤ k.val
    rfl
  · have hiM : i.val < m := by
      have hzlt := (blockIndex m z).isLt
      omega
    let k : Fin m := ⟨i.val, hiM⟩
    have hcross : ∀ {a b : NonhubVertex m}, (nonhubGraph m).Adj a b →
        (¬spinePrefix m k a) → ¬(¬spinePrefix m k b) →
        s(a, b) = spineBridgeEdge m k := by
      intro a b hab ha hb
      have hb' : spinePrefix m k b := Classical.not_not.mp hb
      simpa [Sym2.eq_swap] using spinePrefix_crossing m k hab.symm hb' ha
    have hbase : ¬(¬spinePrefix m k (spineNH m i x)) := by
      simp only [not_not]
      change i.val ≤ k.val
      rfl
    have havoid := IsCycle.avoids_unique_cut m (¬spinePrefix m k ·)
      (spineBridgeEdge m k) hcross p hp hbase z hz
    apply havoid
    change ¬(blockIndex m z).val ≤ k.val
    simp only [k]
    omega

abbrev BlockId (m : ℕ) := Fin (m + 1) ⊕ LeafId m

def blockOf (m : ℕ) (z : NonhubVertex m) : BlockId m :=
  match z.1 with
  | Sum.inl _ => Sum.inl 0
  | Sum.inr (Sum.inl (i, _)) => Sum.inl i
  | Sum.inr (Sum.inr (l, _)) => Sum.inr l

def chordBlock (m : ℕ) (e : Sym2 (NonhubVertex m)) : Sym2 (BlockId m) :=
  e.map (blockOf m)

theorem chordBlock_sym2Mk_of_eq (m : ℕ) (a b : NonhubVertex m)
    (h : blockOf m a = blockOf m b) :
    chordBlock m s(a, b) = s(blockOf m a, blockOf m a) := by
  simp [chordBlock, h]

theorem spine_forward_bridge_mem_of_support (m : ℕ) {u v : NonhubVertex m}
    (p : (nonhubGraph m).Walk u v) (i j : Fin (m + 1)) (x y : Fin 5)
    (haNH : spine m i x ≠ hub m) (hbNH : spine m j y ≠ hub m)
    (ha : ⟨spine m i x, haNH⟩ ∈ p.support)
    (hb : ⟨spine m j y, hbNH⟩ ∈ p.support)
    (hij : i.val + 1 = j.val) (hx : x = 2) (hy : y = 0) :
    s(⟨spine m i x, haNH⟩, ⟨spine m j y, hbNH⟩) ∈ p.edges := by
  have hiM : i.val < m := by have := j.isLt; omega
  let k : Fin m := ⟨i.val, hiM⟩
  have hPa : spinePrefix m k ⟨spine m i x, haNH⟩ := by
    change i.val ≤ k.val
    rfl
  have hPb : ¬spinePrefix m k ⟨spine m j y, hbNH⟩ := by
    change ¬j.val ≤ k.val
    dsimp [k]
    omega
  have hab : (nonhubGraph m).Adj ⟨spine m i x, haNH⟩
      ⟨spine m j y, hbNH⟩ := Or.inr (Or.inl ⟨hij, hx, hy⟩)
  have heq := spinePrefix_crossing m k hab hPa hPb
  have hemem := edge_mem_of_support_crosses_cut m (spinePrefix m k)
    (spineBridgeEdge m k) (spinePrefix_crossing m k) p ha hb hPa hPb
  rwa [← heq] at hemem

theorem leaf_bridge_mem_of_support (m : ℕ) {u v : NonhubVertex m}
    (p : (nonhubGraph m).Walk u v) (l : LeafId m) (x : Fin 5)
    (a : NonhubVertex m) (ha : leafNH m l x ∈ p.support) (hb : a ∈ p.support)
    (hnot : ¬leafSide m l a) (hadj : (nonhubGraph m).Adj (leafNH m l x) a) :
    s(leafNH m l x, a) ∈ p.edges := by
  have hleaf : leafSide m l (leafNH m l x) := ⟨x, rfl⟩
  have heq := leafSide_crossing m l hadj hleaf hnot
  have hemem := edge_mem_of_support_crosses_cut m (leafSide m l)
    (leafBridgeEdge m l) (leafSide_crossing m l) p ha hb hleaf hnot
  rwa [← heq] at hemem

theorem adjacent_different_blocks_has_unique_cut (m : ℕ)
    {a b : NonhubVertex m} (hab : (nonhubGraph m).Adj a b)
    (hne : blockOf m a ≠ blockOf m b) :
    ∃ (P : NonhubVertex m → Prop) (e : Sym2 (NonhubVertex m)),
      (∀ {x y}, (nonhubGraph m).Adj x y → P x → ¬P y → s(x, y) = e) ∧
      ((P a ∧ ¬P b) ∨ (P b ∧ ¬P a)) := by
  rcases a with ⟨a, haNH⟩
  rcases b with ⟨b, hbNH⟩
  rcases a with a | (a | a)
  · exact (haNH (by simp [hub])).elim
  · rcases a with ⟨i, x⟩
    rcases b with b | (b | b)
    · exact (hbNH (by simp [hub])).elim
    · rcases b with ⟨j, y⟩
      change spineAdjacent i x j y at hab
      rcases hab with (⟨hij, _⟩ | h | h)
      · subst j
        exact (hne rfl).elim
      · have hiM : i.val < m := by have := j.isLt; omega
        let k : Fin m := ⟨i.val, hiM⟩
        refine ⟨spinePrefix m k, spineBridgeEdge m k,
          spinePrefix_crossing m k, Or.inl ⟨?_, ?_⟩⟩
        · change i.val ≤ k.val
          rfl
        · change ¬j.val ≤ k.val
          dsimp [k]
          omega
      · have hjM : j.val < m := by have := i.isLt; omega
        let k : Fin m := ⟨j.val, hjM⟩
        refine ⟨spinePrefix m k, spineBridgeEdge m k,
          spinePrefix_crossing m k, Or.inr ⟨?_, ?_⟩⟩
        · change j.val ≤ k.val
          rfl
        · change ¬i.val ≤ k.val
          dsimp [k]
          omega
    · rcases b with ⟨l, y⟩
      refine ⟨leafSide m l, leafBridgeEdge m l, leafSide_crossing m l,
        Or.inr ⟨⟨y, rfl⟩, ?_⟩⟩
      rintro ⟨z, hz⟩
      cases hz
  · rcases a with ⟨l, x⟩
    rcases b with b | (b | b)
    · exact (hbNH (by simp [hub])).elim
    · rcases b with ⟨j, y⟩
      refine ⟨leafSide m l, leafBridgeEdge m l, leafSide_crossing m l,
        Or.inl ⟨⟨x, rfl⟩, ?_⟩⟩
      rintro ⟨z, hz⟩
      cases hz
    · rcases b with ⟨r, y⟩
      change l = r ∧ (cycleGraph 5).Adj x y at hab
      exact (hne (congrArg Sum.inr hab.1)).elim

theorem path_chord_same_block (m : ℕ) {u v : NonhubVertex m}
    (p : (nonhubGraph m).Walk u v) {e : Sym2 (NonhubVertex m)}
    (he : p.IsChord e) :
    e.lift ⟨fun a b ↦ blockOf m a = blockOf m b,
      fun a b ↦ propext (eq_comm)⟩ := by
  classical
  induction e using Sym2.inductionOn with
  | _ a b =>
      rw [SimpleGraph.Walk.isChord_sym2Mk] at he
      rcases he with ⟨hab, heNot, ha, hb⟩
      by_contra hne
      obtain ⟨P, e, hcross, hsides⟩ :=
        adjacent_different_blocks_has_unique_cut m hab hne
      rcases hsides with ⟨hPa, hPb⟩ | ⟨hPb, hPa⟩
      · have heq := hcross hab hPa hPb
        apply heNot
        rw [heq]
        exact edge_mem_of_support_crosses_cut m P e hcross p ha hb hPa hPb
      · have heq := hcross hab.symm hPb hPa
        apply heNot
        rw [Sym2.eq_swap, heq]
        exact edge_mem_of_support_crosses_cut m P e hcross p hb ha hPb hPa

theorem exists_cycle_of_path_chord {V : Type*} {G : SimpleGraph V} {u v : V}
    (p : G.Walk u v) (hp : p.IsPath) {e : Sym2 V} (he : p.IsChord e) :
    ∃ (w : V) (c : G.Walk w w), c.IsCycle ∧ e ∈ c.edges ∧
      (∀ z ∈ c.support, z ∈ p.support) ∧
      ∀ e' ∈ c.edges, e' = e ∨ e' ∈ p.edges := by
  classical
  induction e using Sym2.inductionOn with
  | _ a b =>
      rw [SimpleGraph.Walk.isChord_sym2Mk] at he
      rcases he with ⟨hab, heNot, ha, hb⟩
      let ia := (p.takeUntil a ha).length
      let ib := (p.takeUntil b hb).length
      have hiab : ia ≠ ib := by
        intro hieq
        apply hab.ne
        calc
          a = p.getVert ia := (p.getVert_length_takeUntil ha).symm
          _ = p.getVert ib := by rw [hieq]
          _ = b := p.getVert_length_takeUntil hb
      rcases lt_or_gt_of_ne hiab with hlt | hgt
      · have ha' : a ∈ (p.takeUntil b hb).support := by
          have hm := (p.takeUntil b hb).getVert_mem_support ia
          rw [p.getVert_takeUntil hb (le_of_lt hlt), p.getVert_length_takeUntil ha] at hm
          exact hm
        let r := (p.takeUntil b hb).dropUntil a ha'
        have hrPath : r.IsPath := (hp.takeUntil hb).dropUntil ha'
        have hre : s(a, b) ∉ r.edges := by
          intro hre
          apply heNot
          exact p.edges_takeUntil_subset_edges hb
            ((p.takeUntil b hb).edges_dropUntil_subset_edges ha' hre)
        let c := r.cons hab.symm
        refine ⟨b, c, ?_, ?_, ?_, ?_⟩
        · exact (SimpleGraph.Walk.cons_isCycle_iff r hab.symm).2 ⟨hrPath, by
            simpa [Sym2.eq_swap] using hre⟩
        · simp [c]
        · intro z hz
          change z ∈ b :: r.support at hz
          rcases List.mem_cons.mp hz with rfl | hz
          · exact hb
          · exact p.support_takeUntil_subset_support hb
              ((p.takeUntil b hb).support_dropUntil_subset_support ha' hz)
        · intro e' he'
          change e' ∈ s(b, a) :: r.edges at he'
          rcases List.mem_cons.mp he' with he' | he'
          · left
            simpa [Sym2.eq_swap] using he'
          · right
            exact p.edges_takeUntil_subset_edges hb
              ((p.takeUntil b hb).edges_dropUntil_subset_edges ha' he')
      · have hb' : b ∈ (p.takeUntil a ha).support := by
          have hm := (p.takeUntil a ha).getVert_mem_support ib
          rw [p.getVert_takeUntil ha (le_of_lt hgt), p.getVert_length_takeUntil hb] at hm
          exact hm
        let r := (p.takeUntil a ha).dropUntil b hb'
        have hrPath : r.IsPath := (hp.takeUntil ha).dropUntil hb'
        have hre : s(b, a) ∉ r.edges := by
          intro hre
          apply heNot
          simpa [Sym2.eq_swap] using p.edges_takeUntil_subset_edges ha
            ((p.takeUntil a ha).edges_dropUntil_subset_edges hb' hre)
        let c := r.cons hab
        refine ⟨a, c, ?_, ?_, ?_, ?_⟩
        · exact (SimpleGraph.Walk.cons_isCycle_iff r hab).2 ⟨hrPath, by
            simpa [Sym2.eq_swap] using hre⟩
        · simp [c, Sym2.eq_swap]
        · intro z hz
          change z ∈ a :: r.support at hz
          rcases List.mem_cons.mp hz with rfl | hz
          · exact ha
          · exact p.support_takeUntil_subset_support ha
              ((p.takeUntil a ha).support_dropUntil_subset_support hb' hz)
        · intro e' he'
          change e' ∈ s(a, b) :: r.edges at he'
          rcases List.mem_cons.mp he' with he' | he'
          · exact Or.inl he'
          · right
            exact p.edges_takeUntil_subset_edges ha
              ((p.takeUntil a ha).edges_dropUntil_subset_edges hb' he')

theorem isPath_countP_edges_incident_start_le_one {V : Type*} {G : SimpleGraph V}
    [DecidableEq V] {u v : V} {p : G.Walk u v} (hp : p.IsPath) :
    p.edges.countP (fun e ↦ decide (u ∈ e)) ≤ 1 := by
  classical
  cases p with
  | nil => simp
  | @cons _ w _ huw q =>
      have hn := hp.support_nodup
      rw [SimpleGraph.Walk.support_cons, List.nodup_cons] at hn
      have hzero : q.edges.countP (fun e ↦ decide (u ∈ e)) = 0 := by
        rw [List.countP_eq_zero]
        intro e he
        intro htrue
        have hue : u ∈ e := of_decide_eq_true htrue
        exact hn.1 (q.mem_support_of_mem_edges he hue)
      simp [SimpleGraph.Walk.edges_cons, hzero]

theorem isPath_countP_edges_incident_le_two {V : Type*} {G : SimpleGraph V}
    [DecidableEq V] {u v x : V} {p : G.Walk u v} (hp : p.IsPath) :
    p.edges.countP (fun e ↦ decide (x ∈ e)) ≤ 2 := by
  classical
  induction p with
  | nil => simp
  | @cons u w v huw q ih =>
      have hq : q.IsPath := by simpa using hp.tail
      by_cases hxu : x = u
      · subst x
        exact (isPath_countP_edges_incident_start_le_one hp).trans (by omega)
      by_cases hxw : x = w
      · subst x
        have ht := isPath_countP_edges_incident_start_le_one hq
        simp only [SimpleGraph.Walk.edges_cons, List.countP_cons, Sym2.mem_iff,
          hxu, or_true, decide_true, ite_true]
        omega
      · have ht := ih hq
        simp only [SimpleGraph.Walk.edges_cons, List.countP_cons, Sym2.mem_iff,
          hxu, hxw, or_false, decide_false, ite_false]
        exact ht

theorem isPath_card_incident_path_edges_le_two {V : Type*} {G : SimpleGraph V}
    [DecidableEq V] {u v x : V} {p : G.Walk u v} (hp : p.IsPath) :
    (hp.isTrail.edgesFinset.filter fun e ↦ x ∈ e).card ≤ 2 := by
  change (p.edges.filter fun e ↦ decide (x ∈ e)).length ≤ 2
  rw [← List.countP_eq_length_filter]
  exact isPath_countP_edges_incident_le_two (x := x) hp

theorem isPath_not_three_distinct_incident_edges {V : Type*} {G : SimpleGraph V}
    [DecidableEq V] {u v x : V} {p : G.Walk u v} (hp : p.IsPath)
    {e₁ e₂ e₃ : Sym2 V} (h₁ : e₁ ∈ p.edges) (h₂ : e₂ ∈ p.edges)
    (h₃ : e₃ ∈ p.edges) (hx₁ : x ∈ e₁) (hx₂ : x ∈ e₂) (hx₃ : x ∈ e₃)
    (h₁₂ : e₁ ≠ e₂) (h₁₃ : e₁ ≠ e₃) (h₂₃ : e₂ ≠ e₃) : False := by
  let F := hp.isTrail.edgesFinset.filter fun e ↦ x ∈ e
  have hsub : ({e₁, e₂, e₃} : Finset (Sym2 V)) ⊆ F := by
    intro e he
    simp only [Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with (rfl | rfl | rfl)
    · exact Finset.mem_filter.mpr ⟨h₁, hx₁⟩
    · exact Finset.mem_filter.mpr ⟨h₂, hx₂⟩
    · exact Finset.mem_filter.mpr ⟨h₃, hx₃⟩
  have hthree : ({e₁, e₂, e₃} : Finset (Sym2 V)).card = 3 := by
    simp [h₁₂, h₁₃, h₂₃]
  have hle := Finset.card_le_card hsub
  have htwo : F.card ≤ 2 := isPath_card_incident_path_edges_le_two hp
  omega

noncomputable def visitedLeaves (m : ℕ) {u v : NonhubVertex m}
    (p : (nonhubGraph m).Walk u v) : Finset (LeafId m) := by
  classical
  exact Finset.univ.filter fun l ↦ ∃ x : Fin 5, leafNH m l x ∈ p.support

noncomputable def endpointLeaves (m : ℕ) (z : NonhubVertex m) : Finset (LeafId m) := by
  classical
  exact Finset.univ.filter fun l ↦ leafSide m l z

theorem endpointLeaves_card_le_one (m : ℕ) (z : NonhubVertex m) :
    (endpointLeaves m z).card ≤ 1 := by
  classical
  rw [Finset.card_le_one_iff]
  intro l k hl hk
  change l ∈ Finset.univ.filter (fun l ↦ leafSide m l z) at hl
  change k ∈ Finset.univ.filter (fun l ↦ leafSide m l z) at hk
  obtain ⟨x, hx⟩ := (Finset.mem_filter.mp hl).2
  obtain ⟨y, hy⟩ := (Finset.mem_filter.mp hk).2
  rcases z with ⟨z, hz⟩
  simp only at hx hy
  rw [hx] at hy
  have hlabel := congrArg (fun q : Vertex m ↦
    match q with
    | Sum.inr (Sum.inr (l, _)) => some l
    | _ => none) hy
  simpa [leaf] using hlabel

theorem visitedLeaves_subset_endpointLeaves (m : ℕ) {u v : NonhubVertex m}
    (p : (nonhubGraph m).Walk u v) (hp : p.IsPath) :
    visitedLeaves m p ⊆ endpointLeaves m u ∪ endpointLeaves m v := by
  classical
  intro l hl
  change l ∈ Finset.univ.filter
    (fun l ↦ ∃ x : Fin 5, leafNH m l x ∈ p.support) at hl
  obtain ⟨x, hx⟩ := (Finset.mem_filter.mp hl).2
  by_cases hu : leafSide m l u
  · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hu⟩)
  by_cases hv : leafSide m l v
  · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv⟩)
  exfalso
  exact (IsPath.avoids_cut_of_endpoints m (leafSide m l) (leafBridgeEdge m l)
    (leafSide_crossing m l) p hp hu hv (leafNH m l x) hx) ⟨x, rfl⟩

theorem visitedLeaves_card_le_two (m : ℕ) {u v : NonhubVertex m}
    (p : (nonhubGraph m).Walk u v) (hp : p.IsPath) :
    (visitedLeaves m p).card ≤ 2 := by
  classical
  have hsub := visitedLeaves_subset_endpointLeaves m p hp
  calc
    (visitedLeaves m p).card ≤ (endpointLeaves m u ∪ endpointLeaves m v).card :=
      Finset.card_le_card hsub
    _ ≤ (endpointLeaves m u).card + (endpointLeaves m v).card :=
      Finset.card_union_le _ _
    _ ≤ 2 := by
      have hu := endpointLeaves_card_le_one m u
      have hv := endpointLeaves_card_le_one m v
      omega

theorem isPath_mem_dropLast_support_ne_end {V : Type*} {G : SimpleGraph V}
    {u v : V} {p : G.Walk u v} (hp : p.IsPath) (hnil : ¬p.Nil) :
    ∀ x ∈ p.dropLast.support, x ≠ v := by
  have hn := hp.support_nodup
  rw [← p.support_dropLast_concat hnil] at hn
  have hd : p.dropLast.support.Disjoint [v] :=
    List.disjoint_of_nodup_append hn
  intro x hx hxv
  subst x
  have hvnot : v ∉ p.dropLast.support := by simpa using hd
  exact hvnot hx

theorem cycle_tail_dropLast_avoids_hub (m : ℕ)
    {p : (graph m).Walk (hub m) (hub m)} (hp : p.IsCycle) :
    ∀ x ∈ p.tail.dropLast.support, x ≠ hub m := by
  have htail : p.tail.IsPath := hp.isPath_tail
  have htailNil : ¬p.tail.Nil := by
    rw [SimpleGraph.Walk.not_nil_iff_lt_length, SimpleGraph.Walk.length_tail]
    have := hp.three_le_length
    omega
  exact isPath_mem_dropLast_support_ne_end htail htailNil

/-- Removing the two hub edges from a cycle based at the hub gives a walk
in the induced nonhub graph. -/
noncomputable def hubDeletedPath (m : ℕ)
    (p : (graph m).Walk (hub m) (hub m)) (hp : p.IsCycle) :=
  (p.tail.dropLast).induce {v | v ≠ hub m} (cycle_tail_dropLast_avoids_hub m hp)

theorem hubDeletedPath_isPath (m : ℕ)
    (p : (graph m).Walk (hub m) (hub m)) (hp : p.IsCycle) :
    (hubDeletedPath m p hp).IsPath := by
  rw [SimpleGraph.Walk.isPath_def, hubDeletedPath,
    SimpleGraph.Walk.support_induce]
  apply List.Nodup.of_map (f := Subtype.val)
  rw [List.attachWith_map_subtype_val]
  exact hp.isPath_tail.dropLast.support_nodup

/-- In a finite graph of maximum degree two, every simple cycle is
chordless. -/
theorem cycle_chordless_of_degree_le_two {V : Type*} [Fintype V]
    [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hdeg : ∀ v, G.degree v ≤ 2) {u : V} (p : G.Walk u u)
    (hp : p.IsCycle) : p.IsChordless := by
  rw [SimpleGraph.Walk.isChordless_iff_forall_mem_edges]
  intro a b ha hb hab
  let q := p.rotate a ha
  have hq : q.IsCycle := by simpa [q] using hp.rotate ha
  have hqNil : ¬q.Nil := hq.not_nil
  have htailNil : ¬q.tail.Nil := by
    rw [SimpleGraph.Walk.not_nil_iff_lt_length, SimpleGraph.Walk.length_tail]
    have := hq.three_le_length
    omega
  have hfirstNot : s(a, q.snd) ∉ q.tail.edges := by
    have hc := (SimpleGraph.Walk.cons_isCycle_iff q.tail (q.adj_snd hqNil)).mp
      (by rw [q.cons_tail_eq hqNil]; exact hq)
    exact hc.2
  have hpen : q.penultimate = q.tail.penultimate := by
    calc
      q.penultimate = (q.tail.cons (q.adj_snd hqNil)).penultimate := by
        rw [q.cons_tail_eq hqNil]
      _ = q.tail.penultimate :=
        SimpleGraph.Walk.penultimate_cons_of_not_nil _ _ htailNil
  have hlast : s(q.penultimate, a) ∈ q.tail.edges := by
    rw [hpen]
    exact q.tail.mk_penultimate_end_mem_edges htailNil
  have hsndpen : q.snd ≠ q.penultimate := by
    intro heq
    apply hfirstNot
    simpa [heq, Sym2.eq_swap] using hlast
  have hba : b = q.snd ∨ b = q.penultimate := by
    by_contra hne
    push_neg at hne
    have hsub : ({b, q.snd, q.penultimate} : Finset V) ⊆ G.neighborFinset a := by
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with (rfl | rfl | rfl)
      · simpa using hab
      · simpa using q.adj_snd hqNil
      · simpa using q.adj_penultimate hqNil |>.symm
    have hc : ({b, q.snd, q.penultimate} : Finset V).card ≤ 2 := by
      exact (Finset.card_le_card hsub).trans (by simpa using hdeg a)
    simp [hne.1, hne.2, hsndpen] at hc
  have hqe : s(a, b) ∈ q.edges := by
    rcases hba with rfl | rfl
    · exact q.mk_start_snd_mem_edges hqNil
    · simpa [Sym2.eq_swap] using q.mk_penultimate_end_mem_edges hqNil
  exact (p.rotate_edges a ha).perm.mem_iff.mp hqe

theorem cycle_neighbor_mem_support_of_degree_le_two {V : Type*} [Fintype V]
    [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hdeg : ∀ v, G.degree v ≤ 2) {u : V} (p : G.Walk u u)
    (hp : p.IsCycle) {a b : V} (ha : a ∈ p.support) (hab : G.Adj a b) :
    b ∈ p.support := by
  let q := p.rotate a ha
  have hq : q.IsCycle := by simpa [q] using hp.rotate ha
  have hqNil : ¬q.Nil := hq.not_nil
  have htailNil : ¬q.tail.Nil := by
    rw [SimpleGraph.Walk.not_nil_iff_lt_length, SimpleGraph.Walk.length_tail]
    have := hq.three_le_length
    omega
  have hfirstNot : s(a, q.snd) ∉ q.tail.edges := by
    have hc := (SimpleGraph.Walk.cons_isCycle_iff q.tail (q.adj_snd hqNil)).mp
      (by rw [q.cons_tail_eq hqNil]; exact hq)
    exact hc.2
  have hpen : q.penultimate = q.tail.penultimate := by
    calc
      q.penultimate = (q.tail.cons (q.adj_snd hqNil)).penultimate := by
        rw [q.cons_tail_eq hqNil]
      _ = q.tail.penultimate :=
        SimpleGraph.Walk.penultimate_cons_of_not_nil _ _ htailNil
  have hlast : s(q.penultimate, a) ∈ q.tail.edges := by
    rw [hpen]
    exact q.tail.mk_penultimate_end_mem_edges htailNil
  have hsndpen : q.snd ≠ q.penultimate := by
    intro heq
    apply hfirstNot
    simpa [heq, Sym2.eq_swap] using hlast
  have hba : b = q.snd ∨ b = q.penultimate := by
    by_contra hne
    push Not at hne
    have hsub : ({b, q.snd, q.penultimate} : Finset V) ⊆ G.neighborFinset a := by
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with (rfl | rfl | rfl)
      · simpa using hab
      · simpa using q.adj_snd hqNil
      · simpa using q.adj_penultimate hqNil |>.symm
    have hc : ({b, q.snd, q.penultimate} : Finset V).card ≤ 2 :=
      (Finset.card_le_card hsub).trans (by simpa using hdeg a)
    simp [hne.1, hne.2, hsndpen] at hc
  have hmemQ : b ∈ q.support := by
    rcases hba with rfl | rfl
    · exact q.snd_mem_tail_support hqNil |> List.mem_of_mem_tail
    · exact q.getVert_mem_support (q.length - 1)
  exact (p.mem_support_rotate_iff a ha).mp hmemQ

theorem cycleGraph_five_cycle_support (u : Fin 5) (p : (cycleGraph 5).Walk u u)
    (hp : p.IsCycle) : ∀ z : Fin 5, z ∈ p.support := by
  intro z
  obtain ⟨r⟩ := cycleGraph_connected u z
  have hprop : ∀ {a b : Fin 5} (r : (cycleGraph 5).Walk a b),
      a ∈ p.support → b ∈ p.support := by
    intro a b r
    induction r with
    | nil => exact id
    | @cons _ w _ h r ih =>
        intro ha
        apply ih
        exact cycle_neighbor_mem_support_of_degree_le_two (cycleGraph 5)
          (fun v ↦ by rw [cycleGraph_degree_three_le]) p hp ha h
  exact hprop r p.start_mem_support

theorem chordless_of_map_embedding {V W : Type*} {G : SimpleGraph V}
    {H : SimpleGraph W} (f : G ↪g H) {u v : V} (p : G.Walk u v)
    (h : (p.map f.toHom).IsChordless) : p.IsChordless := by
  rw [SimpleGraph.Walk.isChordless_iff_forall_mem_edges] at h ⊢
  intro a b ha hb hab
  have hfa : f a ∈ (p.map f.toHom).support := by
    rw [SimpleGraph.Walk.support_map]
    exact List.mem_map.mpr ⟨a, ha, rfl⟩
  have hfb : f b ∈ (p.map f.toHom).support := by
    rw [SimpleGraph.Walk.support_map]
    exact List.mem_map.mpr ⟨b, hb, rfl⟩
  have he := h hfa hfb (f.map_adj_iff.mpr hab)
  rw [SimpleGraph.Walk.edges_map] at he
  obtain ⟨e, he, hemap⟩ := List.mem_map.mp he
  have heq : e = s(a, b) := by
    apply Sym2.map.injective f.injective
    simpa using hemap
  simpa [heq] using he

theorem chordless_map_embedding {V W : Type*} {G : SimpleGraph V}
    {H : SimpleGraph W} (f : G ↪g H) {u v : V} (p : G.Walk u v)
    (h : p.IsChordless) : (p.map f.toHom).IsChordless := by
  rw [SimpleGraph.Walk.isChordless_iff_forall_mem_edges] at h ⊢
  intro a b ha hb hab
  rw [SimpleGraph.Walk.support_map] at ha hb
  obtain ⟨a', ha', rfl⟩ := List.mem_map.mp ha
  obtain ⟨b', hb', hbeq⟩ := List.mem_map.mp hb
  have hbeq' : b = f b' := hbeq.symm
  subst b
  have he := h ha' hb' (f.map_adj_iff.mp hab)
  rw [SimpleGraph.Walk.edges_map]
  exact List.mem_map.mpr ⟨s(a', b'), he, by simp⟩

def localPosition (m : ℕ) (z : NonhubVertex m) : Fin 5 :=
  match z.1 with
  | Sum.inl _ => 0
  | Sum.inr (Sum.inl (_, x)) => x
  | Sum.inr (Sum.inr (_, x)) => x

noncomputable def leafBlockIso (m : ℕ) (l : LeafId m) :
    cycleGraph 5 ≃g (nonhubGraph m).induce (leafSide m l) where
  toFun x := ⟨leafNH m l x, ⟨x, rfl⟩⟩
  invFun z := localPosition m z.1
  left_inv x := rfl
  right_inv z := by
    rcases z with ⟨z, hz⟩
    obtain ⟨x, hx⟩ := hz
    have hz : z = leafNH m l x := Subtype.ext hx
    subst z
    rfl
  map_rel_iff' := by
    intro x y
    change (l = l ∧ (cycleGraph 5).Adj x y) ↔ (cycleGraph 5).Adj x y
    simp

def spineSide (m : ℕ) (i : Fin (m + 1)) (z : NonhubVertex m) : Prop :=
  ∃ x : Fin 5, z = spineNH m i x

noncomputable def spineBlockIso (m : ℕ) (i : Fin (m + 1)) :
    cycleGraph 5 ≃g (nonhubGraph m).induce (spineSide m i) where
  toFun x := ⟨spineNH m i x, ⟨x, rfl⟩⟩
  invFun z := localPosition m z.1
  left_inv x := rfl
  right_inv z := by
    rcases z with ⟨z, hz⟩
    obtain ⟨x, rfl⟩ := hz
    rfl
  map_rel_iff' := by
    intro x y
    change (nonhubGraph m).Adj (spineNH m i x) (spineNH m i y) ↔
      (cycleGraph 5).Adj x y
    exact ⟨(fun h ↦ by
      rcases h with (⟨_, h⟩ | ⟨h, _, _⟩ | ⟨h, _, _⟩)
      · exact h
      · omega
      · omega), fun h ↦ Or.inl ⟨rfl, h⟩⟩

theorem chordless_cycle_of_induce_iso_cycleGraph {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Set V)
    (f : cycleGraph 5 ≃g G.induce S) {u : V} (p : G.Walk u u)
    (hp : p.IsCycle) (hS : ∀ z ∈ p.support, z ∈ S) : p.IsChordless := by
  classical
  let q := p.induce S hS
  let inc : G.induce S ↪g G := SimpleGraph.Embedding.induce S
  have hmap : q.map inc.toHom = p := by
    simpa [q, inc] using SimpleGraph.Walk.map_induce p hS
  have hq : q.IsCycle := by
    apply SimpleGraph.Walk.IsCycle.of_map (f := inc.toHom)
    change (q.map (SimpleGraph.Embedding.induce S).toHom).IsCycle
    rw [SimpleGraph.Walk.map_induce]
    exact hp
  have hr : (q.map f.symm.toHom).IsCycle := hq.map f.symm.injective
  have hrChordless : (q.map f.symm.toHom).IsChordless := by
    apply cycle_chordless_of_degree_le_two (cycleGraph 5)
      (fun v ↦ by rw [cycleGraph_degree_three_le]) _ hr
  have hqChordless : q.IsChordless :=
    chordless_of_map_embedding f.symm.toEmbedding q hrChordless
  have hmapped := chordless_map_embedding inc q hqChordless
  rw [hmap] at hmapped
  exact hmapped

theorem cycle_covers_induce_iso_cycleGraph {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Set V)
    (f : cycleGraph 5 ≃g G.induce S) {u : V} (p : G.Walk u u)
    (hp : p.IsCycle) (hS : ∀ z ∈ p.support, z ∈ S) :
    ∀ z, z ∈ S → z ∈ p.support := by
  classical
  let q := p.induce S hS
  let inc : G.induce S ↪g G := SimpleGraph.Embedding.induce S
  have hq : q.IsCycle := by
    apply SimpleGraph.Walk.IsCycle.of_map (f := inc.toHom)
    change (q.map (SimpleGraph.Embedding.induce S).toHom).IsCycle
    rw [SimpleGraph.Walk.map_induce]
    exact hp
  let r := q.map f.symm.toHom
  have hr : r.IsCycle := hq.map f.symm.injective
  intro z hz
  let zS : S := ⟨z, hz⟩
  have hx : f.symm zS ∈ r.support := cycleGraph_five_cycle_support _ r hr _
  rw [SimpleGraph.Walk.support_map] at hx
  obtain ⟨y, hy, heq⟩ := List.mem_map.mp hx
  have hyz : y = zS := by
    apply f.symm.injective
    exact heq
  subst y
  have hzmap : z ∈ q.support.map Subtype.val :=
    List.mem_map.mpr ⟨zS, hy, rfl⟩
  dsimp [q] at hzmap
  rw [SimpleGraph.Walk.support_induce, List.attachWith_map_subtype_val] at hzmap
  exact hzmap

theorem nonhub_cycle_chordless (m : ℕ) {u : NonhubVertex m}
    (p : (nonhubGraph m).Walk u u) (hp : p.IsCycle) : p.IsChordless := by
  classical
  rcases u with ⟨u, hu⟩
  rcases u with a | (a | a)
  · exact (hu (by simp [hub])).elim
  · rcases a with ⟨i, x⟩
    apply chordless_cycle_of_induce_iso_cycleGraph (nonhubGraph m)
      (spineSide m i) (spineBlockIso m i) p hp
    intro z hz
    have hindex := cycle_based_spine_same_index m i x p hp z hz
    rcases z with ⟨z, hzNH⟩
    rcases z with z | (z | z)
    · exact (hzNH (by simp [hub])).elim
    · rcases z with ⟨j, y⟩
      change j = i at hindex
      subst j
      exact ⟨y, rfl⟩
    · rcases z with ⟨l, y⟩
      exfalso
      exact (cycle_based_spine_has_no_leaf m i x p hp l
        ⟨leaf m l y, hzNH⟩ hz) ⟨y, rfl⟩
  · rcases a with ⟨l, x⟩
    apply chordless_cycle_of_induce_iso_cycleGraph (nonhubGraph m)
      (leafSide m l) (leafBlockIso m l) p hp
    exact cycle_based_leaf_stays_leaf m l x p hp

theorem nonhub_cycle_covers_base_block (m : ℕ) {u : NonhubVertex m}
    (p : (nonhubGraph m).Walk u u) (hp : p.IsCycle) :
    ∀ z, blockOf m z = blockOf m u → z ∈ p.support := by
  classical
  rcases u with ⟨u, hu⟩
  rcases u with a | (a | a)
  · exact (hu (by simp [hub])).elim
  · rcases a with ⟨i, x⟩
    have hS : ∀ z ∈ p.support, spineSide m i z := by
      intro z hz
      have hindex := cycle_based_spine_same_index m i x p hp z hz
      rcases z with ⟨z, hzNH⟩
      rcases z with z | (z | z)
      · exact (hzNH (by simp [hub])).elim
      · rcases z with ⟨j, y⟩
        change j = i at hindex
        subst j
        exact ⟨y, rfl⟩
      · rcases z with ⟨l, y⟩
        exfalso
        exact (cycle_based_spine_has_no_leaf m i x p hp l
          ⟨leaf m l y, hzNH⟩ hz) ⟨y, rfl⟩
    have hcover := cycle_covers_induce_iso_cycleGraph (nonhubGraph m)
      (spineSide m i) (spineBlockIso m i) p hp hS
    intro z hzBlock
    rcases z with ⟨z, hzNH⟩
    rcases z with z | (z | z)
    · exact (hzNH (by simp [hub])).elim
    · rcases z with ⟨j, y⟩
      change Sum.inl j = Sum.inl i at hzBlock
      have : j = i := Sum.inl_injective hzBlock
      subst j
      exact hcover _ ⟨y, rfl⟩
    · rcases z with ⟨l, y⟩
      change Sum.inr l = Sum.inl i at hzBlock
      cases hzBlock
  · rcases a with ⟨l, x⟩
    have hS := cycle_based_leaf_stays_leaf m l x p hp
    have hcover := cycle_covers_induce_iso_cycleGraph (nonhubGraph m)
      (leafSide m l) (leafBlockIso m l) p hp hS
    intro z hzBlock
    rcases z with ⟨z, hzNH⟩
    rcases z with z | (z | z)
    · exact (hzNH (by simp [hub])).elim
    · rcases z with ⟨i, y⟩
      change Sum.inl i = Sum.inr l at hzBlock
      cases hzBlock
    · rcases z with ⟨r, y⟩
      change Sum.inr r = Sum.inr l at hzBlock
      have : r = l := Sum.inr_injective hzBlock
      subst r
      exact hcover _ ⟨y, rfl⟩

theorem nonhub_cycle_support_block_eq (m : ℕ) {u : NonhubVertex m}
    (p : (nonhubGraph m).Walk u u) (hp : p.IsCycle) :
    ∀ z ∈ p.support, blockOf m z = blockOf m u := by
  intro z hz
  rcases u with ⟨u, hu⟩
  rcases u with a | (a | a)
  · exact (hu (by simp [hub])).elim
  · rcases a with ⟨i, x⟩
    have hindex := cycle_based_spine_same_index m i x p hp z hz
    rcases z with ⟨z, hzNH⟩
    rcases z with z | (z | z)
    · exact (hzNH (by simp [hub])).elim
    · rcases z with ⟨j, y⟩
      change Sum.inl j = Sum.inl i
      exact congrArg Sum.inl hindex
    · rcases z with ⟨l, y⟩
      exfalso
      exact (cycle_based_spine_has_no_leaf m i x p hp l
        ⟨leaf m l y, hzNH⟩ hz) ⟨y, rfl⟩
  · rcases a with ⟨l, x⟩
    have hleaf := cycle_based_leaf_stays_leaf m l x p hp z hz
    obtain ⟨y, hy⟩ := hleaf
    rcases z with ⟨z, hzNH⟩
    change (match z with
      | Sum.inl _ => Sum.inl 0
      | Sum.inr (Sum.inl (i, _)) => Sum.inl i
      | Sum.inr (Sum.inr (r, _)) => Sum.inr r) = Sum.inr l
    have hy' : z = leaf m l y := hy
    rw [hy']
    rfl

theorem path_chords_eq_of_chordBlock_eq (m : ℕ) {u v : NonhubVertex m}
    (p : (nonhubGraph m).Walk u v) (hp : p.IsPath)
    {e e' : Sym2 (NonhubVertex m)} (he : p.IsChord e) (he' : p.IsChord e')
    (hblock : chordBlock m e = chordBlock m e') : e = e' := by
  classical
  induction e using Sym2.inductionOn with
  | _ a b =>
    induction e' using Sym2.inductionOn with
    | _ c d =>
      have habBlock : blockOf m a = blockOf m b := path_chord_same_block m p he
      have hcdBlock : blockOf m c = blockOf m d := path_chord_same_block m p he'
      rw [chordBlock_sym2Mk_of_eq m a b habBlock,
        chordBlock_sym2Mk_of_eq m c d hcdBlock] at hblock
      have hac : blockOf m a = blockOf m c := by
        rcases Sym2.eq_iff.mp hblock with h | h
        · exact h.1
        · exact h.1
      obtain ⟨w, cyc, hcyc, heCyc, hsupport, hedges⟩ :=
        exists_cycle_of_path_chord p hp he
      have haCyc : a ∈ cyc.support := cyc.fst_mem_support_of_mem_edges heCyc
      have haw : blockOf m a = blockOf m w :=
        nonhub_cycle_support_block_eq m cyc hcyc a haCyc
      have hcCyc : c ∈ cyc.support :=
        nonhub_cycle_covers_base_block m cyc hcyc c (hac.symm.trans haw)
      have hdCyc : d ∈ cyc.support :=
        nonhub_cycle_covers_base_block m cyc hcyc d
          (hcdBlock.symm.trans (hac.symm.trans haw))
      have he'Cyc : s(c, d) ∈ cyc.edges :=
        (nonhub_cycle_chordless m cyc hcyc).mem_edges hcCyc hdCyc he'.1
      rcases hedges _ he'Cyc with heq | he'p
      · exact heq.symm
      · exact (he'.2.1 he'p).elim

noncomputable def pathChordBlocks (m : ℕ) {u v : NonhubVertex m}
    (p : (nonhubGraph m).Walk u v) : Finset (Sym2 (BlockId m)) := by
  classical
  exact (Walk.chordFinset p).image (chordBlock m)

theorem pathChordBlocks_card_eq_chordCount (m : ℕ) {u v : NonhubVertex m}
    (p : (nonhubGraph m).Walk u v) (hp : p.IsPath) :
    (pathChordBlocks m p).card = Walk.chordCount p := by
  classical
  rw [pathChordBlocks, Walk.chordCount]
  apply Finset.card_image_iff.mpr
  intro e he e' he' heq
  exact path_chords_eq_of_chordBlock_eq m p hp
    ((Walk.mem_chordFinset p e).mp he) ((Walk.mem_chordFinset p e').mp he') heq

theorem spine_rim_chord_at_endpoint_index (m : ℕ) {u v : NonhubVertex m}
    (p : (nonhubGraph m).Walk u v) (hp : p.IsPath)
    (i : Fin (m + 1)) (x y : Fin 5)
    (he : p.IsChord s(spineNH m i x, spineNH m i y)) :
    i = blockIndex m u ∨ i = blockIndex m v := by
  classical
  by_contra hend
  push Not at hend
  have hxP : spineNH m i x ∈ p.support := he.2.2.1
  have hbetween := path_blockIndex_between_endpoints m p hp hxP
  change min (blockIndex m u).val (blockIndex m v).val ≤ i.val ∧
    i.val ≤ max (blockIndex m u).val (blockIndex m v).val at hbetween
  have hstrict :
      ((blockIndex m u).val < i.val ∧ i.val < (blockIndex m v).val) ∨
      ((blockIndex m v).val < i.val ∧ i.val < (blockIndex m u).val) := by
    have hnu : i.val ≠ (blockIndex m u).val := by
      intro h
      exact hend.1 (Fin.ext h)
    have hnv : i.val ≠ (blockIndex m v).val := by
      intro h
      exact hend.2 (Fin.ext h)
    omega
  have hiPos : 0 < i.val := by rcases hstrict with h | h <;> omega
  have hiM : i.val < m := by
    rcases hstrict with h | h
    · have := (blockIndex m v).isLt; omega
    · have := (blockIndex m u).isLt; omega
  let kL : Fin m := ⟨i.val - 1, by omega⟩
  let kR : Fin m := ⟨i.val, hiM⟩
  have hkLi : kL.succ = i := by apply Fin.ext; simp [kL]; omega
  have hkRi : kR.castSucc = i := by apply Fin.ext; simp [kR]
  have hleft : spineBridgeEdge m kL ∈ p.edges := by
    by_cases hu : spinePrefix m kL u
    · have hv : ¬spinePrefix m kL v := by
        change ¬(blockIndex m v).val ≤ kL.val
        change (blockIndex m u).val ≤ kL.val at hu
        dsimp [kL] at hu ⊢
        rcases hstrict with h | h <;> omega
      exact edge_mem_of_support_crosses_cut m (spinePrefix m kL)
        (spineBridgeEdge m kL) (spinePrefix_crossing m kL) p
        p.start_mem_support p.end_mem_support hu hv
    · have hv : spinePrefix m kL v := by
        change (blockIndex m v).val ≤ kL.val
        change ¬(blockIndex m u).val ≤ kL.val at hu
        dsimp [kL] at hu ⊢
        rcases hstrict with h | h <;> omega
      exact edge_mem_of_support_crosses_cut m (spinePrefix m kL)
        (spineBridgeEdge m kL) (spinePrefix_crossing m kL) p
        p.end_mem_support p.start_mem_support hv hu
  have hright : spineBridgeEdge m kR ∈ p.edges := by
    by_cases hu : spinePrefix m kR u
    · have hv : ¬spinePrefix m kR v := by
        change ¬(blockIndex m v).val ≤ kR.val
        change (blockIndex m u).val ≤ kR.val at hu
        dsimp [kR] at hu ⊢
        rcases hstrict with h | h <;> omega
      exact edge_mem_of_support_crosses_cut m (spinePrefix m kR)
        (spineBridgeEdge m kR) (spinePrefix_crossing m kR) p
        p.start_mem_support p.end_mem_support hu hv
    · have hv : spinePrefix m kR v := by
        change (blockIndex m v).val ≤ kR.val
        change ¬(blockIndex m u).val ≤ kR.val at hu
        dsimp [kR] at hu ⊢
        rcases hstrict with h | h <;> omega
      exact edge_mem_of_support_crosses_cut m (spinePrefix m kR)
        (spineBridgeEdge m kR) (spinePrefix_crossing m kR) p
        p.end_mem_support p.start_mem_support hv hu
  obtain ⟨w, cyc, hcyc, heCyc, _hsupport, hedges⟩ :=
    exists_cycle_of_path_chord p hp he
  have hxCyc : spineNH m i x ∈ cyc.support :=
    cyc.fst_mem_support_of_mem_edges heCyc
  have hixw : blockOf m (spineNH m i x) = blockOf m w :=
    nonhub_cycle_support_block_eq m cyc hcyc _ hxCyc
  have hpos (t : Fin 5) : spineNH m i t ∈ cyc.support := by
    apply nonhub_cycle_covers_base_block m cyc hcyc
    exact hixw
  have hrim (a b : Fin 5) (hab : (cycleGraph 5).Adj a b)
      (hne : s(spineNH m i a, spineNH m i b) ≠
        s(spineNH m i x, spineNH m i y)) :
      s(spineNH m i a, spineNH m i b) ∈ p.edges := by
    have hCyc : s(spineNH m i a, spineNH m i b) ∈ cyc.edges :=
      (nonhub_cycle_chordless m cyc hcyc).mem_edges (hpos a) (hpos b)
        (Or.inl ⟨rfl, hab⟩)
    rcases hedges _ hCyc with heq | hpEdge
    · exact (hne heq).elim
    · exact hpEdge
  have hzero : x = 0 ∨ y = 0 := by
    by_contra hne0
    push Not at hne0
    have he01 : s(spineNH m i 0, spineNH m i 1) ∈ p.edges := by
      apply hrim 0 1 (by decide)
      intro h
      rcases Sym2.eq_iff.mp h with h | h
      · exact hne0.1 (by simpa [spineNH, spine, localPosition] using
          (congrArg (localPosition m) h.1).symm)
      · exact hne0.2 (by simpa [spineNH, spine, localPosition] using
          (congrArg (localPosition m) h.1).symm)
    have he04 : s(spineNH m i 0, spineNH m i 4) ∈ p.edges := by
      apply hrim 0 4 (by decide)
      intro h
      rcases Sym2.eq_iff.mp h with h | h
      · exact hne0.1 (by simpa [spineNH, spine, localPosition] using
          (congrArg (localPosition m) h.1).symm)
      · exact hne0.2 (by simpa [spineNH, spine, localPosition] using
          (congrArg (localPosition m) h.1).symm)
    apply isPath_not_three_distinct_incident_edges
      (x := spineNH m i 0) hp hleft he01 he04
    · simp [spineBridgeEdge, hkLi]
    · simp
    · simp
    · simp [spineBridgeEdge, Sym2.eq_iff, spineNH, spine, hkLi, kL]
    · simp [spineBridgeEdge, Sym2.eq_iff, spineNH, spine, hkLi, kL]
    · simp [Sym2.eq_iff, spineNH, spine]
  have htwo : x = 2 ∨ y = 2 := by
    by_contra hne2
    push Not at hne2
    have he21 : s(spineNH m i 2, spineNH m i 1) ∈ p.edges := by
      apply hrim 2 1 (by decide)
      intro h
      rcases Sym2.eq_iff.mp h with h | h
      · exact hne2.1 (by simpa [spineNH, spine, localPosition] using
          (congrArg (localPosition m) h.1).symm)
      · exact hne2.2 (by simpa [spineNH, spine, localPosition] using
          (congrArg (localPosition m) h.1).symm)
    have he23 : s(spineNH m i 2, spineNH m i 3) ∈ p.edges := by
      apply hrim 2 3 (by decide)
      intro h
      rcases Sym2.eq_iff.mp h with h | h
      · exact hne2.1 (by simpa [spineNH, spine, localPosition] using
          (congrArg (localPosition m) h.1).symm)
      · exact hne2.2 (by simpa [spineNH, spine, localPosition] using
          (congrArg (localPosition m) h.1).symm)
    apply isPath_not_three_distinct_incident_edges
      (x := spineNH m i 2) hp hright he21 he23
    · simp [spineBridgeEdge, hkRi]
    · simp
    · simp
    · simp [spineBridgeEdge, Sym2.eq_iff, spineNH, spine, hkRi, kR]
    · simp [spineBridgeEdge, Sym2.eq_iff, spineNH, spine, hkRi, kR]
    · simp [Sym2.eq_iff, spineNH, spine]
  have hadj : (cycleGraph 5).Adj x y := by
    have hadj' := he.1
    change spineAdjacent i x i y at hadj'
    rcases hadj' with ⟨_, h⟩ | h | h
    · exact h
    · omega
    · omega
  rcases hzero with hx0 | hy0 <;> rcases htwo with hx2 | hy2
  · exact (show (0 : Fin 5) ≠ 2 by decide) (hx0.symm.trans hx2)
  · exact (show ¬(cycleGraph 5).Adj 0 2 by decide) (by simpa [hx0, hy2] using hadj)
  · exact (show ¬(cycleGraph 5).Adj 2 0 by decide) (by simpa [hy0, hx2] using hadj)
  · exact (show (0 : Fin 5) ≠ 2 by decide) (hy0.symm.trans hy2)

theorem blockOf_eq_leaf_of_leafSide (m : ℕ) (l : LeafId m)
    (z : NonhubVertex m) (hz : leafSide m l z) :
    blockOf m z = Sum.inr l := by
  obtain ⟨x, hx⟩ := hz
  rcases z with ⟨z, hzNH⟩
  change z = leaf m l x at hx
  subst z
  rfl

noncomputable def endpointChordBlocks (m : ℕ) (u v : NonhubVertex m) :
    Finset (Sym2 (BlockId m)) :=
  {s(blockOf m u, blockOf m u), s(blockOf m v, blockOf m v),
    s(Sum.inl (blockIndex m u), Sum.inl (blockIndex m u)),
    s(Sum.inl (blockIndex m v), Sum.inl (blockIndex m v))}

theorem pathChordBlocks_subset_endpointChordBlocks (m : ℕ)
    {u v : NonhubVertex m} (p : (nonhubGraph m).Walk u v) (hp : p.IsPath) :
    pathChordBlocks m p ⊆ endpointChordBlocks m u v := by
  classical
  intro q hq
  rw [pathChordBlocks] at hq
  obtain ⟨e, heFin, rfl⟩ := Finset.mem_image.mp hq
  have he : p.IsChord e := (Walk.mem_chordFinset p e).mp heFin
  induction e using Sym2.inductionOn with
  | _ a b =>
      have habBlock : blockOf m a = blockOf m b := path_chord_same_block m p he
      rw [chordBlock_sym2Mk_of_eq m a b habBlock]
      rcases a with ⟨a, haNH⟩
      rcases b with ⟨b, hbNH⟩
      rcases a with a | (a | a)
      · exact (haNH (by simp [hub])).elim
      · rcases a with ⟨i, x⟩
        rcases b with b | (b | b)
        · exact (hbNH (by simp [hub])).elim
        · rcases b with ⟨j, y⟩
          change Sum.inl i = Sum.inl j at habBlock
          have hij : i = j := Sum.inl.inj habBlock
          subst j
          have hi := spine_rim_chord_at_endpoint_index m p hp i x y he
          rcases hi with hi | hi
          · simp only [endpointChordBlocks, Finset.mem_insert, Finset.mem_singleton]
            right; right; left
            simpa only [blockOf] using congrArg
              (fun z : BlockId m ↦ s(z, z)) (congrArg Sum.inl hi)
          · simp only [endpointChordBlocks, Finset.mem_insert, Finset.mem_singleton]
            right; right; right
            simpa only [blockOf] using congrArg
              (fun z : BlockId m ↦ s(z, z)) (congrArg Sum.inl hi)
        · rcases b with ⟨l, y⟩
          change Sum.inl i = Sum.inr l at habBlock
          cases habBlock
      · rcases a with ⟨l, x⟩
        rcases b with b | (b | b)
        · exact (hbNH (by simp [hub])).elim
        · rcases b with ⟨j, y⟩
          change Sum.inr l = Sum.inl j at habBlock
          cases habBlock
        · rcases b with ⟨k, y⟩
          change Sum.inr l = Sum.inr k at habBlock
          have hlk : l = k := Sum.inr.inj habBlock
          subst k
          have hlVisited : l ∈ visitedLeaves m p := by
            apply Finset.mem_filter.mpr
            refine ⟨Finset.mem_univ _, x, ?_⟩
            exact he.2.2.1
          have hlEnd := visitedLeaves_subset_endpointLeaves m p hp hlVisited
          rw [Finset.mem_union] at hlEnd
          rcases hlEnd with hlu | hlv
          · have hlu' : leafSide m l u := (Finset.mem_filter.mp hlu).2
            have hblock := blockOf_eq_leaf_of_leafSide m l u hlu'
            simp only [endpointChordBlocks, Finset.mem_insert, Finset.mem_singleton]
            left
            simpa only [blockOf] using congrArg
              (fun z : BlockId m ↦ s(z, z)) hblock.symm
          · have hlv' : leafSide m l v := (Finset.mem_filter.mp hlv).2
            have hblock := blockOf_eq_leaf_of_leafSide m l v hlv'
            simp only [endpointChordBlocks, Finset.mem_insert, Finset.mem_singleton]
            right; left
            simpa only [blockOf] using congrArg
              (fun z : BlockId m ↦ s(z, z)) hblock.symm

theorem path_chordCount_le_four (m : ℕ) {u v : NonhubVertex m}
    (p : (nonhubGraph m).Walk u v) (hp : p.IsPath) :
    Walk.chordCount p ≤ 4 := by
  rw [← pathChordBlocks_card_eq_chordCount m p hp]
  apply (Finset.card_le_card (pathChordBlocks_subset_endpointChordBlocks m p hp)).trans
  rw [endpointChordBlocks]
  let a := s(blockOf m u, blockOf m u)
  let b := s(blockOf m v, blockOf m v)
  let c : Sym2 (BlockId m) :=
    s(Sum.inl (blockIndex m u), Sum.inl (blockIndex m u))
  let d : Sym2 (BlockId m) :=
    s(Sum.inl (blockIndex m v), Sum.inl (blockIndex m v))
  change ({a, b, c, d} : Finset (Sym2 (BlockId m))).card ≤ 4
  have h1 := Finset.card_insert_le a ({b, c, d} : Finset (Sym2 (BlockId m)))
  have h2 := Finset.card_insert_le b ({c, d} : Finset (Sym2 (BlockId m)))
  have h3 := Finset.card_insert_le c ({d} : Finset (Sym2 (BlockId m)))
  simp only [Finset.card_singleton] at h1 h2 h3
  omega

noncomputable def hubEdgesForLeaf (m : ℕ) (l : LeafId m) :
    Finset (Sym2 (Vertex m)) := by
  classical
  exact ((Finset.univ : Finset (Fin 5)).erase (attachmentPosition m l)).image
    (fun x ↦ s(hub m, leaf m l x))

theorem hubEdgesForLeaf_card_le_four (m : ℕ) (l : LeafId m) :
    (hubEdgesForLeaf m l).card ≤ 4 := by
  classical
  apply (Finset.card_image_le).trans
  simp [hubEdgesForLeaf]

noncomputable def hubCandidateEdges (m : ℕ) {u v : NonhubVertex m}
    (q : (nonhubGraph m).Walk u v) : Finset (Sym2 (Vertex m)) := by
  classical
  exact (visitedLeaves m q).biUnion (hubEdgesForLeaf m)

theorem hubCandidateEdges_card_le_eight (m : ℕ) {u v : NonhubVertex m}
    (q : (nonhubGraph m).Walk u v) (hq : q.IsPath) :
    (hubCandidateEdges m q).card ≤ 8 := by
  classical
  rw [hubCandidateEdges]
  apply (Finset.card_biUnion_le_card_mul (visitedLeaves m q)
    (hubEdgesForLeaf m) 4 ?_).trans
  · have h := visitedLeaves_card_le_two m q hq
    omega
  · intro l hl
    exact hubEdgesForLeaf_card_le_four m l

theorem mem_hubDeletedPath_support_of_mem_cycle_support (m : ℕ)
    (p : (graph m).Walk (hub m) (hub m)) (hp : p.IsCycle)
    (z : Vertex m) (hzNH : z ≠ hub m) (hz : z ∈ p.support) :
    (⟨z, hzNH⟩ : NonhubVertex m) ∈ (hubDeletedPath m p hp).support := by
  have hpNil : ¬p.Nil := hp.not_nil
  have hzTail : z ∈ p.tail.support := by
    rw [← p.cons_support_tail hpNil] at hz
    rcases List.mem_cons.mp hz with hz | hz
    · exact (hzNH hz).elim
    · exact hz
  have htailNil : ¬p.tail.Nil := by
    rw [SimpleGraph.Walk.not_nil_iff_lt_length, SimpleGraph.Walk.length_tail]
    have := hp.three_le_length
    omega
  have hzDrop : z ∈ p.tail.dropLast.support := by
    rw [← p.tail.support_dropLast_concat htailNil] at hzTail
    rw [List.mem_append] at hzTail
    rcases hzTail with hzTail | hzEnd
    · exact hzTail
    · simp only [List.mem_singleton] at hzEnd
      exact (hzNH hzEnd).elim
  rw [hubDeletedPath, SimpleGraph.Walk.support_induce, List.mem_attachWith]
  exact hzDrop

noncomputable def hubChordFinset (m : ℕ)
    (p : (graph m).Walk (hub m) (hub m)) : Finset (Sym2 (Vertex m)) := by
  classical
  exact (Walk.chordFinset p).filter fun e ↦ hub m ∈ e

theorem hubChordFinset_subset_candidates (m : ℕ)
    (p : (graph m).Walk (hub m) (hub m)) (hp : p.IsCycle) :
    hubChordFinset m p ⊆ hubCandidateEdges m (hubDeletedPath m p hp) := by
  classical
  intro e heHub
  have heFilter := Finset.mem_filter.mp heHub
  have he : p.IsChord e := (Walk.mem_chordFinset p e).mp heFilter.1
  induction e using Sym2.inductionOn with
  | _ a b =>
      rw [Sym2.mem_iff] at heFilter
      rcases heFilter.2 with ha | hb
      · subst a
        obtain ⟨l, x, hx, rfl⟩ := (adj_hub_iff_exists_leaf m b).mp he.1
        have hxNH : leaf m l x ≠ hub m := by simp [leaf, hub]
        have hxQ : leafNH m l x ∈ (hubDeletedPath m p hp).support := by
          exact mem_hubDeletedPath_support_of_mem_cycle_support m p hp _ hxNH he.2.2.2
        have hlVisited : l ∈ visitedLeaves m (hubDeletedPath m p hp) := by
          apply Finset.mem_filter.mpr
          exact ⟨Finset.mem_univ _, x, hxQ⟩
        simp only [hubCandidateEdges]
        apply Finset.mem_biUnion.mpr
        refine ⟨l, hlVisited, ?_⟩
        apply Finset.mem_image.mpr
        exact ⟨x, Finset.mem_erase.mpr ⟨hx, Finset.mem_univ _⟩, rfl⟩
      · subst b
        obtain ⟨l, x, hx, ha⟩ := (adj_hub_iff_exists_leaf m a).mp he.1.symm
        subst a
        have hxNH : leaf m l x ≠ hub m := by simp [leaf, hub]
        have hxQ : leafNH m l x ∈ (hubDeletedPath m p hp).support := by
          exact mem_hubDeletedPath_support_of_mem_cycle_support m p hp _ hxNH he.2.2.1
        have hlVisited : l ∈ visitedLeaves m (hubDeletedPath m p hp) := by
          apply Finset.mem_filter.mpr
          exact ⟨Finset.mem_univ _, x, hxQ⟩
        simp only [hubCandidateEdges]
        apply Finset.mem_biUnion.mpr
        refine ⟨l, hlVisited, ?_⟩
        apply Finset.mem_image.mpr
        refine ⟨x, Finset.mem_erase.mpr ⟨hx, Finset.mem_univ _⟩, ?_⟩
        exact Sym2.eq_swap

theorem hub_edge_mem_candidates_of_adj_mem_support (m : ℕ)
    (p : (graph m).Walk (hub m) (hub m)) (hp : p.IsCycle)
    (z : Vertex m) (hadj : (graph m).Adj (hub m) z) (hz : z ∈ p.support) :
    s(hub m, z) ∈ hubCandidateEdges m (hubDeletedPath m p hp) := by
  classical
  obtain ⟨l, x, hx, rfl⟩ := (adj_hub_iff_exists_leaf m z).mp hadj
  have hxNH : leaf m l x ≠ hub m := by simp [leaf, hub]
  have hxQ : leafNH m l x ∈ (hubDeletedPath m p hp).support :=
    mem_hubDeletedPath_support_of_mem_cycle_support m p hp _ hxNH hz
  have hlVisited : l ∈ visitedLeaves m (hubDeletedPath m p hp) := by
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _, x, hxQ⟩
  simp only [hubCandidateEdges]
  apply Finset.mem_biUnion.mpr
  refine ⟨l, hlVisited, ?_⟩
  apply Finset.mem_image.mpr
  exact ⟨x, Finset.mem_erase.mpr ⟨hx, Finset.mem_univ _⟩, rfl⟩

theorem hubChordFinset_card_le_six (m : ℕ)
    (p : (graph m).Walk (hub m) (hub m)) (hp : p.IsCycle) :
    (hubChordFinset m p).card ≤ 6 := by
  classical
  let q := hubDeletedPath m p hp
  let e₁ := s(hub m, p.snd)
  let e₂ := s(p.penultimate, hub m)
  have hpNil : ¬p.Nil := hp.not_nil
  have he₁Edge : e₁ ∈ p.edges := by
    exact p.mk_start_snd_mem_edges hpNil
  have he₂Edge : e₂ ∈ p.edges := by
    exact p.mk_penultimate_end_mem_edges hpNil
  have he₁Candidate : e₁ ∈ hubCandidateEdges m q := by
    apply hub_edge_mem_candidates_of_adj_mem_support m p hp p.snd
    · exact p.adj_snd hpNil
    · exact p.snd_mem_support_of_mem_edges he₁Edge
  have he₂Candidate : e₂ ∈ hubCandidateEdges m q := by
    have h := hub_edge_mem_candidates_of_adj_mem_support m p hp p.penultimate
      (p.adj_penultimate hpNil).symm (p.fst_mem_support_of_mem_edges he₂Edge)
    simpa only [e₂, Sym2.eq_swap] using h
  have he₁Not : e₁ ∉ hubChordFinset m p := by
    intro he
    have hc : p.IsChord e₁ := (Walk.mem_chordFinset p e₁).mp (Finset.mem_filter.mp he).1
    exact hc.2.1 he₁Edge
  have he₂Not : e₂ ∉ hubChordFinset m p := by
    intro he
    have hc : p.IsChord e₂ := (Walk.mem_chordFinset p e₂).mp (Finset.mem_filter.mp he).1
    exact hc.2.1 he₂Edge
  have he₁₂ : e₁ ≠ e₂ := by
    dsimp [e₁, e₂]
    grind [Sym2.eq_iff, hp.snd_ne_penultimate]
  have hsub : insert e₁ (insert e₂ (hubChordFinset m p)) ⊆
      hubCandidateEdges m q := by
    intro e he
    simp only [Finset.mem_insert] at he
    rcases he with rfl | rfl | he
    · exact he₁Candidate
    · exact he₂Candidate
    · exact hubChordFinset_subset_candidates m p hp he
  have hcard := Finset.card_le_card hsub
  have he₁NotInsert : e₁ ∉ insert e₂ (hubChordFinset m p) := by
    simp only [Finset.mem_insert, not_or]
    exact ⟨he₁₂, he₁Not⟩
  rw [Finset.card_insert_of_notMem he₁NotInsert,
    Finset.card_insert_of_notMem he₂Not] at hcard
  have hcand := hubCandidateEdges_card_le_eight m q (hubDeletedPath_isPath m p hp)
  omega

noncomputable def toNonhubVertex (m : ℕ) (z : Vertex m) : NonhubVertex m := by
  classical
  by_cases hz : z ≠ hub m
  · exact ⟨z, hz⟩
  · exact spineNH m 0 0

@[simp] theorem toNonhubVertex_val_of_ne (m : ℕ) (z : Vertex m)
    (hz : z ≠ hub m) : (toNonhubVertex m z).1 = z := by
  classical
  simp [toNonhubVertex, hz]

noncomputable def toNonhubEdge (m : ℕ) (e : Sym2 (Vertex m)) :
    Sym2 (NonhubVertex m) := e.map (toNonhubVertex m)

theorem map_toNonhubEdge_val (m : ℕ) (e : Sym2 (Vertex m))
    (he : hub m ∉ e) :
    (toNonhubEdge m e).map Subtype.val = e := by
  classical
  induction e using Sym2.inductionOn with
  | _ a b =>
      rw [Sym2.mem_iff] at he
      simp only [not_or] at he
      have ha : a ≠ hub m := Ne.symm he.1
      have hb : b ≠ hub m := Ne.symm he.2
      apply Sym2.eq_iff.mpr
      left
      exact ⟨toNonhubVertex_val_of_ne m a ha, toNonhubVertex_val_of_ne m b hb⟩

theorem toNonhubEdge_injOn (m : ℕ) :
    Set.InjOn (toNonhubEdge m) {e | hub m ∉ e} := by
  intro e he e' he' hEq
  have hmap := congrArg (fun q : Sym2 (NonhubVertex m) ↦ q.map Subtype.val) hEq
  simpa only [map_toNonhubEdge_val m e he, map_toNonhubEdge_val m e' he'] using hmap

noncomputable def nonhubChordFinset (m : ℕ)
    (p : (graph m).Walk (hub m) (hub m)) : Finset (Sym2 (Vertex m)) := by
  classical
  exact (Walk.chordFinset p).filter fun e ↦ hub m ∉ e

theorem toNonhubEdge_isChord_hubDeletedPath (m : ℕ)
    (p : (graph m).Walk (hub m) (hub m)) (hp : p.IsCycle)
    (e : Sym2 (Vertex m)) (he : p.IsChord e) (heHub : hub m ∉ e) :
    (hubDeletedPath m p hp).IsChord (toNonhubEdge m e) := by
  classical
  induction e using Sym2.inductionOn with
  | _ a b =>
      rw [Sym2.mem_iff] at heHub
      simp only [not_or] at heHub
      have haNH : a ≠ hub m := Ne.symm heHub.1
      have hbNH : b ≠ hub m := Ne.symm heHub.2
      rw [SimpleGraph.Walk.isChord_sym2Mk] at he
      change (hubDeletedPath m p hp).IsChord
        s(toNonhubVertex m a, toNonhubVertex m b)
      rw [SimpleGraph.Walk.isChord_sym2Mk]
      have haQ := mem_hubDeletedPath_support_of_mem_cycle_support m p hp a haNH he.2.2.1
      have hbQ := mem_hubDeletedPath_support_of_mem_cycle_support m p hp b hbNH he.2.2.2
      have hadjQ : (nonhubGraph m).Adj (toNonhubVertex m a) (toNonhubVertex m b) := by
        change (graph m).Adj (toNonhubVertex m a).1 (toNonhubVertex m b).1
        simpa [haNH, hbNH] using he.1
      refine ⟨hadjQ, ?_, ?_, ?_⟩
      · intro heQ
        let inc := SimpleGraph.Embedding.induce (G := graph m) {z | z ≠ hub m}
        have hmap : (hubDeletedPath m p hp).map inc.toHom = p.tail.dropLast := by
          dsimp [inc, hubDeletedPath]
          exact SimpleGraph.Walk.map_induce _ _
        have heMap : s(a, b) ∈ ((hubDeletedPath m p hp).map inc.toHom).edges := by
          rw [SimpleGraph.Walk.edges_map]
          have hm : (toNonhubEdge m s(a, b)).map inc ∈
              List.map (Sym2.map inc) (hubDeletedPath m p hp).edges :=
            List.mem_map_of_mem heQ
          have heqMap : (toNonhubEdge m s(a, b)).map inc = s(a, b) := by
            apply Sym2.eq_iff.mpr
            left
            exact ⟨by simp [toNonhubEdge, toNonhubVertex, haNH, inc],
              by simp [toNonhubEdge, toNonhubVertex, hbNH, inc]⟩
          exact heqMap ▸ hm
        have hedgesEq := congrArg SimpleGraph.Walk.edges hmap
        have heDrop : s(a, b) ∈ p.tail.dropLast.edges := hedgesEq ▸ heMap
        have heDrop' : s(a, b) ∈ p.tail.edges.dropLast := by
          rw [← SimpleGraph.Walk.edges_dropLast]
          exact heDrop
        have heTail : s(a, b) ∈ p.tail.edges := List.mem_of_mem_dropLast heDrop'
        apply he.2.1
        rw [← p.cons_tail_eq hp.not_nil, SimpleGraph.Walk.edges_cons]
        exact List.mem_cons_of_mem _ heTail
      · simpa [toNonhubVertex, haNH] using haQ
      · simpa [toNonhubVertex, hbNH] using hbQ

theorem nonhubChordFinset_card_le_four (m : ℕ)
    (p : (graph m).Walk (hub m) (hub m)) (hp : p.IsCycle) :
    (nonhubChordFinset m p).card ≤ 4 := by
  classical
  let q := hubDeletedPath m p hp
  have hsub : (nonhubChordFinset m p).image (toNonhubEdge m) ⊆
      Walk.chordFinset q := by
    intro e he
    obtain ⟨e₀, he₀, rfl⟩ := Finset.mem_image.mp he
    have heFilter := Finset.mem_filter.mp he₀
    apply (Walk.mem_chordFinset q _).mpr
    exact toNonhubEdge_isChord_hubDeletedPath m p hp e₀
      ((Walk.mem_chordFinset p e₀).mp heFilter.1) heFilter.2
  have hcardImage : ((nonhubChordFinset m p).image (toNonhubEdge m)).card =
      (nonhubChordFinset m p).card := by
    apply Finset.card_image_iff.mpr
    intro e he e' he' hEq
    apply toNonhubEdge_injOn m
    · exact (Finset.mem_filter.mp he).2
    · exact (Finset.mem_filter.mp he').2
    · exact hEq
  have hle := Finset.card_le_card hsub
  rw [hcardImage] at hle
  exact hle.trans (path_chordCount_le_four m q (hubDeletedPath_isPath m p hp))

theorem based_hub_cycle_chordCount_le_ten (m : ℕ)
    (p : (graph m).Walk (hub m) (hub m)) (hp : p.IsCycle) :
    Walk.chordCount p ≤ 10 := by
  classical
  have hunion : hubChordFinset m p ∪ nonhubChordFinset m p = Walk.chordFinset p := by
    ext e
    simp only [hubChordFinset, nonhubChordFinset, Finset.mem_union,
      Finset.mem_filter, Walk.mem_chordFinset]
    constructor
    · rintro (⟨he, _⟩ | ⟨he, _⟩) <;> exact he
    · intro he
      by_cases hh : hub m ∈ e
      · exact Or.inl ⟨he, hh⟩
      · exact Or.inr ⟨he, hh⟩
  have hdisj : Disjoint (hubChordFinset m p) (nonhubChordFinset m p) := by
    rw [Finset.disjoint_left]
    intro e heHub heNH
    exact (Finset.mem_filter.mp heNH).2 (Finset.mem_filter.mp heHub).2
  have hcard : Walk.chordCount p =
      (hubChordFinset m p).card + (nonhubChordFinset m p).card := by
    rw [Walk.chordCount, ← hunion, Finset.card_union_of_disjoint hdisj]
  rw [hcard]
  have hhub := hubChordFinset_card_le_six m p hp
  have hnonhub := nonhubChordFinset_card_le_four m p hp
  omega

theorem chordFinset_rotate_eq {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V}
    {v : V} (p : G.Walk v v) (u : V) (hu : u ∈ p.support) :
    Walk.chordFinset (p.rotate u hu) = Walk.chordFinset p := by
  classical
  ext e
  simp only [Walk.mem_chordFinset]
  induction e using Sym2.inductionOn with
  | _ a b =>
      rw [SimpleGraph.Walk.isChord_sym2Mk, SimpleGraph.Walk.isChord_sym2Mk]
      have hedge : s(a, b) ∈ (p.rotate u hu).edges ↔ s(a, b) ∈ p.edges :=
        (p.rotate_edges u hu).perm.mem_iff
      simp only [hedge, p.mem_support_rotate_iff u hu]

theorem chordCount_rotate_eq {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V}
    {v : V} (p : G.Walk v v) (u : V) (hu : u ∈ p.support) :
    Walk.chordCount (p.rotate u hu) = Walk.chordCount p := by
  unfold Walk.chordCount
  rw [chordFinset_rotate_eq p u hu]

theorem mem_map_injective_iff {A B : Type*} {f : A → B}
    (hf : Function.Injective f) (a : A) (l : List A) :
    f a ∈ l.map f ↔ a ∈ l := by
  induction l with
  | nil => simp
  | cons b l ih => simp only [List.map_cons, List.mem_cons, hf.eq_iff, ih]

theorem isChord_map_iso_iff {V W : Type*} {G : SimpleGraph V}
    {H : SimpleGraph W} (f : G ≃g H) {u v : V} (p : G.Walk u v)
    (e : Sym2 V) :
    (p.map f.toHom).IsChord (e.map f) ↔ p.IsChord e := by
  induction e using Sym2.inductionOn with
  | _ a b =>
      change (p.map f.toHom).IsChord s(f a, f b) ↔ p.IsChord s(a, b)
      rw [SimpleGraph.Walk.isChord_sym2Mk, SimpleGraph.Walk.isChord_sym2Mk]
      have hadj : H.Adj (f a) (f b) ↔ G.Adj a b := f.map_rel_iff
      have hedge : s(f a, f b) ∈ (p.map f.toHom).edges ↔ s(a, b) ∈ p.edges := by
        rw [SimpleGraph.Walk.edges_map]
        change (Sym2.map f s(a, b) ∈ p.edges.map (Sym2.map f)) ↔ _
        exact mem_map_injective_iff (Sym2.map.injective f.injective) _ _
      have ha : f a ∈ (p.map f.toHom).support ↔ a ∈ p.support := by
        rw [SimpleGraph.Walk.support_map]
        exact mem_map_injective_iff f.injective _ _
      have hb : f b ∈ (p.map f.toHom).support ↔ b ∈ p.support := by
        rw [SimpleGraph.Walk.support_map]
        exact mem_map_injective_iff f.injective _ _
      simp only [hadj, hedge, ha, hb]

theorem chordCount_map_iso {V W : Type*} [Fintype V] [Fintype W]
    [DecidableEq V] [DecidableEq W] {G : SimpleGraph V} {H : SimpleGraph W}
    (f : G ≃g H) {u v : V} (p : G.Walk u v) :
    Walk.chordCount (p.map f.toHom) = Walk.chordCount p := by
  let fe : Sym2 V ↪ Sym2 W :=
    ⟨Sym2.map f, Sym2.map.injective f.injective⟩
  have hfin : Walk.chordFinset (p.map f.toHom) =
      (Walk.chordFinset p).map fe := by
    ext e
    induction e using Sym2.inductionOn with
    | _ a b =>
        let a' := f.symm a
        let b' := f.symm b
        have heq : s(a, b) = fe s(a', b') := by
          simp [fe, a', b']
        rw [heq, Finset.mem_map]
        simp only [Walk.mem_chordFinset]
        constructor
        · intro h
          have h' : (p.map f.toHom).IsChord (s(a', b').map f) := by
            simpa [fe] using h
          exact ⟨s(a', b'), (isChord_map_iso_iff f p _).mp h', rfl⟩
        · rintro ⟨e', he', heq'⟩
          have heq'' : e' = s(a', b') := fe.injective heq'
          subst e'
          have h' := (isChord_map_iso_iff f p s(a', b')).mpr he'
          simpa [fe] using h'
  rw [Walk.chordCount, Walk.chordCount, hfin, Finset.card_map]

/-- A graph embedding preserves the chord relation.  Unlike a graph homomorphism,
an embedding reflects adjacency, which is exactly what is needed here. -/
theorem isChord_map_embedding_iff {V W : Type*} {G : SimpleGraph V}
    {H : SimpleGraph W} (f : G ↪g H) {u v : V} (p : G.Walk u v)
    (e : Sym2 V) :
    (p.map f.toHom).IsChord (e.map f) ↔ p.IsChord e := by
  induction e using Sym2.inductionOn with
  | _ a b =>
      change (p.map f.toHom).IsChord s(f a, f b) ↔ p.IsChord s(a, b)
      rw [SimpleGraph.Walk.isChord_sym2Mk, SimpleGraph.Walk.isChord_sym2Mk]
      have hedge : s(f a, f b) ∈ (p.map f.toHom).edges ↔ s(a, b) ∈ p.edges := by
        rw [SimpleGraph.Walk.edges_map]
        change (Sym2.map f s(a, b) ∈ p.edges.map (Sym2.map f)) ↔ _
        exact mem_map_injective_iff (Sym2.map.injective f.injective) _ _
      have ha : f a ∈ (p.map f.toHom).support ↔ a ∈ p.support := by
        rw [SimpleGraph.Walk.support_map]
        exact mem_map_injective_iff f.injective _ _
      have hb : f b ∈ (p.map f.toHom).support ↔ b ∈ p.support := by
        rw [SimpleGraph.Walk.support_map]
        exact mem_map_injective_iff f.injective _ _
      simp only [f.map_adj_iff, hedge, ha, hb]

/-- A graph embedding preserves the number of chords of a walk.  Although the
target type can contain additional vertices, every chord of the mapped walk has
both endpoints in the mapped support and therefore comes uniquely from a source
edge. -/
theorem chordCount_map_embedding {V W : Type*} [Fintype V] [Fintype W]
    [DecidableEq V] [DecidableEq W] {G : SimpleGraph V} {H : SimpleGraph W}
    (f : G ↪g H) {u v : V} (p : G.Walk u v) :
    Walk.chordCount (p.map f.toHom) = Walk.chordCount p := by
  let fe : Sym2 V ↪ Sym2 W :=
    ⟨Sym2.map f, Sym2.map.injective f.injective⟩
  have hfin : Walk.chordFinset (p.map f.toHom) =
      (Walk.chordFinset p).map fe := by
    ext e
    induction e using Sym2.inductionOn with
    | _ a b =>
        simp only [Walk.mem_chordFinset, Finset.mem_map]
        constructor
        · intro he
          have ha : a ∈ (p.map f.toHom).support := by
            simpa [SimpleGraph.Walk.isChord_sym2Mk] using he.2.2.1
          have hb : b ∈ (p.map f.toHom).support := by
            simpa [SimpleGraph.Walk.isChord_sym2Mk] using he.2.2.2
          rw [SimpleGraph.Walk.support_map] at ha hb
          obtain ⟨a', ha', rfl⟩ := List.mem_map.mp ha
          obtain ⟨b', hb', rfl⟩ := List.mem_map.mp hb
          refine ⟨s(a', b'), (isChord_map_embedding_iff f p _).mp ?_, by simp [fe]⟩
          simpa using he
        · rintro ⟨e', he', heq⟩
          rw [← heq]
          exact (isChord_map_embedding_iff f p e').mpr he'
  rw [Walk.chordCount, Walk.chordCount, hfin, Finset.card_map]

theorem cycle_chordless_of_hub_not_mem (m : ℕ) {u : Vertex m}
    (p : (graph m).Walk u u) (hp : p.IsCycle) (hhub : hub m ∉ p.support) :
    p.IsChordless := by
  classical
  have hS : ∀ z ∈ p.support, z ∈ {z | z ≠ hub m} := by
    intro z hz hEq
    subst z
    exact hhub hz
  let q := p.induce {z | z ≠ hub m} hS
  let inc : nonhubGraph m ↪g graph m :=
    SimpleGraph.Embedding.induce {z | z ≠ hub m}
  have hmap : q.map inc.toHom = p := by
    dsimp [q, inc]
    exact SimpleGraph.Walk.map_induce p hS
  have hq : q.IsCycle := by
    apply SimpleGraph.Walk.IsCycle.of_map (f := inc.toHom)
    change (q.map (SimpleGraph.Embedding.induce {z | z ≠ hub m}).toHom).IsCycle
    rw [SimpleGraph.Walk.map_induce]
    exact hp
  have hqChordless := nonhub_cycle_chordless m q hq
  have hmapped := chordless_map_embedding inc q hqChordless
  rw [hmap] at hmapped
  exact hmapped

theorem cycle_chordCount_zero_of_hub_not_mem (m : ℕ) {u : Vertex m}
    (p : (graph m).Walk u u) (hp : p.IsCycle) (hhub : hub m ∉ p.support) :
    Walk.chordCount p = 0 := by
  rw [Walk.chordCount_eq_zero_iff]
  exact cycle_chordless_of_hub_not_mem m p hp hhub

theorem graph_cyclesHaveAtMostChords_ten (m : ℕ) :
    CyclesHaveAtMostChords (graph m) 10 := by
  classical
  intro u p hp
  by_cases hhub : hub m ∈ p.support
  · let q := p.rotate (hub m) hhub
    have hq : q.IsCycle := hp.rotate hhub
    have hbound := based_hub_cycle_chordCount_le_ten m q hq
    rw [chordCount_rotate_eq p (hub m) hhub] at hbound
    exact hbound
  · rw [cycle_chordCount_zero_of_hub_not_mem m p hp hhub]
    omega

theorem exists_nonhub_boundary_edge (m : ℕ) (s : Finset (Vertex m))
    (hin : ∃ u ∈ s, u ≠ hub m) (hout : ∃ v, v ≠ hub m ∧ v ∉ s) :
    ∃ u ∈ s, u ≠ hub m ∧ ∃ v, v ∉ s ∧ (graph m).Adj u v := by
  obtain ⟨u, hu, huNH⟩ := hin
  obtain ⟨v, hvNH, hv⟩ := hout
  let u' : NonhubVertex m := ⟨u, huNH⟩
  let v' : NonhubVertex m := ⟨v, hvNH⟩
  obtain ⟨p⟩ := nonhubGraph_connected m u' v'
  obtain ⟨a, b, ha, hb, hab⟩ :=
    walk_exists_boundary_edge {z : NonhubVertex m | z.1 ∈ s} p hu hv
  exact ⟨a.1, ha, a.2, b.1, hb, hab⟩

/-- Every nonempty proper vertex set contains a vertex with at most two
neighbors remaining in that set. -/
theorem exists_internal_degree_le_two (m : ℕ) (s : Finset (Vertex m))
    (hs : s.Nonempty) (hproper : s ≠ Finset.univ) :
    ∃ u ∈ s, (((graph m).neighborFinset u).filter fun v ↦ v ∈ s).card ≤ 2 := by
  classical
  by_cases hin : ∃ u ∈ s, u ≠ hub m
  · have hboundary :
        ∃ u ∈ s, u ≠ hub m ∧ ∃ v, v ∉ s ∧ (graph m).Adj u v := by
      by_cases hout : ∃ v, v ≠ hub m ∧ v ∉ s
      · exact exists_nonhub_boundary_edge m s hin hout
      · have hall : ∀ v, v ≠ hub m → v ∈ s := by
          intro v hv
          by_contra hvs
          exact hout ⟨v, hv, hvs⟩
        have hhub : hub m ∉ s := by
          intro hhs
          apply hproper
          ext v
          simp only [Finset.mem_univ, iff_true]
          by_cases hv : v = hub m
          · simpa [hv] using hhs
          · exact hall v hv
        let u := leaf m (leftLeaf m) 1
        have huNH : u ≠ hub m := by simp [u, leaf, hub]
        have hu : u ∈ s := hall u huNH
        have hadj : (graph m).Adj u (hub m) := by
          exact ((hub_adj_leaf_iff m (leftLeaf m) 1).2 (by
            simp [leftLeaf, attachmentPosition])).symm
        exact ⟨u, hu, huNH, hub m, hhub, hadj⟩
    obtain ⟨u, hu, huNH, v, hv, huv⟩ := hboundary
    refine ⟨u, hu, ?_⟩
    let N := (graph m).neighborFinset u
    let I := N.filter (· ∈ s)
    have hsub : I ⊆ N := Finset.filter_subset _ _
    have hvN : v ∈ N := by simpa [N] using huv
    have hvI : v ∉ I := by simp [I, hv]
    have hlt : I.card < N.card :=
      Finset.card_lt_card ((Finset.ssubset_iff_of_subset hsub).2 ⟨v, hvN, hvI⟩)
    have hdeg : N.card ≤ 3 := by
      have h := nonhub_degree_le_three m u huNH
      change ((graph m).neighborFinset u).card ≤ 3 at h
      simpa only [N] using h
    change I.card ≤ 2
    omega
  · obtain ⟨u, hu⟩ := hs
    have hueq : u = hub m := by
      by_contra hne
      exact hin ⟨u, hu, hne⟩
    subst u
    refine ⟨hub m, hu, ?_⟩
    have hempty : ((graph m).neighborFinset (hub m)).filter (· ∈ s) = ∅ := by
      ext v
      simp only [Finset.mem_filter, SimpleGraph.mem_neighborFinset, Finset.notMem_empty,
        iff_false, not_and]
      intro hvadj hvs
      have hveq : v = hub m := by
        by_contra hne
        exact hin ⟨v, hvs, hne⟩
      subst v
      exact hvadj.ne rfl
    rw [hempty]
    simp

/-- Every proper induced subgraph is three-colorable.  The proof deletes a
boundary vertex of internal degree at most two and extends the coloring. -/
theorem proper_induce_colorable_three (m : ℕ) (s : Finset (Vertex m))
    (hproper : s ≠ Finset.univ) :
    ((graph m).induce (s : Set (Vertex m))).Colorable 3 := by
  classical
  induction s using Finset.strongInductionOn with
  | _ s ih =>
      rcases s.eq_empty_or_nonempty with (rfl | hs)
      · let : IsEmpty ↥((∅ : Finset (Vertex m)) : Set (Vertex m)) :=
          ⟨fun z ↦ by simpa using z.2⟩
        exact SimpleGraph.Colorable.of_isEmpty 3
      · obtain ⟨u, hu, hdeg⟩ := exists_internal_degree_le_two m s hs hproper
        let t := s.erase u
        have hts : t ⊂ s := Finset.erase_ssubset hu
        have htproper : t ≠ Finset.univ := by
          intro ht
          have : s = Finset.univ := by
            ext v
            simp only [Finset.mem_univ, iff_true]
            have hvt : v ∈ t := by rw [ht]; simp
            exact Finset.erase_subset u s hvt
          exact hproper this
        obtain ⟨c⟩ := ih t hts htproper
        let Nt := ((graph m).neighborFinset u).filter (· ∈ t)
        let used : Finset (Fin 3) := Nt.attach.image fun z ↦
          c ⟨z.1, (Finset.mem_filter.mp z.2).2⟩
        have hNt : Nt.card ≤ 2 := by
          apply le_trans (Finset.card_le_card ?_) hdeg
          intro v hv
          have hvt : v ∈ t := (Finset.mem_filter.mp hv).2
          have hvs : v ∈ s := Finset.erase_subset u s hvt
          exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hv).1, hvs⟩
        have hused : used.card ≤ 2 := by
          apply le_trans Finset.card_image_le
          simpa [used, Nt] using hNt
        have husedlt : used.card < (Finset.univ : Finset (Fin 3)).card := by
          simpa using (show used.card < 3 by omega)
        obtain ⟨q, _hqUniv, hq⟩ := Finset.exists_mem_notMem_of_card_lt_card husedlt
        let f : ↥(s : Set (Vertex m)) → Fin 3 := fun z ↦
          if hz : z.1 = u then q else
            c ⟨z.1, Finset.mem_erase.mpr ⟨hz, z.2⟩⟩
        have hq_ne (z : ↥(s : Set (Vertex m))) (hz : z.1 ≠ u)
            (huz : (graph m).Adj u z.1) : q ≠ f z := by
          have hzNt : z.1 ∈ Nt := Finset.mem_filter.mpr
            ⟨by simpa using huz, Finset.mem_erase.mpr ⟨hz, z.2⟩⟩
          let zNt : {v // v ∈ Nt} := ⟨z.1, hzNt⟩
          have hmem : c ⟨z.1, (Finset.mem_filter.mp hzNt).2⟩ ∈ used := by
            apply Finset.mem_image.mpr
            exact ⟨zNt, Finset.mem_attach _ _, rfl⟩
          intro heq
          apply hq
          have hf : f z = c ⟨z.1, (Finset.mem_filter.mp hzNt).2⟩ := by
            simp only [f, dif_neg hz]
          exact (heq.trans hf).symm ▸ hmem
        refine ⟨SimpleGraph.Coloring.mk f ?_⟩
        intro a b hab
        by_cases ha : a.1 = u
        · have hb : b.1 ≠ u := by
            intro hb
            apply hab.ne
            exact Subtype.ext (ha.trans hb.symm)
          have hub : (graph m).Adj u b.1 := by simpa [ha] using hab
          simpa [f, ha, hb] using hq_ne b hb hub
        · by_cases hb : b.1 = u
          · have hua : (graph m).Adj u a.1 := by simpa [hb] using hab.symm
            simpa [f, ha, hb] using (hq_ne a ha hua).symm
          · have hab' : ((graph m).induce (t : Set (Vertex m))).Adj
                ⟨a.1, Finset.mem_erase.mpr ⟨ha, a.2⟩⟩
                ⟨b.1, Finset.mem_erase.mpr ⟨hb, b.2⟩⟩ := hab
            simpa [f, ha, hb] using c.valid hab'

theorem locallyThreeColorable (m r : ℕ) (hr : r < 20 * m + 31) :
    LocallyThreeColorable (graph m) r := by
  intro s hs
  apply SimpleGraph.chromaticNumber_le_iff_colorable.mpr
  apply proper_induce_colorable_three m s
  intro hsuniv
  have hcard : s.card = 20 * m + 31 := by
    rw [hsuniv, Finset.card_univ, card_vertex]
  omega

noncomputable def vertexEquivFin (m : ℕ) : Vertex m ≃ Fin (20 * m + 31) :=
  (Fintype.equivFin (Vertex m)).trans (finCongr (card_vertex m))

noncomputable def finGraph (m : ℕ) : SimpleGraph (Fin (20 * m + 31)) :=
  (graph m).map (vertexEquivFin m).toEmbedding

theorem finGraph_chromatic_four (m : ℕ) : ChromaticFour (finGraph m) := by
  apply SimpleGraph.chromaticNumber_eq_iff_colorable_not_colorable.mpr
  constructor
  · exact (colorable_four m).map (vertexEquivFin m).toEmbedding
  · intro hthree
    apply not_colorable_three m
    exact SimpleGraph.Colorable.of_hom
      (SimpleGraph.Hom.map (vertexEquivFin m) (graph m)
        (fun {_ _} h ↦ (vertexEquivFin m).injective.ne h.ne)) hthree

theorem finGraph_cliqueFree_four (m : ℕ) : (finGraph m).CliqueFree 4 := by
  rw [finGraph, SimpleGraph.cliqueFree_map_iff]
  exact cliqueFree_four m

theorem finGraph_cyclesHaveAtMostChords_ten (m : ℕ) :
    CyclesHaveAtMostChords (finGraph m) 10 := by
  classical
  let e := vertexEquivFin m
  let iso : graph m ≃g finGraph m := by
    dsimp only [finGraph]
    exact SimpleGraph.Iso.map e (graph m)
  intro u p hp
  let q := p.map iso.symm.toHom
  have hq : q.IsCycle := hp.map iso.symm.injective
  have hbound := graph_cyclesHaveAtMostChords_ten m _ q hq
  have hcount : Walk.chordCount q = Walk.chordCount p := chordCount_map_iso iso.symm p
  rw [hcount] at hbound
  exact hbound

theorem finGraph_locallyThreeColorable (m r : ℕ) (hr : r < 20 * m + 31) :
    LocallyThreeColorable (finGraph m) r := by
  classical
  intro s hs
  let e := vertexEquivFin m
  let t : Finset (Vertex m) := s.map e.symm.toEmbedding
  have htcard : t.card ≤ r := by simpa [t] using hs
  have hnative := locallyThreeColorable m r hr t htcard
  apply SimpleGraph.chromaticNumber_le_iff_colorable.mpr
  obtain ⟨c⟩ := SimpleGraph.chromaticNumber_le_iff_colorable.mp hnative
  refine ⟨SimpleGraph.Coloring.mk (fun z ↦ c ⟨e.symm z.1, ?_⟩) ?_⟩
  · apply Finset.mem_map.mpr
    exact ⟨z.1, z.2, rfl⟩
  · intro a b hab
    apply c.valid
    change (graph m).Adj (e.symm a.1) (e.symm b.1)
    change (finGraph m).Adj a.1 b.1 at hab
    rw [finGraph, SimpleGraph.map_adj] at hab
    obtain ⟨x, y, hxy, hxa, hyb⟩ := hab
    have hx : x = e.symm a.1 := by
      apply e.injective
      simpa [e] using hxa
    have hy : y = e.symm b.1 := by
      apply e.injective
      simpa [e] using hyb
    simpa [hx, hy] using hxy

end Counterexample

/-- An odd chorded cycle in an induced subgraph is the same cycle in the
ambient graph.  Inducedness is essential for preservation of the exact chord
set; it is supplied by Mathlib's canonical graph embedding. -/
theorem hasOddCycleWithAtLeastChords_of_induce {V : Type*} [Fintype V]
    [DecidableEq V] (G : SimpleGraph V) (s : Finset V) (d : ℕ)
    (h : HasOddCycleWithAtLeastChords (G.induce (s : Set V)) d) :
    HasOddCycleWithAtLeastChords G d := by
  classical
  obtain ⟨u, p, hp, hodd, hchords⟩ := h
  let f : G.induce (s : Set V) ↪g G :=
    SimpleGraph.Embedding.induce (s : Set V)
  refine ⟨f u, p.map f.toHom, hp.map f.injective, ?_, ?_⟩
  · rw [SimpleGraph.Walk.length_map]
    exact hodd
  · rw [Counterexample.chordCount_map_embedding f p]
    exact hchords

/-- Voss's affirmative conclusion, using the finite critical induced core
and the complete maximal-ear case analysis. -/
theorem erdos_1091_affirmative_of_not_colorable_three {V : Type} [Fintype V]
    (G : SimpleGraph V) (hnot : ¬ G.Colorable 3) (hfree : G.CliqueFree 4) :
    HasOddCycleWithAtLeastChords G 2 := by
  classical
  obtain ⟨W, hdegree, htwo⟩ := Erdos58.Critical.exists_vertexTwoConnected_witness
    (G := G) (n := 3) (by omega) hnot
  let H := Erdos58.Critical.H G W
  have hHfree : H.CliqueFree 4 :=
    hfree.comap (SimpleGraph.Embedding.induce (W.S : Set V)).isContained
  have hHtwo : ¬ H.Colorable 2 := fun hcol => W.not_colorable (hcol.mono (by omega))
  obtain ⟨z, C, hC⟩ := Voss.exists_shortestOddCycle_of_not_colorable_two hHtwo
  have hHresult : Voss.HasOddCycleWithTwoChords H := by
    by_contra hno
    obtain ⟨E, hlen, hmax⟩ := hC.exists_maximal_ear hHfree hdegree hno htwo.1 htwo.2
    have hdelete : ∀ v, (H.induce ({v}ᶜ : Set (Erdos58.Critical.Carrier G W))).Colorable 3 := by
      intro v
      have heq : ({v}ᶜ : Set (Erdos58.Critical.Carrier G W)) = {w | w ≠ v} := by
        ext w
        simp
      rw [heq]
      exact Erdos58.Critical.colorable_delete (G := G) W v
    have hcolH : H.Colorable 3 :=
      @Voss.colorable_of_maximal_ear (Erdos58.Critical.Carrier G W)
        (Finset.Subtype.fintype W.S) H inferInstance z C hC hno E hlen hmax hdegree hdelete
    exact W.not_colorable hcolH
  exact hasOddCycleWithAtLeastChords_of_induce G W.S 2
    ((hasOddCycleWithAtLeastChords_two_iff H).mpr hHresult)

/-- Affirmative resolution of the first question of Problem 1091. Finite
relabeling removes any universe restriction from the linkage argument. -/
theorem erdos_1091_affirmative {V : Type*} [Fintype V]
    (G : SimpleGraph V) (hfour : ChromaticFour G) (hfree : G.CliqueFree 4) :
    HasOddCycleWithAtLeastChords G 2 := by
  classical
  let e := Fintype.equivFin V
  let H := G.map e.toEmbedding
  let f : G ≃g H := SimpleGraph.Iso.map e G
  have hHnot : ¬ H.Colorable 3 := by
    intro hc
    have hGcol := SimpleGraph.Colorable.of_hom f.toHom hc
    have hle := hGcol.chromaticNumber_le
    rw [hfour] at hle
    norm_num at hle
  have hHfree : H.CliqueFree 4 := hfree.comap f.symm.toEmbedding.isContained
  obtain ⟨z, p, hp, ho, hc⟩ := erdos_1091_affirmative_of_not_colorable_three H hHnot hHfree
  refine ⟨f.symm z, p.map f.symm.toHom, hp.map f.symm.injective, ?_, ?_⟩
  · simpa only [SimpleGraph.Walk.length_map] using ho
  · rw [Counterexample.chordCount_map_iso f.symm p]
    exact hc

/-- Reduction of the affirmative half to the vertex-critical case.  This is
the finite critical-core step used by Voss: choose an inclusion-minimal
non-three-colorable induced subgraph, apply the critical theorem there, and
map its witnessed cycle back to the original graph. -/
theorem affirmative_of_vertex_critical_case
    {V : Type*} [Fintype V] [DecidableEq V]
    (hcritical : ∀ (s : Finset V) (H : SimpleGraph s),
      H.chromaticNumber = (4 : ℕ∞) →
      (∀ v : s, (H.induce ({v}ᶜ : Set s)).Colorable 3) →
      H.CliqueFree 4 → HasOddCycleWithAtLeastChords H 2) :
    ∀ (G : SimpleGraph V), ChromaticFour G → G.CliqueFree 4 →
      HasOddCycleWithAtLeastChords G 2 := by
  intro G hfour hfree
  classical
  obtain ⟨s, hsChrom, hsDelete⟩ :=
    SimpleGraph.exists_induced_vertex_critical G 4 (by omega) hfour
  let H := G.induce (s : Set V)
  have hHfree : H.CliqueFree 4 :=
    hfree.comap (SimpleGraph.Embedding.induce (s : Set V)).isContained
  have hcycle : HasOddCycleWithAtLeastChords H 2 :=
    hcritical s H hsChrom hsDelete hHfree
  exact hasOddCycleWithAtLeastChords_of_induce G s 2 hcycle

/-- A four-chromatic `K₄`-free finite graph has at least five vertices.
The only four-chromatic graph on four vertices is the complete graph. -/
theorem five_le_card_of_chromaticFour_cliqueFree {V : Type*} [Fintype V]
    (G : SimpleGraph V) (hfour : ChromaticFour G) (hfree : G.CliqueFree 4) :
    5 ≤ Fintype.card V := by
  have hfour_le : (4 : ℕ∞) ≤ (Fintype.card V : ℕ∞) := by
    rw [← hfour]
    exact G.chromaticNumber_le_card
  have hfour_le' : 4 ≤ Fintype.card V := by exact_mod_cast hfour_le
  by_contra h
  have hcard : Fintype.card V = 4 := by omega
  have htop : G = ⊤ := by
    apply SimpleGraph.eq_top_of_chromaticNumber_eq_card
    simpa [ChromaticFour, hcard] using hfour
  apply hfree (Finset.univ : Finset V)
  constructor
  · rw [htop]
    simp [SimpleGraph.IsClique]
  · simp [hcard]

/-! ## The two-edge bipartization coloring endpoint

The exceptional outcome in Voss's structural classification is naturally
stated as deletion of at most two edges to obtain a bipartite graph.  The
following three lemmas turn that outcome into a three-coloring.  The only
obstruction is that the two deleted edges and all four cross edges form a
`K₄`; this is exactly where the clique-free hypothesis is used. -/

theorem colorable_three_of_deleted_edges_covered_by_independent_pair
    {V : Type*} {G : SimpleGraph V} {E : Set (Sym2 V)}
    (c : (G.deleteEdges E).Coloring (Fin 2))
    (a b : V) (hab : ¬ G.Adj a b)
    (hcover : ∀ e ∈ E, a ∈ e ∨ b ∈ e) :
    G.Colorable 3 := by
  classical
  let base : V → Fin 3 := fun x => Fin.castLE (by omega) (c x)
  let selected : V → Prop := fun x => x = a ∨ x = b
  let col : V → Fin 3 := fun x => if selected x then 2 else base x
  refine ⟨SimpleGraph.Coloring.mk col ?_⟩
  intro x y hxy
  by_cases hx : selected x
  · by_cases hy : selected y
    · exfalso
      rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
      · exact hxy.ne rfl
      · exact hab hxy
      · exact hab hxy.symm
      · exact hxy.ne rfl
    · dsimp only [col]
      rw [if_pos hx, if_neg hy]
      intro heq
      have hval := congrArg Fin.val heq
      have hbase : (base y).val < 2 := by simpa [base] using (c y).isLt
      norm_num at hval
      omega
  · by_cases hy : selected y
    · dsimp only [col]
      rw [if_neg hx, if_pos hy]
      intro heq
      have hval := congrArg Fin.val heq
      have hbase : (base x).val < 2 := by simpa [base] using (c x).isLt
      norm_num at hval
      omega
    · dsimp only [col]
      rw [if_neg hx, if_neg hy]
      intro heq
      have hcxy : c x = c y := by
        apply Fin.ext
        have hval := congrArg Fin.val heq
        simpa [base] using hval
      exact (c.valid (SimpleGraph.deleteEdges_adj.mpr ⟨hxy, by
        intro he
        rcases hcover s(x, y) he with ha | hb
        · have h : x = a ∨ y = a := by
            rcases (Sym2.mem_iff.mp ha) with h | h
            · exact Or.inl h.symm
            · exact Or.inr h.symm
          exact h.elim (fun hxa => hx (Or.inl hxa)) (fun hya => hy (Or.inl hya))
        · have h : x = b ∨ y = b := by
            rcases (Sym2.mem_iff.mp hb) with h | h
            · exact Or.inl h.symm
            · exact Or.inr h.symm
          exact h.elim (fun hxb => hx (Or.inr hxb)) (fun hyb => hy (Or.inr hyb))⟩)) hcxy

theorem independent_endpoint_pair_of_two_edges
    {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    (hfree : G.CliqueFree 4) {a b x y : V}
    (hab : G.Adj a b) (hxy : G.Adj x y) :
    ∃ u v, (u = a ∨ u = b) ∧ (v = x ∨ v = y) ∧ ¬ G.Adj u v := by
  by_cases hax : G.Adj a x
  · by_cases hay : G.Adj a y
    · by_cases hbx : G.Adj b x
      · by_cases hby : G.Adj b y
        · exfalso
          apply hfree {a, b, x, y}
          constructor
          · rw [SimpleGraph.isClique_iff]
            intro p hp q hq hpq
            simp at hp hq
            rcases hp with rfl | rfl | rfl | rfl <;>
              rcases hq with rfl | rfl | rfl | rfl
            · exact (hpq rfl).elim
            · exact hab
            · exact hax
            · exact hay
            · exact hab.symm
            · exact (hpq rfl).elim
            · exact hbx
            · exact hby
            · exact hax.symm
            · exact hbx.symm
            · exact (hpq rfl).elim
            · exact hxy
            · exact hay.symm
            · exact hby.symm
            · exact hxy.symm
            · exact (hpq rfl).elim
          · have habne := hab.ne
            have hxyne := hxy.ne
            have haxne := hax.ne
            have hayne := hay.ne
            have hbxne := hbx.ne
            have hbyne := hby.ne
            simp_all
        · exact ⟨b, y, Or.inr rfl, Or.inr rfl, hby⟩
      · exact ⟨b, x, Or.inr rfl, Or.inl rfl, hbx⟩
    · exact ⟨a, y, Or.inl rfl, Or.inr rfl, hay⟩
  · exact ⟨a, x, Or.inl rfl, Or.inl rfl, hax⟩

theorem colorable_three_of_cliqueFree_four_of_canBipartizeBy_le_two
    {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    (hfree : G.CliqueFree 4) {m : ℕ} (hm : m ≤ 2)
    (hbip : Erdos744.CanBipartizeBy G m) :
    G.Colorable 3 := by
  classical
  obtain ⟨E, hEG, hcard, hbip⟩ := hbip
  have hm_cases : m = 0 ∨ m = 1 ∨ m = 2 := by omega
  rcases hm_cases with rfl | rfl | rfl
  · have hE : E = ∅ := (Set.ncard_eq_zero).mp hcard
    subst E
    simpa using (SimpleGraph.Colorable.mono (by omega) hbip)
  · obtain ⟨e, rfl⟩ := Set.ncard_eq_one.mp hcard
    induction e using Sym2.ind with
    | _ a b =>
      have hab : G.Adj a b := by
        exact hEG (show s(a, b) ∈ ({s(a, b)} : Set (Sym2 V)) by simp)
      obtain ⟨c⟩ := hbip
      apply colorable_three_of_deleted_edges_covered_by_independent_pair
        c a a G.irrefl
      intro (e : Sym2 V) he
      have heq : e = s(a, b) := by simpa only [Set.mem_singleton_iff] using he
      subst e
      exact Or.inl (by simp)
  · obtain ⟨e, f, hef, rfl⟩ := Set.ncard_eq_two.mp hcard
    induction e using Sym2.ind with
    | _ a b =>
      induction f using Sym2.ind with
      | _ x y =>
        have hab : G.Adj a b := hEG
          (show s(a, b) ∈ ({s(a, b), s(x, y)} : Set (Sym2 V)) by simp)
        have hxy : G.Adj x y := hEG
          (show s(x, y) ∈ ({s(a, b), s(x, y)} : Set (Sym2 V)) by simp)
        obtain ⟨u, v, hu, hv, huv⟩ :=
          independent_endpoint_pair_of_two_edges hfree hab hxy
        obtain ⟨c⟩ := hbip
        apply colorable_three_of_deleted_edges_covered_by_independent_pair
          c u v huv
        intro (g : Sym2 V) hg
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
        rcases hg with rfl | rfl
        · left
          rcases hu with rfl | rfl <;> simp
        · right
          rcases hv with rfl | rfl <;> simp

/-- The precise structural consequence of Voss's bridge analysis used by
the formal endgame: a fully four-critical graph with no qualifying odd
cycle can be made bipartite by deleting at most two edges. -/
def VossBipartizationBound (V : Type u) [Fintype V] [DecidableEq V] : Prop :=
  ∀ (s : Finset V) (G : SimpleGraph s),
    Erdos744.IsCritical G 4 → G.CliqueFree 4 →
    ¬ HasOddCycleWithAtLeastChords G 2 →
    ∃ m ≤ 2, Erdos744.CanBipartizeBy G m

/-- Voss's bipartization lemma plus the three-edge Kempe lower bound for a
four-critical graph imply the affirmative half of Problem 1091. -/
theorem affirmative_of_vossBipartizationBound
    {V : Type u} [Fintype V] [DecidableEq V]
    (hVoss : VossBipartizationBound V) (G : SimpleGraph V)
    (hfour : ChromaticFour G) (hfree : G.CliqueFree 4) :
    HasOddCycleWithAtLeastChords G 2 := by
  apply affirmative_of_vertex_critical_case ?_ G hfour hfree
  intro s J hJfour hJdelete hJfree
  let : Nonempty s := Fintype.card_pos_iff.mp (by
    have hcard := five_le_card_of_chromaticFour_cliqueFree J hJfour hJfree
    omega)
  obtain ⟨H, hHJ, hHncol, hHcritical, _⟩ :=
    Erdos744.exists_critical_subgraph_le_of_vertex_deletions
      J 3 J.edgeSet.ncard
      (by
        intro hcol
        have hle := hcol.chromaticNumber_le
        rw [hJfour] at hle
        norm_num at hle)
      hJdelete (Erdos744.canBipartizeBy_allEdges J)
  have hHfree : H.CliqueFree 4 := hJfree.anti hHJ
  apply hasOddCycleWithAtLeastChords_mono hHJ
  by_contra hno
  obtain ⟨m, hm, hbip⟩ := hVoss s H hHcritical hHfree hno
  exact hHncol
    (colorable_three_of_cliqueFree_four_of_canBipartizeBy_le_two
      hHfree hm hbip)

/-- A second, particularly sharp possible interface to Voss's structural
classification.  It says that a fully four-critical `K₄`-free obstruction
without the desired odd cycle has maximum degree at most three. -/
def VossDegreeBound (V : Type u) [Fintype V] [DecidableEq V] : Prop := by
  classical
  exact ∀ (s : Finset V) (G : SimpleGraph s),
      Erdos744.IsCritical G 4 → G.CliqueFree 4 →
      ¬ HasOddCycleWithAtLeastChords G 2 → G.maxDegree ≤ 3

/-- The degree-bound interface closes the affirmative problem by Brooks'
theorem: a non-three-colorable graph of maximum degree three must either
contain a `K₄` or be an odd cycle, and the latter Brooks exception has
maximum degree two. -/
theorem affirmative_of_vossDegreeBound
    {V : Type u} [Fintype V] [DecidableEq V]
    (hVoss : VossDegreeBound V) (G : SimpleGraph V)
    (hfour : ChromaticFour G) (hfree : G.CliqueFree 4) :
    HasOddCycleWithAtLeastChords G 2 := by
  classical
  apply affirmative_of_vertex_critical_case ?_ G hfour hfree
  intro s J hJfour hJdelete hJfree
  let : Nonempty s := Fintype.card_pos_iff.mp (by
    have hcard := five_le_card_of_chromaticFour_cliqueFree J hJfour hJfree
    omega)
  obtain ⟨H, hHJ, hHncol, hHcritical, _⟩ :=
    Erdos744.exists_critical_subgraph_le_of_vertex_deletions
      J 3 J.edgeSet.ncard
      (by
        intro hcol
        have hle := hcol.chromaticNumber_le
        rw [hJfour] at hle
        norm_num at hle)
      hJdelete (Erdos744.canBipartizeBy_allEdges J)
  have hHfree : H.CliqueFree 4 := hJfree.anti hHJ
  apply hasOddCycleWithAtLeastChords_mono hHJ
  by_contra hno
  have hmax_le : H.maxDegree ≤ 3 := hVoss s H hHcritical hHfree hno
  have hmax_ge : 3 ≤ H.maxDegree := by
    by_contra hlt
    apply hHncol
    exact H.colorable_maxDegree_succ.mono (by omega)
  have hmax : H.maxDegree = 3 := by omega
  have hncol_max : ¬ H.Colorable H.maxDegree := by
    simpa [hmax] using hHncol
  have hnotfree : ¬ H.CliqueFree 4 := by
    simpa [hmax] using H.brooks hncol_max
  exact hnotfree hHfree

/-- A uniformly chord-bounded family of arbitrarily locally three-colorable
four-chromatic graphs refutes every proposed unbounded guarantee. -/
theorem not_exists_quantitativeGuarantee_of_counterexamples
    (hfamily : ∀ r : ℕ, ∃ (n : ℕ) (G : SimpleGraph (Fin n)),
      ChromaticFour G ∧ LocallyThreeColorable G r ∧ CyclesHaveAtMostChords G 10) :
    ¬ ∃ f : ℕ → ℕ, QuantitativeGuarantee f := by
  rintro ⟨f, hf⟩
  obtain ⟨r, hr⟩ := (tendsto_atTop_atTop.mp hf.1 11)
  obtain ⟨n, G, hfour, hlocal, hcycles⟩ := hfamily r
  obtain ⟨u, p, hpcycle, _hpodd, hmany⟩ := hf.2 r n G hfour hlocal
  have h11 : 11 ≤ f r := hr r le_rfl
  have hfew : Walk.chordCount p ≤ 10 := hcycles u p hpcycle
  omega

/-- The APSSV family, in its finite relabeling: it is four-chromatic and
`K₄`-free, is locally three-colorable to any prescribed radius, and has
at most ten chords on every cycle. -/
theorem apssv_counterexample_family (r : ℕ) :
    ∃ (n : ℕ) (G : SimpleGraph (Fin n)),
      ChromaticFour G ∧ G.CliqueFree 4 ∧ LocallyThreeColorable G r ∧
        CyclesHaveAtMostChords G 10 := by
  let m := r + 1
  refine ⟨20 * m + 31, Counterexample.finGraph m,
    Counterexample.finGraph_chromatic_four m,
    Counterexample.finGraph_cliqueFree_four m, ?_,
    Counterexample.finGraph_cyclesHaveAtMostChords_ten m⟩
  apply Counterexample.finGraph_locallyThreeColorable
  dsimp [m]
  omega

/-- Negative resolution of the quantitative part of Problem 1091. -/
theorem erdos_1091_quantitative_negative :
    ¬ ∃ f : ℕ → ℕ, QuantitativeGuarantee f := by
  apply not_exists_quantitativeGuarantee_of_counterexamples
  intro r
  obtain ⟨n, G, hfour, _hK4, hlocal, hcycles⟩ := apssv_counterexample_family r
  exact ⟨n, G, hfour, hlocal, hcycles⟩

/-- A fully four-critical counterexample on exactly `20*m+31` vertices.
The spanning edge-minimal extraction preserves the explicit family's
vertex count, clique exclusion, and uniform bound on every cycle. -/
theorem apssv_four_critical_family (m : ℕ) :
    ∃ G : SimpleGraph (Fin (20 * m + 31)),
      ChromaticFour G ∧ G.CliqueFree 4 ∧
      (∀ H : G.Subgraph, H < ⊤ → H.coe.Colorable 3) ∧
      CyclesHaveAtMostChords G 10 := by
  classical
  let G := Counterexample.finGraph m
  have : Nonempty (Fin (20 * m + 31)) := ⟨⟨0, by omega⟩⟩
  have hncol : ¬ G.Colorable 3 := by
    intro hc
    have hle := hc.chromaticNumber_le
    have hfour : G.chromaticNumber = 4 := Counterexample.finGraph_chromatic_four m
    rw [hfour] at hle
    norm_num at hle
  have hvertex : ∀ v, (G.induce ({v}ᶜ : Set (Fin (20 * m + 31)))).Colorable 3 := by
    intro v
    have hlocal := Counterexample.finGraph_locallyThreeColorable m (20 * m + 30) (by omega)
    have hc := hlocal (Finset.univ.erase v) (by simp)
    have heq : (↑(Finset.univ.erase v) : Set (Fin (20 * m + 31))) = {v}ᶜ := by
      ext w
      simp
    rw [heq] at hc
    exact SimpleGraph.chromaticNumber_le_iff_colorable.mp hc
  obtain ⟨H, hHG, _, hcritical, _⟩ :=
    Erdos744.exists_critical_subgraph_le_of_vertex_deletions G 3 G.edgeSet.ncard
      hncol hvertex (Erdos744.canBipartizeBy_allEdges G)
  refine ⟨H, hcritical.1, (Counterexample.finGraph_cliqueFree_four m).anti hHG, ?_, ?_⟩
  · exact ((Erdos744.isCritical_succ_iff H 3).mp hcritical).2.2
  · exact cyclesHaveAtMostChords_of_le hHG (Counterexample.finGraph_cyclesHaveAtMostChords_ten m)

/-- The two answers to Erdős Problem 1091: the two-diagonal assertion is
true, whereas the proposed unbounded quantitative guarantee is false. -/
theorem erdos_1091_resolution :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)), ChromaticFour G → G.CliqueFree 4 →
      HasOddCycleWithAtLeastChords G 2) ∧
    (¬ ∃ f : ℕ → ℕ, QuantitativeGuarantee f) :=
  ⟨fun _ G hfour hfree => erdos_1091_affirmative G hfour hfree,
    erdos_1091_quantitative_negative⟩

/-- Both answers: every four-chromatic, `K₄`-free finite graph has an odd
cycle with two chords, but no growing quantitative guarantee exists. -/
theorem erdos_1091 :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)),
      G.chromaticNumber = (4 : ℕ∞) → G.CliqueFree 4 →
        ∃ (u : Fin n) (p : G.Walk u u),
          p.IsCycle ∧ Odd p.length ∧ 2 ≤ Walk.chordCount p) ∧
    (¬ ∃ f : ℕ → ℕ,
      Tendsto f (@Filter.atTop ℕ Nat.instPreorder) (@Filter.atTop ℕ Nat.instPreorder) ∧
      ∀ (r n : ℕ) (G : SimpleGraph (Fin n)),
        G.chromaticNumber = (4 : ℕ∞) →
        (∀ s : Finset (Fin n), s.card ≤ r →
          (G.induce (s : Set (Fin n))).chromaticNumber ≤ (3 : ℕ∞)) →
        ∃ (u : Fin n) (p : G.Walk u u),
          p.IsCycle ∧ Odd p.length ∧ f r ≤ Walk.chordCount p) := by
  simpa only [ChromaticFour, LocallyThreeColorable,
    HasOddCycleWithAtLeastChords, QuantitativeGuarantee] using erdos_1091_resolution

/-- Explicit four-critical counterexamples with at most ten chords per cycle. -/
theorem erdos_1091_four_critical_counterexamples (m : ℕ) :
    ∃ G : SimpleGraph (Fin (20 * m + 31)),
      G.chromaticNumber = (4 : ℕ∞) ∧ G.CliqueFree 4 ∧
      (∀ H : G.Subgraph, H < ⊤ → H.coe.Colorable 3) ∧
      (∀ (u : Fin (20 * m + 31)) (p : G.Walk u u),
        p.IsCycle → Walk.chordCount p ≤ 10) := by
  simpa only [ChromaticFour, CyclesHaveAtMostChords] using apssv_four_critical_family m

#print axioms erdos_1091_affirmative
#print axioms erdos_1091_quantitative_negative
#print axioms apssv_four_critical_family
#print axioms erdos_1091_resolution
#print axioms erdos_1091
#print axioms erdos_1091_four_critical_counterexamples

end Erdos1091
