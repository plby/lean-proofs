/-
Adapted from the Apache-2.0-licensed polynomial-grid-minor-theorem development,
https://github.com/EdouardBonnet/polynomial-grid-minor-theorem,
commit fe2848173913a00d85c64d2a17af63f2cf0d4fbf,
proofs/Lax17Proofs/Source/Degree.lean.
Local changes: import paths and namespace; Lean 4.33 compatibility changes.
-/
import Mathlib.Combinatorics.SimpleGraph.Finite

namespace Erdos73Infrastructure

universe u v w

/-!
# Degree bounds for finite simple graphs

The grid-minor proof needs to state that an auxiliary subgraph has maximum
degree at most `3`.  This file provides a finset-neighborhood formulation that
is convenient inside existential theorem statements, without requiring a
separate `DecidableRel` instance for every graph that appears as a witness.
-/

namespace SimpleGraph

/-- `N` is exactly the neighbor set of `v` in `G`. -/
def IsNeighborFinset {V : Type*}
    (G : _root_.SimpleGraph V) (v : V) (N : Finset V) : Prop :=
  ∀ u : V, u ∈ N ↔ G.Adj v u

/-- A vertex has degree at most `d` if its neighbor set is represented by a
finset of cardinality at most `d`. -/
def DegreeAtMost {V : Type*}
    (G : _root_.SimpleGraph V) (v : V) (d : ℕ) : Prop :=
  ∃ N : Finset V, IsNeighborFinset G v N ∧ N.card ≤ d

/-- A vertex has degree exactly `d` if its neighbor set is represented by a
finset of cardinality `d`. -/
def DegreeEquals {V : Type*}
    (G : _root_.SimpleGraph V) (v : V) (d : ℕ) : Prop :=
  ∃ N : Finset V, IsNeighborFinset G v N ∧ N.card = d

/-- A graph has maximum degree at most `d`. -/
def MaxDegreeAtMost {V : Type*}
    (G : _root_.SimpleGraph V) (d : ℕ) : Prop :=
  ∀ v : V, DegreeAtMost G v d

namespace DegreeAtMost

/-- Degree upper bounds are monotone in the numerical bound. -/
theorem mono {V : Type*} {G : _root_.SimpleGraph V} {v : V} {d e : ℕ}
    (h : DegreeAtMost G v d) (hde : d ≤ e) :
    DegreeAtMost G v e := by
  rcases h with ⟨N, hN, hcard⟩
  exact ⟨N, hN, hcard.trans hde⟩

end DegreeAtMost

namespace MaxDegreeAtMost

/-- A chosen neighbor finset supplied by a maximum-degree certificate. -/
noncomputable def neighborFinset {V : Type*} {G : _root_.SimpleGraph V} {d : ℕ}
    (h : MaxDegreeAtMost G d) (v : V) : Finset V :=
  Classical.choose (h v)

theorem mem_neighborFinset {V : Type*} {G : _root_.SimpleGraph V} {d : ℕ}
    (h : MaxDegreeAtMost G d) (v u : V) :
    u ∈ neighborFinset h v ↔ G.Adj v u :=
  (Classical.choose_spec (h v)).1 u

theorem card_neighborFinset_le {V : Type*} {G : _root_.SimpleGraph V} {d : ℕ}
    (h : MaxDegreeAtMost G d) (v : V) :
    (neighborFinset h v).card ≤ d :=
  (Classical.choose_spec (h v)).2

end MaxDegreeAtMost

/-- Maximum-degree upper bounds are monotone in the numerical bound. -/
theorem maxDegreeAtMost_mono {V : Type*} {G : _root_.SimpleGraph V} {d e : ℕ}
    (h : MaxDegreeAtMost G d) (hde : d ≤ e) :
    MaxDegreeAtMost G e := by
  intro v
  exact DegreeAtMost.mono (h v) hde

/-- Passing to a spanning subgraph cannot increase the maximum degree. -/
theorem maxDegreeAtMost_of_le {V : Type*}
    {G H : _root_.SimpleGraph V} {d : ℕ}
    (hG : MaxDegreeAtMost G d) (hHG : H ≤ G) :
    MaxDegreeAtMost H d := by
  classical
  intro v
  let N : Finset V :=
    (MaxDegreeAtMost.neighborFinset hG v).filter fun u => H.Adj v u
  refine ⟨N, ?_, ?_⟩
  · intro u
    constructor
    · intro hu
      exact (Finset.mem_filter.mp hu).2
    · intro huv
      exact Finset.mem_filter.mpr
        ⟨(MaxDegreeAtMost.mem_neighborFinset hG v u).2 (hHG huv), huv⟩
  · exact (Finset.card_filter_le _ _).trans
      (MaxDegreeAtMost.card_neighborFinset_le hG v)

/-- A vertex has degree exactly one when it has a unique neighbor. -/
theorem degreeEquals_one_of_unique_neighbor {V : Type*} [DecidableEq V]
    {G : _root_.SimpleGraph V} {v u : V}
    (hadj : G.Adj v u) (huniq : ∀ w : V, G.Adj v w → w = u) :
    DegreeEquals G v 1 := by
  refine ⟨{u}, ?_, by simp⟩
  intro w
  constructor
  · intro hw
    have hwu : w = u := by simpa using hw
    simpa [hwu] using hadj
  · intro hvw
    simp [huniq w hvw]

/-- A degree-one vertex has at most one neighbor. -/
theorem DegreeEquals.one_adj_eq {V : Type*} [DecidableEq V]
    {G : _root_.SimpleGraph V} {v u w : V}
    (h : DegreeEquals G v 1) (hu : G.Adj v u) (hw : G.Adj v w) :
    u = w := by
  rcases h with ⟨N, hN, hcard⟩
  have huN : u ∈ N := (hN u).2 hu
  have hwN : w ∈ N := (hN w).2 hw
  rcases Finset.card_eq_one.mp hcard with ⟨a, ha⟩
  have hua : u = a := by simpa [ha] using huN
  have hwa : w = a := by simpa [ha] using hwN
  exact hua.trans hwa.symm

/-- A degree-one vertex has a unique neighbor, in existence form. -/
theorem DegreeEquals.one_exists_unique_adj {V : Type*} [DecidableEq V]
    {G : _root_.SimpleGraph V} {v : V}
    (h : DegreeEquals G v 1) :
    ∃ u : V, G.Adj v u ∧ ∀ w : V, G.Adj v w → w = u := by
  rcases h with ⟨N, hN, hcard⟩
  rcases Finset.card_eq_one.mp hcard with ⟨u, hN_eq⟩
  have huN : u ∈ N := by simp [hN_eq]
  refine ⟨u, (hN u).1 huN, ?_⟩
  intro w hw
  have hwN : w ∈ N := (hN w).2 hw
  simpa [hN_eq] using hwN

/-- A degree-two vertex has no neighbor other than two given distinct
neighbors. -/
theorem DegreeEquals.two_adj_eq_or_eq {V : Type*} [DecidableEq V]
    {G : _root_.SimpleGraph V} {v a b w : V}
    (h : DegreeEquals G v 2) (ha : G.Adj v a) (hb : G.Adj v b)
    (hab : a ≠ b) (hw : G.Adj v w) :
    w = a ∨ w = b := by
  classical
  rcases h with ⟨N, hN, hcard⟩
  have haN : a ∈ N := (hN a).2 ha
  have hbN : b ∈ N := (hN b).2 hb
  have hwN : w ∈ N := (hN w).2 hw
  let P : Finset V := {a, b}
  have hPsubset : P ⊆ N := by
    intro x hx
    simp [P] at hx
    rcases hx with rfl | rfl
    · exact haN
    · exact hbN
  have hPcard : P.card = 2 := by
    simp [P, hab]
  have hPN : P = N :=
    Finset.eq_of_subset_of_card_le hPsubset (by
      rw [hcard, hPcard])
  have hwP : w ∈ P := by
    simpa [hPN] using hwN
  simpa [P] using hwP

/-- A degree-two vertex adjacent to `a` has another neighbor distinct from
`a`. -/
theorem DegreeEquals.two_exists_adj_ne {V : Type*} [DecidableEq V]
    {G : _root_.SimpleGraph V} {v a : V}
    (h : DegreeEquals G v 2) (_ha : G.Adj v a) :
    ∃ b : V, G.Adj v b ∧ b ≠ a := by
  classical
  rcases h with ⟨N, hN, hcard⟩
  by_contra hnone
  have hsub : N ⊆ ({a} : Finset V) := by
    intro x hx
    by_contra hxa
    exact hnone ⟨x, (hN x).1 hx, by simpa using hxa⟩
  have hcard_le : N.card ≤ 1 := by
    have hcard_le' := Finset.card_le_card hsub
    simpa using hcard_le'
  omega

/-- A degree-two vertex adjacent to two distinct accounted-for neighbors has
no third neighbor. -/
theorem DegreeEquals.two_not_adj_of_ne {V : Type*} [DecidableEq V]
    {G : _root_.SimpleGraph V} {v a b w : V}
    (h : DegreeEquals G v 2) (ha : G.Adj v a) (hb : G.Adj v b)
    (hab : a ≠ b) (hwa : w ≠ a) (hwb : w ≠ b) :
    ¬ G.Adj v w := by
  intro hw
  rcases DegreeEquals.two_adj_eq_or_eq h ha hb hab hw with hwa' | hwb'
  · exact hwa hwa'
  · exact hwb hwb'

/-- Symmetric version of `DegreeEquals.two_not_adj_of_ne`. -/
theorem DegreeEquals.two_not_adj_to_of_ne {V : Type*} [DecidableEq V]
    {G : _root_.SimpleGraph V} {v a b w : V}
    (h : DegreeEquals G v 2) (ha : G.Adj v a) (hb : G.Adj v b)
    (hab : a ≠ b) (hwa : w ≠ a) (hwb : w ≠ b) :
    ¬ G.Adj w v := by
  intro hw
  exact DegreeEquals.two_not_adj_of_ne h ha hb hab hwa hwb
    hw.symm

/-- Finite graph core of the cross local no-skip argument.

The four vertices are ordered as `A -- U -- V -- D`.  The middle vertices are
saturated by the two consecutive local edges, while the left endpoint `A` is
saturated by an outside neighbor `L` and the edge to `U`.  Consequently the
three nonconsecutive local adjacencies touching `A` or the middle vertices are
impossible.  The right endpoint saturation is not needed for these three
undirected skip pairs, but the symmetric paper proof often supplies it as
well. -/
theorem DegreeEquals.cross_four_no_skip_left {α : Type*} [DecidableEq α]
    {G : _root_.SimpleGraph α} {A U M D L : α}
    (hAU : G.Adj A U) (hUM : G.Adj U M) (hMD : G.Adj M D)
    (hU : DegreeEquals G U 2) (hM : DegreeEquals G M 2)
    (hA : DegreeEquals G A 2) (hLA : G.Adj A L)
    (hLU : L ≠ U)
    (hAU_ne : A ≠ U) (hAD : A ≠ D) (hUD : U ≠ D)
    (hAM : A ≠ M) (hDM : D ≠ M) (hLD : L ≠ D) :
    ¬ G.Adj A M ∧ ¬ G.Adj A D ∧ ¬ G.Adj U D := by
  constructor
  · exact DegreeEquals.two_not_adj_to_of_ne hM
      hUM.symm hMD hUD hAU_ne hAD
  constructor
  · exact DegreeEquals.two_not_adj_of_ne hA hLA hAU hLU
      (fun h => hLD h.symm) (fun h => hUD h.symm)
  · exact DegreeEquals.two_not_adj_of_ne hU
      hAU.symm hUM hAM hAD.symm hDM

/-- Paper-shaped finite graph core of the cross local no-skip argument.

The local successor block is ordered as `A -- U -- V -- D`.  The endpoint
vertices `A` and `D` are each saturated by one outside neighbor and one local
neighbor, and the middle vertices `U,V` are saturated by the consecutive local
edges.  Therefore no nonconsecutive local adjacency `A--V`, `A--D`, or `U--D`
can occur.

The proof only needs the left endpoint saturation together with the two middle
degree-two facts; the right endpoint hypotheses are included so that the lemma
matches the Figure 8 successor invariant exactly. -/
theorem DegreeEquals.cross_four_no_skip {α : Type*} [DecidableEq α]
    {G : _root_.SimpleGraph α} {A U V D L R : α}
    (hAU : G.Adj A U) (hUV : G.Adj U V) (hVD : G.Adj V D)
    (hU : DegreeEquals G U 2) (hV : DegreeEquals G V 2)
    (hA : DegreeEquals G A 2) (_hD : DegreeEquals G D 2)
    (hLA : G.Adj A L) (_hDR : G.Adj D R)
    (hLU : L ≠ U) (_hRV : R ≠ V)
    (hAU_ne : A ≠ U) (hAD : A ≠ D) (hUD : U ≠ D)
    (hAV : A ≠ V) (hDV : D ≠ V) (hLD : L ≠ D) :
    ¬ G.Adj A V ∧ ¬ G.Adj A D ∧ ¬ G.Adj U D :=
  DegreeEquals.cross_four_no_skip_left hAU hUV hVD hU hV hA hLA
    hLU hAU_ne hAD hUD hAV hDV hLD

/-- A degree-two vertex has a second neighbor distinct from any given
neighbor. -/
theorem DegreeEquals.two_exists_ne_adj {V : Type*} [DecidableEq V]
    {G : _root_.SimpleGraph V} {v a : V}
    (h : DegreeEquals G v 2) (ha : G.Adj v a) :
    ∃ b : V, b ≠ a ∧ G.Adj v b := by
  classical
  rcases h with ⟨N, hN, hcard⟩
  have haN : a ∈ N := (hN a).2 ha
  by_contra hnone
  have hsubset : N ⊆ ({a} : Finset V) := by
    intro b hb
    by_cases hba : b = a
    · simp [hba]
    · have hbAdj : G.Adj v b := (hN b).1 hb
      exact False.elim (hnone ⟨b, hba, hbAdj⟩)
  have hcard_le : N.card ≤ 1 := by
    calc
      N.card ≤ ({a} : Finset V).card := Finset.card_le_card hsubset
      _ = 1 := by simp
  omega

/-- The finset-neighborhood formulation follows from mathlib's `degree` when
the adjacency relation is decidable. -/
theorem maxDegreeAtMost_of_degree_le
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : _root_.SimpleGraph V} [DecidableRel G.Adj] {d : ℕ}
    (h : ∀ v : V, G.degree v ≤ d) :
    MaxDegreeAtMost G d := by
  intro v
  refine ⟨G.neighborFinset v, ?_, h v⟩
  intro u
  simp

end SimpleGraph

end Erdos73Infrastructure
