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
import ErdosProblems.Erdos58.Arithmetic
import ErdosProblems.Erdos58.Basic
import Mathlib.Combinatorics.SimpleGraph.Hamiltonian
import Mathlib.Tactic

/-!
# An alternative, index-based start on the Gyárfás structural theorem

This file develops the longest-cycle argument using only indices in the
support list of an actual cycle.  In particular, the two cycles cut off by a
chord are constructed here as genuine `SimpleGraph.Walk.IsCycle`s; no fan or
path-family certificate is assumed.
-/

namespace Erdos58.StructuralAlt

open SimpleGraph

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V}

namespace Chord

/-- The cycle consisting of the initial arc from `v` to `x` and the chord
`xv`, oriented from `v` across the chord and then backwards along the arc. -/
def prefixCycle {v x : V} (p : G.Walk v v) (hx : x ∈ p.support)
    (hchord : G.Adj x v) : G.Walk v v :=
  (p.takeUntil x hx).reverse.cons hchord.symm

/-- The cycle consisting of the terminal arc from `x` to `v` and the chord
`vx`. -/
def suffixCycle {v x : V} (p : G.Walk v v) (hx : x ∈ p.support)
    (hchord : G.Adj x v) : G.Walk v v :=
  (p.dropUntil x hx).cons hchord.symm

@[simp] theorem prefixCycle_length {v x : V} (p : G.Walk v v)
    (hx : x ∈ p.support) (hchord : G.Adj x v) :
    (prefixCycle p hx hchord).length = p.support.idxOf x + 1 := by
  simp [prefixCycle, SimpleGraph.Walk.length_takeUntil]

@[simp] theorem suffixCycle_length {v x : V} (p : G.Walk v v)
    (hx : x ∈ p.support) (hchord : G.Adj x v) :
    (suffixCycle p hx hchord).length = p.length - p.support.idxOf x + 1 := by
  simp [suffixCycle, SimpleGraph.Walk.length_dropUntil]

private theorem idxOf_start {v x : V} (p : G.Walk v v)
    (hidx : 0 < p.support.idxOf x) : x ≠ v := by
  intro hxv
  subst x
  have : p.support.idxOf v = 0 := by
    apply (List.idxOf_eq_zero_iff_head_eq p.support_ne_nil).2
    exact p.head_support
  omega

/-- An internal chord endpoint at index at least two cuts off a genuine
simple cycle on the initial side. -/
theorem prefixCycle_isCycle {v x : V} {p : G.Walk v v} (hp : p.IsCycle)
    (hx : x ∈ p.support) (hchord : G.Adj x v)
    (hidx : 2 ≤ p.support.idxOf x) :
    (prefixCycle p hx hchord).IsCycle := by
  rw [SimpleGraph.Walk.isCycle_iff_isPath_tail_and_le_length]
  constructor
  · simp only [prefixCycle, SimpleGraph.Walk.tail_cons]
    apply (SimpleGraph.Walk.isPath_copy _ _ _).2
    exact (hp.isPath_takeUntil hx).reverse
  · simp only [prefixCycle_length]
    omega

/-- An internal chord endpoint at least two edges before the end cuts off a
genuine simple cycle on the terminal side. -/
theorem suffixCycle_isCycle {v x : V} {p : G.Walk v v} (hp : p.IsCycle)
    (hx : x ∈ p.support) (hchord : G.Adj x v)
    (hidx : p.support.idxOf x + 2 ≤ p.length) :
    (suffixCycle p hx hchord).IsCycle := by
  have htaken_nonempty : ¬(p.takeUntil x hx).Nil := by
    simpa only [SimpleGraph.Walk.nil_takeUntil] using hchord.ne.symm
  have hsplit :
      ((p.takeUntil x hx).append (p.dropUntil x hx)).IsCycle := by
    simpa using hp
  have hdrop : (p.dropUntil x hx).IsPath :=
    hsplit.isPath_of_append_right htaken_nonempty
  rw [SimpleGraph.Walk.isCycle_iff_isPath_tail_and_le_length]
  constructor
  · simp only [suffixCycle, SimpleGraph.Walk.tail_cons]
    apply (SimpleGraph.Walk.isPath_copy _ _ _).2
    exact hdrop
  · simp only [suffixCycle_length]
    omega

/-- Exact length certificate for the initial chord cycle. -/
theorem prefixCycle_atLength {v x : V} {p : G.Walk v v} (hp : p.IsCycle)
    (hx : x ∈ p.support) (hchord : G.Adj x v)
    (hidx : 2 ≤ p.support.idxOf x) :
    ∃ c : G.Walk v v,
      c.IsCycle ∧ c.length = p.support.idxOf x + 1 := by
  exact ⟨prefixCycle p hx hchord,
    prefixCycle_isCycle hp hx hchord hidx, prefixCycle_length p hx hchord⟩

/-- Exact length certificate for the terminal chord cycle. -/
theorem suffixCycle_atLength {v x : V} {p : G.Walk v v} (hp : p.IsCycle)
    (hx : x ∈ p.support) (hchord : G.Adj x v)
    (hidx : p.support.idxOf x + 2 ≤ p.length) :
    ∃ c : G.Walk v v,
      c.IsCycle ∧ c.length = p.length - p.support.idxOf x + 1 := by
  exact ⟨suffixCycle p hx hchord,
    suffixCycle_isCycle hp hx hchord hidx, suffixCycle_length p hx hchord⟩

end Chord

open Arithmetic

/-- An odd cycle with at least `2*j-1` proper chords at one vertex already
forces `j+1` distinct odd cycle lengths.  The endpoints are supplied merely
as a finset of vertices; all cycles and their simplicity proofs are built in
this theorem from the original cycle walk. -/
theorem oddCycleLengths_ge_succ_of_odd_cycle_many_chords {v : V}
    {p : G.Walk v v} (hp : p.IsCycle) (hpodd : Odd p.length)
    (X : Finset V)
    (hXmem : ∀ x ∈ X, x ∈ p.support)
    (hXadj : ∀ x ∈ X, G.Adj x v)
    (hXinternal : ∀ x ∈ X,
      2 ≤ p.support.idxOf x ∧ p.support.idxOf x + 2 ≤ p.length)
    {j : ℕ} (hj : 0 < j) (hXcard : 2 * j - 1 ≤ X.card) :
    j + 1 ≤ (oddCycleLengths G).ncard := by
  classical
  let E : Finset V := X.filter fun x ↦ Even (p.support.idxOf x)
  let O : Finset V := X.filter fun x ↦ ¬Even (p.support.idxOf x)
  have hhalf : ceilHalf X.card ≤ E.card ∨ ceilHalf X.card ≤ O.card := by
    simpa only [E, O] using
      (card_filter_ge_ceilHalf_or_card_filter_neg_ge_ceilHalf X
        (fun x ↦ Even (p.support.idxOf x)))
  have hjhalf : j ≤ ceilHalf X.card := by
    apply ceilHalf_mono at hXcard
    have hbase : ceilHalf (2 * j - 1) = j := by
      unfold ceilHalf
      omega
    simpa only [hbase] using hXcard
  have hfinite : (oddCycleLengths G).Finite := oddCycleLengths_finite G
  rcases hhalf with hE | hO
  · let L0 : Finset ℕ := E.image fun x ↦ p.support.idxOf x + 1
    let L : Finset ℕ := insert p.length L0
    have hcardL0 : L0.card = E.card := by
      rw [show L0 = E.image (fun x ↦ p.support.idxOf x + 1) by rfl,
        Finset.card_image_iff.mpr]
      intro a ha b hb hab
      have haX : a ∈ X := (Finset.mem_filter.mp ha).1
      have hidx : p.support.idxOf a = p.support.idxOf b :=
        Nat.add_right_cancel hab
      exact (List.idxOf_inj (hXmem a haX)).mp hidx
    have hlen_not : p.length ∉ L0 := by
      intro h
      obtain ⟨x, hxE, hxlen⟩ := Finset.mem_image.mp h
      have hxX : x ∈ X := (Finset.mem_filter.mp hxE).1
      have hxint := hXinternal x hxX
      omega
    have hcardL : L.card = E.card + 1 := by
      simp only [L, Finset.card_insert_of_notMem hlen_not, hcardL0]
    have hsub : (L : Set ℕ) ⊆ oddCycleLengths G := by
      intro n hn
      simp only [L, L0, Finset.coe_insert, Finset.coe_image,
        Set.mem_insert_iff, Set.mem_image] at hn
      rcases hn with rfl | ⟨x, hxE, rfl⟩
      · exact ⟨hpodd, v, p, hp, rfl⟩
      · have hxE' : x ∈ E := by simpa using hxE
        have hxX : x ∈ X := (Finset.mem_filter.mp hxE').1
        have hxeven : Even (p.support.idxOf x) :=
          (Finset.mem_filter.mp hxE').2
        obtain ⟨c, hc, hclen⟩ := Chord.prefixCycle_atLength hp
          (hXmem x hxX) (hXadj x hxX) (hXinternal x hxX).1
        exact ⟨hxeven.add_one, v, c, hc, hclen⟩
    have hLle : L.card ≤ (oddCycleLengths G).ncard := by
      simpa using Set.ncard_le_ncard hsub hfinite
    rw [hcardL] at hLle
    omega
  · let L0 : Finset ℕ :=
      O.image fun x ↦ p.length - p.support.idxOf x + 1
    let L : Finset ℕ := insert p.length L0
    have hcardL0 : L0.card = O.card := by
      rw [show L0 = O.image
          (fun x ↦ p.length - p.support.idxOf x + 1) by rfl,
        Finset.card_image_iff.mpr]
      intro a ha b hb hab
      have haX : a ∈ X := (Finset.mem_filter.mp ha).1
      have hbX : b ∈ X := (Finset.mem_filter.mp hb).1
      have haint := hXinternal a haX
      have hbint := hXinternal b hbX
      have hsub : p.length - p.support.idxOf a =
          p.length - p.support.idxOf b := Nat.add_right_cancel hab
      have hidx : p.support.idxOf a = p.support.idxOf b :=
        (tsub_right_inj (by omega) (by omega)).mp hsub
      exact (List.idxOf_inj (hXmem a haX)).mp hidx
    have hlen_not : p.length ∉ L0 := by
      intro h
      obtain ⟨x, hxO, hxlen⟩ := Finset.mem_image.mp h
      have hxX : x ∈ X := (Finset.mem_filter.mp hxO).1
      have hxint := hXinternal x hxX
      omega
    have hcardL : L.card = O.card + 1 := by
      simp only [L, Finset.card_insert_of_notMem hlen_not, hcardL0]
    have hsub : (L : Set ℕ) ⊆ oddCycleLengths G := by
      intro n hn
      simp only [L, L0, Finset.coe_insert, Finset.coe_image,
        Set.mem_insert_iff, Set.mem_image] at hn
      rcases hn with rfl | ⟨x, hxO, rfl⟩
      · exact ⟨hpodd, v, p, hp, rfl⟩
      · have hxO' : x ∈ O := by simpa using hxO
        have hxX : x ∈ X := (Finset.mem_filter.mp hxO').1
        have hxodd : Odd (p.support.idxOf x) :=
          Nat.not_even_iff_odd.mp (Finset.mem_filter.mp hxO').2
        have hxint := hXinternal x hxX
        obtain ⟨c, hc, hclen⟩ := Chord.suffixCycle_atLength hp
          (hXmem x hxX) (hXadj x hxX) hxint.2
        have hevenSub : Even (p.length - p.support.idxOf x) := by
          rcases hpodd with ⟨r, hr⟩
          rcases hxodd with ⟨s, hs⟩
          refine ⟨r - s, ?_⟩
          omega
        exact ⟨hevenSub.add_one, v, c, hc, hclen⟩
    have hLle : L.card ≤ (oddCycleLengths G).ncard := by
      simpa using Set.ncard_le_ncard hsub hfinite
    rw [hcardL] at hLle
    omega

/-- The Hamiltonian special case of the longest-odd-cycle argument, with no
certificate assumptions: if the initial vertex of an odd Hamiltonian cycle
has degree at least `2*j+1`, its genuine incident chords force `j+1`
different odd cycle lengths. -/
theorem oddCycleLengths_ge_succ_of_hamiltonian_odd_cycle_degree
    [DecidableRel G.Adj] {v : V} {p : G.Walk v v}
    (hp : p.IsHamiltonianCycle) (hpodd : Odd p.length)
    {j : ℕ} (hj : 0 < j) (hdegree : 2 * j + 1 ≤ G.degree v) :
    j + 1 ≤ (oddCycleLengths G).ncard := by
  classical
  let N : Finset V := G.neighborFinset v
  let internal : V → Prop := fun x ↦
    2 ≤ p.support.idxOf x ∧ p.support.idxOf x + 2 ≤ p.length
  let X : Finset V := N.filter internal
  let B : Finset V := N.filter fun x ↦ ¬internal x
  have hNcard : N.card = G.degree v := by
    simpa only [N, SimpleGraph.card_neighborFinset_eq_degree]
  have hpartition : X.card + B.card = N.card := by
    simpa only [X, B] using
      (Finset.card_filter_add_card_filter_not (s := N) internal)
  let a : V := p.getVert 1
  let b : V := p.getVert (p.length - 1)
  have hBsub : B ⊆ {a, b} := by
    intro x hxB
    have hxN : x ∈ N := (Finset.mem_filter.mp hxB).1
    have hxadj : G.Adj v x := by
      exact (SimpleGraph.mem_neighborFinset (G := G) (v := v) (w := x)).mp hxN
    have hxmem : x ∈ p.support := hp.mem_support x
    let i := p.support.idxOf x
    have higet : p.getVert i = x := p.getVert_support_idxOf hxmem
    have hi_le : i ≤ p.length := by
      have := List.idxOf_lt_length_of_mem hxmem
      rw [p.length_support] at this
      omega
    have hi_pos : 0 < i := by
      by_contra h
      have hi0 : i = 0 := by omega
      have hxv : x = v := by
        rw [← higet, hi0]
        exact p.getVert_zero
      exact hxadj.ne hxv.symm
    have hi_lt : i < p.length := by
      by_contra h
      have hilen : i = p.length := by omega
      have hxv : x = v := by
        rw [← higet, hilen]
        exact p.getVert_length
      exact hxadj.ne hxv.symm
    have hnotinternal : ¬internal x := (Finset.mem_filter.mp hxB).2
    have hi_cases : i = 1 ∨ i = p.length - 1 := by
      change ¬(2 ≤ i ∧ i + 2 ≤ p.length) at hnotinternal
      omega
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rcases hi_cases with hi | hi
    · exact Or.inl (by simpa only [a, hi] using higet.symm)
    · exact Or.inr (by simpa only [b, hi] using higet.symm)
  have hBcard : B.card ≤ 2 := by
    exact (Finset.card_le_card hBsub).trans Finset.card_le_two
  have hXcard : 2 * j - 1 ≤ X.card := by
    omega
  apply oddCycleLengths_ge_succ_of_odd_cycle_many_chords hp.isCycle hpodd X
  · intro x hxX
    exact hp.mem_support x
  · intro x hxX
    have hxN : x ∈ N := (Finset.mem_filter.mp hxX).1
    exact ((SimpleGraph.mem_neighborFinset (G := G) (v := v) (w := x)).mp hxN).symm
  · intro x hxX
    exact (Finset.mem_filter.mp hxX).2
  · exact hj
  · exact hXcard

/-- Hence an odd Hamiltonian graph having at most `j` odd cycle lengths has
degree at most `2*j` at the base of the Hamiltonian cycle. -/
theorem degree_le_two_mul_of_hamiltonian_odd_cycle
    [DecidableRel G.Adj] {v : V} {p : G.Walk v v}
    (hp : p.IsHamiltonianCycle) (hpodd : Odd p.length)
    {j : ℕ} (hj : 0 < j)
    (hodd : (oddCycleLengths G).ncard ≤ j) :
    G.degree v ≤ 2 * j := by
  by_contra hdegree
  have hmany := oddCycleLengths_ge_succ_of_hamiltonian_odd_cycle_degree
    hp hpodd hj (by omega)
  omega

/-- In the numerical regime of the Gyárfás structural theorem, an odd cycle
cannot be Hamiltonian.  This is the unconditional `V(C) = V(G)` branch of
the longest-odd-cycle proof. -/
theorem no_odd_hamiltonian_cycle_of_degree_and_length_bound
    [DecidableRel G.Adj] {j : ℕ} (hj : 0 < j)
    (hdegree : ∀ v : V, 2 * j + 1 ≤ G.degree v)
    (hodd : (oddCycleLengths G).ncard ≤ j) :
    ¬∃ (v : V) (p : G.Walk v v), p.IsHamiltonianCycle ∧ Odd p.length := by
  rintro ⟨v, p, hp, hpodd⟩
  have hle := degree_le_two_mul_of_hamiltonian_odd_cycle hp hpodd hj hodd
  have hge := hdegree v
  omega

end Erdos58.StructuralAlt
