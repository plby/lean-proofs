/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import Mathlib

/-!
# Fan certificates for Erdős problem 58

This file isolates the finite counting part of Gyárfás's two fan lemmas from
the bookkeeping needed to cut a cycle into arcs.  The certificates below are
graph-valued: every number which is counted is the length of an actual
`SimpleGraph.Walk`, together with its `IsCycle` or `IsPath` proof.  Thus the
results can be used by a structural graph proof without converting a purely
arithmetic witness back into a graph cycle.

`OddRimFan` is the certificate naturally obtained from a cycle of odd length
and `2 * j - 1` hub chords.  For every chord it records the two cycles cut off
by the chord.  Their lengths add to the rim length plus two, the left lengths
strictly increase, and the right lengths strictly decrease.  The theorem
`OddRimFan.realizes_odd_cycle_lengths` proves the odd-rim case of Gyárfás's
fan lemma.

`OddCycleFamily` and `PathFamily` are small downstream-facing interfaces for
the remaining (even-rim induction and arbitrary-endpoint path construction).
They deliberately retain the actual walks, rather than only their lengths.
-/

namespace Erdos58

open SimpleGraph

universe u v w

/-- `n` is realized as the length of an actual odd simple cycle in `G`. -/
def IsOddCycleLength {V : Type u} (G : SimpleGraph V) (n : ℕ) : Prop :=
  ∃ v : V, ∃ c : G.Walk v v, c.IsCycle ∧ Odd c.length ∧ c.length = n

/-- `G` realizes at least `j` distinct odd cycle lengths.  The witnessing
finset is retained, which avoids any global finiteness assumption on `V`. -/
def RealizesOddCycleLengths {V : Type u} (G : SimpleGraph V) (j : ℕ) : Prop :=
  ∃ lengths : Finset ℕ,
    j ≤ lengths.card ∧ ∀ n ∈ lengths, IsOddCycleLength G n

/-- A version that also records that all selected lengths are strictly below
`bound`.  This is the form used when the rim is a longest odd cycle. -/
def RealizesOddCycleLengthsBelow {V : Type u} (G : SimpleGraph V)
    (j bound : ℕ) : Prop :=
  ∃ lengths : Finset ℕ,
    j ≤ lengths.card ∧
      ∀ n ∈ lengths, IsOddCycleLength G n ∧ n < bound

/-- A graph-valued family of odd cycles with pairwise distinct lengths. -/
structure OddCycleFamily {V : Type u} (G : SimpleGraph V) (ι : Type w) where
  vertex : ι → V
  cycle : (i : ι) → G.Walk (vertex i) (vertex i)
  isCycle : ∀ i, (cycle i).IsCycle
  odd_length : ∀ i, Odd (cycle i).length
  length_injective : Function.Injective fun i ↦ (cycle i).length

namespace OddCycleFamily

variable {V : Type u} {V' : Type v} {G : SimpleGraph V} {G' : SimpleGraph V'}
  {ι : Type w}

/-- Map an odd-cycle family along an injective graph homomorphism.  In
particular, this transports a family in `H.coe` to the ambient graph via
`H.hom`. -/
def map (F : OddCycleFamily G ι) (f : G →g G') (hf : Function.Injective f) :
    OddCycleFamily G' ι where
  vertex i := f (F.vertex i)
  cycle i := (F.cycle i).map f
  isCycle i := (F.isCycle i).map hf
  odd_length i := by simpa only [SimpleGraph.Walk.length_map] using F.odd_length i
  length_injective := by
    simpa only [SimpleGraph.Walk.length_map] using F.length_injective

/-- The finset of lengths carried by a finite odd-cycle family. -/
noncomputable def lengths [Fintype ι] (F : OddCycleFamily G ι) : Finset ℕ :=
  Finset.univ.image fun i ↦ (F.cycle i).length

theorem card_lengths [Fintype ι] (F : OddCycleFamily G ι) :
    F.lengths.card = Fintype.card ι := by
  classical
  rw [lengths, Finset.card_image_of_injective _ F.length_injective,
    Finset.card_univ]

theorem realizes [Fintype ι] (F : OddCycleFamily G ι) :
    RealizesOddCycleLengths G (Fintype.card ι) := by
  classical
  refine ⟨F.lengths, F.card_lengths.ge, ?_⟩
  intro n hn
  rw [lengths] at hn
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hn
  exact ⟨F.vertex i, F.cycle i, F.isCycle i, F.odd_length i, rfl⟩

end OddCycleFamily

/-- A family of simple `x`--`y` paths whose lengths are injective and all
have the same parity.  This is the conclusion of Gyárfás's bipartite fan
lemma in a form that can be glued to external paths. -/
structure PathFamily {V : Type u} (G : SimpleGraph V) (x y : V) (ι : Type w) where
  path : ι → G.Walk x y
  isPath : ∀ i, (path i).IsPath
  length_injective : Function.Injective fun i ↦ (path i).length
  sameParity : ∀ i i', (path i).length % 2 = (path i').length % 2

/-- Any two walks with the same endpoints in a bipartite graph have lengths
of the same parity.  Mathlib states bipartiteness as two-colorability; closing
the two walks up gives the required even closed walk. -/
theorem bipartite_walk_length_mod_two_eq
    {V : Type u} {G : SimpleGraph V} (hG : G.IsBipartite)
    {x y : V} (p q : G.Walk x y) : p.length % 2 = q.length % 2 := by
  have heven : Even (p.append q.reverse).length :=
    (SimpleGraph.two_colorable_iff_forall_loop_even.mp hG) x (p.append q.reverse)
  rw [SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_reverse] at heven
  rw [Nat.even_iff] at heven
  omega

/-- A graph-valued system of paths with distinct lengths.  In a bipartite
graph its `toPathFamily` automatically acquires the equal-parity field. -/
structure DistinctPathSystem {V : Type u} (G : SimpleGraph V)
    (x y : V) (ι : Type w) where
  path : ι → G.Walk x y
  isPath : ∀ i, (path i).IsPath
  length_injective : Function.Injective fun i ↦ (path i).length

namespace DistinctPathSystem

variable {V : Type u} {G : SimpleGraph V} {x y : V} {ι : Type w}

/-- Supply the parity conclusion using bipartiteness. -/
def toPathFamily (F : DistinctPathSystem G x y ι) (hG : G.IsBipartite) :
    PathFamily G x y ι where
  path := F.path
  isPath := F.isPath
  length_injective := F.length_injective
  sameParity := fun i i' ↦ bipartite_walk_length_mod_two_eq hG (F.path i) (F.path i')

/-- Restrict the first `q` paths of a system indexed by `Fin r`. -/
def take {r q : ℕ} (F : DistinctPathSystem G x y (Fin r)) (hqr : q ≤ r) :
    DistinctPathSystem G x y (Fin q) where
  path i := F.path ⟨i, lt_of_lt_of_le i.isLt hqr⟩
  isPath i := F.isPath ⟨i, lt_of_lt_of_le i.isLt hqr⟩
  length_injective := by
    intro i i' hii'
    have hbig : (⟨i, lt_of_lt_of_le i.isLt hqr⟩ : Fin r) =
        ⟨i', lt_of_lt_of_le i'.isLt hqr⟩ := F.length_injective hii'
    apply Fin.ext
    exact congrArg (fun z : Fin r ↦ z.val) hbig

end DistinctPathSystem

namespace PathFamily

variable {V : Type u} {V' : Type v} {G : SimpleGraph V} {G' : SimpleGraph V'}
  {x y : V} {ι : Type w}

/-- Map a family along an injective graph homomorphism, preserving simplicity,
length distinctness, and parity. -/
def map (F : PathFamily G x y ι) (f : G →g G') (hf : Function.Injective f) :
    PathFamily G' (f x) (f y) ι where
  path i := (F.path i).map f
  isPath i := (F.isPath i).map hf
  length_injective := by
    simpa only [SimpleGraph.Walk.length_map] using F.length_injective
  sameParity i i' := by
    simpa only [SimpleGraph.Walk.length_map] using F.sameParity i i'

/-- The finset of lengths carried by a finite path family. -/
noncomputable def lengths [Fintype ι] (F : PathFamily G x y ι) : Finset ℕ :=
  Finset.univ.image fun i ↦ (F.path i).length

theorem card_lengths [Fintype ι] (F : PathFamily G x y ι) :
    F.lengths.card = Fintype.card ι := by
  classical
  rw [lengths, Finset.card_image_of_injective _ F.length_injective,
    Finset.card_univ]

theorem length_mem [Fintype ι] (F : PathFamily G x y ι) (i : ι) :
    (F.path i).length ∈ F.lengths := by
  classical
  exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩

theorem lengths_sameParity [Fintype ι] (F : PathFamily G x y ι)
    {m n : ℕ} (hm : m ∈ F.lengths) (hn : n ∈ F.lengths) :
    m % 2 = n % 2 := by
  classical
  rw [lengths] at hm hn
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hm
  obtain ⟨i', -, rfl⟩ := Finset.mem_image.mp hn
  exact F.sameParity i i'

theorem length_is_realized [Fintype ι] (F : PathFamily G x y ι)
    {n : ℕ} (hn : n ∈ F.lengths) :
    ∃ p : G.Walk x y, p.IsPath ∧ p.length = n := by
  classical
  rw [lengths] at hn
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hn
  exact ⟨F.path i, F.isPath i, rfl⟩

end PathFamily

/-- A realized odd-rim fan with `2 * j - 1` chords.

The two cycles associated to chord `i` are actual cycles in `G`.  For an
ordinary fan they are obtained by following the chord and one of the two rim
arcs.  The strictness fields encode the cyclic order of chord endpoints. -/
structure OddRimFan {V : Type u} (G : SimpleGraph V) (j : ℕ) where
  hub : V
  rim : G.Walk hub hub
  rim_isCycle : rim.IsCycle
  rim_odd : Odd rim.length
  leftCycle : Fin (2 * j - 1) → G.Walk hub hub
  rightCycle : Fin (2 * j - 1) → G.Walk hub hub
  left_isCycle : ∀ i, (leftCycle i).IsCycle
  right_isCycle : ∀ i, (rightCycle i).IsCycle
  length_sum : ∀ i,
    (leftCycle i).length + (rightCycle i).length = rim.length + 2
  left_length_lt_rim : ∀ i, (leftCycle i).length < rim.length
  right_length_lt_rim : ∀ i, (rightCycle i).length < rim.length
  left_strict : StrictMono fun i ↦ (leftCycle i).length
  right_strict : StrictAnti fun i ↦ (rightCycle i).length

namespace OddRimFan

variable {V : Type u} {G : SimpleGraph V} {j : ℕ}

private theorem odd_left_iff_not_odd_right (F : OddRimFan G j)
    (i : Fin (2 * j - 1)) :
    Odd (F.leftCycle i).length ↔ ¬Odd (F.rightCycle i).length := by
  have hodd : Odd ((F.leftCycle i).length + (F.rightCycle i).length) := by
    rw [F.length_sum i]
    rw [Nat.odd_add]
    constructor
    · intro
      norm_num
    · intro
      exact F.rim_odd
  rw [Nat.odd_add] at hodd
  exact hodd.trans Nat.not_odd_iff_even.symm

/-- In an odd-rim fan, exactly one cycle cut off by each chord is odd. -/
theorem odd_left_xor_odd_right (F : OddRimFan G j)
    (i : Fin (2 * j - 1)) :
    Xor (Odd (F.leftCycle i).length) (Odd (F.rightCycle i).length) := by
  rw [xor_iff_not_iff']
  simpa only [not_not] using (F.odd_left_iff_not_odd_right i).not_left

/-- The strengthened odd-rim case needed in the longest-cycle proof: all
selected chord-cycle lengths are strictly shorter than the rim. -/
theorem realizes_odd_cycle_lengths_below_rim (F : OddRimFan G j) (hj : 1 ≤ j) :
    RealizesOddCycleLengthsBelow G j F.rim.length := by
  classical
  let leftOdd : Finset (Fin (2 * j - 1)) :=
    Finset.univ.filter fun i ↦ Odd (F.leftCycle i).length
  let rightOdd : Finset (Fin (2 * j - 1)) :=
    Finset.univ.filter fun i ↦ Odd (F.rightCycle i).length
  have hright : rightOdd = Finset.univ \ leftOdd := by
    ext i
    simp only [rightOdd, leftOdd, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_sdiff]
    exact (F.odd_left_iff_not_odd_right i).not_left.symm
  have hcards : leftOdd.card + rightOdd.card = 2 * j - 1 := by
    rw [hright, add_comm, Finset.card_sdiff_add_card]
    have hunion : (Finset.univ : Finset (Fin (2 * j - 1))) ∪ leftOdd = Finset.univ := by
      ext i
      simp
    rw [hunion, Finset.card_univ, Fintype.card_fin]
  rcases (show j ≤ leftOdd.card ∨ j ≤ rightOdd.card by omega) with hleft | hrightLarge
  · let lengths : Finset ℕ :=
      leftOdd.image fun i ↦ (F.leftCycle i).length
    refine ⟨lengths, ?_, ?_⟩
    · dsimp [lengths]
      rw [Finset.card_image_of_injective _ F.left_strict.injective]
      exact hleft
    · intro n hn
      dsimp [lengths] at hn
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hn
      have hiOdd : Odd (F.leftCycle i).length := by
        exact (Finset.mem_filter.mp hi).2
      exact ⟨⟨F.hub, F.leftCycle i, F.left_isCycle i, hiOdd, rfl⟩,
        F.left_length_lt_rim i⟩
  · let lengths : Finset ℕ :=
      rightOdd.image fun i ↦ (F.rightCycle i).length
    refine ⟨lengths, ?_, ?_⟩
    · dsimp [lengths]
      rw [Finset.card_image_of_injective _ F.right_strict.injective]
      exact hrightLarge
    · intro n hn
      dsimp [lengths] at hn
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hn
      have hiOdd : Odd (F.rightCycle i).length := by
        exact (Finset.mem_filter.mp hi).2
      exact ⟨⟨F.hub, F.rightCycle i, F.right_isCycle i, hiOdd, rfl⟩,
        F.right_length_lt_rim i⟩

/-- The odd-rim case of Gyárfás's fan lemma: `2 * j - 1` hub chords on an
odd cycle realize at least `j` distinct odd cycle lengths. -/
theorem realizes_odd_cycle_lengths (F : OddRimFan G j) (hj : 1 ≤ j) :
    RealizesOddCycleLengths G j := by
  obtain ⟨lengths, hcard, hlengths⟩ := F.realizes_odd_cycle_lengths_below_rim hj
  exact ⟨lengths, hcard, fun n hn ↦ (hlengths n hn).1⟩

end OddRimFan

/-- The two monotone systems in Gyárfás's bipartite-fan path argument.

The systems consist of actual simple paths.  They need not be injective
across the two systems: the numerical lower bound guarantees that one system
already has at least `j + 1` members.  In the nonexceptional placement in the
paper, `leftCount + rightCount = m + 2 * j` with `m ≥ 1`; the exceptional
placement is handled by swapping the two endpoints before constructing this
certificate. -/
structure FanPathSystems {V : Type u} (G : SimpleGraph V)
    (j : ℕ) (x y : V) where
  leftCount : ℕ
  rightCount : ℕ
  left : DistinctPathSystem G x y (Fin leftCount)
  right : DistinctPathSystem G x y (Fin rightCount)
  enough : 2 * j + 1 ≤ leftCount + rightCount

namespace FanPathSystems

variable {V : Type u} {G : SimpleGraph V} {j : ℕ} {x y : V}

/-- One of two path systems whose total size is at least `2*j+1` contains
`j+1` paths.  Bipartiteness supplies their common parity. -/
theorem pathFamily (F : FanPathSystems G j x y) (hG : G.IsBipartite) :
    ∃ P : PathFamily G x y (Fin (j + 1)), P.lengths.card = j + 1 := by
  have henough := F.enough
  have hlarge : j + 1 ≤ F.leftCount ∨ j + 1 ≤ F.rightCount := by
    omega
  rcases hlarge with hleft | hright
  · let P := (F.left.take hleft).toPathFamily hG
    exact ⟨P, by simpa using P.card_lengths⟩
  · let P := (F.right.take hright).toPathFamily hG
    exact ⟨P, by simpa using P.card_lengths⟩

end FanPathSystems

/-- A checked certificate for the arbitrary-endpoint construction in the
bipartite fan lemma.  Unlike the conclusion, this stores the two explicit
monotone systems used in the proof and only their elementary size estimate. -/
structure BipartiteFanPathCertificate {V : Type u} (G : SimpleGraph V) (j : ℕ) where
  bipartite : G.IsBipartite
  systems : ∀ x y : V, x ≠ y → FanPathSystems G j x y

namespace BipartiteFanPathCertificate

variable {V : Type u} {G : SimpleGraph V} {j : ℕ}

/-- A bipartite fan path certificate gives `j + 1` actual simple paths of
different, equal-parity lengths between every two distinct vertices. -/
theorem realizes_paths (F : BipartiteFanPathCertificate G j)
    {x y : V} (hxy : x ≠ y) :
    ∃ P : PathFamily G x y (Fin (j + 1)),
      P.lengths.card = j + 1 ∧
      (∀ m ∈ P.lengths, ∀ n ∈ P.lengths, m % 2 = n % 2) ∧
      ∀ n ∈ P.lengths, ∃ p : G.Walk x y, p.IsPath ∧ p.length = n := by
  obtain ⟨P, hPcard⟩ := (F.systems x y hxy).pathFamily F.bipartite
  refine ⟨P, ?_, ?_, ?_⟩
  · exact hPcard
  · intro m hm n hn
    exact P.lengths_sameParity hm hn
  · intro n hn
    exact P.length_is_realized hn

end BipartiteFanPathCertificate

end Erdos58
