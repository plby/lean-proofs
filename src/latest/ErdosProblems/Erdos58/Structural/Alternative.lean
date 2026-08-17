/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos58.Arithmetic
import ErdosProblems.Erdos58.Basic
import ErdosProblems.Erdos58.Boundary
import Mathlib.Combinatorics.Additive.CauchyDavenport
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Tactic

/-!
# An alternative DFS endpoint bound for Erdős Problem 58

This file records the sharp additive-combinatorial estimate behind a possible
DFS proof of the structural theorem.  If the depths of the neighbours of a
deepest DFS vertex contain both parities, every absolute difference between
the two parity classes gives an odd cycle through that vertex.  The signed
difference set has at least `|A| + |B| - 1` elements, while absolute value has
fibres of size at most two.  Consequently at most `j` such differences allow
at most `2*j+1` neighbours.

The lemmas below isolate the precise sharp counting input.  Constructing the
associated cycles is the separate graph-geometric obligation in the
bipartite-fan branch.
-/

namespace Erdos58.Structural.Alternative

open scoped Pointwise

/-- A path together with two spokes from a vertex outside the path forms a
simple cycle.  This is the graph-geometric primitive needed to turn an
endpoint cross-difference into an actual odd cycle length. -/
theorem cycleAtLength_of_path_two_spokes
    {V : Type*} {G : SimpleGraph V} {a b z : V}
    (p : G.Walk a b) (hp : p.IsPath) (hab : a ≠ b)
    (hz : z ∉ p.support) (hza : G.Adj z a) (hbz : G.Adj b z) :
    Erdos58.CycleAtLength G (p.length + 2) := by
  let q : G.Path a z := ⟨p.concat hbz, hp.concat hz hbz⟩
  refine ⟨z, SimpleGraph.Walk.cons hza q, ?_, ?_⟩
  · apply q.cons_isCycle hza
    intro hedge
    rw [Sym2.eq_swap] at hedge
    have hlen : (q : G.Walk a z).length = 1 :=
      q.isPath.length_eq_one_of_mem_edges hedge
    have hp_pos : 0 < p.length := by
      rw [← SimpleGraph.Walk.not_nil_iff_lt_length]
      exact fun hnil ↦ hab (hp.nil_iff_eq.mp hnil)
    simp only [q, SimpleGraph.Walk.length_concat] at hlen
    omega
  · simp only [SimpleGraph.Walk.length_cons, q,
      SimpleGraph.Walk.length_concat]

/-- Two neighbors of the endpoint of a simple path, occurring at positions
of opposite parity, determine an odd cycle whose length is their absolute
position difference plus two. -/
theorem cycleAtLength_of_path_endpoint_cross
    {V : Type*} [DecidableEq V] {G : SimpleGraph V} {r z a b : V}
    (p : G.Walk r z) (hp : p.IsPath)
    (ha : a ∈ p.support) (hb : b ∈ p.support)
    (hza : G.Adj z a) (hzb : G.Adj z b)
    (hpar : p.support.idxOf a % 2 ≠ p.support.idxOf b % 2) :
    Erdos58.CycleAtLength G
      (Int.natAbs ((p.support.idxOf a : ℤ) - p.support.idxOf b) + 2) := by
  classical
  have hab : a ≠ b := by
    intro e
    exact hpar (e ▸ rfl)
  by_cases hle : p.support.idxOf a ≤ p.support.idxOf b
  · have ha' : a ∈ (p.takeUntil b hb).support := by
      rw [SimpleGraph.Walk.takeUntil_eq_take, SimpleGraph.Walk.support_copy,
        SimpleGraph.Walk.support_take, List.mem_take_iff_idxOf_lt ha]
      omega
    let q : G.Walk a b := (p.takeUntil b hb).dropUntil a ha'
    have hq : q.IsPath := (hp.takeUntil hb).dropUntil ha'
    have hz_ne_b : z ≠ b := hzb.ne
    have hz : z ∉ q.support := by
      intro hzq
      exact SimpleGraph.Walk.endpoint_notMem_support_takeUntil hp hb hz_ne_b
        ((p.takeUntil b hb).support_dropUntil_subset_support ha' hzq)
    have hidx : (p.takeUntil b hb).support.idxOf a = p.support.idxOf a :=
      (p.support_takeUntil_prefix_support hb).idxOf_eq_of_mem ha'
    have hqlen : q.length = p.support.idxOf b - p.support.idxOf a := by
      simp only [q, SimpleGraph.Walk.length_dropUntil,
        SimpleGraph.Walk.length_takeUntil, hidx]
    have hcycle := cycleAtLength_of_path_two_spokes q hq hab hz hza hzb.symm
    have hnonpos :
        (p.support.idxOf a : ℤ) - p.support.idxOf b ≤ 0 := by omega
    have habs :
        Int.natAbs ((p.support.idxOf a : ℤ) - p.support.idxOf b) =
          p.support.idxOf b - p.support.idxOf a := by
      apply Int.ofNat_inj.mp
      rw [← Int.natAbs_neg,
        Int.natAbs_of_nonneg (Int.neg_nonneg_of_nonpos hnonpos)]
      omega
    rw [habs]
    simpa [hqlen] using hcycle
  · have hle' : p.support.idxOf b ≤ p.support.idxOf a := by omega
    have hb' : b ∈ (p.takeUntil a ha).support := by
      rw [SimpleGraph.Walk.takeUntil_eq_take, SimpleGraph.Walk.support_copy,
        SimpleGraph.Walk.support_take, List.mem_take_iff_idxOf_lt hb]
      omega
    let q : G.Walk b a := (p.takeUntil a ha).dropUntil b hb'
    have hq : q.IsPath := (hp.takeUntil ha).dropUntil hb'
    have hz_ne_a : z ≠ a := hza.ne
    have hz : z ∉ q.support := by
      intro hzq
      exact SimpleGraph.Walk.endpoint_notMem_support_takeUntil hp ha hz_ne_a
        ((p.takeUntil a ha).support_dropUntil_subset_support hb' hzq)
    have hidx : (p.takeUntil a ha).support.idxOf b = p.support.idxOf b :=
      (p.support_takeUntil_prefix_support ha).idxOf_eq_of_mem hb'
    have hq_len : q.length = p.support.idxOf a - p.support.idxOf b := by
      simp only [q, SimpleGraph.Walk.length_dropUntil,
        SimpleGraph.Walk.length_takeUntil, hidx]
    have hcycle := cycleAtLength_of_path_two_spokes q hq hab.symm hz hzb hza.symm
    have hnonneg :
        0 ≤ (p.support.idxOf a : ℤ) - p.support.idxOf b := by omega
    have habs :
        Int.natAbs ((p.support.idxOf a : ℤ) - p.support.idxOf b) =
          p.support.idxOf a - p.support.idxOf b := by
      apply Int.ofNat_inj.mp
      rw [Int.natAbs_of_nonneg hnonneg]
      omega
    rw [habs]
    simpa [hq_len] using hcycle

/-- Opposite residues modulo two give an odd absolute integer difference. -/
theorem odd_natAbs_int_sub_of_mod_two_ne (m n : ℕ)
    (hpar : m % 2 ≠ n % 2) :
    Odd (Int.natAbs ((m : ℤ) - n)) := by
  by_cases hle : m ≤ n
  · have hnonpos : (m : ℤ) - n ≤ 0 := by omega
    have habs : Int.natAbs ((m : ℤ) - n) = n - m := by
      apply Int.ofNat_inj.mp
      rw [← Int.natAbs_neg,
        Int.natAbs_of_nonneg (Int.neg_nonneg_of_nonpos hnonpos)]
      omega
    rw [habs, Nat.odd_iff]
    omega
  · have hnonneg : 0 ≤ (m : ℤ) - n := by omega
    have habs : Int.natAbs ((m : ℤ) - n) = m - n := by
      apply Int.ofNat_inj.mp
      rw [Int.natAbs_of_nonneg hnonneg]
      omega
    rw [habs, Nat.odd_iff]
    omega

/-- Absolute value is at most two-to-one on any finite set of integers. -/
theorem card_le_two_mul_card_image_natAbs (S : Finset ℤ) :
    S.card ≤ 2 * (S.image Int.natAbs).card := by
  classical
  rw [Finset.card_eq_sum_card_image Int.natAbs S]
  calc
    ∑ y ∈ S.image Int.natAbs, (S.filter fun x => Int.natAbs x = y).card
        ≤ ∑ _y ∈ S.image Int.natAbs, 2 := by
          apply Finset.sum_le_sum
          intro y hy
          calc
            (S.filter fun x => Int.natAbs x = y).card ≤
                ({(y : ℤ), -(y : ℤ)} : Finset ℤ).card := by
              apply Finset.card_le_card
              intro x hx
              simp only [Finset.mem_filter] at hx
              simp only [Finset.mem_insert, Finset.mem_singleton]
              rw [Int.natAbs_eq_iff] at hx
              exact hx.2
            _ ≤ 2 := by
              exact (Finset.card_insert_le _ _).trans (by simp)
    _ = 2 * (S.image Int.natAbs).card := by simp [Nat.mul_comm]

/-- The absolute cross-difference set of two nonempty finite integer sets has
at least half the usual Cauchy--Davenport lower bound. -/
theorem add_card_sub_one_le_two_mul_card_absDiff
    (A B : Finset ℤ) (hA : A.Nonempty) (hB : B.Nonempty) :
    A.card + B.card - 1 ≤
      2 * ((A + -B).image Int.natAbs).card := by
  have hCD : A.card + (-B).card - 1 ≤ (A + -B).card :=
    cauchy_davenport_add_of_linearOrder_isCancelAdd hA hB.neg
  simpa using hCD.trans (card_le_two_mul_card_image_natAbs (A + -B))

/-- Sharp endpoint arithmetic: if all absolute cross-parity differences fit
in a `j`-element set, then the two parity classes together have at most
`2*j+1` elements. -/
theorem card_add_card_le_two_mul_add_one_of_absDiff_card_le
    (A B : Finset ℤ) (hA : A.Nonempty) (hB : B.Nonempty) {j : ℕ}
    (hcard : ((A + -B).image Int.natAbs).card ≤ j) :
    A.card + B.card ≤ 2 * j + 1 := by
  have hdiff := add_card_sub_one_le_two_mul_card_absDiff A B hA hB
  omega

/-- Contrapositive form used to produce an additional odd cycle length from
`2*j+2` or more neighbour depths. -/
theorem succ_le_card_absDiff_of_two_mul_add_two_le_card_add
    (A B : Finset ℤ) (hA : A.Nonempty) (hB : B.Nonempty) {j : ℕ}
    (hlarge : 2 * j + 2 ≤ A.card + B.card) :
    j + 1 ≤ ((A + -B).image Int.natAbs).card := by
  by_contra h
  have hcard : ((A + -B).image Int.natAbs).card ≤ j := by omega
  have := card_add_card_le_two_mul_add_one_of_absDiff_card_le A B hA hB hcard
  omega

/-- Graph-facing form of the endpoint estimate.  Once every absolute
cross-difference is realized (after adding the two spokes) as an odd cycle
length, a graph with exactly `j` odd cycle lengths permits at most `2*j+1`
depths in the two nonempty parity classes. -/
theorem card_add_card_le_two_mul_add_one_of_crossDiff_realized
    {V : Type*} [Finite V] (G : SimpleGraph V)
    (A B : Finset ℤ) (hA : A.Nonempty) (hB : B.Nonempty) {j : ℕ}
    (hrealized : ∀ d ∈ (A + -B).image Int.natAbs,
      d + 2 ∈ Erdos58.oddCycleLengths G)
    (hcount : (Erdos58.oddCycleLengths G).ncard = j) :
    A.card + B.card ≤ 2 * j + 1 := by
  let D : Finset ℕ := (A + -B).image Int.natAbs
  let L : Finset ℕ := D.image fun d => d + 2
  have hDL : D.card = L.card := by
    symm
    apply Finset.card_image_of_injOn
    intro a _ b _ hab
    change a + 2 = b + 2 at hab
    exact Nat.add_right_cancel hab
  have hsub : (L : Set ℕ) ⊆ Erdos58.oddCycleLengths G := by
    intro n hn
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hn
    exact hrealized d hd
  have hcardL : L.card ≤ (Erdos58.oddCycleLengths G).ncard := by
    simpa using Set.ncard_le_ncard hsub (Erdos58.oddCycleLengths_finite G)
  apply card_add_card_le_two_mul_add_one_of_absDiff_card_le A B hA hB
  change D.card ≤ j
  rw [hDL, ← hcount]
  exact hcardL

/-- Direct, certificate-free endpoint form.  Two nonempty finite families of
neighbors of the endpoint of a simple path, lying on opposite parities of the
path, have total size at most `2*j+1` when the graph has exactly `j` odd cycle
lengths. -/
theorem card_add_card_le_two_mul_add_one_of_path_endpoint
    {V : Type*} [Finite V] [DecidableEq V] (G : SimpleGraph V)
    {r z : V} (p : G.Walk r z) (hp : p.IsPath)
    (A B : Finset V) (hAne : A.Nonempty) (hBne : B.Nonempty)
    (hA : ∀ a ∈ A,
      a ∈ p.support ∧ G.Adj z a ∧ p.support.idxOf a % 2 = 0)
    (hB : ∀ b ∈ B,
      b ∈ p.support ∧ G.Adj z b ∧ p.support.idxOf b % 2 = 1)
    {j : ℕ} (hcount : (Erdos58.oddCycleLengths G).ncard = j) :
    A.card + B.card ≤ 2 * j + 1 := by
  classical
  let pos : V → ℤ := fun v ↦ p.support.idxOf v
  let AI : Finset ℤ := A.image pos
  let BI : Finset ℤ := B.image pos
  have hAIcard : AI.card = A.card := by
    apply Finset.card_image_of_injOn
    intro a ha b _hab heq
    apply (List.idxOf_inj (hA a ha).1).mp
    change (p.support.idxOf a : ℤ) = p.support.idxOf b at heq
    exact_mod_cast heq
  have hBIcard : BI.card = B.card := by
    apply Finset.card_image_of_injOn
    intro a ha b _hab heq
    apply (List.idxOf_inj (hB a ha).1).mp
    change (p.support.idxOf a : ℤ) = p.support.idxOf b at heq
    exact_mod_cast heq
  have hAIne : AI.Nonempty := hAne.image pos
  have hBIne : BI.Nonempty := hBne.image pos
  have hrealized : ∀ d ∈ (AI + -BI).image Int.natAbs,
      d + 2 ∈ Erdos58.oddCycleLengths G := by
    intro d hd
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hd
    obtain ⟨ai, hai, nbi, hnbi, rfl⟩ := Finset.mem_add.mp hx
    obtain ⟨bi, hbi, hneg⟩ := Finset.mem_neg.mp hnbi
    subst nbi
    obtain ⟨a, haA, haipos⟩ := Finset.mem_image.mp hai
    obtain ⟨b, hbB, hbipos⟩ := Finset.mem_image.mp hbi
    subst ai
    subst bi
    have ha := hA a haA
    have hb := hB b hbB
    have hpar : p.support.idxOf a % 2 ≠ p.support.idxOf b % 2 := by
      omega
    have hcycle := cycleAtLength_of_path_endpoint_cross p hp
      ha.1 hb.1 ha.2.1 hb.2.1 hpar
    have hodd0 := odd_natAbs_int_sub_of_mod_two_ne
      (p.support.idxOf a) (p.support.idxOf b) hpar
    have hodd :
        Odd (Int.natAbs ((p.support.idxOf a : ℤ) - p.support.idxOf b) + 2) := by
      rw [Nat.odd_iff] at hodd0 ⊢
      omega
    simpa [pos, sub_eq_add_neg] using
      Erdos58.CycleAtLength.mem_oddCycleLengths hcycle hodd
  have hbound :=
    card_add_card_le_two_mul_add_one_of_crossDiff_realized
      G AI BI hAIne hBIne hrealized hcount
  rwa [hAIcard, hBIcard] at hbound

/-- Degree form of the endpoint bound.  If every neighbor of the endpoint of
a simple path lies on that path and both position parities occur, the endpoint
has degree at most `2*j+1`. -/
theorem degree_le_two_mul_add_one_of_path_endpoint
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {r z : V} (p : G.Walk r z) (hp : p.IsPath)
    (hall : ∀ w, G.Adj z w → w ∈ p.support)
    (heven : ∃ w, G.Adj z w ∧ p.support.idxOf w % 2 = 0)
    (hodd : ∃ w, G.Adj z w ∧ p.support.idxOf w % 2 = 1)
    {j : ℕ} (hcount : (Erdos58.oddCycleLengths G).ncard = j) :
    G.degree z ≤ 2 * j + 1 := by
  classical
  let N : Finset V := G.neighborFinset z
  let A : Finset V := N.filter fun w ↦ p.support.idxOf w % 2 = 0
  let B : Finset V := N.filter fun w ↦ p.support.idxOf w % 2 ≠ 0
  have hAne : A.Nonempty := by
    obtain ⟨w, hw, hpar⟩ := heven
    exact ⟨w, by simp [A, N, hw, hpar]⟩
  have hBne : B.Nonempty := by
    obtain ⟨w, hw, hpar⟩ := hodd
    exact ⟨w, by simp [B, N, hw, hpar]⟩
  have hA : ∀ a ∈ A,
      a ∈ p.support ∧ G.Adj z a ∧ p.support.idxOf a % 2 = 0 := by
    intro a ha
    have ha' : G.Adj z a ∧ p.support.idxOf a % 2 = 0 := by
      simpa [A, N] using ha
    exact ⟨hall a ha'.1, ha'⟩
  have hB : ∀ b ∈ B,
      b ∈ p.support ∧ G.Adj z b ∧ p.support.idxOf b % 2 = 1 := by
    intro b hb
    have hb' : G.Adj z b ∧ p.support.idxOf b % 2 ≠ 0 := by
      simpa [B, N] using hb
    refine ⟨hall b hb'.1, hb'.1, ?_⟩
    have hlt : p.support.idxOf b % 2 < 2 := Nat.mod_lt _ (by omega)
    omega
  have hbound := card_add_card_le_two_mul_add_one_of_path_endpoint
    G p hp A B hAne hBne hA hB hcount
  have hpartition : A.card + B.card = N.card := by
    simpa [A, B] using
      (Finset.card_filter_add_card_filter_not
        (s := N) (p := fun w ↦ p.support.idxOf w % 2 = 0))
  calc
    G.degree z = N.card := by simp [N]
    _ = A.card + B.card := hpartition.symm
    _ ≤ 2 * j + 1 := hbound

/-- Rigidity consequence of the endpoint count: above the `2*j+1` degree
threshold, all neighbors of a path endpoint must occur on the same parity of
the path.  This pinpoints the sole branch that a 2-connectivity argument must
rule out in a proof of the full structural theorem. -/
theorem endpoint_neighbors_same_parity_of_large_degree
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {r z : V} (p : G.Walk r z) (hp : p.IsPath)
    (hall : ∀ w, G.Adj z w → w ∈ p.support)
    {j : ℕ} (hcount : (Erdos58.oddCycleLengths G).ncard = j)
    (hlarge : 2 * j + 2 ≤ G.degree z) :
    (∀ w, G.Adj z w → p.support.idxOf w % 2 = 0) ∨
      (∀ w, G.Adj z w → p.support.idxOf w % 2 = 1) := by
  classical
  by_cases heven : ∃ w, G.Adj z w ∧ p.support.idxOf w % 2 = 0
  · left
    intro w hw
    by_contra hpar
    have hlt : p.support.idxOf w % 2 < 2 := Nat.mod_lt _ (by omega)
    have hodd : ∃ x, G.Adj z x ∧ p.support.idxOf x % 2 = 1 := by
      exact ⟨w, hw, by omega⟩
    have hdegree := degree_le_two_mul_add_one_of_path_endpoint
      G p hp hall heven hodd hcount
    omega
  · right
    intro w hw
    have hne : p.support.idxOf w % 2 ≠ 0 := by
      intro hzero
      exact heven ⟨w, hw, hzero⟩
    have hlt : p.support.idxOf w % 2 < 2 := Nat.mod_lt _ (by omega)
    omega

end Erdos58.Structural.Alternative
