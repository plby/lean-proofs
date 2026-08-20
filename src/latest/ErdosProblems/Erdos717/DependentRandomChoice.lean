/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- The finite double-counting core of dependent random choice. -/

import ErdosProblems.Erdos717.MaximumCut
import ErdosProblems.Erdos718.Erdos718Core
import Mathlib.Algebra.Order.Chebyshev

open Function Set
open SimpleGraph

namespace Erdos717

/-- Common neighbours of `u,v` inside a prescribed finite set. -/
def commonNeighborFinset {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (T : Finset V) (u v : V) : Finset V :=
  T.filter fun z => G.Adj u z ∧ G.Adj v z

@[simp] theorem mem_commonNeighborFinset {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (T : Finset V) (u v z : V) :
    z ∈ commonNeighborFinset G T u v ↔
      z ∈ T ∧ G.Adj u z ∧ G.Adj v z := by
  simp [commonNeighborFinset]

theorem commonNeighborFinset_comm {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (T : Finset V) (u v : V) :
    commonNeighborFinset G T u v = commonNeighborFinset G T v u := by
  ext z
  simp only [mem_commonNeighborFinset]
  aesop

/-- The ordered pairs in `S` with fewer than `L` common neighbours in `T`. -/
def badOrderedPairs {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (S T : Finset V) (L : ℕ) : Finset (V × V) :=
  (S ×ˢ S).filter fun p => (commonNeighborFinset G T p.1 p.2).card < L

/-- Bad ordered pairs which both lie in the neighbourhood of `z`. -/
def badPairsAt {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (S T : Finset V) (L : ℕ) (z : V) : Finset (V × V) :=
  (badOrderedPairs G S T L).filter fun p => G.Adj p.1 z ∧ G.Adj p.2 z

theorem sum_card_badPairsAt
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (S T : Finset V) (L : ℕ) :
    ∑ z ∈ T, (badPairsAt G S T L z).card =
      ∑ p ∈ badOrderedPairs G S T L,
        (commonNeighborFinset G T p.1 p.2).card := by
  classical
  simp only [badPairsAt, Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p hp
  simp only [commonNeighborFinset, Finset.card_eq_sum_ones, Finset.sum_filter]

theorem sum_card_badPairsAt_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (S T : Finset V) (L : ℕ) :
    ∑ z ∈ T, (badPairsAt G S T L z).card ≤ S.card * S.card * L := by
  rw [sum_card_badPairsAt]
  calc
    (∑ p ∈ badOrderedPairs G S T L,
        (commonNeighborFinset G T p.1 p.2).card) ≤
        ∑ _p ∈ badOrderedPairs G S T L, L := by
      apply Finset.sum_le_sum
      intro p hp
      exact (Finset.mem_filter.mp hp).2.le
    _ = (badOrderedPairs G S T L).card * L := by simp
    _ ≤ (S ×ˢ S).card * L := Nat.mul_le_mul_right L <|
      Finset.card_le_card (Finset.filter_subset _ _)
    _ = S.card * S.card * L := by rw [Finset.card_product]

/-- Double-counting form of dependent random choice.  The hypotheses are
integer inequalities so that all rounding is postponed to the analytic
corollary. -/
theorem exists_neighborhood_with_few_bad_pairs
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (S T : Finset V) (hST : G.IsBipartiteWith (S : Set V) (T : Set V))
    (X0 L : ℕ) (hE : 0 < G.edgeFinset.card)
    (hlarge : T.card *
      (T.card * (X0 * X0) + 40 * (S.card * S.card * L)) ≤
        G.edgeFinset.card * G.edgeFinset.card) :
    ∃ X : Finset V,
      X ⊆ S ∧ (X : Set V) ⊆ G.support ∧ X0 ≤ X.card ∧
      40 * ((X ×ˢ X).filter fun p =>
        (commonNeighborFinset G T p.1 p.2).card < L).card ≤ X.card * X.card := by
  classical
  let d : V → ℕ := fun z => G.degree z
  have hsumDeg : ∑ z ∈ T, d z = G.edgeFinset.card := by
    simpa [d] using SimpleGraph.isBipartiteWith_sum_degrees_eq_card_edges' hST
  have hTnonempty : T.Nonempty := by
    by_contra hT
    rw [Finset.not_nonempty_iff_eq_empty.mp hT] at hsumDeg
    simp at hsumDeg
    omega
  have hcauchy : G.edgeFinset.card * G.edgeFinset.card ≤
      T.card * ∑ z ∈ T, d z * d z := by
    have h := sq_sum_le_card_mul_sum_sq (s := T)
      (f := fun z => (d z : ℤ))
    have h' : ((∑ z ∈ T, d z : ℕ) : ℤ) ^ 2 ≤
        (T.card : ℤ) * ((∑ z ∈ T, d z * d z : ℕ) : ℤ) := by
      simpa [pow_two, Nat.cast_sum, Nat.cast_mul] using h
    rw [hsumDeg] at h'
    have hn : G.edgeFinset.card ^ 2 ≤
        T.card * ∑ z ∈ T, d z * d z := by
      exact_mod_cast h'
    simpa [pow_two] using hn
  have hex : ∃ z ∈ T,
      X0 * X0 + 40 * (badPairsAt G S T L z).card ≤ d z * d z := by
    by_contra! hnone
    have hsumlt : (∑ z ∈ T, d z * d z) <
        ∑ z ∈ T, (X0 * X0 + 40 * (badPairsAt G S T L z).card) := by
      apply Finset.sum_lt_sum
      · intro z hz
        exact (hnone z hz).le
      · exact ⟨hTnonempty.choose, hTnonempty.choose_spec,
          hnone hTnonempty.choose hTnonempty.choose_spec⟩
    have hsumBad := sum_card_badPairsAt_le G S T L
    have hupper :
        T.card * (∑ z ∈ T,
          (X0 * X0 + 40 * (badPairsAt G S T L z).card)) ≤
        T.card * (T.card * (X0 * X0) +
          40 * (S.card * S.card * L)) := by
      apply Nat.mul_le_mul_left
      calc
        (∑ z ∈ T, (X0 * X0 + 40 * (badPairsAt G S T L z).card)) =
            T.card * (X0 * X0) +
              40 * (∑ z ∈ T, (badPairsAt G S T L z).card) := by
          rw [Finset.sum_add_distrib, Finset.mul_sum]
          simp [Nat.mul_comm]
        _ ≤ T.card * (X0 * X0) + 40 * (S.card * S.card * L) :=
          Nat.add_le_add_left (Nat.mul_le_mul_left 40 hsumBad) _
    have hstrict : G.edgeFinset.card * G.edgeFinset.card <
        T.card * (T.card * (X0 * X0) + 40 * (S.card * S.card * L)) :=
      lt_of_le_of_lt hcauchy <|
        lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_left hsumlt hTnonempty.card_pos) hupper
    exact (not_lt_of_ge hlarge) hstrict
  obtain ⟨z, hzT, hz⟩ := hex
  let X := G.neighborFinset z
  have hXsub : X ⊆ S := by
    intro x hx
    have hadj : G.Adj z x := by simpa [X] using hx
    exact hST.symm.mem_of_mem_adj hzT hadj
  have hXcard : X.card = d z := by simp [X, d]
  have hbadEq :
      ((X ×ˢ X).filter fun p =>
        (commonNeighborFinset G T p.1 p.2).card < L) =
        badPairsAt G S T L z := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_product, badPairsAt,
      badOrderedPairs, and_assoc]
    constructor
    · rintro ⟨hp1, hp2, hbad⟩
      have ha1' : G.Adj z p.1 := by simpa [X] using hp1
      have ha2' : G.Adj z p.2 := by simpa [X] using hp2
      have ha1 : G.Adj p.1 z := ha1'.symm
      have ha2 : G.Adj p.2 z := ha2'.symm
      exact ⟨hXsub hp1, hXsub hp2, hbad, ha1, ha2⟩
    · rintro ⟨hp1, hp2, hbad, ha1, ha2⟩
      have hx1 : p.1 ∈ X := by simpa [X] using ha1.symm
      have hx2 : p.2 ∈ X := by simpa [X] using ha2.symm
      exact ⟨hx1, hx2, hbad⟩
  refine ⟨X, hXsub, ?_, ?_, ?_⟩
  · intro x hx
    have hadj : G.Adj z x := by simpa [X] using hx
    exact hadj.mem_support_right
  · rw [hXcard]
    nlinarith
  · rw [hbadEq, hXcard]
    omega

end Erdos717
