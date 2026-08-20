/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- Markov pruning by vertex degree. -/

import ErdosProblems.Erdos717.OptimalReservoir

open Function Set
open SimpleGraph

namespace Erdos717

def lowDegreeFinset {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (D : ℕ) : Finset V :=
  Finset.univ.filter fun v => G.degree v ≤ D

def highDegreeFinset {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (D : ℕ) : Finset V :=
  Finset.univ.filter fun v => D < G.degree v

theorem low_high_degree_partition
    {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (D : ℕ) :
    (lowDegreeFinset G D).card + (highDegreeFinset G D).card = Fintype.card V := by
  classical
  have hunion : lowDegreeFinset G D ∪ highDegreeFinset G D = Finset.univ := by
    ext v
    simp only [lowDegreeFinset, highDegreeFinset, Finset.mem_union,
      Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro _
      trivial
    · intro _
      exact le_or_gt (G.degree v) D
  have hdisj : Disjoint (lowDegreeFinset G D) (highDegreeFinset G D) := by
    rw [Finset.disjoint_left]
    intro v hvL hvH
    have hle := (Finset.mem_filter.mp hvL).2
    have hlt := (Finset.mem_filter.mp hvH).2
    omega
  rw [← Finset.card_union_of_disjoint hdisj, hunion, Finset.card_univ]

theorem highDegree_card_mul_le
    {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (D : ℕ) :
    (D + 1) * (highDegreeFinset G D).card ≤ 2 * G.edgeFinset.card := by
  classical
  calc
    (D + 1) * (highDegreeFinset G D).card =
        ∑ _v ∈ highDegreeFinset G D, (D + 1) := by simp [Nat.mul_comm]
    _ ≤ ∑ v ∈ highDegreeFinset G D, G.degree v := by
      apply Finset.sum_le_sum
      intro v hv
      have := (Finset.mem_filter.mp hv).2
      omega
    _ ≤ ∑ v : V, G.degree v := Finset.sum_le_sum_of_subset (by
      exact Finset.subset_univ _)
    _ = 2 * G.edgeFinset.card := G.sum_degrees_eq_twice_card_edges

/-- At least half the vertices have degree at most `D` once
`4e(G) ≤ n(D+1)`. -/
theorem half_card_le_lowDegreeFinset
    {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (D : ℕ)
    (hD : 4 * G.edgeFinset.card ≤ Fintype.card V * (D + 1)) :
    Fintype.card V / 2 ≤ (lowDegreeFinset G D).card := by
  have hpart := low_high_degree_partition G D
  have hhigh := highDegree_card_mul_le G D
  by_contra h
  have hlt : (lowDegreeFinset G D).card < Fintype.card V / 2 :=
    Nat.lt_of_not_ge h
  have htwice : Fintype.card V < 2 * (highDegreeFinset G D).card := by omega
  have hpos : 0 < D + 1 := by omega
  have hstrict : Fintype.card V * (D + 1) <
      2 * ((D + 1) * (highDegreeFinset G D).card) := by nlinarith
  nlinarith

theorem degree_le_of_mem_lowDegreeFinset
    {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (D : ℕ) :
    ∀ v ∈ lowDegreeFinset G D, G.degree v ≤ D := by
  intro v hv
  exact (Finset.mem_filter.mp hv).2

end Erdos717
