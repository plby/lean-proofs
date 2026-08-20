import ErdosProblems.Erdos746.Asymptotics
import ErdosProblems.Erdos746.ErrorLimits
import ErdosProblems.Erdos746.NeighborDistribution

/-!
# The large-set range in the expansion estimate

This file formalizes Range III of the three-range union bound in the proof of
Erdos Problem 746.  For a fixed set `S` of size `s`, fewer than `2s` external
neighbours forces the absence of at least `s (n - 3s)` independently sampled
edges.  There are at most `2^n` possible exceptional sets.  We then record the
two elementary exponent estimates used for `s <= n/12` and `n/12 <= s <= n/4`.
-/

open Filter MeasureTheory ProbabilityTheory unitInterval
open scoped BigOperators ENNReal SimpleGraph Sym2 Topology

namespace Erdos746

noncomputable section

/-- The elementary Bernoulli estimate `(1-p)^r <= exp (-p r)`. -/
lemma one_sub_pow_le_exp_neg_mul (p : I) (r : ℕ) :
    (1 - (p : ℝ)) ^ r ≤ Real.exp (-(p : ℝ) * (r : ℝ)) := by
  have hp0 : 0 ≤ (p : ℝ) := p.2.1
  have hbase0 : 0 ≤ 1 - (p : ℝ) := sub_nonneg.mpr p.2.2
  calc
    (1 - (p : ℝ)) ^ r ≤ Real.exp (-(p : ℝ)) ^ r :=
      pow_le_pow_left₀ hbase0 (Real.one_sub_le_exp_neg (p : ℝ)) r
    _ = Real.exp (-(p : ℝ) * (r : ℝ)) := by
      rw [← Real.exp_nsmul]
      congr 2
      simp [nsmul_eq_mul]
      ring

/-- The collection of possible exceptional outside sets has cardinality at
most `2^n`. -/
lemma card_smallNeighborCandidateFinset_le_two_pow
    {V : Type*} [Fintype V] [DecidableEq V] (S : Finset V) (r : ℕ) :
    (SimpleGraph.smallNeighborCandidateFinset S r).card ≤ 2 ^ Fintype.card V := by
  calc
    (SimpleGraph.smallNeighborCandidateFinset S r).card ≤
        ((Finset.univ \ S).powerset).card := Finset.card_filter_le _ _
    _ = 2 ^ (Finset.univ \ S).card := Finset.card_powerset _
    _ ≤ 2 ^ Fintype.card V := by
      exact Nat.pow_le_pow_right (by norm_num : 0 < (2 : ℕ))
        (Finset.card_le_univ (Finset.univ \ S))

/-- If `T` is a possible external-neighbour set for `S`, then at least
`n - 3|S|` vertices lie outside `S union T`. -/
lemma three_mul_card_add_compl_le
    {V : Type*} [Fintype V] [DecidableEq V]
    {S T : Finset V} {r : ℕ}
    (hT : T ∈ SimpleGraph.smallNeighborCandidateFinset S (2 * S.card)) :
    Fintype.card V - 3 * S.card ≤ (Finset.univ \ (S ∪ T)).card := by
  rw [SimpleGraph.mem_smallNeighborCandidateFinset] at hT
  have hTS : Disjoint S T := by
    exact Finset.disjoint_left.mpr fun x hxS hxT ↦
      (Finset.mem_sdiff.mp (hT.1 hxT)).2 hxS
  have hcardT : T.card ≤ 2 * S.card := Nat.le_of_lt hT.2
  have hunion : (S ∪ T).card = S.card + T.card :=
    Finset.card_union_of_disjoint hTS
  have hsub : (S ∪ T).card ≤ Fintype.card V := Finset.card_le_univ _
  rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ]
  omega

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Fixed-set Range-III estimate (equation (7) in the writeup). -/
theorem binomialRandom_real_outerNeighborFinset_card_lt_two_mul_le_large
    (p : I) (S : Finset V) (h3 : 3 * S.card ≤ Fintype.card V) :
    G(V, p).real {G | (G.outerNeighborFinset S).card < 2 * S.card} ≤
      (2 : ℝ) ^ Fintype.card V *
        Real.exp (-(p : ℝ) * (S.card : ℝ) *
          (Fintype.card V - 3 * S.card : ℕ)) := by
  classical
  let C := smallNeighborCandidateFinset S (2 * S.card)
  let B : ℝ := Real.exp (-(p : ℝ) * (S.card : ℝ) *
    (Fintype.card V - 3 * S.card : ℕ))
  have hprob := binomialRandom_real_outerNeighborFinset_card_lt_two_mul_le p S
  refine hprob.trans ?_
  calc
    (∑ T ∈ C, (1 - (p : ℝ)) ^
        (S.card * (Finset.univ \ (S ∪ T)).card)) ≤
        ∑ _T ∈ C, B := by
      apply Finset.sum_le_sum
      intro T hT
      have hcomp := three_mul_card_add_compl_le (r := 2 * S.card) hT
      have hexpNat : S.card * (Fintype.card V - 3 * S.card) ≤
          S.card * (Finset.univ \ (S ∪ T)).card :=
        Nat.mul_le_mul_left S.card hcomp
      have hbase0 : 0 ≤ 1 - (p : ℝ) := sub_nonneg.mpr p.2.2
      have hbase1 : 1 - (p : ℝ) ≤ 1 := by linarith [p.2.1]
      calc
        (1 - (p : ℝ)) ^ (S.card * (Finset.univ \ (S ∪ T)).card) ≤
            (1 - (p : ℝ)) ^ (S.card * (Fintype.card V - 3 * S.card)) :=
          pow_le_pow_of_le_one hbase0 hbase1 hexpNat
        _ ≤ B := by
          dsimp [B]
          convert one_sub_pow_le_exp_neg_mul p
            (S.card * (Fintype.card V - 3 * S.card)) using 1 <;>
            norm_num <;> push_cast <;> ring
    _ = (C.card : ℝ) * B := by simp
    _ ≤ ((2 : ℕ) ^ Fintype.card V : ℝ) * B := by
      gcongr
      exact_mod_cast card_smallNeighborCandidateFinset_le_two_pow S (2 * S.card)
    _ = (2 : ℝ) ^ Fintype.card V *
        Real.exp (-(p : ℝ) * (S.card : ℝ) *
          (Fintype.card V - 3 * S.card : ℕ)) := by
      simp [B]

end SimpleGraph

end

end Erdos746
