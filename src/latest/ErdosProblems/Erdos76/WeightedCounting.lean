import ErdosProblems.Erdos76.WeightOptimization
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

/-!
# The two-colour weighted counting inequality

The red and blue graphs here may leave pairs uncoloured. The penalty records
pairs with common neighbours in both colours, including the diagonal.
-/

open Finset
open scoped BigOperators

namespace Erdos76.WeightedCounting

variable {V : Type*} [Fintype V] [DecidableEq V]

attribute [local instance] Classical.propDecidable

def NoTriangle (G : SimpleGraph V) : Prop :=
  ∀ a b c, G.Adj a b → G.Adj b c → G.Adj a c → False

def DoubleCommon (R B : SimpleGraph V) (i j : V) : Prop :=
  (∃ k, R.Adj i k ∧ R.Adj j k) ∧ (∃ k, B.Adj i k ∧ B.Adj j k)

noncomputable def kernel (R B : SimpleGraph V) (i j : V) : ℝ := by
  classical
  exact (if R.Adj i j then 1 else 0) + (if B.Adj i j then 1 else 0) -
    2 * (if DoubleCommon R B i j then 1 else 0)

noncomputable def degree (G : SimpleGraph V) (p : V → ℝ) (i : V) : ℝ := by
  classical
  exact ∑ j, if G.Adj i j then p j else 0

lemma doubleCommon_symm {R B : SimpleGraph V} {i j : V}
    (h : DoubleCommon R B i j) : DoubleCommon R B j i := by
  rcases h with ⟨⟨a, ha, ha'⟩, ⟨b, hb, hb'⟩⟩
  exact ⟨⟨a, ha', ha⟩, ⟨b, hb', hb⟩⟩

lemma doubleCommon_swap {R B : SimpleGraph V} {i j : V} :
    DoubleCommon R B i j ↔ DoubleCommon B R i j := and_comm

lemma doubleCommon_self {R B : SimpleGraph V} {i j : V}
    (h : DoubleCommon R B i j) : DoubleCommon R B i i := by
  rcases h with ⟨⟨a, ha, _⟩, ⟨b, hb, _⟩⟩
  exact ⟨⟨a, ha, ha⟩, ⟨b, hb, hb⟩⟩

lemma doubleCommon_nonadj {R B : SimpleGraph V} (hR : NoTriangle R)
    (hB : NoTriangle B) {i j : V} (h : DoubleCommon R B i j) :
    ¬ R.Adj i j ∧ ¬ B.Adj i j := by
  rcases h with ⟨⟨a, ha, ha'⟩, ⟨b, hb, hb'⟩⟩
  exact ⟨fun hij ↦ hR i j a hij ha' ha, fun hij ↦ hB i j b hij hb' hb⟩

lemma kernel_symm (R B : SimpleGraph V) (i j : V) : kernel R B i j = kernel R B j i := by
  classical
  have hD : DoubleCommon R B i j ↔ DoubleCommon R B j i :=
    ⟨doubleCommon_symm, doubleCommon_symm⟩
  simp only [kernel, R.adj_comm, B.adj_comm, hD]

lemma kernel_zero_curvature {R B : SimpleGraph V} (hR : NoTriangle R)
    (hB : NoTriangle B) {i j : V} (h : DoubleCommon R B i j) :
    kernel R B i i + kernel R B j j - 2 * kernel R B i j = 0 := by
  classical
  obtain ⟨hijR, hijB⟩ := doubleCommon_nonadj hR hB h
  norm_num [kernel, h, doubleCommon_self h, doubleCommon_self (doubleCommon_symm h), hijR, hijB]

lemma degree_nonneg {G : SimpleGraph V} {p : V → ℝ} (hp : ∀ i, 0 ≤ p i) (i : V) :
    0 ≤ degree G p i := by
  classical
  exact sum_nonneg fun j _ ↦ by split_ifs; exact hp j; exact le_rfl

lemma degree_zero_of_no_neighbor {G : SimpleGraph V} (p : V → ℝ) {i : V}
    (hi : ∀ j, ¬G.Adj i j) : degree G p i = 0 := by
  classical
  simp [degree, hi]

lemma degree_eq_support_sum (G : SimpleGraph V) (p : V → ℝ) (i : V) :
    degree G p i = ∑ j ∈ WeightOptimization.support p, if G.Adj i j then p j else 0 := by
  classical
  apply (sum_subset (subset_univ _) ?_).symm
  intro j _ hj
  have hpj : p j = 0 := not_not.mp (WeightOptimization.mem_support.not.mp hj)
  simp [hpj]

lemma adjacent_degree_sum_le {G : SimpleGraph V} (hG : NoTriangle G)
    {p : V → ℝ} (hp : p ∈ stdSimplex ℝ V) {i j : V} (hij : G.Adj i j) :
    degree G p i + degree G p j ≤ 1 := by
  classical
  rw [← hp.2]
  simp only [degree, ← sum_add_distrib]
  apply sum_le_sum
  intro k _
  by_cases hik : G.Adj i k <;> by_cases hjk : G.Adj j k
  · exact (hG i j k hij hjk hik).elim
  · simp [hik, hjk]
  · simp [hik, hjk]
  · simpa [hik, hjk] using hp.1 k

lemma row_kernel_on_support {R B : SimpleGraph V} {p : V → ℝ}
    (hp : p ∈ stdSimplex ℝ V)
    (hD : ∀ i j, i ≠ j → 0 < p i → 0 < p j → ¬DoubleCommon R B i j)
    {i : V} (hi : 0 < p i) :
    WeightOptimization.row (kernel R B) p i = degree R p i + degree B p i -
      2 * (if DoubleCommon R B i i then p i else 0) := by
  classical
  have hsum : (∑ j, (if DoubleCommon R B i j then (1 : ℝ) else 0) * p j) =
      if DoubleCommon R B i i then p i else 0 := by
    rw [sum_eq_single i]
    · split_ifs <;> simp
    · intro j _ hji
      by_cases hj : p j = 0
      · simp [hj]
      · have hnot := hD i j (Ne.symm hji) hi (lt_of_le_of_ne (hp.1 j) (Ne.symm hj))
        simp [hnot]
    · simp
  simp only [WeightOptimization.row, kernel, sub_mul, add_mul,
    sum_sub_distrib, sum_add_distrib, mul_assoc, ← mul_sum, hsum]
  congr 2 <;> apply sum_congr rfl <;> intro j _ <;> split_ifs <;> simp

/-- A constant counted over a predicate with at most one witness is at most
that constant. This is used twice to count two-colour paths. -/
lemma sum_indicator_le {S : Finset V} {P : V → Prop} [DecidablePred P]
    (huniq : ∀ i ∈ S, ∀ j ∈ S, P i → P j → i = j) {c : ℝ} (hc : 0 ≤ c) :
    (∑ i ∈ S, if P i then c else 0) ≤ c := by
  by_cases hex : ∃ i ∈ S, P i
  · obtain ⟨i, hi, hPi⟩ := hex
    rw [sum_eq_single i]
    · simp [hPi]
    · intro j hj hji
      have : ¬P j := fun hPj ↦ hji (huniq j hj i hi hPj hPi)
      simp [this]
    · exact fun h ↦ (h hi).elim
  · have hnone : ∀ i ∈ S, ¬P i := by simpa using hex
    have hzero : (∑ i ∈ S, if P i then c else 0) = 0 :=
      sum_eq_zero fun i hi ↦ by simp [hnone i hi]
    simpa [hzero] using hc

lemma opposite_degree_sum_le_one {R B : SimpleGraph V} {p : V → ℝ}
    (hp : p ∈ stdSimplex ℝ V)
    (hD : ∀ i j, i ≠ j → 0 < p i → 0 < p j → ¬DoubleCommon R B i j)
    (v : V) :
    (∑ u ∈ (WeightOptimization.support p).filter (R.Adj v), degree B p u) ≤ 1 := by
  classical
  unfold degree
  rw [sum_comm, ← hp.2]
  apply sum_le_sum
  intro x _
  apply sum_indicator_le _ (hp.1 x)
  intro i hi j hj hix hjx
  by_contra hij
  have hip : 0 < p i := lt_of_le_of_ne (hp.1 i)
    (Ne.symm (WeightOptimization.mem_support.mp (mem_filter.mp hi).1))
  have hjp : 0 < p j := lt_of_le_of_ne (hp.1 j)
    (Ne.symm (WeightOptimization.mem_support.mp (mem_filter.mp hj).1))
  exact hD i j hij hip hjp
    ⟨⟨v, (mem_filter.mp hi).2.symm, (mem_filter.mp hj).2.symm⟩, ⟨x, hix, hjx⟩⟩

lemma stationary_degree_lt_half {R B : SimpleGraph V} (hR : NoTriangle R)
    {p : V → ℝ} (hp : p ∈ stdSimplex ℝ V)
    (hD : ∀ i j, i ≠ j → 0 < p i → 0 < p j → ¬DoubleCommon R B i j)
    {c : ℝ} (hc : 1 / 2 < c)
    (hstation : ∀ i, 0 < p i → degree R p i + degree B p i -
      2 * (if DoubleCommon R B i i then p i else 0) = c)
    (v : V) : degree R p v < 1 / 2 := by
  by_contra! hv
  let S := (WeightOptimization.support p).filter (R.Adj v)
  have hsum : degree R p v = ∑ u ∈ S, p u := by
    rw [degree_eq_support_sum]
    simp only [S, sum_filter]
  have hS : S.Nonempty := by
    by_contra h
    have hempty := not_nonempty_iff_eq_empty.mp h
    rw [hempty, sum_empty] at hsum
    linarith
  have hgreater : ∀ u ∈ S, 2 * p u < degree B p u := by
    intro u hu
    obtain ⟨hup, hvu⟩ := mem_filter.mp hu
    have hpu : 0 < p u := lt_of_le_of_ne (hp.1 u)
      (Ne.symm (WeightOptimization.mem_support.mp hup))
    have hbound := adjacent_degree_sum_le hR hp hvu.symm
    have hstat := hstation u hpu
    have hmix : DoubleCommon R B u u := by
      by_contra hnot
      have hbzero : degree B p u = 0 := degree_zero_of_no_neighbor p (fun x hux ↦
        hnot ⟨⟨v, hvu.symm, hvu.symm⟩, ⟨x, hux, hux⟩⟩)
      rw [if_neg hnot, hbzero] at hstat
      linarith
    rw [if_pos hmix] at hstat
    linarith
  obtain ⟨u, hu⟩ := hS
  have hstrict : (∑ u ∈ S, 2 * p u) < ∑ u ∈ S, degree B p u :=
    sum_lt_sum (fun u hu ↦ (hgreater u hu).le) ⟨u, hu, hgreater u hu⟩
  rw [← mul_sum, ← hsum] at hstrict
  have hupper := opposite_degree_sum_le_one hp hD v
  change (∑ u ∈ S, degree B p u) ≤ 1 at hupper
  linarith

lemma sum_degree_product_le_one {R B : SimpleGraph V} {p : V → ℝ}
    (hp : p ∈ stdSimplex ℝ V)
    (hD : ∀ i j, i ≠ j → 0 < p i → 0 < p j → ¬DoubleCommon R B i j) :
    (∑ v ∈ WeightOptimization.support p, degree R p v * degree B p v) ≤ 1 := by
  have hexpand : (∑ v ∈ WeightOptimization.support p, degree R p v * degree B p v) =
      ∑ a, ∑ b, ∑ v ∈ WeightOptimization.support p,
        if R.Adj v a ∧ B.Adj v b then p a * p b else 0 := by
    simp only [degree, sum_mul_sum]
    rw [sum_comm]
    apply sum_congr rfl
    intro a _
    rw [sum_comm]
    apply sum_congr rfl
    intro b _
    apply sum_congr rfl
    intro v _
    split_ifs <;> simp_all
  rw [hexpand]
  calc
    _ ≤ ∑ a, ∑ b, p a * p b := by
      apply sum_le_sum
      intro a _
      apply sum_le_sum
      intro b _
      apply sum_indicator_le _ (mul_nonneg (hp.1 a) (hp.1 b))
      intro i hi j hj hiP hjP
      by_contra hij
      exact hD i j hij
        (lt_of_le_of_ne (hp.1 i) (Ne.symm (WeightOptimization.mem_support.mp hi)))
        (lt_of_le_of_ne (hp.1 j) (Ne.symm (WeightOptimization.mem_support.mp hj)))
        ⟨⟨a, hiP.1, hjP.1⟩, ⟨b, hiP.2, hjP.2⟩⟩
    _ = 1 := by simp [← mul_sum, hp.2]

lemma stationary_value_le_half {R B : SimpleGraph V} (hR : NoTriangle R)
    (hB : NoTriangle B) {p : V → ℝ} (hp : p ∈ stdSimplex ℝ V)
    (hD : ∀ i j, i ≠ j → 0 < p i → 0 < p j → ¬DoubleCommon R B i j)
    {c : ℝ} (hstation : ∀ i, 0 < p i → degree R p i + degree B p i -
      2 * (if DoubleCommon R B i i then p i else 0) = c) : c ≤ 1 / 2 := by
  by_contra! hc
  have hred := stationary_degree_lt_half hR hp hD hc hstation
  have hblue : ∀ v, degree B p v < 1 / 2 :=
    stationary_degree_lt_half hB hp
      (fun i j hij hi hj h ↦ hD i j hij hi hj (doubleCommon_swap.mpr h)) hc
      (fun i hi ↦ by simpa only [← doubleCommon_swap, add_comm] using hstation i hi)
  have hsum : (∑ i ∈ WeightOptimization.support p, p i) = 1 := by
    rw [← hp.2]
    apply sum_subset (subset_univ _)
    intro i _ hi
    exact not_not.mp (WeightOptimization.mem_support.not.mp hi)
  have hsupport : (WeightOptimization.support p).Nonempty := by
    by_contra h
    rw [not_nonempty_iff_eq_empty.mp h, sum_empty] at hsum
    norm_num at hsum
  have hprod : ∀ i ∈ WeightOptimization.support p,
      2 * c * p i < degree R p i * degree B p i := by
    intro i hi
    have hpi : 0 < p i := lt_of_le_of_ne (hp.1 i)
      (Ne.symm (WeightOptimization.mem_support.mp hi))
    have hstat := hstation i hpi
    have hmix : DoubleCommon R B i i := by
      by_contra hnot
      rw [if_neg hnot] at hstat
      by_cases hr : ∃ a, R.Adj i a
      · obtain ⟨a, ha⟩ := hr
        have hbzero : degree B p i = 0 := degree_zero_of_no_neighbor p (fun b hb ↦
          hnot ⟨⟨a, ha, ha⟩, ⟨b, hb, hb⟩⟩)
        linarith [hred i]
      · have hrzero : degree R p i = 0 := degree_zero_of_no_neighbor p (by simpa using hr)
        linarith [hblue i]
    rw [if_pos hmix] at hstat
    have h₁ : 0 < degree R p i - 2 * p i := by linarith [hblue i]
    have h₂ : 0 < degree B p i - 2 * p i := by linarith [hred i]
    have hpositive := mul_pos h₁ h₂
    nlinarith
  obtain ⟨i, hi⟩ := hsupport
  have hstrict : (∑ i ∈ WeightOptimization.support p, 2 * c * p i) <
      ∑ i ∈ WeightOptimization.support p, degree R p i * degree B p i :=
    sum_lt_sum (fun i hi ↦ (hprod i hi).le) ⟨i, hi, hprod i hi⟩
  rw [← mul_sum, hsum, mul_one] at hstrict
  have hbound := sum_degree_product_le_one hp hD
  linarith

/-- The weighted counting inequality, in ordered-pair normalization. The
quadratic form is twice the edge-minus-penalty objective. -/
theorem quadratic_kernel_le_half (R B : SimpleGraph V) (hR : NoTriangle R)
    (hB : NoTriangle B) (p : V → ℝ) (hp : p ∈ stdSimplex ℝ V) :
    WeightOptimization.quadratic (kernel R B) p ≤ 1 / 2 := by
  classical
  have : Nonempty V := by
    by_contra h
    have : IsEmpty V := not_nonempty_iff.mp h
    have := hp.2
    simp at this
  obtain ⟨q, hq, hmax, hrow, hcurv⟩ :=
    WeightOptimization.exists_sparse_maximizer (kernel R B) (kernel_symm R B)
  have hD : ∀ i j, i ≠ j → 0 < q i → 0 < q j → ¬DoubleCommon R B i j := by
    intro i j hij hi hj h
    exact hcurv i j hij hi hj (kernel_zero_curvature hR hB h)
  apply (hmax p hp).trans
  apply stationary_value_le_half hR hB hq hD
  intro i hi
  rw [← row_kernel_on_support hq hD hi]
  exact hrow i hi

lemma sum_kernel_le (R B : SimpleGraph V) (hR : NoTriangle R) (hB : NoTriangle B) :
    (∑ i, ∑ j, kernel R B i j) ≤ (Fintype.card V : ℝ) ^ 2 / 2 := by
  classical
  cases isEmpty_or_nonempty V with
  | inl h => simp
  | inr h =>
    let n : ℝ := Fintype.card V
    have hn : 0 < n := by
      dsimp [n]
      exact_mod_cast (Fintype.card_pos : 0 < Fintype.card V)
    have hp : (fun _ : V ↦ 1 / n) ∈ stdSimplex ℝ V := by
      constructor
      · intro i; positivity
      · simp [n, ne_of_gt hn]
    have hbound := quadratic_kernel_le_half R B hR hB _ hp
    have hvalue : WeightOptimization.quadratic (kernel R B) (fun _ : V ↦ 1 / n) =
        (∑ i, ∑ j, kernel R B i j) / n ^ 2 := by
      simp only [WeightOptimization.quadratic, WeightOptimization.bilinear,
        ← sum_mul, div_eq_mul_inv, one_mul, pow_two, mul_inv_rev]
      ring
    rw [hvalue] at hbound
    have := (div_le_iff₀ (sq_pos_of_pos hn)).mp hbound
    dsimp [n] at this
    linarith

def doubleCommonGraph (R B : SimpleGraph V) : SimpleGraph V where
  Adj i j := i ≠ j ∧ DoubleCommon R B i j
  symm := ⟨fun i j h ↦ ⟨Ne.symm h.1, doubleCommon_symm h.2⟩⟩
  loopless := ⟨fun i h ↦ h.1 rfl⟩

lemma sum_adj_indicator (G : SimpleGraph V) :
    (∑ i, ∑ j, if G.Adj i j then (1 : ℝ) else 0) = 2 * G.edgeFinset.card := by
  have hdegree : ∀ i, (∑ j, if G.Adj i j then (1 : ℝ) else 0) = (G.degree i : ℝ) := by
    intro i
    simp [SimpleGraph.degree, SimpleGraph.neighborFinset_def]
  simp_rw [hdegree]
  exact_mod_cast G.sum_degrees_eq_twice_card_edges

/-- Finite unweighted form. `doubleCommonGraph` counts unordered distinct
pairs with a common neighbour of each colour. -/
theorem edge_count_bound (R B : SimpleGraph V) (hR : NoTriangle R) (hB : NoTriangle B) :
    (R.edgeFinset.card : ℝ) + B.edgeFinset.card -
      2 * (doubleCommonGraph R B).edgeFinset.card ≤
        (Fintype.card V : ℝ) ^ 2 / 4 + Fintype.card V := by
  let D := doubleCommonGraph R B
  have hpoint : ∀ i j,
      (if R.Adj i j then (1 : ℝ) else 0) + (if B.Adj i j then 1 else 0) -
        2 * (if D.Adj i j then 1 else 0) - 2 * (if i = j then 1 else 0) ≤
          kernel R B i j := by
    intro i j
    by_cases hij : i = j
    · subst j
      simp only [SimpleGraph.irrefl, if_false, if_true, zero_add, mul_zero,
        mul_one, zero_sub, kernel]
      split_ifs <;> norm_num
    · simp [D, doubleCommonGraph, hij, kernel]
  have hsum := sum_le_sum (s := univ) (fun i _ ↦ sum_le_sum (s := univ) (fun j _ ↦ hpoint i j))
  simp only [sum_sub_distrib, sum_add_distrib, ← mul_sum] at hsum
  rw [sum_adj_indicator R, sum_adj_indicator B, sum_adj_indicator D] at hsum
  simp only [sum_ite_eq, mem_univ, if_true, sum_const, card_univ, nsmul_eq_mul, mul_one] at hsum
  have hbound := sum_kernel_le R B hR hB
  dsimp only [D] at hsum
  linarith

end Erdos76.WeightedCounting
