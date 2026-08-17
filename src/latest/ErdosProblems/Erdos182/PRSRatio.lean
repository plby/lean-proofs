import ErdosProblems.Erdos182.Probability
import ErdosProblems.Erdos182.Roof

/-!
# Ratio amplification for half-regular bipartite graphs

This file formalizes the probabilistic thinning step in the
Pyber--Rödl--Szemerédi extraction argument.  We use the orientation of
`BipartiteGraph` from `Roof.lean`: the active vertices in `B` have constant
degree into the active vertices in `A`.
-/

namespace Erdos182

open scoped BigOperators NNReal
open Finset

noncomputable section

section FiniteProbability

variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

/-- Finite linearity of expectation for a sum indexed by a finset. -/
theorem weightedExpectation_finset_sum {I : Type*} (weight : Finset A → ℝ≥0)
    (S : Finset I) (Z : I → Finset A → ℝ≥0) :
    weightedExpectation weight (fun X ↦ ∑ i ∈ S, Z i X) =
      ∑ i ∈ S, weightedExpectation weight (Z i) := by
  classical
  simp only [weightedExpectation, Finset.mul_sum]
  rw [Finset.sum_comm]

/-- The expectation of an indicator is its event probability. -/
theorem weightedExpectation_indicator (weight : Finset A → ℝ≥0)
    (P : Finset A → Prop) [DecidablePred P] :
    weightedExpectation weight (fun X ↦ if P X then 1 else 0) =
      weightedProbability weight P := by
  unfold weightedExpectation weightedProbability
  apply Finset.sum_congr rfl
  intro X _
  by_cases hX : P X <;> simp [hX]

/-- The expectation of the cardinality of a filtered finite set is the sum of
the probabilities of its membership events.  This is the finite form of
linearity of expectation used in the alteration argument below. -/
theorem weightedExpectation_card_filter (weight : Finset A → ℝ≥0)
    (B₀ : Finset B) (P : B → Finset A → Prop)
    [∀ X, DecidablePred fun b ↦ P b X] [∀ b, DecidablePred (P b)] :
    weightedExpectation weight
        (fun X ↦ ((B₀.filter fun b ↦ P b X).card : ℝ≥0)) =
      ∑ b ∈ B₀, weightedProbability weight (P b) := by
  classical
  calc
    weightedExpectation weight
        (fun X ↦ ((B₀.filter fun b ↦ P b X).card : ℝ≥0)) =
        weightedExpectation weight
          (fun X ↦ ∑ b ∈ B₀, if P b X then 1 else 0) := by
      congr 1
      funext X
      simp
    _ = ∑ b ∈ B₀,
        weightedExpectation weight (fun X ↦ if P b X then 1 else 0) :=
      weightedExpectation_finset_sum weight B₀
        (fun b X ↦ if P b X then 1 else 0)
    _ = ∑ b ∈ B₀, weightedProbability weight (P b) := by
      apply Finset.sum_congr rfl
      intro b _
      exact weightedExpectation_indicator weight (P b)

/-- Pulling a constant through a finite nonnegative expectation. -/
theorem weightedExpectation_const_mul (weight : Finset A → ℝ≥0)
    (c : ℝ≥0) (Z : Finset A → ℝ≥0) :
    weightedExpectation weight (fun X ↦ c * Z X) =
      c * weightedExpectation weight Z := by
  unfold weightedExpectation
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro X _
  ring

/-- Some outcome has cost at most the expectation in a normalized finite
weighted space. -/
theorem exists_le_weightedExpectation (weight : Finset A → ℝ≥0)
    (hsum : ∑ X, weight X = 1) (Z : Finset A → ℝ≥0) :
    ∃ X, Z X ≤ weightedExpectation weight Z := by
  classical
  obtain ⟨X, _hX, hmin⟩ :=
    Finset.exists_min_image (Finset.univ : Finset (Finset A)) Z Finset.univ_nonempty
  refine ⟨X, ?_⟩
  calc
    Z X = (∑ Y, weight Y) * Z X := by rw [hsum, one_mul]
    _ = ∑ Y, weight Y * Z X := by rw [Finset.sum_mul]
    _ ≤ ∑ Y, weight Y * Z Y := by
      exact Finset.sum_le_sum fun Y hY ↦
        mul_le_mul_of_nonneg_left (hmin Y (Finset.mem_univ Y)) (by positivity)
    _ = weightedExpectation weight Z := rfl

end FiniteProbability

section BernoulliLowerTail

variable {alpha : Type*} [Fintype alpha] [DecidableEq alpha]

private theorem coe_weightedExpectation {Omega : Type*} [Fintype Omega]
    (weight : Omega → ℝ≥0) (Z : Omega → ℝ≥0) :
    ((weightedExpectation weight Z : ℝ≥0) : ℝ) =
      realWeightedExpectation weight (fun omega ↦ (Z omega : ℝ)) := by
  simp [weightedExpectation, realWeightedExpectation]

private theorem weightedProbability_mul_le_realWeightedExpectation
    {Omega : Type*} [Fintype Omega] (weight : Omega → ℝ≥0) (P : Omega → Prop)
    (Z : Omega → ℝ) (a : ℝ) (hZ : ∀ omega, 0 ≤ Z omega)
    (hPa : ∀ omega, P omega → a ≤ Z omega) :
    (weightedProbability weight P : ℝ) * a ≤
      realWeightedExpectation weight Z := by
  classical
  unfold weightedProbability realWeightedExpectation
  push_cast
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro omega _homega
  by_cases hPomega : P omega
  · simp only [hPomega, if_true]
    exact mul_le_mul_of_nonneg_left (hPa omega hPomega) (NNReal.coe_nonneg _)
  · simp only [hPomega, if_false, NNReal.coe_zero, zero_mul]
    exact mul_nonneg (NNReal.coe_nonneg _) (hZ omega)

private theorem bernoulli_inter_card_centered_sq (p : ℝ≥0) (hp : p ≤ 1)
    (D : Finset alpha) (hD : D.Nonempty) :
    realWeightedExpectation (bernoulliWeight p)
        (fun X : Finset alpha ↦
          (((D ∩ X).card : ℝ) - (p : ℝ) * (D.card : ℝ)) ^ 2) =
      (p : ℝ) * (D.card : ℝ) * (1 - (p : ℝ)) := by
  classical
  let Y : Finset alpha → ℝ := fun X ↦ ((D ∩ X).card : ℝ)
  let mu : ℝ := (p : ℝ) * (D.card : ℝ)
  have hmassNN : ∑ X : Finset alpha, bernoulliWeight p X = 1 :=
    sum_bernoulliWeight p hp
  have hmass : ∑ X : Finset alpha, (bernoulliWeight p X : ℝ) = 1 := by
    exact_mod_cast hmassNN
  have hfirstNN := bernoulli_expect_inter_card p hp D
  change weightedExpectation (bernoulliWeight p)
      (fun X : Finset alpha ↦ ((D ∩ X).card : ℝ≥0)) = _ at hfirstNN
  have hfirst : realWeightedExpectation (bernoulliWeight p) Y = mu := by
    dsimp [mu]
    change realWeightedExpectation (bernoulliWeight p)
      (fun X : Finset alpha ↦ (((D ∩ X).card : ℝ≥0) : ℝ)) = _
    rw [← coe_weightedExpectation]
    simpa only [NNReal.coe_mul, NNReal.coe_natCast] using
      congrArg (fun z : ℝ≥0 ↦ (z : ℝ)) hfirstNN
  have hsecondNN := bernoulli_expect_inter_card_sq p hp D
  change weightedExpectation (bernoulliWeight p)
      (fun X : Finset alpha ↦ ((D ∩ X).card : ℝ≥0) ^ 2) = _ at hsecondNN
  have hsubNN : (D.card : ℝ≥0) - 1 = ((D.card - 1 : ℕ) : ℝ≥0) := by
    apply NNReal.eq
    simp [Nat.cast_sub (Finset.one_le_card.mpr hD)]
  rw [hsubNN] at hsecondNN
  have hsecond :
      realWeightedExpectation (bernoulliWeight p) (fun X ↦ (Y X) ^ 2) =
        (p : ℝ) * (D.card : ℝ) +
          (p : ℝ) ^ 2 * (D.card : ℝ) * ((D.card - 1 : ℕ) : ℝ) := by
    change realWeightedExpectation (bernoulliWeight p)
      (fun X : Finset alpha ↦ ((((D ∩ X).card : ℝ≥0) ^ 2 : ℝ≥0) : ℝ)) = _
    rw [← coe_weightedExpectation]
    simpa only [NNReal.coe_add, NNReal.coe_mul, NNReal.coe_pow, NNReal.coe_natCast] using
      congrArg (fun z : ℝ≥0 ↦ (z : ℝ)) hsecondNN
  have hexpand :
      realWeightedExpectation (bernoulliWeight p) (fun X ↦ (Y X - mu) ^ 2) =
        realWeightedExpectation (bernoulliWeight p) (fun X ↦ (Y X) ^ 2) -
          2 * mu * realWeightedExpectation (bernoulliWeight p) Y +
          mu ^ 2 * ∑ X : Finset alpha, (bernoulliWeight p X : ℝ) := by
    unfold realWeightedExpectation
    calc
      ∑ X : Finset alpha, (bernoulliWeight p X : ℝ) * (Y X - mu) ^ 2 =
          ∑ X : Finset alpha,
            ((bernoulliWeight p X : ℝ) * (Y X) ^ 2 -
              2 * mu * ((bernoulliWeight p X : ℝ) * Y X) +
              mu ^ 2 * (bernoulliWeight p X : ℝ)) := by
            apply Finset.sum_congr rfl
            intro X _hX
            ring
      _ = (∑ X : Finset alpha, (bernoulliWeight p X : ℝ) * (Y X) ^ 2) -
          2 * mu * (∑ X : Finset alpha, (bernoulliWeight p X : ℝ) * Y X) +
          mu ^ 2 * ∑ X : Finset alpha, (bernoulliWeight p X : ℝ) := by
            rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
            simp only [← Finset.mul_sum]
  rw [show (fun X : Finset alpha ↦
      (((D ∩ X).card : ℝ) - (p : ℝ) * (D.card : ℝ)) ^ 2) =
      (fun X ↦ (Y X - mu) ^ 2) by rfl]
  rw [hexpand, hfirst, hsecond, hmass]
  dsimp [mu]
  have hcard_cast : ((D.card - 1 : ℕ) : ℝ) = (D.card : ℝ) - 1 := by
    rw [Nat.cast_sub (Finset.one_le_card.mpr hD)]
    norm_num
  rw [hcard_cast]
  ring

/-- A Bernoulli sample with retention probability `1 / (2s)` leaves fewer
than `|D| / (4s)` points of `D` with probability at most `1/4`, once
`|D| ≥ 32s`. -/
theorem bernoulli_inter_card_lower_tail (D : Finset alpha) (s : ℕ)
    (hs : 1 ≤ s) (hd : 32 * s ≤ D.card) :
    weightedProbability
        (bernoulliWeight (1 / (2 * (s : ℝ≥0))))
        (fun X : Finset alpha ↦ (D ∩ X).card < D.card / (4 * s)) ≤ 1 / 4 := by
  classical
  let p : ℝ≥0 := 1 / (2 * (s : ℝ≥0))
  let Y : Finset alpha → ℝ := fun X ↦ ((D ∩ X).card : ℝ)
  let mu : ℝ := (p : ℝ) * (D.card : ℝ)
  have hsNN : (1 : ℝ≥0) ≤ (s : ℝ≥0) := by exact_mod_cast hs
  have hdenNN : (1 : ℝ≥0) ≤ 2 * (s : ℝ≥0) := by nlinarith
  have hp : p ≤ 1 := by
    dsimp [p]
    exact (div_le_one (by positivity : (0 : ℝ≥0) < 2 * (s : ℝ≥0))).2 hdenNN
  have hsR : (1 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs
  have hsposR : 0 < (s : ℝ) := lt_of_lt_of_le zero_lt_one hsR
  have hdenR : 0 < 2 * (s : ℝ) := by positivity
  have hdR : 32 * (s : ℝ) ≤ (D.card : ℝ) := by exact_mod_cast hd
  have hD : D.Nonempty := by
    apply Finset.card_pos.mp
    have hspos : 0 < s := lt_of_lt_of_le Nat.zero_lt_one hs
    exact (Nat.mul_pos (by norm_num) hspos).trans_le hd
  have hpcoe : (p : ℝ) = 1 / (2 * (s : ℝ)) := by simp [p]
  have hmu16 : 16 ≤ mu := by
    have hfrac : 16 ≤ (D.card : ℝ) / (2 * (s : ℝ)) := by
      rw [le_div_iff₀ hdenR]
      nlinarith
    dsimp [mu]
    rw [hpcoe]
    convert hfrac using 1 <;> field_simp <;> ring
  have hmupos : 0 < mu := lt_of_lt_of_le (by norm_num) hmu16
  have hthreshold : (D.card : ℝ) / (4 * (s : ℝ)) = mu / 2 := by
    dsimp [mu]
    rw [hpcoe]
    field_simp
    <;> ring
  have hmarkov :
      (weightedProbability (bernoulliWeight p)
          (fun X : Finset alpha ↦ (D ∩ X).card < D.card / (4 * s)) : ℝ) *
          (mu / 2) ^ 2 ≤
        realWeightedExpectation (bernoulliWeight p)
          (fun X : Finset alpha ↦ (Y X - mu) ^ 2) := by
    apply weightedProbability_mul_le_realWeightedExpectation
    · intro X
      positivity
    · intro X hX
      have hcast :
          (((D ∩ X).card : ℕ) : ℝ) < ((D.card / (4 * s) : ℕ) : ℝ) := by
        exact_mod_cast hX
      have hcastDiv :
          ((D.card / (4 * s) : ℕ) : ℝ) ≤
            (D.card : ℝ) / ((4 * s : ℕ) : ℝ) := Nat.cast_div_le
      have hY : Y X < mu / 2 := by
        rw [show ((4 * s : ℕ) : ℝ) = 4 * (s : ℝ) by norm_num] at hcastDiv
        exact hcast.trans_le (hcastDiv.trans_eq hthreshold)
      have hhalf : 0 ≤ mu / 2 := by positivity
      have hdiff : mu / 2 ≤ mu - Y X := by linarith
      have hsquares := mul_self_le_mul_self hhalf hdiff
      nlinarith
  have hcenter := bernoulli_inter_card_centered_sq p hp D hD
  have hvariance :
      realWeightedExpectation (bernoulliWeight p)
          (fun X : Finset alpha ↦ (Y X - mu) ^ 2) ≤ mu := by
    rw [show (fun X : Finset alpha ↦ (Y X - mu) ^ 2) =
        (fun X : Finset alpha ↦
          (((D ∩ X).card : ℝ) - (p : ℝ) * (D.card : ℝ)) ^ 2) by rfl]
    rw [hcenter]
    dsimp [mu]
    have hnonneg : 0 ≤ (p : ℝ) * (D.card : ℝ) * (p : ℝ) := by positivity
    nlinarith
  have hquad : mu ≤ (1 / 4 : ℝ) * (mu / 2) ^ 2 := by
    have hprod : 0 ≤ mu * (mu - 16) :=
      mul_nonneg (le_of_lt hmupos) (sub_nonneg.mpr hmu16)
    nlinarith
  have hmul :
      (weightedProbability (bernoulliWeight p)
          (fun X : Finset alpha ↦ (D ∩ X).card < D.card / (4 * s)) : ℝ) *
          (mu / 2) ^ 2 ≤ (1 / 4 : ℝ) * (mu / 2) ^ 2 :=
    hmarkov.trans (hvariance.trans hquad)
  have hsqpos : 0 < (mu / 2) ^ 2 := sq_pos_of_pos (by positivity)
  have hreal :
      (weightedProbability (bernoulliWeight p)
          (fun X : Finset alpha ↦ (D ∩ X).card < D.card / (4 * s)) : ℝ) ≤
        (1 / 4 : ℝ) := by
    nlinarith
  change weightedProbability (bernoulliWeight p)
      (fun X : Finset alpha ↦ (D ∩ X).card < D.card / (4 * s)) ≤ 1 / 4
  exact_mod_cast hreal

end BernoulliLowerTail

namespace BipartiteGraph

variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

/-- Restriction of a bipartite graph to a set of left vertices. -/
def restrictLeft (G : BipartiteGraph A B) (X : Finset A) : BipartiteGraph A B :=
  ⟨fun a b ↦ a ∈ X ∧ G.Adj a b⟩

@[simp]
theorem restrictLeft_adj (G : BipartiteGraph A B) (X : Finset A) (a : A) (b : B) :
    (G.restrictLeft X).Adj a b ↔ a ∈ X ∧ G.Adj a b :=
  Iff.rfl

@[simp]
theorem leftNeighbors_restrictLeft (G : BipartiteGraph A B) (X : Finset A) (b : B) :
    (G.restrictLeft X).leftNeighbors b = G.leftNeighbors b ∩ X := by
  ext a
  simp [and_comm]

@[simp]
theorem rightDegree_restrictLeft (G : BipartiteGraph A B) (X : Finset A) (b : B) :
    (G.restrictLeft X).rightDegree b = (G.leftNeighbors b ∩ X).card := by
  simp [rightDegree]

/-- Right vertices which retain at least `r` neighbours after a left thinning. -/
def goodRight (G : BipartiteGraph A B) (X : Finset A) (B₀ : Finset B) (r : ℕ) : Finset B :=
  B₀.filter fun b ↦ r ≤ (G.leftNeighbors b ∩ X).card

/-- Right vertices which fail the degree cutoff after a left thinning. -/
def badRight (G : BipartiteGraph A B) (X : Finset A) (B₀ : Finset B) (r : ℕ) : Finset B :=
  B₀.filter fun b ↦ (G.leftNeighbors b ∩ X).card < r

@[simp]
theorem mem_goodRight (G : BipartiteGraph A B) (X : Finset A) (B₀ : Finset B)
    (r : ℕ) (b : B) :
    b ∈ G.goodRight X B₀ r ↔ b ∈ B₀ ∧ r ≤ (G.leftNeighbors b ∩ X).card := by
  simp [goodRight]

@[simp]
theorem mem_badRight (G : BipartiteGraph A B) (X : Finset A) (B₀ : Finset B)
    (r : ℕ) (b : B) :
    b ∈ G.badRight X B₀ r ↔ b ∈ B₀ ∧ (G.leftNeighbors b ∩ X).card < r := by
  simp [badRight]

theorem card_goodRight_add_card_badRight (G : BipartiteGraph A B)
    (X : Finset A) (B₀ : Finset B) (r : ℕ) :
    (G.goodRight X B₀ r).card + (G.badRight X B₀ r).card = B₀.card := by
  simpa [goodRight, badRight, not_le] using
    (B₀.card_filter_add_card_filter_not
      (p := fun b ↦ r ≤ (G.leftNeighbors b ∩ X).card))

/-- Abstract alteration step.  If the expected cost of the selected left
vertices is at most half the right side and each right vertex is bad with
probability at most one quarter, some outcome has strictly more good right
vertices than `s` times selected left vertices. -/
theorem exists_leftSet_ratio_of_probability_bounds
    (G : BipartiteGraph A B) (A₀ : Finset A) (B₀ : Finset B) (r s : ℕ)
    (weight : Finset A → ℝ≥0) (hsum : ∑ X, weight X = 1)
    (hne : B₀.Nonempty)
    (hsize :
      weightedExpectation weight
          (fun X ↦ ((s * (A₀ ∩ X).card : ℕ) : ℝ≥0)) ≤
        (B₀.card : ℝ≥0) / 2)
    (hbad : ∀ b ∈ B₀,
      weightedProbability weight
          (fun X ↦ (G.leftNeighbors b ∩ (A₀ ∩ X)).card < r) ≤ 1 / 4) :
    ∃ X : Finset A, X ⊆ A₀ ∧ s * X.card < (G.goodRight X B₀ r).card := by
  classical
  let badCost : Finset A → ℝ≥0 := fun X ↦
    ((G.badRight (A₀ ∩ X) B₀ r).card : ℝ≥0)
  have hbad_expect :
      weightedExpectation weight badCost ≤ (B₀.card : ℝ≥0) / 4 := by
    rw [show weightedExpectation weight badCost =
        ∑ b ∈ B₀, weightedProbability weight
          (fun X ↦ (G.leftNeighbors b ∩ (A₀ ∩ X)).card < r) by
      simpa [badCost, badRight] using
        (weightedExpectation_card_filter weight B₀
          (fun b X ↦ (G.leftNeighbors b ∩ (A₀ ∩ X)).card < r))]
    calc
      ∑ b ∈ B₀, weightedProbability weight
          (fun X ↦ (G.leftNeighbors b ∩ (A₀ ∩ X)).card < r) ≤
          ∑ _b ∈ B₀, (1 / 4 : ℝ≥0) := by
        exact Finset.sum_le_sum fun b hb ↦ hbad b hb
      _ = (B₀.card : ℝ≥0) / 4 := by
        simp [div_eq_mul_inv, mul_comm]
  let vertexCost : Finset A → ℝ≥0 := fun X ↦
    ((s * (A₀ ∩ X).card : ℕ) : ℝ≥0)
  let totalCost : Finset A → ℝ≥0 := fun X ↦ vertexCost X + badCost X
  have htotal_expect :
      weightedExpectation weight totalCost ≤
        (B₀.card : ℝ≥0) / 2 + (B₀.card : ℝ≥0) / 4 := by
    rw [show weightedExpectation weight totalCost =
        weightedExpectation weight vertexCost + weightedExpectation weight badCost by
      simpa [totalCost] using weightedExpectation_add weight vertexCost badCost]
    exact add_le_add hsize hbad_expect
  have hquarter :
      (B₀.card : ℝ≥0) / 2 + (B₀.card : ℝ≥0) / 4 <
        (B₀.card : ℝ≥0) := by
    have hpos : (0 : ℝ≥0) < (B₀.card : ℝ≥0) := by
      exact_mod_cast hne.card_pos
    nlinarith
  obtain ⟨S, hS⟩ := exists_le_weightedExpectation weight hsum totalCost
  let X := A₀ ∩ S
  have hcost : totalCost S < (B₀.card : ℝ≥0) :=
    hS.trans_lt (htotal_expect.trans_lt hquarter)
  have hcost_nat :
      s * X.card + (G.badRight X B₀ r).card < B₀.card := by
    have hcost' :
        ((s * X.card + (G.badRight X B₀ r).card : ℕ) : ℝ≥0) <
          (B₀.card : ℝ≥0) := by
      simpa [totalCost, vertexCost, badCost, X, Nat.cast_add] using hcost
    exact_mod_cast hcost'
  have hpartition := G.card_goodRight_add_card_badRight X B₀ r
  refine ⟨X, inter_subset_left, ?_⟩
  omega

/-- Once a thinning leaves `r` neighbours at every surviving right vertex,
trim independently at those vertices to obtain an exactly half-regular
subgraph. -/
theorem exists_halfRegularSubgraphOf_goodRight (G : BipartiteGraph A B)
    (X : Finset A) (B₀ : Finset B) (r : ℕ)
    (hne : (G.goodRight X B₀ r).Nonempty) :
    ∃ H : BipartiteGraph A B,
      H.IsHalfRegularSubgraphOf G X (G.goodRight X B₀ r) r := by
  classical
  let B₁ := G.goodRight X B₀ r
  have hdeg : ∀ b ∈ B₁, r ≤ (G.leftNeighbors b ∩ X).card := by
    intro b hb
    exact (G.mem_goodRight X B₀ r b).mp hb |>.2
  let N : B → Finset A := fun b ↦
    if hb : b ∈ B₁ then (Finset.exists_subset_card_eq (hdeg b hb)).choose else ∅
  have hNsub (b : B) (hb : b ∈ B₁) : N b ⊆ G.leftNeighbors b ∩ X := by
    simp only [N, dif_pos hb]
    exact (Finset.exists_subset_card_eq (hdeg b hb)).choose_spec.1
  have hNcard (b : B) (hb : b ∈ B₁) : (N b).card = r := by
    simp only [N, dif_pos hb]
    exact (Finset.exists_subset_card_eq (hdeg b hb)).choose_spec.2
  let H : BipartiteGraph A B := ⟨fun a b ↦ b ∈ B₁ ∧ a ∈ N b⟩
  refine ⟨H, ?_, ?_, hne, ?_⟩
  · intro a b hab
    have hb : b ∈ B₁ := hab.1
    have ha : a ∈ G.leftNeighbors b ∩ X := (hNsub b hb) hab.2
    exact (G.mem_leftNeighbors a b).mp (mem_inter.mp ha).1
  · intro a b hab
    have hb : b ∈ B₁ := hab.1
    have ha : a ∈ G.leftNeighbors b ∩ X := (hNsub b hb) hab.2
    exact ⟨(mem_inter.mp ha).2, hb⟩
  · intro b hb
    have hleft : H.leftNeighbors b = N b := by
      ext a
      simp only [mem_leftNeighbors]
      change (b ∈ B₁ ∧ a ∈ N b) ↔ a ∈ N b
      exact and_iff_right hb
    rw [rightDegree, hleft, hNcard b hb]

/-- Deterministic endpoint of ratio amplification.  The probabilistic part of
the argument only has to find a left set for which the displayed strict
cardinality inequality holds. -/
theorem exists_halfRegularSubgraphOf_goodRight_with_ratio
    (G : BipartiteGraph A B) (X : Finset A) (B₀ : Finset B) (r s : ℕ)
    (hratio : s * X.card < (G.goodRight X B₀ r).card) :
    ∃ H : BipartiteGraph A B,
      H.IsHalfRegularSubgraphOf G X (G.goodRight X B₀ r) r ∧
        s * X.card ≤ (G.goodRight X B₀ r).card := by
  have hne : (G.goodRight X B₀ r).Nonempty :=
    Finset.card_pos.mp (lt_of_le_of_lt (Nat.zero_le _) hratio)
  obtain ⟨H, hH⟩ := G.exists_halfRegularSubgraphOf_goodRight X B₀ r hne
  exact ⟨H, hH, hratio.le⟩

/-- **PRS ratio amplification (finite, rounded form).**

Suppose the active right side is `d`-regular into the active left side, the
right side is at least as large as the left side, and `d ≥ 32s`.  Then there
is an explicitly supported half-regular subgraph whose right/left active-side
ratio is at least `s` and whose half-degree is `d / (4s)`.

The constant `32` is inessential.  It is the convenient finite threshold at
which the second-moment lower-tail estimate has failure probability at most
one quarter. -/
theorem exists_ratioAmplified_halfRegularSubgraph
    (G : BipartiteGraph A B) (A₀ : Finset A) (B₀ : Finset B) (d s : ℕ)
    (hsupp : G.SupportedOn A₀ B₀) (hne : B₀.Nonempty)
    (hreg : G.IsRightRegularOn B₀ d) (hcard : A₀.card ≤ B₀.card)
    (hs : 1 ≤ s) (hd : 32 * s ≤ d) :
    ∃ A₁ : Finset A, ∃ B₁ : Finset B, ∃ H : BipartiteGraph A B,
      A₁ ⊆ A₀ ∧ B₁ ⊆ B₀ ∧
        H.IsHalfRegularSubgraphOf G A₁ B₁ (d / (4 * s)) ∧
        s * A₁.card ≤ B₁.card := by
  classical
  let p : ℝ≥0 := 1 / (2 * (s : ℝ≥0))
  have hp : p ≤ 1 := by
    dsimp [p]
    have hs2 : 1 ≤ 2 * s := by omega
    exact (div_le_one (by positivity : (0 : ℝ≥0) < 2 * (s : ℝ≥0))).2 (by
      exact_mod_cast hs2)
  have hsum : ∑ X : Finset A, bernoulliWeight p X = 1 :=
    sum_bernoulliWeight p hp
  have hsize :
      weightedExpectation (bernoulliWeight p)
          (fun X : Finset A ↦ ((s * (A₀ ∩ X).card : ℕ) : ℝ≥0)) ≤
        (B₀.card : ℝ≥0) / 2 := by
    calc
      weightedExpectation (bernoulliWeight p)
          (fun X : Finset A ↦ ((s * (A₀ ∩ X).card : ℕ) : ℝ≥0)) =
          (s : ℝ≥0) * weightedExpectation (bernoulliWeight p)
            (fun X : Finset A ↦ ((A₀ ∩ X).card : ℝ≥0)) := by
        simpa [Nat.cast_mul] using
          (weightedExpectation_const_mul (bernoulliWeight p) (s : ℝ≥0)
            (fun X : Finset A ↦ ((A₀ ∩ X).card : ℝ≥0)))
      _ = (s : ℝ≥0) * (p * A₀.card) := by
        have hm := bernoulli_expect_inter_card p hp A₀
        change weightedExpectation (bernoulliWeight p)
            (fun X : Finset A ↦ ((A₀ ∩ X).card : ℝ≥0)) = _ at hm
        rw [hm]
      _ = (A₀.card : ℝ≥0) / 2 := by
        apply NNReal.eq
        simp only [NNReal.coe_mul, NNReal.coe_natCast, NNReal.coe_div, NNReal.coe_ofNat]
        dsimp [p]
        simp only [NNReal.coe_div, NNReal.coe_one, NNReal.coe_mul, NNReal.coe_ofNat,
          NNReal.coe_natCast]
        have hs0 : (s : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hs)
        field_simp
      _ ≤ (B₀.card : ℝ≥0) / 2 := by
        gcongr
  have hbad : ∀ b ∈ B₀,
      weightedProbability (bernoulliWeight p)
          (fun X : Finset A ↦
            (G.leftNeighbors b ∩ (A₀ ∩ X)).card < d / (4 * s)) ≤ 1 / 4 := by
    intro b hb
    have hDb : (G.leftNeighbors b).card = d := hreg b hb
    have hDsub : G.leftNeighbors b ⊆ A₀ := by
      intro a ha
      exact (hsupp ((G.mem_leftNeighbors a b).mp ha)).1
    have hinter (X : Finset A) :
        G.leftNeighbors b ∩ (A₀ ∩ X) = G.leftNeighbors b ∩ X := by
      ext a
      simp only [mem_inter]
      constructor
      · exact fun ha ↦ ⟨ha.1, ha.2.2⟩
      · exact fun ha ↦ ⟨ha.1, hDsub ha.1, ha.2⟩
    have htail := bernoulli_inter_card_lower_tail (G.leftNeighbors b) s hs (by
      omega : 32 * s ≤ (G.leftNeighbors b).card)
    simpa [p, hDb, hinter] using htail
  obtain ⟨X, hXA, hratio⟩ :=
    G.exists_leftSet_ratio_of_probability_bounds A₀ B₀ (d / (4 * s)) s
      (bernoulliWeight p) hsum hne hsize hbad
  obtain ⟨H, hH, hratio'⟩ :=
    G.exists_halfRegularSubgraphOf_goodRight_with_ratio
      X B₀ (d / (4 * s)) s hratio
  exact ⟨X, G.goodRight X B₀ (d / (4 * s)), H, hXA,
    Finset.filter_subset _ _, hH, hratio'⟩

end BipartiteGraph

end

end Erdos182
