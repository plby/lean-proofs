/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import ErdosProblems.Erdos444.Basic

/-!
# Prefix products for Erdős Problem 444

This file records the elementary part of a possible sparse-set argument.
The reciprocal mass of a prefix is at most its cardinality, and all members
of a finite prefix divide the product of that prefix.  Thus a divergent
reciprocal mass forces arbitrarily large prefix cardinalities, and those
cardinalities give lower bounds for the maximal divisor count at the
corresponding product cutoffs.

The final comparison deliberately evaluates the reciprocal mass at the
product cutoff.  Controlling that later mass is the genuinely additional
input required to turn this elementary construction into the full divergent
case of Problem 444.
-/

open scoped BigOperators

namespace Erdos444

/-- The positive members of `A` below a natural cutoff. -/
noncomputable def prefixMembersNat (A : Set ℕ) (x : ℕ) : Finset ℕ := by
  classical
  exact (positiveBelowNat x).filter fun a ↦ a ∈ A

/-- The number of positive members of `A` below a natural cutoff. -/
noncomputable def prefixCardNat (A : Set ℕ) (x : ℕ) : ℕ :=
  (prefixMembersNat A x).card

/-- The product of the positive members of `A` below a natural cutoff. -/
noncomputable def prefixProductNat (A : Set ℕ) (x : ℕ) : ℕ :=
  ∏ a ∈ prefixMembersNat A x, a

@[simp]
theorem mem_prefixMembersNat_iff {A : Set ℕ} {x a : ℕ} :
    a ∈ prefixMembersNat A x ↔ 1 ≤ a ∧ a < x ∧ a ∈ A := by
  classical
  simp [prefixMembersNat, and_assoc]

/-- Each reciprocal in a positive prefix is at most one. -/
theorem reciprocalMassNat_le_prefixCardNat (A : Set ℕ) (x : ℕ) :
    reciprocalMassNat A x ≤ prefixCardNat A x := by
  classical
  unfold reciprocalMassNat prefixCardNat prefixMembersNat
  calc
    (∑ a ∈ (positiveBelowNat x).filter (fun a ↦ a ∈ A), (a : ℝ)⁻¹)
        ≤ ∑ _a ∈ (positiveBelowNat x).filter (fun a ↦ a ∈ A), (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro a ha
          have ha1 : 1 ≤ a :=
            (mem_positiveBelowNat_iff.mp (Finset.mem_filter.mp ha).1).1
          have ha0 : (0 : ℝ) < a := by positivity
          exact (inv_le_one₀ ha0).mpr (by exact_mod_cast ha1)
    _ = ((positiveBelowNat x).filter (fun a ↦ a ∈ A)).card := by simp

/-- Divergent reciprocal mass forces arbitrarily large prefix cardinalities,
with the cutoff still lying on every prescribed tail. -/
theorem tailUnbounded_prefixCardNat_of_tailUnbounded_reciprocalMassNat
    (A : Set ℕ) (hA : tailUnbounded (reciprocalMassNat A)) :
    tailUnbounded (fun x ↦ (prefixCardNat A x : ℝ)) := by
  intro C X
  obtain ⟨x, hXx, hx⟩ := hA C X
  exact ⟨x, hXx, hx.trans_le (reciprocalMassNat_le_prefixCardNat A x)⟩

/-- For the monotone reciprocal-mass sequence, ordinary unboundedness above
already implies unboundedness on every tail. -/
theorem tailUnbounded_reciprocalMassNat_of_unbounded
    (A : Set ℕ) (hA : ∀ C : ℝ, ∃ x : ℕ, C < reciprocalMassNat A x) :
    tailUnbounded (reciprocalMassNat A) := by
  intro C X
  obtain ⟨y, hy⟩ := hA C
  refine ⟨max X y, le_max_left _ _, hy.trans_le ?_⟩
  exact reciprocalMassNat_mono A (le_max_right X y)

/-- A prefix product is nonzero because every factor in the prefix is
positive. -/
theorem prefixProductNat_ne_zero (A : Set ℕ) (x : ℕ) :
    prefixProductNat A x ≠ 0 := by
  classical
  unfold prefixProductNat
  exact Finset.prod_ne_zero_iff.mpr fun a ha ↦ by
    exact Nat.ne_of_gt (mem_prefixMembersNat_iff.mp ha).1

/-- Every prefix member divides the prefix product, so the prefix cardinality
is a lower bound for the maximal divisor count at any cutoff past that
product.  The `max` makes the resulting cutoff lie beyond an arbitrary `X`. -/
theorem prefixCardNat_le_maxDivisorCountNat_productCutoff
    (A : Set ℕ) (y X : ℕ) :
    prefixCardNat A y ≤
      maxDivisorCountNat A (max X (prefixProductNat A y + 1)) := by
  classical
  let S := prefixMembersNat A y
  let p := prefixProductNat A y
  have hS : ∀ a ∈ S, a ∈ A ∧ a ≠ 0 := by
    intro a ha
    have ha' := mem_prefixMembersNat_iff.mp ha
    exact ⟨ha'.2.2, Nat.ne_of_gt ha'.1⟩
  have hp : 0 < p := Nat.pos_of_ne_zero (prefixProductNat_ne_zero A y)
  have hproduct : (∏ a ∈ S, a) = p := by
    rfl
  have hcut : p < max X (p + 1) :=
    (Nat.lt_succ_self p).trans_le (le_max_right X (p + 1))
  change S.card ≤ maxDivisorCountNat A (max X (p + 1))
  exact (card_le_divisorCount_prod A S hS).trans
    (hproduct ▸ divisorCount_le_maxDivisorCountNat hp hcut)

/-- Quantitative real-valued form of the prefix-product lower bound. -/
theorem prefixProduct_weight_le_ratioNat
    (A : Set ℕ) (k y X : ℕ) :
    (prefixCardNat A y : ℝ) /
        reciprocalMassNat A (max X (prefixProductNat A y + 1)) ^ k ≤
      ratioNat A k (max X (prefixProductNat A y + 1)) := by
  unfold ratioNat
  exact div_le_div_of_nonneg_right
    (by exact_mod_cast prefixCardNat_le_maxDivisorCountNat_productCutoff A y X)
    (pow_nonneg (reciprocalMassNat_nonneg A _) k)

/-- Any independent estimate making the prefix-product weights unbounded
immediately transfers to the ratios in Problem 444. -/
theorem tailUnbounded_ratioNat_of_prefixProduct_weights
    (A : Set ℕ) (k : ℕ)
    (h : ∀ C : ℝ, ∀ X : ℕ, ∃ y : ℕ,
      C < (prefixCardNat A y : ℝ) /
        reciprocalMassNat A (max X (prefixProductNat A y + 1)) ^ k) :
    tailUnbounded (ratioNat A k) := by
  intro C X
  obtain ⟨y, hy⟩ := h C X
  refine ⟨max X (prefixProductNat A y + 1), le_max_left _ _, ?_⟩
  exact hy.trans_le (prefixProduct_weight_le_ratioNat A k y X)

/-! ## A base-four density consequence of divergent reciprocal mass -/

/-- Members of `A` in the base-four shell `[4^j, 4^(j+1))`. -/
noncomputable def fourShellNat (A : Set ℕ) (j : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Ico (4 ^ j) (4 ^ (j + 1))).filter fun a ↦ a ∈ A

/-- Reciprocal mass in one base-four shell. -/
noncomputable def fourShellMassNat (A : Set ℕ) (j : ℕ) : ℝ :=
  ∑ a ∈ fourShellNat A j, (a : ℝ)⁻¹

@[simp]
theorem mem_fourShellNat_iff {A : Set ℕ} {j a : ℕ} :
    a ∈ fourShellNat A j ↔ 4 ^ j ≤ a ∧ a < 4 ^ (j + 1) ∧ a ∈ A := by
  classical
  simp [fourShellNat, and_assoc]

private theorem fourShell_pairwiseDisjoint (A : Set ℕ) (J : ℕ) :
    Set.PairwiseDisjoint (↑(Finset.range J)) (fourShellNat A) := by
  classical
  intro i hi j hj hij
  change Disjoint (fourShellNat A i) (fourShellNat A j)
  rw [Finset.disjoint_left]
  intro a hai haj
  have hi' := mem_fourShellNat_iff.mp hai
  have hj' := mem_fourShellNat_iff.mp haj
  rcases lt_or_gt_of_ne hij with hijlt | hjilt
  · have hp : 4 ^ (i + 1) ≤ 4 ^ j := by
      exact Nat.pow_le_pow_right (by norm_num) (Nat.succ_le_iff.mpr hijlt)
    exact (not_le_of_gt hi'.2.1) (hp.trans hj'.1)
  · have hp : 4 ^ (j + 1) ≤ 4 ^ i := by
      exact Nat.pow_le_pow_right (by norm_num) (Nat.succ_le_iff.mpr hjilt)
    exact (not_le_of_gt hj'.2.1) (hp.trans hi'.1)

private theorem prefixMembersNat_four_pow_eq_biUnion (A : Set ℕ) (J : ℕ) :
    prefixMembersNat A (4 ^ J) =
      (Finset.range J).biUnion (fourShellNat A) := by
  classical
  ext a
  simp only [Finset.mem_biUnion, Finset.mem_range]
  constructor
  · intro ha
    have ha' := mem_prefixMembersNat_iff.mp ha
    let j := Nat.log 4 a
    have ha0 : a ≠ 0 := Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one ha'.1)
    have hjJ : j < J := Nat.log_lt_of_lt_pow ha0 ha'.2.1
    have hlow : 4 ^ j ≤ a := Nat.pow_log_le_self 4 ha0
    have hupp : a < 4 ^ (j + 1) := Nat.lt_pow_succ_log_self (by norm_num) a
    exact ⟨j, hjJ, mem_fourShellNat_iff.mpr ⟨hlow, hupp, ha'.2.2⟩⟩
  · rintro ⟨j, hjJ, ha⟩
    have ha' := mem_fourShellNat_iff.mp ha
    have hpow : 4 ^ (j + 1) ≤ 4 ^ J :=
      Nat.pow_le_pow_right (by norm_num) hjJ
    exact mem_prefixMembersNat_iff.mpr
      ⟨(Nat.one_le_pow j 4 (by norm_num)).trans ha'.1,
        ha'.2.1.trans_le hpow, ha'.2.2⟩

/-- A prefix ending at a power of four is the disjoint sum of its base-four
shells. -/
theorem reciprocalMassNat_four_pow_eq_sum_shells (A : Set ℕ) (J : ℕ) :
    reciprocalMassNat A (4 ^ J) =
      ∑ j ∈ Finset.range J, fourShellMassNat A j := by
  classical
  unfold reciprocalMassNat fourShellMassNat
  change (∑ a ∈ prefixMembersNat A (4 ^ J), (a : ℝ)⁻¹) = _
  rw [prefixMembersNat_four_pow_eq_biUnion A J]
  exact Finset.sum_biUnion (fourShell_pairwiseDisjoint A J)

/-- Under the density bound at the next base-four endpoint, one shell has
mass at most twice the corresponding geometric-series term. -/
theorem fourShellMassNat_le_geometric
    (A : Set ℕ) (j : ℕ)
    (hcard : prefixCardNat A (4 ^ (j + 1)) ≤ 2 ^ (j + 1)) :
    fourShellMassNat A j ≤ 2 * ((1 : ℝ) / 2) ^ j := by
  classical
  have hterm : ∀ a ∈ fourShellNat A j, (a : ℝ)⁻¹ ≤ ((4 ^ j : ℕ) : ℝ)⁻¹ := by
    intro a ha
    have ha' := mem_fourShellNat_iff.mp ha
    exact inv_anti₀ (by positivity) (by exact_mod_cast ha'.1)
  have hcardShell : (fourShellNat A j).card ≤ prefixCardNat A (4 ^ (j + 1)) := by
    apply Finset.card_le_card
    intro a ha
    exact mem_prefixMembersNat_iff.mpr
      ⟨(Nat.one_le_pow j 4 (by norm_num)).trans
          (mem_fourShellNat_iff.mp ha).1,
        (mem_fourShellNat_iff.mp ha).2.1, (mem_fourShellNat_iff.mp ha).2.2⟩
  calc
    fourShellMassNat A j
        ≤ ∑ _a ∈ fourShellNat A j, ((4 ^ j : ℕ) : ℝ)⁻¹ := by
          unfold fourShellMassNat
          exact Finset.sum_le_sum hterm
    _ = ((fourShellNat A j).card : ℝ) / (4 : ℝ) ^ j := by
      simp [div_eq_mul_inv]
    _ ≤ (2 ^ (j + 1) : ℕ) / (4 : ℝ) ^ j := by
      gcongr
      exact_mod_cast hcardShell.trans hcard
    _ = 2 * ((1 : ℝ) / 2) ^ j := by
      norm_num only [Nat.cast_pow, Nat.cast_ofNat]
      rw [show (4 : ℝ) ^ j = (2 : ℝ) ^ j * (2 : ℝ) ^ j by
        rw [← mul_pow]
        norm_num, pow_succ, div_pow]
      field_simp [pow_ne_zero]
      simp

/-- If every sufficiently late base-four prefix had cardinality at most
`2^j`, the reciprocal masses would be uniformly bounded.  Hence divergent
reciprocal mass forces base-four prefixes exceeding that square-root scale
at arbitrarily large exponents. -/
theorem arbitrarily_large_prefixCardNat_four_pow_gt_two_pow
    (A : Set ℕ) (hdiv : tailUnbounded (reciprocalMassNat A)) :
    ∀ J : ℕ, ∃ j : ℕ, J ≤ j ∧ 2 ^ j < prefixCardNat A (4 ^ j) := by
  intro J
  by_contra hcontra
  push Not at hcontra
  have hbound : ∀ x : ℕ,
      reciprocalMassNat A x ≤ reciprocalMassNat A (4 ^ J) + 4 := by
    intro x
    let L := max J (Nat.log 4 x + 1)
    have hJL : J ≤ L := le_max_left _ _
    have hxpow : x ≤ 4 ^ L := by
      exact (Nat.lt_pow_succ_log_self (by norm_num) x).le.trans
        (Nat.pow_le_pow_right (by norm_num) (le_max_right J (Nat.log 4 x + 1)))
    have hmono : reciprocalMassNat A x ≤ reciprocalMassNat A (4 ^ L) :=
      reciprocalMassNat_mono A hxpow
    rw [reciprocalMassNat_four_pow_eq_sum_shells A L] at hmono
    rw [reciprocalMassNat_four_pow_eq_sum_shells A J]
    have hsplit :
        ∑ j ∈ Finset.range L, fourShellMassNat A j =
          (∑ j ∈ Finset.range J, fourShellMassNat A j) +
            ∑ j ∈ Finset.Ico J L, fourShellMassNat A j := by
      exact (Finset.sum_range_add_sum_Ico (fourShellMassNat A) hJL).symm
    rw [hsplit] at hmono
    refine hmono.trans ?_
    gcongr
    calc
      (∑ j ∈ Finset.Ico J L, fourShellMassNat A j)
          ≤ ∑ j ∈ Finset.Ico J L, 2 * ((1 : ℝ) / 2) ^ j := by
            apply Finset.sum_le_sum
            intro j hj
            apply fourShellMassNat_le_geometric
            exact hcontra (j + 1) (by
              have hj' := Finset.mem_Ico.mp hj
              omega)
      _ ≤ ∑ j ∈ Finset.range L, 2 * ((1 : ℝ) / 2) ^ j := by
            apply Finset.sum_le_sum_of_subset_of_nonneg
            · intro j hj
              exact Finset.mem_range.mpr (Finset.mem_Ico.mp hj).2
            · intro j hj hjnot
              positivity
      _ = 2 * ∑ j ∈ Finset.range L, ((1 : ℝ) / 2) ^ j := by
            rw [Finset.mul_sum]
      _ ≤ 2 * 2 := by
            gcongr
            exact sum_geometric_two_le L
      _ = 4 := by norm_num
  obtain ⟨x, -, hx⟩ := hdiv (reciprocalMassNat A (4 ^ J) + 4) 0
  exact (not_le_of_gt hx) (hbound x)

/-! ## Prefix products at a base-four density spike -/

theorem prefixCardNat_le_cutoff (A : Set ℕ) (y : ℕ) :
    prefixCardNat A y ≤ y := by
  classical
  calc
    prefixCardNat A y ≤ (positiveBelowNat y).card := by
      unfold prefixCardNat prefixMembersNat
      exact Finset.card_filter_le _ _
    _ ≤ y := by
      simp [positiveBelowNat]

theorem prefixProductNat_le_pow_card (A : Set ℕ) (y : ℕ) :
    prefixProductNat A y ≤ y ^ prefixCardNat A y := by
  classical
  unfold prefixProductNat prefixCardNat
  calc
    (∏ a ∈ prefixMembersNat A y, a)
        ≤ ∏ _a ∈ prefixMembersNat A y, y := by
          apply Finset.prod_le_prod
          · intro a ha
            exact Nat.zero_le a
          · intro a ha
            exact (mem_prefixMembersNat_iff.mp ha).2.1.le
    _ = y ^ (prefixMembersNat A y).card := by simp

/-- A deliberately coarse tower bound for a prefix-product cutoff.  Its
double base-four logarithm is nevertheless only linear in `j`. -/
theorem prefixProductCutoff_le_four_tower
    (A : Set ℕ) {j X : ℕ} (hj : 1 ≤ j) (hX : X ≤ 4 ^ j) :
    max X (prefixProductNat A (4 ^ j) + 1) ≤ 4 ^ (4 ^ (2 * j + 2)) := by
  let m := prefixCardNat A (4 ^ j)
  let p := prefixProductNat A (4 ^ j)
  have hm : m ≤ 4 ^ j := prefixCardNat_le_cutoff A (4 ^ j)
  have hp₁ : p ≤ (4 ^ j) ^ m := prefixProductNat_le_pow_card A (4 ^ j)
  have hp₂ : (4 ^ j) ^ m ≤ (4 ^ j) ^ (4 ^ j) :=
    Nat.pow_le_pow_right (by positivity) hm
  have hrewrite : (4 ^ j) ^ (4 ^ j) = 4 ^ (j * 4 ^ j) := by
    rw [← pow_mul]
  have hp : p ≤ 4 ^ (j * 4 ^ j) := hp₁.trans (hp₂.trans_eq hrewrite)
  have hpowpos : 1 ≤ 4 ^ (j * 4 ^ j) := Nat.one_le_pow _ _ (by norm_num)
  have hpadd : p + 1 ≤ 4 ^ (j * 4 ^ j + 1) := by
    rw [pow_succ]
    omega
  have hjpow : j ≤ 4 ^ j :=
    (Nat.lt_pow_self (by norm_num : 1 < 4)).le
  have hexp : j * 4 ^ j + 1 ≤ 4 ^ (2 * j + 2) := by
    have hmul : j * 4 ^ j ≤ 4 ^ (2 * j) := by
      calc
        j * 4 ^ j ≤ 4 ^ j * 4 ^ j := Nat.mul_le_mul_right _ hjpow
        _ = 4 ^ (2 * j) := by rw [← pow_add]; congr 1; omega
    have hstep : 4 ^ (2 * j) + 1 ≤ 4 ^ (2 * j + 2) := by
      have hone : 1 ≤ 4 ^ (2 * j) := Nat.one_le_pow _ _ (by norm_num)
      rw [show 2 * j + 2 = (2 * j) + 2 by omega, pow_add]
      norm_num
    exact (Nat.add_le_add_right hmul 1).trans hstep
  have hpTower : p + 1 ≤ 4 ^ (4 ^ (2 * j + 2)) :=
    hpadd.trans (Nat.pow_le_pow_right (by norm_num) hexp)
  have hXTower : X ≤ 4 ^ (4 ^ (2 * j + 2)) := by
    refine hX.trans (Nat.pow_le_pow_right (by norm_num) ?_)
    exact hjpow.trans (Nat.pow_le_pow_right (by norm_num) (by omega))
  exact max_le hXTower hpTower

theorem iteratedLog_four_prefixProductCutoff_le
    (A : Set ℕ) {j X : ℕ} (hj : 1 ≤ j) (hX : X ≤ 4 ^ j) :
    Nat.log 4 (Nat.log 4 (max X (prefixProductNat A (4 ^ j) + 1))) ≤
      2 * j + 2 := by
  have h := prefixProductCutoff_le_four_tower A hj hX
  calc
    Nat.log 4 (Nat.log 4 (max X (prefixProductNat A (4 ^ j) + 1)))
        ≤ Nat.log 4 (Nat.log 4 (4 ^ (4 ^ (2 * j + 2)))) :=
      Nat.log_monotone (Nat.log_monotone h)
    _ = 2 * j + 2 := by simp [Nat.log_pow (by norm_num : 1 < 4)]

/-- An exponential eventually dominates any fixed power of the affine
function `2*j+2`, including after multiplication by a fixed constant. -/
theorem eventually_const_mul_two_mul_add_pow_lt_two_pow (C : ℝ) (d : ℕ) :
    ∀ᶠ j : ℕ in (Filter.atTop : Filter ℕ),
      C * (2 * (j : ℝ) + 2) ^ d < (2 : ℝ) ^ j := by
  by_cases hC : C ≤ 0
  · filter_upwards [] with j
    exact (mul_nonpos_of_nonpos_of_nonneg hC (pow_nonneg (by positivity) d)).trans_lt
      (pow_pos (by norm_num) j)
  have hCpos : 0 < C := lt_of_not_ge hC
  let ε : ℝ := 1 / (C * 2 ^ (d + 1))
  have hε : 0 < ε := by positivity
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp
    ((tendsto_pow_const_div_const_pow_of_one_lt d (by norm_num : (1 : ℝ) < 2)).eventually
      (gt_mem_nhds hε))
  filter_upwards [Filter.eventually_ge_atTop N] with j hjN
  have hsmall := hN (j + 1) (hjN.trans (Nat.le_succ j))
  have hdenpos : 0 < (2 : ℝ) ^ (j + 1) := pow_pos (by norm_num) _
  have hsmall' : ((j + 1 : ℕ) : ℝ) ^ d < ε * 2 ^ (j + 1) :=
    (div_lt_iff₀ hdenpos).mp hsmall
  have hmul := mul_lt_mul_of_pos_left hsmall'
    (mul_pos hCpos (pow_pos (by norm_num : (0 : ℝ) < 2) d))
  dsimp [ε] at hmul
  norm_num only [Nat.cast_add, Nat.cast_one] at hmul ⊢
  rw [show 2 * (j : ℝ) + 2 = 2 * ((j : ℝ) + 1) by ring, mul_pow]
  rw [pow_succ] at hmul
  field_simp [hCpos.ne', pow_ne_zero] at hmul
  rw [show (2 : ℝ) ^ (j + 1) = 2 ^ j * 2 by rw [pow_succ]] at hmul
  nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) j,
    pow_pos (by norm_num : (0 : ℝ) < 2) d]

/-- The complete low-growth branch of the divergent case.

Here the growth assumption is an integer-valued base-four version of
`reciprocalMassNat A u = O((log log u)^M)`: after an arbitrary fixed cutoff
`U`, the mass is bounded by the `M`-th power of the double base-four
logarithm.  Divergence supplies arbitrarily late square-root-scale density
spikes.  At such a spike the prefix product has double logarithm only linear
in the shell exponent, while the number of its prescribed divisors is
exponential in that exponent. -/
theorem tailUnbounded_ratioNat_of_iteratedLog_growth
    (A : Set ℕ) (k M U : ℕ)
    (hdiv : tailUnbounded (reciprocalMassNat A))
    (hgrowth : ∀ u : ℕ, U ≤ u →
      reciprocalMassNat A u ≤ (Nat.log 4 (Nat.log 4 u) : ℝ) ^ M) :
    tailUnbounded (ratioNat A k) := by
  intro C X
  by_cases hC : C < 0
  · exact ⟨X, le_rfl, hC.trans_le (ratioNat_nonneg A k X)⟩
  have hC0 : 0 ≤ C := le_of_not_gt hC
  have hdomEventually := eventually_const_mul_two_mul_add_pow_lt_two_pow C (M * k)
  rw [Filter.eventually_atTop] at hdomEventually
  obtain ⟨Jdom, hdom⟩ := hdomEventually
  let X₀ := max X U
  let J₀ := max 1 (max Jdom (Nat.log 4 X₀ + 1))
  obtain ⟨j, hJj, hjcard⟩ :=
    arbitrarily_large_prefixCardNat_four_pow_gt_two_pow A hdiv J₀
  have hj : 1 ≤ j := (le_max_left 1 (max Jdom (Nat.log 4 X₀ + 1))).trans hJj
  have hJdomj : Jdom ≤ j :=
    (le_max_left Jdom (Nat.log 4 X₀ + 1)).trans
      ((le_max_right 1 (max Jdom (Nat.log 4 X₀ + 1))).trans hJj)
  have hlogXj : Nat.log 4 X₀ + 1 ≤ j :=
    (le_max_right Jdom (Nat.log 4 X₀ + 1)).trans
      ((le_max_right 1 (max Jdom (Nat.log 4 X₀ + 1))).trans hJj)
  have hX₀pow : X₀ ≤ 4 ^ j := by
    exact (Nat.lt_pow_succ_log_self (by norm_num) X₀).le.trans
      (Nat.pow_le_pow_right (by norm_num) hlogXj)
  let x := max X₀ (prefixProductNat A (4 ^ j) + 1)
  refine ⟨x, (le_max_left X U).trans (le_max_left X₀ _), ?_⟩
  have hUx : U ≤ x := (le_max_right X U).trans (le_max_left X₀ _)
  have hlog : Nat.log 4 (Nat.log 4 x) ≤ 2 * j + 2 := by
    exact iteratedLog_four_prefixProductCutoff_le A hj hX₀pow
  have hmass : reciprocalMassNat A x ≤ (2 * (j : ℝ) + 2) ^ M := by
    calc
      reciprocalMassNat A x ≤ (Nat.log 4 (Nat.log 4 x) : ℝ) ^ M :=
        hgrowth x hUx
      _ ≤ ((2 * j + 2 : ℕ) : ℝ) ^ M := by
        apply pow_le_pow_left₀ (Nat.cast_nonneg _) _ M
        exact_mod_cast hlog
      _ = (2 * (j : ℝ) + 2) ^ M := by norm_num
  have hmassPow : reciprocalMassNat A x ^ k ≤
      (2 * (j : ℝ) + 2) ^ (M * k) := by
    calc
      reciprocalMassNat A x ^ k ≤ ((2 * (j : ℝ) + 2) ^ M) ^ k :=
        pow_le_pow_left₀ (reciprocalMassNat_nonneg A x) hmass k
      _ = (2 * (j : ℝ) + 2) ^ (M * k) := by rw [pow_mul]
  have hdomj : C * (2 * (j : ℝ) + 2) ^ (M * k) < (2 : ℝ) ^ j :=
    hdom j hJdomj
  have hcardReal : (2 : ℝ) ^ j < prefixCardNat A (4 ^ j) := by
    exact_mod_cast hjcard
  have hcardpos : 0 < prefixCardNat A (4 ^ j) :=
    (Nat.pow_pos (by norm_num : 0 < 2)).trans hjcard
  have hmasspos : 0 < reciprocalMassNat A x := by
    obtain ⟨a, ha⟩ := Finset.card_pos.mp hcardpos
    have ha' := mem_prefixMembersNat_iff.mp ha
    have hp : 0 < prefixProductNat A (4 ^ j) :=
      Nat.pos_of_ne_zero (prefixProductNat_ne_zero A (4 ^ j))
    have hadiv : a ∣ prefixProductNat A (4 ^ j) := by
      unfold prefixProductNat
      exact Finset.dvd_prod_of_mem id ha
    have hap : a ≤ prefixProductNat A (4 ^ j) := Nat.le_of_dvd hp hadiv
    have hax : a < x := hap.trans_lt <|
      (Nat.lt_succ_self _).trans_le (le_max_right X₀ _)
    exact reciprocalMassNat_pos_of_mem ha'.2.2 (lt_of_lt_of_le Nat.zero_lt_one ha'.1) hax
  have hdenpos : 0 < reciprocalMassNat A x ^ k := pow_pos hmasspos k
  have hnumerator : C * reciprocalMassNat A x ^ k <
      (prefixCardNat A (4 ^ j) : ℝ) :=
    (mul_le_mul_of_nonneg_left hmassPow hC0).trans_lt (hdomj.trans hcardReal)
  have hweight : C < (prefixCardNat A (4 ^ j) : ℝ) /
      reciprocalMassNat A x ^ k := (lt_div_iff₀ hdenpos).mpr hnumerator
  exact hweight.trans_le (prefixProduct_weight_le_ratioNat A k (4 ^ j) X₀)

/-- Ordinary unboundedness-above formulation of the low-growth branch. -/
theorem tailUnbounded_ratioNat_of_iteratedLog_growth_of_unbounded
    (A : Set ℕ) (k M U : ℕ)
    (hdiv : ∀ C : ℝ, ∃ x : ℕ, C < reciprocalMassNat A x)
    (hgrowth : ∀ u : ℕ, U ≤ u →
      reciprocalMassNat A u ≤ (Nat.log 4 (Nat.log 4 u) : ℝ) ^ M) :
    tailUnbounded (ratioNat A k) :=
  tailUnbounded_ratioNat_of_iteratedLog_growth A k M U
    (tailUnbounded_reciprocalMassNat_of_unbounded A hdiv) hgrowth

/-- Constant-factor and shifted version of the low-growth branch.

This is the form naturally produced by an asymptotic dichotomy: an arbitrary
nonnegative constant multiplies a fixed power of `log log + 1`. -/
theorem tailUnbounded_ratioNat_of_shifted_iteratedLog_growth
    (A : Set ℕ) (k M : ℕ) (D : ℝ) (U : ℕ) (hD : 0 ≤ D)
    (hdiv : tailUnbounded (reciprocalMassNat A))
    (hgrowth : ∀ u : ℕ, U ≤ u → reciprocalMassNat A u ≤
      D * ((Nat.log 4 (Nat.log 4 u) : ℝ) + 1) ^ M) :
    tailUnbounded (ratioNat A k) := by
  intro C X
  by_cases hC : C < 0
  · exact ⟨X, le_rfl, hC.trans_le (ratioNat_nonneg A k X)⟩
  have hC0 : 0 ≤ C := le_of_not_gt hC
  let d := M * k
  let E := C * D ^ k * 2 ^ d
  have hdomEventually := eventually_const_mul_two_mul_add_pow_lt_two_pow E d
  rw [Filter.eventually_atTop] at hdomEventually
  obtain ⟨Jdom, hdom⟩ := hdomEventually
  let X₀ := max X U
  let J₀ := max 1 (max Jdom (Nat.log 4 X₀ + 1))
  obtain ⟨j, hJj, hjcard⟩ :=
    arbitrarily_large_prefixCardNat_four_pow_gt_two_pow A hdiv J₀
  have hj : 1 ≤ j := (le_max_left 1 (max Jdom (Nat.log 4 X₀ + 1))).trans hJj
  have hJdomj : Jdom ≤ j :=
    (le_max_left Jdom (Nat.log 4 X₀ + 1)).trans
      ((le_max_right 1 (max Jdom (Nat.log 4 X₀ + 1))).trans hJj)
  have hlogXj : Nat.log 4 X₀ + 1 ≤ j :=
    (le_max_right Jdom (Nat.log 4 X₀ + 1)).trans
      ((le_max_right 1 (max Jdom (Nat.log 4 X₀ + 1))).trans hJj)
  have hX₀pow : X₀ ≤ 4 ^ j := by
    exact (Nat.lt_pow_succ_log_self (by norm_num) X₀).le.trans
      (Nat.pow_le_pow_right (by norm_num) hlogXj)
  let x := max X₀ (prefixProductNat A (4 ^ j) + 1)
  refine ⟨x, (le_max_left X U).trans (le_max_left X₀ _), ?_⟩
  have hUx : U ≤ x := (le_max_right X U).trans (le_max_left X₀ _)
  have hlog : Nat.log 4 (Nat.log 4 x) ≤ 2 * j + 2 :=
    iteratedLog_four_prefixProductCutoff_le A hj hX₀pow
  have hmass : reciprocalMassNat A x ≤ D * (2 * (j : ℝ) + 3) ^ M := by
    calc
      reciprocalMassNat A x ≤
          D * ((Nat.log 4 (Nat.log 4 x) : ℝ) + 1) ^ M := hgrowth x hUx
      _ ≤ D * (((2 * j + 2 : ℕ) : ℝ) + 1) ^ M := by
        gcongr
      _ = D * (2 * (j : ℝ) + 3) ^ M := by
        congr 2
        norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
        ring
  have hmassPow : reciprocalMassNat A x ^ k ≤
      D ^ k * 2 ^ d * (2 * (j : ℝ) + 2) ^ d := by
    have haffine : 2 * (j : ℝ) + 3 ≤ 2 * (2 * (j : ℝ) + 2) := by
      have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
      linarith
    calc
      reciprocalMassNat A x ^ k
          ≤ (D * (2 * (j : ℝ) + 3) ^ M) ^ k :=
        pow_le_pow_left₀ (reciprocalMassNat_nonneg A x) hmass k
      _ = D ^ k * (2 * (j : ℝ) + 3) ^ d := by
        simp only [mul_pow, d, pow_mul]
      _ ≤ D ^ k * (2 * (2 * (j : ℝ) + 2)) ^ d := by
        gcongr
      _ = D ^ k * 2 ^ d * (2 * (j : ℝ) + 2) ^ d := by
        rw [mul_pow]
        ring
  have hdomj : E * (2 * (j : ℝ) + 2) ^ d < (2 : ℝ) ^ j := hdom j hJdomj
  have hscaledDom :
      C * (D ^ k * 2 ^ d * (2 * (j : ℝ) + 2) ^ d) < (2 : ℝ) ^ j := by
    simpa [E, mul_assoc] using hdomj
  have hcardReal : (2 : ℝ) ^ j < prefixCardNat A (4 ^ j) := by
    exact_mod_cast hjcard
  have hcardpos : 0 < prefixCardNat A (4 ^ j) :=
    (Nat.pow_pos (by norm_num : 0 < 2)).trans hjcard
  have hmasspos : 0 < reciprocalMassNat A x := by
    obtain ⟨a, ha⟩ := Finset.card_pos.mp hcardpos
    have ha' := mem_prefixMembersNat_iff.mp ha
    have hp : 0 < prefixProductNat A (4 ^ j) :=
      Nat.pos_of_ne_zero (prefixProductNat_ne_zero A (4 ^ j))
    have hadiv : a ∣ prefixProductNat A (4 ^ j) := by
      unfold prefixProductNat
      exact Finset.dvd_prod_of_mem id ha
    have hap : a ≤ prefixProductNat A (4 ^ j) := Nat.le_of_dvd hp hadiv
    have hax : a < x := hap.trans_lt <|
      (Nat.lt_succ_self _).trans_le (le_max_right X₀ _)
    exact reciprocalMassNat_pos_of_mem ha'.2.2 (lt_of_lt_of_le Nat.zero_lt_one ha'.1) hax
  have hdenpos : 0 < reciprocalMassNat A x ^ k := pow_pos hmasspos k
  have hnumerator : C * reciprocalMassNat A x ^ k <
      (prefixCardNat A (4 ^ j) : ℝ) :=
    (mul_le_mul_of_nonneg_left hmassPow hC0).trans_lt
      (hscaledDom.trans hcardReal)
  have hweight : C < (prefixCardNat A (4 ^ j) : ℝ) /
      reciprocalMassNat A x ^ k := (lt_div_iff₀ hdenpos).mpr hnumerator
  exact hweight.trans_le (prefixProduct_weight_le_ratioNat A k (4 ^ j) X₀)

/-- Existential wrapper for the constant-factor shifted low-growth branch. -/
theorem tailUnbounded_ratioNat_of_exists_shifted_iteratedLog_growth
    (A : Set ℕ) (k M : ℕ)
    (hdiv : tailUnbounded (reciprocalMassNat A))
    (hgrowth : ∃ D : ℝ, 0 ≤ D ∧ ∃ U : ℕ, ∀ u : ℕ, U ≤ u →
      reciprocalMassNat A u ≤
        D * ((Nat.log 4 (Nat.log 4 u) : ℝ) + 1) ^ M) :
    tailUnbounded (ratioNat A k) := by
  obtain ⟨D, hD, U, hU⟩ := hgrowth
  exact tailUnbounded_ratioNat_of_shifted_iteratedLog_growth A k M D U hD hdiv hU

end Erdos444
