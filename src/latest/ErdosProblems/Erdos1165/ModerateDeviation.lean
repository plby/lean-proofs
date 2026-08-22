/-
Copyright (c) 2026 The Erdos Problems Formalization Project.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Erdos Problems Formalization Project
-/
module

public import ErdosProblems.Erdos1165.NegativeBinomial

@[expose] public section

/-!
# Chernoff bounds for the geometric sums in Erdős Problem 1165

The lazy-local-time decomposition of Hao--Li--Okada--Zheng produces sums of
independent geometric random variables with success probability `15 / 16`.
Their sum has the negative-binomial mass `NegativeBinomial.hlozMass` developed
in `ErdosProblems.Erdos1165.NegativeBinomial`.

This file proves, directly from the negative-binomial generating series:

* the exact exponential moment of that mass;
* a Chernoff upper-tail estimate at every admissible exponential parameter;
* the optimized Cramér exponent for an upper deviation; and
* a quadratic lower bound for that exponent in the moderate range where the
  excess is at most the mean.

No probabilistic limit theorem is used here.  In particular, all the results
are finite-scale inequalities for explicit convergent series.
-/

open scoped ENNReal NNReal
open Filter MeasureTheory ProbabilityTheory Real Topology

namespace Erdos1165.ModerateDeviation

open NegativeBinomial

/-- The real upper-tail mass of the HLOZ negative-binomial law. -/
noncomputable def upperTailMass (i k : ℕ) : ℝ :=
  ∑' j : ℕ, if k ≤ j then hlozMass i j else 0

/-- The real lower-tail mass of the HLOZ negative-binomial law. -/
noncomputable def lowerTailMass (i k : ℕ) : ℝ :=
  ∑' j : ℕ, if j ≤ k then hlozMass i j else 0

/-- The moment generating series of a negative-binomial mass. -/
lemma hasSum_exp_mul_mass {p t : ℝ} {i : ℕ} (hi : 0 < i)
    (ht : ‖(1 - p) * Real.exp t‖ < 1) :
    HasSum (fun j : ℕ ↦ Real.exp (t * j) * mass p i j)
      ((p / (1 - (1 - p) * Real.exp t)) ^ i) := by
  have h := (hasSum_coefficient_mul_pow (r := (1 - p) * Real.exp t) ht hi).mul_left
    (p ^ i)
  have heq :
      (fun j : ℕ ↦ Real.exp (t * j) * mass p i j) =
        (fun j : ℕ ↦ p ^ i *
          ((coefficient i j : ℝ) * ((1 - p) * Real.exp t) ^ j)) := by
    funext j
    rw [mass, mul_pow, ← Real.exp_nat_mul]
    ring_nf
  rw [heq]
  convert h using 1
  · rfl
  · rw [div_pow]
    ring

/-- The exponential moment at HLOZ's parameter `p = 15 / 16`. -/
lemma hasSum_exp_mul_hlozMass {i : ℕ} (hi : 0 < i) {t : ℝ}
    (ht : Real.exp t < 16) :
    HasSum (fun j : ℕ ↦ Real.exp (t * j) * hlozMass i j)
      (((15 : ℝ) / (16 - Real.exp t)) ^ i) := by
  have hnorm : ‖(1 - hlozSuccess) * Real.exp t‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg]
    · norm_num [hlozSuccess] at ⊢
      linarith
    · exact mul_nonneg (by norm_num [hlozSuccess]) (Real.exp_nonneg t)
  have h := hasSum_exp_mul_mass (p := hlozSuccess) (t := t)
    hi hnorm
  have hvalue :
      (hlozSuccess / (1 - (1 - hlozSuccess) * Real.exp t)) ^ i =
        ((15 : ℝ) / (16 - Real.exp t)) ^ i := by
    congr 1
    norm_num [hlozSuccess]
    field_simp
  rw [hvalue] at h
  simpa only [hlozMass] using h

lemma summable_exp_mul_hlozMass {i : ℕ} (hi : 0 < i) {t : ℝ}
    (ht : Real.exp t < 16) :
    Summable (fun j : ℕ ↦ Real.exp (t * j) * hlozMass i j) :=
  (hasSum_exp_mul_hlozMass hi ht).summable

lemma tsum_exp_mul_hlozMass {i : ℕ} (hi : 0 < i) {t : ℝ}
    (ht : Real.exp t < 16) :
    ∑' j : ℕ, Real.exp (t * j) * hlozMass i j =
      ((15 : ℝ) / (16 - Real.exp t)) ^ i :=
  (hasSum_exp_mul_hlozMass hi ht).tsum_eq

lemma summable_upperTailMass {i k : ℕ} (hi : 0 < i) :
    Summable (fun j : ℕ ↦ if k ≤ j then hlozMass i j else 0) := by
  apply Summable.of_nonneg_of_le
  · intro j
    split_ifs
    · exact hlozMass_nonneg i j
    · exact le_rfl
  · intro j
    split_ifs
    · exact le_rfl
    · exact hlozMass_nonneg i j
  · exact (hasSum_hlozMass hi).summable

lemma upperTailMass_nonneg (i k : ℕ) : 0 ≤ upperTailMass i k := by
  apply tsum_nonneg
  intro j
  split_ifs
  · exact hlozMass_nonneg i j
  · exact le_rfl

lemma upperTailMass_le_one {i k : ℕ} (hi : 0 < i) : upperTailMass i k ≤ 1 := by
  have hsum := Summable.tsum_le_tsum
    (f := fun j : ℕ ↦ if k ≤ j then hlozMass i j else 0)
    (g := hlozMass i)
    (fun j ↦ by split_ifs <;> simp only [le_refl, hlozMass_nonneg])
    (summable_upperTailMass hi) (hasSum_hlozMass hi).summable
  simpa only [upperTailMass, tsum_hlozMass hi] using hsum

/-- Chernoff's inequality for the HLOZ negative-binomial upper tail. -/
lemma upperTailMass_le_chernoff {i k : ℕ} (hi : 0 < i) {t : ℝ}
    (ht0 : 0 ≤ t) (ht16 : Real.exp t < 16) :
    upperTailMass i k ≤
      Real.exp (-t * k) * ((15 : ℝ) / (16 - Real.exp t)) ^ i := by
  let f : ℕ → ℝ := fun j ↦ if k ≤ j then hlozMass i j else 0
  let g : ℕ → ℝ := fun j ↦
    Real.exp (-t * k) * (Real.exp (t * j) * hlozMass i j)
  have hfg : ∀ j, f j ≤ g j := by
    intro j
    dsimp only [f, g]
    split_ifs with hkj
    · have hexp : 1 ≤ Real.exp (-t * k) * Real.exp (t * j) := by
        rw [← Real.exp_add, ← Real.exp_zero]
        apply Real.exp_le_exp.mpr
        have hkjR : (k : ℝ) ≤ (j : ℝ) := by exact_mod_cast hkj
        nlinarith
      calc
        hlozMass i j = 1 * hlozMass i j := by ring
        _ ≤ (Real.exp (-t * k) * Real.exp (t * j)) * hlozMass i j :=
          mul_le_mul_of_nonneg_right hexp (hlozMass_nonneg i j)
        _ = Real.exp (-t * k) * (Real.exp (t * j) * hlozMass i j) := by ring
    · exact mul_nonneg (Real.exp_nonneg _) <|
        mul_nonneg (Real.exp_nonneg _) (hlozMass_nonneg i j)
  have hf : Summable f := by
    simpa only [f] using summable_upperTailMass (i := i) (k := k) hi
  have hg : Summable g := by
    exact (summable_exp_mul_hlozMass hi ht16).mul_left (Real.exp (-t * k))
  have hsum := Summable.tsum_le_tsum hfg hf hg
  rw [show upperTailMass i k = ∑' j, f j by rfl]
  refine hsum.trans_eq ?_
  rw [show (∑' j, g j) = Real.exp (-t * k) *
      ∑' j : ℕ, Real.exp (t * j) * hlozMass i j by
        exact tsum_mul_left]
  rw [tsum_exp_mul_hlozMass hi ht16]

lemma summable_lowerTailMass {i k : ℕ} (hi : 0 < i) :
    Summable (fun j : ℕ ↦ if j ≤ k then hlozMass i j else 0) := by
  apply Summable.of_nonneg_of_le
  · intro j
    split_ifs
    · exact hlozMass_nonneg i j
    · exact le_rfl
  · intro j
    split_ifs
    · exact le_rfl
    · exact hlozMass_nonneg i j
  · exact (hasSum_hlozMass hi).summable

lemma lowerTailMass_nonneg (i k : ℕ) : 0 ≤ lowerTailMass i k := by
  apply tsum_nonneg
  intro j
  split_ifs
  · exact hlozMass_nonneg i j
  · exact le_rfl

lemma lowerTailMass_zero (i : ℕ) :
    lowerTailMass i 0 = ((15 : ℝ) / 16) ^ i := by
  rw [lowerTailMass]
  have hsingle :
      (∑' j : ℕ, if j ≤ 0 then hlozMass i j else 0) = hlozMass i 0 := by
    simpa only [Nat.le_zero] using (tsum_ite_eq 0 (hlozMass i))
  rw [hsingle]
  simp [hlozMass, mass_zero, hlozSuccess]

lemma lowerTailMass_le_one {i k : ℕ} (hi : 0 < i) : lowerTailMass i k ≤ 1 := by
  have hsum := Summable.tsum_le_tsum
    (f := fun j : ℕ ↦ if j ≤ k then hlozMass i j else 0)
    (g := hlozMass i)
    (fun j ↦ by split_ifs <;> simp only [le_refl, hlozMass_nonneg])
    (summable_lowerTailMass hi) (hasSum_hlozMass hi).summable
  simpa only [lowerTailMass, tsum_hlozMass hi] using hsum

/-- The lower-tail form of Chernoff's inequality. -/
lemma lowerTailMass_le_chernoff {i k : ℕ} (hi : 0 < i) {t : ℝ}
    (ht0 : t ≤ 0) (ht16 : Real.exp t < 16) :
    lowerTailMass i k ≤
      Real.exp (-t * k) * ((15 : ℝ) / (16 - Real.exp t)) ^ i := by
  let f : ℕ → ℝ := fun j ↦ if j ≤ k then hlozMass i j else 0
  let g : ℕ → ℝ := fun j ↦
    Real.exp (-t * k) * (Real.exp (t * j) * hlozMass i j)
  have hfg : ∀ j, f j ≤ g j := by
    intro j
    dsimp only [f, g]
    split_ifs with hjk
    · have hexp : 1 ≤ Real.exp (-t * k) * Real.exp (t * j) := by
        rw [← Real.exp_add, ← Real.exp_zero]
        apply Real.exp_le_exp.mpr
        have hjkR : (j : ℝ) ≤ (k : ℝ) := by exact_mod_cast hjk
        nlinarith
      calc
        hlozMass i j = 1 * hlozMass i j := by ring
        _ ≤ (Real.exp (-t * k) * Real.exp (t * j)) * hlozMass i j :=
          mul_le_mul_of_nonneg_right hexp (hlozMass_nonneg i j)
        _ = Real.exp (-t * k) * (Real.exp (t * j) * hlozMass i j) := by ring
    · exact mul_nonneg (Real.exp_nonneg _) <|
        mul_nonneg (Real.exp_nonneg _) (hlozMass_nonneg i j)
  have hf : Summable f := by
    simpa only [f] using summable_lowerTailMass (i := i) (k := k) hi
  have hg : Summable g := by
    exact (summable_exp_mul_hlozMass hi ht16).mul_left (Real.exp (-t * k))
  have hsum := Summable.tsum_le_tsum hfg hf hg
  rw [show lowerTailMass i k = ∑' j, f j by rfl]
  refine hsum.trans_eq ?_
  rw [show (∑' j, g j) = Real.exp (-t * k) *
      ∑' j : ℕ, Real.exp (t * j) * hlozMass i j by
        exact tsum_mul_left]
  rw [tsum_exp_mul_hlozMass hi ht16]

/-- The Cramér rate for an upper deviation of the HLOZ geometric sum. -/
noncomputable def upperRate (i k : ℕ) : ℝ :=
  (k : ℝ) * Real.log (16 * (k : ℝ) / (i + k : ℕ)) -
    (i : ℝ) * Real.log (15 * (i + k : ℕ) / (16 * (i : ℝ)))

/-- The optimized Chernoff bound.  The condition `i < 15 k` says that `k`
lies strictly above the mean `i / 15`. -/
lemma upperTailMass_le_exp_neg_upperRate {i k : ℕ} (hi : 0 < i)
    (hk : i < 15 * k) :
    upperTailMass i k ≤ Real.exp (-upperRate i k) := by
  let t : ℝ := Real.log (16 * (k : ℝ) / (i + k : ℕ))
  have hk0 : 0 < k := by omega
  have hik0 : 0 < (i + k : ℕ) := by omega
  have hratio0 : 0 < 16 * (k : ℝ) / (i + k : ℕ) := by positivity
  have hratio1 : 1 < 16 * (k : ℝ) / (i + k : ℕ) := by
    rw [one_lt_div (by positivity)]
    have hik : i + k < 16 * k := by omega
    exact_mod_cast hik
  have ht0 : 0 ≤ t := (Real.log_nonneg hratio1.le)
  have hexpt : Real.exp t = 16 * (k : ℝ) / (i + k : ℕ) := by
    exact Real.exp_log hratio0
  have ht16 : Real.exp t < 16 := by
    rw [hexpt, div_lt_iff₀ (by positivity)]
    push_cast
    nlinarith [show (0 : ℝ) < i by exact_mod_cast hi]
  have hchern := upperTailMass_le_chernoff (i := i) (k := k) hi ht0 ht16
  have hden : 16 - Real.exp t = 16 * (i : ℝ) / (i + k : ℕ) := by
    rw [hexpt]
    field_simp
    push_cast
    ring
  have hbase0 : 0 < 15 * ((i + k : ℕ) : ℝ) / (16 * (i : ℝ)) := by positivity
  have hvalue :
      Real.exp (-t * k) * ((15 : ℝ) / (16 - Real.exp t)) ^ i =
        Real.exp (-upperRate i k) := by
    rw [hden]
    have hbase : (15 : ℝ) / (16 * (i : ℝ) / (i + k : ℕ)) =
        15 * ((i + k : ℕ) : ℝ) / (16 * (i : ℝ)) := by
      field_simp
    rw [hbase]
    rw [← Real.exp_log hbase0, ← Real.exp_nat_mul]
    rw [← Real.exp_add]
    congr 1
    dsimp only [t, upperRate]
    push_cast
    ring
  rw [hvalue] at hchern
  exact hchern

/-- The same optimized Cramér exponent controls the lower tail below the
mean.  The harmless condition `0 < k` excludes the endpoint, whose optimizer
is reached only as `t → -∞`. -/
lemma lowerTailMass_le_exp_neg_upperRate {i k : ℕ} (hi : 0 < i) (hk0 : 0 < k)
    (hk : 15 * k < i) :
    lowerTailMass i k ≤ Real.exp (-upperRate i k) := by
  let t : ℝ := Real.log (16 * (k : ℝ) / (i + k : ℕ))
  have hik0 : 0 < (i + k : ℕ) := by omega
  have hratio0 : 0 < 16 * (k : ℝ) / (i + k : ℕ) := by positivity
  have hratio1 : 16 * (k : ℝ) / (i + k : ℕ) < 1 := by
    rw [div_lt_one (by positivity)]
    have hik : 16 * k < i + k := by omega
    exact_mod_cast hik
  have ht0 : t ≤ 0 := (Real.log_nonpos hratio0.le hratio1.le)
  have hexpt : Real.exp t = 16 * (k : ℝ) / (i + k : ℕ) := by
    exact Real.exp_log hratio0
  have ht16 : Real.exp t < 16 := by linarith
  have hchern := lowerTailMass_le_chernoff (i := i) (k := k) hi ht0 ht16
  have hden : 16 - Real.exp t = 16 * (i : ℝ) / (i + k : ℕ) := by
    rw [hexpt]
    field_simp
    push_cast
    ring
  have hbase0 : 0 < 15 * ((i + k : ℕ) : ℝ) / (16 * (i : ℝ)) := by positivity
  have hvalue :
      Real.exp (-t * k) * ((15 : ℝ) / (16 - Real.exp t)) ^ i =
        Real.exp (-upperRate i k) := by
    rw [hden]
    have hbase : (15 : ℝ) / (16 * (i : ℝ) / (i + k : ℕ)) =
        15 * ((i + k : ℕ) : ℝ) / (16 * (i : ℝ)) := by
      field_simp
    rw [hbase]
    rw [← Real.exp_log hbase0, ← Real.exp_nat_mul]
    rw [← Real.exp_add]
    congr 1
    dsimp only [t, upperRate]
    push_cast
    ring
  rw [hvalue] at hchern
  exact hchern

/-- Relative excess over the mean: `relativeExcess i k = 15 k / i - 1`. -/
noncomputable def relativeExcess (i k : ℕ) : ℝ :=
  15 * (k : ℝ) / (i : ℝ) - 1

/-- The normalized Cramér rate written in terms of relative excess. -/
noncomputable def normalizedUpperRate (u : ℝ) : ℝ :=
  (1 + u) / 15 * Real.log (1 + u) -
    (16 + u) / 15 * Real.log (1 + u / 16)

/-- The exact rate is `i` times the normalized rate of the relative excess. -/
lemma upperRate_eq_normalized {i k : ℕ} (hi : 0 < i) (hk : 0 < k) :
    upperRate i k = (i : ℝ) * normalizedUpperRate (relativeExcess i k) := by
  have hiR : (0 : ℝ) < i := by exact_mod_cast hi
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hikR : (0 : ℝ) < (i + k : ℕ) := by positivity
  have hscaledSum : (0 : ℝ) < (i : ℝ) * 15 + (k : ℝ) * 15 := by positivity
  have harg2 :
      15 * ((i + k : ℕ) : ℝ) / (16 * (i : ℝ)) =
        1 + relativeExcess i k / 16 := by
    dsimp only [relativeExcess]
    push_cast
    field_simp
    ring
  have harg1 :
      16 * (k : ℝ) / (i + k : ℕ) =
        (1 + relativeExcess i k) / (1 + relativeExcess i k / 16) := by
    have hnum : 1 + relativeExcess i k = 15 * (k : ℝ) / (i : ℝ) := by
      dsimp only [relativeExcess]
      ring
    rw [hnum, ← harg2]
    field_simp [hiR.ne', hikR.ne']
  rw [upperRate, harg1, harg2]
  have hu1 : 0 < 1 + relativeExcess i k := by
    dsimp only [relativeExcess]
    have : 0 < 15 * (k : ℝ) / (i : ℝ) := by positivity
    linarith
  have hu16 : 0 < 1 + relativeExcess i k / 16 := by
    dsimp only [relativeExcess]
    have : 0 ≤ 15 * (k : ℝ) / (i : ℝ) := by positivity
    nlinarith
  rw [Real.log_div hu1.ne' hu16.ne']
  dsimp only [normalizedUpperRate, relativeExcess]
  field_simp
  ring

/-- Quadratic lower bound for the normalized rate in the moderate range.

The constant `1 / 60` is deliberately non-sharp; the Taylor coefficient at
zero is `1 / 32`.  The weaker rational constant keeps the proof elementary
and is uniform throughout `0 ≤ u ≤ 1`. -/
lemma normalizedUpperRate_ge_sq_div_sixty {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    u ^ 2 / 60 ≤ normalizedUpperRate u := by
  have hlog1 := Real.le_log_one_add_of_nonneg hu0
  have hpos16 : 0 < 1 + u / 16 := by nlinarith
  have hlog16 : Real.log (1 + u / 16) ≤ u / 16 := by
    have h := Real.log_le_sub_one_of_pos hpos16
    linarith
  have hcoef1 : 0 ≤ (1 + u) / 15 := by positivity
  have hcoef16 : 0 ≤ (16 + u) / 15 := by positivity
  have hmul1 :
      (1 + u) / 15 * (2 * u / (u + 2)) ≤
        (1 + u) / 15 * Real.log (1 + u) :=
    mul_le_mul_of_nonneg_left hlog1 hcoef1
  have hmul16 :
      (16 + u) / 15 * Real.log (1 + u / 16) ≤
        (16 + u) / 15 * (u / 16) :=
    mul_le_mul_of_nonneg_left hlog16 hcoef16
  have hform :
      (1 + u) / 15 * (2 * u / (u + 2)) - (16 + u) / 15 * (u / 16) =
        u ^ 2 * (14 - u) / (240 * (u + 2)) := by
    field_simp
    ring
  have hden : 0 < 240 * (u + 2) := by positivity
  have hquad : u ^ 2 / 60 ≤ u ^ 2 * (14 - u) / (240 * (u + 2)) := by
    rw [le_div_iff₀ hden]
    nlinarith [sq_nonneg u]
  rw [normalizedUpperRate]
  calc
    u ^ 2 / 60 ≤ u ^ 2 * (14 - u) / (240 * (u + 2)) := hquad
    _ = (1 + u) / 15 * (2 * u / (u + 2)) - (16 + u) / 15 * (u / 16) :=
      hform.symm
    _ ≤ (1 + u) / 15 * Real.log (1 + u) -
        (16 + u) / 15 * Real.log (1 + u / 16) := sub_le_sub hmul1 hmul16

/-- Moderate-deviation lower bound for the exact lattice rate. -/
lemma upperRate_ge_relativeExcess_sq {i k : ℕ} (hi : 0 < i)
    (habove : i ≤ 15 * k) (hbelow : 15 * k ≤ 2 * i) :
    (i : ℝ) * relativeExcess i k ^ 2 / 60 ≤ upperRate i k := by
  have hiR : (0 : ℝ) < i := by exact_mod_cast hi
  have hk : 0 < k := by omega
  have haboveR : (i : ℝ) ≤ 15 * (k : ℝ) := by exact_mod_cast habove
  have hbelowR : 15 * (k : ℝ) ≤ 2 * (i : ℝ) := by exact_mod_cast hbelow
  have hu0 : 0 ≤ relativeExcess i k := by
    rw [relativeExcess, sub_nonneg, one_le_div hiR]
    exact haboveR
  have hu1 : relativeExcess i k ≤ 1 := by
    rw [relativeExcess, sub_le_iff_le_add]
    rw [div_le_iff₀ hiR]
    nlinarith
  have hrate := normalizedUpperRate_ge_sq_div_sixty hu0 hu1
  have hmul := mul_le_mul_of_nonneg_left hrate hiR.le
  calc
    (i : ℝ) * relativeExcess i k ^ 2 / 60 =
        (i : ℝ) * (relativeExcess i k ^ 2 / 60) := by ring
    _ ≤ (i : ℝ) * normalizedUpperRate (relativeExcess i k) := hmul
    _ = upperRate i k := (upperRate_eq_normalized hi hk).symm

/-- Fully explicit moderate-deviation tail estimate. -/
lemma upperTailMass_le_exp_neg_quadratic {i k : ℕ} (hi : 0 < i)
    (habove : i < 15 * k) (hbelow : 15 * k ≤ 2 * i) :
    upperTailMass i k ≤
      Real.exp (-((i : ℝ) * relativeExcess i k ^ 2 / 60)) := by
  have htail := upperTailMass_le_exp_neg_upperRate hi habove
  have hrate := upperRate_ge_relativeExcess_sq hi habove.le hbelow
  exact htail.trans (Real.exp_le_exp.mpr (neg_le_neg hrate))

/-- The quadratic estimate with the relative excess expanded.  Its exponent
is a fixed rational multiple of the usual squared deviation divided by the
number of summands. -/
lemma upperTailMass_le_exp_neg_sq_deviation {i k : ℕ} (hi : 0 < i)
    (habove : i < 15 * k) (hbelow : 15 * k ≤ 2 * i) :
    upperTailMass i k ≤
      Real.exp (-((15 * (k : ℝ) - (i : ℝ)) ^ 2 / (60 * (i : ℝ)))) := by
  have htail := upperTailMass_le_exp_neg_quadratic hi habove hbelow
  have hiR : (i : ℝ) ≠ 0 := by exact_mod_cast hi.ne'
  convert htail using 1
  congr 2
  rw [relativeExcess]
  field_simp [hiR]

end Erdos1165.ModerateDeviation
