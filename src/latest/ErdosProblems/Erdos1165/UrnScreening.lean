/-
Copyright (c) 2026 The Erdos Problems Formalization Project.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Erdos Problems Formalization Project
-/
module

public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Data.Nat.Choose.Bounds
public import Mathlib.Probability.Distributions.Binomial

@[expose] public section

/-!
# Finite urn screening estimates for Erdős Problem 1165

The two screening steps in Hao--Li--Okada--Zheng reduce, after conditioning on
the external walk, to elementary statements about finitely many independent
balls.  This file records those statements using Mathlib's binomial probability
measure.

* `adjacent_urn_screening` is the adjacent-strip estimate used in Proposition
  4.8.  If the mass `p` of the lower strip is at most `C` times the mass `q` of
  the next strip, then the conditional probability that all `h` balls fall in
  the lower strip is at most `exp (-h / (1 + C))`.
* `two_window_urn_screening` is the finite-window estimate used in Proposition
  4.9.  If at most `J` balls are candidates and the conditional chance of the
  upper window is at most `C g / f`, the chance of exactly `j` selected balls
  is at most `(C g J / f)^j`.  The case `j = 1`, together with the union bound
  `binomial_one_or_more_le`, gives the required `C g J / f` estimate.

There are no asymptotic hypotheses in this module: all constants and finite
sample sizes occur explicitly in the conclusions.
-/

open MeasureTheory Set
open scoped ENNReal ProbabilityTheory unitInterval

namespace Erdos1165.UrnScreening

/-! ## Conditioning two adjacent urns -/

/-- Conditional success parameter after retaining only two urns of respective
weights `p` and `q`. -/
noncomputable def pairParameter (p q : ℝ) (hp : 0 ≤ p) (hq : 0 ≤ q)
    (hpq : 0 < p + q) : I :=
  ⟨p / (p + q), by
    constructor
    · exact div_nonneg hp hpq.le
    · rw [div_le_one hpq]
      linarith⟩

@[simp] lemma coe_pairParameter (p q : ℝ) (hp : 0 ≤ p) (hq : 0 ≤ q)
    (hpq : 0 < p + q) :
    ((pairParameter p q hp hq hpq : I) : ℝ) = p / (p + q) := rfl

/-- A comparison `p ≤ C q` becomes the explicit conditional-probability
bound `p/(p+q) ≤ C/(1+C)`. -/
lemma pairParameter_le {p q C : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q)
    (hpq : 0 < p + q) (hC : 0 ≤ C) (hpqC : p ≤ C * q) :
    ((pairParameter p q hp hq hpq : I) : ℝ) ≤ C / (1 + C) := by
  rw [coe_pairParameter, div_le_div_iff₀ hpq (by linarith)]
  nlinarith

/-- Exact finite-binomial identity behind adjacent-urn screening: conditioned
on `h` balls landing in one of the two urns, the probability that all of them
land in the first urn is `(p/(p+q))^h`. -/
lemma adjacent_urn_exact (h : ℕ) {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q)
    (hpq : 0 < p + q) :
    Bin(h, pairParameter p q hp hq hpq).real {h} = (p / (p + q)) ^ h := by
  simp [ProbabilityTheory.binomial_real_self, pairParameter]

/-- **Adjacent-urn screening.**  This is the explicit exponential form of
HLOZ (6.9).  One may take `c(C) = 1/(1+C)`. -/
theorem adjacent_urn_screening (h : ℕ) {p q C : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q)
    (hpq : 0 < p + q) (hC : 0 ≤ C) (hpqC : p ≤ C * q) :
    Bin(h, pairParameter p q hp hq hpq).real {h} ≤
      Real.exp (-(h : ℝ) / (1 + C)) := by
  rw [adjacent_urn_exact h hp hq hpq]
  have hratio_nonneg : 0 ≤ p / (p + q) := div_nonneg hp hpq.le
  have hratio : p / (p + q) ≤ C / (1 + C) :=
    pairParameter_le hp hq hpq hC hpqC
  have hCden : 0 < 1 + C := by linarith
  have hCfrac : C / (1 + C) = 1 - 1 / (1 + C) := by
    field_simp [hCden.ne']
    ring
  have hbase_nonneg : 0 ≤ 1 - 1 / (1 + C) := by
    rw [← hCfrac]
    exact div_nonneg hC hCden.le
  calc
    (p / (p + q)) ^ h ≤ (C / (1 + C)) ^ h :=
      pow_le_pow_left₀ hratio_nonneg hratio h
    _ = (1 - 1 / (1 + C)) ^ h := by rw [hCfrac]
    _ ≤ (Real.exp (-(1 / (1 + C)))) ^ h :=
      pow_le_pow_left₀ hbase_nonneg (Real.one_sub_le_exp_neg _) h
    _ = Real.exp (-(h : ℝ) / (1 + C)) := by
      rw [← Real.exp_nat_mul]
      congr 1
      field_simp

/-! ## A small window inside a larger window -/

/-- The exact binomial singleton mass.  We expose it here because in the urn
application `n` is the number of remaining candidates and `j` is the number
selected into the smaller window. -/
lemma finite_upper_window_exact (n j : ℕ) (r : I) :
    Bin(n, r).real {j} =
      (n.choose j : ℝ) * (r : ℝ) ^ j * (1 - (r : ℝ)) ^ (n - j) :=
  ProbabilityTheory.binomial_real_singleton n j r

/-- A binomial singleton is bounded by `(n r)^j`.  This estimate remains true
when `j > n` (both sides are nonnegative and the singleton mass vanishes). -/
lemma binomial_singleton_le_mul_pow (n j : ℕ) (r : I) :
    Bin(n, r).real {j} ≤ ((n : ℝ) * (r : ℝ)) ^ j := by
  rw [finite_upper_window_exact]
  have hr0 : 0 ≤ (r : ℝ) := r.2.1
  have hr1 : (r : ℝ) ≤ 1 := r.2.2
  have htail : (1 - (r : ℝ)) ^ (n - j) ≤ 1 := by
    exact pow_le_one₀ (sub_nonneg.mpr hr1) (sub_le_self 1 hr0)
  have hchoose : (n.choose j : ℝ) ≤ (n : ℝ) ^ j := by
    exact_mod_cast Nat.choose_le_pow n j
  calc
    (n.choose j : ℝ) * (r : ℝ) ^ j * (1 - (r : ℝ)) ^ (n - j) ≤
        (n.choose j : ℝ) * (r : ℝ) ^ j * 1 := by
      exact mul_le_mul_of_nonneg_left htail (mul_nonneg (by positivity) (pow_nonneg hr0 _))
    _ ≤ (n : ℝ) ^ j * (r : ℝ) ^ j := by
      simpa using mul_le_mul_of_nonneg_right hchoose (pow_nonneg hr0 j)
    _ = ((n : ℝ) * (r : ℝ)) ^ j := by rw [mul_pow]

/-- **Two-window urn screening.**  There are `n ≤ J` independent candidates.
Each enters the upper window with conditional probability `r ≤ C g/f`, where
`g` and `f` are the small and large window widths.  The probability of exactly
`j` upper-window candidates is at most `(C g J/f)^j`.

If one ball is already forced to occupy the top urn, interpret `j` as the
number of *additional* upper-window balls; thus total occupancy `j+1` has this
bound. -/
theorem two_window_urn_screening {n J j : ℕ} (r : I) {C g f : ℝ}
    (hnJ : n ≤ J) (hC : 0 ≤ C) (hg : 0 ≤ g) (hf : 0 < f)
    (hr : (r : ℝ) ≤ C * g / f) :
    Bin(n, r).real {j} ≤ (C * g * J / f) ^ j := by
  calc
    Bin(n, r).real {j} ≤ ((n : ℝ) * (r : ℝ)) ^ j :=
      binomial_singleton_le_mul_pow n j r
    _ ≤ ((J : ℝ) * (C * g / f)) ^ j := by
      apply pow_le_pow_left₀
      · exact mul_nonneg (by positivity) r.2.1
      · exact mul_le_mul_of_nonneg (by exact_mod_cast hnJ) hr (by positivity)
          (div_nonneg (mul_nonneg hC hg) hf.le)
    _ = (C * g * J / f) ^ j := by
      congr 1
      ring

/-- Elementary Bernoulli inequality in the exact form needed to bound the
probability that at least one candidate enters the upper window. -/
lemma one_sub_one_sub_pow_le (n : ℕ) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    1 - (1 - x) ^ n ≤ n * x := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hpow_nonneg : 0 ≤ (1 - x) ^ n := pow_nonneg (sub_nonneg.mpr hx1) _
      have hpow_le : (1 - x) ^ n ≤ 1 := by
        exact pow_le_one₀ (sub_nonneg.mpr hx1) (sub_le_self 1 hx0)
      calc
        1 - (1 - x) ^ (n + 1) =
            (1 - (1 - x) ^ n) + x * (1 - x) ^ n := by
          rw [pow_succ]
          ring
        _ ≤ n * x + x * (1 - x) ^ n := by gcongr
        _ ≤ n * x + x := by
          have hxmul : x * (1 - x) ^ n ≤ x * 1 :=
            mul_le_mul_of_nonneg_left hpow_le hx0
          linarith
        _ = ((n + 1 : ℕ) : ℝ) * x := by
          push_cast
          ring

/-- Exact probability that a finite binomial sample has at least one success. -/
lemma binomial_one_or_more_eq (n : ℕ) (r : I) :
    Bin(n, r).real (Set.Ici 1) = 1 - (1 - (r : ℝ)) ^ n := by
  have hcompl : (Set.Ici (1 : ℕ))ᶜ = {0} := by
    ext k
    simp only [Set.mem_compl_iff, Set.mem_Ici, Set.mem_singleton_iff]
    omega
  have hmeas : MeasurableSet (Set.Ici (1 : ℕ)) := measurableSet_Ici
  have h := measureReal_compl (μ := Bin(n, r)) hmeas
  rw [hcompl, ProbabilityTheory.binomial_real_zero, probReal_univ] at h
  linarith

/-- Union-bound form of two-window screening.  With at most `J` candidates and
per-candidate conditional chance at most `C g/f`, some candidate enters the
upper window with probability at most `C g J/f`.  This is the `j = 1`
instance used in HLOZ Proposition 4.9. -/
theorem binomial_one_or_more_le {n J : ℕ} (r : I) {C g f : ℝ}
    (hnJ : n ≤ J) (hC : 0 ≤ C) (hg : 0 ≤ g) (hf : 0 < f)
    (hr : (r : ℝ) ≤ C * g / f) :
    Bin(n, r).real (Set.Ici 1) ≤ C * g * J / f := by
  rw [binomial_one_or_more_eq]
  calc
    1 - (1 - (r : ℝ)) ^ n ≤ n * (r : ℝ) :=
      one_sub_one_sub_pow_le n r.2.1 r.2.2
    _ ≤ J * (C * g / f) := by
      exact mul_le_mul_of_nonneg (by exact_mod_cast hnJ) hr (by positivity)
        (div_nonneg (mul_nonneg hC hg) hf.le)
    _ = C * g * J / f := by ring

end Erdos1165.UrnScreening
