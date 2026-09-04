/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos297.WeightedFourier
import ErdosProblems.Erdos297.FourierPhase
import ErdosProblems.Erdos297.GoodFactorization
import ErdosProblems.Erdos297.ActiveLcm
import ErdosProblems.Erdos297.GoodSetDensity
import ErdosProblems.Erdos297.LogisticNormalization

/-!
# The weighted major arc in Liu--Sawhney's local limit theorem

This file packages the major-arc part of Liu--Sawhney, Proposition 3.2.
There are two ranges.  On the central range the exact expectation removes
the linear phase and the product is trapped in the right half-plane by the
cubic Taylor estimate from `FourierPhase`.  On the remaining major range,
the quadratic characteristic-function estimate gives exponential decay;
the sum of those decaying bounds is an explicit hypothesis of the finite
lemma.

The hypotheses are deliberately finite numerical inequalities.  In the
application, the central cubic budget follows from
`sum_{n >= M} n^{-3} = O(M^{-2})`, while the intermediate budget follows
from the lower bound for `|A|` and the lower bound for `p (1-p)`.
-/

open scoped BigOperators

namespace Erdos297.MajorArc

open Complex Finset Filter
open Erdos297.WeightedFourier
open Erdos297.GoodFactorization

noncomputable section

attribute [local instance] Classical.propDecidable

/-- Nonzero frequencies with balanced representative of magnitude at most
`M / 2`.  This is the source range `0 < |h| <= M/2`. -/
def majorFrequencies (Q M : ℕ) [NeZero Q] : Finset (ZMod Q) :=
  (Finset.univ.erase 0).filter fun h ↦ h.valMinAbs.natAbs ≤ M / 2

/-- The central part `0 < |h| <= H` of the major frequencies. -/
def centralFrequencies (Q H : ℕ) [NeZero Q] : Finset (ZMod Q) :=
  (Finset.univ.erase 0).filter fun h ↦ h.valMinAbs.natAbs ≤ H

/-- The intermediate major range `H < |h| <= M/2`. -/
def intermediateFrequencies (Q M H : ℕ) [NeZero Q] : Finset (ZMod Q) :=
  majorFrequencies Q M \ centralFrequencies Q H

/-- Frequencies outside the major range. -/
def minorFrequencies (Q M : ℕ) [NeZero Q] : Finset (ZMod Q) :=
  (Finset.univ.erase 0) \ majorFrequencies Q M

/-- A source-valid central cutoff, `N^(3/5)` rounded down.  Since
`M ≥ N^0.95` eventually, it lies well inside the major range and leaves
power savings on both sides of the split. -/
noncomputable def centralCutoff (N : ℕ) : ℕ :=
  ⌊(N : ℝ) ^ ((3 : ℝ) / 5)⌋₊

lemma central_union_intermediate (Q M H : ℕ) [NeZero Q] (hHM : H ≤ M / 2) :
    centralFrequencies Q H ∪ intermediateFrequencies Q M H =
      majorFrequencies Q M := by
  apply Finset.Subset.antisymm
  · intro h hh
    rw [Finset.mem_union] at hh
    rcases hh with hh | hh
    · rw [centralFrequencies, Finset.mem_filter] at hh
      rw [majorFrequencies, Finset.mem_filter]
      exact ⟨hh.1, hh.2.trans hHM⟩
    · exact (Finset.mem_sdiff.mp hh).1
  · intro h hh
    by_cases hc : h ∈ centralFrequencies Q H
    · exact Finset.mem_union_left _ hc
    · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hh, hc⟩)

lemma disjoint_central_intermediate (Q M H : ℕ) [NeZero Q] :
    Disjoint (centralFrequencies Q H) (intermediateFrequencies Q M H) := by
  rw [Finset.disjoint_left]
  intro h hc hi
  exact (Finset.mem_sdiff.mp hi).2 hc

lemma major_union_minor (Q M : ℕ) [NeZero Q] :
    majorFrequencies Q M ∪ minorFrequencies Q M =
      (Finset.univ.erase 0 : Finset (ZMod Q)) := by
  unfold minorFrequencies
  exact Finset.union_sdiff_of_subset (Finset.filter_subset _ _)

lemma disjoint_major_minor (Q M : ℕ) [NeZero Q] :
    Disjoint (majorFrequencies Q M) (minorFrequencies Q M) := by
  rw [Finset.disjoint_left]
  intro h hm hn
  exact (Finset.mem_sdiff.mp hn).2 hm

/-- There are at most `M+1` balanced residues with magnitude at most
`M/2`.  The harmless extra one avoids a parity split. -/
lemma majorFrequencies_card_le_add_one (Q M : ℕ) [NeZero Q] :
    (majorFrequencies Q M).card ≤ M + 1 := by
  let r := M / 2
  have himage :
      (majorFrequencies Q M).image ZMod.valMinAbs ⊆
        Finset.Icc (-(r : ℤ)) (r : ℤ) := by
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨h, hh, rfl⟩
    have hk : h.valMinAbs.natAbs ≤ r := by
      simpa [majorFrequencies, r] using (Finset.mem_filter.mp hh).2
    have habs : |h.valMinAbs| ≤ (r : ℤ) := by
      rw [← Int.natCast_natAbs]
      exact_mod_cast hk
    exact Finset.mem_Icc.mpr (abs_le.mp habs)
  have hcardImage :
      ((majorFrequencies Q M).image ZMod.valMinAbs).card =
        (majorFrequencies Q M).card :=
    Finset.card_image_iff.mpr ZMod.injective_valMinAbs.injOn
  calc
    (majorFrequencies Q M).card =
        ((majorFrequencies Q M).image ZMod.valMinAbs).card := hcardImage.symm
    _ ≤ (Finset.Icc (-(r : ℤ)) (r : ℤ)).card :=
      Finset.card_le_card himage
    _ = 2 * r + 1 := by
      rw [Int.card_Icc]
      have hnonneg : (0 : ℤ) ≤ (r : ℤ) + 1 - -(r : ℤ) := by omega
      apply Nat.cast_injective (R := ℤ)
      rw [Int.toNat_of_nonneg hnonneg]
      push_cast
      ring
    _ ≤ M + 1 := by omega

/-- Radian angle of the reciprocal character at a balanced frequency.  The
minus sign matches `WeightedFourier.coefficient`. -/
def reciprocalAngle {Q : ℕ} (h : ZMod Q) (n : ℕ) : ℝ :=
  -(2 * Real.pi * (h.valMinAbs : ℝ) / n)

lemma abs_reciprocalAngle {Q n : ℕ} (h : ZMod Q) (hn : 0 < n) :
    |reciprocalAngle h n| =
      2 * Real.pi * (h.valMinAbs.natAbs : ℝ) / n := by
  unfold reciprocalAngle
  rw [abs_neg, abs_div, abs_mul, abs_mul,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2),
    abs_of_pos Real.pi_pos]
  have hk : |(h.valMinAbs : ℝ)| = (h.valMinAbs.natAbs : ℝ) := by
    rw [← Int.cast_abs, Int.abs_eq_natAbs]
    simp
  rw [hk, abs_of_pos (by exact_mod_cast hn : (0 : ℝ) < n)]

/-- Clearing a denominator inside `Q` identifies the finite character with
the reciprocal phase at the balanced integer representative. -/
lemma stdAddChar_clearedReciprocal
    {Q n : ℕ} [NeZero Q] (hn : 0 < n) (hnQ : n ∣ Q) (h : ZMod Q) :
    ZMod.stdAddChar (-((Q / n : ZMod Q) * h)) =
      Complex.exp (((reciprocalAngle h n : ℝ) : ℂ) * Complex.I) := by
  have harg :
      -((Q / n : ZMod Q) * h) =
        ((-(Int.ofNat (Q / n) * h.valMinAbs) : ℤ) : ZMod Q) := by
    have hcastNat : ((Int.ofNat (Q / n) : ℤ) : ZMod Q) =
        (Q / n : ZMod Q) := by
      simp only [Int.ofNat_eq_natCast, Int.cast_natCast]
    calc
      -((Q / n : ZMod Q) * h) =
          -((Q / n : ZMod Q) * (h.valMinAbs : ZMod Q)) :=
        congrArg (fun x : ZMod Q ↦ -((Q / n : ZMod Q) * x))
          h.coe_valMinAbs.symm
      _ = ((-(Int.ofNat (Q / n) * h.valMinAbs) : ℤ) : ZMod Q) := by
        rw [Int.cast_neg, Int.cast_mul, hcastNat]
  rw [harg, ZMod.stdAddChar_coe]
  apply congrArg Complex.exp
  dsimp [reciprocalAngle]
  have hQpos : 0 < Q := Nat.pos_of_ne_zero (NeZero.ne Q)
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have hQ0 : (Q : ℂ) ≠ 0 := by exact_mod_cast hQpos.ne'
  have hnQint : (n : ℤ) ∣ (Q : ℤ) := by exact_mod_cast hnQ
  have hcancelInt : (Q : ℤ) / (n : ℤ) * (n : ℤ) = (Q : ℤ) :=
    Int.ediv_mul_cancel hnQint
  have hcancel :
      ((((Q : ℤ) / (n : ℤ) : ℤ) : ℂ) * (n : ℂ)) = (Q : ℂ) := by
    exact_mod_cast hcancelInt
  push_cast
  field_simp [hn0, hQ0]
  calc
    -(((((Q : ℤ) / (n : ℤ) : ℤ) : ℂ) * (h.valMinAbs : ℂ)) * (n : ℂ)) =
        -(h.valMinAbs : ℂ) *
          ((((Q : ℤ) / (n : ℤ) : ℤ) : ℂ) * (n : ℂ)) := by ring
    _ = -(h.valMinAbs : ℂ) * (Q : ℂ) := by rw [hcancel]
    _ = -((h.valMinAbs : ℂ) * (Q : ℂ)) := by ring

/-- Exact expectation one cancels the product's linear reciprocal phase at
every balanced frequency. -/
lemma expectationPhase_reciprocalAngle
    {Q : ℕ} [NeZero Q] (I : Finset ℕ) (p : ℕ → ℝ) (h : ZMod Q)
    (hpos : ∀ n ∈ I, 0 < n)
    (hmean : ∑ n ∈ I, p n / n = 1) :
    ZMod.stdAddChar (h * (Q : ZMod Q)) =
      Complex.exp (((-(∑ n ∈ I, p n * reciprocalAngle h n) : ℝ) : ℂ) *
        Complex.I) := by
  have hsum :
      -(∑ n ∈ I, p n * reciprocalAngle h n) =
        (h.valMinAbs : ℝ) * (2 * Real.pi) := by
    rw [show (∑ n ∈ I, p n * reciprocalAngle h n) =
        -(2 * Real.pi * (h.valMinAbs : ℝ)) * ∑ n ∈ I, p n / n by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n hnI
      dsimp [reciprocalAngle]
      have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (hpos n hnI).ne'
      field_simp [hn0]]
    rw [hmean]
    ring
  rw [ZMod.natCast_self, mul_zero]
  rw [(ZMod.stdAddChar (N := Q)).map_zero_eq_one]
  rw [hsum]
  symm
  convert Complex.exp_int_mul_two_pi_mul_I h.valMinAbs using 1 <;>
    push_cast <;> ring_nf

/-- Contribution of a finite block of Fourier frequencies, before the
normalizing factor `1 / Q`. -/
def fourierBlock {ι : Type*} [DecidableEq ι] {Q : ℕ} [NeZero Q]
    (frequencies : Finset (ZMod Q)) (I : Finset ι)
    (step : ι → ZMod Q) (p : ι → ℝ) (target : ZMod Q) : ℂ :=
  ∑ h ∈ frequencies,
    ZMod.stdAddChar (h * target) * coefficient I step p h

/-- Product of the mean-centred Bernoulli factors at real angles `t i`. -/
def centeredProduct {ι : Type*} [DecidableEq ι]
    (I : Finset ι) (p t : ι → ℝ) : ℂ :=
  ∏ i ∈ I, centeredBernoulliFactor (p i) (t i)

/-- Positive quadratic product occurring in the central Taylor
approximation. -/
def quadraticProduct {ι : Type*} [DecidableEq ι]
    (I : Finset ι) (p t : ι → ℝ) : ℝ :=
  ∏ i ∈ I, (1 - p i * (1 - p i) * (t i) ^ 2 / 2)

/-- The genuine Gaussian product with the same variances as the Bernoulli
factors. -/
def gaussianProduct {ι : Type*} [DecidableEq ι]
    (I : Finset ι) (p t : ι → ℝ) : ℂ :=
  ∏ i ∈ I, bernoulliGaussian (p i) (t i)

/-- The central comparison Gaussian is a strictly positive real number. -/
lemma gaussianProduct_eq_exp {ι : Type*} [DecidableEq ι]
    (I : Finset ι) (p t : ι → ℝ) :
    gaussianProduct I p t =
      ((Real.exp (-(∑ i ∈ I, p i * (1 - p i) * (t i) ^ 2) / 2) : ℝ) : ℂ) := by
  unfold gaussianProduct bernoulliGaussian
  change (∏ i ∈ I,
      ((Real.exp (-(p i * (1 - p i) * (t i) ^ 2 / 2)) : ℝ) : ℂ)) = _
  calc
    (∏ i ∈ I,
        ((Real.exp (-(p i * (1 - p i) * (t i) ^ 2 / 2)) : ℝ) : ℂ)) =
        ((∏ i ∈ I,
          Real.exp (-(p i * (1 - p i) * (t i) ^ 2 / 2)) : ℝ) : ℂ) := by
      rw [Complex.ofReal_prod]
    _ = ((Real.exp
        (∑ i ∈ I, -(p i * (1 - p i) * (t i) ^ 2 / 2)) : ℝ) : ℂ) := by
      rw [Real.exp_sum]
    _ = _ := by
      congr 2
      calc
        (∑ i ∈ I, -(p i * (1 - p i) * (t i) ^ 2 / 2)) =
            ∑ i ∈ I, (-(p i * (1 - p i) * (t i) ^ 2)) / 2 := by
          apply Finset.sum_congr rfl
          intro i hi
          ring
        _ = (∑ i ∈ I, -(p i * (1 - p i) * (t i) ^ 2)) / 2 := by
          rw [Finset.sum_div]
        _ = -(∑ i ∈ I, p i * (1 - p i) * (t i) ^ 2) / 2 := by
          rw [Finset.sum_neg_distrib]

lemma gaussianProduct_re_pos {ι : Type*} [DecidableEq ι]
    (I : Finset ι) (p t : ι → ℝ) :
    0 < (gaussianProduct I p t).re := by
  rw [gaussianProduct_eq_exp]
  change 0 < Real.exp (-(∑ i ∈ I, p i * (1 - p i) * (t i) ^ 2) / 2)
  exact Real.exp_pos _

/-- The uncentred Bernoulli product multiplied by the phase dictated by its
exact expectation. -/
def expectationCenteredTerm {ι : Type*} [DecidableEq ι]
    (I : Finset ι) (p t : ι → ℝ) : ℂ :=
  Complex.exp (((-(∑ i ∈ I, p i * t i) : ℝ) : ℂ) * Complex.I) *
    ∏ i ∈ I,
      (((1 - p i : ℝ) : ℂ) +
        (p i : ℂ) * Complex.exp (((t i : ℝ) : ℂ) * Complex.I))

/-- Exact cancellation of the linear phase.  This is the algebraic use of
the expectation equation in the major-arc argument. -/
theorem expectationCenteredTerm_eq_centeredProduct
    {ι : Type*} [DecidableEq ι] (I : Finset ι) (p t : ι → ℝ) :
    expectationCenteredTerm I p t = centeredProduct I p t := by
  unfold expectationCenteredTerm centeredProduct centeredBernoulliFactor
  rw [Finset.prod_mul_distrib]
  have hexp :
      ∏ i ∈ I, Complex.exp (((-(p i * t i) : ℝ) : ℂ) * Complex.I) =
        Complex.exp (((-(∑ i ∈ I, p i * t i) : ℝ) : ℂ) * Complex.I) := by
    rw [← Complex.exp_sum]
    congr 2
    push_cast
    rw [← Finset.sum_mul, Finset.sum_neg_distrib]
  congr 1
  simpa using hexp.symm

/-- A standard product perturbation estimate, specialized to the numerical
budget used on the central arc. -/
lemma norm_prod_one_add_sub_one_le_one_sixth
    {ι : Type*} [DecidableEq ι] (I : Finset ι) (u : ι → ℂ)
    (hbudget : ∑ i ∈ I, ‖u i‖ ≤ (1 / 7 : ℝ)) :
    ‖(∏ i ∈ I, (1 + u i)) - 1‖ ≤ (1 / 6 : ℝ) := by
  calc
    ‖(∏ i ∈ I, (1 + u i)) - 1‖
        ≤ Real.exp (∑ i ∈ I, ‖u i‖) - 1 :=
      Finset.norm_prod_one_add_sub_one_le I u
    _ ≤ Real.exp (1 / 7 : ℝ) - 1 := by
      gcongr
    _ ≤ 1 / (1 - (1 / 7 : ℝ)) - 1 := by
      gcongr
      exact Real.exp_bound_div_one_sub_of_interval (by norm_num) (by norm_num)
    _ = 1 / 6 := by norm_num

/-- Every quadratic Taylor factor is at least `1/2` on the unit angle
interval. -/
lemma quadraticFactor_ge_half {p t : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (ht : |t| ≤ 1) :
    (1 / 2 : ℝ) ≤ 1 - p * (1 - p) * t ^ 2 / 2 := by
  have hpvar : p * (1 - p) ≤ 1 := by
    nlinarith [sq_nonneg (p - 1 / 2)]
  have ht2 : t ^ 2 ≤ 1 := by
    have hpow := pow_le_pow_left₀ (abs_nonneg t) ht 2
    simpa [sq_abs] using hpow
  have hpvar0 : 0 ≤ p * (1 - p) := mul_nonneg hp0 (sub_nonneg.mpr hp1)
  have hmul : p * (1 - p) * t ^ 2 ≤ 1 := by
    calc
      p * (1 - p) * t ^ 2 ≤ 1 * t ^ 2 :=
        mul_le_mul_of_nonneg_right hpvar (sq_nonneg t)
      _ ≤ 1 * 1 := mul_le_mul_of_nonneg_left ht2 (by norm_num)
      _ = 1 := one_mul _
  linarith

/-- The normalized central factor differs from one by at most twice its
cubic Taylor error. -/
lemma normalized_centeredFactor_sub_one
    {p t : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (ht : |t| ≤ 1) :
    ‖centeredBernoulliFactor p t /
          (1 - p * (1 - p) * t ^ 2 / 2 : ℝ) - 1‖
      ≤ 2 * |t| ^ 3 := by
  let b : ℝ := 1 - p * (1 - p) * t ^ 2 / 2
  have hbhalf : (1 / 2 : ℝ) ≤ b := quadraticFactor_ge_half hp0 hp1 ht
  have hbpos : 0 < b := (by norm_num : (0 : ℝ) < 1 / 2).trans_le hbhalf
  have htaylor :
      ‖centeredBernoulliFactor p t - (b : ℂ)‖ ≤ |t| ^ 3 := by
    simpa [b] using centeredBernoulliFactor_local_quadratic hp0 hp1 ht
  have hbne : (b : ℂ) ≠ 0 := by exact_mod_cast hbpos.ne'
  change ‖centeredBernoulliFactor p t / (b : ℂ) - 1‖ ≤ _
  rw [div_sub_one hbne, norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hbpos]
  calc
    ‖centeredBernoulliFactor p t - (b : ℂ)‖ / b
        ≤ |t| ^ 3 / b := div_le_div_of_nonneg_right htaylor hbpos.le
    _ ≤ |t| ^ 3 / (1 / 2 : ℝ) := by
      exact div_le_div_of_nonneg_left (pow_nonneg (abs_nonneg _) _)
        (by norm_num) hbhalf
    _ = 2 * |t| ^ 3 := by ring

/-- Central Gaussian positivity in a completely finite form.  The Taylor
budget `2 * sum |t_i|^3 <= 1/7` guarantees that the centred product remains
in the right half-plane.  The positive comparison product is the quadratic
Gaussian discretization. -/
theorem central_centeredProduct_re_lower
    {ι : Type*} [DecidableEq ι] (I : Finset ι) (p t : ι → ℝ)
    (hp0 : ∀ i ∈ I, 0 ≤ p i) (hp1 : ∀ i ∈ I, p i ≤ 1)
    (ht : ∀ i ∈ I, |t i| ≤ 1)
    (hcubic : 2 * ∑ i ∈ I, |t i| ^ 3 ≤ (1 / 7 : ℝ)) :
    (5 / 6 : ℝ) * quadraticProduct I p t ≤
      (centeredProduct I p t).re := by
  let b : ι → ℝ := fun i ↦ 1 - p i * (1 - p i) * (t i) ^ 2 / 2
  let u : ι → ℂ := fun i ↦ centeredBernoulliFactor (p i) (t i) / b i - 1
  have hbhalf : ∀ i ∈ I, (1 / 2 : ℝ) ≤ b i := by
    intro i hi
    exact quadraticFactor_ge_half (hp0 i hi) (hp1 i hi) (ht i hi)
  have hbpos : ∀ i ∈ I, 0 < b i := by
    intro i hi
    exact (by norm_num : (0 : ℝ) < 1 / 2).trans_le (hbhalf i hi)
  have hubound : ∀ i ∈ I, ‖u i‖ ≤ 2 * |t i| ^ 3 := by
    intro i hi
    exact normalized_centeredFactor_sub_one
      (hp0 i hi) (hp1 i hi) (ht i hi)
  have husum : ∑ i ∈ I, ‖u i‖ ≤ (1 / 7 : ℝ) := by
    calc
      ∑ i ∈ I, ‖u i‖ ≤ ∑ i ∈ I, 2 * |t i| ^ 3 :=
        Finset.sum_le_sum fun i hi ↦ hubound i hi
      _ = 2 * ∑ i ∈ I, |t i| ^ 3 := by rw [Finset.mul_sum]
      _ ≤ 1 / 7 := hcubic
  have hprod := norm_prod_one_add_sub_one_le_one_sixth I u husum
  have hprodRe : (5 / 6 : ℝ) ≤ (∏ i ∈ I, (1 + u i)).re := by
    have hreabs : |((∏ i ∈ I, (1 + u i)) - 1).re| ≤ (1 / 6 : ℝ) :=
      (Complex.abs_re_le_norm _).trans hprod
    have hre := (abs_le.mp hreabs).1
    simp only [Complex.sub_re, Complex.one_re] at hre
    linarith
  have hfactor (i : ι) (hi : i ∈ I) :
      centeredBernoulliFactor (p i) (t i) =
        (b i : ℂ) * (1 + u i) := by
    dsimp [u]
    have hbne : (b i : ℂ) ≠ 0 := by exact_mod_cast (hbpos i hi).ne'
    field_simp
    ring
  have hcentered : centeredProduct I p t =
      ((∏ i ∈ I, b i : ℝ) : ℂ) * ∏ i ∈ I, (1 + u i) := by
    unfold centeredProduct
    calc
      ∏ i ∈ I, centeredBernoulliFactor (p i) (t i) =
          ∏ i ∈ I, ((b i : ℂ) * (1 + u i)) := by
        apply Finset.prod_congr rfl
        intro i hi
        exact hfactor i hi
      _ = ((∏ i ∈ I, b i : ℝ) : ℂ) * ∏ i ∈ I, (1 + u i) := by
        rw [Finset.prod_mul_distrib, Complex.ofReal_prod]
  have hbprod0 : 0 ≤ ∏ i ∈ I, b i :=
    Finset.prod_nonneg fun i hi ↦ (hbpos i hi).le
  rw [hcentered, Complex.mul_re]
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  have hquad : quadraticProduct I p t = ∏ i ∈ I, b i := by rfl
  rw [hquad]
  simpa [mul_comm] using mul_le_mul_of_nonneg_left hprodRe hbprod0

theorem central_centeredProduct_re_nonneg
    {ι : Type*} [DecidableEq ι] (I : Finset ι) (p t : ι → ℝ)
    (hp0 : ∀ i ∈ I, 0 ≤ p i) (hp1 : ∀ i ∈ I, p i ≤ 1)
    (ht : ∀ i ∈ I, |t i| ≤ 1)
    (hcubic : 2 * ∑ i ∈ I, |t i| ^ 3 ≤ (1 / 7 : ℝ)) :
    0 ≤ (centeredProduct I p t).re := by
  have hmain := central_centeredProduct_re_lower I p t hp0 hp1 ht hcubic
  have hquad0 : 0 ≤ quadraticProduct I p t := by
    unfold quadraticProduct
    exact Finset.prod_nonneg fun i hi ↦
      (quadraticFactor_ge_half (hp0 i hi) (hp1 i hi) (ht i hi)).trans'
        (by norm_num)
  exact (mul_nonneg (by norm_num) hquad0).trans hmain

/-- Removing the mean phase does not change the norm. -/
lemma centeredBernoulliFactor_norm_eq_bernoulliFactor
    (p t : ℝ) :
    ‖centeredBernoulliFactor p t‖ =
      ‖((1 - p : ℝ) : ℂ) +
        (p : ℂ) * Complex.exp (((t : ℝ) : ℂ) * Complex.I)‖ := by
  rw [centeredBernoulliFactor, norm_mul, Complex.norm_exp]
  simp

/-- Intermediate-major-arc quadratic decay, in radian variables.  The
circle distance is retained in the conclusion, so the lemma is also useful
at endpoints without choosing integer representatives. -/
theorem centeredProduct_norm_le_exp_circleDistance
    {ι : Type*} [DecidableEq ι] (I : Finset ι) (p t : ι → ℝ)
    (hp0 : ∀ i ∈ I, 0 ≤ p i) (hp1 : ∀ i ∈ I, p i ≤ 1) :
    ‖centeredProduct I p t‖ ≤
      Real.exp (-(8 * ∑ i ∈ I,
        p i * (1 - p i) * circleDistance (t i / (2 * Real.pi)) ^ 2)) := by
  have hphase (i : ι) :
      fourierPhase (t i / (2 * Real.pi)) =
        Complex.exp (((t i : ℝ) : ℂ) * Complex.I) := by
    unfold fourierPhase
    congr 2
    push_cast
    field_simp [Real.pi_ne_zero]
  calc
    ‖centeredProduct I p t‖ =
        ‖∏ i ∈ I, bernoulliFactor (p i) (t i / (2 * Real.pi))‖ := by
      rw [centeredProduct, norm_prod, norm_prod]
      apply Finset.prod_congr rfl
      intro i hi
      rw [centeredBernoulliFactor_norm_eq_bernoulliFactor, bernoulliFactor,
        hphase]
    _ ≤ _ := bernoulliFactor_prod_norm_le_exp I p
      (fun i ↦ t i / (2 * Real.pi)) hp0 hp1

/-- On the principal radian interval, circle distance is ordinary absolute
value after division by `2*pi`. -/
lemma circleDistance_div_two_pi {t : ℝ} (ht : |t| ≤ Real.pi) :
    circleDistance (t / (2 * Real.pi)) = |t| / (2 * Real.pi) := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have habs : |t / (2 * Real.pi)| ≤ (1 / 2 : ℝ) := by
    rw [abs_div, abs_of_pos (by positivity : 0 < 2 * Real.pi)]
    exact (div_le_iff₀ (by positivity : 0 < 2 * Real.pi)).2 (by nlinarith)
  unfold circleDistance
  rw [(AddCircle.norm_coe_eq_abs_iff (p := (1 : ℝ)) (by norm_num)).2 (by simpa using habs)]
  rw [abs_div, abs_of_pos (by positivity : 0 < 2 * Real.pi)]

/-- More familiar radian form of intermediate quadratic decay. -/
theorem centeredProduct_norm_le_exp_of_abs_le_pi
    {ι : Type*} [DecidableEq ι] (I : Finset ι) (p t : ι → ℝ)
    (hp0 : ∀ i ∈ I, 0 ≤ p i) (hp1 : ∀ i ∈ I, p i ≤ 1)
    (ht : ∀ i ∈ I, |t i| ≤ Real.pi) :
    ‖centeredProduct I p t‖ ≤
      Real.exp (-(2 / Real.pi ^ 2 * ∑ i ∈ I,
        p i * (1 - p i) * (t i) ^ 2)) := by
  refine (centeredProduct_norm_le_exp_circleDistance I p t hp0 hp1).trans ?_
  apply Real.exp_le_exp.mpr
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have heq :
      8 * ∑ i ∈ I,
          p i * (1 - p i) * circleDistance (t i / (2 * Real.pi)) ^ 2 =
        2 / Real.pi ^ 2 * ∑ i ∈ I,
          p i * (1 - p i) * (t i) ^ 2 := by
    rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [circleDistance_div_two_pi (ht i hi), div_pow, sq_abs]
    field_simp
    ring
  rw [heq]

/-- Sum form of intermediate decay. -/
theorem intermediate_sum_norm_le
    {κ ι : Type*} [DecidableEq κ] [DecidableEq ι]
    (H : Finset κ) (I : Finset ι) (p : ι → ℝ) (t : κ → ι → ℝ)
    (hp0 : ∀ i ∈ I, 0 ≤ p i) (hp1 : ∀ i ∈ I, p i ≤ 1) :
    ∑ h ∈ H, ‖centeredProduct I p (t h)‖ ≤
      ∑ h ∈ H, Real.exp (-(8 * ∑ i ∈ I,
        p i * (1 - p i) *
          circleDistance (t h i / (2 * Real.pi)) ^ 2)) := by
  exact Finset.sum_le_sum fun h hh ↦
    centeredProduct_norm_le_exp_circleDistance I p (t h) hp0 hp1

/-- Full finite weighted major-arc estimate.  `central` and `intermediate`
partition the nonzero major frequencies.  `hcharacter` identifies each
one-index character with its real angle, while `hexpectation` is precisely
the exact-mean cancellation.  The central cubic budget and intermediate
exponential sum are the two numerical estimates in Liu--Sawhney Lemma 3.1.
-/
theorem weighted_majorArc_lower
    {ι : Type*} [DecidableEq ι] {Q : ℕ} [NeZero Q]
    (major central intermediate : Finset (ZMod Q))
    (I : Finset ι) (step : ι → ZMod Q) (p : ι → ℝ)
    (target : ZMod Q) (t : ZMod Q → ι → ℝ)
    (hmajor : major = central ∪ intermediate)
    (hdisjoint : Disjoint central intermediate)
    (hp0 : ∀ i ∈ I, 0 ≤ p i) (hp1 : ∀ i ∈ I, p i ≤ 1)
    (hcharacter : ∀ h ∈ major, ∀ i ∈ I,
      ZMod.stdAddChar (-(step i * h)) =
        Complex.exp ((((t h i) : ℝ) : ℂ) * Complex.I))
    (hexpectation : ∀ h ∈ major,
      ZMod.stdAddChar (h * target) =
        Complex.exp (((-(∑ i ∈ I, p i * t h i) : ℝ) : ℂ) * Complex.I))
    (hcentralAngle : ∀ h ∈ central, ∀ i ∈ I, |t h i| ≤ 1)
    (hcentralCubic : ∀ h ∈ central,
      2 * ∑ i ∈ I, |t h i| ^ 3 ≤ (1 / 7 : ℝ))
    (hintermediate :
      ∑ h ∈ intermediate, Real.exp (-(8 * ∑ i ∈ I,
        p i * (1 - p i) *
          circleDistance (t h i / (2 * Real.pi)) ^ 2)) ≤ (1 / 4 : ℝ)) :
    (3 / 4 : ℝ) ≤ 1 + (fourierBlock major I step p target).re := by
  have hterm (h : ZMod Q) (hh : h ∈ major) :
      ZMod.stdAddChar (h * target) * coefficient I step p h =
        centeredProduct I p (t h) := by
    rw [coefficient, hexpectation h hh]
    have hprod :
        (∏ i ∈ I,
          (((1 - p i : ℝ) : ℂ) +
            (p i : ℂ) * ZMod.stdAddChar (-(step i * h)))) =
          ∏ i ∈ I,
            (((1 - p i : ℝ) : ℂ) +
              (p i : ℂ) * Complex.exp ((((t h i) : ℝ) : ℂ) * Complex.I)) := by
      apply Finset.prod_congr rfl
      intro i hi
      rw [hcharacter h hh i hi]
    rw [hprod]
    exact expectationCenteredTerm_eq_centeredProduct I p (t h)
  have hcentralRe : 0 ≤
    (∑ h ∈ central,
        ZMod.stdAddChar (h * target) * coefficient I step p h).re := by
    rw [Complex.re_sum]
    exact Finset.sum_nonneg fun h hh ↦ by
      rw [hterm h (by rw [hmajor]; exact Finset.mem_union_left _ hh)]
      exact central_centeredProduct_re_nonneg I p (t h) hp0 hp1
        (hcentralAngle h hh) (hcentralCubic h hh)
  have hintermediateNorm :
      ‖∑ h ∈ intermediate,
          ZMod.stdAddChar (h * target) * coefficient I step p h‖ ≤
        (1 / 4 : ℝ) := by
    calc
      ‖∑ h ∈ intermediate,
          ZMod.stdAddChar (h * target) * coefficient I step p h‖
          ≤ ∑ h ∈ intermediate,
              ‖ZMod.stdAddChar (h * target) * coefficient I step p h‖ := by
        simpa using norm_sum_le (intermediate : Finset (ZMod Q))
          (fun h ↦ ZMod.stdAddChar (h * target) * coefficient I step p h)
      _ = ∑ h ∈ intermediate, ‖centeredProduct I p (t h)‖ := by
        apply Finset.sum_congr rfl
        intro h hh
        rw [hterm h (by rw [hmajor]; exact Finset.mem_union_right _ hh)]
      _ ≤ ∑ h ∈ intermediate, Real.exp (-(8 * ∑ i ∈ I,
          p i * (1 - p i) *
            circleDistance (t h i / (2 * Real.pi)) ^ 2)) :=
        intermediate_sum_norm_le intermediate I p t hp0 hp1
      _ ≤ 1 / 4 := hintermediate
  have hintermediateRe : -(1 / 4 : ℝ) ≤
      (∑ h ∈ intermediate,
        ZMod.stdAddChar (h * target) * coefficient I step p h).re := by
    have habs := (Complex.abs_re_le_norm _).trans hintermediateNorm
    exact (abs_le.mp habs).1
  rw [fourierBlock, hmajor, Finset.sum_union hdisjoint, Complex.add_re]
  linarith

/-- Reciprocal specialization of the finite major-arc lemma.  All structural
Fourier hypotheses (frequency partition, character identification, and
linear-phase cancellation) are discharged here.  The two remaining
hypotheses are exactly the finite central and intermediate numerical
estimates.  In the application `Q` is the LCM of the active denominator set,
not the larger ambient smooth LCM. -/
theorem reciprocal_majorArc_lower_of_budgets
    {Q M H : ℕ} [NeZero Q] (hHM : H ≤ M / 2)
    (A : Finset ℕ) (p : ℕ → ℝ)
    (hApos : ∀ n ∈ A, 0 < n) (hAdvd : ∀ n ∈ A, n ∣ Q)
    (hp0 : ∀ n ∈ A, 0 ≤ p n) (hp1 : ∀ n ∈ A, p n ≤ 1)
    (hmean : ∑ n ∈ A, p n / n = 1)
    (hcentralAngle : ∀ h ∈ centralFrequencies Q H, ∀ n ∈ A,
      |reciprocalAngle h n| ≤ 1)
    (hcentralCubic : ∀ h ∈ centralFrequencies Q H,
      2 * ∑ n ∈ A, |reciprocalAngle h n| ^ 3 ≤ (1 / 7 : ℝ))
    (hintermediate :
      ∑ h ∈ intermediateFrequencies Q M H,
        Real.exp (-(8 * ∑ n ∈ A, p n * (1 - p n) *
          circleDistance (reciprocalAngle h n / (2 * Real.pi)) ^ 2)) ≤
        (1 / 4 : ℝ)) :
    (3 / 4 : ℝ) ≤ 1 +
      (fourierBlock (majorFrequencies Q M) A
        (fun n ↦ (Q / n : ZMod Q)) p (Q : ZMod Q)).re := by
  apply weighted_majorArc_lower
    (majorFrequencies Q M) (centralFrequencies Q H)
    (intermediateFrequencies Q M H) A
    (fun n ↦ (Q / n : ZMod Q)) p (Q : ZMod Q)
    (fun h n ↦ reciprocalAngle h n)
  · exact (central_union_intermediate Q M H hHM).symm
  · exact disjoint_central_intermediate Q M H
  · exact hp0
  · exact hp1
  · intro h hh n hn
    exact stdAddChar_clearedReciprocal (hApos n hn) (hAdvd n hn) h
  · intro h hh
    exact expectationPhase_reciprocalAngle A p h hApos hmean
  · exact hcentralAngle
  · exact hcentralCubic
  · exact hintermediate

/-- The central Taylor hypotheses follow from the source interval
`A ⊆ [M,N]` and one explicit scale inequality.  This is the finite form of
the estimate `|A| (2*pi*H/M)^3 = o(1)`. -/
lemma reciprocal_central_budgets
    {Q M N H : ℕ} [NeZero Q] (hM : 0 < M)
    (A : Finset ℕ) (hA : A ⊆ Finset.Icc M N)
    (hangleNum : 2 * Real.pi * (H : ℝ) ≤ (M : ℝ))
    (hcubicNum :
      2 * (A.card : ℝ) *
        (2 * Real.pi * (H : ℝ) / (M : ℝ)) ^ 3 ≤ (1 / 7 : ℝ)) :
    (∀ h ∈ centralFrequencies Q H, ∀ n ∈ A,
        |reciprocalAngle h n| ≤ 1) ∧
      (∀ h ∈ centralFrequencies Q H,
        2 * ∑ n ∈ A, |reciprocalAngle h n| ^ 3 ≤ (1 / 7 : ℝ)) := by
  have hMreal : (0 : ℝ) < M := by exact_mod_cast hM
  constructor
  · intro h hh n hn
    have hk : h.valMinAbs.natAbs ≤ H := by
      simpa [centralFrequencies] using (Finset.mem_filter.mp hh).2
    have hnM : M ≤ n := (Finset.mem_Icc.mp (hA hn)).1
    have hnpos : 0 < n := hM.trans_le hnM
    rw [abs_reciprocalAngle h hnpos]
    apply (div_le_iff₀ (by exact_mod_cast hnpos : (0 : ℝ) < n)).2
    have hkR : (h.valMinAbs.natAbs : ℝ) ≤ H := by exact_mod_cast hk
    calc
      2 * Real.pi * (h.valMinAbs.natAbs : ℝ) ≤
          2 * Real.pi * (H : ℝ) :=
        mul_le_mul_of_nonneg_left hkR (by positivity)
      _ ≤ (M : ℝ) := hangleNum
      _ ≤ (n : ℝ) := by exact_mod_cast hnM
      _ = 1 * (n : ℝ) := by ring
  · intro h hh
    have hk : h.valMinAbs.natAbs ≤ H := by
      simpa [centralFrequencies] using (Finset.mem_filter.mp hh).2
    have hkR : (h.valMinAbs.natAbs : ℝ) ≤ H := by exact_mod_cast hk
    have hpoint : ∀ n ∈ A,
        |reciprocalAngle h n| ≤
          2 * Real.pi * (H : ℝ) / (M : ℝ) := by
      intro n hn
      have hnM : M ≤ n := (Finset.mem_Icc.mp (hA hn)).1
      have hnpos : 0 < n := hM.trans_le hnM
      rw [abs_reciprocalAngle h hnpos]
      calc
        2 * Real.pi * (h.valMinAbs.natAbs : ℝ) / (n : ℝ) ≤
            2 * Real.pi * (H : ℝ) / (n : ℝ) :=
          div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_left hkR (by positivity))
            (by positivity : (0 : ℝ) ≤ n)
        _ ≤ 2 * Real.pi * (H : ℝ) / (M : ℝ) :=
          div_le_div_of_nonneg_left (by positivity) hMreal
            (by exact_mod_cast hnM)
    calc
      2 * ∑ n ∈ A, |reciprocalAngle h n| ^ 3 ≤
          2 * ∑ _n ∈ A,
            (2 * Real.pi * (H : ℝ) / (M : ℝ)) ^ 3 := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        apply Finset.sum_le_sum
        intro n hn
        exact pow_le_pow_left₀ (abs_nonneg _) (hpoint n hn) 3
      _ = 2 * (A.card : ℝ) *
          (2 * Real.pi * (H : ℝ) / (M : ℝ)) ^ 3 := by
        rw [Finset.sum_const, nsmul_eq_mul]
        ring
      _ ≤ 1 / 7 := hcubicNum

/-- The finite intermediate-arc estimate, reduced to one explicit numerical
inequality.  On this range `H < |h| ≤ M/2`; since every denominator lies
in `[M,N]`, its circle distance is at least `H/N`. -/
lemma reciprocal_intermediate_budget
    {Q M N H : ℕ} [NeZero Q] (hM : 0 < M) (hMN : M ≤ N)
    (A : Finset ℕ) (hA : A ⊆ Finset.Icc M N)
    (p : ℕ → ℝ) (delta : ℝ) (hdelta : 0 ≤ delta)
    (hpLower : ∀ n ∈ A, delta ≤ p n)
    (hpUpper : ∀ n ∈ A, p n ≤ 1 / 2)
    (hnum :
      ((M + 1 : ℕ) : ℝ) * Real.exp (-(4 * delta * (A.card : ℝ) *
        (H : ℝ) ^ 2 / (N : ℝ) ^ 2)) ≤ (1 / 4 : ℝ)) :
    ∑ h ∈ intermediateFrequencies Q M H,
        Real.exp (-(8 * ∑ n ∈ A, p n * (1 - p n) *
          circleDistance (reciprocalAngle h n / (2 * Real.pi)) ^ 2)) ≤
      (1 / 4 : ℝ) := by
  have hN : 0 < N := hM.trans_le hMN
  have hpoint : ∀ h ∈ intermediateFrequencies Q M H,
      Real.exp (-(8 * ∑ n ∈ A, p n * (1 - p n) *
          circleDistance (reciprocalAngle h n / (2 * Real.pi)) ^ 2)) ≤
        Real.exp (-(4 * delta * (A.card : ℝ) *
          (H : ℝ) ^ 2 / (N : ℝ) ^ 2)) := by
    intro h hh
    have hhMajor := (Finset.mem_sdiff.mp hh).1
    have hhNotCentral := (Finset.mem_sdiff.mp hh).2
    have hkUpper : h.valMinAbs.natAbs ≤ M / 2 := by
      simpa [majorFrequencies] using (Finset.mem_filter.mp hhMajor).2
    have hkLower : H ≤ h.valMinAbs.natAbs := by
      have : ¬ h.valMinAbs.natAbs ≤ H := by
        intro hk
        apply hhNotCentral
        simp only [centralFrequencies, Finset.mem_filter]
        exact ⟨(Finset.mem_filter.mp hhMajor).1, hk⟩
      omega
    have hterm : ∀ n ∈ A,
        delta / 2 * ((H : ℝ) / N) ^ 2 ≤
          p n * (1 - p n) *
            circleDistance (reciprocalAngle h n / (2 * Real.pi)) ^ 2 := by
      intro n hn
      have hnIcc := Finset.mem_Icc.mp (hA hn)
      have hnpos : 0 < n := hM.trans_le hnIcc.1
      have hangle : |reciprocalAngle h n| ≤ Real.pi := by
        rw [abs_reciprocalAngle h hnpos]
        apply (div_le_iff₀ (by exact_mod_cast hnpos : (0 : ℝ) < n)).2
        have htwok : 2 * h.valMinAbs.natAbs ≤ n := by
          exact (by omega : 2 * h.valMinAbs.natAbs ≤ M).trans hnIcc.1
        have htwokR : (2 : ℝ) * h.valMinAbs.natAbs ≤ n := by
          exact_mod_cast htwok
        nlinarith [Real.pi_pos]
      have hcircle :
          circleDistance (reciprocalAngle h n / (2 * Real.pi)) =
            (h.valMinAbs.natAbs : ℝ) / n := by
        rw [circleDistance_div_two_pi hangle,
          abs_reciprocalAngle h hnpos]
        field_simp [Real.pi_ne_zero]
      have hfrac : (H : ℝ) / N ≤
          (h.valMinAbs.natAbs : ℝ) / n := by
        calc
          (H : ℝ) / N ≤ (H : ℝ) / n :=
            div_le_div_of_nonneg_left (by positivity)
              (by exact_mod_cast hnpos : (0 : ℝ) < n)
              (by exact_mod_cast hnIcc.2 : (n : ℝ) ≤ N)
          _ ≤ (h.valMinAbs.natAbs : ℝ) / n :=
            div_le_div_of_nonneg_right (by exact_mod_cast hkLower)
              (by positivity)
      have hvariance : delta / 2 ≤ p n * (1 - p n) := by
        have hlower := hpLower n hn
        have hupper := hpUpper n hn
        nlinarith
      rw [hcircle]
      exact mul_le_mul hvariance
        (pow_le_pow_left₀ (by positivity) hfrac 2)
        (sq_nonneg _) (by
          have hlower := hpLower n hn
          have hupper := hpUpper n hn
          nlinarith)
    have hsum :
        (A.card : ℝ) * (delta / 2 * ((H : ℝ) / N) ^ 2) ≤
          ∑ n ∈ A, p n * (1 - p n) *
            circleDistance (reciprocalAngle h n / (2 * Real.pi)) ^ 2 := by
      calc
        (A.card : ℝ) * (delta / 2 * ((H : ℝ) / N) ^ 2) =
            ∑ _n ∈ A, delta / 2 * ((H : ℝ) / N) ^ 2 := by
          rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ _ := Finset.sum_le_sum fun n hn ↦ hterm n hn
    apply Real.exp_le_exp.mpr
    have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
    have hrearrange :
        4 * delta * (A.card : ℝ) * (H : ℝ) ^ 2 / (N : ℝ) ^ 2 =
          8 * ((A.card : ℝ) *
            (delta / 2 * ((H : ℝ) / N) ^ 2)) := by
      field_simp
      ring
    rw [hrearrange]
    exact neg_le_neg (mul_le_mul_of_nonneg_left hsum (by norm_num))
  calc
    ∑ h ∈ intermediateFrequencies Q M H,
        Real.exp (-(8 * ∑ n ∈ A, p n * (1 - p n) *
          circleDistance (reciprocalAngle h n / (2 * Real.pi)) ^ 2)) ≤
        ∑ _h ∈ intermediateFrequencies Q M H,
          Real.exp (-(4 * delta * (A.card : ℝ) *
            (H : ℝ) ^ 2 / (N : ℝ) ^ 2)) :=
      Finset.sum_le_sum fun h hh ↦ hpoint h hh
    _ = ((intermediateFrequencies Q M H).card : ℝ) *
        Real.exp (-(4 * delta * (A.card : ℝ) *
          (H : ℝ) ^ 2 / (N : ℝ) ^ 2)) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((M + 1 : ℕ) : ℝ) *
        Real.exp (-(4 * delta * (A.card : ℝ) *
          (H : ℝ) ^ 2 / (N : ℝ) ^ 2)) := by
      apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
      exact_mod_cast (Finset.card_le_card (Finset.sdiff_subset.trans
        (by rfl : majorFrequencies Q M ⊆ majorFrequencies Q M))).trans
          (majorFrequencies_card_le_add_one Q M)
    _ ≤ 1 / 4 := hnum

/-! ## Eventual source-scale estimates -/

lemma centralCutoff_le_rpow (N : ℕ) :
    (centralCutoff N : ℝ) ≤ (N : ℝ) ^ ((3 : ℝ) / 5) := by
  exact Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg N) _)

lemma eventually_half_rpow_le_centralCutoff :
    ∀ᶠ N : ℕ in atTop,
      (N : ℝ) ^ ((3 : ℝ) / 5) / 2 ≤ (centralCutoff N : ℝ) := by
  have ht : Tendsto (fun N : ℕ ↦ (N : ℝ) ^ ((3 : ℝ) / 5))
      atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < (3 : ℝ) / 5)).comp
      tendsto_natCast_atTop_atTop
  filter_upwards [ht.eventually_ge_atTop 2] with N hN
  exact half_le_floor hN

lemma eventually_centralCutoff_le_half_M :
    ∀ᶠ N : ℕ in atTop, centralCutoff N ≤ M N / 2 := by
  have ht : Tendsto (fun N : ℕ ↦ (N : ℝ) ^ ((7 : ℝ) / 20))
      atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < (7 : ℝ) / 20)).comp
      tendsto_natCast_atTop_atTop
  filter_upwards [GoodSetDensity.eventually_nineteenTwentiethPower_le_M,
    eventually_pos_scales, ht.eventually_ge_atTop 2] with N hM hscales hlarge
  have hNpos := hscales.1
  have hcut := centralCutoff_le_rpow N
  have hreal : 2 * (centralCutoff N : ℝ) ≤ (M N : ℝ) := by
    calc
      2 * (centralCutoff N : ℝ) ≤
          2 * (N : ℝ) ^ ((3 : ℝ) / 5) :=
        mul_le_mul_of_nonneg_left hcut (by norm_num)
      _ ≤ (N : ℝ) ^ ((7 : ℝ) / 20) *
          (N : ℝ) ^ ((3 : ℝ) / 5) :=
        mul_le_mul_of_nonneg_right hlarge (Real.rpow_nonneg hNpos.le _)
      _ = (N : ℝ) ^ ((19 : ℝ) / 20) := by
        rw [← Real.rpow_add hNpos]
        norm_num
      _ ≤ (M N : ℝ) := hM
  exact (Nat.le_div_iff_mul_le (by norm_num : 0 < 2)).2 (by
    simpa [mul_comm] using
      (show 2 * centralCutoff N ≤ M N by exact_mod_cast hreal))

lemma eventually_logLog_inv_ge_small_rpow :
    ∀ᶠ N : ℕ in atTop,
      (N : ℝ) ^ (-((1 : ℝ) / 100)) ≤ (logLogScale N)⁻¹ := by
  have hlittle :=
    ((isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < (1 : ℝ) / 100)).comp_tendsto
      tendsto_natCast_atTop_atTop).eventuallyLE
  filter_upwards [hlittle, eventually_pos_scales] with N hlog hscales
  rcases hscales with ⟨hNpos, hL, hLL, hLLL⟩
  have hlogNonneg : 0 ≤ Real.log (N : ℝ) := by
    simpa [logScale] using (zero_le_one.trans hL.le)
  have hpowpos : 0 < (N : ℝ) ^ ((1 : ℝ) / 100) :=
    Real.rpow_pos_of_pos hNpos _
  have hLLpos : 0 < logLogScale N := zero_lt_one.trans hLL
  have hLbound : logScale N ≤ (N : ℝ) ^ ((1 : ℝ) / 100) := by
    simpa [Function.comp_apply, logScale,
      Real.norm_of_nonneg hlogNonneg,
      Real.norm_of_nonneg (Real.rpow_nonneg hNpos.le _)] using hlog
  have hLLleL : logLogScale N ≤ logScale N := by
    dsimp [logLogScale]
    exact (Real.log_le_sub_one_of_pos (zero_lt_one.trans hL)).trans (by linarith)
  have hLLbound : logLogScale N ≤ (N : ℝ) ^ ((1 : ℝ) / 100) :=
    hLLleL.trans hLbound
  rw [Real.rpow_neg hNpos.le]
  exact (inv_le_inv₀ hpowpos hLLpos).2 hLLbound

/-- The active-LCM major-frequency block for the normalized source measure.
The local `NeZero` instance is deliberately encapsulated here: the active
LCM is positive for every finite denominator set. -/
noncomputable def normalizedMajorBlock (lam : ℝ) (N : ℕ) : ℂ := by
  let A := Erdos297.LogisticNormalization.goodSet N
  let Q := Erdos297.ActiveLcm.activeLcm A
  letI : NeZero Q := ⟨Erdos297.ActiveLcm.activeLcm_ne_zero A⟩
  exact fourierBlock (majorFrequencies Q (M N)) A
    (fun n ↦ (Q / n : ZMod Q))
    (Erdos297.LogisticNormalization.normalizedLogisticProbability lam N)
    (Q : ZMod Q)

end

end Erdos297.MajorArc

#print axioms Erdos297.MajorArc.weighted_majorArc_lower
