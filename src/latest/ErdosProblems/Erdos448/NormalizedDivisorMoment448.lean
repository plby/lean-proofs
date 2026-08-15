import ErdosProblems.Erdos448.Lemma4FirstMoment448
import ErdosProblems.Erdos448.HalberstamComplete448
import ErdosProblems.Erdos448.MertensEulerProduct448

open scoped BigOperators Topology
open Filter Finset

namespace NormalizedDivisorMoment448

attribute [local instance] Classical.propDecidable

open Lemma4FirstMoment448

/-- The fixed-cutoff normalized divisor moment used in the upper-tail
argument.  The value at zero is zero, as for the underlying arithmetic
function. -/
noncomputable def fixedMoment (Y n : ℕ) : ℝ :=
  divisorMoment (6 / 5) (Y : ℝ) n

@[simp] lemma fixedMoment_zero (Y : ℕ) : fixedMoment Y 0 = 0 := by
  simp [fixedMoment]

@[simp] lemma fixedMoment_one (Y : ℕ) : fixedMoment Y 1 = 1 := by
  simp [fixedMoment]

lemma fixedMoment_nonneg (Y n : ℕ) : 0 ≤ fixedMoment Y n := by
  exact divisorMoment_nonneg (by norm_num) (Y : ℝ) n

lemma fixedMoment_mul {a b : ℕ} (hab : a.Coprime b) (Y : ℕ) :
    fixedMoment Y (a * b) = fixedMoment Y a * fixedMoment Y b := by
  exact divisorMoment_mul hab (6 / 5) (Y : ℝ)

lemma fixedMoment_prime_pow (Y : ℕ) {p j : ℕ} (hp : p.Prime) :
    fixedMoment Y (p ^ j) =
      (∑ i ∈ Finset.range (j + 1),
        (6 / 5 : ℝ) ^ (if p < Y then i else 0)) / (j + 1 : ℝ) := by
  unfold fixedMoment
  rw [divisorMoment_prime_pow (6 / 5) (Y : ℝ) hp]
  have hcast : ((p : ℝ) < (Y : ℝ)) = (p < Y) :=
    propext (by norm_cast)
  simp only [hcast]

lemma fixedMoment_prime_pow_eq_one_of_not_lt (Y : ℕ) {p j : ℕ}
    (hp : p.Prime) (hpY : ¬p < Y) :
    fixedMoment Y (p ^ j) = 1 := by
  rw [fixedMoment_prime_pow Y hp]
  simp [hpY, show (j + 1 : ℝ) ≠ 0 by positivity]

lemma fixedMoment_prime (Y : ℕ) {p : ℕ} (hp : p.Prime) (hpY : p < Y) :
    fixedMoment Y p = (11 / 10 : ℝ) := by
  simpa [fixedMoment_prime_pow Y hp, hpY] using
    (show fixedMoment Y (p ^ 1) = (11 / 10 : ℝ) by
      rw [fixedMoment_prime_pow Y hp]
      simp [hpY]
      norm_num)

lemma fixedMoment_prime_pow_le_pow (Y : ℕ) {p j : ℕ} (hp : p.Prime) :
    fixedMoment Y (p ^ j) ≤ (6 / 5 : ℝ) ^ j := by
  rw [fixedMoment_prime_pow Y hp]
  have hterm : ∀ i ∈ Finset.range (j + 1),
      (6 / 5 : ℝ) ^ (if p < Y then i else 0) ≤ (6 / 5 : ℝ) ^ j := by
    intro i hi
    by_cases hpY : p < Y
    · simp only [if_pos hpY]
      exact pow_le_pow_right₀ (by norm_num)
        (Nat.le_of_lt_succ (Finset.mem_range.mp hi))
    · simp only [if_neg hpY, pow_zero]
      exact one_le_pow₀ (by norm_num)
  have hsum := Finset.sum_le_sum hterm
  calc
    (∑ i ∈ Finset.range (j + 1),
        (6 / 5 : ℝ) ^ (if p < Y then i else 0)) / (j + 1 : ℝ)
        ≤ (∑ _i ∈ Finset.range (j + 1), (6 / 5 : ℝ) ^ j) /
            (j + 1 : ℝ) := div_le_div_of_nonneg_right hsum (by positivity)
    _ = (6 / 5 : ℝ) ^ j := by
      simp [show (j + 1 : ℝ) ≠ 0 by positivity]

lemma fixedMoment_prime_pow_succ_le (Y : ℕ) {p : ℕ} (hp : p.Prime)
    (j : ℕ) :
    fixedMoment Y (p ^ (j + 1)) ≤
      (6 / 5 : ℝ) * (6 / 5 : ℝ) ^ j := by
  simpa [pow_succ'] using fixedMoment_prime_pow_le_pow Y hp (j := j + 1)

/-- Absolute summability of every local Euler factor. -/
lemma fixedMoment_local_summable (Y : ℕ) {p : ℕ} (hp : p.Prime) :
    Summable (fun j : ℕ =>
      ‖fixedMoment Y (p ^ j) / ((p ^ j : ℕ) : ℝ)‖) := by
  exact (HalberstamScratch.prime_power_local_mass
    (fixedMoment Y) p (6 / 5) (6 / 5) hp
    (fixedMoment_nonneg Y) (fixedMoment_one Y)
    (by norm_num) (by norm_num) (by norm_num)
    (fixedMoment_prime_pow_succ_le Y hp)).1

lemma fixedMoment_local_summable_plain (Y : ℕ) {p : ℕ} (hp : p.Prime) :
    Summable (fun j : ℕ =>
      fixedMoment Y (p ^ j) / ((p ^ j : ℕ) : ℝ)) := by
  exact (fixedMoment_local_summable Y hp).of_norm

/-- The exact local Euler factor away from the cutoff. -/
lemma fixedMoment_local_eq_ge_cutoff (Y : ℕ) {p : ℕ} (hp : p.Prime)
    (hpY : ¬p < Y) :
    (∑' j : ℕ, fixedMoment Y (p ^ j) / ((p ^ j : ℕ) : ℝ)) =
      (1 - 1 / (p : ℝ))⁻¹ := by
  have hpR : 0 < (p : ℝ) := by exact_mod_cast hp.pos
  have hr0 : 0 ≤ (1 / (p : ℝ)) := by positivity
  have hr1 : (1 / (p : ℝ)) < 1 := by
    exact (div_lt_one hpR).mpr (by exact_mod_cast hp.one_lt)
  calc
    (∑' j : ℕ, fixedMoment Y (p ^ j) / ((p ^ j : ℕ) : ℝ)) =
        ∑' j : ℕ, (1 / (p : ℝ)) ^ j := by
      apply tsum_congr
      intro j
      rw [fixedMoment_prime_pow_eq_one_of_not_lt Y hp hpY, Nat.cast_pow]
      simp only [one_div, inv_pow]
    _ = (1 - 1 / (p : ℝ))⁻¹ :=
      (hasSum_geometric_of_lt_one hr0 hr1).tsum_eq

/-- A tail estimate retaining the exact first prime coefficient. -/
lemma fixedMoment_local_tail_two_le (Y : ℕ) {p : ℕ} (hp : p.Prime) :
    (∑' j : ℕ,
      fixedMoment Y (p ^ (j + 2)) / ((p ^ (j + 2) : ℕ) : ℝ)) ≤
      ((6 / 5 : ℝ) / p) ^ 2 /
        (1 - (6 / 5 : ℝ) / p) := by
  have hpR : 0 < (p : ℝ) := by exact_mod_cast hp.pos
  have hpTwo : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  let r : ℝ := (6 / 5 : ℝ) / p
  have hr0 : 0 ≤ r := by dsimp [r]; positivity
  have hr1 : r < 1 := by
    dsimp [r]
    apply (div_lt_one hpR).mpr
    exact (show (6 / 5 : ℝ) < 2 by norm_num).trans_le hpTwo
  have hmajor : Summable (fun j : ℕ => r ^ (j + 2)) := by
    exact ((summable_geometric_of_lt_one hr0 hr1).mul_left (r ^ 2)).congr
      (fun j => by rw [pow_add]; ring)
  have hpoint : ∀ j : ℕ,
      fixedMoment Y (p ^ (j + 2)) / ((p ^ (j + 2) : ℕ) : ℝ) ≤
        r ^ (j + 2) := by
    intro j
    calc
      fixedMoment Y (p ^ (j + 2)) / ((p ^ (j + 2) : ℕ) : ℝ)
          ≤ (6 / 5 : ℝ) ^ (j + 2) / ((p ^ (j + 2) : ℕ) : ℝ) :=
        div_le_div_of_nonneg_right
          (fixedMoment_prime_pow_le_pow Y hp) (by positivity)
      _ = r ^ (j + 2) := by
        dsimp [r]
        rw [Nat.cast_pow, ← div_pow]
  have htail : Summable (fun j : ℕ =>
      fixedMoment Y (p ^ (j + 2)) / ((p ^ (j + 2) : ℕ) : ℝ)) :=
    ((summable_nat_add_iff 2).mpr (fixedMoment_local_summable_plain Y hp))
  calc
    (∑' j : ℕ,
      fixedMoment Y (p ^ (j + 2)) / ((p ^ (j + 2) : ℕ) : ℝ)) ≤
        ∑' j : ℕ, r ^ (j + 2) := htail.tsum_le_tsum hpoint hmajor
    _ = r ^ 2 / (1 - r) := by
      rw [show (fun j : ℕ => r ^ (j + 2)) = fun j => r ^ 2 * r ^ j by
        funext j; rw [pow_add]; ring]
      rw [tsum_mul_left]
      rw [(hasSum_geometric_of_lt_one hr0 hr1).tsum_eq]
      ring
    _ = ((6 / 5 : ℝ) / p) ^ 2 /
        (1 - (6 / 5 : ℝ) / p) := rfl

lemma geometric_tail_bound {p : ℕ} (hp : p.Prime) :
    ((6 / 5 : ℝ) / p) ^ 2 / (1 - (6 / 5 : ℝ) / p) ≤
      (18 / 5 : ℝ) / (p : ℝ) ^ 2 := by
  have hpR : 0 < (p : ℝ) := by exact_mod_cast hp.pos
  have hpTwo : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hden : 0 < 1 - (6 / 5 : ℝ) / p := by
    rw [sub_pos, div_lt_one hpR]
    exact (show (6 / 5 : ℝ) < 2 by norm_num).trans_le hpTwo
  rw [div_le_iff₀ hden]
  have hpne : (p : ℝ) ≠ 0 := ne_of_gt hpR
  field_simp [hpne]
  nlinarith

lemma one_add_inv_le_geometric {p : ℕ} (hp : p.Prime) :
    1 + 1 / (p : ℝ) ≤ (1 - 1 / (p : ℝ))⁻¹ := by
  have hpR : 0 < (p : ℝ) := by exact_mod_cast hp.pos
  have hpOne : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hden : 0 < 1 - 1 / (p : ℝ) := by
    rw [sub_pos, div_lt_one hpR]
    exact hpOne
  rw [inv_eq_one_div, le_div_iff₀ hden]
  have hpne : (p : ℝ) ≠ 0 := ne_of_gt hpR
  field_simp [hpne]
  nlinarith

noncomputable def localCorrection (Y p : ℕ) : ℝ :=
  if p < Y then
    1 + (1 / 10 : ℝ) / p + (18 / 5 : ℝ) / (p : ℝ) ^ 2
  else 1

lemma localCorrection_nonneg (Y p : ℕ) : 0 ≤ localCorrection Y p := by
  unfold localCorrection
  split_ifs <;> positivity

lemma localCorrection_eq_one_of_not_lt {Y p : ℕ} (hpY : ¬p < Y) :
    localCorrection Y p = 1 := by simp [localCorrection, hpY]

lemma fixedMoment_local_split (Y : ℕ) {p : ℕ} (hp : p.Prime)
    (hpY : p < Y) :
    (∑' j : ℕ, fixedMoment Y (p ^ j) / ((p ^ j : ℕ) : ℝ)) =
      1 + (11 / 10 : ℝ) / p +
        ∑' j : ℕ,
          fixedMoment Y (p ^ (j + 2)) / ((p ^ (j + 2) : ℕ) : ℝ) := by
  let f : ℕ → ℝ := fun j =>
    fixedMoment Y (p ^ j) / ((p ^ j : ℕ) : ℝ)
  have hf : Summable f := fixedMoment_local_summable_plain Y hp
  rw [← hf.sum_add_tsum_nat_add 2]
  change (∑ i ∈ Finset.range 2, f i) + ∑' i : ℕ, f (i + 2) = _
  have hprime : fixedMoment Y p = (11 / 10 : ℝ) :=
    fixedMoment_prime Y hp hpY
  rw [Finset.sum_range_succ, Finset.sum_range_succ]
  norm_num [f, hprime, fixedMoment_one, Nat.add_comm]

/-- Sharp local-factor majorant.  Its first correction coefficient is exactly
`1/10`; all prime-power terms of degree at least two are absorbed into an
absolutely summable reciprocal-square correction. -/
lemma fixedMoment_localFactor_le (Y : ℕ) {p : ℕ} (hp : p.Prime) :
    (∑' j : ℕ, fixedMoment Y (p ^ j) / ((p ^ j : ℕ) : ℝ)) ≤
      (1 - 1 / (p : ℝ))⁻¹ * localCorrection Y p := by
  by_cases hpY : p < Y
  · rw [fixedMoment_local_split Y hp hpY]
    have htail := fixedMoment_local_tail_two_le Y hp
    have htail' :
        (∑' j : ℕ,
          fixedMoment Y (p ^ (j + 2)) / ((p ^ (j + 2) : ℕ) : ℝ)) ≤
          (18 / 5 : ℝ) / (p : ℝ) ^ 2 :=
      htail.trans (geometric_tail_bound hp)
    have hbase := one_add_inv_le_geometric hp
    have hpR : 0 < (p : ℝ) := by exact_mod_cast hp.pos
    have hbaseOne : (1 : ℝ) ≤ (1 - 1 / (p : ℝ))⁻¹ :=
      le_trans (by
        have hinv : 0 ≤ 1 / (p : ℝ) := by positivity
        linarith) hbase
    have hu : 0 ≤ (1 / 10 : ℝ) / p + (18 / 5 : ℝ) / (p : ℝ) ^ 2 := by
      positivity
    rw [localCorrection, if_pos hpY]
    calc
      1 + (11 / 10 : ℝ) / p +
          ∑' j : ℕ,
            fixedMoment Y (p ^ (j + 2)) / ((p ^ (j + 2) : ℕ) : ℝ)
          ≤ 1 + (11 / 10 : ℝ) / p +
              (18 / 5 : ℝ) / (p : ℝ) ^ 2 := by linarith
      _ = (1 + 1 / (p : ℝ)) +
          ((1 / 10 : ℝ) / p + (18 / 5 : ℝ) / (p : ℝ) ^ 2) := by ring
      _ ≤ (1 - 1 / (p : ℝ))⁻¹ +
          ((1 / 10 : ℝ) / p + (18 / 5 : ℝ) / (p : ℝ) ^ 2) :=
        add_le_add hbase le_rfl
      _ ≤ (1 - 1 / (p : ℝ))⁻¹ *
          (1 + (1 / 10 : ℝ) / p + (18 / 5 : ℝ) / (p : ℝ) ^ 2) := by
        nlinarith
  · rw [fixedMoment_local_eq_ge_cutoff Y hp hpY,
      localCorrection_eq_one_of_not_lt hpY, mul_one]

noncomputable def correctionExponent (Y p : ℕ) : ℝ :=
  if p < Y then
    (1 / 10 : ℝ) / p + (18 / 5 : ℝ) / (p : ℝ) ^ 2
  else 0

lemma localCorrection_eq_one_add (Y p : ℕ) :
    localCorrection Y p = 1 + correctionExponent Y p := by
  unfold localCorrection correctionExponent
  split_ifs <;> ring

lemma correctionExponent_nonneg (Y p : ℕ) :
    0 ≤ correctionExponent Y p := by
  unfold correctionExponent
  split_ifs <;> positivity

lemma prime_inv_sq_le_correction {p : ℕ} (hp : p.Prime) :
    1 / (p : ℝ) ^ 2 ≤
      (((p : ℝ) * ((p : ℝ) - 1))⁻¹) := by
  have hpR : 0 < (p : ℝ) := by exact_mod_cast hp.pos
  have hpOne : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hsmall : 0 < (p : ℝ) * ((p : ℝ) - 1) :=
    mul_pos hpR (sub_pos.mpr hpOne)
  simpa only [one_div] using
    (one_div_le_one_div_of_le hsmall (by nlinarith) :
      1 / (p : ℝ) ^ 2 ≤ 1 / ((p : ℝ) * ((p : ℝ) - 1)))

lemma correctionExponent_sum_le (N Y : ℕ) :
    (∑ p ∈ (N + 1).primesBelow, correctionExponent Y p) ≤
      (1 / 10 : ℝ) *
          (∑ p ∈ (Finset.Icc 1 Y).filter Nat.Prime, (p : ℝ)⁻¹) +
        18 / 5 := by
  let S := ((N + 1).primesBelow).filter fun p => p < Y
  let P := (Finset.Icc 1 Y).filter Nat.Prime
  have hsubset : S ⊆ P := by
    intro p hp
    have hp' := Finset.mem_filter.mp hp
    have hprime := Nat.prime_of_mem_primesBelow hp'.1
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr ⟨hprime.one_le, hp'.2.le⟩, hprime⟩
  have hinv :
      (∑ p ∈ S, (p : ℝ)⁻¹) ≤ ∑ p ∈ P, (p : ℝ)⁻¹ := by
    exact Finset.sum_le_sum_of_subset_of_nonneg hsubset
      (fun p hp hnot => inv_nonneg.mpr (Nat.cast_nonneg p))
  have hinvSq :
      (∑ p ∈ S, 1 / (p : ℝ) ^ 2) ≤ 1 := by
    calc
      (∑ p ∈ S, 1 / (p : ℝ) ^ 2) ≤
          ∑ p ∈ S, (((p : ℝ) * ((p : ℝ) - 1))⁻¹) := by
        apply Finset.sum_le_sum
        intro p hp
        exact prime_inv_sq_le_correction
          (Nat.prime_of_mem_primesBelow (Finset.mem_filter.mp hp).1)
      _ ≤ ∑ p ∈ P, (((p : ℝ) * ((p : ℝ) - 1))⁻¹) := by
        refine Finset.sum_le_sum_of_subset_of_nonneg hsubset ?_
        intro p hp hnot
        have hprime := (Finset.mem_filter.mp hp).2
        have hpR : (0 : ℝ) < p := by exact_mod_cast hprime.pos
        have hpOne : (1 : ℝ) < p := by exact_mod_cast hprime.one_lt
        positivity
      _ ≤ 1 := by
        simpa [P] using Erdos448.prime_correction_sum_le_one Y
  have hrewrite :
      (∑ p ∈ (N + 1).primesBelow, correctionExponent Y p) =
        (1 / 10 : ℝ) * (∑ p ∈ S, (p : ℝ)⁻¹) +
          (18 / 5 : ℝ) * (∑ p ∈ S, 1 / (p : ℝ) ^ 2) := by
    calc
      (∑ p ∈ (N + 1).primesBelow, correctionExponent Y p) =
          ∑ p ∈ S, correctionExponent Y p := by
        symm
        apply Finset.sum_subset (Finset.filter_subset _ _)
        intro p hp hnot
        have hpY : ¬p < Y := by
          intro hpY
          exact hnot (Finset.mem_filter.mpr ⟨hp, hpY⟩)
        simp [correctionExponent, hpY]
      _ = ∑ p ∈ S,
          ((1 / 10 : ℝ) * (p : ℝ)⁻¹ +
            (18 / 5 : ℝ) * (1 / (p : ℝ) ^ 2)) := by
        apply Finset.sum_congr rfl
        intro p hp
        have hpY : p < Y := (Finset.mem_filter.mp hp).2
        rw [correctionExponent, if_pos hpY]
        ring
      _ = (1 / 10 : ℝ) * (∑ p ∈ S, (p : ℝ)⁻¹) +
          (18 / 5 : ℝ) * (∑ p ∈ S, 1 / (p : ℝ) ^ 2) := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
  rw [hrewrite]
  calc
    (1 / 10 : ℝ) * (∑ p ∈ S, (p : ℝ)⁻¹) +
        (18 / 5 : ℝ) * (∑ p ∈ S, 1 / (p : ℝ) ^ 2)
        ≤ (1 / 10 : ℝ) * (∑ p ∈ P, (p : ℝ)⁻¹) +
          (18 / 5 : ℝ) * 1 := by gcongr
    _ = (1 / 10 : ℝ) *
          (∑ p ∈ (Finset.Icc 1 Y).filter Nat.Prime, (p : ℝ)⁻¹) +
        18 / 5 := by simp [P]

lemma correctionProduct_le_exp (N Y : ℕ) :
    (∏ p ∈ (N + 1).primesBelow, localCorrection Y p) ≤
      Real.exp ((1 / 10 : ℝ) *
          (∑ p ∈ (Finset.Icc 1 Y).filter Nat.Prime, (p : ℝ)⁻¹) +
        18 / 5) := by
  rw [show (∏ p ∈ (N + 1).primesBelow, localCorrection Y p) =
      ∏ p ∈ (N + 1).primesBelow, (1 + correctionExponent Y p) by
    apply Finset.prod_congr rfl
    intro p hp
    exact localCorrection_eq_one_add Y p]
  calc
    (∏ p ∈ (N + 1).primesBelow, (1 + correctionExponent Y p)) ≤
        Real.exp (∑ p ∈ (N + 1).primesBelow,
          correctionExponent Y p) :=
      Erdos448.finite_product_one_add_le_exp_sum _ _
        (fun p hp => correctionExponent_nonneg Y p)
    _ ≤ Real.exp ((1 / 10 : ℝ) *
          (∑ p ∈ (Finset.Icc 1 Y).filter Nat.Prime, (p : ℝ)⁻¹) +
        18 / 5) := Real.exp_le_exp.mpr (correctionExponent_sum_le N Y)

noncomputable def reciprocalPrimeSum (Y : ℕ) : ℝ :=
  ∑ p ∈ (Finset.Icc 1 Y).filter Nat.Prime, (p : ℝ)⁻¹

lemma exists_prime_reciprocal_threshold :
    ∃ Y₀ : ℕ, ∀ Y : ℕ, Y₀ ≤ Y →
      reciprocalPrimeSum Y ≤
        Real.log (Real.log (Y : ℝ)) + meissel_mertens + 1 := by
  rcases (eventually_atTop.1
      Erdos448.eventually_prime_reciprocal_sum_le_loglog_add_one) with
    ⟨Y₀, hY₀⟩
  exact ⟨Y₀, fun Y hY => by simpa [reciprocalPrimeSum] using hY₀ Y hY⟩

lemma reciprocalPrimeSum_mono {Y Z : ℕ} (hYZ : Y ≤ Z) :
    reciprocalPrimeSum Y ≤ reciprocalPrimeSum Z := by
  unfold reciprocalPrimeSum
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro p hp
    have hp' := Finset.mem_filter.mp hp
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr
        ⟨(Finset.mem_Icc.mp hp'.1).1,
          (Finset.mem_Icc.mp hp'.1).2.trans hYZ⟩,
        hp'.2⟩
  · intro p hp hnot
    exact inv_nonneg.mpr (Nat.cast_nonneg p)

lemma primesBelow_succ_eq_primeIcc (N : ℕ) :
    (N + 1).primesBelow = (Finset.Icc 1 N).filter Nat.Prime := by
  ext p
  rw [Nat.mem_primesBelow, Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨hpN, hp⟩
    exact ⟨⟨hp.one_le, Nat.le_of_lt_succ hpN⟩, hp⟩
  · rintro ⟨⟨hp1, hpN⟩, hp⟩
    exact ⟨Nat.lt_succ_of_le hpN, hp⟩

lemma inv_prime_pred_identity {p : ℕ} (hp : p.Prime) :
    1 / ((p : ℝ) - 1) = (p : ℝ)⁻¹ +
      (((p : ℝ) * ((p : ℝ) - 1))⁻¹) := by
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hpOne : (p : ℝ) - 1 ≠ 0 := by
    exact ne_of_gt (sub_pos.mpr (by exact_mod_cast hp.one_lt))
  field_simp [hpR, hpOne]
  ring

lemma baseline_local_eq_one_add {p : ℕ} (hp : p.Prime) :
    (1 - 1 / (p : ℝ))⁻¹ = 1 + 1 / ((p : ℝ) - 1) := by
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hpOne : (p : ℝ) - 1 ≠ 0 := by
    exact ne_of_gt (sub_pos.mpr (by exact_mod_cast hp.one_lt))
  field_simp [hpR, hpOne]
  ring

lemma sum_prime_inv_pred_le (N : ℕ) :
    (∑ p ∈ (N + 1).primesBelow, 1 / ((p : ℝ) - 1)) ≤
      reciprocalPrimeSum N + 1 := by
  rw [primesBelow_succ_eq_primeIcc]
  calc
    (∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime,
        1 / ((p : ℝ) - 1)) =
        ∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime,
          ((p : ℝ)⁻¹ + (((p : ℝ) * ((p : ℝ) - 1))⁻¹)) := by
      apply Finset.sum_congr rfl
      intro p hp
      exact inv_prime_pred_identity (Finset.mem_filter.mp hp).2
    _ = reciprocalPrimeSum N +
        ∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime,
          (((p : ℝ) * ((p : ℝ) - 1))⁻¹) := by
      rw [Finset.sum_add_distrib]
      rfl
    _ ≤ reciprocalPrimeSum N + 1 := by
      exact add_le_add le_rfl (Erdos448.prime_correction_sum_le_one N)

lemma baseEulerProduct_le_exp (N : ℕ) :
    (∏ p ∈ (N + 1).primesBelow,
      (1 - 1 / (p : ℝ))⁻¹) ≤
        Real.exp (reciprocalPrimeSum N + 1) := by
  rw [show (∏ p ∈ (N + 1).primesBelow,
      (1 - 1 / (p : ℝ))⁻¹) =
      ∏ p ∈ (N + 1).primesBelow, (1 + 1 / ((p : ℝ) - 1)) by
    apply Finset.prod_congr rfl
    intro p hp
    exact baseline_local_eq_one_add (Nat.prime_of_mem_primesBelow hp)]
  calc
    (∏ p ∈ (N + 1).primesBelow, (1 + 1 / ((p : ℝ) - 1))) ≤
        Real.exp (∑ p ∈ (N + 1).primesBelow,
          1 / ((p : ℝ) - 1)) := by
      apply Erdos448.finite_product_one_add_le_exp_sum
      intro p hp
      have hpPrime := Nat.prime_of_mem_primesBelow hp
      exact div_nonneg zero_le_one
        (sub_nonneg.mpr (by exact_mod_cast hpPrime.one_le))
    _ ≤ Real.exp (reciprocalPrimeSum N + 1) :=
      Real.exp_le_exp.mpr (sum_prime_inv_pred_le N)

lemma exists_baseEulerProduct_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 3 ≤ N →
      (∏ p ∈ (N + 1).primesBelow,
        (1 - 1 / (p : ℝ))⁻¹) ≤ C * Real.log (N : ℝ) := by
  rcases exists_prime_reciprocal_threshold with ⟨N₀, hN₀⟩
  let Clarge : ℝ := Real.exp (meissel_mertens + 2)
  let Csmall : ℝ := Real.exp (reciprocalPrimeSum N₀ + 1) / Real.log 3
  refine ⟨Clarge + Csmall, add_nonneg (by positivity) (by
    dsimp [Csmall]
    exact div_nonneg (Real.exp_pos _).le (Real.log_pos (by norm_num)).le), ?_⟩
  intro N hN
  have hraw := baseEulerProduct_le_exp N
  have hlogN : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  by_cases hlarge : N₀ ≤ N
  · have hrec := hN₀ N hlarge
    have hexp : Real.exp (reciprocalPrimeSum N + 1) ≤
        Clarge * Real.log (N : ℝ) := by
      calc
        Real.exp (reciprocalPrimeSum N + 1) ≤
            Real.exp (Real.log (Real.log (N : ℝ)) + meissel_mertens + 2) := by
          apply Real.exp_le_exp.mpr
          linarith
        _ = Clarge * Real.log (N : ℝ) := by
          dsimp [Clarge]
          rw [show Real.log (Real.log (N : ℝ)) + meissel_mertens + 2 =
              (meissel_mertens + 2) + Real.log (Real.log (N : ℝ)) by ring,
            Real.exp_add, Real.exp_log hlogN]
    exact hraw.trans (hexp.trans (by
      apply mul_le_mul_of_nonneg_right
      · exact le_add_of_nonneg_right (by
          dsimp [Csmall]
          exact div_nonneg (Real.exp_pos _).le
            (Real.log_pos (by norm_num)).le)
      · exact hlogN.le))
  · have hNle : N ≤ N₀ := Nat.le_of_not_ge hlarge
    have hrec := reciprocalPrimeSum_mono hNle
    have hlog3 : Real.log (3 : ℝ) ≤ Real.log (N : ℝ) := by
      exact Real.log_le_log (by norm_num) (by exact_mod_cast hN)
    have hexp : Real.exp (reciprocalPrimeSum N + 1) ≤
        Csmall * Real.log (N : ℝ) := by
      calc
        Real.exp (reciprocalPrimeSum N + 1) ≤
            Real.exp (reciprocalPrimeSum N₀ + 1) :=
          Real.exp_le_exp.mpr (by linarith)
        _ = Csmall * Real.log 3 := by
          dsimp [Csmall]
          rw [div_mul_cancel₀ _ (ne_of_gt (Real.log_pos (by norm_num)))]
        _ ≤ Csmall * Real.log (N : ℝ) := by
          apply mul_le_mul_of_nonneg_left hlog3
          dsimp [Csmall]
          exact div_nonneg (Real.exp_pos _).le
            (Real.log_pos (by norm_num)).le
    exact hraw.trans (hexp.trans (by
      apply mul_le_mul_of_nonneg_right
      · exact le_add_of_nonneg_left (by positivity : 0 ≤ Clarge)
      · exact hlogN.le))

noncomputable def baseEulerConstant : ℝ :=
  Classical.choose exists_baseEulerProduct_bound

lemma baseEulerConstant_nonneg : 0 ≤ baseEulerConstant :=
  (Classical.choose_spec exists_baseEulerProduct_bound).1

lemma baseEulerProduct_le (N : ℕ) (hN : 3 ≤ N) :
    (∏ p ∈ (N + 1).primesBelow,
      (1 - 1 / (p : ℝ))⁻¹) ≤
        baseEulerConstant * Real.log (N : ℝ) :=
  (Classical.choose_spec exists_baseEulerProduct_bound).2 N hN

lemma fixedMoment_eulerProduct_nonneg (N Y : ℕ) :
    0 ≤ ∏ p ∈ (N + 1).primesBelow,
      ∑' j : ℕ, fixedMoment Y (p ^ j) / ((p ^ j : ℕ) : ℝ) := by
  apply Finset.prod_nonneg
  intro p hp
  exact tsum_nonneg fun j =>
    div_nonneg (fixedMoment_nonneg Y _) (by positivity)

lemma fixedMoment_eulerProduct_le (N Y : ℕ) (hN : 3 ≤ N) :
    (∏ p ∈ (N + 1).primesBelow,
      ∑' j : ℕ, fixedMoment Y (p ^ j) / ((p ^ j : ℕ) : ℝ)) ≤
      baseEulerConstant * Real.log (N : ℝ) *
        Real.exp ((1 / 10 : ℝ) *
            (∑ p ∈ (Finset.Icc 1 Y).filter Nat.Prime, (p : ℝ)⁻¹) +
          18 / 5) := by
  let S := (N + 1).primesBelow
  have hfactor :
      (∏ p ∈ S,
        ∑' j : ℕ, fixedMoment Y (p ^ j) / ((p ^ j : ℕ) : ℝ)) ≤
        ∏ p ∈ S, ((1 - 1 / (p : ℝ))⁻¹ * localCorrection Y p) := by
    apply Finset.prod_le_prod
    · intro p hp
      exact tsum_nonneg fun j =>
        div_nonneg (fixedMoment_nonneg Y _) (by positivity)
    · intro p hp
      exact fixedMoment_localFactor_le Y
        (Nat.prime_of_mem_primesBelow hp)
  have hbaseNonneg :
      0 ≤ ∏ p ∈ S, (1 - 1 / (p : ℝ))⁻¹ := by
    apply Finset.prod_nonneg
    intro p hp
    have hpPrime := Nat.prime_of_mem_primesBelow hp
    have hpR : (0 : ℝ) < p := by exact_mod_cast hpPrime.pos
    have hpOne : (1 : ℝ) < p := by exact_mod_cast hpPrime.one_lt
    exact (inv_pos.mpr (sub_pos.mpr ((div_lt_one hpR).mpr hpOne))).le
  have hcorrectionNonneg :
      0 ≤ ∏ p ∈ S, localCorrection Y p :=
    Finset.prod_nonneg fun p hp => localCorrection_nonneg Y p
  calc
    (∏ p ∈ (N + 1).primesBelow,
        ∑' j : ℕ, fixedMoment Y (p ^ j) / ((p ^ j : ℕ) : ℝ))
        ≤ ∏ p ∈ S,
          ((1 - 1 / (p : ℝ))⁻¹ * localCorrection Y p) := hfactor
    _ = (∏ p ∈ S, (1 - 1 / (p : ℝ))⁻¹) *
          ∏ p ∈ S, localCorrection Y p := by
      rw [Finset.prod_mul_distrib]
    _ ≤ (baseEulerConstant * Real.log (N : ℝ)) *
        Real.exp ((1 / 10 : ℝ) *
            (∑ p ∈ (Finset.Icc 1 Y).filter Nat.Prime, (p : ℝ)⁻¹) +
          18 / 5) := by
      apply mul_le_mul
      · simpa [S] using baseEulerProduct_le N hN
      · simpa [S] using correctionProduct_le_exp N Y
      · exact hcorrectionNonneg
      · exact mul_nonneg baseEulerConstant_nonneg
          (Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega)))

noncomputable def hrMomentConstant : ℝ :=
  baseEulerConstant *
    (HalberstamScratch.explicitMassConstant (6 / 5) (6 / 5) + 1)

lemma hrMomentConstant_nonneg : 0 ≤ hrMomentConstant := by
  unfold hrMomentConstant
  have hmass := HalberstamScratch.explicitMassConstant_nonneg
    (show (0 : ℝ) ≤ 6 / 5 by norm_num)
    (show (0 : ℝ) ≤ 6 / 5 by norm_num)
  exact mul_nonneg baseEulerConstant_nonneg (by linarith)

/-- The unconditional HR estimate before inserting the prime-reciprocal
asymptotic. -/
theorem fixedMoment_partialSum_le_exp (N Y : ℕ) (hN : 3 ≤ N) :
    HalberstamScratch.partialSum (fixedMoment Y) N ≤
      hrMomentConstant * (N : ℝ) *
        Real.exp ((1 / 10 : ℝ) *
            (∑ p ∈ (Finset.Icc 1 Y).filter Nat.Prime, (p : ℝ)⁻¹) +
          18 / 5) := by
  have hHR := HalberstamComplete448.halberstam_richert_explicit
    (fixedMoment Y) (fixedMoment_zero Y) (fixedMoment_one Y)
    (fun {_m _n} hmn => fixedMoment_mul hmn Y)
    (fixedMoment_nonneg Y)
    (6 / 5) (6 / 5)
    (by norm_num) (by norm_num) (by norm_num)
    (fun p hp j => fixedMoment_prime_pow_succ_le Y hp j)
    N (by omega)
  have hEuler := fixedMoment_eulerProduct_le N Y hN
  have hlogPos : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hcoeff :
      0 ≤ (HalberstamScratch.explicitMassConstant (6 / 5) (6 / 5) + 1) *
        (N : ℝ) / Real.log (N : ℝ) := by
    have hmass := HalberstamScratch.explicitMassConstant_nonneg
      (show (0 : ℝ) ≤ 6 / 5 by norm_num)
      (show (0 : ℝ) ≤ 6 / 5 by norm_num)
    positivity
  calc
    HalberstamScratch.partialSum (fixedMoment Y) N ≤
        (HalberstamScratch.explicitMassConstant (6 / 5) (6 / 5) + 1) *
          (N : ℝ) / Real.log (N : ℝ) *
          ∏ p ∈ (N + 1).primesBelow,
            ∑' j : ℕ, fixedMoment Y (p ^ j) /
              ((p ^ j : ℕ) : ℝ) := hHR
    _ ≤ (HalberstamScratch.explicitMassConstant (6 / 5) (6 / 5) + 1) *
          (N : ℝ) / Real.log (N : ℝ) *
        (baseEulerConstant * Real.log (N : ℝ) *
          Real.exp ((1 / 10 : ℝ) *
              (∑ p ∈ (Finset.Icc 1 Y).filter Nat.Prime, (p : ℝ)⁻¹) +
            18 / 5)) :=
      mul_le_mul_of_nonneg_left hEuler hcoeff
    _ = hrMomentConstant * (N : ℝ) *
        Real.exp ((1 / 10 : ℝ) *
            (∑ p ∈ (Finset.Icc 1 Y).filter Nat.Prime, (p : ℝ)⁻¹) +
          18 / 5) := by
      unfold hrMomentConstant
      field_simp [ne_of_gt hlogPos]

noncomputable def primeAsymptoticConstant : ℝ :=
  Real.exp ((1 / 10 : ℝ) * (meissel_mertens + 1) + 18 / 5)

lemma primeAsymptoticConstant_pos : 0 < primeAsymptoticConstant := by
  exact Real.exp_pos _

lemma exp_reciprocalPrimeSum_le_log_rpow
    {Y : ℕ} (hY : 2 ≤ Y)
    (hrec : reciprocalPrimeSum Y ≤
      Real.log (Real.log (Y : ℝ)) + meissel_mertens + 1) :
    Real.exp ((1 / 10 : ℝ) * reciprocalPrimeSum Y + 18 / 5) ≤
      primeAsymptoticConstant *
        (Real.log (Y : ℝ)).rpow (1 / 10 : ℝ) := by
  have hlogY : 0 < Real.log (Y : ℝ) :=
    Real.log_pos (by exact_mod_cast hY)
  have hexp :
      Real.exp ((1 / 10 : ℝ) * reciprocalPrimeSum Y + 18 / 5) ≤
        Real.exp ((1 / 10 : ℝ) *
          (Real.log (Real.log (Y : ℝ)) + meissel_mertens + 1) + 18 / 5) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  calc
    Real.exp ((1 / 10 : ℝ) * reciprocalPrimeSum Y + 18 / 5) ≤
        Real.exp ((1 / 10 : ℝ) *
          (Real.log (Real.log (Y : ℝ)) + meissel_mertens + 1) + 18 / 5) :=
      hexp
    _ = primeAsymptoticConstant *
        Real.exp ((1 / 10 : ℝ) * Real.log (Real.log (Y : ℝ))) := by
      unfold primeAsymptoticConstant
      rw [← Real.exp_add]
      congr 1
      ring
    _ = primeAsymptoticConstant *
        (Real.log (Y : ℝ)).rpow (1 / 10 : ℝ) := by
      change primeAsymptoticConstant *
        Real.exp ((1 / 10 : ℝ) * Real.log (Real.log (Y : ℝ))) =
        primeAsymptoticConstant * (Real.log (Y : ℝ)) ^ (1 / 10 : ℝ)
      rw [Real.rpow_def_of_pos hlogY]
      congr 2
      ring

theorem fixedMoment_partialSum_le_log_rpow_of_prime_bound
    {N Y : ℕ} (hN : 3 ≤ N) (hY : 2 ≤ Y)
    (hrec : reciprocalPrimeSum Y ≤
      Real.log (Real.log (Y : ℝ)) + meissel_mertens + 1) :
    HalberstamScratch.partialSum (fixedMoment Y) N ≤
      (hrMomentConstant * primeAsymptoticConstant) * (N : ℝ) *
        (Real.log (Y : ℝ)).rpow (1 / 10 : ℝ) := by
  have hraw := fixedMoment_partialSum_le_exp N Y hN
  have hexp := exp_reciprocalPrimeSum_le_log_rpow hY hrec
  rw [show
    (∑ p ∈ (Finset.Icc 1 Y).filter Nat.Prime, (p : ℝ)⁻¹) =
      reciprocalPrimeSum Y by rfl] at hraw
  calc
    HalberstamScratch.partialSum (fixedMoment Y) N ≤
        hrMomentConstant * (N : ℝ) *
          Real.exp ((1 / 10 : ℝ) * reciprocalPrimeSum Y + 18 / 5) := hraw
    _ ≤ hrMomentConstant * (N : ℝ) *
        (primeAsymptoticConstant *
          (Real.log (Y : ℝ)).rpow (1 / 10 : ℝ)) := by
      exact mul_le_mul_of_nonneg_left hexp
        (mul_nonneg hrMomentConstant_nonneg (Nat.cast_nonneg N))
    _ = (hrMomentConstant * primeAsymptoticConstant) * (N : ℝ) *
        (Real.log (Y : ℝ)).rpow (1 / 10 : ℝ) := by ring

noncomputable def smallPrimeConstant (Y₀ : ℕ) : ℝ :=
  Real.exp ((1 / 10 : ℝ) * reciprocalPrimeSum Y₀ + 18 / 5) /
    (Real.log 2).rpow (1 / 10 : ℝ)

lemma smallPrimeConstant_nonneg (Y₀ : ℕ) : 0 ≤ smallPrimeConstant Y₀ := by
  unfold smallPrimeConstant
  apply div_nonneg (Real.exp_pos _).le
  change 0 ≤ (Real.log 2) ^ (1 / 10 : ℝ)
  exact (Real.rpow_pos_of_pos (Real.log_pos (by norm_num)) _).le

lemma log_two_rpow_pos : 0 < (Real.log 2).rpow (1 / 10 : ℝ) := by
  change 0 < (Real.log 2) ^ (1 / 10 : ℝ)
  exact Real.rpow_pos_of_pos (Real.log_pos (by norm_num)) _

lemma log_two_rpow_le {Y : ℕ} (hY : 2 ≤ Y) :
    (Real.log 2).rpow (1 / 10 : ℝ) ≤
      (Real.log (Y : ℝ)).rpow (1 / 10 : ℝ) := by
  have hlog2 : 0 ≤ Real.log (2 : ℝ) :=
    (Real.log_pos (by norm_num)).le
  have hlogle : Real.log (2 : ℝ) ≤ Real.log (Y : ℝ) := by
    apply Real.log_le_log (by norm_num)
    exact_mod_cast hY
  change (Real.log 2) ^ (1 / 10 : ℝ) ≤
    (Real.log (Y : ℝ)) ^ (1 / 10 : ℝ)
  exact Real.rpow_le_rpow hlog2 hlogle (by norm_num)

lemma exp_reciprocalPrimeSum_le_small
    {Y Y₀ : ℕ} (hY : 2 ≤ Y) (hYY₀ : Y ≤ Y₀) :
    Real.exp ((1 / 10 : ℝ) * reciprocalPrimeSum Y + 18 / 5) ≤
      smallPrimeConstant Y₀ *
        (Real.log (Y : ℝ)).rpow (1 / 10 : ℝ) := by
  have hsum := reciprocalPrimeSum_mono hYY₀
  have hexp :
      Real.exp ((1 / 10 : ℝ) * reciprocalPrimeSum Y + 18 / 5) ≤
        Real.exp ((1 / 10 : ℝ) * reciprocalPrimeSum Y₀ + 18 / 5) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  have hpow := log_two_rpow_le hY
  have hconst :
      Real.exp ((1 / 10 : ℝ) * reciprocalPrimeSum Y₀ + 18 / 5) =
        smallPrimeConstant Y₀ *
          (Real.log 2).rpow (1 / 10 : ℝ) := by
    unfold smallPrimeConstant
    rw [div_mul_cancel₀ _ (ne_of_gt log_two_rpow_pos)]
  calc
    Real.exp ((1 / 10 : ℝ) * reciprocalPrimeSum Y + 18 / 5) ≤
        Real.exp ((1 / 10 : ℝ) * reciprocalPrimeSum Y₀ + 18 / 5) := hexp
    _ = smallPrimeConstant Y₀ *
        (Real.log 2).rpow (1 / 10 : ℝ) := hconst
    _ ≤ smallPrimeConstant Y₀ *
        (Real.log (Y : ℝ)).rpow (1 / 10 : ℝ) :=
      mul_le_mul_of_nonneg_left hpow (smallPrimeConstant_nonneg Y₀)

noncomputable def uniformMomentConstant (Y₀ : ℕ) : ℝ :=
  hrMomentConstant * (primeAsymptoticConstant + smallPrimeConstant Y₀) +
    2 / (Real.log 2).rpow (1 / 10 : ℝ)

lemma uniformMomentConstant_nonneg (Y₀ : ℕ) :
    0 ≤ uniformMomentConstant Y₀ := by
  unfold uniformMomentConstant
  apply add_nonneg
  · exact mul_nonneg hrMomentConstant_nonneg
      (add_nonneg primeAsymptoticConstant_pos.le
        (smallPrimeConstant_nonneg Y₀))
  · exact div_nonneg (by norm_num) log_two_rpow_pos.le

theorem fixedMoment_partialSum_uniform_from_threshold
    {Y₀ : ℕ}
    (hthreshold : ∀ Y : ℕ, Y₀ ≤ Y →
      reciprocalPrimeSum Y ≤
        Real.log (Real.log (Y : ℝ)) + meissel_mertens + 1) :
    ∀ N Y : ℕ, 2 ≤ N → 2 ≤ Y →
      HalberstamScratch.partialSum (fixedMoment Y) N ≤
        uniformMomentConstant Y₀ * (N : ℝ) *
          (Real.log (Y : ℝ)).rpow (1 / 10 : ℝ) := by
  intro N Y hNtwo hY
  by_cases hN : N = 2
  · subst N
    have htwo : fixedMoment Y 2 ≤ (6 / 5 : ℝ) := by
      rw [show 2 = 2 ^ 1 by norm_num]
      simpa using fixedMoment_prime_pow_le_pow Y Nat.prime_two (j := 1)
    have hsum : HalberstamScratch.partialSum (fixedMoment Y) 2 ≤ 11 / 5 := by
      rw [HalberstamScratch.partialSum, Finset.sum_Icc_succ_top (by omega)]
      have hset : Finset.Icc 1 1 = {1} := by ext n; simp
      rw [hset, Finset.sum_singleton, fixedMoment_one]
      linarith
    have hC :
        2 / (Real.log 2).rpow (1 / 10 : ℝ) ≤
          uniformMomentConstant Y₀ := by
      unfold uniformMomentConstant
      exact le_add_of_nonneg_left
        (mul_nonneg hrMomentConstant_nonneg
          (add_nonneg primeAsymptoticConstant_pos.le
            (smallPrimeConstant_nonneg Y₀)))
    have hpow := log_two_rpow_le hY
    have hfour : (4 : ℝ) ≤ uniformMomentConstant Y₀ * 2 *
        (Real.log (Y : ℝ)).rpow (1 / 10 : ℝ) := by
      calc
        (4 : ℝ) = (2 / (Real.log 2).rpow (1 / 10 : ℝ)) * 2 *
            (Real.log 2).rpow (1 / 10 : ℝ) := by
          rw [show (2 / (Real.log 2).rpow (1 / 10 : ℝ)) * 2 *
              (Real.log 2).rpow (1 / 10 : ℝ) =
              4 * ((1 / (Real.log 2).rpow (1 / 10 : ℝ)) *
                (Real.log 2).rpow (1 / 10 : ℝ)) by ring,
            div_mul_cancel₀ _ (ne_of_gt log_two_rpow_pos)]
          ring
        _ ≤ uniformMomentConstant Y₀ * 2 *
            (Real.log 2).rpow (1 / 10 : ℝ) := by
          have hmul := mul_le_mul_of_nonneg_right hC
            (show 0 ≤ (2 : ℝ) * (Real.log 2).rpow (1 / 10 : ℝ) by
              exact mul_nonneg (by norm_num) log_two_rpow_pos.le)
          nlinarith
        _ ≤ uniformMomentConstant Y₀ * 2 *
            (Real.log (Y : ℝ)).rpow (1 / 10 : ℝ) := by
          exact mul_le_mul_of_nonneg_left hpow
            (mul_nonneg (uniformMomentConstant_nonneg Y₀) (by norm_num))
    exact hsum.trans (by linarith)
  · have hN3 : 3 ≤ N := by omega
    have hraw := fixedMoment_partialSum_le_exp N Y hN3
    have hexp :
        Real.exp ((1 / 10 : ℝ) * reciprocalPrimeSum Y + 18 / 5) ≤
          (primeAsymptoticConstant + smallPrimeConstant Y₀) *
            (Real.log (Y : ℝ)).rpow (1 / 10 : ℝ) := by
      by_cases hlarge : Y₀ ≤ Y
      · have h := exp_reciprocalPrimeSum_le_log_rpow hY
          (hthreshold Y hlarge)
        calc
          Real.exp ((1 / 10 : ℝ) * reciprocalPrimeSum Y + 18 / 5) ≤
              primeAsymptoticConstant *
                (Real.log (Y : ℝ)).rpow (1 / 10 : ℝ) := h
          _ ≤ (primeAsymptoticConstant + smallPrimeConstant Y₀) *
                (Real.log (Y : ℝ)).rpow (1 / 10 : ℝ) := by
            apply mul_le_mul_of_nonneg_right
            · exact le_add_of_nonneg_right (smallPrimeConstant_nonneg Y₀)
            · change 0 ≤ Real.log (Y : ℝ) ^ (1 / 10 : ℝ)
              exact (Real.rpow_pos_of_pos
                (Real.log_pos (by exact_mod_cast hY)) _).le
      · have hsmallY : Y ≤ Y₀ := by omega
        have h := exp_reciprocalPrimeSum_le_small hY hsmallY
        calc
          Real.exp ((1 / 10 : ℝ) * reciprocalPrimeSum Y + 18 / 5) ≤
              smallPrimeConstant Y₀ *
                (Real.log (Y : ℝ)).rpow (1 / 10 : ℝ) := h
          _ ≤ (primeAsymptoticConstant + smallPrimeConstant Y₀) *
                (Real.log (Y : ℝ)).rpow (1 / 10 : ℝ) := by
            apply mul_le_mul_of_nonneg_right
            · exact le_add_of_nonneg_left primeAsymptoticConstant_pos.le
            · change 0 ≤ Real.log (Y : ℝ) ^ (1 / 10 : ℝ)
              exact (Real.rpow_pos_of_pos
                (Real.log_pos (by exact_mod_cast hY)) _).le
    rw [show
      (∑ p ∈ (Finset.Icc 1 Y).filter Nat.Prime, (p : ℝ)⁻¹) =
        reciprocalPrimeSum Y by rfl] at hraw
    have hmain :
        HalberstamScratch.partialSum (fixedMoment Y) N ≤
          (hrMomentConstant *
            (primeAsymptoticConstant + smallPrimeConstant Y₀)) * (N : ℝ) *
              (Real.log (Y : ℝ)).rpow (1 / 10 : ℝ) := by
      calc
        HalberstamScratch.partialSum (fixedMoment Y) N ≤
            hrMomentConstant * (N : ℝ) *
              Real.exp ((1 / 10 : ℝ) * reciprocalPrimeSum Y + 18 / 5) := hraw
        _ ≤ hrMomentConstant * (N : ℝ) *
            ((primeAsymptoticConstant + smallPrimeConstant Y₀) *
              (Real.log (Y : ℝ)).rpow (1 / 10 : ℝ)) := by
          exact mul_le_mul_of_nonneg_left hexp
            (mul_nonneg hrMomentConstant_nonneg (Nat.cast_nonneg N))
        _ = (hrMomentConstant *
            (primeAsymptoticConstant + smallPrimeConstant Y₀)) * (N : ℝ) *
              (Real.log (Y : ℝ)).rpow (1 / 10 : ℝ) := by ring
    exact hmain.trans (by
      apply mul_le_mul_of_nonneg_right
      · apply mul_le_mul_of_nonneg_right
        · unfold uniformMomentConstant
          exact le_add_of_nonneg_right
            (div_nonneg (by norm_num) log_two_rpow_pos.le)
        · exact Nat.cast_nonneg N
      · change 0 ≤ Real.log (Y : ℝ) ^ (1 / 10 : ℝ)
        exact (Real.rpow_pos_of_pos
          (Real.log_pos (by exact_mod_cast hY)) _).le)

/-- Uniform fixed-cutoff normalized divisor moment bound. -/
theorem exists_fixedMoment_partialSum_uniform :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ N Y : ℕ, 2 ≤ N → 2 ≤ Y →
        HalberstamScratch.partialSum (fixedMoment Y) N ≤
          C * (N : ℝ) *
            (Real.log (Y : ℝ)).rpow (1 / 10 : ℝ) := by
  rcases exists_prime_reciprocal_threshold with ⟨Y₀, hY₀⟩
  exact ⟨uniformMomentConstant Y₀, uniformMomentConstant_nonneg Y₀,
    fixedMoment_partialSum_uniform_from_threshold hY₀⟩

lemma range_sum_fixedMoment_le_partialSum (N Y : ℕ) (hN : 1 ≤ N) :
    (∑ n ∈ Finset.range N, fixedMoment Y n) ≤
      HalberstamScratch.partialSum (fixedMoment Y) N := by
  have hrange : Finset.range N = {0} ∪ Finset.Ico 1 N := by
    ext n
    simp only [Finset.mem_range, Finset.mem_union, Finset.mem_singleton,
      Finset.mem_Ico]
    constructor
    · intro hn
      by_cases hn0 : n = 0
      · exact Or.inl hn0
      · exact Or.inr ⟨Nat.one_le_iff_ne_zero.mpr hn0, hn⟩
    · rintro (rfl | ⟨hn1, hnN⟩)
      · exact hN
      · exact hnN
  rw [hrange, Finset.sum_union (by simp), Finset.sum_singleton,
    fixedMoment_zero, zero_add]
  unfold HalberstamScratch.partialSum
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro n hn
    exact Finset.mem_Icc.mpr
      ⟨(Finset.mem_Ico.mp hn).1, (Finset.mem_Ico.mp hn).2.le⟩
  · intro n hn hnot
    exact fixedMoment_nonneg Y n

/-- The range-sum version used by density arguments. -/
theorem exists_fixedMoment_range_uniform :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ N Y : ℕ, 2 ≤ N → 2 ≤ Y →
        (∑ n ∈ Finset.range N, fixedMoment Y n) ≤
          C * (N : ℝ) *
            (Real.log (Y : ℝ)).rpow (1 / 10 : ℝ) := by
  rcases exists_fixedMoment_partialSum_uniform with ⟨C, hC, hbound⟩
  refine ⟨C, hC, ?_⟩
  intro N Y hN hY
  exact (range_sum_fixedMoment_le_partialSum N Y (by omega)).trans
    (hbound N Y hN hY)

/-- Specialization to the natural dyadic cutoff.  The logarithmic factor is
absorbed into the absolute constant, leaving the exact `q^(1/10)` growth
used by the natural-grid concentration argument. -/
theorem exists_powTwo_fixedMoment_range_uniform :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ N q : ℕ, 2 ≤ N → 1 ≤ q →
        (∑ n ∈ Finset.range N, fixedMoment (2 ^ q) n) ≤
          C * (N : ℝ) * (q : ℝ).rpow (1 / 10 : ℝ) := by
  rcases exists_fixedMoment_range_uniform with ⟨C, hC, hbound⟩
  let C' := C * (Real.log 2).rpow (1 / 10 : ℝ)
  have hC' : 0 ≤ C' :=
    mul_nonneg hC log_two_rpow_pos.le
  refine ⟨C', hC', ?_⟩
  intro N q hN hq
  have hY : 2 ≤ 2 ^ q := by
    simpa using Nat.pow_le_pow_right (by omega : 0 < (2 : ℕ)) hq
  have h := hbound N (2 ^ q) hN hY
  have hlog : Real.log (((2 ^ q : ℕ) : ℝ)) =
      (q : ℝ) * Real.log 2 := by
    rw [show (((2 ^ q : ℕ) : ℝ)) = (2 : ℝ) ^ q by norm_num,
      Real.log_pow]
  have hrpow :
      (Real.log (((2 ^ q : ℕ) : ℝ))).rpow (1 / 10 : ℝ) =
        (q : ℝ).rpow (1 / 10 : ℝ) *
          (Real.log 2).rpow (1 / 10 : ℝ) := by
    rw [hlog]
    change ((q : ℝ) * Real.log 2) ^ (1 / 10 : ℝ) =
      (q : ℝ) ^ (1 / 10 : ℝ) * (Real.log 2) ^ (1 / 10 : ℝ)
    exact Real.mul_rpow (Nat.cast_nonneg q)
      (Real.log_pos (by norm_num)).le
  rw [hrpow] at h
  calc
    (∑ n ∈ Finset.range N, fixedMoment (2 ^ q) n) ≤
        C * (N : ℝ) *
          ((q : ℝ).rpow (1 / 10 : ℝ) *
            (Real.log 2).rpow (1 / 10 : ℝ)) := h
    _ = C' * (N : ℝ) * (q : ℝ).rpow (1 / 10 : ℝ) := by
      dsimp [C']
      ring

end NormalizedDivisorMoment448

#print axioms NormalizedDivisorMoment448.fixedMoment_mul
#print axioms NormalizedDivisorMoment448.fixedMoment_prime_pow
#print axioms NormalizedDivisorMoment448.exists_powTwo_fixedMoment_range_uniform
