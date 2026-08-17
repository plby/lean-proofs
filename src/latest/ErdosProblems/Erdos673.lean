/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Erdős Problem 673.

The mathematical proof, including the correction that Tao's lower bound
requires a divisor `m > 1`, is documented in `tex/673.tex`.
-/

import ErdosProblems.Erdos448.HalberstamComplete448
import ErdosProblems.Erdos448.MertensEulerProduct448
import ErdosProblems.Erdos459
import ErdosProblems.Erdos673.Mean
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Util.Density

open scoped BigOperators ArithmeticFunction.sigma
open Filter Finset Set Asymptotics

namespace Erdos673

noncomputable section

attribute [local instance] Classical.propDecidable

/-- The increasing enumeration of the positive divisors of `n`. -/
def divisorSequence (n : ℕ) : Fin n.divisors.card ↪o ℕ :=
  n.divisors.orderEmbOfFin rfl

/-- Short internal name for the ordered divisor enumeration. -/
abbrev orderedDivisor := divisorSequence

/-- The sum of the ratios of consecutive divisors from Erdős Problem 673.
For `n = 0` the divisor finset is empty and the sum is zero. -/
def G (n : ℕ) : ℝ :=
  ∑ i : Fin (n.divisors.card - 1),
    ((divisorSequence n ⟨i.1, by omega⟩ : ℕ) : ℝ) /
      ((divisorSequence n ⟨i.1 + 1, by omega⟩ : ℕ) : ℝ)

/-- The source-faithful meaning of tending to infinity for almost all
natural numbers. -/
def TendsToInfinityAlmostAll (f : ℕ → ℝ) : Prop :=
  ∀ C : ℝ, {n : ℕ | C < f n}.HasDensity 1

/-- The summatory function in Problem 673. -/
def GSum (X : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 X, G n

/-- The ordinary divisor summatory function, in the same endpoint
convention as `GSum`. -/
def tauSum (X : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 X, (n.divisors.card : ℝ)

/-- Positive integers with fewer than `r` prime factors counted with
multiplicity. -/
def omegaLow (r : ℕ) : Set ℕ :=
  {n | n ≠ 0 ∧ ArithmeticFunction.cardFactors n < r}

lemma divisorSequence_mem (n : ℕ) (i : Fin n.divisors.card) :
    divisorSequence n i ∈ n.divisors :=
  Finset.orderEmbOfFin_mem n.divisors rfl i

lemma divisorSequence_pos (n : ℕ) (i : Fin n.divisors.card) :
    0 < divisorSequence n i :=
  Nat.pos_of_mem_divisors (divisorSequence_mem n i)

lemma card_divisors_pos {n : ℕ} (hn : n ≠ 0) : 0 < n.divisors.card :=
  Finset.card_pos.mpr (Nat.nonempty_divisors.mpr hn)

/-- The first term of the increasing divisor sequence is one. -/
lemma divisorSequence_zero {n : ℕ} (hn : n ≠ 0) :
    divisorSequence n ⟨0, card_divisors_pos hn⟩ = 1 := by
  rw [divisorSequence, Finset.orderEmbOfFin_zero rfl (card_divisors_pos hn)]
  apply (Finset.min'_eq_iff _ _ _).2
  refine ⟨Nat.one_mem_divisors.mpr hn, ?_⟩
  intro d hd
  exact Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt (Nat.pos_of_mem_divisors hd))

/-- The final term of the increasing divisor sequence is `n`. -/
lemma divisorSequence_last {n : ℕ} (hn : n ≠ 0) :
    divisorSequence n
      ⟨n.divisors.card - 1,
        Nat.sub_lt (card_divisors_pos hn) (Nat.succ_pos 0)⟩ = n := by
  rw [divisorSequence, Finset.orderEmbOfFin_last rfl (card_divisors_pos hn)]
  apply (Finset.max'_eq_iff _ _ _).2
  exact ⟨Nat.mem_divisors_self n hn, fun d hd ↦ Nat.divisor_le hd⟩

lemma G_nonneg (n : ℕ) : 0 ≤ G n := by
  unfold G
  exact Finset.sum_nonneg fun i _ ↦
    div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

/-- Every consecutive-divisor ratio is at most one. -/
lemma G_le_card_divisors (n : ℕ) : G n ≤ (n.divisors.card : ℝ) := by
  unfold G
  calc
    (∑ i : Fin (n.divisors.card - 1),
        ((divisorSequence n ⟨i.1, by omega⟩ : ℕ) : ℝ) /
          ((divisorSequence n ⟨i.1 + 1, by omega⟩ : ℕ) : ℝ))
        ≤ ∑ _i : Fin (n.divisors.card - 1), (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro i _hi
          have hlt :
              divisorSequence n ⟨i.1, by omega⟩ <
                divisorSequence n ⟨i.1 + 1, by omega⟩ :=
            (divisorSequence n).strictMono (by simp)
          have hpos :
              (0 : ℝ) < divisorSequence n ⟨i.1 + 1, by omega⟩ := by
            exact_mod_cast divisorSequence_pos n ⟨i.1 + 1, by omega⟩
          exact (div_le_one hpos).2 (by exact_mod_cast hlt.le)
    _ = (n.divisors.card - 1 : ℕ) := by simp
    _ ≤ (n.divisors.card : ℝ) := by exact_mod_cast Nat.sub_le _ _

lemma orderedDivisor_dvd (n : ℕ) (i : Fin n.divisors.card) :
    orderedDivisor n i ∣ n :=
  Nat.dvd_of_mem_divisors (divisorSequence_mem n i)

lemma orderedDivisor_pos {n : ℕ} (hn : n ≠ 0) (i : Fin n.divisors.card) :
    0 < orderedDivisor n i :=
  Nat.pos_of_dvd_of_pos (orderedDivisor_dvd n i) (Nat.pos_of_ne_zero hn)

lemma orderedDivisor_strictMono (n : ℕ) : StrictMono (orderedDivisor n) :=
  (orderedDivisor n).strictMono

@[simp] lemma orderedDivisor_zero {n : ℕ} (hn : n ≠ 0) :
    orderedDivisor n ⟨0, card_divisors_pos hn⟩ = 1 :=
  divisorSequence_zero hn

@[simp] lemma orderedDivisor_last {n : ℕ} (hn : n ≠ 0) :
    orderedDivisor n ⟨n.divisors.card - 1,
      Nat.sub_lt (card_divisors_pos hn) Nat.zero_lt_one⟩ = n :=
  divisorSequence_last hn

noncomputable def divisorIndex (n d : ℕ) (hd : d ∈ n.divisors) :
    Fin n.divisors.card :=
  (n.divisors.orderIsoOfFin rfl).symm ⟨d, hd⟩

@[simp] lemma orderedDivisor_divisorIndex (n d : ℕ) (hd : d ∈ n.divisors) :
    orderedDivisor n (divisorIndex n d hd) = d := by
  exact congrArg Subtype.val
    ((n.divisors.orderIsoOfFin rfl).apply_symm_apply ⟨d, hd⟩)

lemma divisorIndex_lt_card_sub_one {n d : ℕ} (hn : n ≠ 0)
    (hd : d ∈ n.divisors) (hdn : d < n) :
    (divisorIndex n d hd : ℕ) < n.divisors.card - 1 := by
  have hlt :
      orderedDivisor n (divisorIndex n d hd) <
        orderedDivisor n ⟨n.divisors.card - 1,
          Nat.sub_lt (card_divisors_pos hn) Nat.zero_lt_one⟩ := by
    rw [orderedDivisor_divisorIndex, orderedDivisor_last hn]
    exact hdn
  exact ((orderedDivisor n).lt_iff_lt).mp hlt

lemma orderedDivisor_succ_le_of_le {n e : ℕ} (_hn : n ≠ 0)
    (i : Fin (n.divisors.card - 1)) (he : e ∈ n.divisors)
    (hde : orderedDivisor n ⟨i, by omega⟩ < e) :
    orderedDivisor n ⟨i + 1, by omega⟩ ≤ e := by
  let j := divisorIndex n e he
  have hij : (⟨i, by omega⟩ : Fin n.divisors.card) < j := by
    apply ((orderedDivisor n).lt_iff_lt).mp
    simpa [j] using hde
  have hij' : (⟨i + 1, by omega⟩ : Fin n.divisors.card) ≤ j := hij
  simpa [j] using (orderedDivisor n).monotone hij'

lemma ratio_pos {n : ℕ} (hn : n ≠ 0) (i : Fin (n.divisors.card - 1)) :
    0 < (orderedDivisor n ⟨i, by omega⟩ : ℝ) /
      orderedDivisor n ⟨i + 1, by omega⟩ := by
  exact div_pos (by exact_mod_cast orderedDivisor_pos hn ⟨i, by omega⟩)
    (by exact_mod_cast orderedDivisor_pos hn ⟨i + 1, by omega⟩)

lemma ratio_lt_one {n : ℕ} (hn : n ≠ 0) (i : Fin (n.divisors.card - 1)) :
    (orderedDivisor n ⟨i, by omega⟩ : ℝ) /
        orderedDivisor n ⟨i + 1, by omega⟩ < 1 := by
  rw [div_lt_one]
  · exact_mod_cast orderedDivisor_strictMono n
      (show (i : ℕ) < i + 1 by omega)
  · exact_mod_cast orderedDivisor_pos hn ⟨i + 1, by omega⟩

lemma quotient_ne_zero {n m : ℕ} (hn : n ≠ 0) (hmn : m ∣ n) :
    n / m ≠ 0 := by
  intro hq
  have hmul := Nat.div_mul_cancel hmn
  rw [hq, zero_mul] at hmul
  exact hn hmul.symm

lemma divisor_quotient_lt {n m d : ℕ} (hn : n ≠ 0) (hm : 1 < m)
    (hmn : m ∣ n) (hd : d ∈ (n / m).divisors) : d < n := by
  have hqpos : 0 < n / m := Nat.pos_of_ne_zero (quotient_ne_zero hn hmn)
  have hdle : d ≤ n / m :=
    Nat.le_of_dvd hqpos (Nat.dvd_of_mem_divisors hd)
  have hmul : n / m * m = n := Nat.div_mul_cancel hmn
  have hq_lt : n / m < n / m * m := by nlinarith
  exact hdle.trans_lt (hq_lt.trans_eq hmul)

lemma quotient_divisor_mem {n m d : ℕ} (hn : n ≠ 0) (hmn : m ∣ n)
    (hd : d ∈ (n / m).divisors) : d ∈ n.divisors := by
  rw [Nat.mem_divisors] at hd ⊢
  exact ⟨hd.1.trans ⟨m, (Nat.div_mul_cancel hmn).symm⟩, hn⟩

lemma mul_quotient_divisor_mem {n m d : ℕ} (hn : n ≠ 0) (hmn : m ∣ n)
    (hd : d ∈ (n / m).divisors) : d * m ∈ n.divisors := by
  rw [Nat.mem_divisors] at hd ⊢
  rcases hd.1 with ⟨c, hc⟩
  refine ⟨⟨c, ?_⟩, hn⟩
  calc
    n = n / m * m := (Nat.div_mul_cancel hmn).symm
    _ = (d * c) * m := by rw [hc]
    _ = d * m * c := by ac_rfl

lemma tao_pointwise {n m d : ℕ} (hn : n ≠ 0) (hm : 1 < m)
    (hmn : m ∣ n) (hd : d ∈ (n / m).divisors) :
    ∃ i : Fin (n.divisors.card - 1),
      orderedDivisor n ⟨i, by omega⟩ = d ∧
        (1 : ℝ) / m ≤
          (orderedDivisor n ⟨i, by omega⟩ : ℝ) /
            orderedDivisor n ⟨i + 1, by omega⟩ := by
  have hdN : d ∈ n.divisors := quotient_divisor_mem hn hmn hd
  have hdn : d < n := divisor_quotient_lt hn hm hmn hd
  let i : Fin (n.divisors.card - 1) :=
    ⟨divisorIndex n d hdN, divisorIndex_lt_card_sub_one hn hdN hdn⟩
  refine ⟨i, by simp [i], ?_⟩
  have hdpos : 0 < d :=
    Nat.pos_of_dvd_of_pos (Nat.dvd_of_mem_divisors hd)
      (Nat.pos_of_ne_zero (quotient_ne_zero hn hmn))
  have himem : d * m ∈ n.divisors := mul_quotient_divisor_mem hn hmn hd
  have hilt : orderedDivisor n ⟨i, by omega⟩ < d * m := by
    change orderedDivisor n (divisorIndex n d hdN) < d * m
    rw [orderedDivisor_divisorIndex]
    nlinarith
  have hsucc : orderedDivisor n ⟨i + 1, by omega⟩ ≤ d * m :=
    orderedDivisor_succ_le_of_le hn i himem hilt
  have hsuccpos : (0 : ℝ) < orderedDivisor n ⟨i + 1, by omega⟩ := by
    exact_mod_cast orderedDivisor_pos hn ⟨i + 1, by omega⟩
  have hdposR : (0 : ℝ) < d := by exact_mod_cast hdpos
  calc
    (1 : ℝ) / m = (d : ℝ) / (d * m) := by field_simp
    _ ≤ (d : ℝ) / orderedDivisor n ⟨i + 1, by omega⟩ := by
      exact div_le_div_of_nonneg_left hdposR.le hsuccpos
        (by exact_mod_cast hsucc)
    _ = (orderedDivisor n ⟨i, by omega⟩ : ℝ) /
        orderedDivisor n ⟨i + 1, by omega⟩ := by simp [i]

/-- Tao's lower comparison, with the necessary hypothesis `m > 1`. -/
theorem tao_lower_bound {n m : ℕ} (hn : n ≠ 0) (hm : 1 < m)
    (hmn : m ∣ n) :
    ((n / m).divisors.card : ℝ) / m ≤ G n := by
  classical
  let f : (n / m).divisors → Fin (n.divisors.card - 1) := fun d ↦
    ⟨divisorIndex n d (quotient_divisor_mem hn hmn d.property),
      divisorIndex_lt_card_sub_one hn
        (quotient_divisor_mem hn hmn d.property)
        (divisor_quotient_lt hn hm hmn d.property)⟩
  have hf_value (d : (n / m).divisors) :
      orderedDivisor n ⟨f d, by omega⟩ = d := by simp [f]
  have hf_inj : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    let g : Fin (n.divisors.card - 1) → ℕ := fun i ↦
      orderedDivisor n ⟨i, by omega⟩
    have hg := congrArg g hab
    simpa [g, hf_value] using hg
  have hf_bound (d : (n / m).divisors) :
      (1 : ℝ) / m ≤
        (orderedDivisor n ⟨f d, by omega⟩ : ℝ) /
          orderedDivisor n ⟨f d + 1, by omega⟩ := by
    obtain ⟨i, hi, hibound⟩ := tao_pointwise hn hm hmn d.property
    have hw : (⟨i, by omega⟩ : Fin n.divisors.card) =
        ⟨f d, by omega⟩ := by
      apply (orderedDivisor n).injective
      rw [hi, hf_value]
    have hif : i = f d := by
      apply Fin.ext
      simpa using congrArg Fin.val hw
    simpa [hif] using hibound
  calc
    ((n / m).divisors.card : ℝ) / m =
        ∑ _d : (n / m).divisors, (1 : ℝ) / m := by simp [div_eq_mul_inv]
    _ ≤ ∑ d : (n / m).divisors,
        (orderedDivisor n ⟨f d, by omega⟩ : ℝ) /
          orderedDivisor n ⟨f d + 1, by omega⟩ := by
      exact Finset.sum_le_sum fun d _ ↦ hf_bound d
    _ = ∑ i ∈ Finset.image f Finset.univ,
        (orderedDivisor n ⟨i, by omega⟩ : ℝ) /
          orderedDivisor n ⟨i + 1, by omega⟩ := by
      rw [Finset.sum_image]
      exact fun a _ b _ hab ↦ hf_inj hab
    _ ≤ ∑ i : Fin (n.divisors.card - 1),
        (orderedDivisor n ⟨i, by omega⟩ : ℝ) /
          orderedDivisor n ⟨i + 1, by omega⟩ := by
      exact Finset.sum_le_sum_of_subset_of_nonneg (by simp)
        (fun i _ _ ↦ (ratio_pos hn i).le)
    _ = G n := rfl

noncomputable def orderedLog (n i : ℕ) : ℝ :=
  if hi : i < n.divisors.card then
    Real.log (orderedDivisor n ⟨i, hi⟩) else 0

lemma orderedLog_eq {n i : ℕ} (hi : i < n.divisors.card) :
    orderedLog n i = Real.log (orderedDivisor n ⟨i, hi⟩) := by
  simp [orderedLog, hi]

lemma sum_range_succ_sub (u : ℕ → ℝ) (k : ℕ) :
    ∑ i ∈ Finset.range k, (u (i + 1) - u i) = u k - u 0 := by
  induction k with
  | zero => simp
  | succ k ih => rw [Finset.sum_range_succ, ih]; ring

lemma log_ratio_eq_orderedLog_sub {n : ℕ} (hn : n ≠ 0)
    (i : Fin (n.divisors.card - 1)) :
    Real.log ((orderedDivisor n ⟨i + 1, by omega⟩ : ℝ) /
        orderedDivisor n ⟨i, by omega⟩) =
      orderedLog n (i + 1) - orderedLog n i := by
  rw [Real.log_div]
  · rw [orderedLog_eq (by omega), orderedLog_eq (by omega)]
  · exact_mod_cast Nat.ne_of_gt (orderedDivisor_pos hn ⟨i + 1, by omega⟩)
  · exact_mod_cast Nat.ne_of_gt (orderedDivisor_pos hn ⟨i, by omega⟩)

lemma sum_log_ratios {n : ℕ} (hn : n ≠ 0) :
    ∑ i : Fin (n.divisors.card - 1),
        Real.log ((orderedDivisor n ⟨i + 1, by omega⟩ : ℝ) /
          orderedDivisor n ⟨i, by omega⟩) = Real.log n := by
  calc
    ∑ i : Fin (n.divisors.card - 1),
        Real.log ((orderedDivisor n ⟨i + 1, by omega⟩ : ℝ) /
          orderedDivisor n ⟨i, by omega⟩) =
        ∑ i : Fin (n.divisors.card - 1),
          (orderedLog n (i + 1) - orderedLog n i) := by
      exact Finset.sum_congr rfl fun i _ ↦ log_ratio_eq_orderedLog_sub hn i
    _ = ∑ i ∈ Finset.range (n.divisors.card - 1),
          (orderedLog n (i + 1) - orderedLog n i) := by
      exact (Fin.sum_univ_eq_sum_range
        (fun i ↦ orderedLog n (i + 1) - orderedLog n i))
          (n.divisors.card - 1)
    _ = orderedLog n (n.divisors.card - 1) - orderedLog n 0 :=
      sum_range_succ_sub (orderedLog n) (n.divisors.card - 1)
    _ = Real.log n := by
      rw [orderedLog_eq (Nat.sub_lt (card_divisors_pos hn) Nat.zero_lt_one),
        orderedLog_eq (card_divisors_pos hn), orderedDivisor_last hn,
        orderedDivisor_zero hn, Nat.cast_one, Real.log_one, sub_zero]

lemma one_sub_ratio_le_log_ratio {n : ℕ} (hn : n ≠ 0)
    (i : Fin (n.divisors.card - 1)) :
    1 - (orderedDivisor n ⟨i, by omega⟩ : ℝ) /
        orderedDivisor n ⟨i + 1, by omega⟩ ≤
      Real.log ((orderedDivisor n ⟨i + 1, by omega⟩ : ℝ) /
        orderedDivisor n ⟨i, by omega⟩) := by
  have hcur : (0 : ℝ) < orderedDivisor n ⟨i, by omega⟩ := by
    exact_mod_cast orderedDivisor_pos hn ⟨i, by omega⟩
  have hnxt : (0 : ℝ) < orderedDivisor n ⟨i + 1, by omega⟩ := by
    exact_mod_cast orderedDivisor_pos hn ⟨i + 1, by omega⟩
  have h := Real.one_sub_inv_le_log_of_pos (div_pos hnxt hcur)
  convert h using 1
  all_goals field_simp

lemma card_sub_G_eq {n : ℕ} (hn : n ≠ 0) :
    (n.divisors.card : ℝ) - G n =
      1 + ∑ i : Fin (n.divisors.card - 1),
        (1 - (orderedDivisor n ⟨i, by omega⟩ : ℝ) /
          orderedDivisor n ⟨i + 1, by omega⟩) := by
  rw [G, Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one]
  have hc : 1 ≤ n.divisors.card := card_divisors_pos hn
  rw [Nat.cast_sub hc]
  ring

/-- The total deficit from the divisor count telescopes logarithmically. -/
theorem logarithmic_deficit_bound {n : ℕ} (hn : n ≠ 0) :
    (n.divisors.card : ℝ) - G n ≤ 1 + Real.log n := by
  rw [card_sub_G_eq hn]
  gcongr
  calc
    ∑ i : Fin (n.divisors.card - 1),
        (1 - (orderedDivisor n ⟨i, by omega⟩ : ℝ) /
          orderedDivisor n ⟨i + 1, by omega⟩) ≤
        ∑ i : Fin (n.divisors.card - 1),
          Real.log ((orderedDivisor n ⟨i + 1, by omega⟩ : ℝ) /
            orderedDivisor n ⟨i, by omega⟩) := by
      exact Finset.sum_le_sum fun i _ ↦ one_sub_ratio_le_log_ratio hn i
    _ = Real.log n := sum_log_ratios hn

/-- The elementary inequality `1 + ∑ eᵢ ≤ ∏ (eᵢ + 1)`. -/
lemma one_add_sum_le_prod_succ {α : Type*}
    (s : Finset α) (e : α → ℕ) :
    1 + ∑ a ∈ s, e a ≤ ∏ a ∈ s, (e a + 1) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.prod_insert ha]
      have hprod : 1 + ∑ x ∈ s, e x ≤ ∏ x ∈ s, (e x + 1) := ih
      have hsum : 0 ≤ ∑ x ∈ s, e x := Nat.zero_le _
      nlinarith

/-- The divisor count is at least one plus the number of prime factors
counted with multiplicity. -/
lemma cardFactors_add_one_le_card_divisors {n : ℕ} (hn : n ≠ 0) :
    ArithmeticFunction.cardFactors n + 1 ≤ n.divisors.card := by
  rw [Nat.card_divisors hn,
    ArithmeticFunction.cardFactors_eq_sum_factorization,
    Finsupp.sum, Nat.support_factorization]
  simpa [add_comm] using
    one_add_sum_le_prod_succ n.primeFactors n.factorization

/-- Removing one prime factor lowers `Ω` by exactly one. -/
lemma cardFactors_div_prime_add_one {n p : ℕ} (hn : n ≠ 0)
    (hp : p.Prime) (hpn : p ∣ n) :
    ArithmeticFunction.cardFactors (n / p) + 1 =
      ArithmeticFunction.cardFactors n := by
  have hq : n / p ≠ 0 := by
    intro hzero
    apply hn
    rw [← Nat.mul_div_cancel' hpn, hzero, mul_zero]
  conv_rhs => rw [← Nat.mul_div_cancel' hpn]
  rw [ArithmeticFunction.cardFactors_mul hp.ne_zero hq,
    ArithmeticFunction.cardFactors_apply_prime hp]
  omega

/-- A prime quotient has at least `Ω(n)` divisors. -/
lemma cardFactors_le_card_divisors_div_prime {n p : ℕ} (hn : n ≠ 0)
    (hp : p.Prime) (hpn : p ∣ n) :
    ArithmeticFunction.cardFactors n ≤ (n / p).divisors.card := by
  have hq : n / p ≠ 0 := by
    intro hzero
    apply hn
    rw [← Nat.mul_div_cancel' hpn, hzero, mul_zero]
  rw [← cardFactors_div_prime_add_one hn hp hpn]
  exact cardFactors_add_one_le_card_divisors hq

def primePrefix (M : ℕ) : Finset ℕ :=
  (Finset.range M).filter Nat.Prime

def avoidsPrimePrefix (M : ℕ) : Set ℕ :=
  {n | ∀ p ∈ primePrefix M, ¬ p ∣ n}

private def densityRatio (A : Set ℕ) (N : ℕ) : ℝ :=
  ((Finset.filter (fun n ↦ n ∈ A) (Finset.range N)).card : ℝ) / N

private lemma densityRatio_nonneg (A : Set ℕ) (N : ℕ) :
    0 ≤ densityRatio A N := by
  exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

private lemma densityRatio_mono {A B : Set ℕ} (hAB : A ⊆ B) (N : ℕ) :
    densityRatio A N ≤ densityRatio B N := by
  unfold densityRatio
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact_mod_cast Finset.card_le_card (by
    intro n hn
    rw [Finset.mem_filter] at hn ⊢
    exact ⟨hn.1, hAB hn.2⟩)

lemma naturalDensity_zero_mono {A B : Set ℕ} (hAB : A ⊆ B)
    (hB : Erdos459.has_natural_density B 0) :
    Erdos459.has_natural_density A 0 := by
  rw [Erdos459.has_natural_density] at hB ⊢
  change Tendsto (densityRatio A) atTop (nhds 0)
  change Tendsto (densityRatio B) atTop (nhds 0) at hB
  exact squeeze_zero (densityRatio_nonneg A) (densityRatio_mono hAB) hB

lemma naturalDensity_zero_union {A B : Set ℕ}
    (hA : Erdos459.has_natural_density A 0)
    (hB : Erdos459.has_natural_density B 0) :
    Erdos459.has_natural_density (A ∪ B) 0 := by
  have hdiff : Erdos459.has_natural_density (B \ A) 0 :=
    naturalDensity_zero_mono Set.sdiff_subset hB
  have hdisj : Disjoint A (B \ A) := Set.disjoint_sdiff_right
  simpa [Set.union_sdiff_self] using
    Erdos459.density_disjoint_union A (B \ A) 0 0 hA hdiff hdisj

lemma naturalDensity_zero_biUnion {α : Type*} (s : Finset α) (A : α → Set ℕ)
    (hA : ∀ a ∈ s, Erdos459.has_natural_density (A a) 0) :
    Erdos459.has_natural_density (⋃ a ∈ s, A a) 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Erdos459.has_natural_density]
  | @insert a s ha ih =>
      rw [Finset.set_biUnion_insert]
      exact naturalDensity_zero_union (hA a (Finset.mem_insert_self a s))
        (ih fun b hb ↦ hA b (Finset.mem_insert_of_mem hb))

lemma naturalDensity_union_zero_right {A Z : Set ℕ} {d : ℝ}
    (hA : Erdos459.has_natural_density A d)
    (hZ : Erdos459.has_natural_density Z 0) :
    Erdos459.has_natural_density (A ∪ Z) d := by
  have hdiff : Erdos459.has_natural_density (Z \ A) 0 :=
    naturalDensity_zero_mono Set.sdiff_subset hZ
  have hdisj : Disjoint A (Z \ A) := Set.disjoint_sdiff_right
  simpa [Set.union_sdiff_self] using
    Erdos459.density_disjoint_union A (Z \ A) d 0 hA hdiff hdisj

private lemma primeAvoidanceDensity_nonneg (M : ℕ) :
    0 ≤ ∏ p ∈ primePrefix M, (1 - 1 / (p : ℝ)) := by
  apply Finset.prod_nonneg
  intro p hp
  have hprime : p.Prime := (Finset.mem_filter.mp hp).2
  have hpone : (1 : ℝ) ≤ p := by exact_mod_cast hprime.one_lt.le
  exact sub_nonneg.mpr (by
    simpa [one_div] using inv_le_one_of_one_le₀ hpone)

private lemma primeAvoidanceDensity_le_bound (M : ℕ) :
    (∏ p ∈ primePrefix M, (1 - 1 / (p : ℝ))) ≤
      (∏ p ∈ primePrefix M, (1 - 1 / (p : ℝ))) *
        (1 + ∑ p ∈ primePrefix M, (1 / (p - 1 : ℝ))) := by
  have hsum : 0 ≤ ∑ p ∈ primePrefix M, (1 / (p - 1 : ℝ)) := by
    apply Finset.sum_nonneg
    intro p hp
    have hprime : p.Prime := (Finset.mem_filter.mp hp).2
    have hpcast : (1 : ℝ) < p := by exact_mod_cast hprime.one_lt
    exact one_div_nonneg.mpr (sub_pos.mpr hpcast).le
  nth_rw 1 [← mul_one (∏ p ∈ primePrefix M, (1 - 1 / (p : ℝ)))]
  exact mul_le_mul_of_nonneg_left (by linarith)
    (primeAvoidanceDensity_nonneg M)

lemma naturalDensity_zero_of_primePrefix_covers (B : Set ℕ)
    (hcover : ∀ M, ∃ Z : Set ℕ,
      Erdos459.has_natural_density Z 0 ∧ B ⊆ avoidsPrimePrefix M ∪ Z) :
    Erdos459.has_natural_density B 0 := by
  rw [Erdos459.has_natural_density, Metric.tendsto_nhds]
  change ∀ ε > 0, ∀ᶠ N in atTop, dist (densityRatio B N) 0 < ε
  intro ε hε
  let bound : ℕ → ℝ := fun M ↦
    (∏ p ∈ primePrefix M, (1 - 1 / (p : ℝ))) *
      (1 + ∑ p ∈ primePrefix M, (1 / (p - 1 : ℝ)))
  have hbound : Tendsto bound atTop (nhds 0) := by
    simpa [bound, primePrefix] using Erdos459.density_bound_tends_to_zero
  have hevent : ∀ᶠ M in atTop, dist (bound M) 0 < ε / 2 :=
    (Metric.tendsto_nhds.mp hbound) (ε / 2) (half_pos hε)
  obtain ⟨M, hM⟩ := hevent.exists
  obtain ⟨Z, hZ, hBZ⟩ := hcover M
  let d : ℝ := ∏ p ∈ primePrefix M, (1 - 1 / (p : ℝ))
  have hAd : Erdos459.has_natural_density (avoidsPrimePrefix M) d := by
    simpa [avoidsPrimePrefix, d, primePrefix] using
      Erdos459.density_no_prime (primePrefix M) (fun p hp ↦
        (Finset.mem_filter.mp hp).2)
  have hAZ : Erdos459.has_natural_density (avoidsPrimePrefix M ∪ Z) d :=
    naturalDensity_union_zero_right hAd hZ
  rw [Erdos459.has_natural_density] at hAZ
  change Tendsto (densityRatio (avoidsPrimePrefix M ∪ Z)) atTop (nhds d) at hAZ
  have hAZevent : ∀ᶠ N in atTop,
      dist (densityRatio (avoidsPrimePrefix M ∪ Z) N) d < ε / 2 :=
    (Metric.tendsto_nhds.mp hAZ) (ε / 2) (half_pos hε)
  have hdlt : d < ε / 2 := by
    have hdle : d ≤ bound M := by
      simpa [d, bound] using primeAvoidanceDensity_le_bound M
    have hbabs : |bound M| < ε / 2 := by simpa [Real.dist_eq] using hM
    exact hdle.trans_lt ((le_abs_self (bound M)).trans_lt hbabs)
  filter_upwards [hAZevent] with N hN
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (densityRatio_nonneg B N)]
  have hmono := densityRatio_mono hBZ N
  have hupper : densityRatio (avoidsPrimePrefix M ∪ Z) N < d + ε / 2 := by
    rw [Real.dist_eq] at hN
    linarith [le_abs_self (densityRatio (avoidsPrimePrefix M ∪ Z) N - d)]
  linarith

/-- For each fixed `r`, positive integers with `Ω(n) < r` have density zero. -/
theorem omegaLow_hasNaturalDensity_zero (r : ℕ) :
    Erdos459.has_natural_density (omegaLow r) 0 := by
  induction r with
  | zero =>
      have hempty : omegaLow 0 = ∅ := by ext n; simp [omegaLow]
      rw [hempty]
      simp [Erdos459.has_natural_density]
  | succ r ih =>
      apply naturalDensity_zero_of_primePrefix_covers
      intro M
      let scaled : ℕ → Set ℕ := fun p ↦
        {n | ∃ a ∈ omegaLow r, n = p * a}
      let Z : Set ℕ := ⋃ p ∈ primePrefix M, scaled p
      refine ⟨Z, ?_, ?_⟩
      · apply naturalDensity_zero_biUnion
        intro p hp
        have hpprime : p.Prime := (Finset.mem_filter.mp hp).2
        simpa [scaled] using
          Erdos459.density_scaled (omegaLow r) 0 p hpprime.pos ih
      · intro n hn
        by_cases hav : ∀ p ∈ primePrefix M, ¬ p ∣ n
        · exact Or.inl hav
        · right
          push Not at hav
          obtain ⟨p, hpS, hpn⟩ := hav
          refine Set.mem_iUnion_of_mem p (Set.mem_iUnion_of_mem hpS ?_)
          refine ⟨n / p, ?_, (Nat.mul_div_cancel' hpn).symm⟩
          have hpprime : p.Prime := (Finset.mem_filter.mp hpS).2
          have hq0 : n / p ≠ 0 := by
            intro hzero
            exact hn.1 (by rw [← Nat.mul_div_cancel' hpn, hzero, mul_zero])
          refine ⟨hq0, ?_⟩
          have hcard := cardFactors_div_prime_add_one hn.1 hpprime hpn
          change ArithmeticFunction.cardFactors (n / p) < r
          apply Nat.lt_of_add_lt_add_right (n := 1)
          rw [hcard]
          simpa [Nat.succ_eq_add_one] using hn.2

theorem sublevel_hasNaturalDensity_zero_of_cardFactors_div_prime_lower
    (f : ℕ → ℝ)
    (hlower : ∀ {n p : ℕ}, n ≠ 0 → p.Prime → p ∣ n →
      (ArithmeticFunction.cardFactors n : ℝ) / p ≤ f n)
    (C : ℝ) :
    Erdos459.has_natural_density {n : ℕ | n ≠ 0 ∧ f n ≤ C} 0 := by
  apply naturalDensity_zero_of_primePrefix_covers
  intro M
  obtain ⟨R, hR⟩ := exists_nat_gt (max C 0 * (M : ℝ))
  refine ⟨omegaLow R, omegaLow_hasNaturalDensity_zero R, ?_⟩
  intro n hn
  by_cases hav : ∀ p ∈ primePrefix M, ¬ p ∣ n
  · exact Or.inl hav
  · by_cases hlow : n ∈ omegaLow R
    · exact Or.inr hlow
    · exfalso
      push Not at hav
      obtain ⟨p, hpS, hpn⟩ := hav
      have hpprime : p.Prime := (Finset.mem_filter.mp hpS).2
      have hpM : p < M := Finset.mem_range.mp (Finset.mem_filter.mp hpS).1
      have hOmega : R ≤ ArithmeticFunction.cardFactors n := by
        have : ¬ ArithmeticFunction.cardFactors n < R := by
          intro hlt
          exact hlow ⟨hn.1, hlt⟩
        omega
      have hp0 : (0 : ℝ) < p := by exact_mod_cast hpprime.pos
      have hCp : C * (p : ℝ) < (ArithmeticFunction.cardFactors n : ℝ) := by
        calc
          C * (p : ℝ) ≤ max C 0 * (p : ℝ) :=
            mul_le_mul_of_nonneg_right (le_max_left C 0) (Nat.cast_nonneg p)
          _ ≤ max C 0 * (M : ℝ) := by
            exact mul_le_mul_of_nonneg_left (by exact_mod_cast hpM.le)
              (le_max_right C 0)
          _ < (R : ℕ) := hR
          _ ≤ (ArithmeticFunction.cardFactors n : ℕ) := by exact_mod_cast hOmega
      have hClower : C < (ArithmeticFunction.cardFactors n : ℝ) / p :=
        (lt_div_iff₀ hp0).2 hCp
      exact (not_lt_of_ge hn.2) (hClower.trans_le (hlower hn.1 hpprime hpn))

/-- Combining Tao's comparison with `τ(n / p) ≥ Ω(n)`. -/
lemma cardFactors_div_prime_le_G {n p : ℕ} (hn : n ≠ 0)
    (hp : p.Prime) (hpn : p ∣ n) :
    (ArithmeticFunction.cardFactors n : ℝ) / p ≤ G n := by
  have hpR : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  calc
    (ArithmeticFunction.cardFactors n : ℝ) / p ≤
        ((n / p).divisors.card : ℝ) / p := by
      exact div_le_div_of_nonneg_right
        (by exact_mod_cast cardFactors_le_card_divisors_div_prime hn hp hpn) hpR
    _ ≤ G n := tao_lower_bound hn hp.one_lt hpn

lemma zeroSingleton_hasNaturalDensity_zero :
    Erdos459.has_natural_density ({0} : Set ℕ) 0 := by
  change Erdos459.has_natural_density {n : ℕ | n = 0} 0
  refine squeeze_zero_norm' (a := fun n : ℕ => 1 / (n : ℝ)) ?_ ?_
  · norm_num [Finset.filter_eq']
    exact ⟨1, fun n hn ↦ by rw [if_pos (by omega)]; norm_num⟩
  · exact tendsto_one_div_atTop_nhds_zero_nat

/-- Every fixed sublevel set of `G` has natural density zero. -/
theorem G_sublevel_hasNaturalDensity_zero (C : ℝ) :
    Erdos459.has_natural_density {n : ℕ | G n ≤ C} 0 := by
  let B : Set ℕ := {n : ℕ | n ≠ 0 ∧ G n ≤ C}
  have hB : Erdos459.has_natural_density B 0 :=
    sublevel_hasNaturalDensity_zero_of_cardFactors_div_prime_lower
      G cardFactors_div_prime_le_G C
  apply naturalDensity_zero_mono
    (B := B ∪ ({0} : Set ℕ))
  · intro n hn
    by_cases hn0 : n = 0
    · exact Or.inr (by simp [hn0])
    · exact Or.inl ⟨hn0, hn⟩
  · exact naturalDensity_zero_union hB zeroSingleton_hasNaturalDensity_zero

lemma hasDensity_of_hasNaturalDensity (S : Set ℕ) (d : ℝ)
    (h : Erdos459.has_natural_density S d) : S.HasDensity d := by
  classical
  rw [Set.HasDensity]
  rw [Erdos459.has_natural_density] at h
  exact h.congr' (Filter.Eventually.of_forall fun n ↦ by
    simp only [Set.partialDensity, Set.inter_univ, Set.univ_inter,
      Set.ncard_Iio_nat]
    have hcard : (S ∩ Set.Iio n).ncard =
        ((Finset.range n).filter fun m ↦ m ∈ S).card := by
      rw [Set.ncard_eq_toFinset_card _
        ((Set.finite_Iio n).subset Set.inter_subset_right)]
      congr 1
      ext m
      simp [and_comm]
    rw [hcard])

lemma hasDensity_one_of_compl_ratio_tendsto_zero (S : Set ℕ)
    (h : Tendsto
      (fun N : ℕ ↦ (((Sᶜ ∩ Set.Iio N).ncard : ℕ) : ℝ) / N)
      atTop (nhds 0)) :
    S.HasDensity 1 := by
  rw [Set.HasDensity]
  have ht : Tendsto
      (fun N : ℕ ↦ (1 : ℝ) - (((Sᶜ ∩ Set.Iio N).ncard : ℕ) : ℝ) / N)
      atTop (nhds ((1 : ℝ) - 0)) := tendsto_const_nhds.sub h
  simpa only [sub_zero] using ht.congr' (by
    filter_upwards [eventually_gt_atTop 0] with N hN
    simp only [Set.partialDensity, Set.inter_univ, Set.univ_inter,
      Set.ncard_Iio_nat]
    have hdisj : Disjoint (S ∩ Set.Iio N) (Sᶜ ∩ Set.Iio N) := by
      exact Set.disjoint_left.mpr fun x hxS hxC ↦ hxC.1 hxS.1
    have hunion : (S ∩ Set.Iio N) ∪ (Sᶜ ∩ Set.Iio N) = Set.Iio N := by
      ext x
      by_cases hx : x ∈ S <;> simp [hx]
    have hcard : (S ∩ Set.Iio N).ncard + (Sᶜ ∩ Set.Iio N).ncard = N := by
      rw [← Set.ncard_union_eq hdisj, hunion]
      simp
    have hcardR : ((S ∩ Set.Iio N).ncard : ℝ) +
        ((Sᶜ ∩ Set.Iio N).ncard : ℝ) = (N : ℝ) := by
      exact_mod_cast hcard
    have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
    field_simp
    linarith [hcardR])

/-- The affirmative answer to the first question of Problem 673. -/
theorem G_tendsToInfinityAlmostAll : TendsToInfinityAlmostAll G := by
  intro C
  let B : Set ℕ := {n : ℕ | G n ≤ C}
  have hBnat : Erdos459.has_natural_density B 0 :=
    G_sublevel_hasNaturalDensity_zero C
  have hB : B.HasDensity 0 := hasDensity_of_hasNaturalDensity B 0 hBnat
  apply hasDensity_one_of_compl_ratio_tendsto_zero
  have hBt : Tendsto
      (fun N : ℕ ↦ (((B ∩ Set.Iio N).ncard : ℕ) : ℝ) / N)
      atTop (nhds 0) := by
    rw [Set.HasDensity] at hB
    simpa only [Set.partialDensity, Set.inter_univ, Set.univ_inter,
      Set.ncard_Iio_nat] using hB
  have hset : ({n : ℕ | C < G n}ᶜ : Set ℕ) = B := by
    ext n
    change (¬ C < G n) ↔ G n ≤ C
    exact not_lt
  simpa only [hset] using hBt

/-- The divisor sum counts factor pairs. -/
lemma tauSum_eq_floorSum (X : ℕ) :
    tauSum X = ∑ d ∈ Finset.Ioc 0 X, ((X / d : ℕ) : ℝ) := by
  rw [tauSum, show Finset.Icc 1 X = Finset.Ioc 0 X by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_Ioc]
    omega]
  norm_cast
  simpa only [ArithmeticFunction.sigma_zero_apply] using
    ArithmeticFunction.sum_Ioc_sigma0_eq_sum_div X

lemma mul_harmonic_eq (X : ℕ) :
    (X : ℝ) * (harmonic X : ℝ) =
      ∑ d ∈ Finset.Ioc 0 X, (X : ℝ) / d := by
  rw [harmonic_eq_sum_Icc]
  push_cast
  rw [Finset.mul_sum,
    show Finset.Icc 1 X = Finset.Ioc 0 X by
      ext n
      simp only [Finset.mem_Icc, Finset.mem_Ioc]
      omega]
  simp only [div_eq_mul_inv]

lemma floorSum_le_mul_harmonic (X : ℕ) :
    (∑ d ∈ Finset.Ioc 0 X, ((X / d : ℕ) : ℝ)) ≤
      (X : ℝ) * (harmonic X : ℝ) := by
  rw [mul_harmonic_eq]
  exact Finset.sum_le_sum fun _ _ ↦ Nat.cast_div_le

lemma mul_harmonic_le_floorSum_add (X : ℕ) :
    (X : ℝ) * (harmonic X : ℝ) ≤
      (∑ d ∈ Finset.Ioc 0 X, ((X / d : ℕ) : ℝ)) + X := by
  rw [mul_harmonic_eq]
  calc
    ∑ d ∈ Finset.Ioc 0 X, (X : ℝ) / d
        ≤ ∑ d ∈ Finset.Ioc 0 X, (((X / d : ℕ) : ℝ) + 1) := by
          apply Finset.sum_le_sum
          intro d hd
          have hdpos : 0 < d := (Finset.mem_Ioc.mp hd).1
          exact le_of_lt <| by
            rw [div_lt_iff₀ (Nat.cast_pos.mpr hdpos)]
            norm_cast
            simpa [mul_comm] using Nat.lt_mul_div_succ X hdpos
    _ = (∑ d ∈ Finset.Ioc 0 X, ((X / d : ℕ) : ℝ)) + X := by
      simp [Finset.sum_add_distrib]

lemma tauSum_sub_mul_harmonic_isBigO :
    (fun X : ℕ ↦ tauSum X - (X : ℝ) * (harmonic X : ℝ))
      =O[atTop] (fun X : ℕ ↦ (X : ℝ)) := by
  refine Asymptotics.IsBigO.of_bound 1 (.of_forall fun X ↦ ?_)
  simp only [Real.norm_eq_abs, one_mul]
  nth_rewrite 2 [abs_of_nonneg (Nat.cast_nonneg X)]
  rw [tauSum_eq_floorSum]
  have hle := floorSum_le_mul_harmonic X
  have hlt := mul_harmonic_le_floorSum_add X
  rw [abs_of_nonpos (sub_nonpos.mpr hle)]
  linarith

lemma natCast_isLittleO_natCast_mul_log :
    (fun X : ℕ ↦ (X : ℝ)) =o[atTop]
      (fun X : ℕ ↦ (X : ℝ) * Real.log X) := by
  have hlog : (fun _ : ℕ ↦ (1 : ℝ)) =o[atTop]
      (fun X : ℕ ↦ Real.log X) := by
    rw [Asymptotics.isLittleO_const_left]
    right
    have ht := tendsto_norm_atTop_atTop.comp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
    exact ht.congr' (Filter.Eventually.of_forall fun _ ↦ rfl)
  simpa only [mul_one] using
    (Asymptotics.isBigO_refl (fun X : ℕ ↦ (X : ℝ)) atTop).mul_isLittleO hlog

lemma harmonic_isEquivalent_log :
    (fun X : ℕ ↦ (harmonic X : ℝ)) ~[atTop]
      (fun X : ℕ ↦ Real.log X) := by
  apply Asymptotics.IsLittleO.isEquivalent
  exact (Real.tendsto_harmonic_sub_log.isBigO_one ℝ).trans_isLittleO
    ((Real.isLittleO_const_log_atTop (c := (1 : ℝ))).comp_tendsto
      tendsto_natCast_atTop_atTop)

/-- The classical leading term for the divisor summatory function. -/
theorem tauSum_isEquivalent :
    (fun X : ℕ ↦ tauSum X) ~[atTop]
      (fun X : ℕ ↦ (X : ℝ) * Real.log X) := by
  have hmain :
      (fun X : ℕ ↦ (X : ℝ) * (harmonic X : ℝ)) ~[atTop]
        (fun X : ℕ ↦ (X : ℝ) * Real.log X) :=
    (Asymptotics.IsEquivalent.refl :
      (fun X : ℕ ↦ (X : ℝ)) ~[atTop] (fun X : ℕ ↦ (X : ℝ))).mul
        harmonic_isEquivalent_log
  rw [Asymptotics.IsEquivalent]
  have herr :
      (fun X : ℕ ↦ tauSum X - (X : ℝ) * (harmonic X : ℝ))
        =o[atTop] (fun X : ℕ ↦ (X : ℝ) * Real.log X) :=
    tauSum_sub_mul_harmonic_isBigO.trans_isLittleO
      natCast_isLittleO_natCast_mul_log
  have hsum := herr.add hmain.isLittleO
  refine hsum.congr' ?_ (Filter.Eventually.of_forall fun _ ↦ rfl)
  filter_upwards with X
  simp only [Pi.sub_apply]
  ring

/-- The deficit between the divisor count and `G` is nonnegative. -/
lemma G_deficit_nonneg (n : ℕ) :
    0 ≤ (n.divisors.card : ℝ) - G n :=
  sub_nonneg.mpr (G_le_card_divisors n)

/-- The two elementary deficit bounds, combined geometrically.  This is the
pointwise estimate used by the fractional-moment argument in
`Erdos673Mean`. -/
lemma G_deficit_le_weighted_sqrtTau (n : ℕ) :
    (n.divisors.card : ℝ) - G n ≤
      Erdos673Mean.sqrtTau n * Real.sqrt (1 + Real.log (n : ℝ)) := by
  by_cases hn : n = 0
  · subst n
    have hG0 : G 0 = 0 :=
      le_antisymm (by simpa using G_le_card_divisors 0) (G_nonneg 0)
    simp [hG0, Erdos673Mean.sqrtTau]
  · let D : ℝ := (n.divisors.card : ℝ) - G n
    let L : ℝ := 1 + Real.log (n : ℝ)
    have hD0 : 0 ≤ D := G_deficit_nonneg n
    have hDtau : D ≤ (n.divisors.card : ℝ) := by
      dsimp [D]
      linarith [G_nonneg n]
    have hDL : D ≤ L := by
      simpa only [D, L] using logarithmic_deficit_bound hn
    have hsq : D ^ 2 ≤ (n.divisors.card : ℝ) * L := by
      simpa only [pow_two] using
        mul_le_mul hDtau hDL hD0 (Nat.cast_nonneg n.divisors.card)
    calc
      D ≤ Real.sqrt ((n.divisors.card : ℝ) * L) :=
        Real.le_sqrt_of_sq_le hsq
      _ = Real.sqrt (n.divisors.card : ℝ) * Real.sqrt L := by
        rw [Real.sqrt_mul (Nat.cast_nonneg n.divisors.card)]
      _ = Erdos673Mean.sqrtTau n *
          Real.sqrt (1 + Real.log (n : ℝ)) := by
        rfl

/-- The asymptotic formula requested in Problem 673:
`∑_{n ≤ X} G(n) ∼ X log X`. -/
theorem GSum_isEquivalent :
    (fun X : ℕ ↦ GSum X) ~[atTop]
      (fun X : ℕ ↦ (X : ℝ) * Real.log X) := by
  simpa only [GSum, Erdos673Mean.statisticSum,
      HalberstamScratch.partialSum] using
    Erdos673Mean.statisticSum_isEquivalent_of_weighted_sqrtTau_deficit
      G G_deficit_nonneg G_deficit_le_weighted_sqrtTau

/-- Erdős's ``easy'' consequence: the mean value of `G` tends to infinity. -/
theorem G_average_tendsto_atTop :
    Tendsto (fun X : ℕ ↦ GSum X / (X : ℝ)) atTop atTop := by
  have hdiv :
      (fun X : ℕ ↦ GSum X / (X : ℝ)) ~[atTop]
        (fun X : ℕ ↦ ((X : ℝ) * Real.log X) / (X : ℝ)) :=
    GSum_isEquivalent.div
      (Asymptotics.IsEquivalent.refl :
        (fun X : ℕ ↦ (X : ℝ)) ~[atTop] (fun X : ℕ ↦ (X : ℝ)))
  have hcancel :
      (fun X : ℕ ↦ ((X : ℝ) * Real.log X) / (X : ℝ)) =ᶠ[atTop]
        (fun X : ℕ ↦ Real.log X) := by
    filter_upwards [eventually_gt_atTop 0] with X hX
    field_simp
  have havg := hdiv.congr_right hcancel
  exact havg.symm.tendsto_atTop tendsto_log_coe_at_top

/-- Complete formal resolution of Erdős Problem 673: `G(n)` tends to infinity
on a set of natural density one, and its summatory function has leading term
`X log X`. -/
theorem erdos_673 :
    TendsToInfinityAlmostAll G ∧
      (fun X : ℕ ↦ GSum X) ~[atTop]
        (fun X : ℕ ↦ (X : ℝ) * Real.log X) ∧
      Tendsto (fun X : ℕ ↦ GSum X / (X : ℝ)) atTop atTop :=
  ⟨G_tendsToInfinityAlmostAll, GSum_isEquivalent,
    G_average_tendsto_atTop⟩

#print axioms erdos_673

end

end Erdos673
