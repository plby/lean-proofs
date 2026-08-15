import ErdosProblems.Erdos448.Lemma4MathLean

open scoped BigOperators Topology
open Filter Finset

namespace Lemma4FirstMoment448

attribute [local instance] Classical.propDecidable

/-!
The exponential-moment arithmetic functions used in the proof of the
specialized divisor-normal-order estimate.  This file deliberately keeps the
cutoff real: it therefore applies directly to `etGridCutoff` without a
rounding lemma.
-/

noncomputable def omegaBelow (d : ℕ) (u : ℝ) : ℕ :=
  (d.primeFactorsList.filter fun p : ℕ ↦ (p : ℝ) < u).length

lemma omegaBelow_eq_mathLean (d : ℕ) (u : ℝ) :
    omegaBelow d u = Erdos448Lemma4Scratch.omegaBelowReal d u := by
  unfold omegaBelow Erdos448Lemma4Scratch.omegaBelowReal
  generalize d.primeFactorsList = l
  induction l with
  | nil => simp
  | cons p l ih =>
      by_cases hp : (p : ℝ) < u <;> simp [hp, ih]

lemma omegaBelow_one (u : ℝ) : omegaBelow 1 u = 0 := by
  simp [omegaBelow]

lemma omegaBelow_mul {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) (u : ℝ) :
    omegaBelow (a * b) u = omegaBelow a u + omegaBelow b u := by
  unfold omegaBelow
  have hp := (Nat.perm_primeFactorsList_mul ha hb).filter
    (fun p : ℕ ↦ (p : ℝ) < u)
  simpa using hp.length_eq

lemma omegaBelow_prime_pow {p j : ℕ} (hp : p.Prime) (u : ℝ) :
    omegaBelow (p ^ j) u = if (p : ℝ) < u then j else 0 := by
  rw [omegaBelow, hp.primeFactorsList_pow]
  by_cases hpu : (p : ℝ) < u <;> simp [hpu]

/-- The completely multiplicative Rankin weight `y ^ Ω(d,u)`, with the
standard zero value required by `ArithmeticFunction`. -/
noncomputable def omegaRankinWeight (y u : ℝ) (d : ℕ) : ℝ :=
  if d = 0 then 0 else y ^ omegaBelow d u

@[simp] lemma omegaRankinWeight_zero (y u : ℝ) :
    omegaRankinWeight y u 0 = 0 := by simp [omegaRankinWeight]

@[simp] lemma omegaRankinWeight_one (y u : ℝ) :
    omegaRankinWeight y u 1 = 1 := by simp [omegaRankinWeight, omegaBelow_one]

lemma omegaRankinWeight_nonneg {y : ℝ} (hy : 0 ≤ y) (u : ℝ) (d : ℕ) :
    0 ≤ omegaRankinWeight y u d := by
  simp only [omegaRankinWeight]
  split_ifs
  · exact le_rfl
  · positivity

lemma omegaRankinWeight_mul {a b : ℕ} (hab : a.Coprime b) (y u : ℝ) :
    omegaRankinWeight y u (a * b) =
      omegaRankinWeight y u a * omegaRankinWeight y u b := by
  by_cases ha : a = 0
  · subst a
    have hb : b = 1 := by simpa using hab
    subst b
    simp
  by_cases hb : b = 0
  · subst b
    have ha1 : a = 1 := by simpa [Nat.coprime_comm] using hab
    subst a
    simp
  simp only [omegaRankinWeight, if_neg ha, if_neg hb, if_neg (Nat.mul_ne_zero ha hb)]
  rw [omegaBelow_mul ha hb, pow_add]

noncomputable def omegaRankinAF (y u : ℝ) : ArithmeticFunction ℝ :=
  ⟨omegaRankinWeight y u, omegaRankinWeight_zero y u⟩

lemma omegaRankinAF_multiplicative (y u : ℝ) :
    ArithmeticFunction.IsMultiplicative (omegaRankinAF y u) := by
  refine ⟨omegaRankinWeight_one y u, ?_⟩
  intro a b hab
  exact omegaRankinWeight_mul hab y u

/-- The numerator `sum_{d|n} y ^ Ω(d,u)` as a Dirichlet convolution. -/
noncomputable def divisorMomentNumeratorAF (y u : ℝ) : ArithmeticFunction ℝ :=
  (ArithmeticFunction.zeta : ArithmeticFunction ℝ) * omegaRankinAF y u

lemma divisorMomentNumeratorAF_apply (y u : ℝ) (n : ℕ) :
    divisorMomentNumeratorAF y u n =
      ∑ d ∈ n.divisors, omegaRankinWeight y u d := by
  rw [divisorMomentNumeratorAF, ArithmeticFunction.coe_zeta_mul_apply]
  rfl

lemma divisorMomentNumeratorAF_multiplicative (y u : ℝ) :
    ArithmeticFunction.IsMultiplicative (divisorMomentNumeratorAF y u) :=
  ArithmeticFunction.isMultiplicative_zeta.natCast.mul
    (omegaRankinAF_multiplicative y u)

/-- Normalized exponential moment of `Ω(d,u)` over divisors `d | n`. -/
noncomputable def divisorMoment (y u : ℝ) (n : ℕ) : ℝ :=
  if n = 0 then 0 else
    divisorMomentNumeratorAF y u n / (n.divisors.card : ℝ)

@[simp] lemma divisorMoment_zero (y u : ℝ) : divisorMoment y u 0 = 0 := by
  simp [divisorMoment]

@[simp] lemma divisorMoment_one (y u : ℝ) : divisorMoment y u 1 = 1 := by
  simp [divisorMoment, divisorMomentNumeratorAF_apply]

lemma divisorMoment_nonneg {y : ℝ} (hy : 0 ≤ y) (u : ℝ) (n : ℕ) :
    0 ≤ divisorMoment y u n := by
  simp only [divisorMoment]
  split_ifs
  · exact le_rfl
  · exact div_nonneg
      (by
        rw [divisorMomentNumeratorAF_apply]
        exact Finset.sum_nonneg fun d hd ↦ omegaRankinWeight_nonneg hy u d)
      (Nat.cast_nonneg _)

lemma divisorMoment_eq_divisor_average {y u : ℝ} {n : ℕ} (hn : n ≠ 0) :
    divisorMoment y u n =
      (∑ d ∈ n.divisors, y ^ omegaBelow d u) / (n.divisors.card : ℝ) := by
  simp only [divisorMoment, if_neg hn, divisorMomentNumeratorAF_apply]
  apply congrArg (fun z : ℝ ↦ z / (n.divisors.card : ℝ))
  apply Finset.sum_congr rfl
  intro d hd
  rw [omegaRankinWeight, if_neg (Nat.ne_of_gt (Nat.pos_of_mem_divisors hd))]

lemma divisorMoment_mul {a b : ℕ} (hab : a.Coprime b) (y u : ℝ) :
    divisorMoment y u (a * b) = divisorMoment y u a * divisorMoment y u b := by
  by_cases ha : a = 0
  · subst a
    have hb : b = 1 := by simpa using hab
    subst b
    simp
  by_cases hb : b = 0
  · subst b
    have ha1 : a = 1 := by simpa [Nat.coprime_comm] using hab
    subst a
    simp
  have hnum := (divisorMomentNumeratorAF_multiplicative y u).map_mul_of_coprime hab
  have hcard := hab.card_divisors_mul
  simp only [divisorMoment, if_neg ha, if_neg hb, if_neg (Nat.mul_ne_zero ha hb)]
  rw [hnum, hcard]
  push_cast
  have hca : (a.divisors.card : ℝ) ≠ 0 := by
    exact_mod_cast (Finset.card_ne_zero.mpr
      ⟨1, Nat.one_mem_divisors.mpr ha⟩)
  have hcb : (b.divisors.card : ℝ) ≠ 0 := by
    exact_mod_cast (Finset.card_ne_zero.mpr
      ⟨1, Nat.one_mem_divisors.mpr hb⟩)
  field_simp [hca, hcb]

noncomputable def divisorMomentAF (y u : ℝ) : ArithmeticFunction ℝ :=
  ⟨divisorMoment y u, divisorMoment_zero y u⟩

lemma divisorMomentAF_multiplicative (y u : ℝ) :
    ArithmeticFunction.IsMultiplicative (divisorMomentAF y u) := by
  refine ⟨divisorMoment_one y u, ?_⟩
  intro a b hab
  exact divisorMoment_mul hab y u

lemma divisorMoment_prime_pow (y u : ℝ) {p j : ℕ} (hp : p.Prime) :
    divisorMoment y u (p ^ j) =
      (∑ i ∈ Finset.range (j + 1),
        y ^ (if (p : ℝ) < u then i else 0)) / (j + 1 : ℝ) := by
  have hpj : p ^ j ≠ 0 := pow_ne_zero _ hp.ne_zero
  rw [divisorMoment_eq_divisor_average hpj, Nat.divisors_prime_pow hp]
  simp only [Finset.card_map, Finset.card_range]
  rw [Finset.sum_map]
  by_cases hpu : (p : ℝ) < u <;>
    simp [omegaBelow_prime_pow hp u, hpu, Nat.cast_add]

lemma divisorMoment_prime_pow_eq_one_of_not_lt (y u : ℝ) {p j : ℕ}
    (hp : p.Prime) (hpu : ¬(p : ℝ) < u) :
    divisorMoment y u (p ^ j) = 1 := by
  rw [divisorMoment_prime_pow y u hp]
  simp [hpu, show (j + 1 : ℝ) ≠ 0 by positivity]

lemma divisorMoment_prime_pow_le_pow {y : ℝ} (hy : 1 ≤ y)
    (u : ℝ) {p j : ℕ} (hp : p.Prime) :
    divisorMoment y u (p ^ j) ≤ y ^ j := by
  rw [divisorMoment_prime_pow y u hp]
  have hden : (0 : ℝ) < j + 1 := by positivity
  apply (div_le_iff₀ hden).2
  calc
    (∑ i ∈ Finset.range (j + 1),
      y ^ (if (p : ℝ) < u then i else 0)) ≤
        ∑ i ∈ Finset.range (j + 1), y ^ j := by
      apply Finset.sum_le_sum
      intro i hi
      split_ifs
      · exact pow_le_pow_right₀ hy
          (Nat.le_of_lt_succ (Finset.mem_range.mp hi))
      · simpa using one_le_pow₀ (n := j) hy
    _ = (j + 1 : ℝ) * y ^ j := by
      simp [Finset.sum_const, nsmul_eq_mul]
    _ = y ^ j * (j + 1 : ℝ) := by ring

lemma divisorMoment_prime_pow_le_one {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ 1)
    (u : ℝ) {p j : ℕ} (hp : p.Prime) :
    divisorMoment y u (p ^ j) ≤ 1 := by
  rw [divisorMoment_prime_pow y u hp]
  have hden : (0 : ℝ) < j + 1 := by positivity
  apply (div_le_iff₀ hden).2
  calc
    (∑ i ∈ Finset.range (j + 1),
      y ^ (if (p : ℝ) < u then i else 0)) ≤
        ∑ i ∈ Finset.range (j + 1), (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro i hi
      exact pow_le_one₀ hy0 hy1
    _ = (j + 1 : ℝ) := by simp
    _ = 1 * (j + 1 : ℝ) := by ring

/-! ## Pointwise Rankin bounds -/

noncomputable def rankinScale (c y : ℝ) : ℝ :=
  Real.exp (-c * Real.log y)

lemma rankinScale_pos (c y : ℝ) : 0 < rankinScale c y :=
  Real.exp_pos _

lemma one_le_rankinScale_mul_pow_of_one_lt
    {c y : ℝ} {m : ℕ} (hy : 1 < y) (hcm : c ≤ (m : ℝ)) :
    1 ≤ rankinScale c y * y ^ m := by
  have hy0 : 0 < y := zero_lt_one.trans hy
  rw [rankinScale, ← Real.exp_log hy0, ← Real.exp_nat_mul,
    ← Real.exp_add, ← Real.exp_zero]
  apply Real.exp_le_exp.mpr
  rw [Real.log_exp]
  have hlog : 0 < Real.log y := Real.log_pos hy
  nlinarith

lemma one_le_rankinScale_mul_pow_of_lt_one
    {c y : ℝ} {m : ℕ} (hy0 : 0 < y) (hy1 : y < 1)
    (hmc : (m : ℝ) ≤ c) :
    1 ≤ rankinScale c y * y ^ m := by
  rw [rankinScale, ← Real.exp_log hy0, ← Real.exp_nat_mul,
    ← Real.exp_add, ← Real.exp_zero]
  apply Real.exp_le_exp.mpr
  rw [Real.log_exp]
  have hlog : Real.log y < 0 := Real.log_neg hy0 hy1
  nlinarith

/-- Proportion of divisors satisfying a predicate.  As elsewhere in the
development, its value at `0` is set to zero. -/
noncomputable def divisorPredicateFraction (R : ℕ → Prop) (n : ℕ) : ℝ :=
  if n = 0 then 0 else
    (((n.divisors.filter R).card : ℕ) : ℝ) / n.divisors.card

lemma divisorPredicateFraction_nonneg (R : ℕ → Prop) (n : ℕ) :
    0 ≤ divisorPredicateFraction R n := by
  simp only [divisorPredicateFraction]
  split_ifs
  · exact le_rfl
  · positivity

lemma divisorPredicateFraction_le_one (R : ℕ → Prop) (n : ℕ) :
    divisorPredicateFraction R n ≤ 1 := by
  simp only [divisorPredicateFraction]
  split_ifs with hn
  · norm_num
  · have htau : 0 < (n.divisors.card : ℝ) := by
      exact_mod_cast Finset.card_pos.mpr
        ⟨1, Nat.one_mem_divisors.mpr hn⟩
    apply (div_le_one htau).2
    exact_mod_cast Finset.card_filter_le n.divisors R

lemma divisorPredicateFraction_mono {R S : ℕ → Prop}
    (hRS : ∀ d, R d → S d) (n : ℕ) :
    divisorPredicateFraction R n ≤ divisorPredicateFraction S n := by
  by_cases hn : n = 0
  · simp [divisorPredicateFraction, hn]
  rw [divisorPredicateFraction, if_neg hn,
    divisorPredicateFraction, if_neg hn]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact_mod_cast Finset.card_le_card fun d hd ↦
    Finset.mem_filter.mpr
      ⟨(Finset.mem_filter.mp hd).1, hRS d (Finset.mem_filter.mp hd).2⟩

lemma divisorPredicateFraction_union_le (R S T : ℕ → Prop)
    (hRST : ∀ d, R d → S d ∨ T d) (n : ℕ) :
    divisorPredicateFraction R n ≤
      divisorPredicateFraction S n + divisorPredicateFraction T n := by
  by_cases hn : n = 0
  · simp [divisorPredicateFraction, hn]
  simp only [divisorPredicateFraction, if_neg hn]
  have hsubset : n.divisors.filter R ⊆
      n.divisors.filter S ∪ n.divisors.filter T := by
    intro d hd
    have hdr := Finset.mem_filter.mp hd
    rcases hRST d hdr.2 with hs | ht
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hdr.1, hs⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hdr.1, ht⟩)
  have hcard : (n.divisors.filter R).card ≤
      (n.divisors.filter S).card + (n.divisors.filter T).card :=
    (Finset.card_le_card hsubset).trans (Finset.card_union_le _ _)
  have htau : 0 ≤ (n.divisors.card : ℝ) := Nat.cast_nonneg _
  rw [← add_div]
  apply div_le_div_of_nonneg_right _ htau
  exact_mod_cast hcard

/-- Generic finite Rankin argument over the divisor set. -/
lemma divisorPredicateFraction_le_rankin
    (R : ℕ → Prop) {y c u : ℝ} (hy : 0 ≤ y)
    (hR : ∀ d, R d →
      1 ≤ rankinScale c y * y ^ omegaBelow d u)
    (n : ℕ) :
    divisorPredicateFraction R n ≤
      rankinScale c y * divisorMoment y u n := by
  by_cases hn : n = 0
  · subst n
    simp [divisorPredicateFraction]
  have htau : 0 < (n.divisors.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr
      ⟨1, Nat.one_mem_divisors.mpr hn⟩
  have hsum : (((n.divisors.filter R).card : ℕ) : ℝ) ≤
      ∑ d ∈ n.divisors,
        rankinScale c y * y ^ omegaBelow d u := by
    calc
      (((n.divisors.filter R).card : ℕ) : ℝ) =
          ∑ d ∈ n.divisors.filter R, (1 : ℝ) := by simp
      _ ≤ ∑ d ∈ n.divisors.filter R,
          rankinScale c y * y ^ omegaBelow d u := by
        exact Finset.sum_le_sum fun d hd ↦ hR d (Finset.mem_filter.mp hd).2
      _ ≤ ∑ d ∈ n.divisors,
          rankinScale c y * y ^ omegaBelow d u := by
        refine Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.filter_subset R n.divisors) ?_
        intro d hd hnot
        exact mul_nonneg (rankinScale_pos c y).le (by positivity)
  rw [divisorPredicateFraction, if_neg hn,
    divisorMoment_eq_divisor_average hn]
  calc
    (((n.divisors.filter R).card : ℕ) : ℝ) / n.divisors.card ≤
        (∑ d ∈ n.divisors,
          rankinScale c y * y ^ omegaBelow d u) / n.divisors.card :=
      div_le_div_of_nonneg_right hsum htau.le
    _ = rankinScale c y *
        ((∑ d ∈ n.divisors, y ^ omegaBelow d u) /
          n.divisors.card) := by
      rw [← Finset.mul_sum]
      ring

lemma upperTailFraction_le_rankin
    {y c u : ℝ} (hy : 1 < y) (n : ℕ) :
    divisorPredicateFraction (fun d ↦ c ≤ (omegaBelow d u : ℝ)) n ≤
      rankinScale c y * divisorMoment y u n := by
  refine divisorPredicateFraction_le_rankin _
    (zero_le_one.trans hy.le) ?_ n
  intro d hd
  exact one_le_rankinScale_mul_pow_of_one_lt hy hd

lemma lowerTailFraction_le_rankin
    {y c u : ℝ} (hy0 : 0 < y) (hy1 : y < 1) (n : ℕ) :
    divisorPredicateFraction (fun d ↦ (omegaBelow d u : ℝ) ≤ c) n ≤
      rankinScale c y * divisorMoment y u n := by
  refine divisorPredicateFraction_le_rankin _ hy0.le ?_ n
  intro d hd
  exact one_le_rankinScale_mul_pow_of_lt_one hy0 hy1 hd

/-! ## The finite grid union bound -/

noncomputable def gridLogScale (ξ : ℝ) (k : ℕ) : ℝ :=
  Real.log
    (Real.log (Erdos448Lemma4Scratch.etGridCutoff ξ k) / Real.log 2)

lemma gridLogScale_eq {ξ : ℝ} (hξ : 1 < ξ) (k : ℕ) :
    gridLogScale ξ k = (k : ℝ) + Real.log (Real.log ξ) := by
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hlogξ : 0 < Real.log ξ := Real.log_pos hξ
  unfold gridLogScale Erdos448Lemma4Scratch.etGridCutoff
  rw [Real.log_exp]
  have hquot :
      (Real.exp (k : ℝ) * Real.log 2 * Real.log ξ) / Real.log 2 =
        Real.exp (k : ℝ) * Real.log ξ := by
    field_simp [ne_of_gt hlog2]
  rw [hquot, Real.log_mul (Real.exp_ne_zero _) (ne_of_gt hlogξ),
    Real.log_exp]

lemma gridLogScale_exp_exp (M k : ℕ) :
    gridLogScale (Real.exp (Real.exp (M : ℝ))) k = (k : ℝ) + M := by
  rw [gridLogScale_eq]
  · simp
  · exact Real.one_lt_exp_iff.mpr (Real.exp_pos _)

noncomputable def upperExponent : ℝ :=
  (49 / 250 : ℝ) - (87 / 125 : ℝ) * Real.log (174 / 125)

noncomputable def lowerExponent : ℝ :=
  (-49 / 250 : ℝ) - (38 / 125 : ℝ) * Real.log (76 / 125)

lemma upperExponent_neg : upperExponent < 0 := by
  have hpos : 0 < ((174 / 125 : ℝ)⁻¹) := by norm_num
  have hne : ((174 / 125 : ℝ)⁻¹) ≠ 1 := by norm_num
  have hlog := Real.log_lt_sub_one_of_pos hpos hne
  rw [Real.log_inv] at hlog
  unfold upperExponent
  norm_num at hlog ⊢
  nlinarith

lemma lowerExponent_neg : lowerExponent < 0 := by
  have hlog := Real.log_lt_sub_one_of_pos
    (show 0 < (125 / 76 : ℝ) by norm_num)
    (show (125 / 76 : ℝ) ≠ 1 by norm_num)
  have hinv : (76 / 125 : ℝ) = (125 / 76 : ℝ)⁻¹ := by norm_num
  unfold lowerExponent
  rw [hinv, Real.log_inv]
  norm_num at hlog ⊢
  nlinarith

lemma upper_rankin_exponent_identity (A : ℝ) :
    rankinScale ((87 / 125 : ℝ) * A) (174 / 125) *
        Real.exp (((174 / 125 : ℝ) - 1) / 2 * A) =
      Real.exp (upperExponent * A) := by
  rw [rankinScale, ← Real.exp_add]
  congr 1
  unfold upperExponent
  ring

lemma lower_rankin_exponent_identity (A : ℝ) :
    rankinScale ((38 / 125 : ℝ) * A) (76 / 125) *
        Real.exp (((76 / 125 : ℝ) - 1) / 2 * A) =
      Real.exp (lowerExponent * A) := by
  rw [rankinScale, ← Real.exp_add]
  congr 1
  unfold lowerExponent
  ring

def gridBad (ξ : ℝ) (k d : ℕ) : Prop :=
  Erdos448Lemma4Scratch.etGridCutoff ξ k < d ∧
    (49 / 250 : ℝ) * gridLogScale ξ k ≤
      Erdos448Lemma4Scratch.etDeviation d
        (Erdos448Lemma4Scratch.etGridCutoff ξ k)

def upperGridTail (ξ : ℝ) (k d : ℕ) : Prop :=
  (87 / 125 : ℝ) * gridLogScale ξ k ≤
    (omegaBelow d (Erdos448Lemma4Scratch.etGridCutoff ξ k) : ℝ)

def lowerGridTail (ξ : ℝ) (k d : ℕ) : Prop :=
  (omegaBelow d (Erdos448Lemma4Scratch.etGridCutoff ξ k) : ℝ) ≤
    (38 / 125 : ℝ) * gridLogScale ξ k

lemma gridBad_imp_tail (ξ : ℝ) (k d : ℕ) (hd : gridBad ξ k d) :
    upperGridTail ξ k d ∨ lowerGridTail ξ k d := by
  let u := Erdos448Lemma4Scratch.etGridCutoff ξ k
  let A := gridLogScale ξ k
  have hdev : (49 / 250 : ℝ) * A ≤
      |(omegaBelow d u : ℝ) - (1 / 2 : ℝ) * A| := by
    have h := hd.2
    rw [Erdos448Lemma4Scratch.etDeviation,
      ← omegaBelow_eq_mathLean d u] at h
    exact h
  rcases le_abs.mp hdev with hupper | hlower
  · left
    dsimp [upperGridTail, u, A] at *
    linarith
  · right
    dsimp [lowerGridTail, u, A] at *
    linarith

lemma not_etGridGoodDivisor_iff (ξ : ℝ) (d : ℕ) :
    ¬ Erdos448Lemma4Scratch.etGridGoodDivisor ξ d ↔
      ∃ k < d, gridBad ξ k d := by
  simp [Erdos448Lemma4Scratch.etGridGoodDivisor, gridBad,
    gridLogScale]

noncomputable def gridBadFraction (ξ : ℝ) (k n : ℕ) : ℝ :=
  divisorPredicateFraction (gridBad ξ k) n

lemma gridBadFraction_le_rankin_moments (ξ : ℝ) (k n : ℕ) :
    gridBadFraction ξ k n ≤
      rankinScale ((87 / 125 : ℝ) * gridLogScale ξ k) (174 / 125) *
          divisorMoment (174 / 125) (Erdos448Lemma4Scratch.etGridCutoff ξ k) n +
        rankinScale ((38 / 125 : ℝ) * gridLogScale ξ k) (76 / 125) *
          divisorMoment (76 / 125) (Erdos448Lemma4Scratch.etGridCutoff ξ k) n := by
  calc
    gridBadFraction ξ k n ≤
        divisorPredicateFraction (upperGridTail ξ k) n +
          divisorPredicateFraction (lowerGridTail ξ k) n :=
      divisorPredicateFraction_union_le _ _ _
        (gridBad_imp_tail ξ k) n
    _ ≤ rankinScale ((87 / 125 : ℝ) * gridLogScale ξ k) (174 / 125) *
          divisorMoment (174 / 125)
            (Erdos448Lemma4Scratch.etGridCutoff ξ k) n +
        rankinScale ((38 / 125 : ℝ) * gridLogScale ξ k) (76 / 125) *
          divisorMoment (76 / 125)
            (Erdos448Lemma4Scratch.etGridCutoff ξ k) n := by
      apply add_le_add
      · exact upperTailFraction_le_rankin (by norm_num)
          n
      · exact lowerTailFraction_le_rankin (by norm_num) (by norm_num)
          n

/-- Uniform two-parameter consequence of Halberstam--Richert needed by the
grid argument.  The generic HR theorem supplies such a record: the two fixed
values of `y` can be absorbed into one maximum constant. -/
structure GridMomentBound where
  C : ℝ
  C_nonneg : 0 ≤ C
  M0 : ℕ
  upper : ∀ (M : ℕ), M0 ≤ M → ∀ (k x : ℕ),
    Nat.ceil (Erdos448Lemma4Scratch.etGridCutoff
      (Real.exp (Real.exp (M : ℝ))) k) ≤ x →
    (∑ n ∈ Finset.range x,
      divisorMoment (174 / 125)
        (Erdos448Lemma4Scratch.etGridCutoff
          (Real.exp (Real.exp (M : ℝ))) k) n) ≤
      C * x * Real.exp
        (((174 / 125 : ℝ) - 1) / 2 *
          gridLogScale (Real.exp (Real.exp (M : ℝ))) k)
  lower : ∀ (M : ℕ), M0 ≤ M → ∀ (k x : ℕ),
    Nat.ceil (Erdos448Lemma4Scratch.etGridCutoff
      (Real.exp (Real.exp (M : ℝ))) k) ≤ x →
    (∑ n ∈ Finset.range x,
      divisorMoment (76 / 125)
        (Erdos448Lemma4Scratch.etGridCutoff
          (Real.exp (Real.exp (M : ℝ))) k) n) ≤
      C * x * Real.exp
        (((76 / 125 : ℝ) - 1) / 2 *
          gridLogScale (Real.exp (Real.exp (M : ℝ))) k)

lemma sum_gridBadFraction_le (H : GridMomentBound)
    {M : ℕ} (hM : H.M0 ≤ M) (k x : ℕ) :
    (∑ n ∈ Finset.range x,
      gridBadFraction (Real.exp (Real.exp (M : ℝ))) k n) ≤
      H.C * x *
        (Real.exp (upperExponent *
          gridLogScale (Real.exp (Real.exp (M : ℝ))) k) +
          Real.exp (lowerExponent *
            gridLogScale (Real.exp (Real.exp (M : ℝ))) k)) := by
  let ξ := Real.exp (Real.exp (M : ℝ))
  let su := rankinScale
    ((87 / 125 : ℝ) * gridLogScale ξ k) (174 / 125)
  let sl := rankinScale
    ((38 / 125 : ℝ) * gridLogScale ξ k) (76 / 125)
  by_cases hx : Nat.ceil (Erdos448Lemma4Scratch.etGridCutoff ξ k) ≤ x
  swap
  · have hxu : (x : ℝ) < Erdos448Lemma4Scratch.etGridCutoff ξ k := by
      rw [← Nat.lt_ceil]
      omega
    have hzero : ∀ n ∈ Finset.range x, gridBadFraction ξ k n = 0 := by
      intro n hn
      rw [gridBadFraction, divisorPredicateFraction]
      split_ifs with hn0
      · rfl
      · have hc : (n.divisors.filter (gridBad ξ k)).card = 0 := by
          apply Finset.card_eq_zero.mpr
          apply Finset.filter_eq_empty_iff.mpr
          intro d hd hbad
          have hdn : d ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn0)
            (Nat.dvd_of_mem_divisors hd)
          have hnx : n < x := Finset.mem_range.mp hn
          have hdx : (d : ℝ) < x := by exact_mod_cast hdn.trans_lt hnx
          exact (not_lt_of_ge hdx.le) (hxu.trans hbad.1)
        rw [hc]
        norm_num
    rw [Finset.sum_eq_zero hzero]
    exact mul_nonneg
      (mul_nonneg H.C_nonneg (Nat.cast_nonneg x))
      (add_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)
  calc
    (∑ n ∈ Finset.range x, gridBadFraction ξ k n) ≤
        ∑ n ∈ Finset.range x,
          (su * divisorMoment (174 / 125)
              (Erdos448Lemma4Scratch.etGridCutoff ξ k) n +
            sl * divisorMoment (76 / 125)
              (Erdos448Lemma4Scratch.etGridCutoff ξ k) n) := by
      apply Finset.sum_le_sum
      intro n hn
      simpa [su, sl] using gridBadFraction_le_rankin_moments ξ k n
    _ = su * (∑ n ∈ Finset.range x,
          divisorMoment (174 / 125)
            (Erdos448Lemma4Scratch.etGridCutoff ξ k) n) +
        sl * (∑ n ∈ Finset.range x,
          divisorMoment (76 / 125)
            (Erdos448Lemma4Scratch.etGridCutoff ξ k) n) := by
      rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    _ ≤ su * (H.C * x * Real.exp
          (((174 / 125 : ℝ) - 1) / 2 * gridLogScale ξ k)) +
        sl * (H.C * x * Real.exp
          (((76 / 125 : ℝ) - 1) / 2 * gridLogScale ξ k)) := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left (H.upper M hM k x hx)
          (rankinScale_pos _ _).le
      · exact mul_le_mul_of_nonneg_left (H.lower M hM k x hx)
          (rankinScale_pos _ _).le
    _ = H.C * x *
        (Real.exp (upperExponent * gridLogScale ξ k) +
          Real.exp (lowerExponent * gridLogScale ξ k)) := by
      dsimp [su, sl]
      rw [← upper_rankin_exponent_identity (gridLogScale ξ k),
        ← lower_rankin_exponent_identity (gridLogScale ξ k)]
      ring

/-- A rejected divisor fails at one of the first `n` grid points. -/
lemma rejectedFraction_le_sum_gridBadFraction (ξ : ℝ) (n : ℕ) :
    Erdos448Lemma4Scratch.rejectedFraction
        (Erdos448Lemma4Scratch.etGridGoodDivisor ξ) n ≤
      ∑ k ∈ Finset.range n, gridBadFraction ξ k n := by
  by_cases hn : n = 0
  · subst n
    simp [Erdos448Lemma4Scratch.rejectedFraction]
  let badAt : ℕ → Finset ℕ := fun k ↦ n.divisors.filter (gridBad ξ k)
  have hsubset :
      (n.divisors.filter fun d ↦
        ¬ Erdos448Lemma4Scratch.etGridGoodDivisor ξ d) ⊆
        (Finset.range n).biUnion badAt := by
    intro d hd
    have hdr := Finset.mem_filter.mp hd
    rcases (not_etGridGoodDivisor_iff ξ d).mp hdr.2 with ⟨k, hkd, hbad⟩
    have hdn : d ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn)
      (Nat.dvd_of_mem_divisors hdr.1)
    exact Finset.mem_biUnion.mpr
      ⟨k, Finset.mem_range.mpr (hkd.trans_le hdn),
        Finset.mem_filter.mpr ⟨hdr.1, hbad⟩⟩
  have hcard :
      (n.divisors.filter fun d ↦
        ¬ Erdos448Lemma4Scratch.etGridGoodDivisor ξ d).card ≤
        ∑ k ∈ Finset.range n, (badAt k).card :=
    (Finset.card_le_card hsubset).trans Finset.card_biUnion_le
  have htau : 0 ≤ (n.divisors.card : ℝ) := Nat.cast_nonneg _
  rw [Erdos448Lemma4Scratch.rejectedFraction, if_neg hn]
  simp only [Erdos448Lemma4Scratch.rejectedDivisorMass,
    Erdos448Lemma4Scratch.rejectedDivisors]
  calc
    ((n.divisors.filter fun d ↦
      ¬ Erdos448Lemma4Scratch.etGridGoodDivisor ξ d).card : ℝ) /
        n.divisors.card ≤
        (∑ k ∈ Finset.range n, ((badAt k).card : ℝ)) /
          n.divisors.card := by
      apply div_le_div_of_nonneg_right _ htau
      exact_mod_cast hcard
    _ = ∑ k ∈ Finset.range n, gridBadFraction ξ k n := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro k hk
      simp only [gridBadFraction, divisorPredicateFraction, if_neg hn]
      rfl

lemma gridBadFraction_nonneg (ξ : ℝ) (k n : ℕ) :
    0 ≤ gridBadFraction ξ k n :=
  divisorPredicateFraction_nonneg _ _

lemma sum_rejectedFraction_le_finite_grid (H : GridMomentBound)
    (M : ℕ) (hM : H.M0 ≤ M) (x : ℕ) :
    (∑ n ∈ Finset.range x,
      Erdos448Lemma4Scratch.rejectedFraction
        (Erdos448Lemma4Scratch.etGridGoodDivisor
          (Real.exp (Real.exp (M : ℝ)))) n) ≤
      H.C * x * ∑ k ∈ Finset.range x,
        (Real.exp (upperExponent * ((k : ℝ) + M)) +
          Real.exp (lowerExponent * ((k : ℝ) + M))) := by
  let ξ := Real.exp (Real.exp (M : ℝ))
  have hξ : 1 < ξ := Real.one_lt_exp_iff.mpr (Real.exp_pos _)
  calc
    (∑ n ∈ Finset.range x,
      Erdos448Lemma4Scratch.rejectedFraction
        (Erdos448Lemma4Scratch.etGridGoodDivisor ξ) n) ≤
        ∑ n ∈ Finset.range x,
          ∑ k ∈ Finset.range n, gridBadFraction ξ k n := by
      exact Finset.sum_le_sum fun n hn ↦
        rejectedFraction_le_sum_gridBadFraction ξ n
    _ ≤ ∑ n ∈ Finset.range x,
          ∑ k ∈ Finset.range x, gridBadFraction ξ k n := by
      apply Finset.sum_le_sum
      intro n hn
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.range_mono (Nat.le_of_lt (Finset.mem_range.mp hn)))
        (fun k hk hnot ↦ gridBadFraction_nonneg ξ k n)
    _ = ∑ k ∈ Finset.range x,
          ∑ n ∈ Finset.range x, gridBadFraction ξ k n := by
      rw [Finset.sum_comm]
    _ ≤ ∑ k ∈ Finset.range x,
          H.C * x *
            (Real.exp (upperExponent * gridLogScale ξ k) +
              Real.exp (lowerExponent * gridLogScale ξ k)) := by
      exact Finset.sum_le_sum fun k hk ↦ sum_gridBadFraction_le H hM k x
    _ = H.C * x * ∑ k ∈ Finset.range x,
        (Real.exp (upperExponent * ((k : ℝ) + M)) +
          Real.exp (lowerExponent * ((k : ℝ) + M))) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      rw [gridLogScale_exp_exp M k]

lemma finite_exp_geometric_le {q : ℝ} (hq : q < 0) (M x : ℕ) :
    (∑ k ∈ Finset.range x, Real.exp (q * ((k : ℝ) + M))) ≤
      Real.exp (q * M) / (1 - Real.exp q) := by
  let r := Real.exp q
  have hr0 : 0 ≤ r := (Real.exp_pos q).le
  have hr1 : r < 1 := by
    dsimp [r]
    exact Real.exp_lt_one_iff.mpr hq
  have hgeom := hasSum_geometric_of_lt_one hr0 hr1
  have hfinite : (∑ k ∈ Finset.range x, r ^ k) ≤ (1 - r)⁻¹ := by
    rw [← hgeom.tsum_eq]
    exact hgeom.summable.sum_le_tsum (Finset.range x) (fun k hk ↦ by positivity)
  calc
    (∑ k ∈ Finset.range x, Real.exp (q * ((k : ℝ) + M))) =
        Real.exp (q * M) * ∑ k ∈ Finset.range x, r ^ k := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      dsimp [r]
      rw [← Real.exp_nat_mul]
      rw [← Real.exp_add]
      congr 1
      ring
    _ ≤ Real.exp (q * M) * (1 - r)⁻¹ :=
      mul_le_mul_of_nonneg_left hfinite (Real.exp_pos _).le
    _ = Real.exp (q * M) / (1 - Real.exp q) := by
      dsimp [r]
      rw [div_eq_mul_inv]

lemma sum_rejectedFraction_le_geometric (H : GridMomentBound)
    (M : ℕ) (hM : H.M0 ≤ M) (x : ℕ) :
    (∑ n ∈ Finset.range x,
      Erdos448Lemma4Scratch.rejectedFraction
        (Erdos448Lemma4Scratch.etGridGoodDivisor
          (Real.exp (Real.exp (M : ℝ)))) n) ≤
      H.C * x *
        (Real.exp (upperExponent * M) / (1 - Real.exp upperExponent) +
          Real.exp (lowerExponent * M) / (1 - Real.exp lowerExponent)) := by
  calc
    (∑ n ∈ Finset.range x,
      Erdos448Lemma4Scratch.rejectedFraction
        (Erdos448Lemma4Scratch.etGridGoodDivisor
          (Real.exp (Real.exp (M : ℝ)))) n) ≤
      H.C * x * ∑ k ∈ Finset.range x,
        (Real.exp (upperExponent * ((k : ℝ) + M)) +
          Real.exp (lowerExponent * ((k : ℝ) + M))) :=
      sum_rejectedFraction_le_finite_grid H M hM x
    _ = H.C * x *
        ((∑ k ∈ Finset.range x,
            Real.exp (upperExponent * ((k : ℝ) + M))) +
          ∑ k ∈ Finset.range x,
            Real.exp (lowerExponent * ((k : ℝ) + M))) := by
      rw [Finset.sum_add_distrib]
    _ ≤ H.C * x *
        (Real.exp (upperExponent * M) / (1 - Real.exp upperExponent) +
          Real.exp (lowerExponent * M) / (1 - Real.exp lowerExponent)) := by
      apply mul_le_mul_of_nonneg_left _
        (mul_nonneg H.C_nonneg (Nat.cast_nonneg x))
      exact add_le_add
        (finite_exp_geometric_le upperExponent_neg M x)
        (finite_exp_geometric_le lowerExponent_neg M x)

lemma exp_mul_nat_eq_pow (q : ℝ) (M : ℕ) :
    Real.exp (q * M) = (Real.exp q) ^ M := by
  rw [mul_comm, Real.exp_nat_mul]

lemma gridCoefficient_tendsto_zero (H : GridMomentBound) :
    Tendsto
      (fun M : ℕ ↦ H.C *
        (Real.exp (upperExponent * M) / (1 - Real.exp upperExponent) +
          Real.exp (lowerExponent * M) / (1 - Real.exp lowerExponent)))
      atTop (𝓝 0) := by
  have hru0 : 0 ≤ Real.exp upperExponent := (Real.exp_pos _).le
  have hru1 : Real.exp upperExponent < 1 :=
    Real.exp_lt_one_iff.mpr upperExponent_neg
  have hrl0 : 0 ≤ Real.exp lowerExponent := (Real.exp_pos _).le
  have hrl1 : Real.exp lowerExponent < 1 :=
    Real.exp_lt_one_iff.mpr lowerExponent_neg
  have hu0 : Tendsto (fun M : ℕ ↦ (Real.exp upperExponent) ^ M)
      atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hru0 hru1
  have hl0 : Tendsto (fun M : ℕ ↦ (Real.exp lowerExponent) ^ M)
      atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hrl0 hrl1
  have hu : Tendsto
      (fun M : ℕ ↦ Real.exp (upperExponent * M) /
        (1 - Real.exp upperExponent)) atTop (𝓝 0) := by
    have := hu0.mul_const ((1 - Real.exp upperExponent)⁻¹)
    simpa only [← exp_mul_nat_eq_pow, div_eq_mul_inv, zero_mul] using this
  have hl : Tendsto
      (fun M : ℕ ↦ Real.exp (lowerExponent * M) /
        (1 - Real.exp lowerExponent)) atTop (𝓝 0) := by
    have := hl0.mul_const ((1 - Real.exp lowerExponent)⁻¹)
    simpa only [← exp_mul_nat_eq_pow, div_eq_mul_inv, zero_mul] using this
  have hC : Tendsto (fun _ : ℕ ↦ H.C) atTop (𝓝 H.C) :=
    tendsto_const_nhds
  simpa only [mul_zero, add_zero] using hC.mul (hu.add hl)

/-- Once HR supplies `GridMomentBound`, the first-moment input consumed by
`Lemma4MathLean` follows with the exact numerical constant `1/20`. -/
theorem exists_grid_first_moment (H : GridMomentBound) :
    ∃ ξ : ℝ, 1 < ξ ∧
      ∀ᶠ x : ℕ in atTop,
        (∑ n ∈ Finset.range x,
          Erdos448Lemma4Scratch.rejectedFraction
            (Erdos448Lemma4Scratch.etGridGoodDivisor ξ) n) ≤
          (1 / 20 : ℝ) * x := by
  have hev : ∀ᶠ M : ℕ in atTop,
      H.C *
        (Real.exp (upperExponent * M) / (1 - Real.exp upperExponent) +
          Real.exp (lowerExponent * M) / (1 - Real.exp lowerExponent)) <
        (1 / 20 : ℝ) :=
    (tendsto_order.1 (gridCoefficient_tendsto_zero H)).2 _ (by norm_num)
  have hev' := hev.and (Filter.eventually_ge_atTop H.M0)
  rcases hev'.exists with ⟨M, hsmall, hM0⟩
  refine ⟨Real.exp (Real.exp (M : ℝ)),
    Real.one_lt_exp_iff.mpr (Real.exp_pos _), ?_⟩
  filter_upwards [] with x
  have hbound := sum_rejectedFraction_le_geometric H M hM0 x
  calc
    (∑ n ∈ Finset.range x,
      Erdos448Lemma4Scratch.rejectedFraction
        (Erdos448Lemma4Scratch.etGridGoodDivisor
          (Real.exp (Real.exp (M : ℝ)))) n) ≤
      H.C * x *
        (Real.exp (upperExponent * M) / (1 - Real.exp upperExponent) +
          Real.exp (lowerExponent * M) / (1 - Real.exp lowerExponent)) := hbound
    _ = (H.C *
        (Real.exp (upperExponent * M) / (1 - Real.exp upperExponent) +
          Real.exp (lowerExponent * M) / (1 - Real.exp lowerExponent))) * x := by
      ring
    _ ≤ (1 / 20 : ℝ) * x :=
      mul_le_mul_of_nonneg_right hsmall.le (Nat.cast_nonneg x)

end Lemma4FirstMoment448
