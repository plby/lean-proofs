import ErdosProblems.Erdos587.HooleyDelta

/-!
# Integrable moments of the Hooley divisor count

Each divisor contributes the indicator of a half-open interval of length
one. This gives the first-moment identity and integrability of all positive
integer moments, without a mean-value hypothesis.
-/

open MeasureTheory
open scoped BigOperators

namespace Erdos587

lemma mem_deltaDivisors_iff_log {n d : ℕ} {u : ℝ} :
    d ∈ deltaDivisors n u ↔
      d ∈ n.divisors ∧ Real.log d - 1 ≤ u ∧ u < Real.log d := by
  constructor
  · intro hd
    obtain ⟨hdn, hn, hlow, hupp⟩ := mem_deltaDivisors.mp hd
    have hdiv : d ∈ n.divisors := Nat.mem_divisors.mpr ⟨hdn, hn⟩
    have hdpos : (0 : ℝ) < d := by
      exact_mod_cast Nat.pos_of_mem_divisors hdiv
    refine ⟨hdiv, ?_, (Real.lt_log_iff_exp_lt hdpos).mpr hlow⟩
    have hlog := (Real.log_le_iff_le_exp hdpos).mpr hupp
    linarith
  · rintro ⟨hdiv, hlow, hupp⟩
    obtain ⟨hdn, hn⟩ := Nat.mem_divisors.mp hdiv
    have hdpos : (0 : ℝ) < d := by
      exact_mod_cast Nat.pos_of_mem_divisors hdiv
    apply mem_deltaDivisors.mpr
    refine ⟨hdn, hn, (Real.lt_log_iff_exp_lt hdpos).mp hupp, ?_⟩
    apply (Real.log_le_iff_le_exp hdpos).mp
    linarith

/-- The real-valued local divisor concentration. -/
noncomputable def deltaCount (n : ℕ) (u : ℝ) : ℝ := (deltaDivisors n u).card

lemma deltaCount_nonneg (n : ℕ) (u : ℝ) : 0 ≤ deltaCount n u := by
  unfold deltaCount
  positivity

lemma deltaCount_le_hooleyDelta (n : ℕ) (u : ℝ) :
    deltaCount n u ≤ (hooleyDelta n : ℝ) := by
  unfold deltaCount
  exact_mod_cast card_deltaDivisors_le_hooleyDelta n u

lemma deltaCount_eq_sum_indicator (n : ℕ) (u : ℝ) :
    deltaCount n u = ∑ d ∈ n.divisors,
      (Set.Ico (Real.log d - 1) (Real.log d)).indicator (fun _ : ℝ => (1 : ℝ)) u := by
  classical
  have hset : deltaDivisors n u = n.divisors.filter
      (fun d : ℕ => u ∈ Set.Ico (Real.log d - 1) (Real.log d)) := by
    ext d
    simp only [mem_deltaDivisors_iff_log, Finset.mem_filter, Set.mem_Ico]
  calc
    deltaCount n u = ∑ _d ∈ deltaDivisors n u, (1 : ℝ) := by
      simp [deltaCount]
    _ = ∑ d ∈ n.divisors,
        if u ∈ Set.Ico (Real.log d - 1) (Real.log d) then (1 : ℝ) else 0 := by
      rw [hset, Finset.sum_filter]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro d hd
      simp only [Set.indicator_apply]

lemma integrable_log_divisor_indicator (d : ℕ) :
    Integrable ((Set.Ico (Real.log d - 1) (Real.log d)).indicator
      (fun _ : ℝ => (1 : ℝ))) := by
  apply IntegrableOn.integrable_indicator
  · exact integrableOn_const (by simp)
  · exact measurableSet_Ico

lemma integrable_deltaCount (n : ℕ) : Integrable (deltaCount n) := by
  change Integrable (fun u : ℝ => deltaCount n u)
  have hsum := integrable_finsetSum n.divisors
    (fun d _ => integrable_log_divisor_indicator d)
  simpa only [deltaCount_eq_sum_indicator] using hsum

/-- The first integral moment is exactly the number of divisors. -/
theorem integral_deltaCount (n : ℕ) :
    (∫ u : ℝ, deltaCount n u) = (n.divisors.card : ℝ) := by
  calc
    (∫ u : ℝ, deltaCount n u) =
        ∫ u : ℝ, ∑ d ∈ n.divisors,
          (Set.Ico (Real.log d - 1) (Real.log d)).indicator (fun _ : ℝ => (1 : ℝ)) u := by
      congr 1
      funext u
      exact deltaCount_eq_sum_indicator n u
    _ = ∑ d ∈ n.divisors, ∫ u : ℝ,
        (Set.Ico (Real.log d - 1) (Real.log d)).indicator (fun _ : ℝ => (1 : ℝ)) u :=
      integral_finsetSum n.divisors (fun d _ => integrable_log_divisor_indicator d)
    _ = ∑ _d ∈ n.divisors, (1 : ℝ) := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [integral_indicator_const _ measurableSet_Ico, Real.volume_real_Ico]
      simp
    _ = (n.divisors.card : ℝ) := by simp

lemma deltaCount_pow_succ_le (n q : ℕ) (u : ℝ) :
    deltaCount n u ^ (q + 1) ≤ (hooleyDelta n : ℝ) ^ q * deltaCount n u := by
  rw [pow_succ]
  exact mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (deltaCount_nonneg n u) (deltaCount_le_hooleyDelta n u) q)
    (deltaCount_nonneg n u)

lemma integrable_deltaCount_pow_succ (n q : ℕ) :
    Integrable (fun u : ℝ => deltaCount n u ^ (q + 1)) := by
  apply ((integrable_deltaCount n).const_mul ((hooleyDelta n : ℝ) ^ q)).mono'
    ((integrable_deltaCount n).aestronglyMeasurable.pow (q + 1))
  apply Filter.Eventually.of_forall
  intro u
  change ‖deltaCount n u ^ (q + 1)‖ ≤ (hooleyDelta n : ℝ) ^ q * deltaCount n u
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (deltaCount_nonneg n u) _)]
  exact deltaCount_pow_succ_le n q u

lemma integrable_deltaCount_pow {n q : ℕ} (hq : q ≠ 0) :
    Integrable (fun u : ℝ => deltaCount n u ^ q) := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hq
  exact integrable_deltaCount_pow_succ n r

/-- Integral moments of the local count; positive orders are integrable. -/
noncomputable def deltaMoment (n q : ℕ) : ℝ :=
  ∫ u : ℝ, deltaCount n u ^ q

lemma deltaMoment_nonneg (n q : ℕ) : 0 ≤ deltaMoment n q :=
  integral_nonneg (fun u => pow_nonneg (deltaCount_nonneg n u) q)

@[simp] theorem deltaMoment_one (n : ℕ) :
    deltaMoment n 1 = (n.divisors.card : ℝ) := by
  simpa only [deltaMoment, pow_one] using integral_deltaCount n

theorem deltaMoment_succ_le (n q : ℕ) :
    deltaMoment n (q + 1) ≤ (hooleyDelta n : ℝ) ^ q * n.divisors.card := by
  calc
    deltaMoment n (q + 1) ≤
        ∫ u : ℝ, (hooleyDelta n : ℝ) ^ q * deltaCount n u :=
      integral_mono (integrable_deltaCount_pow_succ n q)
        ((integrable_deltaCount n).const_mul _)
        (deltaCount_pow_succ_le n q)
    _ = _ := by rw [integral_const_mul, integral_deltaCount]

lemma card_divisors_le_deltaMoment (n : ℕ) {q : ℕ} (hq : q ≠ 0) :
    (n.divisors.card : ℝ) ≤ deltaMoment n q := by
  rw [← integral_deltaCount]
  apply integral_mono (integrable_deltaCount n) (integrable_deltaCount_pow hq)
  intro u
  change deltaCount n u ≤ deltaCount n u ^ q
  unfold deltaCount
  exact_mod_cast Nat.le_self_pow hq (deltaDivisors n u).card

lemma deltaMoment_le_card_divisors_pow (n : ℕ) {q : ℕ} (hq : q ≠ 0) :
    deltaMoment n q ≤ (n.divisors.card : ℝ) ^ q := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hq
  have hdelta : (hooleyDelta n : ℝ) ≤ n.divisors.card := by
    exact_mod_cast hooleyDelta_le_card_divisors n
  calc
    deltaMoment n (r + 1) ≤ (hooleyDelta n : ℝ) ^ r * n.divisors.card :=
      deltaMoment_succ_le n r
    _ ≤ (n.divisors.card : ℝ) ^ r * n.divisors.card :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hdelta r) (by positivity)
    _ = _ := (pow_succ _ r).symm

@[simp] lemma deltaMoment_at_one {q : ℕ} (hq : q ≠ 0) : deltaMoment 1 q = 1 := by
  apply le_antisymm
  · simpa using deltaMoment_le_card_divisors_pow 1 hq
  · simpa using card_divisors_le_deltaMoment 1 hq

lemma deltaMoment_mul_le_card_divisors_pow (n : ℕ) {a b : ℕ}
    (ha : a ≠ 0) (hb : b ≠ 0) :
    deltaMoment n a * deltaMoment n b ≤ (n.divisors.card : ℝ) ^ (a + b) := by
  rw [pow_add]
  exact mul_le_mul (deltaMoment_le_card_divisors_pow n ha)
    (deltaMoment_le_card_divisors_pow n hb) (deltaMoment_nonneg n b) (by positivity)

lemma integrable_deltaCount_mixed (n a b : ℕ) (t : ℝ) (hab : a + b ≠ 0) :
    Integrable (fun u : ℝ => deltaCount n u ^ a * deltaCount n (u - t) ^ b) := by
  by_cases ha : a = 0
  · subst a
    simpa only [pow_zero, one_mul] using
      (integrable_deltaCount_pow (n := n) (by simpa using hab)).comp_sub_right t
  · have hi := integrable_deltaCount_pow (n := n) ha
    have hmeas := ((integrable_deltaCount n).aestronglyMeasurable.pow a).mul
      (((integrable_deltaCount n).comp_sub_right t).aestronglyMeasurable.pow b)
    apply (hi.mul_const ((hooleyDelta n : ℝ) ^ b)).mono' hmeas
    apply Filter.Eventually.of_forall
    intro u
    change ‖deltaCount n u ^ a * deltaCount n (u - t) ^ b‖ ≤
      deltaCount n u ^ a * (hooleyDelta n : ℝ) ^ b
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg
      (pow_nonneg (deltaCount_nonneg n u) a)
      (pow_nonneg (deltaCount_nonneg n (u - t)) b))]
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (deltaCount_nonneg n (u - t))
        (deltaCount_le_hooleyDelta n (u - t)) b)
      (pow_nonneg (deltaCount_nonneg n u) a)

/-- Correlation of two positive-order local divisor moments. Zero exponents
are allowed as long as their sum is positive when integrability is needed. -/
noncomputable def deltaMixedMoment (n a b : ℕ) (t : ℝ) : ℝ :=
  ∫ u : ℝ, deltaCount n u ^ a * deltaCount n (u - t) ^ b

lemma deltaMixedMoment_nonneg (n a b : ℕ) (t : ℝ) :
    0 ≤ deltaMixedMoment n a b t :=
  integral_nonneg (fun u => mul_nonneg (pow_nonneg (deltaCount_nonneg n u) a)
    (pow_nonneg (deltaCount_nonneg n (u - t)) b))

lemma deltaMixedMoment_le_deltaMoment_mul (n : ℕ) {a : ℕ} (ha : a ≠ 0)
    (b : ℕ) (t : ℝ) :
    deltaMixedMoment n a b t ≤ deltaMoment n a * (hooleyDelta n : ℝ) ^ b := by
  calc
    _ ≤ ∫ u : ℝ, deltaCount n u ^ a * (hooleyDelta n : ℝ) ^ b := by
      apply integral_mono (integrable_deltaCount_mixed n a b t (by omega))
        ((integrable_deltaCount_pow ha).mul_const _)
      intro u
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (deltaCount_nonneg n (u - t))
          (deltaCount_le_hooleyDelta n (u - t)) b)
        (pow_nonneg (deltaCount_nonneg n u) a)
    _ = _ := integral_mul_const _ _

lemma deltaMixedMoment_at_one_le {a : ℕ} (ha : a ≠ 0) (b : ℕ) (t : ℝ) :
    deltaMixedMoment 1 a b t ≤ 1 := by
  simpa [deltaMoment_at_one ha] using deltaMixedMoment_le_deltaMoment_mul 1 ha b t

@[simp] lemma deltaMixedMoment_zero_right (n a : ℕ) (t : ℝ) :
    deltaMixedMoment n a 0 t = deltaMoment n a := by
  simp only [deltaMixedMoment, deltaMoment, pow_zero, mul_one]

@[simp] lemma deltaMixedMoment_zero_left (n b : ℕ) (t : ℝ) :
    deltaMixedMoment n 0 b t = deltaMoment n b := by
  simp only [deltaMixedMoment, pow_zero, one_mul, deltaMoment]
  exact integral_sub_right_eq_self (fun u : ℝ => deltaCount n u ^ b) t

end Erdos587
