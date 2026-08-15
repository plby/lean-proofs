/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos285.PrimePowers
import ErdosProblems.Erdos285.LinearPadding
import PrimeNumberTheoremAnd.Consequences
import Mathlib.NumberTheory.AbelSummation

/-!
# A positive-density prime-power-smooth reservoir for Erdős 285

This file gives an elementary replacement for the smooth-number density input
used in Martin's proof.  The proof deletes, from a fixed interval, every
multiple of an exact prime power larger than `x ^ (2/5)`.  Abel summation and
the prime number theorem show that the prime contribution to the union bound
tends to `log (5/2) < 1`; higher prime powers and the endpoint errors are
sublinear.
-/

open Filter Finset Real Asymptotics MeasureTheory
open scoped BigOperators Topology

namespace Erdos285.PositiveReservoir

noncomputable section

attribute [local instance] Classical.propDecidable

/-- The indicator sequence of the primes, as a real-valued sequence. -/
private def primeIndicator (n : ℕ) : ℝ := if n.Prime then 1 else 0

/-- Sum of reciprocals of primes in `(a,b]`. -/
def primeReciprocalInterval (a b : ℕ) : ℝ :=
  ∑ p ∈ Ioc a b with p.Prime, (p : ℝ)⁻¹

private lemma sum_primeIndicator_Icc (n : ℕ) :
    ∑ k ∈ Icc 0 n, primeIndicator k = (Nat.primeCounting n : ℝ) := by
  rw [Nat.primeCounting, Nat.primeCounting', Nat.count_eq_card_filter_range]
  rw [Nat.range_succ_eq_Icc_zero]
  push_cast
  calc
    ∑ k ∈ Icc 0 n, primeIndicator k =
        ∑ k ∈ Icc 0 n, if k.Prime then (1 : ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro k hk
      simp [primeIndicator]
    _ = ∑ k ∈ (Icc 0 n).filter Nat.Prime, (1 : ℝ) := by
      rw [Finset.sum_filter]
    _ = ((Icc 0 n).filter Nat.Prime).card := by
      simp only [sum_const, nsmul_eq_mul, mul_one]

/-- Abel summation for the reciprocal-prime sum. -/
lemma primeReciprocalInterval_eq (a b : ℕ) (ha : 2 ≤ a) (hab : a ≤ b) :
    primeReciprocalInterval a b =
      (Nat.primeCounting b : ℝ) / b - (Nat.primeCounting a : ℝ) / a +
        ∫ t in Set.Ioc (a : ℝ) b, (Nat.primeCounting ⌊t⌋₊ : ℝ) / t ^ 2 := by
  have hAbel := sum_mul_eq_sub_sub_integral_mul'
    (c := primeIndicator) (f := fun t : ℝ ↦ t⁻¹) hab
    (fun t ht ↦ differentiableAt_inv (by
      exact ne_of_gt (lt_of_lt_of_le (by positivity) ht.1)))
    (by
      rw [deriv_inv']
      refine ContinuousOn.integrableOn_Icc fun t ht ↦ ContinuousAt.continuousWithinAt ?_
      have ht0 : t ≠ 0 := by exact ne_of_gt (lt_of_lt_of_le (by positivity) ht.1)
      exact ((continuousAt_id.pow 2).inv₀ (pow_ne_zero 2 ht0)).neg)
  rw [primeReciprocalInterval]
  calc
    ∑ p ∈ Ioc a b with p.Prime, (p : ℝ)⁻¹ =
        ∑ p ∈ Ioc a b, (p : ℝ)⁻¹ * primeIndicator p := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro p hp
      by_cases hprime : p.Prime <;> simp [primeIndicator, hprime]
    ∑ p ∈ Ioc a b, (p : ℝ)⁻¹ * primeIndicator p =
        (b : ℝ)⁻¹ * (Nat.primeCounting b : ℝ) -
          (a : ℝ)⁻¹ * (Nat.primeCounting a : ℝ) -
          ∫ t in Set.Ioc (a : ℝ) b,
            deriv (fun t : ℝ ↦ t⁻¹) t * (Nat.primeCounting ⌊t⌋₊ : ℝ) := by
      simpa only [sum_primeIndicator_Icc] using hAbel
    _ = _ := by
      rw [sub_eq_add_neg]
      congr 1
      · ring
      · rw [← MeasureTheory.integral_neg]
        apply MeasureTheory.integral_congr_ae
        filter_upwards with t
        rw [deriv_inv]
        ring

/-- A convenient uniform upper form of the prime number theorem. -/
theorem eventually_primeCounting_upper :
    ∀ᶠ t : ℝ in atTop,
      (Nat.primeCounting ⌊t⌋₊ : ℝ) ≤ (101 / 100 : ℝ) * t / Real.log t := by
  obtain ⟨e, he, hpi⟩ := pi_alt
  have he' := he.bound (show (0 : ℝ) < 1 / 100 by norm_num)
  filter_upwards [he', eventually_gt_atTop 2] with t het ht
  have hlog : 0 < Real.log t := Real.log_pos (by linarith)
  have heUpper : 1 + e t ≤ (101 / 100 : ℝ) := by
    have habs : |e t| ≤ (1 / 100 : ℝ) := by simpa using het
    linarith [le_abs_self (e t)]
  rw [hpi]
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right heUpper (by linarith)) hlog.le

lemma log_five_halves_lt_one : Real.log (5 / 2 : ℝ) < 1 := by
  rw [Real.log_lt_iff_lt_exp (by norm_num)]
  exact lt_trans (by norm_num : (5 / 2 : ℝ) < 2.7182818283) Real.exp_one_gt_d9

/-- Number of proper (exponent at least two) prime powers up to `n`. -/
def properPrimePowerCount (n : ℕ) : ℕ :=
  ((Icc 2 n).filter fun q ↦ IsPrimePow q ∧ ¬ q.Prime).card

private def properPrimePowerIndicator (n : ℕ) : ℝ :=
  if IsPrimePow n ∧ ¬ n.Prime then 1 else 0

def properPrimePowerReciprocalInterval (a b : ℕ) : ℝ :=
  ∑ q ∈ Ioc a b with IsPrimePow q ∧ ¬ q.Prime, (q : ℝ)⁻¹

private lemma sum_properPrimePowerIndicator_Icc (n : ℕ) :
    ∑ q ∈ Icc 0 n, properPrimePowerIndicator q = (properPrimePowerCount n : ℝ) := by
  rw [properPrimePowerCount]
  have hfilter : ((Icc 0 n).filter fun q ↦ IsPrimePow q ∧ ¬ q.Prime) =
      (Icc 2 n).filter fun q ↦ IsPrimePow q ∧ ¬ q.Prime := by
    ext q
    simp only [Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨-, hqn⟩, hqpp, hqnprime⟩
      exact ⟨⟨hqpp.one_lt, hqn⟩, hqpp, hqnprime⟩
    · rintro ⟨⟨hq2, hqn⟩, hqpp, hqnprime⟩
      exact ⟨⟨by omega, hqn⟩, hqpp, hqnprime⟩
  calc
    ∑ q ∈ Icc 0 n, properPrimePowerIndicator q =
        ∑ q ∈ Icc 0 n, if IsPrimePow q ∧ ¬ q.Prime then (1 : ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro q hq
      simp [properPrimePowerIndicator]
    _ = ∑ q ∈ (Icc 0 n).filter (fun q ↦ IsPrimePow q ∧ ¬ q.Prime), (1 : ℝ) := by
      rw [Finset.sum_filter]
    _ = ∑ q ∈ (Icc 2 n).filter (fun q ↦ IsPrimePow q ∧ ¬ q.Prime), (1 : ℝ) := by
      rw [hfilter]
    _ = ((Icc 2 n).filter (fun q ↦ IsPrimePow q ∧ ¬ q.Prime)).card := by
      simp only [sum_const, nsmul_eq_mul, mul_one]

lemma properPrimePowerCount_le (n : ℕ) :
    properPrimePowerCount n ≤ n.sqrt * Nat.log 2 n := by
  have hsubset : (Icc 2 n).filter (fun q ↦ IsPrimePow q ∧ ¬ q.Prime) ⊆
      LinearPadding.properPowerValues n := by
    intro q hq
    rw [Finset.mem_filter, Finset.mem_Icc] at hq
    exact LinearPadding.mem_properPowerValues_of_isPrimePow_not_prime
      hq.2.1 hq.2.2 hq.1.2
  exact (Finset.card_le_card hsubset).trans
    (LinearPadding.card_properPowerValues_le n)

lemma properPrimePowerReciprocalInterval_eq (a b : ℕ) (ha : 2 ≤ a) (hab : a ≤ b) :
    properPrimePowerReciprocalInterval a b =
      (properPrimePowerCount b : ℝ) / b - (properPrimePowerCount a : ℝ) / a +
        ∫ t in Set.Ioc (a : ℝ) b, (properPrimePowerCount ⌊t⌋₊ : ℝ) / t ^ 2 := by
  have hAbel := sum_mul_eq_sub_sub_integral_mul'
    (c := properPrimePowerIndicator) (f := fun t : ℝ ↦ t⁻¹) hab
    (fun t ht ↦ differentiableAt_inv (by
      exact ne_of_gt (lt_of_lt_of_le (by positivity) ht.1)))
    (by
      rw [deriv_inv']
      refine ContinuousOn.integrableOn_Icc fun t ht ↦ ContinuousAt.continuousWithinAt ?_
      have ht0 : t ≠ 0 := by exact ne_of_gt (lt_of_lt_of_le (by positivity) ht.1)
      exact ((continuousAt_id.pow 2).inv₀ (pow_ne_zero 2 ht0)).neg)
  rw [properPrimePowerReciprocalInterval]
  calc
    ∑ q ∈ Ioc a b with IsPrimePow q ∧ ¬q.Prime, (q : ℝ)⁻¹ =
        ∑ q ∈ Ioc a b, (q : ℝ)⁻¹ * properPrimePowerIndicator q := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro q hq
      by_cases hproper : IsPrimePow q ∧ ¬ q.Prime <;>
        simp [properPrimePowerIndicator, hproper]
    _ = (b : ℝ)⁻¹ * (properPrimePowerCount b : ℝ) -
          (a : ℝ)⁻¹ * (properPrimePowerCount a : ℝ) -
          ∫ t in Set.Ioc (a : ℝ) b,
            deriv (fun t : ℝ ↦ t⁻¹) t * (properPrimePowerCount ⌊t⌋₊ : ℝ) := by
      simpa only [sum_properPrimePowerIndicator_Icc] using hAbel
    _ = _ := by
      rw [sub_eq_add_neg]
      congr 1
      · ring
      · rw [← MeasureTheory.integral_neg]
        apply MeasureTheory.integral_congr_ae
        filter_upwards with t
        rw [deriv_inv]
        ring

private lemma primeIntegral_intervalIntegrable (a b : ℕ) (ha : 2 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable
      (fun t : ℝ ↦ (Nat.primeCounting ⌊t⌋₊ : ℝ) / t ^ 2)
      MeasureTheory.volume a b := by
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le (by exact_mod_cast hab)]
  have hcont : ContinuousOn (fun t : ℝ ↦ (t ^ 2)⁻¹) (Set.Icc (a : ℝ) b) := by
    intro t ht
    exact ContinuousAt.continuousWithinAt <|
      (continuousAt_id.pow 2).inv₀ (pow_ne_zero 2 (ne_of_gt <| by
        exact lt_of_lt_of_le (by positivity) ht.1))
  have hbase : IntegrableOn (fun t : ℝ ↦ (t ^ 2)⁻¹) (Set.Icc (a : ℝ) b) :=
    hcont.integrableOn_Icc
  have hmul := integrableOn_mul_sum_Icc (m := 0) primeIndicator
    (show (0 : ℝ) ≤ a by positivity) hbase
  have heq : (fun t : ℝ ↦ (t ^ 2)⁻¹ * ∑ k ∈ Icc 0 ⌊t⌋₊, primeIndicator k) =
      fun t : ℝ ↦ (Nat.primeCounting ⌊t⌋₊ : ℝ) / t ^ 2 := by
    funext t
    rw [sum_primeIndicator_Icc]
    ring
  rw [heq] at hmul
  exact hmul

/-- A sharp union-bound estimate for primes on a finite interval.  The PNT
hypothesis is deliberately stated uniformly, so this lemma is also useful
without filters. -/
lemma primeReciprocalInterval_le (a b : ℕ) (ha : 2 ≤ a) (hab : a ≤ b)
    (hpi : ∀ t ∈ Set.Icc (a : ℝ) b,
      (Nat.primeCounting ⌊t⌋₊ : ℝ) ≤ (101 / 100 : ℝ) * t / Real.log t) :
    primeReciprocalInterval a b ≤
      (101 / 100 : ℝ) / Real.log b +
        (101 / 100 : ℝ) *
          (Real.log (Real.log b) - Real.log (Real.log a)) := by
  have haR : (1 : ℝ) < a := by exact_mod_cast (show 1 < a by omega)
  have hbR : (1 : ℝ) < b := lt_of_lt_of_le haR (by exact_mod_cast hab)
  have hb0 : (0 : ℝ) < b := by positivity
  have hlogb : 0 < Real.log (b : ℝ) := Real.log_pos hbR
  have hpiB := hpi b (by exact ⟨by exact_mod_cast hab, le_rfl⟩)
  simp only [Nat.floor_natCast] at hpiB
  have hend : (Nat.primeCounting b : ℝ) / b ≤
      (101 / 100 : ℝ) / Real.log b := by
    calc
      (Nat.primeCounting b : ℝ) / b ≤
          ((101 / 100 : ℝ) * b / Real.log b) / b :=
        div_le_div_of_nonneg_right hpiB hb0.le
      _ = _ := by field_simp
  have hIntLeft := primeIntegral_intervalIntegrable a b ha hab
  have hIntRight : IntervalIntegrable
      (fun t : ℝ ↦ (101 / 100 : ℝ) * (t⁻¹ / Real.log t))
      MeasureTheory.volume a b := by
    refine ContinuousOn.intervalIntegrable fun t ht ↦ ?_
    have ht' : t ∈ Set.Icc (a : ℝ) b := by
      rwa [Set.uIcc_of_le (by exact_mod_cast hab)] at ht
    have ht1 : 1 < t := lt_of_lt_of_le haR ht'.1
    have ht0 : t ≠ 0 := ne_of_gt (lt_trans (by norm_num) ht1)
    have hlog0 : Real.log t ≠ 0 := ne_of_gt (Real.log_pos ht1)
    fun_prop
  have hIntegral :
      (∫ t in (a : ℝ)..b, (Nat.primeCounting ⌊t⌋₊ : ℝ) / t ^ 2) ≤
        ∫ t in (a : ℝ)..b, (101 / 100 : ℝ) * (t⁻¹ / Real.log t) := by
    exact intervalIntegral.integral_mono_on (by exact_mod_cast hab) hIntLeft hIntRight
      (fun t ht ↦ by
        have ht0 : 0 < t := lt_of_lt_of_le (by positivity) ht.1
        have hlogt : 0 < Real.log t := Real.log_pos
          (lt_of_lt_of_le haR ht.1)
        calc
          (Nat.primeCounting ⌊t⌋₊ : ℝ) / t ^ 2 ≤
              ((101 / 100 : ℝ) * t / Real.log t) / t ^ 2 :=
            div_le_div_of_nonneg_right (hpi t ht) (sq_nonneg t)
          _ = (101 / 100 : ℝ) * (t⁻¹ / Real.log t) := by field_simp)
  rw [primeReciprocalInterval_eq a b ha hab]
  rw [← intervalIntegral.integral_of_le (by exact_mod_cast hab)]
  calc
    (Nat.primeCounting b : ℝ) / b - (Nat.primeCounting a : ℝ) / a +
          ∫ t in (a : ℝ)..b, (Nat.primeCounting ⌊t⌋₊ : ℝ) / t ^ 2
        ≤ (Nat.primeCounting b : ℝ) / b +
          ∫ t in (a : ℝ)..b, (Nat.primeCounting ⌊t⌋₊ : ℝ) / t ^ 2 := by
      have : 0 ≤ (Nat.primeCounting a : ℝ) / a := by positivity
      linarith
    _ ≤ (101 / 100 : ℝ) / Real.log b +
          ∫ t in (a : ℝ)..b, (101 / 100 : ℝ) * (t⁻¹ / Real.log t) :=
      add_le_add hend hIntegral
    _ = _ := by
      rw [intervalIntegral.integral_const_mul,
        integral_inv_div_log haR hbR]

/-! ## The finite reservoir -/

/-- The cutoff `⌊x^(2/5)⌋`. -/
def smoothCutoff (x : ℕ) : ℕ := ⌊(x : ℝ) ^ (2 / 5 : ℝ)⌋₊

/-- The integer interval `[⌈αx/2⌉,⌊αx⌋]`. -/
def reservoirInterval (α : ℝ) (x : ℕ) : Finset ℕ :=
  Icc ⌈α * x / 2⌉₊ ⌊α * x⌋₊

/-- Prime powers above the smoothness cutoff which can occur in the interval. -/
def obstructingPrimePowers (α : ℝ) (x : ℕ) : Finset ℕ :=
  (Ioc (smoothCutoff x) ⌊α * x⌋₊).filter IsPrimePow

lemma obstructingPrimePowers_subset_upTo (α : ℝ) (x : ℕ) :
    obstructingPrimePowers α x ⊆
      PrimePowers.primePowersUpTo ⌊α * x⌋₊ := by
  intro q hq
  rw [obstructingPrimePowers, Finset.mem_filter, Finset.mem_Ioc] at hq
  exact PrimePowers.mem_primePowersUpTo.mpr ⟨hq.2, hq.1.2⟩

lemma obstructingPrimePowers_card_le_piStar (α : ℝ) (x : ℕ) :
    (obstructingPrimePowers α x).card ≤ PrimePowers.piStar ⌊α * x⌋₊ :=
  Finset.card_le_card (obstructingPrimePowers_subset_upTo α x)

theorem obstructingPrimePowers_card_isLittleO (α : ℝ) (hα : 0 < α) :
    (fun x : ℕ ↦ ((obstructingPrimePowers α x).card : ℝ)) =o[atTop]
      (fun x : ℕ ↦ (x : ℝ)) := by
  have hscaleReal : Tendsto (fun x : ℕ ↦ α * (x : ℝ)) atTop atTop :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop hα
  have hscale : Tendsto (fun x : ℕ ↦ ⌊α * (x : ℝ)⌋₊) atTop atTop :=
    tendsto_nat_floor_atTop.comp hscaleReal
  have hpp := LinearPadding.piStar_isLittleO.comp_tendsto hscale
  have hfloorBigO : (fun x : ℕ ↦ (⌊α * (x : ℝ)⌋₊ : ℝ)) =O[atTop]
      (fun x : ℕ ↦ (x : ℝ)) := by
    apply Asymptotics.IsBigO.of_bound (|α| + 1)
    filter_upwards with x
    rw [Real.norm_natCast, Real.norm_natCast]
    have hfloor : (⌊α * (x : ℝ)⌋₊ : ℝ) ≤ α * x := by
      exact Nat.floor_le (mul_nonneg hα.le (by positivity))
    have hx : 0 ≤ (x : ℝ) := by positivity
    calc
      (⌊α * (x : ℝ)⌋₊ : ℝ) ≤ α * x := hfloor
      _ ≤ (|α| + 1) * x := by
        gcongr
        linarith [le_abs_self α]
  have hpiStar : (fun x : ℕ ↦ (PrimePowers.piStar ⌊α * (x : ℝ)⌋₊ : ℝ)) =o[atTop]
      (fun x : ℕ ↦ (x : ℝ)) := hpp.trans_isBigO hfloorBigO
  have hdom : (fun x : ℕ ↦ ((obstructingPrimePowers α x).card : ℝ)) =O[atTop]
      (fun x : ℕ ↦ (PrimePowers.piStar ⌊α * (x : ℝ)⌋₊ : ℝ)) := by
    apply Filter.Eventually.isBigO
    filter_upwards with x
    exact_mod_cast obstructingPrimePowers_card_le_piStar α x
  exact hdom.trans_isLittleO hpiStar

lemma obstructingPrimePower_reciprocal_sum_eq (α : ℝ) (x : ℕ) :
    (∑ q ∈ obstructingPrimePowers α x, (q : ℝ)⁻¹) =
      primeReciprocalInterval (smoothCutoff x) ⌊α * x⌋₊ +
        properPrimePowerReciprocalInterval (smoothCutoff x) ⌊α * x⌋₊ := by
  rw [obstructingPrimePowers, primeReciprocalInterval,
    properPrimePowerReciprocalInterval]
  calc
    ∑ q ∈ (Ioc (smoothCutoff x) ⌊α * x⌋₊).filter IsPrimePow, (q : ℝ)⁻¹ =
        ∑ q ∈ Ioc (smoothCutoff x) ⌊α * x⌋₊,
          ((if q.Prime then (q : ℝ)⁻¹ else 0) +
            (if IsPrimePow q ∧ ¬ q.Prime then (q : ℝ)⁻¹ else 0)) := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro q hq
      by_cases hqpp : IsPrimePow q
      · by_cases hqp : q.Prime <;> simp [hqpp, hqp]
      · have hnprime : ¬ q.Prime := fun hp ↦ hqpp hp.isPrimePow
        simp [hqpp, hnprime]
    _ = _ := by
      rw [Finset.sum_add_distrib, Finset.sum_filter, Finset.sum_filter]

theorem eventually_smoothCutoff_two_le :
    ∀ᶠ x : ℕ in atTop, 2 ≤ smoothCutoff x := by
  have hgrowth : Tendsto (fun x : ℕ ↦ (x : ℝ) ^ (2 / 5 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
  have hfloor := tendsto_nat_floor_atTop.comp hgrowth
  exact hfloor.eventually_ge_atTop 2

/-- Multiples of `q` lying in the reservoir interval. -/
def multiplesInReservoir (α : ℝ) (x q : ℕ) : Finset ℕ :=
  (reservoirInterval α x).filter (q ∣ ·)

/-- The positive-density reservoir: all denominators in the fixed interval
whose prime-power divisors are at most `smoothCutoff x`. -/
def positiveReservoir (α : ℝ) (x : ℕ) : Finset ℕ :=
  (reservoirInterval α x).filter
    (UnitFractions.is_smooth (smoothCutoff x : ℝ))

@[simp] lemma mem_reservoirInterval {α : ℝ} {x n : ℕ} :
    n ∈ reservoirInterval α x ↔
      ⌈α * x / 2⌉₊ ≤ n ∧ n ≤ ⌊α * x⌋₊ := by
  simp [reservoirInterval]

lemma mem_reservoirInterval_real {α : ℝ} {x n : ℕ} (hα : 0 ≤ α)
    (hn : n ∈ reservoirInterval α x) :
    α * x / 2 ≤ n ∧ (n : ℝ) ≤ α * x := by
  rw [mem_reservoirInterval] at hn
  exact ⟨(Nat.ceil_le.mp hn.1), (Nat.cast_le.mpr hn.2).trans
    (Nat.floor_le (mul_nonneg hα (by positivity)))⟩

theorem eventually_reservoirInterval_card_lower (α : ℝ) (hα : 0 < α) :
    ∀ᶠ x : ℕ in atTop,
      α / 3 * x ≤ ((reservoirInterval α x).card : ℝ) := by
  have hscale : Tendsto (fun x : ℕ ↦ α * (x : ℝ)) atTop atTop :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop hα
  filter_upwards [hscale.eventually_ge_atTop 12] with x hx
  let lo := ⌈α * (x : ℝ) / 2⌉₊
  let hi := ⌊α * (x : ℝ)⌋₊
  have hnonneg : 0 ≤ α * (x : ℝ) := mul_nonneg hα.le (by positivity)
  have hlo_lt : (lo : ℝ) < α * x / 2 + 1 := by
    exact Nat.ceil_lt_add_one (div_nonneg hnonneg (by norm_num))
  have hhi_lower : α * x < (hi : ℝ) + 1 := by
    exact Nat.lt_floor_add_one _
  have hlohi : lo ≤ hi := by
    exact_mod_cast (show (lo : ℝ) ≤ hi by nlinarith)
  have hcard : (reservoirInterval α x).card = hi + 1 - lo := by
    simp [reservoirInterval, lo, hi]
  rw [hcard, Nat.cast_sub (by omega)]
  push_cast
  nlinarith

@[simp] lemma mem_positiveReservoir {α : ℝ} {x n : ℕ} :
    n ∈ positiveReservoir α x ↔
      n ∈ reservoirInterval α x ∧
        UnitFractions.is_smooth (smoothCutoff x : ℝ) n := by
  simp [positiveReservoir]

lemma positiveReservoir_subset_interval (α : ℝ) (x : ℕ) :
    positiveReservoir α x ⊆ reservoirInterval α x :=
  Finset.filter_subset _ _

lemma positiveReservoir_smooth {α : ℝ} {x n : ℕ}
    (hn : n ∈ positiveReservoir α x) :
    UnitFractions.is_smooth (smoothCutoff x : ℝ) n :=
  (mem_positiveReservoir.mp hn).2

lemma positiveReservoir_primePowerSmooth {α : ℝ} {x n : ℕ}
    (hn0 : n ≠ 0) (hn : n ∈ positiveReservoir α x) :
    PrimePowers.PrimePowerSmooth (smoothCutoff x) n := by
  intro q hq
  have hqspec := (PrimePowers.mem_primePowerParts hn0).mp hq
  exact_mod_cast positiveReservoir_smooth hn q hqspec.1 hqspec.2.1

/-- Select any prescribed number of distinct unused denominators from the
positive reservoir. -/
lemma exists_positiveReservoir_subset_card_eq {α : ℝ} {x m : ℕ}
    (hm : m ≤ (positiveReservoir α x).card) :
    ∃ T ⊆ positiveReservoir α x, T.card = m :=
  Finset.exists_subset_card_eq hm

/-- Select a prescribed number of reservoir elements while avoiding an
arbitrary finite set of denominators already used by the construction. -/
lemma exists_positiveReservoir_subset_disjoint_card_eq
    {α : ℝ} {x m : ℕ} (used : Finset ℕ)
    (hm : m ≤ (positiveReservoir α x \ used).card) :
    ∃ T ⊆ positiveReservoir α x, Disjoint T used ∧ T.card = m := by
  obtain ⟨T, hTsub, hTcard⟩ :=
    Finset.exists_subset_card_eq (s := positiveReservoir α x \ used) hm
  refine ⟨T, hTsub.trans (Finset.sdiff_subset), ?_, hTcard⟩
  rw [Finset.disjoint_left]
  intro n hnT hnused
  exact (Finset.mem_sdiff.mp (hTsub hnT)).2 hnused

lemma nonsmooth_mem_multiples_biUnion {α : ℝ} {x n : ℕ}
    (hn0 : n ≠ 0) (hn : n ∈ reservoirInterval α x)
    (hns : ¬ UnitFractions.is_smooth (smoothCutoff x : ℝ) n) :
    n ∈ (obstructingPrimePowers α x).biUnion (multiplesInReservoir α x) := by
  rw [UnitFractions.is_smooth] at hns
  push_neg at hns
  obtain ⟨q, hq⟩ := hns
  have hqle : q ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hq.2.1
  have hnupper : n ≤ ⌊α * x⌋₊ := (mem_reservoirInterval.mp hn).2
  have hqcut : smoothCutoff x < q := by exact_mod_cast hq.2.2
  rw [Finset.mem_biUnion]
  refine ⟨q, ?_, ?_⟩
  · exact Finset.mem_filter.mpr
      ⟨Finset.mem_Ioc.mpr ⟨hqcut, hqle.trans hnupper⟩, hq.1⟩
  · exact Finset.mem_filter.mpr ⟨hn, hq.2.1⟩

private lemma Ico_filter_dvd_card_real_le (a b q : ℕ) (hq : 0 < q) (hab : a ≤ b) :
    (((Ico a b).filter (q ∣ ·)).card : ℝ) ≤ ((b - a : ℕ) : ℝ) / q + 1 := by
  have heq := Nat.Ico_filter_modEq_card a b hq 0
  simp only [Nat.modEq_zero_iff_dvd, Nat.cast_zero, sub_zero] at heq
  have hmono : ⌈(a : ℚ) / q⌉ ≤ ⌈(b : ℚ) / q⌉ := by
    exact Int.ceil_mono (div_le_div_of_nonneg_right (by exact_mod_cast hab) (by positivity))
  rw [max_eq_left (sub_nonneg.mpr hmono)] at heq
  have heqQ : ((((Ico a b).filter (q ∣ ·)).card : ℕ) : ℚ) =
      (⌈(b : ℚ) / q⌉ : ℤ) - ⌈(a : ℚ) / q⌉ := by
    exact_mod_cast heq
  have hQ : ((((Ico a b).filter (q ∣ ·)).card : ℕ) : ℚ) ≤
      ((b - a : ℕ) : ℚ) / q + 1 := by
    rw [heqQ]
    have hbceil := Int.ceil_lt_add_one ((b : ℚ) / q)
    have haceil := Int.le_ceil ((a : ℚ) / q)
    push_cast at hbceil haceil ⊢
    have hdiv : ((b - a : ℕ) : ℚ) / q = (b : ℚ) / q - (a : ℚ) / q := by
      rw [Nat.cast_sub hab]
      ring
    rw [hdiv]
    nlinarith
  have hQ' : ((((Ico a b).filter (q ∣ ·)).card : ℕ) : ℚ) * q ≤
      ((b - a : ℕ) : ℚ) + q := by
    calc
      _ ≤ (((b - a : ℕ) : ℚ) / q + 1) * q :=
        mul_le_mul_of_nonneg_right hQ (by positivity)
      _ = _ := by field_simp
  rw [show ((b - a : ℕ) : ℝ) / q + 1 =
    (((b - a : ℕ) : ℝ) + q) / q by field_simp]
  apply (le_div_iff₀ (show (0 : ℝ) < q by positivity)).2
  exact_mod_cast hQ'

/-- The sharp elementary count `length/q + 1` for multiples in an interval. -/
lemma multiplesInReservoir_card_le (α : ℝ) (x q : ℕ) (hq : q ≠ 0) :
    ((multiplesInReservoir α x q).card : ℝ) ≤
      ((reservoirInterval α x).card : ℝ) / q + 1 := by
  let lo := ⌈α * x / 2⌉₊
  let hi := ⌊α * x⌋₊
  by_cases hlohi : lo ≤ hi
  · have hcard : (reservoirInterval α x).card = hi + 1 - lo := by
      simp [reservoirInterval, lo, hi, hlohi]
    have heq : multiplesInReservoir α x q = (Ico lo (hi + 1)).filter (q ∣ ·) := by
      ext n
      simp [multiplesInReservoir, reservoirInterval, lo, hi, hlohi]
    rw [heq, hcard]
    exact Ico_filter_dvd_card_real_le lo (hi + 1) q (Nat.pos_of_ne_zero hq) (by omega)
  · have hempty : reservoirInterval α x = ∅ := by
      simp [reservoirInterval, lo, hi, Nat.not_le.mp hlohi]
    simp [multiplesInReservoir, hempty]

lemma reservoir_complement_card_le_union (α : ℝ) (x : ℕ)
    (hlo : 1 ≤ ⌈α * x / 2⌉₊) :
    (reservoirInterval α x).card - (positiveReservoir α x).card ≤
      ((obstructingPrimePowers α x).biUnion
        (multiplesInReservoir α x)).card := by
  rw [← Finset.card_sdiff_of_subset (positiveReservoir_subset_interval α x)]
  apply Finset.card_le_card
  intro n hn
  rw [Finset.mem_sdiff] at hn
  have hn0 : n ≠ 0 := by
    have := (mem_reservoirInterval.mp hn.1).1
    omega
  exact nonsmooth_mem_multiples_biUnion hn0 hn.1
    (fun hs ↦ hn.2 (mem_positiveReservoir.mpr ⟨hn.1, hs⟩))

/-- Union bound in the exact form used for density: interval length times the
reciprocal prime-power tail, plus one endpoint error for every prime power. -/
lemma obstructing_union_card_le (α : ℝ) (x : ℕ) :
    (((obstructingPrimePowers α x).biUnion
        (multiplesInReservoir α x)).card : ℝ) ≤
      ((reservoirInterval α x).card : ℝ) *
          (∑ q ∈ obstructingPrimePowers α x, (q : ℝ)⁻¹) +
        (obstructingPrimePowers α x).card := by
  calc
    (((obstructingPrimePowers α x).biUnion
          (multiplesInReservoir α x)).card : ℝ) ≤
        ∑ q ∈ obstructingPrimePowers α x,
          ((multiplesInReservoir α x q).card : ℝ) := by
      exact_mod_cast Finset.card_biUnion_le
    _ ≤ ∑ q ∈ obstructingPrimePowers α x,
          (((reservoirInterval α x).card : ℝ) / q + 1) := by
      apply Finset.sum_le_sum
      intro q hq
      have hqpp : IsPrimePow q := (Finset.mem_filter.mp hq).2
      exact multiplesInReservoir_card_le α x q hqpp.ne_zero
    _ = _ := by
      rw [Finset.sum_add_distrib]
      simp only [div_eq_mul_inv, Finset.mul_sum, Finset.sum_const, nsmul_eq_mul,
        mul_one, Nat.cast_id]

end

end Erdos285.PositiveReservoir
