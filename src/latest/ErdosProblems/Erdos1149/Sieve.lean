/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import Mathlib
import ErdosProblems.Erdos1149.Mobius

/-!
# Abstract density assembly for Erdős Problem 1149

This file contains only the limit-theoretic sieve assembly.  Its hypotheses
are the finite-prime approximations and their uniformly negligible excess.
-/

namespace Erdos1149

open Filter
open scoped BigOperators

/-- Number of indices in the zero-based prefix `[0,N)` satisfying `P`. -/
noncomputable def prefixCount (P : ℕ → Prop) (N : ℕ) : ℕ := by
  classical
  exact ((Finset.range N).filter P).card

/-- Normalized zero-based prefix count. -/
noncomputable def prefixRatio (P : ℕ → Prop) (N : ℕ) : ℝ :=
  (prefixCount P N : ℝ) / N

/-- Set-cardinality presentation of `prefixCount`. -/
lemma prefixCount_eq_ncard (P : ℕ → Prop) (N : ℕ) :
    prefixCount P N = ({n | P n} ∩ Set.Iio N).ncard := by
  classical
  unfold prefixCount
  rw [← Set.ncard_coe_finset]
  congr 1
  ext n
  simp [and_comm]

/-- The local event that the fixed integer `d` divides the positive value
indexed by `n`. -/
def localDivisorEvent (ξ : ℕ → ℕ) (d n : ℕ) : Prop :=
  0 < n ∧ d ∣ ξ n

/-- The outer approximation in which all prime factors up to `D` are
excluded at once by coprimality with `D!`. -/
def factorialCutoffEvent (ξ : ℕ → ℕ) (D n : ℕ) : Prop :=
  0 < n ∧ (ξ n).Coprime D.factorial

/-- The exact event `ξ n = 1` on positive indices. -/
def exactOneEvent (ξ : ℕ → ℕ) (n : ℕ) : Prop :=
  0 < n ∧ ξ n = 1

/-- The error event left after removing all prime factors at most `D`. -/
def largePrimeEvent (ξ : ℕ → ℕ) (D n : ℕ) : Prop :=
  0 < n ∧ ∃ p : ℕ, p.Prime ∧ D < p ∧ p ∣ ξ n

instance (ξ : ℕ → ℕ) (d n : ℕ) : Decidable (localDivisorEvent ξ d n) := by
  unfold localDivisorEvent
  infer_instance

instance (ξ : ℕ → ℕ) (D n : ℕ) : Decidable (factorialCutoffEvent ξ D n) := by
  unfold factorialCutoffEvent
  infer_instance

instance (ξ : ℕ → ℕ) (n : ℕ) : Decidable (exactOneEvent ξ n) := by
  unfold exactOneEvent
  infer_instance

/-- An exact-one value survives every factorial cutoff. -/
lemma exactOneEvent_subset_factorialCutoffEvent (ξ : ℕ → ℕ) (D : ℕ) :
    {n | exactOneEvent ξ n} ⊆ {n | factorialCutoffEvent ξ D n} := by
  rintro n ⟨hn, hξ⟩
  refine ⟨hn, ?_⟩
  simp [hξ]

/-- A value which survives the cutoff but is not one has a prime factor
strictly larger than the cutoff. -/
lemma factorialCutoffEvent_diff_exactOneEvent_subset_largePrimeEvent
    (ξ : ℕ → ℕ) (D : ℕ) :
    {n | factorialCutoffEvent ξ D n} \ {n | exactOneEvent ξ n} ⊆
      {n | largePrimeEvent ξ D n} := by
  rintro n ⟨⟨hn, hcop⟩, hnot⟩
  have hξne : ξ n ≠ 1 := by
    intro hξ
    exact hnot ⟨hn, hξ⟩
  obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hξne
  refine ⟨hn, p, hp, ?_, hpdvd⟩
  have hpcop : p.Coprime D.factorial := hcop.coprime_dvd_left hpdvd
  have hpnot : ¬p ∣ D.factorial := hp.coprime_iff_not_dvd.mp hpcop
  exact lt_of_not_ge (fun hpD ↦ hpnot (hp.dvd_factorial.mpr hpD))

/-- At every finite prefix, the factorial-cutoff ratio exceeds the exact-one
ratio by at most the large-prime error ratio. -/
theorem factorialCutoff_prefixRatio_sub_exactOne_bounds
    (ξ : ℕ → ℕ) (D N : ℕ) :
    0 ≤ prefixRatio (factorialCutoffEvent ξ D) N -
        prefixRatio (exactOneEvent ξ) N ∧
    prefixRatio (factorialCutoffEvent ξ D) N -
        prefixRatio (exactOneEvent ξ) N ≤
      prefixRatio (largePrimeEvent ξ D) N := by
  let A : Set ℕ := {n | factorialCutoffEvent ξ D n} ∩ Set.Iio N
  let B : Set ℕ := {n | exactOneEvent ξ n} ∩ Set.Iio N
  let T : Set ℕ := {n | largePrimeEvent ξ D n} ∩ Set.Iio N
  have hBA : B ⊆ A := by
    rintro n ⟨hnB, hnN⟩
    exact ⟨exactOneEvent_subset_factorialCutoffEvent ξ D hnB, hnN⟩
  have hdiff : A \ B ⊆ T := by
    rintro n ⟨⟨hnA, hnN⟩, hnB⟩
    refine ⟨factorialCutoffEvent_diff_exactOneEvent_subset_largePrimeEvent
      ξ D ⟨hnA, ?_⟩, hnN⟩
    intro hexact
    exact hnB ⟨hexact, hnN⟩
  have hAfin : A.Finite := (Set.finite_Iio N).subset Set.inter_subset_right
  have hTfin : T.Finite := (Set.finite_Iio N).subset Set.inter_subset_right
  have hdecompNat : (A \ B).ncard + B.ncard = A.ncard :=
    Set.ncard_sdiff_add_ncard_of_subset hBA hAfin
  have hdiffNat : (A \ B).ncard ≤ T.ncard :=
    Set.ncard_le_ncard hdiff hTfin
  have hdecompReal : ((A \ B).ncard : ℝ) + B.ncard = A.ncard := by
    exact_mod_cast hdecompNat
  have hdiffReal : ((A \ B).ncard : ℝ) ≤ T.ncard := by
    exact_mod_cast hdiffNat
  rw [prefixRatio, prefixRatio, prefixRatio,
    prefixCount_eq_ncard, prefixCount_eq_ncard, prefixCount_eq_ncard]
  change 0 ≤ (A.ncard : ℝ) / N - (B.ncard : ℝ) / N ∧
    (A.ncard : ℝ) / N - (B.ncard : ℝ) / N ≤ (T.ncard : ℝ) / N
  constructor
  · apply sub_nonneg.mpr
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg N)
    linarith
  · calc
      (A.ncard : ℝ) / N - (B.ncard : ℝ) / N =
          ((A \ B).ncard : ℝ) / N := by rw [← hdecompReal]; ring
      _ ≤ (T.ncard : ℝ) / N :=
        div_le_div_of_nonneg_right hdiffReal (Nat.cast_nonneg N)

/-- Pointwise finite Möbius expansion of a factorial cutoff. -/
lemma factorialCutoff_indicator_eq_mobius_sum (ξ : ℕ → ℕ)
    (D n : ℕ) :
    (if factorialCutoffEvent ξ D n then 1 else 0 : ℝ) =
      ∑ d ∈ D.factorial.divisors,
        (ArithmeticFunction.moebius d : ℝ) *
          (if localDivisorEvent ξ d n then 1 else 0) := by
  classical
  by_cases hn : 0 < n
  · simp only [factorialCutoffEvent, localDivisorEvent, hn, true_and]
    rw [finite_sieve_indicator_mobius (Nat.factorial_ne_zero D)]
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro d hd
    by_cases hdiv : d ∣ ξ n <;> simp [hdiv]
  · simp [factorialCutoffEvent, localDivisorEvent, hn]

/-- The exact finite-count identity obtained by summing the pointwise
factorial-cutoff expansion and interchanging two finite sums. -/
lemma factorialCutoff_prefixCount_eq_mobius_sum (ξ : ℕ → ℕ)
    (D N : ℕ) :
    (prefixCount (factorialCutoffEvent ξ D) N : ℝ) =
      ∑ d ∈ D.factorial.divisors,
        (ArithmeticFunction.moebius d : ℝ) *
          (prefixCount (localDivisorEvent ξ d) N : ℝ) := by
  classical
  calc
    (prefixCount (factorialCutoffEvent ξ D) N : ℝ) =
        ∑ n ∈ Finset.range N,
          (if factorialCutoffEvent ξ D n then 1 else 0 : ℝ) := by
      rw [Finset.sum_boole]
      norm_cast
      apply congrArg Finset.card
      apply Finset.ext
      intro n
      simp
    _ = ∑ n ∈ Finset.range N, ∑ d ∈ D.factorial.divisors,
          (ArithmeticFunction.moebius d : ℝ) *
            (if localDivisorEvent ξ d n then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro n hn
      exact factorialCutoff_indicator_eq_mobius_sum ξ D n
    _ = ∑ d ∈ D.factorial.divisors, ∑ n ∈ Finset.range N,
          (ArithmeticFunction.moebius d : ℝ) *
            (if localDivisorEvent ξ d n then 1 else 0) := by
      rw [Finset.sum_comm]
    _ = ∑ d ∈ D.factorial.divisors,
          (ArithmeticFunction.moebius d : ℝ) *
            (prefixCount (localDivisorEvent ξ d) N : ℝ) := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [← Finset.mul_sum]
      congr 1
      rw [Finset.sum_boole]
      norm_cast
      apply congrArg Finset.card
      apply Finset.ext
      intro n
      simp

/-- Normalized form of `factorialCutoff_prefixCount_eq_mobius_sum`. -/
lemma factorialCutoff_prefixRatio_eq_mobius_sum (ξ : ℕ → ℕ)
    (D N : ℕ) :
    prefixRatio (factorialCutoffEvent ξ D) N =
      ∑ d ∈ D.factorial.divisors,
        (ArithmeticFunction.moebius d : ℝ) *
          prefixRatio (localDivisorEvent ξ d) N := by
  rw [prefixRatio, factorialCutoff_prefixCount_eq_mobius_sum]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro d hd
  simp only [prefixRatio]
  ring

/-- Fixed local divisor densities give the density of every fixed factorial
prime cutoff by finite Möbius inversion. -/
theorem factorialCutoff_tendsto_of_localDivisor_tendsto (ξ : ℕ → ℕ)
    (hlocal : ∀ d, 0 < d →
      Tendsto (prefixRatio (localDivisorEvent ξ d)) atTop
        (nhds ((d : ℝ)⁻¹ ^ 2))) (D : ℕ) :
    Tendsto (prefixRatio (factorialCutoffEvent ξ D)) atTop
      (nhds (∑ d ∈ D.factorial.divisors,
        (ArithmeticFunction.moebius d : ℝ) / (d : ℝ) ^ 2)) := by
  have hsum : Tendsto
      (fun N ↦ ∑ d ∈ D.factorial.divisors,
        (ArithmeticFunction.moebius d : ℝ) *
          prefixRatio (localDivisorEvent ξ d) N)
      atTop
      (nhds (∑ d ∈ D.factorial.divisors,
        (ArithmeticFunction.moebius d : ℝ) * ((d : ℝ)⁻¹ ^ 2))) := by
    apply tendsto_finsetSum
    intro d hd
    exact tendsto_const_nhds.mul (hlocal d (Nat.pos_of_dvd_of_pos
      (Nat.dvd_of_mem_divisors hd) (Nat.factorial_pos D)))
  convert hsum using 1
  · funext N
    exact factorialCutoff_prefixRatio_eq_mobius_sum ξ D N
  · congr 1
    apply Finset.sum_congr rfl
    intro d hd
    rw [inv_pow]
    ring

/-- If `a D` is an outer approximation to `b`, its limit `c D` tends to `L`,
and the excess `a D - b` is uniformly negligible as `D → ∞`, then `b → L`.

This is the precise two-limit squeeze used to remove the finite prime cutoff.
-/
theorem tendsto_of_outer_approximants
    (a : ℕ → ℕ → ℝ) (b : ℕ → ℝ) (r : ℕ → ℕ → ℝ)
    (c : ℕ → ℝ) (L : ℝ)
    (hc : Tendsto c atTop (nhds L))
    (ha : ∀ D, Tendsto (a D) atTop (nhds (c D)))
    (hbound : ∀ D N, 0 ≤ a D N - b N ∧ a D N - b N ≤ r D N)
    (htail : ∀ ε > 0, ∃ D₀, ∀ D ≥ D₀,
      ∀ᶠ N : ℕ in atTop, r D N < ε) :
    Tendsto b atTop (nhds L) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hthird : 0 < ε / 3 := by positivity
  obtain ⟨Dc, hDc⟩ := Metric.tendsto_atTop.mp hc (ε / 3) hthird
  obtain ⟨Dt, hDt⟩ := htail (ε / 3) hthird
  let D := max Dc Dt
  have hcD : dist (c D) L < ε / 3 := hDc D (le_max_left _ _)
  have haD : ∀ᶠ N : ℕ in atTop, dist (a D N) (c D) < ε / 3 :=
    (ha D).eventually (Metric.ball_mem_nhds _ hthird)
  have htD : ∀ᶠ N : ℕ in atTop, r D N < ε / 3 :=
    hDt D (le_max_right _ _)
  have hall : ∀ᶠ N : ℕ in atTop, dist (b N) L < ε := by
    filter_upwards [haD, htD] with N haN htN
    rw [Real.dist_eq] at haN hcD ⊢
    have habs : |a D N - b N| < ε / 3 := by
      rw [abs_of_nonneg (hbound D N).1]
      exact (hbound D N).2.trans_lt htN
    calc
      |b N - L| =
          |-(a D N - b N) + (a D N - c D) + (c D - L)| := by ring_nf
      _ ≤ |a D N - b N| + |a D N - c D| + |c D - L| := by
        calc
          |-(a D N - b N) + (a D N - c D) + (c D - L)|
              ≤ |-(a D N - b N) + (a D N - c D)| + |c D - L| :=
                abs_add_le _ _
          _ ≤ (|-(a D N - b N)| + |a D N - c D|) + |c D - L| := by
                gcongr
                exact abs_add_le _ _
          _ = |a D N - b N| + |a D N - c D| + |c D - L| := by
                rw [abs_neg]
      _ < ε := by linarith
  exact Filter.eventually_atTop.mp hall

/-- Abstract factorial-cutoff sieve.  Fixed local divisor densities and a
uniformly negligible large-prime event imply density `6 / π²` for the
exact-one event. -/
theorem exactOne_tendsto_of_localDivisor_and_largePrime
    (ξ : ℕ → ℕ)
    (hlocal : ∀ d, 0 < d →
      Tendsto (prefixRatio (localDivisorEvent ξ d)) atTop
        (nhds ((d : ℝ)⁻¹ ^ 2)))
    (htail : ∀ ε > 0, ∃ D₀, ∀ D ≥ D₀,
      ∀ᶠ N : ℕ in atTop, prefixRatio (largePrimeEvent ξ D) N < ε) :
    Tendsto (prefixRatio (exactOneEvent ξ)) atTop
      (nhds (6 / Real.pi ^ 2)) := by
  apply tendsto_of_outer_approximants
    (a := fun D ↦ prefixRatio (factorialCutoffEvent ξ D))
    (b := prefixRatio (exactOneEvent ξ))
    (r := fun D ↦ prefixRatio (largePrimeEvent ξ D))
    (c := fun D ↦ ∑ d ∈ D.factorial.divisors,
      (ArithmeticFunction.moebius d : ℝ) / (d : ℝ) ^ 2)
    (L := 6 / Real.pi ^ 2)
  · exact mobius_div_sq_factorial_divisor_sums_tendsto
  · exact factorialCutoff_tendsto_of_localDivisor_tendsto ξ hlocal
  · exact factorialCutoff_prefixRatio_sub_exactOne_bounds ξ
  · exact htail

end Erdos1149
