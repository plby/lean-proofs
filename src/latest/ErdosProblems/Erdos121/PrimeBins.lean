import ErdosProblems.Erdos888.PrimeEstimates
import ErdosProblems.Erdos285.SmoothReservoir

/-!
# Reciprocal mass in dyadic prime bins

The `K₅` construction for Erdős Problem 121 uses primes in the bin
`(2^b, 2^(b+1)]`, with weight `1/p`.  This file packages the only analytic
estimate needed for those bins: their reciprocal mass is comparable to
`1 / b`, uniformly for all sufficiently large natural `b`.
-/

open Filter
open scoped BigOperators Topology

namespace Erdos121

set_option autoImplicit false

noncomputable section

/-- Reciprocal-prime mass of the dyadic bin `(2^b,2^(b+1)]`. -/
def dyadicPrimeMass (b : ℕ) : ℝ :=
  (Erdos888.dyadicPrimes (2 ^ b)).sum fun p => (p : ℝ)⁻¹

lemma dyadicPrimeMass_nonneg (b : ℕ) : 0 ≤ dyadicPrimeMass b := by
  exact Finset.sum_nonneg fun _ _ => inv_nonneg.mpr (by positivity)

lemma dyadicPrimeMass_upper_of_count {C : ℝ} (hC : 0 ≤ C) (b : ℕ)
    (hcount : ((Erdos888.dyadicPrimes (2 ^ b)).card : ℝ) ≤
      C * (((2 ^ b : ℕ) : ℝ) / Erdos888.lambda ((2 ^ b : ℕ) : ℝ))) :
    dyadicPrimeMass b ≤ C / Erdos888.lambda ((2 ^ b : ℕ) : ℝ) := by
  have hpow : (0 : ℝ) < ((2 ^ b : ℕ) : ℝ) := by positivity
  have hterm : ∀ p ∈ Erdos888.dyadicPrimes (2 ^ b),
      (p : ℝ)⁻¹ ≤ (((2 ^ b : ℕ) : ℝ))⁻¹ := by
    intro p hp
    have hpgt : (2 ^ b : ℕ) < p := (Erdos888.mem_dyadicPrimes.mp hp).2.1
    have hpPos : (0 : ℝ) < p := by
      exact_mod_cast (Erdos888.mem_dyadicPrimes.mp hp).1.pos
    exact (inv_le_inv₀ hpPos hpow).2
      (by exact_mod_cast hpgt.le)
  calc
    dyadicPrimeMass b ≤
        ((Erdos888.dyadicPrimes (2 ^ b)).card : ℝ) *
          (((2 ^ b : ℕ) : ℝ))⁻¹ := by
      rw [dyadicPrimeMass]
      simpa [nsmul_eq_mul] using
        (Finset.sum_le_card_nsmul (Erdos888.dyadicPrimes (2 ^ b))
          (fun p => (p : ℝ)⁻¹) ((((2 ^ b : ℕ) : ℝ))⁻¹) hterm)
    _ ≤ (C * (((2 ^ b : ℕ) : ℝ) /
          Erdos888.lambda ((2 ^ b : ℕ) : ℝ))) *
          (((2 ^ b : ℕ) : ℝ))⁻¹ := by
      gcongr
    _ = C / Erdos888.lambda ((2 ^ b : ℕ) : ℝ) := by
      field_simp

lemma reservoirPrimes_subset_dyadic (b : ℕ) :
    Erdos285.reservoirPrimes (((2 ^ (b + 1) : ℕ) : ℝ)) ⊆
      Erdos888.dyadicPrimes (2 ^ b) := by
  intro p hp
  have hp' := Erdos285.mem_reservoirPrimes hp
  apply Erdos888.mem_dyadicPrimes.mpr
  refine ⟨hp'.1, ?_, ?_⟩
  · have hpow : (0 : ℝ) < ((2 ^ b : ℕ) : ℝ) := by positivity
    have hcast : (((2 ^ (b + 1) : ℕ) : ℝ)) =
        2 * (((2 ^ b : ℕ) : ℝ)) := by
      norm_num [pow_succ, mul_comm]
    rw [hcast] at hp'
    have : (((2 ^ b : ℕ) : ℝ)) < p := by nlinarith
    exact_mod_cast this
  · have hcast : (((2 ^ (b + 1) : ℕ) : ℝ)) =
        ((2 * 2 ^ b : ℕ) : ℝ) := by
      norm_num [pow_succ, mul_comm]
    exact_mod_cast (hp'.2.2.trans_eq hcast)

lemma reservoir_card_div_le_dyadicPrimeMass (b : ℕ) :
    ((Erdos285.reservoirPrimes (((2 ^ (b + 1) : ℕ) : ℝ))).card : ℝ) /
        (((2 ^ (b + 1) : ℕ) : ℝ)) ≤ dyadicPrimeMass b := by
  let R := Erdos285.reservoirPrimes (((2 ^ (b + 1) : ℕ) : ℝ))
  have hsub : R ⊆ Erdos888.dyadicPrimes (2 ^ b) :=
    reservoirPrimes_subset_dyadic b
  calc
    (R.card : ℝ) / (((2 ^ (b + 1) : ℕ) : ℝ)) =
        R.sum (fun _ => ((((2 ^ (b + 1) : ℕ) : ℝ))⁻¹)) := by
      simp [div_eq_mul_inv]
    _ ≤ R.sum (fun p => (p : ℝ)⁻¹) := by
      apply Finset.sum_le_sum
      intro p hp
      have hpUpper := (Erdos285.mem_reservoirPrimes hp).2.2
      have hpPos : (0 : ℝ) < p := by
        exact_mod_cast Erdos285.reservoirPrime_pos hp
      have hyPos : (0 : ℝ) < (((2 ^ (b + 1) : ℕ) : ℝ)) := by positivity
      exact (inv_le_inv₀ hyPos hpPos).2 hpUpper
    _ ≤ (Erdos888.dyadicPrimes (2 ^ b)).sum (fun p => (p : ℝ)⁻¹) := by
      exact Finset.sum_le_sum_of_subset_of_nonneg hsub fun p hp _ =>
        inv_nonneg.mpr (by positivity)
    _ = dyadicPrimeMass b := rfl

/-- Uniform two-sided reciprocal-mass estimate for dyadic prime bins. -/
theorem eventually_dyadicPrimeMass_bounds :
    ∀ᶠ b : ℕ in atTop,
      (1 : ℝ) / (200 * b) ≤ dyadicPrimeMass b ∧
        dyadicPrimeMass b ≤ (4 * Classical.choose
          Erdos888.exists_forall_dyadicPrimeCount_le_scale) / b := by
  let C : ℝ := Classical.choose Erdos888.exists_forall_dyadicPrimeCount_le_scale
  have hCspec := Classical.choose_spec
    Erdos888.exists_forall_dyadicPrimeCount_le_scale
  have hCpos : 0 < C := hCspec.1
  have hcount : ∀ X : ℕ,
      ((Erdos888.dyadicPrimes X).card : ℝ) ≤
        C * ((X : ℝ) / Erdos888.lambda (X : ℝ)) := hCspec.2
  have htendsto : Tendsto (fun b : ℕ => (((2 ^ (b + 1) : ℕ) : ℝ)))
      atTop atTop := by
    have hpowNat : Tendsto (fun b : ℕ => (2 : ℕ) ^ b) atTop atTop :=
      tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
    exact tendsto_natCast_atTop_atTop.comp
      (hpowNat.comp (tendsto_add_atTop_nat 1))
  have hreservoir := htendsto.eventually
    Erdos285.eventually_reservoirPrimes_card_lower
  filter_upwards [hreservoir, eventually_ge_atTop 2] with b hres hb
  have hbR : (0 : ℝ) < b := by positivity
  have hy : (0 : ℝ) < (((2 ^ (b + 1) : ℕ) : ℝ)) := by positivity
  have hlogpow : Real.log (((2 ^ (b + 1) : ℕ) : ℝ)) =
      (b + 1 : ℝ) * Real.log 2 := by
    convert Real.log_pow (2 : ℝ) (b + 1) using 1 <;> norm_num
  have hlogUpper : Real.log (((2 ^ (b + 1) : ℕ) : ℝ)) ≤ 2 * b := by
    rw [hlogpow]
    have hlog2 : Real.log 2 ≤ 1 :=
      Real.log_two_lt_d9.le.trans (by norm_num)
    have hlog2nonneg : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    have hb1 : ((b + 1 : ℕ) : ℝ) ≤ 2 * (b : ℝ) := by
      exact_mod_cast (show b + 1 ≤ 2 * b by omega)
    calc
      ((b : ℝ) + 1) * Real.log 2 ≤ ((b : ℝ) + 1) * 1 := by
        gcongr
      _ ≤ 2 * (b : ℝ) := by norm_num at hb1 ⊢; exact hb1
  have hlogPos : 0 < Real.log (((2 ^ (b + 1) : ℕ) : ℝ)) := by
    apply Real.log_pos
    exact_mod_cast Nat.one_lt_two_pow (by omega : b + 1 ≠ 0)
  have hlowerRaw :
      (1 : ℝ) / (100 * Real.log (((2 ^ (b + 1) : ℕ) : ℝ))) ≤
        ((Erdos285.reservoirPrimes (((2 ^ (b + 1) : ℕ) : ℝ))).card : ℝ) /
          (((2 ^ (b + 1) : ℕ) : ℝ)) := by
    apply (le_div_iff₀ hy).2
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hres
  have hlower : (1 : ℝ) / (200 * b) ≤ dyadicPrimeMass b := by
    calc
      (1 : ℝ) / (200 * b) ≤
          1 / (100 * Real.log (((2 ^ (b + 1) : ℕ) : ℝ))) := by
        apply one_div_le_one_div_of_le (by positivity)
        nlinarith
      _ ≤ ((Erdos285.reservoirPrimes
          (((2 ^ (b + 1) : ℕ) : ℝ))).card : ℝ) /
            (((2 ^ (b + 1) : ℕ) : ℝ)) := hlowerRaw
      _ ≤ dyadicPrimeMass b := reservoir_card_div_le_dyadicPrimeMass b
  have hlambda : (b : ℝ) / 2 ≤
      Erdos888.lambda (((2 ^ b : ℕ) : ℝ)) := by
    rw [Erdos888.lambda_eq_one_add_log (by positivity : (((2 ^ b : ℕ) : ℝ)) ≠ 0)]
    rw [show (((2 ^ b : ℕ) : ℝ)) = (2 : ℝ) ^ b by norm_num, Real.log_pow]
    have hlog2 : (1 / 2 : ℝ) < Real.log 2 := by
      nlinarith [Real.log_two_gt_d9]
    have hbnonneg : (0 : ℝ) ≤ b := by positivity
    nlinarith
  have hupperRaw := dyadicPrimeMass_upper_of_count hCpos.le b (hcount (2 ^ b))
  have hupper : dyadicPrimeMass b ≤ (4 * C) / b := by
    calc
      dyadicPrimeMass b ≤ C / Erdos888.lambda (((2 ^ b : ℕ) : ℝ)) := hupperRaw
      _ ≤ (4 * C) / b := by
        have hpowOne : (1 : ℝ) ≤ (((2 ^ b : ℕ) : ℝ)) := by
          exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by norm_num)))
        rw [div_le_div_iff₀ (Erdos888.lambda_pos hpowOne) hbR]
        nlinarith
  exact ⟨hlower, by simpa [C] using hupper⟩

/-- The dyadic estimates, made uniform for every bin on the scale
`[U/100,U]`.  This is the form used in the finite `K₅` sample space. -/
theorem eventually_dyadicPrimeMass_bounds_on_scale :
    ∀ᶠ U : ℕ in atTop, ∀ b : ℕ, U / 100 ≤ b → b ≤ U →
      (1 : ℝ) / (200 * U) ≤ dyadicPrimeMass b ∧
        dyadicPrimeMass b ≤
          (800 * Classical.choose
            Erdos888.exists_forall_dyadicPrimeCount_le_scale) / U := by
  have hEvent := eventually_dyadicPrimeMass_bounds
  rw [Filter.eventually_atTop] at hEvent ⊢
  obtain ⟨B, hB⟩ := hEvent
  refine ⟨max 100 (100 * B), ?_⟩
  intro U hU b hbLower hbUpper
  have hU100 : 100 ≤ U := (le_max_left _ _).trans hU
  have hUB : 100 * B ≤ U := (le_max_right _ _).trans hU
  have hB' : B ≤ U / 100 := (Nat.le_div_iff_mul_le (by norm_num)).2 (by
    simpa [Nat.mul_comm] using hUB)
  have hbB : B ≤ b := hB'.trans hbLower
  obtain ⟨hlower, hupper⟩ := hB b hbB
  have hUpos : (0 : ℝ) < U := by positivity
  have hbPosNat : 0 < b := by omega
  have hbPos : (0 : ℝ) < b := by exact_mod_cast hbPosNat
  constructor
  · calc
      (1 : ℝ) / (200 * U) ≤ 1 / (200 * b) := by
        apply one_div_le_one_div_of_le (by positivity)
        exact_mod_cast Nat.mul_le_mul_left 200 hbUpper
      _ ≤ dyadicPrimeMass b := hlower
  · calc
      dyadicPrimeMass b ≤
          (4 * Classical.choose
            Erdos888.exists_forall_dyadicPrimeCount_le_scale) / b := hupper
      _ ≤ (800 * Classical.choose
            Erdos888.exists_forall_dyadicPrimeCount_le_scale) / U := by
        have hCpos : 0 < Classical.choose
            Erdos888.exists_forall_dyadicPrimeCount_le_scale :=
          (Classical.choose_spec
            Erdos888.exists_forall_dyadicPrimeCount_le_scale).1
        rw [div_le_div_iff₀ hbPos hUpos]
        have hUb : U ≤ 200 * b := by
          have hdiv : U < 100 * (U / 100 + 1) := by omega
          omega
        have hUbCast : (U : ℝ) ≤ 200 * (b : ℝ) := by exact_mod_cast hUb
        nlinarith

end

end Erdos121
