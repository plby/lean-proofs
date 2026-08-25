import ErdosProblems.Erdos1141.FiniteEulerProduct
import ErdosProblems.Erdos1141.PrimeSetBounds
import Mathlib.Analysis.PSeries

/-!
# Sparse exceptional primes in a quadratic Euler product

Primes with character value `-1` contribute only even powers, giving a
convergent square-power Euler product for every Rankin parameter above
`1/2`.  The remaining primes cost an exponential depending only on their
cardinality.
-/

namespace Pollack17

open scoped BigOperators

noncomputable def eulerLogConstant : ℝ := (1 - (2 : ℝ) ^ (-(1 / 2 : ℝ)))⁻¹

theorem eulerLogConstant_pos : 0 < eulerLogConstant := by
  apply inv_pos.mpr
  exact sub_pos.mpr (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num))

theorem inv_one_sub_le_exp_eulerLogConstant {u : ℝ} (hu0 : 0 ≤ u)
    (hu : u ≤ (2 : ℝ) ^ (-(1 / 2 : ℝ))) :
    (1 - u)⁻¹ ≤ Real.exp (eulerLogConstant * u) := by
  let c : ℝ := (2 : ℝ) ^ (-(1 / 2 : ℝ))
  have hc : c < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
  have hden : 0 < 1 - u := sub_pos.mpr (hu.trans_lt hc)
  have hcden : 0 < 1 - c := sub_pos.mpr hc
  have hlog : -Real.log (1 - u) ≤ (1 - u)⁻¹ - 1 := by
    linarith [Real.one_sub_inv_le_log_of_pos hden]
  have hid : (1 - u)⁻¹ - 1 = u * (1 - u)⁻¹ := by
    field_simp
    ring
  have hinv : (1 - u)⁻¹ ≤ (1 - c)⁻¹ :=
    (inv_le_inv₀ hden hcden).2 (sub_le_sub_left hu 1)
  have hexp : -Real.log (1 - u) ≤ eulerLogConstant * u := by
    calc
      -Real.log (1 - u) ≤ (1 - u)⁻¹ - 1 := hlog
      _ = u * (1 - u)⁻¹ := hid
      _ ≤ u * (1 - c)⁻¹ := mul_le_mul_of_nonneg_left hinv hu0
      _ = eulerLogConstant * u := by simp [eulerLogConstant, c, mul_comm]
  calc
    (1 - u)⁻¹ = Real.exp (-Real.log (1 - u)) := by rw [Real.exp_neg, Real.exp_log hden]
    _ ≤ Real.exp (eulerLogConstant * u) := Real.exp_le_exp.mpr hexp

theorem prime_neg_rpow_le_half_reference {p : ℕ} (hp : p.Prime)
    {s : ℝ} (hs : 1 / 2 ≤ s) :
    (p : ℝ) ^ (-s) ≤ (2 : ℝ) ^ (-(1 / 2 : ℝ)) := by
  calc
    (p : ℝ) ^ (-s) ≤ (p : ℝ) ^ (-(1 / 2 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hp.one_le) (neg_le_neg hs)
    _ ≤ (2 : ℝ) ^ (-(1 / 2 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos (by norm_num) (by exact_mod_cast hp.two_le) (by norm_num)

theorem local_divisorCoefficient_sum_le_squareFactor
    {m : ℕ} (χ : DirichletCharacter ℂ m) (hχ : MulChar.IsQuadratic χ)
    {p : ℕ} (hp : p.Prime) {s : ℝ} (hs : 1 / 2 ≤ s) :
    (∑' e : ℕ, divisorCoefficient χ (p ^ e) * ((p : ℝ) ^ (-s)) ^ e) ≤
      (1 - ((p : ℝ) ^ (-s)) ^ 2)⁻¹ *
        Real.exp (if χ (p : ZMod m) ≠ -1 then
          2 * eulerLogConstant * (p : ℝ) ^ (-s) else 0) := by
  let u : ℝ := (p : ℝ) ^ (-s)
  have hu0 : 0 ≤ u := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have huref : u ≤ (2 : ℝ) ^ (-(1 / 2 : ℝ)) := prime_neg_rpow_le_half_reference hp hs
  have hu1 : u < 1 := huref.trans_lt
    (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num))
  have hden : 0 < 1 - u ^ 2 := by nlinarith
  have hbase : 1 ≤ (1 - u ^ 2)⁻¹ := by
    rw [← one_div, le_div_iff₀ hden]
    nlinarith
  by_cases h : χ (p : ZMod m) = -1
  · simpa [h, u] using (hasSum_divisorCoefficient_of_neg_one χ hp h hu0 hu1).tsum_eq.le
  · rw [if_pos h]
    calc
      (∑' e : ℕ, divisorCoefficient χ (p ^ e) * u ^ e) ≤ (1 - u)⁻¹ ^ 2 :=
        local_divisorCoefficient_sum_le χ hχ hp hu0 hu1
      _ ≤ Real.exp (eulerLogConstant * u) ^ 2 :=
        pow_le_pow_left₀ (inv_nonneg.mpr (sub_nonneg.mpr hu1.le))
          (inv_one_sub_le_exp_eulerLogConstant hu0 huref) 2
      _ = Real.exp (2 * eulerLogConstant * u) := by
        rw [pow_two, ← Real.exp_add]
        congr 1
        ring
      _ ≤ (1 - u ^ 2)⁻¹ * Real.exp (2 * eulerLogConstant * u) :=
        le_mul_of_one_le_left (Real.exp_nonneg _) hbase

/-- The primes whose Euler factor is not the square-only factor. -/
noncomputable def exceptionalPrimes {m : ℕ} (χ : DirichletCharacter ℂ m) (X : ℕ) : Finset ℕ :=
  ((X + 1).primesBelow).filter fun p => χ (p : ZMod m) ≠ -1

noncomputable def natPowerHom (s : ℝ) : ℕ →* ℝ where
  toFun n := (n : ℝ) ^ s
  map_one' := by simp
  map_mul' a b := by simp [Real.mul_rpow (Nat.cast_nonneg a) (Nat.cast_nonneg b)]

theorem squareEulerProduct_le_tsum (X : ℕ) {s : ℝ} (hs : 1 / 2 < s) :
    (∏ p ∈ (X + 1).primesBelow, (1 - ((p : ℝ) ^ (-s)) ^ 2)⁻¹) ≤
      ∑' n : ℕ, (n : ℝ) ^ (-(2 * s)) := by
  let f := natPowerHom (-(2 * s))
  have hf : Summable f := Real.summable_nat_rpow.mpr (by linarith)
  have hlocal (p : ℕ) : ((p : ℝ) ^ (-s)) ^ 2 = f p := by
    dsimp [f, natPowerHom]
    rw [← Real.rpow_mul_natCast (Nat.cast_nonneg p)]
    congr 1
    push_cast
    ring
  simp_rw [hlocal]
  rw [EulerProduct.prod_primesBelow_geometric_eq_tsum_smoothNumbers hf]
  exact tsum_comp_le_tsum_of_inj hf (fun n => Real.rpow_nonneg (Nat.cast_nonneg n) _)
    (Subtype.val_injective : Function.Injective (fun n : (X + 1).smoothNumbers => (n : ℕ)))

theorem finiteEulerProduct_le_sparse_bound
    {m : ℕ} (χ : DirichletCharacter ℂ m) (hχ : MulChar.IsQuadratic χ)
    (X : ℕ) {s : ℝ} (hs0 : 1 / 2 < s) (hs1 : s < 1) :
    (∏ p ∈ (X + 1).primesBelow,
      ∑' e : ℕ, divisorCoefficient χ (p ^ e) * ((p : ℝ) ^ (-s)) ^ e) ≤
      (∑' n : ℕ, (n : ℝ) ^ (-(2 * s))) *
        Real.exp (2 * eulerLogConstant *
          (exceptionalPrimes χ X).card ^ (1 - s) *
            (2 + Real.log (exceptionalPrimes χ X).card)) := by
  classical
  let S := (X + 1).primesBelow
  let B : ℕ → ℝ := fun p => (1 - ((p : ℝ) ^ (-s)) ^ 2)⁻¹
  let E : ℕ → ℝ := fun p => if χ (p : ZMod m) ≠ -1 then
    2 * eulerLogConstant * (p : ℝ) ^ (-s) else 0
  have hprod :
      (∏ p ∈ S, ∑' e : ℕ, divisorCoefficient χ (p ^ e) * ((p : ℝ) ^ (-s)) ^ e) ≤
        (∏ p ∈ S, B p) * Real.exp (∑ p ∈ S, E p) := by
    calc
      _ ≤ ∏ p ∈ S, B p * Real.exp (E p) := by
        apply Finset.prod_le_prod
        · intro p hp
          exact tsum_nonneg fun e =>
            mul_nonneg (divisorCoefficient_nonneg χ hχ _)
              (pow_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) _)
        · intro p hp
          exact local_divisorCoefficient_sum_le_squareFactor χ hχ
            (Nat.prime_of_mem_primesBelow hp) hs0.le
      _ = _ := by rw [Finset.prod_mul_distrib, Real.exp_sum]
  have hsum : (∑ p ∈ S, E p) ≤
      2 * eulerLogConstant * (exceptionalPrimes χ X).card ^ (1 - s) *
        (2 + Real.log (exceptionalPrimes χ X).card) := by
    have hmass := sum_rpow_sub_one_le_card (exceptionalPrimes χ X)
      (fun p hp => (Nat.prime_of_mem_primesBelow (Finset.mem_filter.mp hp).1).pos)
      (sub_pos.mpr hs1) (by linarith : 1 - s ≤ 1)
    have hmass' : (∑ p ∈ exceptionalPrimes χ X, (p : ℝ) ^ (-s)) ≤
        (exceptionalPrimes χ X).card ^ (1 - s) *
          (2 + Real.log (exceptionalPrimes χ X).card) := by
      simpa only [sub_sub_cancel_left] using hmass
    calc
      (∑ p ∈ S, E p) =
          2 * eulerLogConstant * ∑ p ∈ exceptionalPrimes χ X, (p : ℝ) ^ (-s) := by
        simp only [exceptionalPrimes, Finset.sum_filter, E, S, Finset.mul_sum,
          mul_ite, mul_zero]
      _ ≤ _ := by
        simpa only [mul_assoc] using
          mul_le_mul_of_nonneg_left hmass'
            (mul_nonneg (by norm_num) eulerLogConstant_pos.le)
  exact hprod.trans (mul_le_mul (squareEulerProduct_le_tsum X hs0)
    (Real.exp_le_exp.mpr hsum) (Real.exp_nonneg _)
    (tsum_nonneg fun n => Real.rpow_nonneg (Nat.cast_nonneg n) _))

theorem sum_divisorCoefficient_le_sparse_bound
    {m : ℕ} (χ : DirichletCharacter ℂ m) (hχ : MulChar.IsQuadratic χ)
    (X : ℕ) {s : ℝ} (hs0 : 1 / 2 < s) (hs1 : s < 1) :
    (∑ n ∈ Finset.Icc 1 X, divisorCoefficient χ n) ≤
      (X : ℝ) ^ s * (∑' n : ℕ, (n : ℝ) ^ (-(2 * s))) *
        Real.exp (2 * eulerLogConstant *
          (exceptionalPrimes χ X).card ^ (1 - s) *
            (2 + Real.log (exceptionalPrimes χ X).card)) := by
  have h := mul_le_mul_of_nonneg_left
    (finiteEulerProduct_le_sparse_bound χ hχ X hs0 hs1)
    (Real.rpow_nonneg (Nat.cast_nonneg X) s)
  exact (sum_divisorCoefficient_le_finiteEulerProduct χ hχ
    (by linarith : 0 < s) X).trans (by simpa only [mul_assoc] using h)

end Pollack17
