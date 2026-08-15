import Mathlib.NumberTheory.EulerProduct.Basic
import ErdosProblems.Erdos697.Erdos697PrimeHarmonic

/-!
# Smooth reciprocal sums for Erdős 697

The small part of an eligible divisor is supported on primes at most the
lower endpoint.  Its reciprocal sum is dominated by the finite Euler
product, and that product is bounded by the exponential of twice the
reciprocal-prime sum.
-/

open scoped BigOperators

namespace Erdos697.Smooth

noncomputable section

/-- Positive `L`-smooth integers in `[1,X]`. -/
def parts (L X : ℕ) : Finset ℕ :=
  (Finset.Icc 1 X).filter fun a => a ∈ (L + 1).smoothNumbers

@[simp] theorem mem_parts {L X a : ℕ} :
    a ∈ parts L X ↔ 1 ≤ a ∧ a ≤ X ∧ a ∈ (L + 1).smoothNumbers := by
  simp [parts, and_assoc]

/-- The reciprocal map, regarded as a completely multiplicative real-valued
function. -/
def reciprocalHom : ℕ →* ℝ where
  toFun n := (n : ℝ)⁻¹
  map_one' := by norm_num
  map_mul' a b := by
    change (((a * b : ℕ) : ℝ))⁻¹ = (a : ℝ)⁻¹ * (b : ℝ)⁻¹
    rw [Nat.cast_mul, mul_inv]

/-- The completely multiplicative weight `n ↦ 1 / √n`. -/
def sqrtReciprocalHom : ℕ →* ℝ where
  toFun n := (Real.sqrt (n : ℝ))⁻¹
  map_one' := by norm_num
  map_mul' a b := by
    rw [Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg a), mul_inv]

/-- A finite smooth reciprocal sum is bounded by its Euler product. -/
theorem sum_parts_reciprocal_le_euler (L X : ℕ) :
    (∑ a ∈ parts L X, (1 : ℝ) / a) ≤
      ∏ p ∈ (L + 1).primesBelow, (1 - (1 : ℝ) / p)⁻¹ := by
  classical
  let s := parts L X
  let e : {a // a ∈ s} ↪ (L + 1).smoothNumbers :=
    ⟨fun a => ⟨a.1, (mem_parts.mp a.2).2.2⟩, by
      intro a b h
      apply Subtype.ext
      exact congrArg (fun z : (L + 1).smoothNumbers => z.1) h⟩
  let A : Finset ((L + 1).smoothNumbers) := s.attach.map e
  have hprime {p : ℕ} (hp : p.Prime) :
      ‖reciprocalHom p‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg
      (inv_nonneg.mpr (by exact_mod_cast hp.pos.le))]
    change (p : ℝ)⁻¹ < 1
    rw [inv_lt_one₀ (by exact_mod_cast hp.pos)]
    exact_mod_cast hp.one_lt
  have heuler :=
    EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_geometric
      (f := reciprocalHom) hprime (L + 1)
  have hfinite :
      (∑ a ∈ A, reciprocalHom a.1) ≤
        ∑' a : (L + 1).smoothNumbers, reciprocalHom a.1 :=
    (Summable.of_norm heuler.1).sum_le_tsum A (fun a _ => by
      change 0 ≤ (a.1 : ℝ)⁻¹
      positivity)
  have hsumA :
      (∑ a ∈ parts L X, (1 : ℝ) / a) =
        ∑ a ∈ A, reciprocalHom a.1 := by
    change (∑ a ∈ s, (1 : ℝ) / a) = _
    rw [← Finset.sum_attach, Finset.sum_map]
    apply Finset.sum_congr rfl
    intro a ha
    simp [reciprocalHom, one_div, e]
    rfl
  rw [hsumA]
  exact hfinite.trans_eq (by simpa [reciprocalHom, one_div] using heuler.2.tsum_eq)

/-- Each Euler factor is bounded by `exp (2/p)`. -/
theorem eulerFactor_le_exp {p : ℕ} (hp : p.Prime) :
    (1 - (1 : ℝ) / p)⁻¹ ≤ Real.exp (2 / (p : ℝ)) := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  let x : ℝ := 1 / p
  have hx0 : 0 ≤ x := by dsimp [x]; positivity
  have hxhalf : x ≤ 1 / 2 := by
    dsimp [x]
    exact one_div_le_one_div_of_le (by norm_num) hp2
  have hden : 0 < 1 - x := by linarith
  have hrat : (1 - x)⁻¹ ≤ 1 + 2 * x := by
    rw [inv_le_iff_one_le_mul₀ hden]
    nlinarith
  calc
    (1 - (1 : ℝ) / p)⁻¹ = (1 - x)⁻¹ := by rfl
    _ ≤ 1 + 2 * x := hrat
    _ ≤ Real.exp (2 * x) := by
      simpa [add_comm] using Real.add_one_le_exp (2 * x)
    _ = Real.exp (2 / (p : ℝ)) := by congr 1; dsimp [x]; ring

/-- The finite Euler product over primes at most `L` is at most
`exp (2 * ∑_{p≤L} 1/p)`. -/
theorem euler_le_exp_primeHarmonic (L : ℕ) :
    (∏ p ∈ (L + 1).primesBelow, (1 - (1 : ℝ) / p)⁻¹) ≤
      Real.exp (2 * PrimeHarmonic.sum L) := by
  calc
    (∏ p ∈ (L + 1).primesBelow, (1 - (1 : ℝ) / p)⁻¹) ≤
        ∏ p ∈ (L + 1).primesBelow, Real.exp (2 / (p : ℝ)) := by
      apply Finset.prod_le_prod
      · intro p hp
        have hprime := Nat.prime_of_mem_primesBelow hp
        have : (0 : ℝ) < 1 - 1 / (p : ℝ) := by
          have hpgt : (1 : ℝ) < p := by exact_mod_cast hprime.one_lt
          have hpR : (0 : ℝ) < p := by positivity
          rw [sub_pos]
          exact (div_lt_one hpR).mpr hpgt
        positivity
      · intro p hp
        exact eulerFactor_le_exp (Nat.prime_of_mem_primesBelow hp)
    _ = Real.exp (2 * PrimeHarmonic.sum L) := by
      rw [← Real.exp_sum]
      unfold PrimeHarmonic.sum Nat.primesLE
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _
      ring

/-- Convenient combined form used by the density estimate. -/
theorem sum_parts_reciprocal_le_exp (L X : ℕ) :
    (∑ a ∈ parts L X, (1 : ℝ) / a) ≤
      Real.exp (2 * PrimeHarmonic.sum L) :=
  (sum_parts_reciprocal_le_euler L X).trans
    (euler_le_exp_primeHarmonic L)

/-- A finite smooth `1 / √n` sum is bounded by its Euler product. -/
theorem sum_parts_sqrtReciprocal_le_euler (L X : ℕ) :
    (∑ a ∈ parts L X, (Real.sqrt (a : ℝ))⁻¹) ≤
      ∏ p ∈ (L + 1).primesBelow,
        (1 - (Real.sqrt (p : ℝ))⁻¹)⁻¹ := by
  classical
  let s := parts L X
  let e : {a // a ∈ s} ↪ (L + 1).smoothNumbers :=
    ⟨fun a => ⟨a.1, (mem_parts.mp a.2).2.2⟩, by
      intro a b h
      apply Subtype.ext
      exact congrArg (fun z : (L + 1).smoothNumbers => z.1) h⟩
  let A : Finset ((L + 1).smoothNumbers) := s.attach.map e
  have hprime {p : ℕ} (hp : p.Prime) :
      ‖sqrtReciprocalHom p‖ < 1 := by
    change ‖(Real.sqrt (p : ℝ))⁻¹‖ < 1
    rw [Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))]
    rw [inv_lt_one₀ (Real.sqrt_pos.2 (by exact_mod_cast hp.pos))]
    rw [Real.lt_sqrt (by norm_num)]
    exact_mod_cast hp.one_lt
  have heuler :=
    EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_geometric
      (f := sqrtReciprocalHom) hprime (L + 1)
  have hfinite :
      (∑ a ∈ A, sqrtReciprocalHom a.1) ≤
        ∑' a : (L + 1).smoothNumbers, sqrtReciprocalHom a.1 :=
    (Summable.of_norm heuler.1).sum_le_tsum A (fun a _ => by
      change 0 ≤ (Real.sqrt (a.1 : ℝ))⁻¹
      positivity)
  have hsumA :
      (∑ a ∈ parts L X, (Real.sqrt (a : ℝ))⁻¹) =
        ∑ a ∈ A, sqrtReciprocalHom a.1 := by
    change (∑ a ∈ s, (Real.sqrt (a : ℝ))⁻¹) = _
    rw [← Finset.sum_attach, Finset.sum_map]
    rfl
  rw [hsumA]
  exact hfinite.trans_eq (by simpa [sqrtReciprocalHom] using heuler.2.tsum_eq)

private theorem sqrtEulerFactor_le_exp_five {p : ℕ} (hp : p.Prime) :
    (1 - (Real.sqrt (p : ℝ))⁻¹)⁻¹ ≤ Real.exp 5 := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hspos : 0 < Real.sqrt (p : ℝ) := Real.sqrt_pos.2 hpR
  have hsone : 1 < Real.sqrt (p : ℝ) := by
    rw [Real.lt_sqrt (by norm_num)]
    exact_mod_cast hp.one_lt
  let x : ℝ := (Real.sqrt (p : ℝ))⁻¹
  have hx0 : 0 ≤ x := by dsimp [x]; positivity
  have hxlt : x < 1 := (inv_lt_one₀ hspos).2 hsone
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hs54 : (5 / 4 : ℝ) ≤ Real.sqrt (p : ℝ) := by
    exact (Real.le_sqrt (by norm_num) hpR.le).2 (by nlinarith)
  have hx45 : x ≤ 4 / 5 := by
    dsimp [x]
    rw [inv_le_iff_one_le_mul₀ hspos]
    nlinarith
  have hden : 0 < 1 - x := sub_pos.mpr hxlt
  have hinv : (1 - x)⁻¹ ≤ 1 + 5 * x := by
    rw [inv_le_iff_one_le_mul₀ hden]
    nlinarith
  calc
    (1 - (Real.sqrt (p : ℝ))⁻¹)⁻¹ = (1 - x)⁻¹ := by rfl
    _ ≤ 1 + 5 * x := hinv
    _ ≤ Real.exp (5 * x) := by
      simpa [add_comm] using Real.add_one_le_exp (5 * x)
    _ ≤ Real.exp 5 := Real.exp_monotone (by nlinarith)

/-- A deliberately coarse Euler-product estimate.  Its exponent is linear
in the smoothness cutoff; this is enough when `L = (log m)^ρ`, `ρ < 1`. -/
theorem sqrtEuler_le_exp_five_mul (L : ℕ) :
    (∏ p ∈ (L + 1).primesBelow,
        (1 - (Real.sqrt (p : ℝ))⁻¹)⁻¹) ≤
      Real.exp (5 * (L + 1 : ℕ)) := by
  calc
    (∏ p ∈ (L + 1).primesBelow,
        (1 - (Real.sqrt (p : ℝ))⁻¹)⁻¹) ≤
        ∏ _p ∈ (L + 1).primesBelow, Real.exp 5 := by
      apply Finset.prod_le_prod
      · intro p hp
        have hprime := Nat.prime_of_mem_primesBelow hp
        have hs : 1 < Real.sqrt (p : ℝ) := by
          rw [Real.lt_sqrt (by norm_num)]
          exact_mod_cast hprime.one_lt
        have : 0 < 1 - (Real.sqrt (p : ℝ))⁻¹ := by
          rw [sub_pos]
          exact (inv_lt_one₀ (by positivity)).2 hs
        positivity
      · intro p hp
        exact sqrtEulerFactor_le_exp_five (Nat.prime_of_mem_primesBelow hp)
    _ = Real.exp (5 * ((L + 1).primesBelow.card : ℕ)) := by
      rw [Finset.prod_const, ← Real.exp_nat_mul]
      congr 1
      push_cast
      ring
    _ ≤ Real.exp (5 * (L + 1 : ℕ)) := by
      apply Real.exp_monotone
      norm_cast
      gcongr
      have hsub : (L + 1).primesBelow ⊆ Finset.range (L + 1) := by
        intro p hp
        exact Finset.mem_range.mpr (Nat.lt_of_mem_primesBelow hp)
      simpa using Finset.card_le_card hsub

/-- Rankin's trick for the reciprocal mass of `L`-smooth integers at
least `m`. -/
theorem sum_parts_reciprocal_ge_le
    (L X m : ℕ) (hm : 0 < m) :
    (∑ a ∈ (parts L X).filter (fun a ↦ m ≤ a), (1 : ℝ) / a) ≤
      (Real.sqrt (m : ℝ))⁻¹ * Real.exp (5 * (L + 1 : ℕ)) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hterm {a : ℕ} (ha : a ∈ (parts L X).filter (fun a ↦ m ≤ a)) :
      (1 : ℝ) / a ≤
        (Real.sqrt (m : ℝ))⁻¹ * (Real.sqrt (a : ℝ))⁻¹ := by
    have hma : m ≤ a := (Finset.mem_filter.mp ha).2
    have haR : (0 : ℝ) < a := by
      exact_mod_cast lt_of_lt_of_le hm hma
    have hsma : Real.sqrt (m : ℝ) ≤ Real.sqrt (a : ℝ) :=
      Real.sqrt_le_sqrt (by exact_mod_cast hma)
    have hprod : Real.sqrt (m : ℝ) * Real.sqrt (a : ℝ) ≤ (a : ℝ) := by
      calc
        Real.sqrt (m : ℝ) * Real.sqrt (a : ℝ) ≤
            Real.sqrt (a : ℝ) * Real.sqrt (a : ℝ) := by gcongr
        _ = (a : ℝ) := Real.mul_self_sqrt haR.le
    rw [one_div, ← mul_inv]
    exact inv_anti₀ (mul_pos (Real.sqrt_pos.2 hmR) (Real.sqrt_pos.2 haR)) hprod
  calc
    (∑ a ∈ (parts L X).filter (fun a ↦ m ≤ a), (1 : ℝ) / a) ≤
        ∑ a ∈ (parts L X).filter (fun a ↦ m ≤ a),
          (Real.sqrt (m : ℝ))⁻¹ * (Real.sqrt (a : ℝ))⁻¹ :=
      Finset.sum_le_sum fun a ha ↦ hterm ha
    _ = (Real.sqrt (m : ℝ))⁻¹ *
        ∑ a ∈ (parts L X).filter (fun a ↦ m ≤ a),
          (Real.sqrt (a : ℝ))⁻¹ := by rw [Finset.mul_sum]
    _ ≤ (Real.sqrt (m : ℝ))⁻¹ *
        ∑ a ∈ parts L X, (Real.sqrt (a : ℝ))⁻¹ := by
      have hsum :
          (∑ a ∈ (parts L X).filter (fun a ↦ m ≤ a),
              (Real.sqrt (a : ℝ))⁻¹) ≤
            ∑ a ∈ parts L X, (Real.sqrt (a : ℝ))⁻¹ :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (by
            intro a ha hnot
            exact inv_nonneg.mpr (Real.sqrt_nonneg (a : ℝ)))
      exact mul_le_mul_of_nonneg_left hsum
        (inv_nonneg.mpr (Real.sqrt_nonneg (m : ℝ)))
    _ ≤ (Real.sqrt (m : ℝ))⁻¹ *
        ∏ p ∈ (L + 1).primesBelow,
          (1 - (Real.sqrt (p : ℝ))⁻¹)⁻¹ := by
      gcongr
      exact sum_parts_sqrtReciprocal_le_euler L X
    _ ≤ _ := by
      gcongr
      exact sqrtEuler_le_exp_five_mul L

end

end Erdos697.Smooth
