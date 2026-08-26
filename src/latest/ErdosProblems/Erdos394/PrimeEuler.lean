import ErdosProblems.Erdos394.PrimeReciprocal
import ErdosProblems.Erdos394.SymmetricTail

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Euler-product bounds from reciprocal prime mass
-/

open Nat Finset

namespace Erdos394

/-- Primes in the half-open interval `(a,b]`. -/
def primeInterval (a b : ℕ) : Finset ℕ :=
  b.primesLE \ a.primesLE

/-- The reciprocal sum over `(a,b]` is the difference of the two cumulative
prime-reciprocal sums. -/
theorem sum_primeInterval_one_div {a b : ℕ} (hab : a ≤ b) :
    (∑ p ∈ primeInterval a b, (1 / p : ℝ)) =
      primeReciprocalSum b - primeReciprocalSum a := by
  have hsub : a.primesLE ⊆ b.primesLE := Nat.primesLE_mono hab
  have hs := Finset.sum_sdiff hsub (f := fun p : ℕ ↦ (1 / p : ℝ))
  unfold primeInterval primeReciprocalSum
  linarith

/-- Multiplying the local sieve density by its square-root Euler sum retains
exponential decay in half of the total reciprocal mass. -/
theorem localEulerProduct_mul_halfEuler_le_exp
    (P : Finset α) (x : α → ℝ)
    (hx0 : ∀ i ∈ P, 0 ≤ x i) (hx1 : ∀ i ∈ P, x i ≤ 1) :
    localEulerProduct P x * (∏ i ∈ P, (1 + x i / 2)) ≤
      Real.exp (-(∑ i ∈ P, x i) / 2) := by
  classical
  unfold localEulerProduct
  rw [← Finset.prod_mul_distrib]
  calc
    (∏ i ∈ P, (1 - x i) * (1 + x i / 2)) ≤
        ∏ i ∈ P, Real.exp (-(x i) / 2) := by
      apply Finset.prod_le_prod
      · intro i hi
        exact mul_nonneg (sub_nonneg.mpr (hx1 i hi))
          (by nlinarith [hx0 i hi])
      · intro i hi
        calc
          (1 - x i) * (1 + x i / 2) ≤ 1 - x i / 2 := by
            nlinarith [sq_nonneg (x i)]
          _ ≤ Real.exp (-(x i / 2)) := Real.one_sub_le_exp_neg _
          _ = Real.exp (-(x i) / 2) := by ring_nf
    _ = Real.exp (∑ i ∈ P, (-(x i) / 2)) :=
      (Real.exp_sum P (fun i ↦ (-(x i) / 2))).symm
    _ = Real.exp (-(∑ i ∈ P, x i) / 2) := by
      congr 1
      calc
        (∑ i ∈ P, (-(x i) / 2)) =
            ∑ i ∈ P, ((-1 : ℝ) / 2) * x i := by
              apply Finset.sum_congr rfl
              intro i _
              ring
        _ = ((-1 : ℝ) / 2) * (∑ i ∈ P, x i) := by
              rw [Finset.mul_sum]
        _ = -(∑ i ∈ P, x i) / 2 := by ring

/-- For `0≤x≤1/2`, the local factor `1-x` is bounded below by
`exp(-2x)`. -/
theorem exp_neg_two_mul_le_one_sub {x : ℝ} (hx0 : 0 ≤ x)
    (hxhalf : x ≤ 1 / 2) :
    Real.exp (-2 * x) ≤ 1 - x := by
  rw [show -2 * x = -(2 * x) by ring, Real.exp_neg]
  have hdiv : 1 / Real.exp (2 * x) ≤ 1 - x := by
    apply (div_le_iff₀ (Real.exp_pos (2 * x))).2
    have hexp : 1 + 2 * x ≤ Real.exp (2 * x) := by
      simpa [add_comm] using Real.add_one_le_exp (2 * x)
    calc
      1 ≤ (1 - x) * (1 + 2 * x) := by nlinarith
      _ ≤ (1 - x) * Real.exp (2 * x) :=
        mul_le_mul_of_nonneg_left hexp
          (sub_nonneg.mpr (hxhalf.trans (by norm_num)))
  simpa only [one_div] using hdiv

/-- A finite local Euler product is bounded below exponentially in its total
weight when every weight is at most one half. -/
theorem exp_neg_two_sum_le_localEulerProduct
    (P : Finset α) (x : α → ℝ)
    (hx0 : ∀ i ∈ P, 0 ≤ x i) (hxhalf : ∀ i ∈ P, x i ≤ 1 / 2) :
    Real.exp (-2 * (∑ i ∈ P, x i)) ≤ localEulerProduct P x := by
  classical
  unfold localEulerProduct
  calc
    Real.exp (-2 * (∑ i ∈ P, x i)) =
        Real.exp (∑ i ∈ P, -2 * x i) := by
      congr 1
      rw [Finset.mul_sum]
    _ = ∏ i ∈ P, Real.exp (-2 * x i) := Real.exp_sum P _
    _ ≤ ∏ i ∈ P, (1 - x i) := by
      apply Finset.prod_le_prod
      · intro i _
        exact (Real.exp_pos _).le
      · intro i hi
        exact exp_neg_two_mul_le_one_sub (hx0 i hi) (hxhalf i hi)

/-- Prime specialization of the combined Euler-product bound. -/
theorem primeInterval_combinedEuler_le_exp {a b : ℕ} (hab : a ≤ b) :
    localEulerProduct (primeInterval a b) (fun p ↦ 1 / (p : ℝ)) *
        (∏ p ∈ primeInterval a b, (1 + (1 / (p : ℝ)) / 2)) ≤
      Real.exp (-(primeReciprocalSum b - primeReciprocalSum a) / 2) := by
  have hprime : ∀ p ∈ primeInterval a b, p.Prime := by
    intro p hp
    exact (Nat.mem_primesLE.mp (Finset.mem_sdiff.mp hp).1).2
  have hx0 : ∀ p ∈ primeInterval a b, 0 ≤ (1 / (p : ℝ)) := by
    intro p hp
    positivity
  have hx1 : ∀ p ∈ primeInterval a b, (1 / (p : ℝ)) ≤ 1 := by
    intro p hp
    have hp0 : (0 : ℝ) < p := by exact_mod_cast (hprime p hp).pos
    exact (div_le_one hp0).2 (by exact_mod_cast (hprime p hp).one_le)
  have h := localEulerProduct_mul_halfEuler_le_exp
    (primeInterval a b) (fun p ↦ 1 / (p : ℝ)) hx0 hx1
  rw [sum_primeInterval_one_div hab] at h
  exact h

/-- Prime specialization of the lower Euler-product bound. -/
theorem exp_neg_two_primeReciprocal_sub_le_localEulerProduct
    {a b : ℕ} (hab : a ≤ b) :
    Real.exp (-2 * (primeReciprocalSum b - primeReciprocalSum a)) ≤
      localEulerProduct (primeInterval a b) (fun p ↦ 1 / (p : ℝ)) := by
  have hprime : ∀ p ∈ primeInterval a b, p.Prime := by
    intro p hp
    exact (Nat.mem_primesLE.mp (Finset.mem_sdiff.mp hp).1).2
  have hx0 : ∀ p ∈ primeInterval a b, 0 ≤ (1 / (p : ℝ)) := by
    intro p hp
    positivity
  have hxhalf : ∀ p ∈ primeInterval a b, (1 / (p : ℝ)) ≤ 1 / 2 := by
    intro p hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (hprime p hp).two_le
    exact one_div_le_one_div_of_le (by norm_num) hp2
  have h := exp_neg_two_sum_le_localEulerProduct
    (primeInterval a b) (fun p ↦ 1 / (p : ℝ)) hx0 hxhalf
  rwa [sum_primeInterval_one_div hab] at h

/-- Along geometric endpoints, the combined Euler factor has a fixed positive
power saving in the upper exponent. -/
theorem exists_geometric_combinedEuler_decay :
    ∃ J₀ : ℕ, 0 < J₀ ∧ ∀ J : ℕ, J₀ ≤ J →
      localEulerProduct (primeInterval (16 ^ J₀) (16 ^ J))
          (fun p ↦ 1 / (p : ℝ)) *
          (∏ p ∈ primeInterval (16 ^ J₀) (16 ^ J),
            (1 + (1 / (p : ℝ)) / 2)) ≤
        Real.exp (-((Real.log J - (harmonic (J₀ - 1) : ℝ)) / 128)) := by
  obtain ⟨J₀, hJ₀, hrecip⟩ := exists_geometric_primeReciprocal_log_lower
  refine ⟨J₀, hJ₀, ?_⟩
  intro J hJ
  have hpow : 16 ^ J₀ ≤ 16 ^ J := Nat.pow_le_pow_right (by omega) hJ
  apply (primeInterval_combinedEuler_le_exp hpow).trans
  apply Real.exp_le_exp.mpr
  nlinarith [hrecip J hJ]

/-- Along geometric endpoints the local sieve density is no smaller than a
fixed negative power of the upper exponent. -/
theorem exists_geometric_localEulerProduct_lower :
    ∃ J₀ : ℕ, 0 < J₀ ∧ ∀ J : ℕ, J₀ ≤ J →
      Real.exp (-24 * (1 + Real.log J)) ≤
        localEulerProduct (primeInterval (16 ^ J₀) (16 ^ J))
          (fun p ↦ 1 / (p : ℝ)) := by
  obtain ⟨J₀, hJ₀, hrecip⟩ := exists_geometric_primeReciprocal_log_upper
  refine ⟨J₀, hJ₀, ?_⟩
  intro J hJ
  have hpow : 16 ^ J₀ ≤ 16 ^ J := Nat.pow_le_pow_right (by omega) hJ
  apply (Real.exp_le_exp.mpr ?_).trans
    (exp_neg_two_primeReciprocal_sub_le_localEulerProduct hpow)
  nlinarith [hrecip J hJ]

/-- Uniform combined-decay and sieve-density bounds between any two
sufficiently late powers of `16`. -/
theorem exists_geometric_interval_euler_bounds :
    ∃ Jmin : ℕ, 2 ≤ Jmin ∧ ∀ Jz Jy : ℕ, Jmin ≤ Jz → Jz ≤ Jy →
      localEulerProduct (primeInterval (16 ^ Jz) (16 ^ Jy))
          (fun p ↦ 1 / (p : ℝ)) *
          (∏ p ∈ primeInterval (16 ^ Jz) (16 ^ Jy),
            (1 + (1 / (p : ℝ)) / 2)) ≤
        Real.exp (-((Real.log Jy - (1 + Real.log Jz)) / 128)) ∧
      Real.exp (-24 * (1 + Real.log Jy)) ≤
        localEulerProduct (primeInterval (16 ^ Jz) (16 ^ Jy))
          (fun p ↦ 1 / (p : ℝ)) := by
  obtain ⟨Jmin, hJmin, hrecip⟩ :=
    exists_geometric_interval_primeReciprocal_bounds
  refine ⟨Jmin, hJmin, ?_⟩
  intro Jz Jy hmin hzY
  have hpow : 16 ^ Jz ≤ 16 ^ Jy := Nat.pow_le_pow_right (by omega) hzY
  obtain ⟨hlower, hupper⟩ := hrecip Jz Jy hmin hzY
  constructor
  · apply (primeInterval_combinedEuler_le_exp hpow).trans
    apply Real.exp_le_exp.mpr
    nlinarith
  · apply (Real.exp_le_exp.mpr ?_).trans
      (exp_neg_two_primeReciprocal_sub_le_localEulerProduct hpow)
    nlinarith

end Erdos394
