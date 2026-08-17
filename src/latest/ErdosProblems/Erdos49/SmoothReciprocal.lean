import ErdosProblems.Erdos49.PrimeSums
import Mathlib.NumberTheory.EulerProduct.Basic

/-!
# Reciprocal sums of smooth numbers

The pair-cluster estimate needs the sharp (up to an absolute constant)
bound `∑ 1 / d ≪ (log y)^2` over a finite collection of `y`-smooth
integers.  We prove it directly from the finite Euler product.  The exponent
two is deliberately slightly wasteful, but is small enough for Tao's final
power of `log log`.
-/

open scoped BigOperators Topology

namespace Erdos49

noncomputable section

def reciprocalWeight (n : ℕ) : ℝ :=
  if n = 0 then 0 else (n : ℝ)⁻¹

@[simp] lemma reciprocalWeight_zero : reciprocalWeight 0 = 0 := by
  simp [reciprocalWeight]

@[simp] lemma reciprocalWeight_one : reciprocalWeight 1 = 1 := by
  simp [reciprocalWeight]

lemma reciprocalWeight_nonneg (n : ℕ) : 0 ≤ reciprocalWeight n := by
  unfold reciprocalWeight
  split_ifs
  · rfl
  · positivity

lemma reciprocalWeight_mul {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) :
    reciprocalWeight (m * n) = reciprocalWeight m * reciprocalWeight n := by
  simp only [reciprocalWeight, if_neg hm, if_neg hn,
    if_neg (mul_ne_zero hm hn)]
  push_cast
  rw [mul_inv]

lemma reciprocalWeight_coprime_mul {m n : ℕ} (_hmn : m.Coprime n) :
    reciprocalWeight (m * n) = reciprocalWeight m * reciprocalWeight n := by
  by_cases hm : m = 0
  · subst m
    simp
  by_cases hn : n = 0
  · subst n
    simp
  exact reciprocalWeight_mul hm hn

lemma reciprocalWeight_prime_pow {p j : ℕ} (hp : p.Prime) :
    reciprocalWeight (p ^ j) = ((p : ℝ)⁻¹) ^ j := by
  have hp0 : p ^ j ≠ 0 := pow_ne_zero _ hp.ne_zero
  simp only [reciprocalWeight, if_neg hp0]
  push_cast
  rw [inv_pow]

lemma summable_reciprocalWeight_prime_pow {p : ℕ} (hp : p.Prime) :
    Summable (fun j : ℕ ↦ ‖reciprocalWeight (p ^ j)‖) := by
  have hp0 : 0 ≤ (p : ℝ)⁻¹ := by positivity
  have hp1 : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.one_lt)
  simpa only [reciprocalWeight_prime_pow hp, Real.norm_eq_abs,
    abs_pow, abs_of_nonneg hp0] using
      (summable_geometric_of_norm_lt_one
        (by simpa [Real.norm_eq_abs, abs_of_nonneg hp0] using hp1))

lemma tsum_reciprocalWeight_prime_pow {p : ℕ} (hp : p.Prime) :
    (∑' j : ℕ, reciprocalWeight (p ^ j)) = (1 - (p : ℝ)⁻¹)⁻¹ := by
  rw [show (fun j : ℕ ↦ reciprocalWeight (p ^ j)) =
      fun j : ℕ ↦ ((p : ℝ)⁻¹) ^ j by
    funext j
    exact reciprocalWeight_prime_pow hp]
  exact tsum_geometric_of_lt_one (by positivity)
    (inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.one_lt))

def reciprocalEulerProduct (y : ℕ) : ℝ :=
  ∏ p ∈ Nat.primesLE y, (1 - (p : ℝ)⁻¹)⁻¹

theorem smooth_reciprocal_sum_le_euler {X y : ℕ} :
    (∑ n ∈ smoothUpTo X y, (1 : ℝ) / n) ≤ reciprocalEulerProduct y := by
  let f : ℕ → ℝ := reciprocalWeight
  have hEuler :=
    EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_tsum
      (f := f) reciprocalWeight_one reciprocalWeight_coprime_mul
      (fun hp ↦ summable_reciprocalWeight_prime_pow hp) (y + 1)
  let e : {n // n ∈ smoothUpTo X y} ↪ (y + 1).smoothNumbers :=
    { toFun := fun n ↦ ⟨n, smooth_iff_mem_nat_smoothNumbers.mp
          (mem_smoothUpTo.mp n.property).2⟩
      inj' := fun a b hab ↦ by
        apply Subtype.ext
        exact congrArg (fun z : (y + 1).smoothNumbers ↦ (z : ℕ)) hab }
  let S : Finset ((y + 1).smoothNumbers) := (smoothUpTo X y).attach.map e
  have hsum :
      (∑ n ∈ smoothUpTo X y, (1 : ℝ) / n) = ∑ n ∈ S, f n := by
    calc
      (∑ n ∈ smoothUpTo X y, (1 : ℝ) / n) =
          ∑ n ∈ (smoothUpTo X y).attach, (1 : ℝ) / (n : ℕ) :=
        (Finset.sum_attach _ _).symm
      _ = ∑ n ∈ (smoothUpTo X y).attach, f n := by
        apply Finset.sum_congr rfl
        intro n hn
        simp only [f, reciprocalWeight, if_neg (smooth_ne_zero
          (mem_smoothUpTo.mp n.property).2)]
        rw [one_div]
      _ = ∑ n ∈ S, f n := by
        change (∑ n ∈ (smoothUpTo X y).attach, f n) =
          ∑ n ∈ (smoothUpTo X y).attach.map e, f n
        rw [Finset.sum_map]
        rfl
  rw [hsum]
  calc
    (∑ n ∈ S, f n) ≤ ∑' n : (y + 1).smoothNumbers, f n :=
      hEuler.1.of_norm.sum_le_tsum S (fun n _ ↦ reciprocalWeight_nonneg n)
    _ = ∏ p ∈ (y + 1).primesBelow, ∑' j : ℕ, f (p ^ j) :=
      hEuler.2.tsum_eq
    _ = reciprocalEulerProduct y := by
      unfold reciprocalEulerProduct
      rw [show (y + 1).primesBelow = Nat.primesLE y from rfl]
      apply Finset.prod_congr rfl
      intro p hp
      exact tsum_reciprocalWeight_prime_pow (Nat.prime_of_mem_primesLE hp)

lemma inv_one_sub_le_exp_two {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) :
    (1 - x)⁻¹ ≤ Real.exp (2 * x) := by
  have hsub : 0 < 1 - x := by linarith
  have hinv : 0 < (1 - x)⁻¹ := inv_pos.mpr hsub
  rw [← Real.exp_log hinv]
  apply Real.exp_le_exp.mpr
  calc
    Real.log (1 - x)⁻¹ ≤ (1 - x)⁻¹ - 1 :=
      Real.log_le_sub_one_of_pos hinv
    _ = x / (1 - x) := by field_simp; ring
    _ ≤ 2 * x := by
      rw [div_le_iff₀ hsub]
      nlinarith

lemma reciprocalEulerProduct_le_exp_primeSum (y : ℕ) :
    reciprocalEulerProduct y ≤
      Real.exp (2 * ∑ p ∈ Nat.primesLE y, (1 : ℝ) / p) := by
  unfold reciprocalEulerProduct
  calc
    ∏ p ∈ Nat.primesLE y, (1 - (p : ℝ)⁻¹)⁻¹ ≤
        ∏ p ∈ Nat.primesLE y, Real.exp (2 * ((p : ℝ)⁻¹)) := by
      apply Finset.prod_le_prod
      · intro p hp
        apply inv_nonneg.mpr
        have hp2 := (Nat.prime_of_mem_primesLE hp).two_le
        have hp2r : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp2
        have : (p : ℝ)⁻¹ ≤ 1 / 2 := by
          simpa only [one_div] using
            (one_div_le_one_div_of_le (a := (2 : ℝ)) (b := (p : ℝ))
              (by norm_num) hp2r)
        linarith
      · intro p hp
        apply inv_one_sub_le_exp_two (by positivity)
        have hp2r : (2 : ℝ) ≤ (p : ℝ) := by
          exact_mod_cast (Nat.prime_of_mem_primesLE hp).two_le
        simpa only [one_div] using
          (one_div_le_one_div_of_le (a := (2 : ℝ)) (b := (p : ℝ))
            (by norm_num) hp2r)
    _ = Real.exp (∑ p ∈ Nat.primesLE y, 2 * ((p : ℝ)⁻¹)) := by
      rw [Real.exp_sum]
    _ = Real.exp (2 * ∑ p ∈ Nat.primesLE y, (1 : ℝ) / p) := by
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      ring

theorem exists_smooth_reciprocal_log_sq_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X y : ℕ, Real.exp 1 < y →
      (∑ n ∈ smoothUpTo X y, (1 : ℝ) / n) ≤
        C * Real.log (y : ℝ) ^ 2 := by
  obtain ⟨C, hC⟩ := Mertens.sum_prime_div_eq_log_log
  refine ⟨Real.exp (2 * C), (Real.exp_pos _).le, ?_⟩
  intro X y hy
  have hy2 : (2 : ℝ) ≤ y := by
    exact (Real.exp_one_gt_two.trans hy).le
  have hsum := hC (y : ℝ) hy2
  have hsumId :
      (∑ p ∈ Finset.Ioc 0 ⌊(y : ℝ)⌋₊ with p.Prime, (1 : ℝ) / p) =
        ∑ p ∈ Nat.primesLE y, (1 : ℝ) / p := by
    apply Finset.sum_congr
    · ext p
      simp only [Finset.mem_filter, Finset.mem_Ioc, Nat.floor_natCast,
        Nat.mem_primesLE]
      constructor
      · rintro ⟨⟨_hp0, hpy⟩, hp⟩
        exact ⟨hpy, hp⟩
      · rintro ⟨hpy, hp⟩
        exact ⟨⟨hp.pos, hpy⟩, hp⟩
    · intro p hp
      rfl
  rw [hsumId] at hsum
  have hsumUpper :
      (∑ p ∈ Nat.primesLE y, (1 : ℝ) / p) ≤
        Real.log (Real.log (y : ℝ)) + C := by
    linarith [le_abs_self
      ((∑ p ∈ Nat.primesLE y, (1 : ℝ) / p) -
        Real.log (Real.log (y : ℝ)))]
  apply smooth_reciprocal_sum_le_euler.trans
  apply (reciprocalEulerProduct_le_exp_primeSum y).trans
  calc
    Real.exp (2 * ∑ p ∈ Nat.primesLE y, (1 : ℝ) / p) ≤
        Real.exp (2 * (Real.log (Real.log (y : ℝ)) + C)) := by
      exact Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_left hsumUpper (by norm_num))
    _ = Real.exp (2 * C) * Real.log (y : ℝ) ^ 2 := by
      have hlog : 0 < Real.log (y : ℝ) := by
        have hy0 : 0 < (y : ℝ) := (Real.exp_pos 1).trans hy
        have : 1 < Real.log (y : ℝ) := by
          rw [Real.lt_log_iff_exp_lt hy0]
          exact hy
        linarith
      rw [show 2 * (Real.log (Real.log (y : ℝ)) + C) =
          2 * C + Real.log (Real.log (y : ℝ)) * 2 by ring,
        Real.exp_add]
      congr 1
      calc
        Real.exp (Real.log (Real.log (y : ℝ)) * 2) =
            Real.exp ((2 : ℕ) * Real.log (Real.log (y : ℝ))) := by
              congr 1
              norm_num
              ring
        _ = Real.exp (Real.log (Real.log (y : ℝ))) ^ 2 :=
          Real.exp_nat_mul _ _
        _ = Real.log (y : ℝ) ^ 2 := by rw [Real.exp_log hlog]

#print axioms exists_smooth_reciprocal_log_sq_bound

end

end Erdos49
