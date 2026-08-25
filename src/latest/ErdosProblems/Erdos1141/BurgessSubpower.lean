import ErdosProblems.Erdos1141.QuadraticCRT
import Mathlib.Order.Filter.AtTopBot.Finite
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Subpower losses from the number of prime factors

The factorial argument is extracted from `Erdos587.NVDevelopment`.
-/

namespace Pollack17.Burgess

open Filter
open scoped BigOperators

lemma factorial_card_le_prod_of_one_le (s : Finset ℕ)
    (hs : ∀ x ∈ s, 1 ≤ x) :
    Nat.factorial s.card ≤ ∏ x ∈ s, x := by
  classical
  let f : Fin s.card ↪o ℕ := s.orderEmbOfFin rfl
  have hidx : ∀ i : ℕ, ∀ hi : i < s.card, i + 1 ≤ f ⟨i, hi⟩ := by
    intro i hi
    induction i with
    | zero =>
        have hmem : f ⟨0, hi⟩ ∈ s := by
          simp [f]
        simpa [f] using hs (f ⟨0, hi⟩) hmem
    | succ i ih =>
        have hi' : i < s.card := Nat.lt_of_succ_lt hi
        have hprev : i + 1 ≤ f ⟨i, hi'⟩ := ih hi'
        have hlt : f ⟨i, hi'⟩ < f ⟨i + 1, hi⟩ := by
          exact f.strictMono (Nat.lt_succ_self i)
        exact le_trans (Nat.succ_le_succ hprev) (Nat.succ_le_of_lt hlt)
  have hprod : (∏ i : Fin s.card, (i.1 + 1)) ≤ ∏ i : Fin s.card, f i := by
    refine Finset.prod_le_prod' ?_
    intro i _
    exact hidx i.1 i.2
  have hleft : (∏ i : Fin s.card, (i.1 + 1)) = Nat.factorial s.card := by
    calc
      (∏ i : Fin s.card, (i.1 + 1)) =
          ∏ i ∈ Finset.range s.card, (i + 1) := by
        simpa using (Fin.prod_univ_eq_prod_range (fun i : ℕ => i + 1) s.card)
      _ = Nat.factorial s.card := Finset.prod_range_add_one_eq_factorial s.card
  have hright : (∏ i : Fin s.card, f i) = ∏ x ∈ s, x := by
    calc
      (∏ i : Fin s.card, f i) =
          ∏ x ∈ Finset.map (s.orderEmbOfFin rfl).toEmbedding Finset.univ, x := by
        symm
        simpa [f] using
          (Finset.prod_map (s := Finset.univ)
            (e := (s.orderEmbOfFin rfl).toEmbedding) (f := fun x : ℕ => x))
      _ = ∏ x ∈ s, x := by
        rw [Finset.map_orderEmbOfFin_univ (s := s) (h := rfl)]
  calc
    Nat.factorial s.card = ∏ i : Fin s.card, (i.1 + 1) := hleft.symm
    _ ≤ ∏ i : Fin s.card, f i := hprod
    _ = ∏ x ∈ s, x := hright

/-- The factorial of the number of distinct prime factors of a nonzero
natural is bounded by the natural itself. -/
lemma factorial_card_primeFactors_le (n : ℕ) (hn : n ≠ 0) :
    Nat.factorial n.primeFactors.card ≤ n := by
  have hprod : Nat.factorial n.primeFactors.card ≤ ∏ p ∈ n.primeFactors, p :=
    factorial_card_le_prod_of_one_le _ (by
      intro p hp
      exact (Nat.prime_of_mem_primeFactors hp).one_le)
  exact hprod.trans
    (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) (Nat.prod_primeFactors_dvd n))

/-- For fixed `b` and positive `m`, the loss `b ^ ω(n)` is eventually at
most `n ^ (1 / m)`.  This is the exact subpower input needed to absorb the
`3 ^ ω(q)` CRT loss in the quadratic Burgess fourth moment. -/
theorem const_pow_primeFactors_card_le_rpow_eventually
    (b m : ℕ) (hb : 1 ≤ b) (hm : 0 < m) :
    ∃ Nω : ℕ, ∀ {n : ℕ}, Nω ≤ n →
      (b : ℝ) ^ n.primeFactors.card ≤ (n : ℝ) ^ ((1 : ℝ) / m) := by
  have hfact : ∀ᶠ k : ℕ in atTop, (b ^ m) ^ k < Nat.factorial (k - 1) := by
    simpa using (Nat.eventually_pow_lt_factorial_sub (b ^ m) 1)
  rcases eventually_atTop.mp hfact with ⟨k₀, hk₀⟩
  refine ⟨max 3 ((b ^ k₀) ^ m), ?_⟩
  intro n hn
  let k := n.primeFactors.card
  have hn3 : 3 ≤ n := (Nat.le_max_left _ _).trans hn
  have hnpos : 0 < n := by omega
  by_cases hk_small : k < k₀
  · have hk_le : k ≤ k₀ := hk_small.le
    have hpow_nat : (b ^ k : ℕ) ≤ b ^ k₀ :=
      Nat.pow_le_pow_right (by omega : 0 < b) hk_le
    have hpow_real : (b : ℝ) ^ k ≤ (b : ℝ) ^ k₀ := by
      exact_mod_cast hpow_nat
    have hconst_nat : ((b ^ k₀ : ℕ) ^ m) ≤ n :=
      (Nat.le_max_right _ _).trans hn
    have hconst_real : (((b : ℝ) ^ k₀) ^ m) ≤ (n : ℝ) := by
      exact_mod_cast hconst_nat
    have hroot_le :
        (((b : ℝ) ^ k₀) ^ m) ^ ((1 : ℝ) / m) ≤
          (n : ℝ) ^ ((1 : ℝ) / m) := by
      exact Real.rpow_le_rpow (by positivity) hconst_real (by positivity)
    have hroot :
        (((b : ℝ) ^ k₀) ^ m) ^ ((1 : ℝ) / m) = (b : ℝ) ^ k₀ := by
      simpa [one_div] using
        Real.pow_rpow_inv_natCast (show 0 ≤ (b : ℝ) ^ k₀ by positivity)
          (Nat.ne_of_gt hm)
    rw [hroot] at hroot_le
    exact hpow_real.trans hroot_le
  · have hk_ge : k₀ ≤ k := Nat.le_of_not_gt hk_small
    have hmain_nat : (b ^ m) ^ k < Nat.factorial k := by
      exact (hk₀ k hk_ge).trans_le (Nat.factorial_le (Nat.sub_le _ _))
    have hk_fact_le_n : Nat.factorial k ≤ n := by
      simpa [k] using factorial_card_primeFactors_le n (Nat.ne_of_gt hnpos)
    have hpowm_nat' : (b ^ m) ^ k ≤ n :=
      (Nat.le_of_lt hmain_nat).trans hk_fact_le_n
    have hpowm_nat : (b ^ k : ℕ) ^ m ≤ n := by
      calc
        (b ^ k : ℕ) ^ m = b ^ (k * m) := by rw [pow_mul]
        _ = b ^ (m * k) := by rw [Nat.mul_comm]
        _ = (b ^ m) ^ k := by rw [pow_mul]
        _ ≤ n := hpowm_nat'
    have hpowm_real : (((b : ℝ) ^ k) ^ m) ≤ (n : ℝ) := by
      exact_mod_cast hpowm_nat
    have hroot_le :
        (((b : ℝ) ^ k) ^ m) ^ ((1 : ℝ) / m) ≤
          (n : ℝ) ^ ((1 : ℝ) / m) := by
      exact Real.rpow_le_rpow (by positivity) hpowm_real (by positivity)
    have hroot :
        (((b : ℝ) ^ k) ^ m) ^ ((1 : ℝ) / m) = (b : ℝ) ^ k := by
      simpa [one_div] using
        Real.pow_rpow_inv_natCast (show 0 ≤ (b : ℝ) ^ k by positivity)
          (Nat.ne_of_gt hm)
    rw [hroot] at hroot_le
    exact hroot_le


theorem primeModulus_primeFactors (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) :
    (primeModulus s).primeFactors = s := Nat.primeFactors_prod hs

theorem primeModulus_card_divisors (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) :
    (primeModulus s).divisors.card = 2 ^ s.card := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [primeModulus]
  | @insert p s hp ih =>
    have hs' : ∀ r ∈ s, r.Prime := fun r hr => hs r (Finset.mem_insert_of_mem hr)
    have hpp : p.Prime := hs p (Finset.mem_insert_self p s)
    have hcop : p.Coprime (primeModulus s) := Nat.Coprime.prod_right fun r hr =>
      hpp.coprime_iff_not_dvd.mpr fun hdvd =>
        hp ((Nat.prime_dvd_prime_iff_eq hpp (hs' r hr)).mp hdvd ▸ hr)
    rw [show primeModulus (insert p s) = p * primeModulus s from Finset.prod_insert hp,
      hcop.card_divisors_mul, ih hs', Finset.card_insert_of_notMem hp, pow_succ', hpp.divisors]
    have hpne : p ≠ 1 := hpp.ne_one
    simp [Ne.symm hpne]

theorem eventually_const_pow_primeFactors_le (b : ℕ) (hb : 1 ≤ b)
    {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ q : ℕ in atTop, (b : ℝ) ^ q.primeFactors.card ≤ (q : ℝ) ^ δ := by
  obtain ⟨m, hm⟩ := exists_nat_gt (1 / δ)
  have hmpos : 0 < m := by
    have hreal : 0 < (m : ℝ) := lt_trans (one_div_pos.mpr hδ) hm
    exact_mod_cast hreal
  have hexp : (1 : ℝ) / m ≤ δ := by
    have hprod : 1 < (m : ℝ) * δ := (div_lt_iff₀ hδ).mp hm
    exact (div_le_iff₀ (by exact_mod_cast hmpos : 0 < (m : ℝ))).mpr (by nlinarith)
  obtain ⟨Q, hQ⟩ := const_pow_primeFactors_card_le_rpow_eventually b m hb hmpos
  filter_upwards [eventually_ge_atTop Q, eventually_ge_atTop 1] with q hq hq1
  exact (hQ hq).trans (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hq1) hexp)

theorem eventually_primeSet_const_pow_le (b : ℕ) (hb : 1 ≤ b)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ Q : ℕ, ∀ (s : Finset ℕ) (_hs : ∀ p ∈ s, p.Prime), Q ≤ primeModulus s →
      (b : ℝ) ^ s.card ≤ (primeModulus s : ℝ) ^ δ := by
  obtain ⟨Q, hQ⟩ := eventually_atTop.mp (eventually_const_pow_primeFactors_le b hb hδ)
  refine ⟨Q, fun s hs hq => ?_⟩
  simpa only [primeModulus_primeFactors s hs] using hQ (primeModulus s) hq

theorem eventually_const_mul_pow_primeFactors_le (K : ℝ) (b : ℕ) (hb : 1 ≤ b)
    {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ q : ℕ in atTop, K * (b : ℝ) ^ q.primeFactors.card ≤ (q : ℝ) ^ δ := by
  have hp := eventually_const_pow_primeFactors_le b hb (half_pos hδ)
  have hK : ∀ᶠ q : ℕ in atTop, K ≤ (q : ℝ) ^ (δ / 2) :=
    ((tendsto_rpow_atTop (half_pos hδ)).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))).eventually (eventually_ge_atTop K)
  filter_upwards [hp, hK, eventually_ge_atTop 1] with q hq hKq hq1
  have hqpos : 0 < (q : ℝ) := by exact_mod_cast hq1
  calc
    K * (b : ℝ) ^ q.primeFactors.card ≤
        (q : ℝ) ^ (δ / 2) * (q : ℝ) ^ (δ / 2) :=
      mul_le_mul hKq hq (pow_nonneg (Nat.cast_nonneg _) _) (Real.rpow_nonneg hqpos.le _)
    _ = (q : ℝ) ^ δ := by rw [← Real.rpow_add hqpos]; congr 1; ring

end Pollack17.Burgess
